"""
Compilación, pruebas diferenciales y medición de las materializaciones en C.

- `build_library` compila la unidad generada (y la línea base, si existe) como
  biblioteca compartida para llamarla con ctypes.
- `differential` contrasta cada función compilada con el intérprete (evidencia
  experimental sobre la traducción a C, que no está demostrada).
- `benchmark` genera un arnés en C que llama a todas las funciones con la carga
  declarada, intercalando repeticiones para que la deriva de la máquina
  afecte a todas por igual. Cada función está en otra unidad de traducción,
  así que ninguna se beneficia de inlining en el arnés.
"""

import ctypes
import json
import os
import pathlib
import random
import statistics
import struct
import subprocess

from . import backend_c, workload
from .interp import Undefined, evaluate

OPT_FLAGS = ["-O2"]  # optimización, configurable con --cflags; se registra en la evidencia
BASE_FLAGS = ["-std=c11", "-Wall", "-Wno-unused-variable", "-Wno-unused-but-set-variable"]
CFLAGS = OPT_FLAGS + BASE_FLAGS


def set_optimization(flags):
    global CFLAGS
    CFLAGS = list(flags) + BASE_FLAGS
_builds = 0


def compiler_version():
    return subprocess.run(["gcc", "--version"], capture_output=True, text=True).stdout.splitlines()[0]


def _gcc(args, cwd):
    proc = subprocess.run(["gcc", *CFLAGS, *args], cwd=cwd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError("gcc falló:\n" + proc.stderr[-3000:])


def build_library(out_dir, unit_text, baseline_path=None):
    out_dir = pathlib.Path(out_dir).resolve()
    (out_dir / "impl.c").write_text(unit_text)
    sources = ["impl.c"]
    if baseline_path:
        sources.append(str(pathlib.Path(baseline_path).resolve()))
    # Nombre único: dlopen devolvería la biblioteca ya cargada si se repite la ruta.
    global _builds
    _builds += 1
    lib = out_dir / f"libefch-{os.getpid()}-{_builds}.so"
    _gcc(["-shared", "-fPIC", "-o", str(lib), *sources], out_dir)
    return ctypes.CDLL(str(lib))


def bind(lib, comp, fname):
    """Envuelve una función C con la ABI de EFCH; devuelve valores como el intérprete."""
    fn = getattr(lib, fname)
    argtypes = []
    for _, ty in comp.inputs:
        argtypes += [ctypes.c_char_p, ctypes.c_size_t] if ty[0] == "bytes" else \
            [ctypes.c_int if ty[0] == "bool" else ctypes.c_uint64]
    out = comp.output
    if out[0] == "bytes":
        argtypes.append(ctypes.c_char_p)
        fn.restype = ctypes.c_size_t
    elif out[0] == "option":
        argtypes += [ctypes.POINTER(ctypes.c_uint64)] * len(out[1])
        fn.restype = ctypes.c_int
    else:
        fn.restype = ctypes.c_int if out[0] == "bool" else ctypes.c_uint64
    fn.argtypes = argtypes

    def call(args):
        cargs = []
        for v, (_, ty) in zip(args, comp.inputs):
            cargs += [bytes(v), len(v)] if ty[0] == "bytes" else [int(v)]
        if out[0] == "bytes":
            buf = ctypes.create_string_buffer(max(out[1], 1))
            n = fn(*cargs, buf)
            return tuple(buf.raw[:n])
        if out[0] == "option":
            cells = [ctypes.c_uint64() for _ in out[1]]
            tag = fn(*cargs, *[ctypes.byref(c) for c in cells])
            if not tag:
                return None
            return tuple(bool(c.value) if t[0] == "bool" else c.value for c, t in zip(cells, out[1]))
        r = fn(*cargs)
        return bool(r) if out[0] == "bool" else r

    return call


def differential(comp, definition, call, seed=20261020, n_random=3000, n_workload=2000):
    """Compara una función nativa con la semántica en entradas de borde, aleatorias y de la carga."""
    rng = random.Random(seed)
    cases = workload.edge_inputs(comp, rng, n_random)
    if comp.workload is not None:
        cases += workload.generate(comp, definition, seed, n_workload)
    failures = []
    for args in cases:
        env = {name: v for (name, _), v in zip(comp.inputs, args)}
        try:
            expected = evaluate(comp.semantics, env)
        except Undefined:
            continue
        got = call(args)
        if got != expected:
            failures.append({"entrada": [list(a) if isinstance(a, tuple) else a for a in args],
                             "esperado": _plain(expected), "obtenido": _plain(got)})
    return {"estado": "refutado" if failures else "desconocido",
            "evidencia": "experimental: pruebas diferenciales frente al intérprete",
            "casos": len(cases), "fallos": len(failures), "contraejemplos": failures[:5]}


def _plain(v):
    return list(v) if isinstance(v, tuple) else v


# --- Medición ------------------------------------------------------------------

def _call_expr(comp, fname, idx):
    args = []
    for k, (_, ty) in enumerate(comp.inputs):
        if ty[0] == "bytes":
            args += [f"in{k}_b + (size_t){idx} * {max(ty[1], 1)}", f"(size_t)in{k}_n[{idx}]"]
        else:
            args.append(f"({backend_c.ctype(ty)})in{k}[{idx}]")
    out = comp.output
    if out[0] == "bytes":
        return f"acc += (uint64_t){fname}({', '.join(args + ['ob'])}) + ob[0];"
    if out[0] == "option":
        outs = [f"&o{k}" for k in range(len(out[1]))]
        return f"acc += (uint64_t){fname}({', '.join(args + outs)}) + o0;"
    return f"acc += (uint64_t){fname}({', '.join(args)});"


def _harness(comp, fnames, repeats):
    out = comp.output
    decls = "\n".join(backend_c.signature(comp, f) + ";" for f in fnames)
    load = []
    for k, (_, ty) in enumerate(comp.inputs):
        if ty[0] == "bytes":
            m = max(ty[1], 1)
            load.append(f"in{k}_n = malloc(count * 8); in{k}_b = malloc(count * {m});"
                        f" if (fread(in{k}_n, 8, count, f) != count || fread(in{k}_b, {m}, count, f) != count) return 1;")
        else:
            load.append(f"in{k} = malloc(count * 8); if (fread(in{k}, 8, count, f) != count) return 1;")
    globals_ = "\n".join(
        f"static uint64_t *in{k}_n; static uint8_t *in{k}_b;" if ty[0] == "bytes" else f"static uint64_t *in{k};"
        for k, (_, ty) in enumerate(comp.inputs))
    out_decl = f"uint8_t ob[{max(out[1], 1)}] = {{0}};" if out[0] == "bytes" else \
        ("uint64_t " + ", ".join(f"o{k} = 0" for k in range(len(out[1]))) + ";" if out[0] == "option" else "")
    loops = []
    for j, f in enumerate(fnames):
        loops.append(f"""
            {{
                uint64_t acc = 0;
                double t0 = now_ns();
                for (size_t i = 0; i < count; i++) {{ {_call_expr(comp, f, 'i')} }}
                samples[{j}][r] = (now_ns() - t0) / count;
                sink += acc;
            }}""")
    names = ", ".join(f'"{f}"' for f in fnames)
    return f"""#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef unsigned __int128 efch_u128;
{decls}
{globals_}
static volatile uint64_t sink;
static double now_ns(void) {{ struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e9 + ts.tv_nsec; }}
int main(int argc, char **argv) {{
    if (argc != 2) return 2;
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    uint64_t count64; if (fread(&count64, 8, 1, f) != 1) return 1;
    size_t count = (size_t)count64;
    {' '.join(load)}
    fclose(f);
    {out_decl}
    static double samples[{len(fnames)}][{repeats}];
    const char *names[] = {{{names}}};
    for (int r = 0; r < {repeats}; r++) {{
        {''.join(loops)}
    }}
    printf("{{");
    for (int j = 0; j < {len(fnames)}; j++) {{
        printf("%s\\"%s\\": [", j ? ", " : "", names[j]);
        for (int r = 0; r < {repeats}; r++) printf("%s%.4f", r ? ", " : "", samples[j][r]);
        printf("]");
    }}
    printf("}}\\n");
    return 0;
}}
"""


def _pack_inputs(comp, rows):
    data = [struct.pack("<Q", len(rows))]
    for k, (_, ty) in enumerate(comp.inputs):
        col = [r[k] for r in rows]
        if ty[0] == "bytes":
            m = max(ty[1], 1)
            data.append(struct.pack(f"<{len(col)}Q", *(len(v) for v in col)))
            data.append(b"".join(bytes(v) + bytes(m - len(v)) for v in col))
        else:
            data.append(struct.pack(f"<{len(col)}Q", *(int(v) for v in col)))
    return b"".join(data)


def symbol_sizes(obj_path):
    proc = subprocess.run(["nm", "-S", "--defined-only", str(obj_path)], capture_output=True, text=True)
    sizes = {}
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[2] in "Tt":
            sizes[parts[3]] = int(parts[1], 16)
    return sizes


def benchmark(out_dir, comp, definition, unit_text, fnames, baseline_path=None, repeats=15,
              extra_objects=(), link_flags=()):
    """Mide ns/op por semilla para cada función. Devuelve {fname: {semilla: {mediana, min, max}}}.

    extra_objects: objetos o bibliotecas estáticas de otros compiladores con la misma ABI (EXP-005)."""
    out_dir = pathlib.Path(out_dir).resolve()
    (out_dir / "impl.c").write_text(unit_text)
    _gcc(["-c", "impl.c", "-o", "impl.o"], out_dir)
    objects = ["impl.o"]
    sizes = symbol_sizes(out_dir / "impl.o")
    if baseline_path:
        _gcc(["-c", str(pathlib.Path(baseline_path).resolve()), "-o", "baseline.o"], out_dir)
        objects.append("baseline.o")
        sizes.update(symbol_sizes(out_dir / "baseline.o"))
    (out_dir / "bench.c").write_text(_harness(comp, fnames, repeats))
    objects += [str(pathlib.Path(o).resolve()) for o in extra_objects]
    _gcc(["bench.c", *objects, "-o", "bench", *link_flags], out_dir)
    seeds, _, _ = workload.parse(comp, definition)
    results = {f: {} for f in fnames}
    for seed in seeds:
        path = out_dir / f"carga-{seed}.bin"
        path.write_bytes(_pack_inputs(comp, workload.generate(comp, definition, seed)))
        proc = subprocess.run([str(out_dir / "bench"), str(path)], capture_output=True, text=True, check=True)
        for f, samples in json.loads(proc.stdout).items():
            results[f][str(seed)] = {"mediana": round(statistics.median(samples), 3),
                                     "min": round(min(samples), 3), "max": round(max(samples), 3)}
    return results, {f: sizes.get(f) for f in fnames}
