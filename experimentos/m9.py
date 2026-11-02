"""
M9: cociente de tiempo robusto frente a la colocación del código (RESEARCH_PROTOCOL.md, §6, M9; versión sencilla
de la propuesta de Codex Sol, docs/borradores/M9-rendimiento-codex-sol.md).

    python3 experimentos/maquina.py medir NOMBRE -- python3 experimentos/m9.py \
        --a impl.c:efch_tcp_options__lang --b ejemplos/corpus-g3/tcp/baseline.c:baseline_tcp_options \
        --carga resultados/exp-010/tcp/medicion/carga-*.bin --salida DIR [--control]

- Cada función va en su propio objeto. Se construyen K = 16 ejecutables con relleno no ejecutado delante de cada
  función: los desplazamientos 0, 16, …, 240 se reparten con dos permutaciones fijas (semilla 20261024), y la mitad de
  los ejecutables enlaza A antes que B. Las direcciones finales se comprueban con `nm`.
- En cada ejecutable y carga: 16 bloques ABBA o BAAB (alternos), y cada ventana recorre la carga 32 veces.
- m[f,k,s] = mediana por bloques de la media de las dos ventanas de f. R[k] = Σs m[A,k,s] / Σs m[B,k,s].
- Banda simultánea del 95 %: 2 000 remuestreos de bloques dentro de cada (k, s), c = p95 de max_k |log R*/R|.
- Decisión frente al umbral U: «cumple» si max_k R[k]·e^c ≤ U; «no cumple» si min_k R[k]·e^-c > U; si no,
  «indeterminado».
- `--control` mide A frente a una copia idéntica de A (validación del instrumento). Se espera que la media geométrica
  de R[k] quede en [0,98, 1,02].
"""

import argparse
import glob
import json
import math
import pathlib
import random
import re
import statistics
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from efch import backend_c, core, native  # noqa: E402

K, BLOQUES, PASADAS = 16, 16, 32
FLAGS = ["-O3", "-march=native", "-fno-lto"]
CPU = "2"


def harness(comp, fa, fb, bloques, pasadas):
    """Arnés ABBA/BAAB; imprime, por bloque, los tiempos ns/op de las cuatro ventanas en orden de A y B."""
    load = []
    for k, (_, ty) in enumerate(comp.inputs):
        if ty[0] == "bytes":
            m = max(ty[1], 1)
            load.append(f"in{k}_n = malloc(count * 8); in{k}_b = malloc(count * {m});"
                        f" if (fread(in{k}_n, 8, count, f) != count || fread(in{k}_b, {m}, count, f) != count) return 1;")
        else:
            load.append(f"in{k} = malloc(count * 8); if (fread(in{k}, 8, count, f) != count) return 1;")
    globs = "\n".join(f"static uint64_t *in{k}_n; static uint8_t *in{k}_b;" if ty[0] == "bytes"
                      else f"static uint64_t *in{k};" for k, (_, ty) in enumerate(comp.inputs))
    out = comp.output
    outs = ("uint64_t " + ", ".join(f"o{k} = 0" for k in range(len(out[1]))) + ";") if out[0] == "option" else \
        (f"uint8_t ob[{max(out[1], 1)}] = {{0}};" if out[0] == "bytes" else "")
    reset = " ".join(f"o{k} = 0;" for k in range(len(out[1]))) if out[0] == "option" else ""

    def window(f):
        return (f"__attribute__((noinline)) static double win_{f}(size_t count) {{ {outs} uint64_t acc = 0; {reset}"
                f" double t0 = now_ns(); for (int p = 0; p < {pasadas}; p++) for (size_t i = 0; i < count; i++) "
                f"{{ {native._call_expr(comp, f, 'i')} }} double t = (now_ns() - t0) / ((double)count * {pasadas});"
                f" sink += acc; return t; }}")
    decls = "\n".join(backend_c.signature(comp, f) + ";" for f in (fa, fb))
    return f"""#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef unsigned __int128 efch_u128;
{decls}
{globs}
static volatile uint64_t sink;
static double now_ns(void) {{ struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e9 + ts.tv_nsec; }}
{window(fa)}
{window(fb)}
int main(int argc, char **argv) {{
    if (argc != 2) return 2;
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    uint64_t count64; if (fread(&count64, 8, 1, f) != 1) return 1;
    size_t count = (size_t)count64;
    {' '.join(load)}
    fclose(f);
    for (int w = 0; w < 2; w++) {{ win_{fa}(count); win_{fb}(count); }}
    printf("[");
    for (int b = 0; b < {bloques}; b++) {{
        double a1, a2, b1, b2;
        if (b % 2 == 0) {{ a1 = win_{fa}(count); b1 = win_{fb}(count); b2 = win_{fb}(count); a2 = win_{fa}(count); }}
        else {{ b1 = win_{fb}(count); a1 = win_{fa}(count); a2 = win_{fa}(count); b2 = win_{fb}(count); }}
        printf("%s[%.4f, %.4f, %.4f, %.4f]", b ? ", " : "", a1, a2, b1, b2);
    }}
    printf("]\\n");
    return 0;
}}
"""


def sh(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(f"{' '.join(map(str, cmd))}: {p.stderr[-800:]}")
    return p.stdout


def pad_obj(d, name, n):
    s = d / f"{name}.s"
    s.write_text(f'.section .text,"ax",@progbits\n.balign 256\n.skip {n}, 0xcc\n' if n else
                 '.section .text,"ax",@progbits\n.balign 256\n')
    sh(["gcc", "-c", s.name, "-o", f"{name}.o"], d)
    return f"{name}.o"


def copy_source(src, fname, new):
    """Copia de la fuente con la función renombrada (control de copias idénticas)."""
    text = src.read_text()
    assert re.search(rf"\b{fname}\b", text)
    return re.sub(rf"\b{fname}\b", new, text)


def stats(data, umbral, rng):
    """data[k][s] = lista de bloques (a1, a2, b1, b2)."""
    def ratio(blocks_by_seed):
        num = sum(statistics.median((x[0] + x[1]) / 2 for x in bl) for bl in blocks_by_seed.values())
        den = sum(statistics.median((x[2] + x[3]) / 2 for x in bl) for bl in blocks_by_seed.values())
        return num / den
    R = [ratio(data[k]) for k in range(len(data))]
    devs = []
    for _ in range(2000):
        dev = 0.0
        for k in range(len(data)):
            boot = {s: [rng.choice(bl) for _ in bl] for s, bl in data[k].items()}
            dev = max(dev, abs(math.log(ratio(boot) / R[k])))
        devs.append(dev)
    c = sorted(devs)[int(0.95 * len(devs)) - 1]
    lo, hi = min(R) * math.exp(-c), max(R) * math.exp(c)
    decision = "cumple" if hi <= umbral else ("no cumple" if lo > umbral else "indeterminado")
    gmean = math.exp(statistics.mean(math.log(r) for r in R))
    return {"R": [round(r, 4) for r in R], "mediana": round(statistics.median(R), 4), "min": round(min(R), 4),
            "max": round(max(R), 4), "media_geometrica": round(gmean, 4), "c": round(c, 4),
            "banda": [round(lo, 4), round(hi, 4)], "umbral": umbral, "decision": decision}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--a", required=True, help="FUENTE.c:función (numerador)")
    ap.add_argument("--b", required=True, help="FUENTE.c:función (denominador)")
    ap.add_argument("--carga", nargs="+", required=True)
    ap.add_argument("--definicion", default="ejemplos/corpus-g3/tcp/spec.efch")
    ap.add_argument("--computacion", default="tcp-options")
    ap.add_argument("--umbral", type=float, default=1.25)
    ap.add_argument("--control", action="store_true", help="B = copia idéntica de A")
    ap.add_argument("--salida", required=True)
    args = ap.parse_args()
    t_start = time.time()
    spec = core.load_definition((ROOT / args.definicion).read_text(), args.definicion)
    comp = spec.computations[args.computacion]
    (sa, fa), (sb, fb) = [(pathlib.Path(x.rsplit(":", 1)[0]).resolve(), x.rsplit(":", 1)[1]) for x in (args.a, args.b)]
    out = (ROOT / args.salida).resolve()
    out.mkdir(parents=True, exist_ok=True)
    (out / "a.c").write_text(sa.read_text())
    if args.control:
        sb, fb = out / "b.c", fa + "_copia"
        sb.write_text(copy_source(sa, fa, fb))
    elif fb == fa:  # mismo nombre en dos fuentes (p. ej., antes y después de un cambio del backend)
        (out / "b.c").write_text(copy_source(sb, fb, fb + "_b"))
        sb, fb = out / "b.c", fb + "_b"
    else:
        (out / "b.c").write_text(sb.read_text())
    sh(["gcc", *FLAGS, "-c", "a.c", "-o", "a.o"], out)
    sh(["gcc", *FLAGS, "-c", "b.c", "-o", "b.o"], out)
    sh(["objcopy", f"--keep-global-symbol={fa}", "a.o"], out)  # solo la función medida queda global
    sh(["objcopy", f"--keep-global-symbol={fb}", "b.o"], out)
    (out / "bench.c").write_text(harness(comp, fa, fb, BLOQUES, PASADAS))
    sh(["gcc", *FLAGS, "-c", "bench.c", "-o", "bench.o"], out)
    cargas = sorted(pathlib.Path(p).resolve() for g in args.carga for p in glob.glob(str(ROOT / g)) or [g])
    rng = random.Random(20261024)
    offs = list(range(0, 256, 16))
    pa, pb = offs[:], offs[:]
    rng.shuffle(pa)
    rng.shuffle(pb)
    data, layout = [], []
    for k in range(K):
        objs_a = [pad_obj(out, f"pad-a{k}", pa[k]), "a.o"]
        objs_b = [pad_obj(out, f"pad-b{k}", pb[k]), "b.o"]
        order = objs_a + objs_b if k % 2 == 0 else objs_b + objs_a
        exe = f"bench-{k}"
        sh(["gcc", *FLAGS, "bench.o", *order, "-o", exe], out)
        syms = {l.split()[2]: int(l.split()[0], 16) for l in sh(["nm", exe], out).splitlines()
                if len(l.split()) == 3 and l.split()[2] in (fa, fb)}
        layout.append({"k": k, "relleno_a": pa[k], "relleno_b": pb[k], "a_primero": k % 2 == 0,
                       "dir_a_mod64": syms[fa] % 64, "dir_b_mod64": syms[fb] % 64,
                       "dir_a_mod4096": syms[fa] % 4096, "dir_b_mod4096": syms[fb] % 4096})
        data.append({})
    ordenes = list(range(K))
    rng.shuffle(ordenes)
    for k in ordenes:
        for c in cargas:
            res = sh(["taskset", "-c", CPU, f"./bench-{k}", str(c)], out)
            data[k][c.name] = json.loads(res)
        print(f"colocación {k}: {layout[k]}", flush=True)
    st = stats(data, args.umbral, random.Random(20261025))
    ev = {"fecha": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "a": f"{sa}:{fa}", "b": f"{sb}:{fb}",
          "control": args.control, "flags": FLAGS, "cpu": CPU, "K": K, "bloques": BLOQUES, "pasadas": PASADAS,
          "gcc": native.compiler_version(), "cargas": [c.name for c in cargas], "orden_ejecucion": ordenes,
          "colocaciones": layout, "muestras": data, "estadistico": st, "segundos": round(time.time() - t_start, 1)}
    if args.control:
        st["control_valido"] = 0.98 <= st["media_geometrica"] <= 1.02
    (out / "evidencia.json").write_text(json.dumps(ev, ensure_ascii=False, indent=1))
    for f in out.glob("bench-*"):
        f.unlink()
    print(json.dumps(st, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
