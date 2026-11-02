"""
Oráculo formal de C con CBMC: ¿una implementación en C equivale a una definición EFCH?

Se materializa la definición en C (backend_c) y se genera un arnés que llama a
las dos funciones con entradas no deterministas del dominio declarado, y afirma
que sus resultados son observablemente iguales. Las entradas `bytes` se reservan
con malloc del tamaño exacto, así que `--pointer-check` detecta cualquier
lectura más allá de la longitud. Con `--unwinding-assertions`, un desenrollado
insuficiente de los bucles de la implementación se informa como fallo, no se
ignora: si la causa es solo el desenrollado, el resultado es «desconocido».

Supuestos de un «probado»: corrección de CBMC y de su solver, la ABI de EFCH
(backend_c) para la función comparada y la traducción de la definición a C de
backend_c (que aquí hace de referencia; no está verificada formalmente).
"""

import pathlib
import re
import subprocess
import tempfile
import time

from . import backend_c, core

ROOT = pathlib.Path(__file__).resolve().parent.parent
CBMC = ROOT / ".vendor" / "cbmc-6.11.0" / "usr" / "bin" / "cbmc"


def version():
    return subprocess.run([str(CBMC), "--version"], capture_output=True, text=True).stdout.strip()


def _harness(comp, ref_name, impl_name):
    lines = ["#include <stdint.h>", "#include <stddef.h>", "#include <stdlib.h>", "#include <assert.h>",
             backend_c.signature(comp, ref_name) + ";", backend_c.signature(comp, impl_name) + ";",
             "uint64_t nondet_u64(void); size_t nondet_size(void); int nondet_int(void);", "int main(void) {"]
    args = []
    for k, (_, ty) in enumerate(comp.inputs):
        if ty[0] == "bytes":
            lines += [f"    size_t n{k} = nondet_size();", f"    __CPROVER_assume(n{k} <= {ty[1]});",
                      f"    uint8_t *b{k} = malloc(n{k});",  # tamaño exacto, también con n = 0
                      # CBMC modela que malloc puede fallar; aquí se compara con un búfer válido.
                      f"    __CPROVER_assume(b{k} != NULL);"]
            args += [f"b{k}", f"n{k}"]
        elif ty[0] == "bool":
            lines += [f"    int x{k} = nondet_int();", f"    __CPROVER_assume(x{k} == 0 || x{k} == 1);"]
            args.append(f"x{k}")
        else:
            lines.append(f"    uint64_t x{k} = nondet_u64();")
            if ty[1] < 64:
                lines.append(f"    __CPROVER_assume(x{k} < (UINT64_C(1) << {ty[1]}));")
            args.append(f"x{k}")
    out = comp.output
    a = ", ".join(args)
    if out[0] == "bytes":
        m = max(out[1], 1)
        lines += [f"    uint8_t ra[{m}], rb[{m}];",
                  f"    size_t la = {ref_name}({a}, ra);", f"    size_t lb = {impl_name}({a}, rb);",
                  "    assert(la == lb);",
                  f"    for (size_t i = 0; i < la && i < {m}; i++) assert(ra[i] == rb[i]);"]
    elif out[0] == "option":
        k = len(out[1])
        lines += [f"    uint64_t a[{k}], b[{k}];",
                  f"    int ta = {ref_name}({a}, {', '.join(f'&a[{i}]' for i in range(k))});",
                  f"    int tb = {impl_name}({a}, {', '.join(f'&b[{i}]' for i in range(k))});",
                  "    assert((ta != 0) == (tb != 0));"]
        lines += [f"    if (ta) assert(a[{i}] == b[{i}]);" for i in range(k)]
    else:
        lines += [f"    assert({ref_name}({a}) == {impl_name}({a}));"]
    lines += ["    return 0;", "}"]
    return "\n".join(lines) + "\n"


# Prefijo opcional para lanzar CBMC con límites de recursos, p. ej. systemd-run con MemoryMax (EXP-003, fase 3).
PREFIX = []


def check_equivalence(comp, impl_c, impl_name, unwind=70, timeout_s=300, workdir=None, include_dirs=()):
    """CBMC: impl_c (texto C) frente a la semántica de comp. Devuelve un dict con estado.

    `include_dirs`: directorios para los `#include "..."` de impl_c (p. ej. el de firma.h)."""
    ref_name = "efch_ref_" + backend_c.c_ident(comp.name)
    ref_unit = backend_c.emit_unit([(comp, comp.semantics, ref_name)])
    with tempfile.TemporaryDirectory(dir=workdir) as tmp:
        tmp = pathlib.Path(tmp)
        (tmp / "ref.c").write_text(ref_unit)
        (tmp / "impl.c").write_text(impl_c)
        (tmp / "harness.c").write_text(_harness(comp, ref_name, impl_name))
        cmd = PREFIX + [str(CBMC), "harness.c", "ref.c", "impl.c", "--bounds-check", "--pointer-check",
               "--unwind", str(unwind), "--unwinding-assertions", "--trace"]
        for d in include_dirs:
            cmd += ["-I", str(pathlib.Path(d).resolve())]
        t0 = time.perf_counter()
        try:
            proc = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True, timeout=timeout_s)
        except subprocess.TimeoutExpired:
            return {"estado": "desconocido", "detalle": f"CBMC sin respuesta en {timeout_s} s",
                    "segundos": timeout_s}
        secs = round(time.perf_counter() - t0, 2)
        text = proc.stdout + proc.stderr
        if proc.returncode in (-9, 137) or "Out of memory" in text:
            return {"estado": "desconocido", "segundos": secs, "detalle": "CBMC terminado: memoria agotada"}
        if "VERIFICATION SUCCESSFUL" in text:
            return {"estado": "probado", "segundos": secs, "detalle": f"CBMC, unwind {unwind}"}
        if "VERIFICATION FAILED" in text:
            failed = re.findall(r"\[(.*?)\] .*?: FAILURE", text) or re.findall(r"^(.*): FAILURE$", text, re.M)
            only_unwind = failed and all("unwind" in f for f in failed)
            return {"estado": "desconocido" if only_unwind else "refutado", "segundos": secs,
                    "detalle": ("desenrollado insuficiente: " if only_unwind else "propiedades fallidas: ")
                    + ", ".join(failed[:6]),
                    "traza": _trace_inputs(text)}
        return {"estado": "no_aplicable", "segundos": secs, "detalle": text[-1500:]}


def _trace_inputs(text):
    """Asignaciones relevantes de la traza de CBMC (entradas del contraejemplo)."""
    vals = re.findall(r"^\s+(n\d+|x\d+|b\d+\[\d+\]|dynamic_object\d*\[\d+\w*\])=(\S+)", text, re.M)
    seen = {}
    for k, v in vals:
        seen.setdefault(k, v)
    return seen


def check_c_against_definition(defn_text, comp_name, impl_c, impl_name, **kw):
    comp = core.load_definition(defn_text).computations[comp_name]
    return check_equivalence(comp, impl_c, impl_name, **kw)
