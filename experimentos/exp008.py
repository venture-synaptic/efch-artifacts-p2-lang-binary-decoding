"""
EXP-008: segunda escritura del nombre DNS en EFCH Lang (docs/experimentos/EXP-008.md).

    python3 experimentos/exp008.py vectores                       # especificación nueva frente a los vectores
    python3 experimentos/exp008.py diferencial-spec               # especificación nueva frente a la de EXP-007 (intérprete)
    python3 experimentos/exp008.py todo --salida resultados/exp-008

Reutiliza experimentos/exp007.py (carga, D5 y criterios) y experimentos/exp005.py (medidas) con el
corpus ejemplos/corpus-g2-v2/ y las correcciones de la ficha:
    F1  el C generado por EFCH solo se compila y ejecuta si su verificación es «probado»;
    F2  especificación frente a los vectores, y entradas indefinidas contadas como fallo de integridad;
    F3  D0–D5 siempre presentes: una medición obligatoria ausente no cumple;
    F4  contadores de Dafny (solo se excluye la postcondición principal) y de C (`*` no es comentario
        fuera de un bloque);
    F5  carga con un estrato de nombres largos y rendimiento por estrato;
    F6  huellas de exp008.py, exp007.py, exp005.py y exp005_dafny_rendimiento.py;
    F7  (adenda) OOMPolicy=continue en el límite de memoria, para distinguir memoria (137) de otras señales.
El traductor 0.1 se ejecuta con un límite de recursión mayor (experimentos/exp008_efch.py; adenda de la ficha).
"""

import json
import os
import pathlib
import random
import re
import statistics
import subprocess
import sys
import threading

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "experimentos"))

import exp007 as X  # noqa: E402  (fija E.FUNCTIONS y la carga de EXP-007)
from exp007 import E  # noqa: E402
from efch import backend_c, core, interp, lang, native, workload  # noqa: E402
from efch.interp import Undefined, evaluate  # noqa: E402

E.CORPUS = ROOT / "ejemplos" / "corpus-g2-v2"
OLD = ROOT / "ejemplos" / "corpus-g2" / "dns" / "spec.efch"
NAME = X.NAME
EFCH_CLI = [sys.executable, str(ROOT / "experimentos" / "exp008_efch.py")]
# Revisión de Sonnet, I6: `timeout` dentro del scope de memoria, para que al agotar el tiempo mueran también
# los procesos hijo (CBMC) y no contaminen las mediciones siguientes; queda por debajo de los 900 s de E.timed.
KILL = ["timeout", "-k", "10", "880"]
E.MEMORY = E.MEMORY + ["-p", "OOMPolicy=continue"]  # F7


def spec(path=None):
    return core.load_definition((path or E.CORPUS / "dns" / "spec.efch").read_text()).computations[NAME]


# --- F5: carga con nombres largos -----------------------------------------------------

def long_name(rng):
    """Nombre largo: etiquetas cortas hasta llenar casi los 64 bytes (unas 17 etiquetas de media; el máximo
    observado en 3 000 muestras es 28), final en 0 o
    puntero y, con probabilidad 1/2, una alteración en una posición (como en exp007.structured_name)."""
    out = bytearray()
    room = rng.randint(40, 61)
    while len(out) < room:
        n = rng.choice([1, 1, 1, 2, 3])
        out += bytes([n]) + bytes(rng.choice(X.LDH[:62]) for _ in range(n))
    out += rng.choice([b"\x00", b"\x00", bytes([0xc0 | rng.getrandbits(6), rng.getrandbits(8)])])
    if rng.random() < 0.5:
        k = rng.randrange(len(out))
        kind = rng.randrange(3)
        if kind == 0:
            out[k] = 0x2d
        elif kind == 1:
            out[k] = rng.choice(b"_. \x7f\xe9/")
        else:
            out = out[:k]
    return tuple(out[:64])


STRATA = {"aleatorio": None, "cortos": X.structured_name, "largos": long_name}
_base_generate = X._generate
_stratum = {"activo": None}


def generate(comp, definition, seed, count=None):
    """Carga total: tercios de bytes aleatorios (la declarada), nombres cortos (EXP-007) y largos.
    Con un estrato activo (medición por estrato), solo ese estrato."""
    cases = _base_generate(comp, definition, seed, count)
    if comp.name != NAME:
        return cases
    rng = random.Random(seed)
    s = _stratum["activo"]
    out = []
    for i, c in enumerate(cases):
        kind = s or ("aleatorio", "cortos", "largos")[i % 3]
        out.append(c if kind == "aleatorio" else (STRATA[kind](rng),))
    return out


def edge_inputs(comp, rng, n_random=2000):
    cases = X.edge_inputs(comp, rng, n_random)
    if comp.name == NAME:
        cases += [(long_name(rng),) for _ in range(n_random)]
    return cases


workload.generate = generate
workload.edge_inputs = edge_inputs


# --- F2: integridad con entradas indefinidas contadas ---------------------------------------------

def undefined_count(comp, cases):
    n = 0
    for args in cases:
        try:
            evaluate(comp.semantics, {name: v for (name, _), v in zip(comp.inputs, args)})
        except Undefined:
            n += 1
    return n


def interp_differential(comp, spec_defn, body):
    """Pruebas diferenciales del cuerpo traducido en el intérprete (sin compilar ni ejecutar C; F1)."""
    rng = random.Random(20261020)
    cases = workload.edge_inputs(comp, rng, 3000) + workload.generate(comp, spec_defn, 20261020, 2000)
    fails = []
    for a in cases:
        try:
            if interp.run(body, comp.inputs, list(a)) != interp.run(comp, comp.inputs, list(a)):
                fails.append(bytes(a[0]).hex())
        except Undefined:
            fails.append("indefinida: " + bytes(a[0]).hex())  # fallo de integridad (F2), sin abortar
    return {"casos": len(cases), "fallos": len(fails), "ejemplos": fails[:3],
            "via": "intérprete (el C no se ejecuta sin «probado», F1)"}


# --- F1: EFCH, verificación antes de ejecutar ------------------------------------------------

def efch_part(d, name, spec_defn, comp, out):
    prog = E.CORPUS / d / "prog.efl"
    text = prog.read_text()
    cands = core.load_candidates(lang.candidates_text(text, spec_defn), spec_defn)
    body = cands[0].body
    row = {"vectores_fallidos": E.check_vectors(lambda a: interp.run(body, comp.inputs, a), name),
           "especificacion_vectores_fallidos": E.check_vectors(lambda a: interp.run(comp, comp.inputs, a), name)}
    env = {**os.environ, "PYTHONPATH": str(ROOT)}
    secs, rc, log = E.timed(KILL + EFCH_CLI + ["lang", "verify", str(prog), str(E.CORPUS / d / "spec.efch"),
                                         "--smt-segundos", "60"], env=env)
    (out / "efch-verify.txt").write_text(log)
    m = re.search(r"⇒ (\w+)", log)
    state = m.group(1) if m else "desconocido"
    row["verificacion"] = {"estado": state, "segundos": secs, "codigo": rc,
                           "detalle": None if m else f"sin veredicto (código {rc}); fase no registrada",
                           "herramienta": ("CBMC" if "CBMC" in log and "probado" in log.split("CBMC")[-1][:80]
                                           else "Z3") if m else "desconocida"}
    fname = backend_c.function_name(comp.name, "lang")
    if state == "probado":
        (out / "dif-efch").mkdir(exist_ok=True)
        lib = native.build_library(out / "dif-efch", backend_c.emit_unit([(comp, body, fname)]))
        row["diferencial"] = native.differential(comp, spec_defn, native.bind(lib, comp, fname))
    else:
        row["diferencial"] = interp_differential(comp, spec_defn, body)
    row["lineas"] = {"especificacion": E.spec_lines((E.CORPUS / d / "spec.efch").read_text()),
                     "programa": E.code_lines(text, "//")}
    row["lineas"]["total"] = row["lineas"]["especificacion"] + row["lineas"]["programa"]
    secs2, rc2, log2 = E.timed(KILL + EFCH_CLI + ["check", str(E.CORPUS / d / "spec.efch")], env=env)
    (out / "efch-check-spec.txt").write_text(log2)
    n_comp = len(spec_defn.computations)
    spec_proved = rc2 == 0 and log2.count("✓ probado      semántica bien definida") == n_comp \
        and "desconocido" not in log2 and "refutado" not in log2
    row["solo_especificacion"] = {"estado": "probado" if spec_proved else f"desconocido ({rc2})",
                                  "segundos": secs2, "lineas": row["lineas"]["especificacion"]}
    return row, body, fname


E.efch_part = efch_part


# --- F4: contadores --------------------------------------------------------------------

def dafny_annotations(text):
    """Como en EXP-005, pero solo se excluye la postcondición principal; los invariantes cuentan."""
    pat = re.compile(r"^\s*(invariant|decreases|assert|requires|ensures|ghost|lemma)\b")
    main = re.compile(r"^\s*ensures\s+\w+\s*==\s*Spec\(")
    return sum(1 for l in text.splitlines() if pat.match(l) and not main.match(l))


E.dafny_annotations = dafny_annotations


def c_lines(text):
    """Líneas de C sin comentarios ni `#include`; `*` solo es comentario dentro de un bloque."""
    n, in_block = 0, False
    for line in text.splitlines():
        s = line.strip()
        if in_block:
            in_block = "*/" not in s
            continue
        if s.startswith("/*"):
            in_block = "*/" not in s
            continue
        if not s or s.startswith("//") or s.startswith("#include"):
            continue
        n += 1
    return n


# --- F1 y F5: medición ---------------------------------------------------------------

def measure(d, spec_defn, comp, out, lang_body, lang_fname, c_fname, rust_fname, rust_static, go_runner,
            efch_ok, spec_ok, sub="medicion"):
    fspec = backend_c.function_name(comp.name)
    parts = ([(comp, comp.semantics, fspec)] if spec_ok else []) + ([(comp, lang_body, lang_fname)] if efch_ok else [])
    names = ([fspec] if spec_ok else []) + ([lang_fname] if efch_ok else []) + [c_fname, rust_fname]
    mdir = out / sub
    mdir.mkdir(exist_ok=True)
    results, _ = native.benchmark(mdir, comp, spec_defn, backend_c.emit_unit(parts) if parts else "", names,
                                  E.CORPUS / d / "baseline.c", extra_objects=[rust_static], link_flags=E.RUST_LINK)
    labels = {fspec: "especificacion", lang_fname: "efch_lang", c_fname: "c_a_mano", rust_fname: "rust"}
    res = {labels[f]: r for f, r in results.items()}
    res["go"] = {}
    seeds, _, _ = workload.parse(comp, spec_defn)
    for seed in seeds:
        proc = subprocess.run([str(go_runner), "bench", str(mdir / f"carga-{seed}.bin"), "15"],
                              capture_output=True, text=True, check=True)
        r = json.loads(proc.stdout)
        res["go"][str(seed)] = {k: round(r[k], 3) for k in ("mediana", "min", "max")}
    return res


def run_function(d, name, gofunc, out_root):
    out = out_root / d
    out.mkdir(parents=True, exist_ok=True)
    spec_defn = E.load_spec(d)
    comp = spec_defn.computations[name]
    row = {"computacion": name, "fuente": E.vectors()[name]["fuente"]}
    row["efch"], body, lang_fname = efch_part(d, name, spec_defn, comp, out)
    row["c"], c_fname = E.c_part(d, name, spec_defn, comp, out)
    row["c"]["lineas_exp007"] = row["c"]["lineas"]
    row["c"]["lineas"] = c_lines((E.CORPUS / d / "baseline.c").read_text())
    row["rust_kani"], rust_fname, rust_static = E.rust_part(d, name, spec_defn, comp, out)
    row["dafny"] = E.dafny_part(d, name, spec_defn, comp, out)
    row["go"], go_runner = E.go_part(d, name, gofunc, spec_defn, comp, out)
    rng = random.Random(20261020)
    row["integridad_indefinidas"] = {
        "diferencial_nativo": undefined_count(comp, workload.edge_inputs(comp, rng, 3000)
                                              + workload.generate(comp, spec_defn, 20261020, 2000)),
        "diferencial_externo": undefined_count(comp, E.differential_inputs(comp, spec_defn))}
    efch_ok = row["efch"]["verificacion"]["estado"] == "probado"
    spec_ok = row["efch"]["solo_especificacion"]["estado"] == "probado"
    args = (d, spec_defn, comp, out, body, lang_fname, c_fname, rust_fname, rust_static, go_runner, efch_ok, spec_ok)
    row["medicion_ns_op"] = measure(*args)
    row["ns_op"] = {k: E.mean_median(v) for k, v in row["medicion_ns_op"].items()}
    row["ns_op_por_estrato"] = {}
    for s in STRATA:
        _stratum["activo"] = s
        try:
            per = measure(*args, sub=f"medicion-{s}")
        finally:
            _stratum["activo"] = None
        row["ns_op_por_estrato"][s] = {k: E.mean_median(v) for k, v in per.items()}
    for f in (rust_static, out / f"lib{d}-rust.so"):
        f.unlink(missing_ok=True)
    return row


E.run_function = run_function


# --- F3: criterios siempre completos -----------------------------------------------------------

def criteria(row):
    res = {}
    e = row["efch"]
    integrity_bad = any(row[k]["vectores_fallidos"] or row[k]["diferencial"]["fallos"]
                        for k in ("efch", "c", "rust_kani", "dafny", "go")) or e["especificacion_vectores_fallidos"] \
        or any(row["integridad_indefinidas"].values())
    res["D0"] = {"cumple": not integrity_bad, "indefinidas": row["integridad_indefinidas"],
                 "especificacion_vectores_fallidos": e["especificacion_vectores_fallidos"]}
    res["D1"] = {"valor": "revisión manual: ver la ficha (estado empaquetado y límite de recursión)", "cumple": None}
    ok = lambda k: row[k]["verificacion"]["estado"] == "probado"
    res["D2"] = {"valor": e["verificacion"], "cumple": ok("efch")}
    if "efch_lang" in row["ns_op"]:
        ratio = row["ns_op"]["efch_lang"] / row["ns_op"]["c_a_mano"]
        res["D3"] = {"efch_lang_sobre_c": round(ratio, 3), "cumple": ratio <= 1.25}
    else:
        res["D3"] = {"valor": "no comprobado: el C de EFCH no se ejecuta sin «probado» (F1)", "cumple": False}
    d4 = {}
    for k in ("rust_kani", "dafny"):
        effort = e["lineas"]["total"] / row[k]["lineas"]
        a, b = effort <= 0.80, ok("efch") and not ok(k)
        c = ok("efch") and ok(k) and e["verificacion"]["segundos"] <= 0.5 * row[k]["verificacion"]["segundos"]
        d4[k] = {"esfuerzo_relativo": round(effort, 3), "a": a, "b": b, "c": c, "cumple": a or b or c}
    res["D4"] = {**d4, "cumple": all(v["cumple"] for v in d4.values())}
    dspec = row["dafny"]["solo_especificacion"]["lineas"]
    applies = dspec <= e["lineas"]["total"]
    if "dafny_espec_go" in row and "efch_lang" in row["ns_op"]:
        q = row["ns_op"]["efch_lang"] / row["dafny_espec_go"]["ns_op"]
        res["D5"] = {"aplica": applies, "lineas_dafny_spec": dspec, "efch_lang_sobre_dafny_spec_go": round(q, 3),
                     "cumple": (not applies) or q <= 0.1}
    else:
        res["D5"] = {"aplica": applies, "valor": "medición ausente", "cumple": not applies}
    decided = [v["cumple"] for k, v in res.items() if k != "D1"]
    res["decision"] = "pendiente de D1 (revisión manual)" if all(decided) else "no cumplido"
    return res


def _no_exp005_criteria(rows):
    return {"nota": "sustituidos por D0–D5 de EXP-008 (criteria de exp008.py)"}


def _minimal_report(ev):
    return "# EXP-008 (nombre DNS, segunda escritura)\n"


def equivalence_with_exp007(out):
    """Intento de equivalencia (Z3) entre la especificación nueva y la de EXP-007, prometido en la ficha."""
    from efch import smt
    import time
    t0 = time.perf_counter()
    try:
        r = smt.check_equivalence(spec(OLD), spec().semantics, 600).as_dict()
    except Exception as e:  # se registra
        r = {"estado": "desconocido", "detalle": repr(e)[:300]}
    r["segundos"] = round(time.perf_counter() - t0, 1)
    return r


def exp007_efforts():
    """Esfuerzos de EXP-007 recalculados con los contadores F4 (solo referencia; la ficha lo promete)."""
    d = ROOT / "ejemplos" / "corpus-g2" / "dns"
    efch = E.spec_lines((d / "spec.efch").read_text()) + E.code_lines((d / "prog.efl").read_text(), "//")
    dfy = (d / "impl.dfy").read_text()
    return {"efch_total": efch, "c_lineas": c_lines((d / "baseline.c").read_text()),
            "dafny_lineas": E.code_lines(dfy, "//"), "dafny_anotaciones": dafny_annotations(dfy)}


def cmd_todo(args):
    E.criteria, E.report_md = _no_exp005_criteria, _minimal_report
    E.cmd_todo(args)
    out = (ROOT / args.salida).resolve()
    ev = json.loads((out / "evidencia.json").read_text())
    row = ev["funciones"]["dns"]
    if "efch_lang" in row["ns_op"]:
        try:
            row["dafny_espec_go"] = X.d5_dafny_go(out, row)
        except Exception as e:  # se registra; D5 no cumple (F3)
            row["dafny_espec_go_error"] = repr(e)
    out_eq = equivalence_with_exp007(out)
    row["especificacion_equivale_exp007"] = out_eq
    row["esfuerzos_exp007_contadores_f4"] = exp007_efforts()
    ev["criterios"] = criteria(row)
    import hashlib
    for p in ("experimentos/exp008.py", "experimentos/exp008_efch.py", "experimentos/exp007.py",
              "experimentos/exp005.py", "experimentos/exp005_dafny_rendimiento.py"):
        ev["huellas_sha256"][p] = hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
    (out / "evidencia.json").write_text(json.dumps(ev, ensure_ascii=False, indent=2, default=str))
    report = "# EXP-008 (nombre DNS, segunda escritura)\n\n" + "\n".join(
        f"- {k}: {json.dumps(row.get(k), ensure_ascii=False, default=str)}"
        for k in ("ns_op", "ns_op_por_estrato", "especificacion_equivale_exp007", "esfuerzos_exp007_contadores_f4"))
    report += "\n```json\n" + json.dumps(ev["criterios"], ensure_ascii=False, indent=2, default=str) + "\n```\n"
    (out / "informe.md").write_text(report)
    print(json.dumps(ev["criterios"], ensure_ascii=False, indent=2, default=str))
    return 0


def cmd_diferencial_spec(n=20000, seed=20261022):
    """La especificación nueva y la de EXP-007 dan lo mismo en el intérprete (evidencia, no prueba)."""
    new, old = spec(), spec(OLD)
    rng = random.Random(seed)
    diffs = []
    for i in range(n):
        b = X.structured_name(rng) if i % 2 else tuple(rng.getrandbits(8) for _ in range(rng.randint(0, 64)))
        a, o = interp.run(new, new.inputs, [b]), interp.run(old, old.inputs, [b])
        if a != o:
            diffs.append({"b": bytes(b).hex(), "nueva": a, "exp007": o})
    print(json.dumps({"casos": n, "diferencias": len(diffs), "primeras": diffs[:5]}, ensure_ascii=False))
    return 1 if diffs else 0


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "diferencial-spec":
        return cmd_diferencial_spec()
    if len(sys.argv) > 1 and sys.argv[1] == "todo":
        import argparse
        ap = argparse.ArgumentParser()
        ap.add_argument("orden")
        ap.add_argument("--salida", default="resultados/exp-008")
        ap.add_argument("--solo")
        return cmd_todo(ap.parse_args())
    return E.main()


def _in_big_stack(fn):
    """El traductor 0.1 es recursivo (continuaciones): con 64 vueltas y guardas supera el límite por
    defecto de Python. Se ejecuta en un hilo con pila grande y límite de recursión alto (adenda)."""
    sys.setrecursionlimit(200000)
    threading.stack_size(512 * 1024 * 1024)
    box = {}
    t = threading.Thread(target=lambda: box.update(r=fn()))
    t.start()
    t.join()
    return box.get("r", 1)


if __name__ == "__main__":
    sys.exit(_in_big_stack(main))
