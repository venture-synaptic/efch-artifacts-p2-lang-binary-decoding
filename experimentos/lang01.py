"""
EXP-004: primer prototipo vertical de EFCH Lang (manifiesto v0.5, §24.1).

    python3 experimentos/lang01.py --salida resultados/lang-0.1-prototipo
    python3 experimentos/lang01.py --salida resultados/lang-0.1-prototipo-O3 --cflags="-O3 -march=native"

Para cada ejemplo (programa EFCH Lang + especificación en el lenguaje de investigación):
1. ruta ordinaria: traducción al núcleo, buena definición y C, con su tiempo;
2. ruta de investigación: equivalencia con la especificación (Z3 y, si no termina, CBMC);
3. pruebas diferenciales del C generado frente al intérprete;
4. medición ns/op del C de EFCH Lang, del C de la especificación y de la línea base escrita a mano;
5. tamaño del fuente (líneas no vacías ni de comentario).
"""

import argparse
import json
import pathlib
import platform
import re
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from efch import backend_c, cbmc, core, lang, native, pipeline  # noqa: E402

EXAMPLES = [
    ("varint", "ejemplos/lang/varint.efl", "ejemplos/varint.efch", "varint-decode"),
    ("trama", "ejemplos/lang/trama.efl", "ejemplos/trama.efch", "trama-decode"),
]


def source_lines(path, comment):
    """Líneas con código: sin vacías ni solo-comentario."""
    n = 0
    for line in pathlib.Path(path).read_text().splitlines():
        s = line.strip()
        if s and not s.startswith(comment) and not s.startswith("/*") and not s.startswith("*"):
            n += 1
    return n


def c_function_lines(path, name):
    text = pathlib.Path(path).read_text()
    start = text.index(name)
    start = text.rfind("\n", 0, start) + 1
    depth, i = 0, text.index("{", start)
    while True:
        depth += {"{": 1, "}": -1}.get(text[i], 0)
        if depth == 0:
            break
        i += 1
    body = text[start:i + 1]
    return sum(1 for l in body.splitlines() if l.strip() and not l.strip().startswith(("/*", "*", "//")))


def spec_semantics_lines(spec_path, comp_name):
    text = pathlib.Path(spec_path).read_text()
    m = re.search(rf"\(computation {re.escape(comp_name)}\b", text)
    sem = text.index("(semantics", m.start())
    depth, i = 0, sem
    while True:
        depth += {"(": 1, ")": -1}.get(text[i], 0)
        if depth == 0:
            break
        i += 1
    return sum(1 for l in text[sem:i + 1].splitlines() if l.strip() and not l.strip().startswith(";"))


def run_example(name, prog, spec_path, comp_name, out):
    d = out / name
    d.mkdir(parents=True, exist_ok=True)
    text = (ROOT / prog).read_text()
    spec = core.load_definition((ROOT / spec_path).read_text(), str(ROOT / spec_path))
    comp = spec.computations[comp_name]
    row = {"programa": prog, "especificacion": spec_path, "computacion": comp_name}

    # 1. Ruta ordinaria (núcleo → buena definición → C → gcc), sin LLM.
    t0 = time.perf_counter()
    core_text = lang.core_definition_text(text, prog)
    t_translate = time.perf_counter() - t0
    defn = core.load_definition(core_text)
    own = next(iter(defn.computations.values()))
    t1 = time.perf_counter()
    report = pipeline.check_definition(defn, 60)
    t_wd = time.perf_counter() - t1
    unit = backend_c.emit_unit([(own, own.semantics, "efch_lang_ordinaria")])
    (d / "ordinaria.c").write_text(unit)
    t2 = time.perf_counter()
    native._gcc(["-c", "ordinaria.c", "-o", "ordinaria.o"], d)
    t_gcc = time.perf_counter() - t2
    (d / "nucleo.efch").write_text(core_text)
    row["ruta_ordinaria"] = {
        "bien_definida": report["computaciones"][own.name]["bien_definida"]["estado"],
        "segundos": {"traduccion_y_elaboracion": round(t_translate + (t1 - t0 - t_translate), 3),
                     "buena_definicion_smt": round(t_wd, 3), "gcc": round(t_gcc, 3)},
        "nodos_nucleo": core.node_count(own.semantics),
        "nodos_especificacion": core.node_count(comp.semantics),
        "lineas_c_generado": unit.count("\n")}

    # 2. Ruta de investigación: equivalencia con la especificación.
    [(cand, _, obligations, status)] = lang.verify(text, spec, prog, smt_seconds=30)
    (d / "candidatas.efch").write_text(lang.candidates_text(text, spec, prog))
    row["verificacion"] = {"estado": status, "obligaciones": obligations, "identidad": cand.identity(comp)}

    # 3. Pruebas diferenciales del C generado frente al intérprete de la especificación.
    fname = backend_c.function_name(comp.name, "lang")
    (d / "dif").mkdir(exist_ok=True)
    lib = native.build_library(d / "dif", backend_c.emit_unit([(comp, cand.body, fname)]))
    row["diferencial"] = native.differential(comp, spec, native.bind(lib, comp, fname))

    # 4. Medición (juntas e intercaladas: especificación, EFCH Lang y línea base a mano).
    fspec = backend_c.function_name(comp.name)
    base = f"baseline_{backend_c.c_ident(comp.name)}"
    bench_unit = backend_c.emit_unit([(comp, comp.semantics, fspec), (comp, cand.body, fname)])
    baseline = (pathlib.Path(spec.path).parent / spec.baseline_c) if spec.baseline_c else None
    names = [fspec, fname] + ([base] if baseline else [])
    (d / "medicion").mkdir(exist_ok=True)
    results, sizes = native.benchmark(d / "medicion", comp, spec, bench_unit, names, baseline)
    labels = {fspec: "especificacion", fname: "efch_lang", base: "linea_base_c"}
    row["medicion_ns_op"] = {labels[f]: r for f, r in results.items()}
    row["tamano_codigo_bytes"] = {labels[f]: s for f, s in sizes.items()}

    # 5. Tamaño del fuente.
    row["lineas_fuente"] = {"efch_lang": source_lines(ROOT / prog, "//"),
                            "especificacion_semantica": spec_semantics_lines(ROOT / spec_path, comp_name)}
    if baseline:
        row["lineas_fuente"]["linea_base_c"] = c_function_lines(baseline, base)
    return row


def report_md(ev):
    lines = ["# EXP-004: prototipo vertical de EFCH Lang 0.1", "",
             f"Fecha: {ev['fecha']}. gcc: {ev['entorno']['gcc']}, `{' '.join(ev['entorno']['cflags'])}`. CPU: {ev['entorno']['cpu']}.", "",
             "| Ejemplo | Equivalencia | Diferencial | ns/op EFCH Lang | ns/op especificación | ns/op C a mano | "
             "Líneas EFCH Lang | Líneas C a mano | Ruta ordinaria (s) |",
             "|---|---|---|---|---|---|---|---|---|"]
    for name, r in ev["ejemplos"].items():
        m = r["medicion_ns_op"]
        mean = lambda k: round(sum(v["mediana"] for v in m[k].values()) / len(m[k]), 2) if k in m else "—"
        via = [o["obligacion"] for o in r["verificacion"]["obligaciones"] if o["estado"] == "probado"]
        tool = "CBMC" if any("CBMC" in v for v in via) else "Z3"
        ro = r["ruta_ordinaria"]["segundos"]
        lines.append(f"| {name} | {r['verificacion']['estado']} ({tool}) | {r['diferencial']['fallos']}/{r['diferencial']['casos']} fallos | "
                     f"{mean('efch_lang')} | {mean('especificacion')} | {mean('linea_base_c')} | "
                     f"{r['lineas_fuente']['efch_lang']} | {r['lineas_fuente'].get('linea_base_c', '—')} | "
                     f"{round(sum(ro.values()), 2)} |")
    lines += ["", "ns/op: media de las medianas por semilla. Las pruebas diferenciales son evidencia "
              "experimental; la equivalencia es formal con los supuestos de cada herramienta."]
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--salida", default="resultados/lang-0.1-prototipo")
    ap.add_argument("--cflags", help='optimización de gcc, p. ej. "-O3 -march=native" (por defecto -O2)')
    args = ap.parse_args()
    if args.cflags:
        native.set_optimization(args.cflags.split())
    out = ROOT / args.salida
    out.mkdir(parents=True, exist_ok=True)
    cpu = next((l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name")), "?")
    ev = {"fecha": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
          "entorno": {"gcc": native.compiler_version(), "cpu": cpu, "python": platform.python_version(),
                      "cbmc": cbmc.version() if cbmc.CBMC.exists() else None,
                      "cflags": native.CFLAGS},
          "ejemplos": {}}
    for name, prog, spec, comp in EXAMPLES:
        print(f"== {name}", flush=True)
        ev["ejemplos"][name] = run_example(name, prog, spec, comp, out)
        print(json.dumps({k: ev["ejemplos"][name][k] for k in ("verificacion", "medicion_ns_op", "lineas_fuente")},
                         ensure_ascii=False, default=str)[:900], flush=True)
    (out / "evidencia.json").write_text(json.dumps(ev, ensure_ascii=False, indent=2, default=str))
    (out / "informe.md").write_text(report_md(ev))
    print(report_md(ev))


if __name__ == "__main__":
    main()
