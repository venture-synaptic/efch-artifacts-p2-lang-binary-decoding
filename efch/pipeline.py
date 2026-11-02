"""
Canalización de EFCH (un SCSV): definición → candidatas → verificación formal →
materialización en C → pruebas diferenciales → medición → selección → evidencia.

Reglas de aceptación (manifiesto v0.4, §4, §8.1 y §19.2):
- Solo es elegible una candidata cuya buena definición y equivalencia con la
  semántica estén *probadas* por SMT y cuya traducción a C no haya sido
  *refutada* por las pruebas diferenciales.
- La IA solo propone; el veredicto es del verificador.
- Si se agota el presupuesto o no hay candidata elegible, se dice explícitamente.
"""

import hashlib
import json
import pathlib
import platform
import re
import statistics
import time

from . import VERSION, backend_c, core, llm, native, smt
from ._z3 import VERSION as Z3_VERSION

DOCS = pathlib.Path(__file__).resolve().parent.parent / "docs" / "lenguaje-efch-0.1.md"


def environment():
    cpu = platform.processor() or "desconocido"
    try:
        for line in pathlib.Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                cpu = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    return {"efch": VERSION, "lenguaje": f"EFCH {core.LANGUAGE_VERSION}", "python": platform.python_version(),
            "z3": Z3_VERSION, "compilador": native.compiler_version(), "opciones_c": native.CFLAGS,
            "sistema": platform.platform(), "cpu": cpu}


def assumptions(comp):
    dom = ", ".join(f"{n}: {core.type_str(t)}" for n, t in comp.inputs)
    return [f"semántica del núcleo EFCH {core.LANGUAGE_VERSION} (efch/interp.py y efch/smt.py)",
            f"dominio declarado: {dom}",
            f"corrección de Z3 {Z3_VERSION}"]


# --- Comprobación de una definición --------------------------------------------

def check_definition(defn, smt_seconds=None):
    report = {"computaciones": {}, "propiedades": []}
    for comp in defn.computations.values():
        t = smt_seconds or comp.budget["smt-seconds"]
        r = smt.check_well_defined("semántica bien definida", comp.semantics, comp.inputs, t)
        report["computaciones"][comp.name] = {
            "identidad": comp.identity(), "nodos": core.node_count(comp.semantics),
            "firma": comp.signature(), "bien_definida": r.as_dict(), "supuestos": assumptions(comp),
            "invariantes": [x.as_dict() for x in smt.check_fold_invariants(comp.semantics, comp.inputs, t)]}
    for prop in defn.properties:
        names = property_closure(defn, prop)
        t = smt_seconds or max([defn.computations[n].budget["smt-seconds"] for n in names] or
                               [core.DEFAULT_BUDGET["smt-seconds"]])
        report["propiedades"].append({"nombre": prop.name, **smt.check_property(prop, t).as_dict()})
    return report


def property_closure(defn, prop):
    """Computaciones del cierre de dependencias de una propiedad: las listas `(call NOMBRE …)` de su fuente, como
    árbol (identidad.llamadas, §2.2), cerradas transitivamente en la definición y en el orden de esta. Antes se
    buscaban con `\\(call NOMBRE\\b` en el texto, que omite `f-` y solo veía las llamadas directas (D7)."""
    from . import identidad
    vistos, pila = set(), list(identidad.llamadas(prop.source))
    while pila:
        n = pila.pop()
        if n in vistos or n not in defn.computations:
            continue
        vistos.add(n)
        pila.extend(identidad.llamadas(defn.computations[n].source))
    return [n for n in defn.computations if n in vistos]


# --- Verificación de una candidata ---------------------------------------------

def verify_candidate(comp, body, smt_seconds):
    wd = smt.check_well_defined("candidata bien definida", body, comp.inputs, smt_seconds)
    # `clase` y `herramienta` son campos tipados de cada obligación: quien los lee no analiza su texto (D10).
    wd_d = {**wd.as_dict(), "clase": "buena-definicion", "herramienta": "z3"}
    if wd.status == "refutado":
        return {"estado": "refutado", "obligaciones": [wd_d]}
    eq = smt.check_equivalence(comp, body, smt_seconds)
    obligations = [wd_d, {**eq.as_dict(), "clase": "equivalencia", "herramienta": "z3"}]
    statuses = {wd.status, eq.status}
    status = "refutado" if "refutado" in statuses else ("probado" if statuses == {"probado"} else "desconocido")
    return {"estado": status, "obligaciones": obligations}


# --- Retroalimentación y prompts -----------------------------------------------

SYSTEM = (
    "Eres el motor de propuesta de un sistema de computación sintética verificable. "
    "Recibes la referencia de un lenguaje de especificación y una definición, y propones "
    "una implementación alternativa escrita en ese mismo lenguaje. Un verificador formal "
    "independiente decide si es correcta. Respondes únicamente con un bloque ```efch``` "
    "que contiene la candidata."
)


def build_prompt(defn_text, comp, history, context):
    parts = [
        "Referencia del lenguaje:\n\n" + DOCS.read_text(),
        "Definición (fuente de verdad):\n```efch\n" + defn_text + "\n```",
        f"Tarea: propón una candidata para `{comp.name}` con esta forma exacta:\n"
        f"```efch\n(efch 0.1\n  (candidate NOMBRE (implements {comp.name})\n    (body EXPR)))\n```",
        "La candidata se compila a C con gcc -O2 y se mide con la carga declarada. Objetivo: que sea "
        "observablemente equivalente a la semántica en todo el dominio y que minimice los ns por llamada. "
        "A igualdad de tiempo, mejor cuanto menos código. Solo puedes usar las construcciones de la "
        "referencia. Las expresiones muy grandes pueden agotar el tiempo del verificador.",
        context,
    ]
    for i, (text, feedback) in enumerate(history, 1):
        parts.append(f"Intento {i}:\n```efch\n{text}\n```\nResultado:\n{feedback}")
    if history:
        parts.append("Propón una nueva candidata completa teniendo en cuenta los resultados.")
    return "\n\n".join(parts)


def extract_efch(text):
    blocks = re.findall(r"```(?:efch|lisp|scheme)?\n(.*?)```", text, re.S)
    return blocks[-1].strip() if blocks else None


def _describe(entry, measurements, best_id):
    v = entry.get("verificacion")
    if entry.get("error"):
        return f"NO APLICABLE: {entry['error']}"
    if v["estado"] == "refutado":
        bad = next(o for o in v["obligaciones"] if o["estado"] == "refutado")
        return (f"REFUTADA ({bad['obligacion']}). Contraejemplo: {json.dumps(bad['contraejemplo'])}. "
                f"{bad['detalle']}")
    if v["estado"] == "desconocido":
        unk = next(o for o in v["obligaciones"] if o["estado"] == "desconocido")
        return f"DESCONOCIDA: {unk['obligacion']} no se decidió ({unk['detalle']}). Simplifica la expresión."
    m = entry.get("materializacion", {})
    if m.get("estado") == "refutado":
        return f"PROBADA en el núcleo, pero su traducción a C falló pruebas diferenciales: {m['contraejemplos'][:1]}"
    ns = lambda k: _mean(measurements[k]) if k in measurements else None
    parts = [f"PROBADA (bien definida y equivalente para todo el dominio). Medición en las mismas condiciones, "
             f"mediana de ns/op: esta candidata {ns(entry['id'])}; semántica directa {ns('semantica')}"]
    if "linea-base" in measurements:
        parts.append(f"; línea base en C escrita a mano {ns('linea-base')}")
    if best_id and best_id != entry["id"]:
        parts.append(f"; mejor candidata hasta ahora {ns(best_id)}")
    parts.append(f". Tamaño de código: {entry.get('tamano_codigo')} bytes.")
    return "".join(parts)


def _mean(per_seed):
    return round(statistics.mean(m["mediana"] for m in per_seed.values()), 3)


# --- Ejecución -----------------------------------------------------------------

class Synthesis:
    def __init__(self, defn, defn_text, comp_name, out_dir, log=print):
        if comp_name not in defn.computations:
            raise core.EFCHError(f"la definición no tiene la computación {comp_name}")
        self.defn, self.defn_text = defn, defn_text
        self.comp = defn.computations[comp_name]
        self.out = pathlib.Path(out_dir).resolve()
        (self.out / "candidatas").mkdir(parents=True, exist_ok=True)
        (self.out / "c").mkdir(exist_ok=True)
        self.log = log
        self.entries = []
        self.measurements = {}
        self.sizes = {}
        self.spent = {"llamadas": 0, "usd": 0.0, "segundos": 0.0, "agotado": None}
        self.baseline = None
        if defn.baseline_c:
            path = pathlib.Path(defn.path or ".").parent / defn.baseline_c
            if f"baseline_{backend_c.c_ident(self.comp.name)}" in path.read_text():
                self.baseline = path

    @property
    def budget(self):
        return self.comp.budget

    def add(self, cid, origin, text):
        """Elabora, verifica y (si procede) materializa una candidata."""
        entry = {"id": cid, "origen": origin, "fuente": text}
        self.entries.append(entry)
        try:
            cands = core.load_candidates(text, self.defn, origin)
            cand = next(c for c in cands if c.implements == self.comp.name)
        except (core.EFCHError, StopIteration) as e:
            entry["error"] = str(e) if not isinstance(e, StopIteration) else f"no implementa {self.comp.name}"
            entry["verificacion"] = {"estado": "no_aplicable", "obligaciones": []}
            self.log(f"   {cid}: no aplicable: {entry['error'][:120]}")
            return entry
        entry["identidad"] = cand.identity(self.comp)
        entry["nodos"] = core.node_count(cand.body)
        entry["_body"] = cand.body
        (self.out / "candidatas" / f"{cid}.efch").write_text(text + "\n")
        (self.out / "candidatas" / f"{cid}.efir").write_text(
            f"; identidad {entry['identidad']}\n{cand.canonical(self.comp)}\n")
        t0 = time.perf_counter()
        entry["verificacion"] = verify_candidate(self.comp, cand.body, self.budget["smt-seconds"])
        entry["verificacion"]["segundos"] = round(time.perf_counter() - t0, 3)
        status = entry["verificacion"]["estado"]
        self.log(f"   {cid}: {status} ({entry['verificacion']['segundos']} s, {entry['nodos']} nodos)")
        if status == "probado":
            self._materialize(entry)
        return entry

    def eligible(self):
        return [e for e in self.entries if e.get("verificacion", {}).get("estado") == "probado"
                and e.get("materializacion", {}).get("estado") != "refutado"]

    def _functions(self, entries):
        return [(self.comp, e["_body"], backend_c.function_name(self.comp.name, e["id"])) for e in entries]

    def _materialize(self, entry):
        unit = backend_c.emit_unit(self._functions([entry]))
        lib = native.build_library(self.out / "c", unit)
        call = native.bind(lib, self.comp, backend_c.function_name(self.comp.name, entry["id"]))
        entry["materializacion"] = native.differential(self.comp, self.defn, call)
        if entry["materializacion"]["estado"] == "refutado":
            self.log(f"   {entry['id']}: ¡traducción a C refutada por pruebas diferenciales!")

    def measure(self):
        """Mide juntas, intercaladas, todas las elegibles y la línea base."""
        entries = self.eligible()
        unit = backend_c.emit_unit(self._functions(entries))
        (self.out / "c" / "impl.c").write_text(unit)
        names = {backend_c.function_name(self.comp.name, e["id"]): e["id"] for e in entries}
        if self.baseline:
            names[f"baseline_{backend_c.c_ident(self.comp.name)}"] = "linea-base"
        results, sizes = native.benchmark(self.out / "c", self.comp, self.defn, unit, list(names),
                                          self.baseline)
        self.measurements = {names[f]: r for f, r in results.items()}
        self.sizes = {names[f]: s for f, s in sizes.items()}
        for e in self.entries:
            if e["id"] in self.measurements:
                e["metricas"] = self.measurements[e["id"]]
                e["tamano_codigo"] = self.sizes.get(e["id"])
        return self.best()

    def best(self):
        pool = [e for e in self.eligible() if e["id"] in self.measurements]
        if not pool:
            return None
        return min(pool, key=lambda e: (_mean(self.measurements[e["id"]]), e.get("tamano_codigo") or 0))

    def _budget_exhausted(self):
        b, s = self.budget, self.spent
        if s["llamadas"] >= b["llm-calls"]:
            return f"llamadas ({s['llamadas']}/{b['llm-calls']})"
        if s["usd"] >= b["llm-usd"]:
            return f"coste ({s['usd']:.2f}/{b['llm-usd']} USD)"
        if s["segundos"] >= b["llm-seconds"]:
            return f"tiempo de LLM ({s['segundos']:.0f}/{b['llm-seconds']} s)"
        return None

    def llm_lineage(self, lineage, rounds):
        history = []
        for r in range(rounds):
            reason = self._budget_exhausted()
            if reason:
                self.spent["agotado"] = reason
                self.log(f"   PRESUPUESTO AGOTADO por {reason}")
                return False
            context = self._context()
            prompt = build_prompt(self.defn_text, self.comp, history, context)
            try:
                resp = llm.complete(SYSTEM, prompt)
            except llm.LLMError as e:
                self.log(f"   error del LLM: {e}")
                self.entries.append({"id": f"llm-L{lineage}-R{r}", "origen": "llm", "error_llm": str(e)})
                return True
            self.spent["llamadas"] += 1
            self.spent["usd"] += resp["coste_usd"] or 0
            self.spent["segundos"] += resp["duracion_s"]
            text = extract_efch(resp["texto"]) or resp["texto"]
            entry = self.add(f"llm-L{lineage}-R{r}", "llm", text)
            entry["llamada"] = {k: v for k, v in resp.items() if k != "texto"}
            entry["respuesta"] = resp["texto"]
            if entry["verificacion"]["estado"] == "probado":
                self.measure()
            history.append((text, _describe(entry, self.measurements, (self.best() or {}).get("id"))))
        return True

    def _context(self):
        if not self.measurements:
            return ""
        lines = ["Mediciones actuales (mediana de ns/op, mismas condiciones):"]
        for k, v in sorted(self.measurements.items(), key=lambda kv: _mean(kv[1])):
            lines.append(f"- {k}: {_mean(v)} ns/op" + (f", {self.sizes.get(k)} bytes de código" if self.sizes.get(k)
                                                        else ""))
        return "\n".join(lines)

    def finish(self, started):
        best = self.measure() if self.eligible() else None
        sem = self.measurements.get("semantica")
        base = self.measurements.get("linea-base")
        selection = None
        if best:
            selection = {
                "candidata": best["id"], "identidad": best["identidad"],
                "ns_por_op": _mean(best["metricas"]),
                "frente_a_semantica_directa": round(_mean(sem) / _mean(best["metricas"]), 2) if sem else None,
                "frente_a_linea_base": round(_mean(base) / _mean(best["metricas"]), 2) if base else None,
                "garantia": {
                    "nucleo": "probado: bien definida y observablemente equivalente a la semántica en todo el dominio",
                    "supuestos": assumptions(self.comp),
                    "traduccion_a_c": f"no demostrada; {best['materializacion']['casos']} pruebas diferenciales "
                                      f"sin fallos (evidencia experimental)",
                },
            }
            unit = backend_c.emit_unit([(self.comp, best["_body"], backend_c.function_name(self.comp.name))])
            (self.out / f"{backend_c.c_ident(self.comp.name)}.c").write_text(
                f"/* Generado por EFCH {VERSION} a partir de la candidata {best['id']}.\n"
                f" * Identidad semántica de la computación: {self.comp.identity()}\n"
                f" * Identidad de la candidata: {best['identidad']}\n"
                f" * Garantía: {selection['garantia']['nucleo']}; traducción a C: "
                f"{selection['garantia']['traduccion_a_c']}. */\n" + unit)
        for e in self.entries:
            e.pop("_body", None)
        evidence = {
            "sistema": f"EFCH {VERSION} (SCSV, paradigma POC)", "inicio": started, "entorno": environment(),
            "definicion": {"archivo": self.defn.path,
                           "sha256": hashlib.sha256(self.defn_text.encode()).hexdigest(),
                           "computacion": self.comp.name, "identidad": self.comp.identity(),
                           "firma": self.comp.signature()},
            "presupuesto": self.budget, "presupuesto_agotado": self.spent["agotado"],
            "candidatas": self.entries,
            "medicion": {"metricas": self.measurements, "tamano_codigo": self.sizes,
                         "linea_base": str(self.baseline) if self.baseline else None},
            "seleccion": selection,
            "tasa_probadas": round(sum(e.get("verificacion", {}).get("estado") == "probado" for e in self.entries)
                                   / max(1, len(self.entries)), 3),
            "costo_llm": {k: v for k, v in self.spent.items() if k != "agotado"},
        }
        (self.out / "evidencia.json").write_text(json.dumps(evidence, ensure_ascii=False, indent=2, default=repr))
        (self.out / "informe.md").write_text(report_markdown(evidence))
        return evidence


def report_markdown(ev):
    comp = ev["definicion"]["computacion"]
    lines = [f"# EFCH — {comp}", "",
             f"- Definición: `{ev['definicion']['archivo']}` (sha256 `{ev['definicion']['sha256'][:16]}…`)",
             f"- Identidad semántica: `{ev['definicion']['identidad'][:16]}…`",
             f"- Entorno: {ev['entorno']['compilador']}, Z3 {ev['entorno']['z3']}, Python {ev['entorno']['python']}",
             "", "| Candidata | Origen | Estado formal | Traducción a C | ns/op | Código (bytes) |",
             "|---|---|---|---|---|---|"]
    metrics = ev["medicion"]["metricas"]
    for e in ev["candidatas"]:
        st = e.get("verificacion", {}).get("estado", "error")
        m = e.get("materializacion")
        mat = "—" if not m else (f"refutada ({m['fallos']} fallos)" if m["estado"] == "refutado"
                                 else f"sin fallos ({m['casos']} pruebas)")
        ns = _mean(metrics[e["id"]]) if e["id"] in metrics else "—"
        lines.append(f"| {e['id']} | {e['origen']} | {st} | {mat} | {ns} | {e.get('tamano_codigo') or '—'} |")
    if "linea-base" in metrics:
        lines.append(f"| linea-base | C a mano | no verificable formalmente | — | {_mean(metrics['linea-base'])} | "
                     f"{ev['medicion']['tamano_codigo'].get('linea-base')} |")
    lines.append("")
    sel = ev["seleccion"]
    if sel:
        lines += [f"**Seleccionada:** `{sel['candidata']}` — {sel['ns_por_op']} ns/op; "
                  f"{sel['frente_a_semantica_directa']}× la semántica directa"
                  + (f", {sel['frente_a_linea_base']}× la línea base." if sel["frente_a_linea_base"] else "."),
                  "", f"**Garantía:** {sel['garantia']['nucleo']}. Supuestos: "
                  + "; ".join(sel["garantia"]["supuestos"]) + f". Traducción a C: {sel['garantia']['traduccion_a_c']}."]
    else:
        lines.append("**Sin candidata elegible.**")
    if ev["presupuesto_agotado"]:
        lines.append(f"\n**Presupuesto agotado:** {ev['presupuesto_agotado']}.")
    lines.append(f"\nCoste de LLM: {ev['costo_llm']}.")
    return "\n".join(lines) + "\n"


def synthesize(defn, defn_text, comp_name, out_dir, use_llm=True, lineages=2, rounds=2, extra=(), log=print):
    started = time.strftime("%Y%m%dT%H%M%S")
    syn = Synthesis(defn, defn_text, comp_name, out_dir, log)
    comp = syn.comp
    log(f"Computación {comp.name} (identidad {comp.identity()[:16]}…)")
    wd = smt.check_well_defined("semántica bien definida", comp.semantics, comp.inputs, comp.budget["smt-seconds"])
    if wd.status != "probado":
        raise core.EFCHError(f"la semántica de {comp.name} no está probada como bien definida: {wd.as_dict()}")
    log("Candidatas iniciales")
    syn.add("semantica", "definición",
            f"(efch 0.1 (candidate semantica (implements {comp.name}) (body "
            f"{core.dumps(_semantics_sx(comp))})))")
    for path in extra:
        p = pathlib.Path(path)
        text = p.read_text()
        try:
            cands = [c for c in core.load_candidates(text, defn) if c.implements == comp.name]
        except core.EFCHError:
            cands = None  # se registra como no aplicable con su error
        if not cands:
            syn.add(f"archivo-{p.stem}", f"archivo {p.name}", text)
        for c in cands or ():
            syn.add(f"archivo-{c.name}", f"archivo {p.name}", f"(efch 0.1 {c.source_text})")
    syn.measure()
    if use_llm:
        log(f"Síntesis guiada por LLM ({llm.MODEL}): {lineages} linajes × {rounds} rondas")
        for lineage in range(lineages):
            if not syn.llm_lineage(lineage, rounds):
                break
    return syn.finish(started)


def _semantics_sx(comp):
    sem = next(x for x in comp.source.items if isinstance(x, core.SList) and x.head() == "semantics")
    return sem.items[1]
