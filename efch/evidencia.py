"""
Exportación de la evidencia de verificación con el contrato versionado `efch-evidencia/1.0`
(contracts/evidencia/1.0/README.md; EXP-016, puerta G5).

    python3 -m efch export check DEF.efch -o evidencia.json
    python3 -m efch export lang  PROG.efl ESPEC.efch -o evidencia.json
"""

import hashlib
import json
import pathlib

from . import core, lang, pipeline

FORMATO, VERSION = "efch-evidencia", "1.0"
ROOT = pathlib.Path(__file__).resolve().parent.parent
HERRAMIENTA = "Z3 (efch.smt)"
HERRAMIENTA_CBMC = "CBMC (efch.cbmc)"


def canonical_json(obj):
    """Serialización canónica de R2: claves ordenadas por punto de código, sin espacios, UTF-8 sin escapar."""
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")


def seal(doc):
    body = {k: v for k, v in doc.items() if k != "huella"}
    return {**body, "huella": hashlib.sha256(canonical_json(body)).hexdigest()}


def package_fingerprint():
    h = hashlib.sha256()
    for p in sorted((ROOT / "efch").glob("*.py")):
        h.update(p.name.encode() + b"\0" + hashlib.sha256(p.read_bytes()).digest())
    return h.hexdigest()


def _rel(path):
    p = pathlib.Path(path).resolve()
    try:
        return p.relative_to(ROOT).as_posix()
    except ValueError:
        return p.name


def _source(path):
    return {"ruta": _rel(path), "sha256": hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()}


def _ms(secs):
    return None if secs is None else max(0, int(round(float(secs) * 1000)))


def _cex(c):
    if c is None:
        return None
    return c if isinstance(c, dict) and c else {"valor": c}


HERRAMIENTAS = {"z3": HERRAMIENTA, "cbmc": HERRAMIENTA_CBMC}


def _herramienta(r):
    """Por el campo tipado `herramienta` (pipeline.verify_candidate), no por el texto (D10). Residuo declarado
    (resultados/identidad-v2/dudas.md, D-8): las obligaciones que añade lang.verify (equivalencia por casos y por
    CBMC) no llevan ese campo y tiparlas exige cambiar efch/lang.py, cuya huella fija el oráculo de D-S1-2; para
    ellas se mantiene la regla anterior («(CBMC)» en el nombre, Codex Astra, EXP-016). Las de smt son de Z3."""
    if "herramienta" in r:
        return r["herramienta"]
    return "cbmc" if "(CBMC)" in (r.get("obligacion") or "") else "z3"


def _clase_lang(o):
    """Clase de una obligación de lang.verify: el campo tipado de pipeline.verify_candidate (buena definición o
    equivalencia); las que lang.verify añade después son, por su contrato, equivalencias (por casos o CBMC)."""
    return o.get("clase", "equivalencia")


def _obl(oid, clase, r):
    estado = r["estado"]
    cex = _cex(r.get("contraejemplo")) if estado == "refutado" else None
    detalle = r.get("detalle") or ""
    if estado == "desconocido" and not detalle:
        detalle = "sin motivo registrado"
    herramienta = HERRAMIENTAS[_herramienta(r)]
    return {"id": oid, "clase": clase, "estado": estado, "herramienta": herramienta,
            "milisegundos": _ms(r.get("segundos")), "detalle": detalle, "contraejemplo": cex}


def verdict(subjects):
    states = [o["estado"] for s in subjects for o in s["obligaciones"] if o["estado"] != "fuera de alcance"]
    for s in ("refutado", "desconocido", "no comprobado"):
        if s in states:
            return s
    return "probado" if states else "no comprobado"


def document(sources, subjects):
    doc = {"formato": FORMATO, "version": VERSION,
           "generador": {"nombre": "efch", "version": "0.1", "huella_paquete": package_fingerprint()},
           "fuentes": [_source(p) for p in sources], "sujetos": subjects, "veredicto": verdict(subjects)}
    return seal(doc)


def from_check(path, smt_seconds=None):
    defn = core.load_definition(pathlib.Path(path).read_text(), str(path))
    report = pipeline.check_definition(defn, smt_seconds)
    subjects = []
    for name, info in report["computaciones"].items():
        obls = [_obl("buena-definicion", "buena-definicion", info["bien_definida"])]
        for k, inv in enumerate(info.get("invariantes", [])):
            obls.append(_obl(f"invariante-{k}", "invariante", inv))
        subjects.append({"tipo": "computacion", "nombre": name, "identidad": info["identidad"],
                         "obligaciones": obls, "supuestos": list(info.get("supuestos", []))})
    for p in report["propiedades"]:
        subjects.append({"tipo": "propiedad", "nombre": p["nombre"], "identidad": None,
                         "obligaciones": [_obl("verdad", "propiedad", p)], "supuestos": []})
    return document([path], subjects)


def from_lang(prog, spec_path, smt_seconds=None):
    text = pathlib.Path(prog).read_text()
    spec = core.load_definition(pathlib.Path(spec_path).read_text(), str(spec_path))
    subjects = []
    for cand, comp, obligations, _status in lang.verify(text, spec, str(prog), smt_seconds):
        obls = []
        for k, o in enumerate(obligations):
            clase = _clase_lang(o)      # campo tipado (D10); antes se deducía de la frase «equivalente»
            obls.append(_obl(f"{clase}-{k}", clase, o))
        subjects.append({"tipo": "candidata", "nombre": f"{cand.name} implementa {comp.name}",
                         "identidad": cand.identity(comp), "obligaciones": obls,
                         "supuestos": [f"semántica del núcleo EFCH 0.1 (efch/interp.py y efch/smt.py)",
                                       f"traducción de EFCH Lang (efch/lang.py)", "corrección de Z3"]})
    return document([prog, spec_path], subjects)
