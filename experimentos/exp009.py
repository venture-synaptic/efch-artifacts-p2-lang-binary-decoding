"""
EXP-009: pliegue acotado en el núcleo y verificación modular (docs/experimentos/EXP-009.md).

    python3 experimentos/exp009.py vectores
    python3 experimentos/exp009.py todo --salida resultados/exp-009

Reutiliza experimentos/exp008.py (carga en tercios, F1–F7, criterios D0–D5) con el corpus
ejemplos/corpus-g2-v3/. Cambios respecto a exp008.py, todos declarados en la ficha:
- la CLI de EFCH se usa tal cual (`python3 -m efch`), sin el envoltorio de recursión de EXP-008: el
  programa con `fold` se traduce sin él, y así cuenta para D1;
- la comparación con la especificación de EXP-008 es diferencial en el intérprete (la de Z3 sin
  pliegues en los dos lados no terminó en EXP-008 y no forma parte de D0–D5);
- Kani: si su salida dice que CBMC se quedó sin memoria, el estado es «desconocido» (memoria), no
  «refutado» (error de clasificación de exp005.py detectado en EXP-008).
"""

import json
import pathlib
import random
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "experimentos"))

import exp008 as X8  # noqa: E402  (aplica F1–F7 y la carga en tercios sobre exp005)
from exp008 import E, X  # noqa: E402
from efch import core, interp  # noqa: E402

E.CORPUS = ROOT / "ejemplos" / "corpus-g2-v3"
X8.EFCH_CLI = [sys.executable, "-m", "efch"]
V2 = ROOT / "ejemplos" / "corpus-g2-v2" / "dns" / "spec.efch"


def equivalence_with_v2(out, n=20000, seed=20261023):
    """La especificación con fold frente a la de EXP-008 (cadena de 32 let), en el intérprete."""
    new = core.load_definition((E.CORPUS / "dns" / "spec.efch").read_text()).computations[X8.NAME]
    old = core.load_definition(V2.read_text()).computations[X8.NAME]
    rng = random.Random(seed)
    diffs = 0
    for i in range(n):
        b = (X.structured_name, X8.long_name, None)[i % 3]
        b = b(rng) if b else tuple(rng.getrandbits(8) for _ in range(rng.randint(0, 64)))
        diffs += interp.run(new, new.inputs, [b]) != interp.run(old, old.inputs, [b])
    return {"estado": "desconocido", "via": "diferencial en el intérprete (evidencia, no prueba)",
            "casos": n, "diferencias": diffs}


X8.equivalence_with_exp007 = equivalence_with_v2

_rust_part = E.rust_part


def rust_part(d, name, spec_defn, comp, out):
    row, fname, static = _rust_part(d, name, spec_defn, comp, out)
    log = (out / "kani.txt").read_text() if (out / "kani.txt").exists() else ""
    if row["verificacion"]["estado"] == "refutado" and "run out of memory" in log:
        row["verificacion"] = {**row["verificacion"], "estado": "desconocido",
                               "detalle": "CBMC se quedó sin memoria (no es un contraejemplo)"}
    return row, fname, static


E.rust_part = rust_part


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "todo":
        import argparse
        ap = argparse.ArgumentParser()
        ap.add_argument("orden")
        ap.add_argument("--salida", default="resultados/exp-009")
        ap.add_argument("--solo")
        args = ap.parse_args()
        out = X8.cmd_todo(args)
        import hashlib
        ev_path = ROOT / args.salida / "evidencia.json"
        ev = json.loads(ev_path.read_text())
        ev["huellas_sha256"]["experimentos/exp009.py"] = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
        ev_path.write_text(json.dumps(ev, ensure_ascii=False, indent=2, default=str))
        text = ROOT / args.salida / "informe.md"
        if text.exists():
            text.write_text(text.read_text().replace("EXP-008 (nombre DNS, segunda escritura)",
                                                     "EXP-009 (nombre DNS con fold)"))
        return out
    return E.main()


if __name__ == "__main__":
    sys.exit(X8._in_big_stack(main))
