"""
EXP-010: función reservada para el pliegue, opciones de la cabecera TCP (docs/experimentos/EXP-010.md).

    python3 experimentos/exp010.py vectores
    python3 experimentos/exp010.py todo --salida resultados/exp-010

Reutiliza exp009.py → exp008.py → exp007.py → exp005.py con el corpus ejemplos/corpus-g3/ y la
función `tcp-options`. Solo cambian la carga y los nombres; las medidas, F1–F7 y los criterios
D0–D5 son los de EXP-009. Kani sin memoria = `desconocido` (exp009.py).
"""

import json
import pathlib
import random
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "experimentos"))

import exp009  # noqa: E402,F401  (CLI normal, clasificación de Kani)
import exp008 as X8  # noqa: E402
from exp008 import E, X  # noqa: E402
from efch import workload  # noqa: E402

NAME = "tcp-options"
E.CORPUS = ROOT / "ejemplos" / "corpus-g3"
E.FUNCTIONS = [("tcp", NAME, "TcpOptions")]
X.NAME = X8.NAME = NAME

OPTS = [b"\x01", b"\x01", b"\x00", b"\x02\x04\x05\xb4", b"\x02\x04\x22\x38", b"\x03\x03\x07", b"\x03\x03\x0e",
        b"\x04\x02", b"\x08\x0a" + bytes(8), b"\x05\x0a" + bytes(8), b"\x1e\x04\x00\x00"]


def valid_header(rng):
    """Cabecera con opciones bien formadas (sin duplicados) y cola aleatoria."""
    opts, seen = b"", set()
    for _ in range(rng.randint(0, 8)):
        o = rng.choice(OPTS)
        if o[0] in (2, 3, 4) and o[0] in seen:
            continue
        seen.add(o[0])
        if len(opts) + len(o) <= 40:
            opts += o
    doff = 5 + (len(opts) + 3) // 4
    opts += b"\x00" * (4 * (doff - 5) - len(opts))
    fixed = bytes(rng.getrandbits(8) for _ in range(12)) + bytes([doff << 4]) + \
        bytes(rng.getrandbits(8) for _ in range(7))
    return fixed + opts + bytes(rng.getrandbits(8) for _ in range(rng.randint(0, 60 - 20 - len(opts))))


def altered_header(rng):
    """Como valid_header, con una alteración: byte cambiado, truncado o opción duplicada."""
    b = bytearray(valid_header(rng))
    kind = rng.randrange(3)
    if kind == 0:
        b[rng.randrange(12, len(b))] = rng.getrandbits(8)
    elif kind == 1:
        b = b[:rng.randrange(10, len(b) + 1)]
    elif len(b) >= 28:
        b[20:28] = b"\x02\x04\x05\xb4\x02\x04\x05\xb4"
        b[12] = max(b[12], 7 << 4)
    return bytes(b[:60])


STRATA = {"aleatorio": None, "validas": valid_header, "alteradas": altered_header}
X8.STRATA = STRATA


def generate(comp, definition, seed, count=None):
    """Carga total: tercios de bytes aleatorios (la declarada), cabeceras válidas y alteradas."""
    cases = X8._base_generate(comp, definition, seed, count)
    if comp.name != NAME:
        return cases
    rng = random.Random(seed)
    s = X8._stratum["activo"]
    return [c if (s or ("aleatorio", "validas", "alteradas")[i % 3]) == "aleatorio"
            else (tuple(STRATA[s or ("aleatorio", "validas", "alteradas")[i % 3]](rng)),) for i, c in enumerate(cases)]


def edge_inputs(comp, rng, n_random=2000):
    cases = X._edge(comp, rng, n_random)
    if comp.name == NAME:
        cases += [(tuple(valid_header(rng)),) for _ in range(n_random)]
        cases += [(tuple(altered_header(rng)),) for _ in range(n_random)]
    return cases


workload.generate = generate
workload.edge_inputs = edge_inputs
X8.equivalence_with_exp007 = lambda out: {"estado": "no comprobado", "detalle": "no aplica a EXP-010"}
X8.exp007_efforts = lambda: {"detalle": "no aplica a EXP-010"}


def cmd_todo(args):
    """X8.cmd_todo con la fila «tcp» en lugar de «dns»."""
    E.criteria, E.report_md = X8._no_exp005_criteria, X8._minimal_report
    E.cmd_todo(args)
    out = (ROOT / args.salida).resolve()
    ev = json.loads((out / "evidencia.json").read_text())
    row = ev["funciones"]["tcp"]
    if "efch_lang" in row["ns_op"]:
        try:
            row["dafny_espec_go"] = X.d5_dafny_go(out, row)
        except Exception as e:  # se registra; D5 no cumple (F3)
            row["dafny_espec_go_error"] = repr(e)
    ev["criterios"] = X8.criteria(row)
    import hashlib
    for p in ("experimentos/exp010.py", "experimentos/exp009.py", "experimentos/exp008.py", "experimentos/exp007.py",
              "experimentos/exp005.py", "experimentos/exp005_dafny_rendimiento.py", "experimentos/exp010_vectores.py"):
        ev["huellas_sha256"][p] = hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
    (out / "evidencia.json").write_text(json.dumps(ev, ensure_ascii=False, indent=2, default=str))
    report = "# EXP-010 (opciones TCP con fold)\n\n" + "\n".join(
        f"- {k}: {json.dumps(row.get(k), ensure_ascii=False, default=str)}" for k in ("ns_op", "ns_op_por_estrato"))
    report += "\n```json\n" + json.dumps(ev["criterios"], ensure_ascii=False, indent=2, default=str) + "\n```\n"
    (out / "informe.md").write_text(report)
    print(json.dumps(ev["criterios"], ensure_ascii=False, indent=2, default=str))
    return 0


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "todo":
        import argparse
        ap = argparse.ArgumentParser()
        ap.add_argument("orden")
        ap.add_argument("--salida", default="resultados/exp-010")
        ap.add_argument("--solo")
        return cmd_todo(ap.parse_args())
    return E.main()


if __name__ == "__main__":
    sys.exit(X8._in_big_stack(main))
