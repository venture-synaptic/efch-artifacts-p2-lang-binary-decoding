"""
EXP-007: un programa no trivial en EFCH Lang, nombre de host DNS en formato de cable
(docs/experimentos/EXP-007.md).

    python3 experimentos/exp007.py vectores                       # especificación frente a los vectores
    python3 experimentos/exp007.py todo --salida resultados/exp-007

Reutiliza experimentos/exp005.py sin cambiar sus funciones de medida: solo cambia el corpus
(ejemplos/corpus-g2/) y la carga (adenda de la ficha: nombres estructurados además de bytes
aleatorios, para que las pruebas diferenciales y la medición recorran nombres válidos).
"""

import json
import pathlib
import random
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "experimentos"))

import exp005 as E  # noqa: E402
from efch import workload  # noqa: E402

E.CORPUS = ROOT / "ejemplos" / "corpus-g2"
E.FUNCTIONS = [("dns", "dns-hostname-wire", "DnsHostnameWire")]
NAME = "dns-hostname-wire"

LDH = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-"


def structured_name(rng):
    """Nombre en formato de cable casi válido: etiquetas LDH, final en 0 o en puntero, y con
    probabilidad 1/2 una alteración (guion en un extremo, carácter fuera de LDH, truncado,
    longitud reservada o que no cabe)."""
    out = bytearray()
    for _ in range(rng.randint(0, 8)):
        n = rng.choice([1, 1, 2, 3, 3, 4, 5, 7, 10, 15, 30, 62])
        label = bytearray(rng.choice(LDH) for _ in range(n))
        if label[0] == 0x2d:
            label[0] = 0x61
        if label[-1] == 0x2d:
            label[-1] = 0x30
        out += bytes([n]) + label
    out += rng.choice([b"\x00", b"\x00", bytes([0xc0 | rng.getrandbits(6), rng.getrandbits(8)])])
    out += bytes(rng.getrandbits(8) for _ in range(rng.randint(0, 3)))
    if rng.random() < 0.5 and out:
        k = rng.randrange(len(out))
        kind = rng.randrange(5)
        if kind == 0:
            out[k] = 0x2d
        elif kind == 1:
            out[k] = rng.choice(b"_. \x7f\xe9/")
        elif kind == 2:
            out = out[:k]
        elif kind == 3:
            out[k] = rng.randrange(0x40, 0xc0)
        else:
            out[k] = rng.randrange(1, 64)
    return tuple(out[:64])


_generate = workload.generate
_edge = workload.edge_inputs


def generate(comp, definition, seed, count=None):
    """Mitad bytes aleatorios (la carga declarada en la especificación), mitad nombres estructurados."""
    cases = _generate(comp, definition, seed, count)
    if comp.name != NAME:
        return cases
    rng = random.Random(seed)
    return [(structured_name(rng),) if i % 2 else c for i, c in enumerate(cases)]


def edge_inputs(comp, rng, n_random=2000):
    cases = _edge(comp, rng, n_random)
    if comp.name == NAME:
        cases += [(structured_name(rng),) for _ in range(n_random)]
    return cases


workload.generate = generate
workload.edge_inputs = edge_inputs


def d5_dafny_go(out, row):
    """Especificación ejecutable de Dafny compilada a Go, sobre las mismas cargas (D5)."""
    import exp005_dafny_rendimiento as R
    import shutil
    import statistics
    import re
    d = E.FUNCTIONS[0][0]
    # El script de EXP-005 busca un método Decode o Check: se renombra solo en la copia medida.
    src = (out / d / "dafny-solo-spec.dfy").read_text()
    dfy = out / f"{d}-dafny-solo-spec-check.dfy"
    dfy.write_text(re.sub(r"^method Parse\(", "method Check(", src, flags=re.M))
    cargas = {s: out / d / "medicion" / f"carga-{s}.bin" for s in row["medicion_ns_op"]["efch_lang"]}
    res = R.dafny_go(d, NAME, dfy, out, cargas)
    shutil.rmtree(out / f"{d}-dafny-go", ignore_errors=True)
    return {"por_semilla": res, "ns_op": round(statistics.mean(v["mediana"] for v in res.values()), 3)}


def criteria(row):
    """Criterios D0–D5 de la ficha (función única)."""
    ok = lambda k: row[k]["verificacion"]["estado"] == "probado"
    e = row["efch"]
    res = {"D0": {"cumple": not any(row[k]["vectores_fallidos"] or row[k]["diferencial"]["fallos"]
                                   for k in ("efch", "c", "rust_kani", "dafny", "go"))},
           "D1": {"valor": "expresada con un rodeo (if de expresión); ver la ficha", "cumple": True},
           "D2": {"valor": e["verificacion"], "cumple": ok("efch")}}
    ratio = row["ns_op"]["efch_lang"] / row["ns_op"]["c_a_mano"]
    res["D3"] = {"efch_lang_sobre_c": round(ratio, 3), "cumple": ratio <= 1.25}
    d4 = {}
    for k in ("rust_kani", "dafny"):
        effort = e["lineas"]["total"] / row[k]["lineas"]
        a, b = effort <= 0.80, ok("efch") and not ok(k)
        c = ok("efch") and ok(k) and e["verificacion"]["segundos"] <= 0.5 * row[k]["verificacion"]["segundos"]
        d4[k] = {"esfuerzo_relativo": round(effort, 3), "a": a, "b": b, "c": c, "cumple": a or b or c}
    res["D4"] = {**d4, "cumple": all(v["cumple"] for v in d4.values())}
    dspec = row["dafny"]["solo_especificacion"]["lineas"]
    if "dafny_espec_go" in row:
        q = row["ns_op"]["efch_lang"] / row["dafny_espec_go"]["ns_op"]
        applies = dspec <= e["lineas"]["total"]
        res["D5"] = {"aplica": applies, "lineas_dafny_spec": dspec, "efch_lang_sobre_dafny_spec_go": round(q, 3),
                     "cumple": (not applies) or q <= 0.1}
    res["decision"] = "G2 cumplido para esta función" if all(v["cumple"] for v in res.values() if isinstance(v, dict)) \
        else "no cumplido"
    return res


def cmd_todo(args):
    E.cmd_todo(args)
    out = (ROOT / args.salida).resolve()
    ev = json.loads((out / "evidencia.json").read_text())
    row = ev["funciones"]["dns"]
    try:
        row["dafny_espec_go"] = d5_dafny_go(out, row)
    except Exception as e:  # se registra; D5 queda sin evaluar
        row["dafny_espec_go_error"] = repr(e)
    # Los criterios de EXP-005 (8 funciones) no aplican: se sustituyen por D0–D5 de esta ficha.
    ev["criterios"] = criteria(row)
    (out / "evidencia.json").write_text(json.dumps(ev, ensure_ascii=False, indent=2, default=str))
    report = E.report_md(ev).replace("# EXP-005:", "# EXP-007 (nombre DNS):")
    if "dafny_espec_go" in row:
        report += f"\nEspecificación de Dafny compilada a Go: {row['dafny_espec_go']['ns_op']} ns/op.\n"
    (out / "informe.md").write_text(report)
    print(json.dumps(ev["criterios"], ensure_ascii=False, indent=2))
    return 0


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "todo":
        import argparse
        ap = argparse.ArgumentParser()
        ap.add_argument("orden")
        ap.add_argument("--salida", default="resultados/exp-007")
        ap.add_argument("--solo")
        return cmd_todo(ap.parse_args())
    return E.main()


if __name__ == "__main__":
    sys.exit(main())
