#!/usr/bin/env python3
"""Registro de la frontera: lee la evidencia guardada (no ejecuta verificadores)
y escribe resultados/frontera.json y docs/frontera.md. Re-ejecutable."""
import json
import os
import sys

RAIZ = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FUENTES = [("EXP-005", "exp-005"), ("EXP-007", "exp-007"),
           ("EXP-008", "exp-008"), ("EXP-009", "exp-009"), ("EXP-010", "exp-010")]

# Correcciones documentadas en las fichas (la evidencia no se edita).
NOTAS = {
    ("EXP-007", "dns"): ["Dafny en Go: 12 103 ns/op, no 13 750 (EXP-007, errata 11)."],
    ("EXP-008", "dns"): [
        "Kani: «desconocido (memoria)», no «refutado» (EXP-008, resultados; el script heredado de EXP-005 lo clasificó mal).",
        "D3 «no comprobado» por la regla F1: el C de EFCH no se ejecuta sin «probado» (EXP-008)."],
}


def _g(d, *ks):
    for k in ks:
        if not isinstance(d, dict) or k not in d:
            return None
        d = d[k]
    return d


def _ratio(a, b):
    return round(a / b, 2) if a and b else None


def filas_de(exp, ruta):
    p = os.path.join(RAIZ, "resultados", ruta, "evidencia.json")
    if not os.path.exists(p):
        return []
    with open(p, encoding="utf-8") as fh:
        d = json.load(fh)
    out = []
    for clave, f in d.get("funciones", {}).items():
        ef, kn, df = f.get("efch", {}), f.get("rust_kani", {}), f.get("dafny", {})
        ns = f.get("ns_op", {})
        kani_est = _g(kn, "verificacion", "estado")
        notas = list(NOTAS.get((exp, clave), []))
        if (exp, clave) == ("EXP-008", "dns"):
            kani_est = "desconocido (memoria)"
        dafny_go = _g(f, "dafny_espec_go", "ns_op")
        if (exp, clave) == ("EXP-007", "dns"):
            dafny_go = 12103.211
        lang, c = ns.get("efch_lang"), ns.get("c_a_mano")
        if (exp, clave) == ("EXP-008", "dns"):
            lang = None
        out.append({
            "experimento": exp, "funcion": f.get("computacion", clave), "clave": clave,
            "fecha": (d.get("fecha") or "")[:10],
            "efch_estado": _g(ef, "verificacion", "estado"),
            "efch_segundos": _g(ef, "verificacion", "segundos"),
            "efch_herramienta": _g(ef, "verificacion", "herramienta"),
            "espec_estado": _g(ef, "solo_especificacion", "estado"),
            "espec_segundos": _g(ef, "solo_especificacion", "segundos"),
            "nodos_nucleo": None,
            "ns_op_efch_lang": lang, "ns_op_c_a_mano": c,
            "cociente_lang_c": _ratio(lang, c),
            "ns_op_dafny_espec_go": dafny_go,
            "lineas_efch": _g(ef, "lineas", "total"),
            "lineas_kani": kn.get("lineas"), "lineas_dafny": df.get("lineas"),
            "kani_estado": kani_est, "kani_segundos": _g(kn, "verificacion", "segundos"),
            "dafny_estado": _g(df, "verificacion", "estado"),
            "dafny_segundos": _g(df, "verificacion", "segundos"),
            "nota": " ".join(notas) or None,
        })
    return out


def construir():
    filas = []
    for exp, ruta in FUENTES:
        filas += filas_de(exp, ruta)
    return filas


def _c(v):
    return "—" if v is None else str(v)


def _fila_md(r):
    t = lambda e, s: _c(e) if s is None else f"{_c(e)} ({s} s)"
    return (f"| {r['experimento']} | {r['funcion']} | {r['fecha']} | {t(r['efch_estado'], r['efch_segundos'])} "
            f"| {t(r['espec_estado'], r['espec_segundos'])} | {_c(r['ns_op_efch_lang'])} | {_c(r['ns_op_c_a_mano'])} "
            f"| {_c(r['cociente_lang_c'])} | {_c(r['lineas_efch'])}/{_c(r['lineas_kani'])}/{_c(r['lineas_dafny'])} "
            f"| {t(r['kani_estado'], r['kani_segundos'])} | {t(r['dafny_estado'], r['dafny_segundos'])} | {_c(r['nota'])} |")


def markdown(filas):
    L = ["# Registro de la frontera", "",
         "Generado por `experimentos/frontera.py` a partir de la evidencia guardada en `resultados/`. "
         "No ejecuta verificadores. Las correcciones se aplican aquí con cita a la ficha; las evidencias no se editan. "
         "«Nodos del núcleo» se omite: no se puede obtener sin ejecutar verificadores.", "",
         "**[Resultado]** Lo que sigue es lo medido y registrado. Un tiempo es evidencia experimental, no prueba. "
         "«—» = no existe en la evidencia o no comprobado.", "",
         "## Tabla por experimento y función", "",
         "| Exp. | Función | Fecha | EFCH (verificación) | Especificación sola | ns/op EFCH Lang | ns/op C a mano | Cociente | Líneas EFCH/Kani/Dafny | Kani | Dafny | Nota |",
         "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    L += [_fila_md(r) for r in filas]
    L += ["", "## Curva de la función dns-hostname-wire", "",
          "**[Resultado]** Métricas clave por experimento (EXP-007 → EXP-008 → EXP-009).", "",
          "| Exp. | EFCH | Espec. sola | Líneas EFCH | ns/op EFCH Lang | ns/op C | Cociente | Kani | Dafny |",
          "|---|---|---|---|---|---|---|---|---|"]
    for r in filas:
        if r["funcion"] == "dns-hostname-wire":
            t = lambda e, s: _c(e) if s is None else f"{_c(e)} ({s} s)"
            L.append(f"| {r['experimento']} | {t(r['efch_estado'], r['efch_segundos'])} | {t(r['espec_estado'], r['espec_segundos'])} "
                     f"| {_c(r['lineas_efch'])} | {_c(r['ns_op_efch_lang'])} | {_c(r['ns_op_c_a_mano'])} | {_c(r['cociente_lang_c'])} "
                     f"| {t(r['kani_estado'], r['kani_segundos'])} | {t(r['dafny_estado'], r['dafny_segundos'])} |")
    L += ["", "Notas: " + " ".join(f"({r['experimento']}) {r['nota']}" for r in filas if r["nota"] and r["funcion"] == "dns-hostname-wire"),
          "", "Las mediciones de EXP-007, EXP-008 y EXP-009 no son comparables en ns/op sin tener en cuenta que "
          "la carga cambió entre fichas; ver cada ficha.", "",
          ]
    L += ["## Función reservada: tcp-options (EXP-010)", "",
          "**[Resultado]** Métricas clave de EXP-010, en el mismo formato que la curva de dns-hostname-wire. "
          "Un «desconocido (124)» de Kani es tiempo agotado a 600 s: ni éxito ni fracaso.", "",
          "| Exp. | EFCH | Espec. sola | Líneas EFCH | ns/op EFCH Lang | ns/op C | Cociente | Kani | Dafny |",
          "|---|---|---|---|---|---|---|---|---|"]
    for r in filas:
        if r["funcion"] == "tcp-options":
            t = lambda e, s: _c(e) if s is None else f"{_c(e)} ({s} s)"
            L.append(f"| {r['experimento']} | {t(r['efch_estado'], r['efch_segundos'])} | {t(r['espec_estado'], r['espec_segundos'])} "
                     f"| {_c(r['lineas_efch'])} | {_c(r['ns_op_efch_lang'])} | {_c(r['ns_op_c_a_mano'])} | {_c(r['cociente_lang_c'])} "
                     f"| {t(r['kani_estado'], r['kani_segundos'])} | {t(r['dafny_estado'], r['dafny_segundos'])} |")
    L += ["", "## Cómo se actualiza", "",
          "1. Terminar el experimento y guardar su `resultados/exp-NNN/evidencia.json` (y su ficha con las correcciones, si las hay).",
          "2. Si hay correcciones documentadas, añadirlas a `NOTAS` (y al ajuste de campo) en `experimentos/frontera.py`, citando la ficha.",
          "3. Añadir la fuente a `FUENTES` si es un experimento nuevo.",
          "4. `nice -n 19 python3 experimentos/frontera.py` (solo lee JSON; reescribe `resultados/frontera.json` y `docs/frontera.md`).",
          "5. `python3 -m unittest tests.test_frontera -v`.", ""]
    return "\n".join(L)


def main():
    filas = construir()
    json.dump(filas, open(os.path.join(RAIZ, "resultados", "frontera.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)
    open(os.path.join(RAIZ, "docs", "frontera.md"), "w", encoding="utf-8").write(markdown(filas))
    print(f"{len(filas)} filas")


if __name__ == "__main__":
    sys.exit(main())
