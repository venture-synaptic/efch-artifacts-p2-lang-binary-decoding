"""Traducción única de la salida de cada herramienta de verificación a los estados del manifiesto (§6).

Estados: `probado`, `refutado` (solo con contraejemplo), `desconocido` (con motivo normalizado),
`no comprobado` (no lo produce este módulo: es una obligación que no se intentó).

Motivos de `desconocido`: "memoria", "tiempo", "señal", "herramienta", "sin veredicto".
`refutado` lleva el motivo "contraejemplo"; `probado`, None.

Regla de fondo: un timeout, una muerte por señal o un agotamiento de memoria NUNCA son «refutado»
ni «probado». Un código 143 (SIGTERM) no se atribuye a memoria salvo que el texto lo diga.
Dafny no produce contraejemplos confirmados: un fallo de verificación de Dafny es «no demostrado»
(desconocido/herramienta), no «refutado», salvo que la salida traiga un contraejemplo concreto.

No se usa en los scripts de experimentos ya registrados (son evidencia); es para los nuevos.
"""
import re

HERRAMIENTAS = ("kani", "dafny", "cbmc", "efch-check", "efch-lang-verify", "efch-verify")
_MEMORIA = re.compile(r"out of memory|std::bad_alloc|cannot allocate memory|memory allocation failed", re.I)


def _res(estado, motivo, detalle=""):
    detalle = " ".join(str(detalle).split())
    return {"estado": estado, "motivo": motivo, "detalle": detalle[:200]}


def _linea(texto, patron):
    """Primera línea del texto que casa con el patrón (expresión regular o cadena)."""
    rx = re.compile(patron) if isinstance(patron, str) else patron
    for l in texto.splitlines():
        if rx.search(l):
            return l.strip()
    return ""


def _motivo_texto(linea):
    l = linea.lower()
    if "timeout" in l or "timed out" in l:
        return "tiempo"
    if _MEMORIA.search(linea) or "memory" in l or "memoria" in l:
        return "memoria"
    return "herramienta"


def _por_codigo(codigo, texto):
    """Estados que dependen solo del código de salida; None si no aplica."""
    if codigo == "timeout" or codigo == 124:
        return _res("desconocido", "tiempo", f"código de salida {codigo}: límite de tiempo")
    if codigo == 137:
        return _res("desconocido", "memoria", "código 137 (SIGKILL; muerte por memoria con OOMPolicy=continue)")
    if codigo == 143:
        mem = _linea(texto, _MEMORIA)
        if mem:
            return _res("desconocido", "memoria", mem)
        return _res("desconocido", "señal", "código 143 (SIGTERM): causa no determinada, no se atribuye a memoria")
    return None


def _kani(codigo, texto):
    mem = _linea(texto, _MEMORIA)
    if "VERIFICATION:- SUCCESSFUL" in texto and codigo == 0 and not mem:
        return _res("probado", None, "VERIFICATION:- SUCCESSFUL")
    if mem:
        return _res("desconocido", "memoria", mem)
    if "VERIFICATION:- FAILED" in texto and _linea(texto, r"Status:\s*FAILURE"):
        return _res("refutado", "contraejemplo", _linea(texto, r"Status:\s*FAILURE") or "VERIFICATION:- FAILED")
    return _res("desconocido", "sin veredicto", f"sin veredicto de Kani (código {codigo})")


def _dafny(codigo, texto):
    if codigo == 0 and re.search(r"\b0 errors\b", texto):
        return _res("probado", None, _linea(texto, r"finished with") or "0 errors")
    cex = _linea(texto, r"(?i)counter-?example")
    if cex and re.search(r"Error|might not hold", texto):
        return _res("refutado", "contraejemplo", cex)
    err = _linea(texto, r"Error|might not hold|errors?\b") or f"sin '0 errors' (código {codigo})"
    return _res("desconocido", "herramienta", "no demostrado: " + err)


def _cbmc(codigo, texto):
    mem = _linea(texto, _MEMORIA)
    if mem:
        return _res("desconocido", "memoria", mem)
    if codigo == 0 and "VERIFICATION SUCCESSFUL" in texto:
        return _res("probado", None, "VERIFICATION SUCCESSFUL")
    if codigo == 10:
        return _res("refutado", "contraejemplo", _linea(texto, r"VERIFICATION FAILED") or "código 10")
    return _res("desconocido", "herramienta", f"CBMC sin veredicto (código {codigo})")


_OBLIG = re.compile(r"^\s*(✓ probado|✗ refutado|\? desconocido)\b(.*)$", re.M)
_GLOBAL = re.compile(r"⇒\s*(\w+)")


def _efch(codigo, texto):
    obl = [(m.group(1), m.group(0).strip()) for m in _OBLIG.finditer(texto)]
    glob = _GLOBAL.search(texto)
    refut = [l for k, l in obl if k.startswith("✗")]
    desc = [l for k, l in obl if k.startswith("?")]
    if refut:
        return _res("refutado", "contraejemplo", refut[0])
    if glob:
        # `lang verify` ya combina las obligaciones (p. ej. Z3 desconocido + CBMC probado => probado).
        g = glob.group(1)
        if g == "probado":
            return _res("probado", None, glob.group(0))
        if g == "refutado":
            return _res("refutado", "contraejemplo", glob.group(0))
    if obl and not desc and codigo == 0:
        return _res("probado", None, obl[-1][1])
    if desc:
        return _res("desconocido", _motivo_texto(desc[0]), desc[0])
    if obl:
        return _res("desconocido", "herramienta", f"código {codigo}: {obl[-1][1]}")
    return _res("desconocido", "sin veredicto", f"sin líneas de obligación (código {codigo})")


_DESPACHO = {"kani": _kani, "dafny": _dafny, "cbmc": _cbmc, "efch-check": _efch,
             "efch-lang-verify": _efch, "efch-verify": _efch}


def clasificar(herramienta, codigo_salida, salida_texto):
    """Devuelve {"estado", "motivo", "detalle"} según las reglas del módulo."""
    if herramienta not in _DESPACHO:
        raise ValueError(f"herramienta desconocida: {herramienta!r} (válidas: {', '.join(HERRAMIENTAS)})")
    texto = salida_texto or ""
    # Un veredicto textual completo prevalece sobre el código (p. ej. `timeout 600` que mata tras imprimir
    # nada es tiempo; pero un 143 con texto de memoria es memoria, resuelto en _por_codigo).
    r = _por_codigo(codigo_salida, texto)
    if r:
        return r
    return _DESPACHO[herramienta](codigo_salida, texto)


if __name__ == "__main__":
    import sys
    if len(sys.argv) != 4:
        sys.exit("uso: estados.py HERRAMIENTA CODIGO ARCHIVO")
    cod = sys.argv[2]
    cod = int(cod) if cod.lstrip("-").isdigit() else cod
    print(clasificar(sys.argv[1], cod, open(sys.argv[3], errors="replace").read()))
