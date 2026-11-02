"""
Vectores de EXP-010 (opciones TCP), generados a partir de la definición de la ficha.

    python3 experimentos/exp010_vectores.py      # escribe ejemplos/corpus-g3/vectores.json

`referencia` traduce literalmente la sección «Función» de docs/experimentos/EXP-010.md y se
escribe antes que la especificación EFCH. Todos los casos son «derivado» (los RFC no traen
cabeceras de ejemplo en hexadecimal); cada uno lleva la regla que ejercita.
"""

import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent


def referencia(b):
    if len(b) < 20:
        return None
    doff = b[12] >> 4
    hl = 4 * doff
    if doff < 5 or hl > len(b):
        return None
    p, mss, ws, sack = 20, None, None, False
    for _ in range(40):
        if p >= hl or b[p] == 0:
            break
        if b[p] == 1:
            p += 1
            continue
        if p + 1 >= hl:
            return None
        L = b[p + 1]
        if L < 2 or p + L > hl:
            return None
        k = b[p]
        if k == 2:
            if L != 4 or mss is not None:
                return None
            mss = b[p + 2] * 256 + b[p + 3]
        elif k == 3:
            if L != 3 or ws is not None:
                return None
            ws = min(b[p + 2], 14)
        elif k == 4:
            if L != 2 or sack:
                return None
            sack = True
        p += L
    return [hl, 0xFFFF if mss is None else mss, 0xFF if ws is None else ws, sack]


def cabecera(opciones=b"", doff=None, extra=b""):
    doff = doff if doff is not None else 5 + (len(opciones) + 3) // 4
    opts = opciones + b"\x00" * (4 * (doff - 5) - len(opciones)) if 4 * (doff - 5) >= len(opciones) else opciones
    fijo = bytes([0x01, 0xBB, 0xC3, 0x50, 0, 0, 0, 1, 0, 0, 0, 0, doff << 4, 0x12, 0xFF, 0xFF, 0, 0, 0, 0])
    return fijo + opts + extra


CASOS = [
    (cabecera(), "sin opciones (doff = 5)"),
    (cabecera()[:19], "menos de 20 bytes"),
    (cabecera(doff=4), "doff < 5"),
    (cabecera(b"\x02\x04\x05\xb4", doff=6)[:23], "hl mayor que el búfer"),
    (cabecera(b"\x02\x04\x05\xb4"), "MSS 1460"),
    (cabecera(b"\x02\x04\x05\xb4\x01\x03\x03\x07\x04\x02\x01\x01"), "MSS, NOP, escala 7, SACK permitido"),
    (cabecera(b"\x03\x03\x0f\x00"), "escala 15 → 14 (RFC 7323 §2.3)"),
    (cabecera(b"\x03\x03\xff\x00"), "escala 255 → 14"),
    (cabecera(b"\x01\x01\x08\x0a\x00\x00\x00\x01\x00\x00\x00\x00"), "NOP, NOP, marca de tiempo (se salta)"),
    (cabecera(b"\x00\x02\x04\x05\xb4"), "EOL: lo siguiente no se lee"),
    (cabecera(b"\x02\x04\x05\xb4\x02\x04\x02\x18"), "MSS duplicado"),
    (cabecera(b"\x03\x03\x01\x03\x03\x02"), "escala duplicada"),
    (cabecera(b"\x04\x02\x04\x02"), "SACK permitido duplicado"),
    (cabecera(b"\x02\x05\x05\xb4\x00"), "MSS con L = 5"),
    (cabecera(b"\x03\x02\x00\x00"), "escala con L = 2"),
    (cabecera(b"\x04\x03\x00\x00"), "SACK permitido con L = 3"),
    (cabecera(b"\x08\x01\x00\x00"), "longitud 1 (< 2)"),
    (cabecera(b"\x08\x00\x00\x00"), "longitud 0"),
    (cabecera(b"\x01\x01\x01\x08"), "tipo al final sin byte de longitud"),
    (cabecera(b"\x05\x0a\x00\x00\x00\x01\x00\x00\x00\x02"), "SACK (tipo 5) de 10 bytes, se salta"),
    (cabecera(b"\x08\x0b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", doff=7), "opción que se sale de hl (20 + 11 > 28)"),
    (cabecera(b"\x01" * 40), "40 NOP (máximo de opciones)"),
    (cabecera(b"\x02\x04\x05\xb4", extra=b"\xde\xad"), "datos tras la cabecera (se ignoran)"),
    (cabecera(b"\x02\x04\x00\x00\x03\x03\x00\x01"), "MSS 0 y escala 0"),
]


def main():
    casos = []
    for b, nota in CASOS:
        assert len(b) <= 60, nota
        casos.append({"in": b.hex(), "out": referencia(b), "nota": "derivado: " + nota})
    data = {"tcp-options": {"fuente": "RFC 9293 §3.1 y §3.2; RFC 7323 §2.2–2.3; RFC 2018 §2. Todos los casos son "
                                      "derivados de las reglas de docs/experimentos/EXP-010.md",
                            "salida": "option(hl u8, mss u16, ws u8, sack bool)", "casos": casos}}
    out = ROOT / "ejemplos" / "corpus-g3" / "vectores.json"
    out.write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n")
    print(len(casos), "casos;", sum(c["out"] is not None for c in casos), "aceptados")


if __name__ == "__main__":
    main()
