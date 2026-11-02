"""Carga de Z3: el paquete instalado o, si no lo hay, la copia en .vendor/."""

import pathlib
import sys

VENDOR = pathlib.Path(__file__).resolve().parent.parent / ".vendor" / "z3-5.1.0.0"

try:
    import z3
except ImportError:
    if not VENDOR.is_dir():
        raise ImportError("Z3 no está disponible: instala z3-solver o ejecuta scripts/vendor_z3.sh") from None
    sys.path.insert(0, str(VENDOR))
    import z3

VERSION = z3.get_version_string()
