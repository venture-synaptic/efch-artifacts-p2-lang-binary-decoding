"""
La CLI de EFCH (`python3 -m efch ...`) con un límite de recursión de Python mayor (EXP-008, adenda).

    python3 experimentos/exp008_efch.py lang verify PROG.efl ESPEC.efch [...]

El traductor de EFCH Lang 0.1 es recursivo (estilo de continuaciones); con un bucle de 64 vueltas y
guardas `if ... { return }` supera el límite por defecto de 1 000 marcos. No cambia la semántica:
solo el límite de recursión y el tamaño de pila del hilo que ejecuta la CLI sin modificar.
"""

import pathlib
import sys
import threading

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from efch.__main__ import main  # noqa: E402

if __name__ == "__main__":
    sys.setrecursionlimit(200000)
    threading.stack_size(512 * 1024 * 1024)
    box = {}
    t = threading.Thread(target=lambda: box.update(r=main()))
    t.start()
    t.join()
    sys.exit(box.get("r", 1))
