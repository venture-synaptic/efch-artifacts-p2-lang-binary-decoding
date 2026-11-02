"""
Reserva de la máquina para las medidas de tiempo y coste (RESEARCH_PROTOCOL.md, §M1).

    python3 experimentos/maquina.py estado
    python3 experimentos/maquina.py medir NOMBRE -- ORDEN ...      # exclusiva: espera a que no haya otra
    python3 experimentos/maquina.py fondo NOMBRE -- ORDEN ...      # compartida, limitada a un núcleo

En EXP-003 la fase 3 se contaminó dos veces con trabajo lanzado en paralelo: una medida de tiempo
necesita la máquina para ella sola, y eso se impone con un cerrojo, no con la memoria de quien
lanza. `medir` toma el cerrojo en exclusiva; `fondo` lo toma compartido (varios trabajos de fondo
pueden convivir, pero no con una medida) y además corre en la slice `efch-fondo.slice`, limitada a
un núcleo y con `nice 19`. Cada reserva se anota en resultados/maquina.log para la evidencia.

Se usa desde Python con `with reserva("EXP-009", exclusiva=True): ...`.
"""

import contextlib
import fcntl
import os
import pathlib
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
LOCK = pathlib.Path.home() / ".cache" / "efch" / "maquina.lock"
LOG = ROOT / "resultados" / "maquina.log"
SLICE = "efch-fondo.slice"


def _log(text):
    with open(LOG, "a") as f:
        f.write(f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} pid={os.getpid()} {text}\n")


@contextlib.contextmanager
def reserva(nombre, exclusiva=True):
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(LOCK, os.O_RDWR | os.O_CREAT, 0o600)
    kind = "exclusiva" if exclusiva else "compartida"
    try:
        try:
            fcntl.flock(fd, (fcntl.LOCK_EX if exclusiva else fcntl.LOCK_SH) | fcntl.LOCK_NB)
        except BlockingIOError:
            print(f"maquina: {nombre} espera la reserva {kind}…", file=sys.stderr, flush=True)
            _log(f"espera {kind} {nombre}")
            fcntl.flock(fd, fcntl.LOCK_EX if exclusiva else fcntl.LOCK_SH)
        if exclusiva:
            os.ftruncate(fd, 0)
            os.write(fd, f"{nombre} pid={os.getpid()} desde {time.strftime('%H:%M:%SZ', time.gmtime())}\n".encode())
        _log(f"toma {kind} {nombre}")
        yield
    finally:
        _log(f"suelta {kind} {nombre}")
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def estado():
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(LOCK, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        fcntl.flock(fd, fcntl.LOCK_UN)
        return "libre"
    except BlockingIOError:
        try:
            fcntl.flock(fd, fcntl.LOCK_SH | fcntl.LOCK_NB)
            fcntl.flock(fd, fcntl.LOCK_UN)
            return "trabajo de fondo en curso (se admite más fondo; una medida esperaría)"
        except BlockingIOError:
            return "medida en curso: " + LOCK.read_text().strip()
    finally:
        os.close(fd)


def main(argv):
    if not argv or argv[0] == "estado":
        print(estado())
        return 0
    if len(argv) < 3 or argv[0] not in ("medir", "fondo") or "--" not in argv:
        raise SystemExit(__doc__)
    nombre, cmd = argv[1], argv[argv.index("--") + 1:]
    if argv[0] == "fondo":
        cuota = os.environ.get("EFCH_FONDO_CPU", "100%")  # p. ej. 200% para una búsqueda de dos procesos (EXP-011)
        # Tope de memoria de todo el fondo: el 23/10 una búsqueda sin él agotó RAM y swap (OOM global).
        memoria = os.environ.get("EFCH_FONDO_MEMORIA", "5G")
        subprocess.run(["systemctl", "--user", "set-property", "--runtime", SLICE, f"CPUQuota={cuota}",
                        f"MemoryMax={memoria}", "MemorySwapMax=0"], check=False)
        cmd = ["systemd-run", "--user", "--scope", "-q", f"--slice={SLICE}", "--", "nice", "-n", "19"] + cmd
    with reserva(nombre, exclusiva=argv[0] == "medir"):
        return subprocess.run(cmd).returncode


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
