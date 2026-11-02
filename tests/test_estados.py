"""Pruebas de experimentos/estados.py: casos sintéticos y archivos reales de resultados/."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "experimentos"))
import estados  # noqa: E402

C = estados.clasificar


def real(ruta):
    p = ROOT / "resultados" / ruta
    if not p.exists():
        raise unittest.SkipTest(f"no existe {ruta}")
    return p.read_text(errors="replace")


class Codigos(unittest.TestCase):
    def test_timeout(self):
        for h in estados.HERRAMIENTAS:
            for c in ("timeout", 124):
                r = C(h, c, "")
                self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "tiempo"))

    def test_137_memoria(self):
        self.assertEqual(C("kani", 137, "")["motivo"], "memoria")

    def test_143_senal_no_memoria(self):
        r = C("kani", 143, "VERIFICATION:- SUCCESSFUL")
        self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "señal"))
        self.assertEqual(C("cbmc", 143, "out of memory")["motivo"], "memoria")

    def test_herramienta_invalida(self):
        with self.assertRaises(ValueError):
            C("coq", 0, "")

    def test_detalle_acotado(self):
        self.assertLessEqual(len(C("kani", 1, "x" * 1000)["detalle"]), 200)


class Kani(unittest.TestCase):
    def test_probado(self):
        self.assertEqual(C("kani", 0, "Status: SUCCESS\nVERIFICATION:- SUCCESSFUL")["estado"], "probado")

    def test_exito_con_codigo_distinto_no_es_probado(self):
        self.assertEqual(C("kani", 1, "VERIFICATION:- SUCCESSFUL")["estado"], "desconocido")

    def test_memoria_no_es_refutado(self):
        t = "Status: FAILURE\nVERIFICATION:- FAILED\nCBMC appears to have run out of memory."
        r = C("kani", 1, t)
        self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "memoria"))

    def test_refutado(self):
        r = C("kani", 1, "Check 3\n - Status: FAILURE\nVERIFICATION:- FAILED")
        self.assertEqual((r["estado"], r["motivo"]), ("refutado", "contraejemplo"))

    def test_failed_sin_failure(self):
        self.assertEqual(C("kani", 1, "VERIFICATION:- FAILED")["estado"], "desconocido")

    def test_sin_veredicto(self):
        r = C("kani", 1, "warning: algo")
        self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "sin veredicto"))


class Dafny(unittest.TestCase):
    def test_probado(self):
        self.assertEqual(C("dafny", 0, "Dafny program verifier finished with 6 verified, 0 errors")["estado"], "probado")

    def test_fallo_no_es_refutado(self):
        r = C("dafny", 4, "a.dfy(3,1): Error: a postcondition might not hold\nfinished with 1 verified, 1 error")
        self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "herramienta"))

    def test_contraejemplo_concreto(self):
        r = C("dafny", 4, "Error: assertion might not hold\nCounterexample: x = 3")
        self.assertEqual(r["estado"], "refutado")


class Cbmc(unittest.TestCase):
    def test_casos(self):
        self.assertEqual(C("cbmc", 0, "VERIFICATION SUCCESSFUL")["estado"], "probado")
        self.assertEqual(C("cbmc", 10, "VERIFICATION FAILED")["estado"], "refutado")
        self.assertEqual(C("cbmc", 1, "std::bad_alloc")["motivo"], "memoria")
        self.assertEqual(C("cbmc", 6, "PARSING ERROR")["motivo"], "herramienta")
        self.assertEqual(C("cbmc", 0, "")["estado"], "desconocido")


class Efch(unittest.TestCase):
    def test_refutado(self):
        t = "  ✓ probado  a\n  ✗ refutado  b — contraejemplo\n  ⇒ refutado"
        self.assertEqual(C("efch-lang-verify", 1, t)["estado"], "refutado")

    def test_probado_todas(self):
        self.assertEqual(C("efch-check", 0, "  ✓ probado      semántica bien definida")["estado"], "probado")

    def test_probado_con_codigo_malo(self):
        self.assertEqual(C("efch-check", 1, "  ✓ probado      semántica bien definida")["estado"], "desconocido")

    def test_desconocido_tiempo(self):
        r = C("efch-check", 1, "  ✓ probado  a\n  ? desconocido  semántica — Z3: timeout")
        self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "tiempo"))

    def test_sin_lineas(self):
        self.assertEqual(C("efch-verify", 0, "")["motivo"], "sin veredicto")


class Reales(unittest.TestCase):
    """Archivos de resultados/. La salida no guarda el código: se pasa 0 si hubo veredicto, 1 si no."""

    def test_exp008_kani_memoria(self):
        r = C("kani", 1, real("exp-008/dns/kani.txt"))
        self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "memoria"))
        self.assertIn("out of memory", r["detalle"])

    def test_exp009_kani_memoria(self):
        self.assertEqual(C("kani", 1, real("exp-009/dns/kani.txt"))["motivo"], "memoria")

    def test_exp007_kani_sin_veredicto(self):
        r = C("kani", 1, real("exp-007/dns/kani.txt"))
        self.assertEqual(r["estado"], "desconocido")

    def test_kani_exp005_probado(self):
        r = C("kani", 0, real("exp-005/ipv4/kani.txt"))
        self.assertEqual(r["estado"], "probado")

    def test_dafny_reales(self):
        for e in ("exp-005/ipv4", "exp-007/dns", "exp-008/dns"):
            self.assertEqual(C("dafny", 0, real(f"{e}/dafny.txt"))["estado"], "probado", e)

    def test_efch_verify_exp005(self):
        r = C("efch-lang-verify", 0, real("exp-005/ipv4/efch-verify.txt"))
        self.assertEqual(r["estado"], "probado")  # Z3 desconocido, CBMC probado, ⇒ probado

    def test_efch_verify_vacio(self):
        self.assertEqual(C("efch-verify", 0, real("exp-008/dns/efch-verify.txt"))["motivo"], "sin veredicto")

    def test_efch_check_exp008_tiempo(self):
        r = C("efch-check", 0, real("exp-008/dns/efch-check-spec.txt"))
        self.assertEqual((r["estado"], r["motivo"]), ("desconocido", "tiempo"))


if __name__ == "__main__":
    unittest.main()
