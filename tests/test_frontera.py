import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "experimentos"))
import frontera


class TestFrontera(unittest.TestCase):
    def test_filas(self):
        filas = frontera.construir()
        exps = {f["experimento"] for f in filas}
        self.assertTrue({"EXP-005", "EXP-007", "EXP-008", "EXP-010"} <= exps)
        t10 = [f for f in filas if f["experimento"] == "EXP-010"]
        self.assertEqual(len(t10), 1)
        self.assertEqual(t10[0]["funcion"], "tcp-options")
        self.assertEqual(t10[0]["efch_estado"], "probado")
        n8 = [f for f in filas if f["experimento"] == "EXP-008"]
        self.assertIn("desconocido (memoria)", n8[0]["kani_estado"])
        self.assertIn("Kani", n8[0]["nota"])
        self.assertEqual([f for f in filas if f["experimento"] == "EXP-007"][0]["ns_op_dafny_espec_go"], 12103.211)


if __name__ == "__main__":
    unittest.main()
