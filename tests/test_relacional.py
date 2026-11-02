"""
Pruebas de la congruencia condicional de pliegues (EXP-014): un plan relacional R solo se usa si sus obligaciones
quedan `probado`, y nunca permite probar una propiedad falsa.
python3 -m unittest tests.test_relacional -v
"""

import itertools
import random
import unittest

from efch import core, interp, smt

T = 10


def prop(body, variables="(x (bv 4)) (y (bv 4))"):
    return core.load_definition(f"(efch 0.1 (property q (forall ({variables}) {body})))").properties[0]


def check(body, plan, variables="(x (bv 4)) (y (bv 4))", i=0, j=1):
    p = prop(body, variables)
    rels = [(i, j, smt.relation(plan, p))] if plan is not None else []
    return p, smt.check_property(p, T, rels)


def always(p):
    return all(interp.evaluate(p.body, {"x": x, "y": y}) is True for x, y in itertools.product(range(16), repeat=2))


F = "(fold i 0 3 (a {v}) (add a (bv 4 i)))"
G = "(fold i 0 3 (a (bv 4 0)) (add a {v}))"


class TestCongruenciaCondicional(unittest.TestCase):
    def test_verdadera_con_el_plan(self):
        p, r = check(f"(any (ne x y) (eq {F.format(v='x')} {F.format(v='y')}))", "(eq x y)")
        self.assertEqual(r.status, "probado")
        self.assertIn("1 congruencia", r.detail)
        self.assertTrue(always(p))

    def test_la_relacion_debe_cubrir_lo_que_lee_el_paso(self):
        # Mismos bits bajos no basta: el paso suma todo x.
        body = f"(any (ne (and x (bv 4 3)) (and y (bv 4 3))) (eq {G.format(v='x')} {G.format(v='y')}))"
        p, r = check(body, "(eq (and x (bv 4 3)) (and y (bv 4 3)))")
        self.assertFalse(always(p))
        self.assertEqual(r.status, "refutado")

    def test_valor_inicial_distinto(self):
        body = f"(eq {F.format(v='x')} {F.format(v='y')})"
        p, r = check(body, "true")
        self.assertEqual(r.status, "refutado")

    def test_relacion_falsa_no_prueba_nada(self):
        p, r = check(f"(eq {F.format(v='x')} {F.format(v='y')})", "false")
        self.assertEqual(r.status, "refutado")

    def test_relacion_indefinida_no_se_usa(self):
        variables = "(x (bv 4)) (y (bv 4)) (b (bytes 1))"
        body = f"(eq {F.format(v='x')} {F.format(v='y')})"
        p, r = check(body, "(eq (byte b (bv 16 0)) (bv 8 0))", variables)
        self.assertNotEqual(r.status, "probado")

    def test_distinto_numero_de_pasos(self):
        body = f"(any (ne x y) (eq {F.format(v='x')} (fold i 0 4 (a y) (add a (bv 4 i)))))"
        p, r = check(body, "(eq x y)")
        self.assertFalse(always(p))
        self.assertEqual(r.status, "refutado")

    def test_pasos_en_distinto_orden(self):
        a = "(fold i 0 2 (a x) (ite (eq (bv 4 i) (bv 4 0)) (mul a (bv 4 2)) (add a (bv 4 1))))"
        b = "(fold i 0 2 (a y) (ite (eq (bv 4 i) (bv 4 0)) (add a (bv 4 1)) (mul a (bv 4 2))))"
        p, r = check(f"(any (ne x y) (eq {a} {b}))", "(eq x y)")
        self.assertFalse(always(p))
        self.assertEqual(r.status, "refutado")

    def test_indices_invalidos_se_ignoran(self):
        body = f"(any (ne x y) (eq {F.format(v='x')} {F.format(v='y')}))"
        for i, j in [(0, 0), (0, 5), (-1, 1)]:
            p, r = check(body, "(eq x y)", i=i, j=j)
            self.assertNotIn("1 congruencia", r.detail or "")

    def test_relacion_con_pliegue_se_rechaza(self):
        body = f"(any (ne x y) (eq {F.format(v='x')} {F.format(v='y')}))"
        p, r = check(body, f"(eq {F.format(v='x')} {F.format(v='y')})")
        self.assertNotIn("1 congruencia", r.detail or "")

    def test_nombres_que_parecen_internos(self):
        variables = "(acc%rel_0 (bv 4)) (y (bv 4))"
        a = "(fold i 0 3 (a acc%rel_0) (add a acc%rel_0))"
        b = "(fold i 0 3 (a y) (add a y))"
        p = prop(f"(any (ne acc%rel_0 y) (eq {a} {b}))", variables)
        r = smt.check_property(p, T, [(0, 1, smt.relation("(eq acc%rel_0 y)", p))])
        self.assertEqual(r.status, "probado")
        self.assertIn("1 congruencia", r.detail)


class TestRelacionalAleatoria(unittest.TestCase):
    """Pliegues y relaciones al azar sobre x, y de 4 bits: todo `probado` debe valer en las 256 entradas."""

    STEPS = ["(add a {v})", "(xor a {v})", "(and a {v})", "(add a (bv 4 i))", "(ite (ult a {v}) {v} a)",
             "(mul a (bv 4 3))", "(sub {v} a)", "(or a (and {v} (bv 4 i)))"]
    INITS = ["{v}", "(bv 4 0)", "(not {v})", "(and {v} (bv 4 3))"]
    RELS = ["(eq x y)", "(eq (and x (bv 4 3)) (and y (bv 4 3)))", "(ule x y)", "true", "false",
            "(eq (xor x y) (bv 4 8))", "(all (eq x y) (ult x (bv 4 8)))"]

    def fold(self, rng, v, steps, init, n):
        return f"(fold i 0 {n} (a {init.format(v=v)}) {steps.format(v=v)})"

    def test_aleatoria(self):
        rng = random.Random(20261023)
        stats = {"probado": 0, "con_congruencia": 0, "otros": 0}
        for _ in range(500):
            st, ini, n = rng.choice(self.STEPS), rng.choice(self.INITS), rng.randint(1, 3)
            fx = self.fold(rng, "x", st, ini, n)
            if rng.random() < 0.3:  # segundo pliegue ligeramente distinto
                fy = self.fold(rng, "y", rng.choice(self.STEPS), rng.choice(self.INITS), rng.choice([n, n + 1]))
            else:
                fy = self.fold(rng, "y", st, ini, n)
            premise, plan = rng.choice(self.RELS), rng.choice(self.RELS)
            cmp = rng.choice(["eq", "ule", "ne"])
            body = f"(any (not {premise}) ({cmp} {fx} {fy}))"
            p = prop(body)
            r = smt.check_property(p, T, [(0, 1, smt.relation(plan, p))])
            if r.status == "probado":
                stats["probado"] += 1
                stats["con_congruencia"] += "1 congruencia" in (r.detail or "")
                self.assertTrue(always(p), f"probado falso: {body} con plan {plan}")
            else:
                stats["otros"] += 1
        print("\n  relacional aleatoria:", stats)
        self.assertGreater(stats["con_congruencia"], 5, stats)


if __name__ == "__main__":
    unittest.main()
