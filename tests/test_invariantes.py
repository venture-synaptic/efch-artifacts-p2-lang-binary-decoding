"""
Pruebas adversarias de los invariantes de pliegue y de la vía modular de propiedades (EXP-013).

Objetivo: intentar romperlos. Ningún «probado» falso: un invariante no inductivo o falso no se usa,
una propiedad falsa nunca queda probada, y la anotación no cambia la semántica (intérprete = Z3 = C).
python3 -m unittest tests.test_invariantes -v
"""

import dataclasses
import random
import tempfile
import unittest

from efch import backend_c, core, interp, lang, native, pipeline, smt
from efch.workload import edge_inputs
from tests.test_fold import comp_of, z3_value

T = 20  # segundos de SMT por obligación


def load_prop(body, variables="(x (bv 8)) (y (bv 8)) (b (bytes 8)) (p bool)", name="q", comps=""):
    d = core.load_definition(f"(efch 0.1 {comps} (property {name} (forall ({variables}) {body})))")
    return d, d.properties[0]


def obligations(body, inputs):
    return smt.check_fold_invariants(body, inputs, T)


def states(rs):
    return [r.status for r in rs]


# Pliegues de referencia (acumulador bv 8, entrada x).
INDUCTIVO = "(fold i 0 4 (a (and x (bv 8 3))) (and (add a (bv 8 1)) (bv 8 3)) (invariant (ule a (bv 8 3))))"
SIN_INV = "(fold i 0 4 (a (and x (bv 8 3))) (and (add a (bv 8 1)) (bv 8 3)))"
# Alcanzable {0, 4} desde 0, pero «a <= 4» NO es inductivo: a=3 -> 7.
NO_INDUCTIVO = "(fold i 0 4 (a (bv 8 0)) (or a (bv 8 4)) (invariant (ule a (bv 8 4))))"
SIN_INV_NI = "(fold i 0 4 (a (bv 8 0)) (or a (bv 8 4)))"
# Falso ya en el valor inicial.
FALSO_INI = "(fold i 0 4 (a (bv 8 0)) (or a (bv 8 4)) (invariant (eq a (bv 8 7))))"


class TestInvarianteCorrecto(unittest.TestCase):
    def test_obligaciones_probadas(self):
        _, c = comp_of(INDUCTIVO)
        rs = obligations(c.semantics, c.inputs)
        self.assertGreaterEqual(len(rs), 2)
        self.assertEqual(states(rs), ["probado"] * len(rs), [r.as_dict() for r in rs])

    def test_propiedad_verdadera_solo_gracias_al_invariante(self):
        _, p = load_prop(f"(ule {INDUCTIVO} (bv 8 3))")
        r = smt.check_property_modular(p, T)
        self.assertIsNotNone(r)
        self.assertEqual(r.status, "probado")
        self.assertIn("1 invariante", r.detail)
        # Sin invariante la abstracción es demasiado débil: la vía modular no la prueba.
        _, q = load_prop(f"(ule {SIN_INV} (bv 8 3))")
        self.assertIsNone(smt.check_property_modular(q, T))
        self.assertEqual(smt.check_property(q, T).status, "probado")   # por la vía expandida

    def test_invariante_con_variable_exterior(self):
        f = "(fold i 0 5 (a x) (xor a (bv 8 0)) (invariant (eq a x)))"
        _, p = load_prop(f"(eq {f} x)")
        r = smt.check_property_modular(p, T)
        self.assertIsNotNone(r)
        self.assertEqual(r.status, "probado")

    def test_check_definition_informa_invariantes(self):
        d = core.load_definition(f"(efch 0.1 (computation f (input x (bv 8)) (output (bv 8)) (semantics {INDUCTIVO})))")
        rep = pipeline.check_definition(d, T)
        inv = rep["computaciones"]["f"]["invariantes"]
        self.assertTrue(inv)
        self.assertTrue(all(o["estado"] == "probado" for o in inv), inv)

    def test_propiedad_via_computacion_llamada_y_alias(self):
        comps = f"(computation f (input x (bv 8)) (output (bv 8)) (semantics {INDUCTIVO}))"
        _, p = load_prop("(ule (call f x) (bv 8 3))", "(x (bv 8))", comps=comps)
        r = smt.check_property(p, T)
        self.assertEqual(r.status, "probado", r.as_dict())
        self.assertIn("vía modular", r.detail)


class TestInvarianteNoInductivo(unittest.TestCase):
    def test_paso_refutado(self):
        _, c = comp_of(NO_INDUCTIVO)
        rs = obligations(c.semantics, c.inputs)
        self.assertEqual(rs[0].status, "probado")               # (a) el valor inicial lo cumple
        self.assertIn("refutado", states(rs[1:]), [r.as_dict() for r in rs])   # (b) no es inductivo

    def test_no_se_usa_por_la_via_modular(self):
        # Verdadera (el valor es 4), pero el invariante no inductivo no puede apoyarla.
        _, p = load_prop(f"(ule {NO_INDUCTIVO} (bv 8 4))")
        self.assertIsNone(smt.check_property_modular(p, T))
        self.assertEqual(smt.check_property(p, T).status, "probado")   # vía expandida

    def test_no_inductivo_no_prueba_una_falsa(self):
        # El valor es 4: «fold <= 0» es falsa.
        _, p = load_prop(f"(ule {NO_INDUCTIVO} (bv 8 0))")
        self.assertIsNone(smt.check_property_modular(p, T))
        r = smt.check_property(p, T)
        self.assertEqual(r.status, "refutado", r.as_dict())

    def test_inductivo_pero_solo_gracias_a_bits_sobrantes(self):
        # Caso real: el paso combina con OR; «a <= 14» vale en lo alcanzable pero no es inductivo.
        f = "(fold i 0 3 (a (bv 8 0)) (ite (eq (bv 8 i) x) (or a (bv 8 1)) a) (invariant (ule a (bv 8 14))))"
        _, c = comp_of(f)
        rs = obligations(c.semantics, c.inputs)
        self.assertIn("refutado", states(rs))
        _, p = load_prop(f"(ule {f} (bv 8 14))")
        r = smt.check_property(p, T)
        self.assertEqual(r.status, "probado")
        self.assertNotIn("1 invariante", r.detail)


class TestInvarianteFalso(unittest.TestCase):
    def test_inicial_refutado(self):
        _, c = comp_of(FALSO_INI)
        rs = obligations(c.semantics, c.inputs)
        self.assertEqual(rs[0].status, "refutado", rs[0].as_dict())
        self.assertIsNotNone(rs[0].counterexample)

    def test_falso_no_se_usa(self):
        # Si se usara, «fold == 7» pasaría; es falsa (el valor es 4).
        _, p = load_prop(f"(eq {FALSO_INI} (bv 8 7))")
        r = smt.check_property(p, T)
        self.assertNotEqual(r.status, "probado", r.as_dict())
        self.assertEqual(r.status, "refutado")

    def test_invariante_contradictorio_no_prueba_cualquier_cosa(self):
        # Invariante insatisfacible (false): si se usara sin demostrar, todo se probaría.
        f = "(fold i 0 3 (a x) (add a (bv 8 1)) (invariant false))"
        _, c = comp_of(f)
        self.assertIn("refutado", states(obligations(c.semantics, c.inputs)))
        _, p = load_prop(f"(eq {f} (bv 8 99))")
        self.assertNotEqual(smt.check_property(p, T).status, "probado")


class TestPropiedadFalsa(unittest.TestCase):
    FALSAS = [
        ("sin-inv", f"(ult {SIN_INV_NI} (bv 8 4))"),
        ("inv-ok", f"(ult {INDUCTIVO} (bv 8 0))"),
        ("inv-ni", f"(ult {NO_INDUCTIVO} (bv 8 4))"),
        ("inv-falso", f"(eq {FALSO_INI} (bv 8 7))"),
        ("depende-de-x", f"(eq {INDUCTIVO} x)"),
        ("distinto-de-lo-que-parece",
         "(eq (fold i 0 4 (a x) (add a (bv 8 1)) (invariant (ule a (bv 8 255)))) (add x (bv 8 5)))"),
    ]

    def test_nunca_probada(self):
        for name, body in self.FALSAS:
            with self.subTest(name):
                _, p = load_prop(body)
                r = smt.check_property(p, T)
                self.assertIn(r.status, ("refutado", "desconocido"), (name, r.as_dict()))
                if r.status == "refutado":
                    self.assertIsNotNone(r.counterexample)
                m = smt.check_property_modular(p, T)
                self.assertIsNone(m, name)

    def test_contraejemplo_confirmado_por_el_interprete(self):
        _, p = load_prop(f"(ult {SIN_INV_NI} (bv 8 4))")
        r = smt.check_property(p, T)
        self.assertEqual(r.status, "refutado")
        self.assertIsNotNone(r.counterexample)
        self.assertIn("intérprete", r.detail)   # el detalle viene de confirm(): lo confirmó el intérprete


class TestAbstraccion(unittest.TestCase):
    def test_verdadera_para_todo_valor_del_pliegue(self):
        _, p = load_prop("(eq (xor (fold i 0 6 (a x) (add a y)) (fold i 0 6 (a x) (add a y))) (bv 8 0))")
        # dos pliegues sintácticamente iguales: cada uno se abstrae con su variable; esto NO es verdad para
        # variables independientes -> la vía modular no debe probarlo.
        self.assertIsNone(smt.check_property_modular(p, T))
        self.assertEqual(smt.check_property(p, T).status, "probado")
        _, q = load_prop("(ule (and (fold i 0 6 (a x) (add a y)) (bv 8 15)) (bv 8 15))")
        r = smt.check_property_modular(q, T)
        self.assertIsNotNone(r)
        self.assertEqual(r.status, "probado")

    def test_depende_del_valor_y_es_verdadera(self):
        _, p = load_prop("(eq (fold i 0 3 (a x) (xor a (bv 8 0))) x)")
        self.assertIsNone(smt.check_property_modular(p, T))      # no se «prueba» con una abstracción débil
        self.assertEqual(smt.check_property(p, T).status, "probado")

    def test_depende_del_valor_y_es_falsa(self):
        _, p = load_prop("(eq (fold i 0 3 (a x) (xor a (bv 8 1))) x)")
        self.assertIsNone(smt.check_property_modular(p, T))
        r = smt.check_property(p, T)
        self.assertEqual(r.status, "refutado", r.as_dict())

    def test_pliegues_anidados_y_en_ramas(self):
        _, p = load_prop("(ite p (ule (and (fold i 0 3 (a x) (add a y)) (bv 8 7)) (bv 8 7)) "
                         "(eq (fold i 0 3 (a y) (add a x)) (bv 8 1)))")
        r = smt.check_property(p, T)
        self.assertNotEqual(r.status, "probado", r.as_dict())     # falsa con p = false, x = y = 0


class TestBuenaDefinicionModular(unittest.TestCase):
    # Paso indefinido solo para a = 200 (inalcanzable desde 0 con paso identidad).
    F = "(fold i 0 4 (a (bv 8 0)) (ite (eq a (bv 8 200)) (byte b (bv 16 100)) a)%s)"

    def test_no_se_usa_la_via_modular(self):
        _, p = load_prop(f"(eq {self.F % ''} (bv 8 0))")
        self.assertIsNone(smt.check_property_modular(p, T))
        self.assertEqual(smt.check_property(p, T).status, "probado")

    def test_con_invariante_inductivo_tampoco_se_usa_modular_si_el_paso_no_es_total(self):
        f = self.F % " (invariant (ule a (bv 8 100)))"
        _, p = load_prop(f"(eq {f} (bv 8 0))")
        self.assertIsNone(smt.check_property_modular(p, T))
        self.assertEqual(smt.check_property(p, T).status, "probado")

    def test_realmente_indefinida_no_se_prueba(self):
        f = "(fold i 0 4 (a (bv 8 0)) (add a (byte b (bv 16 100))))"
        _, p = load_prop(f"(ule {f} (bv 8 255))")
        self.assertIsNone(smt.check_property_modular(p, T))
        self.assertEqual(smt.check_property(p, T).status, "refutado")


class TestAlias(unittest.TestCase):
    def check_same(self, body, n=300, output="(bv 8)"):
        _, c = comp_of(body, output)
        new = smt._inline_aliases(c.semantics)
        c2 = dataclasses.replace(c, semantics=new)
        rng = random.Random(77)
        for args in edge_inputs(c, rng, n):
            try:
                a = interp.run(c, c.inputs, list(args))
            except interp.Undefined:
                with self.assertRaises(interp.Undefined):
                    interp.run(c2, c2.inputs, list(args))
                continue
            self.assertEqual(a, interp.run(c2, c2.inputs, list(args)), (body, args))
        return c.semantics, new

    def test_encadenados(self):
        old, new = self.check_same("(let ((u x)) (let ((v u)) (let ((w v)) (add w (mul v u)))))")
        self.assertNotIn("'let'", str(new))

    def test_sombreado_por_let(self):
        # u := x no puede aplicarse si x se vuelve a ligar dentro.
        self.check_same("(let ((u x)) (let ((x y)) (add u x)))")

    def test_sombreado_por_pliegue(self):
        self.check_same("(let ((w y)) (fold i 0 3 (y x) (add y w)))")
        self.check_same("(let ((w x)) (fold i 0 3 (x y) (add x w)))")

    def test_dentro_de_match(self):
        self.check_same("(let ((w x)) (match (some y x) ((some x v) (add w x)) (none w)))")
        self.check_same("(let ((w x)) (match (some y y) ((some u v) (add w (add u v))) (none w)))")

    def test_no_alias_si_no_es_variable(self):
        self.check_same("(let ((w (add x y))) (mul w w))")

    def test_alias_de_una_variable_ligada_en_otro_lugar(self):
        self.check_same("(add (let ((u x)) (add u u)) (let ((x y)) (let ((u x)) (add u x))))")

    def test_alias_y_pliegue_con_invariante(self):
        old, new = self.check_same(
            "(let ((u x)) (fold i 0 3 (a u) (and (add a (bv 8 1)) (bv 8 3)) (invariant (ule a (bv 8 255)))))")


# --- Tres semánticas con y sin invariante --------------------------------------------

CASOS = [
    ("inductivo", "(bv 8)", "(fold i 0 4 (a (and x (bv 8 3))) (and (add a (bv 8 1)) (bv 8 3)) (invariant (ule a (bv 8 3))))"),
    ("no-inductivo", "(bv 8)", "(fold i 0 4 (a x) (or a (bv 8 4)) (invariant (ule a (bv 8 4))))"),
    ("falso", "(bv 8)", "(fold i 0 4 (a x) (add a y) (invariant (eq a (bv 8 7))))"),
    ("indice-en-paso", "(bv 8)", "(fold i 0 5 (a x) (xor a (bv 8 i)) (invariant (ule a (bv 8 255))))"),
    ("bool", "bool", "(fold i 0 5 (a p) (ite a (ult x y) (ugt (bv 8 i) x)) (invariant (eq a a)))"),
    ("lee-bytes", "(bv 8)",
     "(fold i 0 8 (a x) (ite (ult (bv 16 i) (len b)) (add a (byte b (bv 16 i))) a) (invariant (ule a (bv 8 255))))"),
    ("anidado", "(bv 8)",
     "(fold i 0 3 (a x) (add a (fold j 0 2 (c y) (xor c a) (invariant (eq c c)))) (invariant (ule a (bv 8 255))))"),
    ("bajo-let", "(bv 8)", "(let ((t (fold i 0 4 (a x) (add a y) (invariant (ule a (bv 8 255)))))) (mul t t))"),
]


def strip_inv(text):
    """Quita (invariant ...) a nivel textual: devuelve el mismo pliegue sin anotación."""
    import re
    while True:
        m = re.search(r" \(invariant ", text)
        if not m:
            return text
        i, depth = m.start() + 1, 0
        for j in range(i, len(text)):
            depth += text[j] == "("
            depth -= text[j] == ")"
            if depth == 0:
                break
        text = text[:m.start()] + text[j + 1:]


class TestTresSemanticas(unittest.TestCase):
    def test_anotar_no_cambia_la_semantica(self):
        rng = random.Random(1313)
        pares = []
        for name, out, body in CASOS:
            self.assertNotEqual(strip_inv(body), body, name)
            _, ca = comp_of(body, out, name=name.replace("-", "_") + "_i")
            _, cs = comp_of(strip_inv(body), out, name=name.replace("-", "_") + "_s")
            pares.append((name, ca, cs))
        unit = backend_c.emit_unit([(c, c.semantics, backend_c.function_name(c.name)) for _, a, s in pares for c in (a, s)])
        with tempfile.TemporaryDirectory() as tmp:
            lib = native.build_library(tmp, unit)
            for name, ca, cs in pares:
                fa = native.bind(lib, ca, backend_c.function_name(ca.name))
                fs = native.bind(lib, cs, backend_c.function_name(cs.name))
                defined = 0
                for args in edge_inputs(ca, rng, 120):
                    try:
                        ref = interp.run(cs, cs.inputs, list(args))
                    except interp.Undefined:
                        with self.assertRaises(interp.Undefined):
                            interp.run(ca, ca.inputs, list(args))
                        _, ok = z3_value(ca, args)
                        self.assertFalse(ok, (name, args))
                        continue
                    defined += 1
                    self.assertEqual(ref, interp.run(ca, ca.inputs, list(args)), (name, "interp", args))
                    v, ok = z3_value(ca, args)
                    self.assertTrue(ok, (name, args))
                    self.assertEqual(ref, v, (name, "Z3", args))
                    self.assertEqual(ref, fa(args), (name, "C", args))
                    self.assertEqual(ref, fs(args), (name, "C sin inv", args))
                self.assertGreater(defined, 10, name)

    def test_equivalencia_con_y_sin_invariante(self):
        # La candidata anotada con un invariante falso sigue siendo equivalente (y probada): la anotación no
        # entra en la equivalencia; su obligación se informa aparte.
        d, comp = comp_of("(fold i 0 4 (a x) (add a y))")
        [c] = core.load_candidates(
            "(efch 0.1 (candidate c (implements f) (body (fold k 0 4 (s x) (add s y) (invariant (eq s (bv 8 7)))))))", d)
        v = pipeline.verify_candidate(comp, c.body, T)
        self.assertEqual(v["estado"], "probado", v)


# --- EFCH Lang -----------------------------------------------------------------------

def lang_comp(src):
    defn = core.load_definition(lang.core_definition_text(src))
    return list(defn.computations.values())[-1]


class TestLang(unittest.TestCase):
    PROG = "fn f(x: u8) -> u8 { return fold k in 0..4 from x & u8(3) with s invariant s <= u8(3) { (s + u8(1)) & u8(3) } }"

    def test_traduce(self):
        text = lang.core_definition_text(self.PROG)
        self.assertIn("invariant", text)
        c = lang_comp(self.PROG)
        self.assertEqual(c.semantics.op, "finv")
        for x in range(0, 256, 7):
            self.assertEqual(interp.run(c, c.inputs, [x]), ((x & 3) + 4) & 3)

    def test_sin_invariante_es_la_misma_semantica(self):
        a = lang_comp(self.PROG)
        b = lang_comp(self.PROG.replace(" invariant s <= u8(3)", ""))
        for x in range(256):
            self.assertEqual(interp.run(a, a.inputs, [x]), interp.run(b, b.inputs, [x]))

    def test_invariante_no_ve_el_indice(self):
        with self.assertRaises(core.EFCHError):
            lang_comp("fn f(x: u8) -> u8 { return fold k in 0..4 from x with s invariant k < 9 { s + u8(1) } }")

    def test_invariante_ve_variables_exteriores(self):
        c = lang_comp("fn f(x: u8, y: u8) -> u8 { return fold k in 0..4 from x with s invariant s == x { s } }")
        self.assertEqual(c.semantics.op, "finv")

    def test_invariante_debe_ser_bool(self):
        with self.assertRaises(core.EFCHError):
            lang_comp("fn f(x: u8) -> u8 { return fold k in 0..4 from x with s invariant s + u8(1) { s } }")

    def test_obligaciones_y_c(self):
        defn = core.load_definition(lang.core_definition_text(self.PROG))
        c = defn.computations["f"]
        rs = smt.check_fold_invariants(c.semantics, c.inputs, T)
        self.assertTrue(rs)
        self.assertEqual(states(rs), ["probado"] * len(rs), [r.as_dict() for r in rs])
        unit = backend_c.emit_unit([(c, c.semantics, "g")])
        with tempfile.TemporaryDirectory() as tmp:
            call = native.bind(native.build_library(tmp, unit), c, "g")
            r = native.differential(c, defn, call, n_random=300, n_workload=0)
            self.assertEqual(r["fallos"], 0, r)

    def test_verify_con_invariante(self):
        spec = core.load_definition(
            "(efch 0.1 (computation f (input x (bv 8)) (output (bv 8)) "
            "(semantics (fold k 0 4 (s (and x (bv 8 3))) (and (add s (bv 8 1)) (bv 8 3))))))")
        text = self.PROG.replace("fn f(x: u8) -> u8 {", "fn f(x: u8) -> u8 implements f {")
        [(_, _, obs, status)] = lang.verify(text, spec, smt_seconds=30, cbmc_seconds=1)
        self.assertEqual(status, "probado", obs)

    def test_verify_refuta_si_el_cuerpo_es_incorrecto_aunque_el_invariante_valga(self):
        spec = core.load_definition(
            "(efch 0.1 (computation f (input x (bv 8)) (output (bv 8)) "
            "(semantics (fold k 0 4 (s (and x (bv 8 3))) (and (add s (bv 8 1)) (bv 8 3))))))")
        text = self.PROG.replace("fn f(x: u8) -> u8 {", "fn f(x: u8) -> u8 implements f {").replace("& u8(3) }", "& u8(1) }")
        [(_, _, obs, status)] = lang.verify(text, spec, smt_seconds=30, cbmc_seconds=1)
        self.assertNotEqual(status, "probado", obs)


# --- Identidad -----------------------------------------------------------------------

class TestIdentidad(unittest.TestCase):
    def test_el_invariante_cambia_la_identidad(self):
        _, a = comp_of(SIN_INV)
        _, b = comp_of(INDUCTIVO)
        self.assertNotEqual(a.identity(), b.identity())
        self.assertIn("finv", b.canonical())
        _, c = comp_of(INDUCTIVO.replace("(bv 8 3))))", "(bv 8 4))))"))
        self.assertNotEqual(b.identity(), c.identity())

    def test_alfa_equivalentes(self):
        _, a = comp_of("(fold i 0 4 (a x) (add a y) (invariant (ule a (bv 8 9))))")
        _, b = comp_of("(fold j 0 4 (s x) (add s y) (invariant (ule s (bv 8 9))))")
        self.assertEqual(a.identity(), b.identity())

    def test_invariante_sobre_otra_variable_no_se_confunde(self):
        _, a = comp_of("(fold i 0 4 (a x) (add a y) (invariant (ule a y)))")
        _, b = comp_of("(fold i 0 4 (a x) (add a y) (invariant (ule x y)))")
        _, c = comp_of("(fold j 0 4 (s x) (add s y) (invariant (ule s y)))")
        self.assertNotEqual(a.identity(), b.identity())
        self.assertEqual(a.identity(), c.identity())


if __name__ == "__main__":
    unittest.main()


class TestAmbitoLexico(unittest.TestCase):
    """Revisión de Codex Astra (23/10/2026): un pliegue bajo un `let` o `match` que liga una de sus variables
    libres no es un pliegue sobre la entrada del mismo nombre. Antes daba un «probado» falso."""

    def check(self, body, variables="(x (bv 8))"):
        d, p = load_prop(body, variables)
        r = smt.check_property(p, T)
        return d, p, r

    def test_let_sombrea_la_entrada_con_invariante(self):
        body = "(eq (let ((x (bv 8 1))) (fold i 0 1 (a x) a (invariant (eq a x)))) x)"
        _, p, r = self.check(body)
        self.assertNotEqual(r.status, "probado")
        self.assertFalse(interp.evaluate(p.body, {"x": 0}))

    def test_let_sombrea_la_entrada_sin_invariante(self):
        body = "(eq (let ((x (bv 8 1))) (fold i 0 2 (a x) (add a (bv 8 0)))) x)"
        _, _, r = self.check(body)
        self.assertEqual(r.status, "refutado")

    def test_match_sombrea_la_entrada(self):
        body = ("(match (some (bv 8 1)) ((some x) (eq (fold i 0 1 (a x) a (invariant (eq a x))) (bv 8 1)))"
                " (none true))")
        _, _, r = self.check(body)
        self.assertEqual(r.status, "probado")  # verdadera: aquí x = 1 dentro del match
        falsa = ("(eq (match (some (bv 8 1)) ((some x) (fold i 0 1 (a x) a (invariant (eq a x)))) (none (bv 8 0)))"
                 " x)")
        _, p, r = self.check(falsa)
        self.assertNotEqual(r.status, "probado")

    def test_sin_sombra_sigue_por_la_via_modular(self):
        body = "(eq (fold i 0 1 (a x) a (invariant (eq a x))) x)"
        d, p, r = self.check(body)
        self.assertEqual(r.status, "probado")
        self.assertIsNotNone(smt.check_property_modular(p, T))

    def test_buena_definicion_y_congruencia_bajo_sombra(self):
        self.assertIsNone(smt._closed_folds(load_prop(
            "(eq (let ((x (bv 8 1))) (fold i 0 1 (a x) a)) x)", "(x (bv 8))")[1].body, [("x", None)]))


class TestNombresInternos(unittest.TestCase):
    """Auditoría de Codex Astra (23/10/2026): los nombres internos de la vía modular (`fold%k`, `acc%k`) no
    pueden capturar variables del usuario con el mismo nombre."""

    def check(self, body, variables=""):
        d = core.load_definition(f"(efch 0.1 (property q (forall ({variables}) {body})))")
        return d.properties[0], smt.check_property(d.properties[0], T)

    def test_entrada_llamada_como_el_pliegue_abstraido(self):
        p, r = self.check("(eq (fold i 0 1 (a (bv 8 0)) a) fold%0)", "(fold%0 (bv 8))")
        self.assertFalse(interp.evaluate(p.body, {"fold%0": 1}))
        self.assertEqual(r.status, "refutado")

    def test_let_llamado_como_el_pliegue_abstraido(self):
        p, r = self.check("(eq (let ((fold%0 (bv 8 1))) (fold i 0 1 (a (bv 8 0)) a)) (bv 8 1))")
        self.assertFalse(interp.evaluate(p.body, {}))
        self.assertEqual(r.status, "refutado")

    def test_nombres_frescos_y_verdadera(self):
        p, r = self.check("(eq (let ((fold%0_0 (bv 8 1))) (fold i 0 1 (a fold%0_0) a)) (bv 8 1))")
        self.assertEqual(r.status, "probado")

    def test_congruencia_con_variable_llamada_como_el_acumulador_interno(self):
        self.assertNotIn(smt._fresh("acc%0_", core.load_definition(
            "(efch 0.1 (property q (forall ((acc%0_0 (bv 8))) (eq acc%0_0 acc%0_0))))").properties[0].body,
            inputs=[("acc%0_0", None)]), {"acc%0_0"})


class TestAuditoriaSolidez(unittest.TestCase):
    """Auditoría de Codex Astra (docs/borradores/solidez-codex-astra.md): símbolos SMT compartidos, colisión de
    `canonical` con una variable libre `_0` y bytes omitidos de `mkbytes` sin inicializar en C."""

    def prop(self, body, variables):
        return core.load_definition(f"(efch 0.1 (property q (forall ({variables}) {body})))").properties[0]

    def comp(self, expr, inputs="", output="(bv 8)"):
        d = core.load_definition(f"(efch 0.1 (computation f {inputs} (output {output}) (semantics {expr})))")
        return d.computations["f"]

    def test_entrada_llamada_como_la_longitud_de_otra(self):
        p = self.prop("(eq (fold i 0 1 (a (len b)) a (invariant (eq a (len b)))) b.len)",
                      "(b (bytes 1)) (b.len (bv 16))")
        self.assertFalse(interp.evaluate(p.body, {"b": (), "b.len": 1}))
        self.assertEqual(smt.check_property(p, T).status, "refutado")

    def test_entrada_llamada_como_un_byte_de_otra(self):
        p = self.prop("(ite (ult (bv 16 0) (len b)) (eq (byte b (bv 16 0)) b[0]) true)", "(b (bytes 1)) (b[0] (bv 8))")
        self.assertEqual(smt.check_property(p, T).status, "refutado")

    def test_canonical_distingue_libre_de_ligada(self):
        s0, s1 = "(let ((x (bv 8 0))) x)", "(let ((x (bv 8 0))) _0)"
        c = self.comp(f"(fold% a (bv 8 0) {s0} {s1})", "(input _0 (bv 8))")
        keys = [core.canonical(s) for s in c.semantics.args[1:]]
        self.assertNotEqual(keys[0], keys[1])

    def test_invariante_falso_por_colision_canonica(self):
        s0, s1 = "(let ((x (bv 8 0))) x)", "(let ((x (bv 8 0))) _0)"
        p = self.prop(f"(eq (finv% a (fold% a (bv 8 0) {s0} {s1}) (eq a (bv 8 0))) (bv 8 0))", "(_0 (bv 8))")
        self.assertFalse(interp.evaluate(p.body, {"_0": 1}))
        self.assertEqual(smt.check_property(p, T).status, "refutado")

    def test_congruencia_por_colision_canonica(self):
        s0, s1 = "(let ((x (bv 8 0))) x)", "(let ((x (bv 8 0))) _0)"
        cs = self.comp(f"(fold% a (bv 8 0) {s0} {s0})", "(input _0 (bv 8))")
        cc = self.comp(f"(fold% a (bv 8 0) {s0} {s1})", "(input _0 (bv 8))")
        self.assertNotEqual(pipeline.verify_candidate(cs, cc.semantics, T)["estado"], "probado")

    def test_buena_definicion_por_colision_canonica(self):
        c = self.comp("(fold% a (bv 8 0) (let ((x (bv 16 0))) (byte (mkbytes 1 7) x))"
                      " (let ((x (bv 16 0))) (byte (mkbytes 1 7) _0)))", "(input _0 (bv 16))")
        self.assertNotEqual(smt.check_well_defined("wd", c.semantics, c.inputs, T).status, "probado")

    def test_identidades_sin_nombres_reservados_no_cambian(self):
        c = self.comp("(let ((x (bv 8 1))) (add x y))", "(input y (bv 8))")
        self.assertEqual(core.canonical(c.semantics, c.inputs), "(let _0 (const 8 1) (add _0 y))")

    def test_mkbytes_rellena_con_ceros_en_c(self):
        c = self.comp("(mkbytes (fold i 0 1 (a (bv 16 2)) a) 7)", output="(bytes 2)")
        self.assertEqual(pipeline.verify_candidate(c, c.semantics, T)["estado"], "probado")
        unit = backend_c.emit_unit([(c, c.semantics, "g")])
        self.assertIn("= {0};", unit)
        with tempfile.TemporaryDirectory() as tmp:
            got = native.bind(native.build_library(tmp, unit), c, "g")([])
        self.assertEqual(tuple(got), tuple(interp.evaluate(c.semantics, {})))


class TestAuditoriaSolidez2(unittest.TestCase):
    """Segunda ronda de la auditoría de Codex Astra (cortada por cuota; hallazgos en resultados/codex/astra-solidez3.log)."""

    def test_variables_cuantificadas_repetidas_se_rechazan(self):
        with self.assertRaises(core.EFCHError):
            core.load_definition("(efch 0.1 (property p (forall ((b (bytes 0)) (b (bytes 1))) (eq (len b) (bv 16 0)))))")

    def test_call_no_captura_un_let_del_cuerpo(self):
        d = core.load_definition("""(efch 0.1
 (computation g (input x (bv 8)) (output (bv 8)) (semantics (let ((x%1 (bv 8 0))) x)))
 (computation f (output (bv 8)) (semantics (call g (bv 8 1)))))""")
        self.assertEqual(interp.run(d.computations["f"], [], []), 1)

    def test_call_no_captura_una_variable_del_argumento(self):
        d = core.load_definition("""(efch 0.1
 (computation g (input x (bv 8)) (input y (bv 8)) (output (bv 8)) (semantics (sub x y)))
 (computation f (input x%1 (bv 8)) (output (bv 8)) (semantics (call g (bv 8 5) x%1))))""")
        f = d.computations["f"]
        self.assertEqual(interp.run(f, f.inputs, [2]), 3)
