"""
Pruebas adversarias de la forma `fold` (núcleo 0.2, EXP-009).

Objetivo: intentar romperla. Intérprete = Z3 = C compilado en pliegues aleatorios, congruencia y
buena definición modulares (nunca un «probado» falso), EFCH Lang e identidad canónica.
python3 -m unittest tests.test_fold -v
"""

import pathlib
import random
import tempfile
import unittest

from efch import backend_c, core, interp, lang, native, pipeline, smt
from efch._z3 import z3
from efch.workload import edge_inputs

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "ejemplos"

INPUTS = "(input x (bv 8)) (input y (bv 8)) (input b (bytes 8)) (input p bool)"


def comp_of(body, output="(bv 8)", inputs=INPUTS, name="f"):
    d = core.load_definition(f"(efch 0.1 (computation {name} {inputs} (output {output}) (semantics {body})))")
    return d, d.computations[name]


def cand_of(d, comp, body):
    [c] = core.load_candidates(f"(efch 0.1 (candidate c (implements {comp.name}) (body {body})))", d)
    return c.body


def z3_value(comp, args):
    """Traduce la semántica y la evalúa con valores concretos; devuelve (valor, definida)."""
    env, subs = {}, []
    for (n, ty), v in zip(comp.inputs, args):
        sym, _ = smt.make_input(n, ty)
        env[n] = sym
        if ty[0] == "bv":
            subs.append((sym, z3.BitVecVal(v, ty[1])))
        elif ty[0] == "bool":
            subs.append((sym, z3.BoolVal(bool(v))))
        else:
            subs.append((sym.n, z3.BitVecVal(len(v), 16)))
            for k, bsym in enumerate(sym.b):
                subs.append((bsym, z3.BitVecVal(v[k] if k < len(v) else 0, 8)))
    val, dom = smt.translate(comp.semantics, env)
    out = z3.simplify(z3.substitute(val, *subs))
    defined = z3.is_true(z3.simplify(z3.substitute(dom, *subs)))
    if comp.output[0] == "bool":
        return z3.is_true(out), defined
    return out.as_long(), defined


# (nombre, salida, cuerpo). Entradas fijas: x y (bv 8), b (bytes 8), p bool.
CASOS = [
    ("bv8-indice", "(bv 8)", "(fold i 0 6 (a x) (add (xor a (bv 8 i)) y))"),
    ("bv16", "(bv 16)", "(fold i 0 5 (a (zext 16 x)) (add (mul a (bv 16 3)) (zext 16 y)))"),
    ("bv64", "(bv 64)", "(fold i 1 9 (a (zext 64 x)) (xor (shl a (bv 64 3)) (lshr a (bv 64 5))))"),
    ("bv3", "(bv 3)", "(fold i 0 4 (a (trunc 3 x)) (add a (bv 3 3)))"),
    ("bv1", "(bv 1)", "(fold i 0 3 (a (trunc 1 x)) (xor a (trunc 1 y)))"),
    ("bool", "bool", "(fold i 0 5 (a p) (ite a (ult x y) (ugt (bv 8 i) x)))"),
    ("bool-indice-literal", "bool", "(fold i 0 4 (a false) (ite (eq (bv 8 i) x) true a))"),
    ("sin-indice-punto-fijo", "(bv 8)", "(fold i 0 8 (a x) (ite (ugt a (bv 8 10)) (sub a (bv 8 1)) a))"),
    # Punto fijo en 0 durante cinco pasos y luego el índice lo mueve: el bucle NO puede salir antes.
    ("punto-fijo-y-luego-indice", "(bv 8)",
     "(fold i 0 8 (a (bv 8 0)) (ite (eq (bv 8 i) (bv 8 5)) (bv 8 9) a))"),
    ("punto-fijo-con-cambio-tardio", "(bv 8)",
     "(fold i 0 8 (a (bv 8 0)) (ite (ult (bv 8 i) (bv 8 4)) a (add a (bv 8 1))))"),
    ("punto-fijo-bool", "bool", "(fold i 0 6 (a false) (ite (eq (bv 8 i) (bv 8 4)) true a))"),
    ("con-guarda-de-longitud", "(bv 8)",
     "(fold i 0 8 (a (bv 8 0)) (ite (ult (bv 16 i) (len b)) (add a (byte b (bv 16 i))) a))"),
    ("lee-sin-guarda", "(bv 8)", "(fold i 0 3 (a x) (add a (byte b (bv 16 i))))"),
    ("lee-con-acc-como-indice", "(bv 8)",
     "(fold i 0 4 (a (bv 8 0)) (ite (eq (len b) (bv 16 0)) a (byte b (urem (zext 16 a) (len b)))))"),
    ("bajo-let", "(bv 8)",
     "(let ((t (fold i 0 4 (a x) (add a y)))) (mul t (fold i 0 3 (a t) (xor a (bv 8 i)))))"),
    ("bajo-ite", "(bv 8)",
     "(ite p (fold i 0 4 (a x) (add a y)) (fold i 0 3 (a y) (sub a (bv 8 i))))"),
    ("bajo-match", "(bv 8)",
     "(match (ite p (some x y) (some y x)) ((some u v) (fold i 0 3 (a u) (add a v))) (none (bv 8 0)))"),
    ("en-el-paso-de-otro", "(bv 8)",
     "(fold i 0 3 (a x) (add a (fold j 0 3 (c y) (xor c (add a (bv 8 j))))))"),
    ("anidado-mismos-nombres", "(bv 8)",
     "(fold i 0 3 (a x) (fold i 0 2 (a (add a y)) (add a (bv 8 i))))"),
    ("acc-sombrea-variable-externa", "(bv 8)",
     "(let ((a (bv 8 5))) (add a (fold i 0 3 (a x) (add a y))))"),
    ("acc-sombrea-entrada", "(bv 8)", "(add x (fold i 0 3 (x y) (add x (bv 8 i))))"),
    ("indice-sombrea-entrada", "(bv 8)", "(add y (fold y 0 3 (a x) (add a (bv 8 y))))"),
    ("init-ve-el-exterior", "(bv 8)",
     "(let ((a (bv 8 7))) (fold i 0 3 (a (add a x)) (add a y)))"),
    ("un-solo-paso", "(bv 8)", "(fold i 3 4 (a x) (add a (bv 8 i)))"),
    ("rango-desplazado", "(bv 8)", "(fold i 250 256 (a x) (add a (bv 8 i)))"),
    ("lnot-bool-acc", "bool", "(fold i 0 5 (a p) (not a))"),
]


class TestTresSemanticas(unittest.TestCase):
    """Intérprete = Z3 = C sobre pliegues. Donde el intérprete es indefinido, Z3 también debe decirlo."""

    def test_coinciden(self):
        rng = random.Random(909)
        comps = []
        for name, out, body in CASOS:
            _, c = comp_of(body, out, name=name.replace("-", "_"))
            comps.append(c)
        unit = backend_c.emit_unit([(c, c.semantics, backend_c.function_name(c.name)) for c in comps])
        with tempfile.TemporaryDirectory() as tmp:
            lib = native.build_library(tmp, unit)
            for (name, _, body), c in zip(CASOS, comps):
                call = native.bind(lib, c, backend_c.function_name(c.name))
                cases = edge_inputs(c, rng, 150)
                defined = 0
                for args in cases:
                    try:
                        ref = interp.run(c, c.inputs, list(args))
                    except interp.Undefined:
                        _, ok = z3_value(c, args)
                        self.assertFalse(ok, (name, args, "Z3 la da por definida"))
                        continue
                    defined += 1
                    via_z3, ok = z3_value(c, args)
                    self.assertTrue(ok, (name, args))
                    self.assertEqual(ref, via_z3, (name, "Z3", args))
                    self.assertEqual(ref, call(args), (name, "C", args))
                self.assertGreater(defined, 20, name)
                r = native.differential(c, None, call, n_random=300, n_workload=0)
                self.assertEqual(r["fallos"], 0, (name, r["contraejemplos"]))

    def test_expansion_a_mano_es_la_semantica(self):
        # La semántica de referencia: fold = cadena de let.
        _, c1 = comp_of("(fold i 0 4 (a x) (add (xor a (bv 8 i)) y))")
        _, c2 = comp_of("(let ((s0 x)) (let ((s1 (add (xor s0 (bv 8 0)) y))) (let ((s2 (add (xor s1 (bv 8 1)) y))) "
                        "(let ((s3 (add (xor s2 (bv 8 2)) y))) (add (xor s3 (bv 8 3)) y)))))")
        rng = random.Random(3)
        for _ in range(200):
            args = [rng.getrandbits(8), rng.getrandbits(8), (), rng.random() < 0.5]
            self.assertEqual(interp.run(c1, c1.inputs, args), interp.run(c2, c2.inputs, args))

    def test_punto_fijo_en_c_no_sale_antes_si_depende_del_indice(self):
        # acc se queda en 0 cinco pasos y en el paso 5 pasa a 9; si C saliera al primer punto fijo daría 0.
        _, c = comp_of("(fold i 0 8 (a (bv 8 0)) (ite (eq (bv 8 i) (bv 8 5)) (bv 8 9) a))")
        self.assertEqual(interp.run(c, c.inputs, [0, 0, (), False]), 9)
        unit = backend_c.emit_unit([(c, c.semantics, "g")])
        with tempfile.TemporaryDirectory() as tmp:
            call = native.bind(native.build_library(tmp, unit), c, "g")
            self.assertEqual(call([0, 0, (), False]), 9)
        self.assertNotIn("break", unit)

    def test_punto_fijo_en_c_se_usa_sin_indice_y_conserva_valor(self):
        _, c = comp_of("(fold i 0 20 (a x) (ite (ugt a (bv 8 10)) (sub a (bv 8 1)) a))")
        unit = backend_c.emit_unit([(c, c.semantics, "g")])
        self.assertIn("break", unit)
        with tempfile.TemporaryDirectory() as tmp:
            call = native.bind(native.build_library(tmp, unit), c, "g")
            for x in range(256):
                self.assertEqual(call([x, 0, (), False]), interp.run(c, c.inputs, [x, 0, (), False]))

    def test_guarda_absorbente_en_c(self):
        """Paso (let ... (ite G acc E)): C sale cuando G vale y si no hace acc := E; debe coincidir con el intérprete."""
        casos = [
            # guarda directa, alias de let, guarda con lecturas de bytes y acumulador bool
            ("(fold i 0 6 (a x) (ite (ugt a (bv 8 200)) a (add a y)))", "(bv 8)", True),
            ("(fold i 0 6 (a x) (let ((s a) (t (add s (bv 8 3)))) (ite (eq (and s (bv 8 7)) (bv 8 0)) s (mul t y))))",
             "(bv 8)", True),
            ("(fold i 0 8 (a (bv 8 0)) (let ((q (zext 16 a))) (ite (any (uge q (len b)) (eq (byte b q) (bv 8 0))) a "
             "(add a (bv 8 1)))))", "(bv 8)", True),
            ("(fold i 0 5 (a p) (ite a a (eq (add x y) (bv 8 7))))", "bool", True),
            # la rama «entonces» no es el acumulador: no se usa la vía de guarda
            ("(fold i 0 6 (a x) (let ((s y)) (ite (ugt a (bv 8 200)) s (add a y))))", "(bv 8)", False),
            ("(fold i 0 6 (a x) (ite (ugt a (bv 8 200)) (add a (bv 8 0)) (add a y)))", "(bv 8)", False),
        ]
        rng = random.Random(5)
        for body, out, guarded in casos:
            _, c = comp_of(body, out)
            unit = backend_c.emit_unit([(c, c.semantics, "g")])
            body_c = unit[unit.index("int g(") if "int g(" in unit else unit.index(" g("):]
            self.assertEqual(") break;" in body_c and "== f" not in body_c, guarded, (body, body_c))
            with tempfile.TemporaryDirectory() as tmp:
                call = native.bind(native.build_library(tmp, unit), c, "g")
                n = 0
                for x in range(0, 256, 3):
                    for y in (0, 1, 2, 7, 128, 255, rng.getrandbits(8)):
                        bs = tuple(rng.getrandbits(8) if rng.random() < 0.7 else 0 for _ in range(rng.randint(0, 8)))
                        args = [x, y, bs, rng.random() < 0.5]
                        try:
                            ref = interp.run(c, c.inputs, args)
                        except interp.Undefined:
                            continue
                        n += 1
                        self.assertEqual(call(args), ref, (body, args))
                self.assertGreater(n, 500, body)

    def test_rangos_invalidos(self):
        for body in ("(fold i 3 3 (a x) a)", "(fold i 0 257 (a x) a)", "(fold i 0 4 (a b) a)",
                     "(fold i 0 4 (a x) (ult a y))", "(fold i 0 4 (a x) b)"):
            with self.subTest(body=body), self.assertRaises(core.EFCHError):
                comp_of(body)


# --- Congruencia ---------------------------------------------------------------------

SPEC = "(fold i 0 4 (a x) (add (xor a y) (bv 8 i)))"


def verdict(spec_body, cand_body, secs=20, output="(bv 8)"):
    d, comp = comp_of(spec_body, output)
    body = cand_of(d, comp, cand_body)
    cong = smt.check_equivalence_congruence(comp, body, secs)
    v = pipeline.verify_candidate(comp, body, secs)
    return comp, body, cong, v


class TestCongruencia(unittest.TestCase):
    def test_correcta_escrita_distinto_se_prueba_por_la_via_modular(self):
        comp, body, cong, v = verdict(SPEC, "(fold k 0 4 (s x) (add (bv 8 k) (xor y s)))")
        self.assertIsNotNone(cong)
        self.assertEqual(cong.status, "probado")
        self.assertIn("modular", cong.detail)
        self.assertEqual(v["estado"], "probado")

    def test_paso_distinto_solo_para_un_indice(self):
        cand = "(fold k 0 4 (s x) (ite (eq (bv 8 k) (bv 8 2)) (add s y) (add (xor s y) (bv 8 k))))"
        comp, body, cong, v = verdict(SPEC, cand)
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "refutado")
        cx = v["obligaciones"][-1]["contraejemplo"]
        args = [cx.get("x", 0), cx.get("y", 0), (), False]
        self.assertNotEqual(interp.run(comp, comp.inputs, args), interp.run(body, comp.inputs, args))

    def test_init_distinto(self):
        comp, body, cong, v = verdict(SPEC, "(fold k 0 4 (s y) (add (xor s y) (bv 8 k)))")
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "refutado")

    def test_distinto_numero_de_pasos_va_por_la_via_normal(self):
        # Equivalentes de verdad (paso idempotente) pero con 4 y 2 pasos: sin congruencia, expansión.
        comp, body, cong, v = verdict("(fold i 0 4 (a x) (or a (bv 8 1)))", "(fold k 0 2 (s x) (or s (bv 8 1)))")
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "probado")
        self.assertNotIn("modular", v["obligaciones"][-1]["detalle"])
        comp, body, cong, v = verdict(SPEC, "(fold k 0 5 (s x) (add (xor s y) (bv 8 k)))")
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "refutado")

    def test_distinto_numero_de_pliegues(self):
        spec = "(add (fold i 0 2 (a x) (add a y)) (fold i 0 2 (a y) (add a x)))"
        comp, body, cong, v = verdict(spec, "(add (fold i 0 2 (a x) (add a y)) (add y (add x y)))")
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "refutado")

    def test_variable_libre_que_no_es_entrada(self):
        spec = "(let ((t (add x y))) (fold i 0 3 (a t) (add a t)))"
        cand = "(let ((u (add y x))) (fold k 0 3 (s u) (add u s)))"
        comp, body, cong, v = verdict(spec, cand)
        self.assertIsNone(cong)          # t no es entrada: no se intenta la vía modular
        self.assertEqual(v["estado"], "probado")
        bad = "(let ((u (add y x))) (fold k 0 3 (s u) (add y s)))"
        comp, body, cong, v = verdict(spec, bad)
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "refutado")

    def test_acc_con_el_nombre_de_una_entrada_no_se_intenta(self):
        spec = "(fold i 0 3 (x y) (add x (bv 8 i)))"
        cand = "(fold k 0 3 (x y) (add (bv 8 k) x))"
        comp, body, cong, v = verdict(spec, cand)
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "probado")

    def test_difiere_solo_en_acumuladores_inalcanzables(self):
        # La equivalencia es cierta (acc arranca en 0 y sube de uno en uno hasta 3), pero la congruencia
        # modular no la prueba (para acc = 200 difieren): nunca debe salir «refutado».
        spec = "(fold i 0 3 (a (bv 8 0)) (ite (ult a (bv 8 100)) (add a (bv 8 1)) (bv 8 100)))"
        cand = "(fold k 0 3 (s (bv 8 0)) (ite (ult s (bv 8 100)) (add s (bv 8 1)) s))"
        comp, body, cong, v = verdict(spec, cand, 30)
        self.assertIsNone(cong)
        self.assertIn(v["estado"], ("probado", "desconocido"), v)
        for _ in range(100):
            args = [random.getrandbits(8), 0, (), False]
            self.assertEqual(interp.run(comp, comp.inputs, args), interp.run(body, comp.inputs, args))

    def test_incorrecta_solo_para_acumuladores_alcanzables_nunca_probada(self):
        spec = "(fold i 0 4 (a (bv 8 0)) (add a (bv 8 1)))"
        cand = "(fold k 0 4 (s (bv 8 0)) (ite (eq s (bv 8 2)) (bv 8 7) (add s (bv 8 1))))"
        comp, body, cong, v = verdict(spec, cand)
        self.assertIsNone(cong)
        self.assertEqual(v["estado"], "refutado")
        self.assertNotEqual(interp.run(comp, comp.inputs, [0, 0, (), False]),
                            interp.run(body, comp.inputs, [0, 0, (), False]))

    def test_donde_la_semantica_esta_indefinida_la_candidata_es_libre(self):
        # Paso de la semántica indefinido (lee fuera de rango) para algunos acc: la candidata puede diferir
        # ahí. Pero no se debe probar nada si difiere donde la semántica está definida.
        spec = "(fold i 0 2 (a (bv 8 0)) (ite (ult (zext 16 a) (len b)) (add a (byte b (zext 16 a))) (byte b (bv 16 0))))"
        # Esta semántica es indefinida con len = 0 (se usa solo para el valor: no hay verificación de buena definición).
        d, comp = comp_of(spec)
        bad = cand_of(d, comp, "(fold k 0 2 (s (bv 8 0)) (add s (bv 8 1)))")
        r = smt.check_equivalence(comp, bad, 20)
        self.assertNotEqual(r.status, "probado")

    def test_aleatorio_nunca_probado_si_hay_diferencia(self):
        # Generador de candidatas mutadas: si el resultado es «probado», el intérprete no debe hallar diferencia.
        rng = random.Random(55)
        steps = ["(add (xor a y) (bv 8 i))", "(sub a (bv 8 i))", "(ite (ult a y) (add a x) a)", "(and a (bv 8 #xF0))",
                 "(or a (bv 8 1))", "(xor (shl a (bv 8 1)) y)", "(mul a (bv 8 i))"]
        for t in range(12):
            st = rng.choice(steps)
            n = rng.randint(1, 5)
            spec = f"(fold i 0 {n} (a x) {st})"
            st2 = rng.choice(steps) if rng.random() < 0.7 else st
            n2 = n if rng.random() < 0.8 else n + 1
            cand = f"(fold i 0 {n2} (a x) {st2})".replace(" a ", " s ").replace("(a x)", "(s x)")
            cand = cand.replace("(a ", "(s ").replace(" a)", " s)")
            d, comp = comp_of(spec)
            body = cand_of(d, comp, cand)
            v = pipeline.verify_candidate(comp, body, 15)
            diffs = [args for args in edge_inputs(comp, rng, 400)
                     if interp.run(comp, comp.inputs, list(args)) != interp.run(body, comp.inputs, list(args))]
            if diffs:
                self.assertNotEqual(v["estado"], "probado", (spec, cand, diffs[0]))
            if v["estado"] == "refutado":
                self.assertTrue(diffs, ("refutado sin diferencia observable", spec, cand))


# --- Buena definición modular --------------------------------------------------------

class TestBuenaDefinicionModular(unittest.TestCase):
    def test_paso_definido_solo_en_los_alcanzables_vuelve_a_la_via_expandida(self):
        # acc <= 3 por construcción y len = 8; byte b acc es indefinido para acc >= 8 (acumulador arbitrario).
        body = ("(ite (eq (len b) (bv 16 8)) (fold i 0 3 (a (bv 8 0)) (and (byte b (zext 16 a)) (bv 8 3))) (bv 8 0))")
        _, comp = comp_of(body)
        self.assertIsNone(smt.check_well_defined_modular("wd", comp.semantics, comp.inputs, 20))
        r = smt.check_well_defined("wd", comp.semantics, comp.inputs, 20)
        self.assertEqual(r.status, "probado", r)
        self.assertNotIn("modular", r.detail)

    def test_modular_prueba_cuando_el_paso_es_definido_para_todo_acc(self):
        body = "(fold i 0 5 (a x) (ite (ult (zext 16 (and a (bv 8 3))) (len b)) (add a (byte b (zext 16 (and a (bv 8 3))))) a))"
        _, comp = comp_of(body)
        r = smt.check_well_defined_modular("wd", comp.semantics, comp.inputs, 20)
        self.assertIsNotNone(r)
        self.assertEqual(r.status, "probado")

    def test_realmente_indefinido_no_se_prueba(self):
        _, comp = comp_of("(fold i 0 3 (a x) (byte b (zext 16 a)))")
        r = smt.check_well_defined("wd", comp.semantics, comp.inputs, 20)
        self.assertEqual(r.status, "refutado")
        cx = r.counterexample
        with self.assertRaises(interp.Undefined):
            interp.run(comp, comp.inputs, [cx["x"], cx["y"], tuple(cx["b"]), cx["p"]])

    def test_indefinido_solo_en_el_ultimo_paso(self):
        # Division por cero que aparece solo con i = 2 y acc = 0.
        _, comp = comp_of("(fold i 0 3 (a x) (ite (eq (bv 8 i) (bv 8 2)) (byte b (zext 16 a)) (add a (bv 8 1))))")
        r = smt.check_well_defined("wd", comp.semantics, comp.inputs, 20)
        self.assertIn(r.status, ("refutado", "desconocido"))
        if r.status == "refutado":
            with self.assertRaises(interp.Undefined):
                interp.run(comp, comp.inputs, [r.counterexample["x"], r.counterexample["y"], (), False])

    def test_init_indefinido_no_se_prueba(self):
        _, comp = comp_of("(fold i 0 3 (a (byte b (bv 16 0))) (add a x))")
        r = smt.check_well_defined("wd", comp.semantics, comp.inputs, 20)
        self.assertEqual(r.status, "refutado")

    def test_resto_indefinido_con_el_pliegue_abstraido(self):
        _, comp = comp_of("(byte b (zext 16 (fold i 0 3 (a y) (add a (bv 8 1)))))")
        r = smt.check_well_defined("wd", comp.semantics, comp.inputs, 20)
        self.assertEqual(r.status, "refutado")
        cx = r.counterexample
        with self.assertRaises(interp.Undefined):
            interp.run(comp, comp.inputs, [cx["x"], cx["y"], (), False])

    def test_indefinido_dentro_de_otro_paso(self):
        _, comp = comp_of("(fold i 0 2 (a x) (add a (fold j 0 2 (c y) (byte b (zext 16 c)))))")
        r = smt.check_well_defined("wd", comp.semantics, comp.inputs, 20)
        self.assertNotEqual(r.status, "probado")


# --- EFCH Lang ---------------------------------------------------------------------------

PROG = """
fn f(b: bytes[8], x: u8) -> u8 {
    return fold k in 0..8 from x with s { if k >= b.len { s } else { s ^ (b[k] + b[0]) } }
}
"""


class TestLang(unittest.TestCase):
    SPEC = """(efch 0.1
      (computation f (input b (bytes 8)) (input x (bv 8)) (output (bv 8))
        (semantics (fold k 0 8 (s x) (ite (ult (bv 16 k) (len b)) (xor s (add (byte b (bv 16 k)) (byte b (bv 16 0)))) s)))))"""

    def test_traduce_y_coincide_con_la_especificacion(self):
        defn = core.load_definition(lang.core_definition_text(PROG))
        c = defn.computations["f"]
        spec = core.load_definition(self.SPEC)
        sc = spec.computations["f"]
        rng = random.Random(4)
        for args in edge_inputs(sc, rng, 400):
            self.assertEqual(interp.run(c, c.inputs, list(args)), interp.run(sc, sc.inputs, list(args)), args)

    def test_c_coincide_con_el_interprete(self):
        defn = core.load_definition(lang.core_definition_text(PROG))
        c = defn.computations["f"]
        unit = backend_c.emit_unit([(c, c.semantics, "g")])
        with tempfile.TemporaryDirectory() as tmp:
            call = native.bind(native.build_library(tmp, unit), c, "g")
            r = native.differential(c, defn, call, n_random=500, n_workload=0)
            self.assertEqual(r["fallos"], 0, r)

    def test_verify(self):
        spec = core.load_definition(self.SPEC)
        text = PROG.replace("fn f(b: bytes[8], x: u8) -> u8 {", "fn f(b: bytes[8], x: u8) -> u8 implements f {")
        [(_, _, obligations, status)] = lang.verify(text, spec, smt_seconds=30, cbmc_seconds=1)
        self.assertEqual(status, "probado", obligations)

    def test_verify_refuta_un_programa_incorrecto(self):
        spec = core.load_definition(self.SPEC)
        text = PROG.replace("fn f(b: bytes[8], x: u8) -> u8 {", "fn f(b: bytes[8], x: u8) -> u8 implements f {")
        bad = text.replace("s ^ (b[k] + b[0]) }", "s ^ (b[k] + b[0] + (if k == 5 { u8(1) } else { u8(0) })) }")
        self.assertNotEqual(bad, text)
        [(_, _, obligations, status)] = lang.verify(bad, spec, smt_seconds=30, cbmc_seconds=1)
        self.assertNotEqual(status, "probado", obligations)

    def test_bool_y_cuerpo_en_linea(self):
        comp = lang_comp("fn f(x: u8) -> bool { let b0 = u8(3)\n return fold k in 0..4 from false with s { s || x == b0 } }")
        for x in range(8):
            self.assertEqual(interp.run(comp, comp.inputs, [x]), x == 3)

    def assertError(self, src, fragment=None):
        with self.assertRaises(core.EFCHError) as cm:
            lang_comp(src)
        if fragment:
            self.assertIn(fragment, str(cm.exception))

    def test_errores(self):
        self.assertError("fn f(n: u8) -> u8 { return fold k in 0..n from u8(0) with s { s + 1 } }", "constantes")
        self.assertError("fn f(n: u8) -> u8 { return fold k in n..4 from u8(0) with s { s + 1 } }", "constantes")
        self.assertError("fn f(x: u8) -> u8 { return fold k in 0..65 from u8(0) with s { s + 1 } }", "64")
        self.assertError("fn f(x: u8) -> u8 { return fold k in 3..3 from u8(0) with s { s + 1 } }", "1 a 64")
        self.assertError("fn f(x: u8) -> u8 { return fold k in 0..4 from x with s { s + 1 } }".replace("x with", "none with"))
        self.assertError("fn f(b: bytes[4]) -> u8 { let t = fold k in 0..4 from b with s { s }\n return 0 }")
        self.assertError("fn f(x: u8) -> u8 { let t = fold k in 0..4 from some(x) with s { s }\n return 0 }")
        self.assertError("fn f(x: u8) -> u8 { return fold k in 0..4 from x with x { x } }")

    # Fallo encontrado por estas pruebas y corregido en lang.py: el índice del pliegue se traducía como un
    # literal sin ancho, y fallaba al convertirlo o pasarlo a una función.
    def test_indice_en_conversion_o_llamada(self):
        comp = lang_comp("fn f(x: u8) -> u8 { return fold k in 0..2 from x with s { s + (k as u8) } }")
        self.assertEqual(interp.run(comp, comp.inputs, [10]), 11)

    def test_indice_pasado_a_funcion(self):
        comp = lang_comp("fn g(k: u16) -> u16 { return k + 1 }\n"
                         "fn f(x: u8) -> u16 { return fold k in 0..2 from u16(0) with s { g(k) } }")
        self.assertEqual(interp.run(comp, comp.inputs, [0]), 2)

    def test_limite_de_64_pasos_se_admite(self):
        comp = lang_comp("fn f(x: u8) -> u8 { return fold k in 0..64 from x with s { s + 1 } }")
        self.assertEqual(interp.run(comp, comp.inputs, [10]), 74)


def lang_comp(src):
    defn = core.load_definition(lang.core_definition_text(src))
    return list(defn.computations.values())[-1]   # la última función: las anteriores son auxiliares


# --- Forma canónica e identidad ------------------------------------------------------

class TestIdentidad(unittest.TestCase):
    def test_pliegues_alfa_equivalentes(self):
        _, a = comp_of("(fold i 0 4 (acc x) (add (xor acc y) (bv 8 i)))")
        _, b = comp_of("(fold j 0 4 (s x) (add (xor s y) (bv 8 j)))")
        self.assertEqual(a.identity(), b.identity())

    def test_pliegues_distintos_tienen_identidad_distinta(self):
        _, a = comp_of("(fold i 0 4 (acc x) (add (xor acc y) (bv 8 i)))")
        for other in ("(fold i 0 5 (acc x) (add (xor acc y) (bv 8 i)))",
                      "(fold i 1 5 (acc x) (add (xor acc y) (bv 8 i)))",
                      "(fold i 0 4 (acc y) (add (xor acc y) (bv 8 i)))",
                      "(fold i 0 4 (acc x) (add (xor acc x) (bv 8 i)))",
                      "(fold i 0 4 (acc x) (add (xor acc y) (bv 8 0)))"):
            _, o = comp_of(other)
            self.assertNotEqual(a.identity(), o.identity(), other)

    def test_acc_y_variable_exterior_no_se_confunden(self):
        # (let ((a 5)) (fold (a x) (add a y))): el acc es el de dentro; la identidad cambia si el paso usa el exterior.
        _, a = comp_of("(let ((t (bv 8 5))) (fold i 0 3 (a x) (add a t)))")
        _, b = comp_of("(let ((t (bv 8 5))) (fold i 0 3 (a x) (add a a)))")
        _, c = comp_of("(let ((u (bv 8 5))) (fold i 0 3 (z x) (add z u)))")
        self.assertNotEqual(a.identity(), b.identity())
        self.assertEqual(a.identity(), c.identity())

    def test_pliegue_con_nombre_de_acc_igual_a_otra_variable(self):
        _, a = comp_of("(add y (fold i 0 3 (y x) (add y (bv 8 i))))")
        _, b = comp_of("(add y (fold i 0 3 (q x) (add q (bv 8 i))))")
        self.assertEqual(a.identity(), b.identity())
        _, c = comp_of("(add y (fold i 0 3 (q x) (add y (bv 8 i))))")
        self.assertNotEqual(a.identity(), c.identity())

    def test_programas_sin_fold_conservan_identidad(self):
        # La forma canónica de siempre no cambia: se comprueba con el texto canónico y con un ejemplo fijo.
        d = core.load_definition((EXAMPLES / "popcount.efch").read_text())
        c = d.computations["popcount64"]
        self.assertNotIn("fold", c.canonical())
        self.assertEqual(len(c.identity()), 64)
        _, a = comp_of("(let ((a (add x y))) (mul a a))")
        _, b = comp_of("(let ((zz (add x y))) (mul zz zz))")
        self.assertEqual(a.identity(), b.identity())
        self.assertNotIn("fold", a.canonical())

    def test_candidata_y_semantica_con_el_mismo_texto_comparten_identidad_canonica(self):
        d, comp = comp_of(SPEC)
        body = cand_of(d, comp, "(fold k 0 4 (s x) (add (xor s y) (bv 8 k)))")
        self.assertEqual(core.canonical(body, comp.inputs), core.canonical(comp.semantics, comp.inputs))


if __name__ == "__main__":
    unittest.main()
