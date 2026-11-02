"""
Pruebas de EFCH Lang 0.1 (efch/lang.py): traducción al núcleo, errores de la ruta ordinaria y
equivalencia de los ejemplos con su especificación.
"""

import pathlib
import random
import sys
import threading
import unittest

from efch import core, interp, lang, smt
from efch.__main__ import LIMITE_RECURSION, PILA_BYTES
from efch.workload import edge_inputs

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "ejemplos"


def compile_one(src):
    """Traduce un programa de una función y devuelve su computation del núcleo."""
    defn = core.load_definition(lang.core_definition_text(src))
    return next(iter(defn.computations.values()))


def run(comp, *args):
    return interp.run(comp, comp.inputs, list(args))


class TestTraduccion(unittest.TestCase):
    def test_mutacion_if_y_bucle(self):
        comp = compile_one("""
            fn f(b: bytes[6]) -> u16 {
                var s: u16 = 0
                for i in 0..b.len {
                    if b[i] & 1 == 1 { s += b[i] } else { s = s ^ 3 }
                }
                return s
            }""")
        rng = random.Random(1)
        for _ in range(300):
            b = tuple(rng.randrange(256) for _ in range(rng.randint(0, 6)))
            s = 0
            for x in b:
                s = (s + x) & 0xFFFF if x & 1 else s ^ 3
            self.assertEqual(run(comp, b), s)

    def test_precedencia_bit_a_bit_antes_que_comparacion(self):
        # A diferencia de C, «a ^ b == 0» es «(a ^ b) == 0».
        comp = compile_one("fn f(a: u8, b: u8) -> bool { return a ^ b == 0 }")
        self.assertTrue(run(comp, 7, 7))
        self.assertFalse(run(comp, 7, 6))

    def test_literales_toman_el_ancho_del_contexto(self):
        comp = compile_one("fn f(x: u8) -> u64 { return u64(x) << (8 * 7) }")
        self.assertEqual(run(comp, 0xAB), 0xAB << 56)

    def test_llamada_se_inline(self):
        defn = core.load_definition(lang.core_definition_text("""
            fn g(x: u8) -> u8 { return x + 1 }
            fn f(x: u8) -> u8 { return g(g(x)) }"""))
        self.assertEqual(run(defn.computations["f"], 255), 1)

    def test_cota_de_desplazamiento_con_cantidad_acotada(self):
        # EXP-005: «1 << (b >> 6)» vale como mucho 8, así que acota el bucle sin SMT.
        comp = compile_one("""
            fn f(b: bytes[8]) -> u8 {
                if b.len == 0 { return 0 }
                let n = 1 << (b[0] >> 6)
                var s: u8 = 0
                for i in 0..n { s += 1 }
                return s
            }""")
        self.assertEqual(run(comp, (0xC0,)), 8)
        self.assertEqual(run(comp, (0x40,)), 2)

    def test_if_expresion_con_else_if(self):
        comp = compile_one("fn f(x: u8) -> u8 { return if x < 10 { 1 } else if x < 20 { 2 } else { 3 } }")
        self.assertEqual([run(comp, v) for v in (5, 15, 25)], [1, 2, 3])

    def test_tamano_lineal_en_bucles_con_return(self):
        # Regresión: cada vuelta con cota dinámica duplicaba el resto del bucle (2^10 copias).
        text = (EXAMPLES / "lang" / "varint.efl").read_text()
        comp = compile_one(text)
        self.assertLess(core.node_count(comp.semantics), 1000)

    def test_tamano_lineal_en_if_anidados_sin_return(self):
        # Regresión (EXP-007, EXP-017): fusionar los if traducía cada rama una vez por variable asignada;
        # prog-v1-sentencias con 4 bytes daba 15,7 millones de nodos. Predicadas, crece lineal con el búfer.
        text = (EXAMPLES / "corpus-g2" / "dns" / "prog-v1-sentencias.efl").read_text()
        sizes = []

        def measure():  # con la pila de la CLI (efch.__main__.main_con_pila): el traductor es recursivo
            sys.setrecursionlimit(LIMITE_RECURSION)
            sizes.extend(core.node_count(compile_one(text.replace("bytes[64]", f"bytes[{n}]")).semantics)
                         for n in (8, 16))

        limit = sys.getrecursionlimit()
        threading.stack_size(PILA_BYTES)
        t = threading.Thread(target=measure)
        t.start()
        t.join()
        threading.stack_size(0)
        sys.setrecursionlimit(limit)
        self.assertEqual(len(sizes), 2)
        self.assertLess(sizes[1], 2.2 * sizes[0], sizes)
        self.assertLess(sizes[1], 20000, sizes)

    def test_rama_predicada_no_lee_fuera_de_rango(self):
        # La lectura b[i + 1] solo es válida bajo la guarda i + 1 < len: predicada, debe seguir siéndolo.
        comp = compile_one("""
            fn f(b: bytes[4]) -> u8 {
                var s: u8 = 0
                for i in 0..b.len {
                    if i + 1 < b.len {
                        let c = b[i + 1]
                        if c == 1 { s += 1 } else { s = s ^ c }
                    }
                }
                return s
            }""")
        self.assertEqual(smt.check_well_defined("bien definida", comp.semantics, comp.inputs, 30).status, "probado")
        rng = random.Random(3)
        for _ in range(300):
            b = tuple(rng.randrange(3) for _ in range(rng.randint(0, 4)))
            s = 0
            for i in range(len(b) - 1):
                s = (s + 1) & 0xFF if b[i + 1] == 1 else s ^ b[i + 1]
            self.assertEqual(run(comp, b), s)
        comp = compile_one("""
            fn f(b: bytes[4]) -> u8 {
                var s: u8 = 0
                for i in 0..b.len { if i < 3 { s = b[i + 1] } }
                return s
            }""")
        self.assertEqual(smt.check_well_defined("bien definida", comp.semantics, comp.inputs, 30).status, "refutado")

    def test_ligadura_option_en_rama_predicada(self):
        # Codex Astra (EXP-017): el neutro none no tenía tipo esperado dentro del ite de una ligadura.
        comp = compile_one("""
            fn f(c: bool, b: bytes[1]) -> option(u8) {
                var x: option(u8) = some(0)
                if c {
                    let y = some(b[0])
                    x = y
                }
                return x
            }""")
        self.assertEqual(run(comp, False, ()), (0,))
        self.assertEqual(run(comp, True, (5,)), (5,))
        self.assertEqual(smt.check_well_defined("bien definida", comp.semantics, comp.inputs, 30).status, "refutado")

    def test_ligadura_de_rama_se_evalua_aunque_no_se_use(self):
        # Desde EXP-017, como en el nivel superior: una rama que se ejecuta evalúa sus let estrictos.
        comp = compile_one("fn f(c: bool, b: bytes[1]) -> u8 {\n if c { let x = b[0] }\n return 0 }")
        self.assertEqual(smt.check_well_defined("bien definida", comp.semantics, comp.inputs, 30).status, "refutado")
        self.assertEqual(run(comp, False, ()), 0)

    def test_if_anidados_con_else_y_varias_variables(self):
        comp = compile_one("""
            fn f(x: u8, y: u8) -> u16 {
                var a: u8 = 0
                var b: u8 = 1
                if x < 100 {
                    if y < 50 { a = x\n b = y } else if y < 200 { a = y } else { b = 7 }
                } else {
                    a = 9
                    if y == x { b = 2 }
                }
                return u16(a) << 8 | b
            }""")
        def ref(x, y):
            a, b = 0, 1
            if x < 100:
                if y < 50:
                    a, b = x, y
                elif y < 200:
                    a = y
                else:
                    b = 7
            else:
                a = 9
                if y == x:
                    b = 2
            return a << 8 | b
        for x in (0, 99, 100, 255):
            for y in (0, 49, 50, 199, 200, 255, x):
                self.assertEqual(run(comp, x, y), ref(x, y), (x, y))


class TestCLI(unittest.TestCase):
    def test_codigos_de_salida_con_pila_propia(self):
        # Codex Astra (EXP-017): main_con_pila perdía el código de SystemExit (--help salía con 1).
        from efch.__main__ import main_con_pila
        self.assertEqual(main_con_pila(["--help"]), 0)
        self.assertEqual(main_con_pila([]), 2)


class TestErrores(unittest.TestCase):
    def assertError(self, src, fragment):
        with self.assertRaises(core.EFCHError) as cm:
            compile_one(src)
        self.assertIn(fragment, str(cm.exception))

    def test_conversion_con_perdida(self):
        self.assertError("fn f(x: u16) -> u8 { return x }", "conversión con pérdida")

    def test_bucle_sin_cota(self):
        self.assertError("fn f(x: u8) -> u8 { var s: u8 = 0\n for i in 0..x { s += 1 }\n return s }",
                         "no se puede acotar el bucle")

    def test_falta_return(self):
        self.assertError("fn f(x: u8) -> u8 { if x == 0 { return 1 } }", "puede terminar sin return")

    def test_sin_sombreado(self):
        self.assertError("fn f(x: u8) -> u8 { let x = 1\n return x }", "no admite sombrear")

    def test_inmutable(self):
        self.assertError("fn f(x: u8) -> u8 { let y = x\n y = 2\n return y }", "no es mutable")

    def test_recursion(self):
        self.assertError("fn f(x: u8) -> u8 { return f(x) }", "definida después")

    def test_posicion_en_el_mensaje(self):
        self.assertError("fn f(x: u8) -> u8 {\n  return x +\n}", "3:")

    def test_lectura_fuera_de_rango_rechazada_con_contraejemplo(self):
        # La ruta ordinaria exige demostrar la buena definición: b[3] con len < 4 se rechaza.
        comp = compile_one("fn f(b: bytes[4]) -> u8 { return b[3] }")
        r = smt.check_well_defined("bien definida", comp.semantics, comp.inputs, 30)
        self.assertEqual(r.status, "refutado")
        comp = compile_one("fn f(b: bytes[4]) -> u8 { if b.len < 4 { return 0 }\n return b[3] }")
        self.assertEqual(smt.check_well_defined("bien definida", comp.semantics, comp.inputs, 30).status,
                         "probado")


class TestEjemplos(unittest.TestCase):
    def check_example(self, prog, spec_file, comp_name, smt_seconds):
        spec = core.load_definition((EXAMPLES / spec_file).read_text())
        text = (EXAMPLES / "lang" / prog).read_text()
        cands = core.load_candidates(lang.candidates_text(text, spec), spec)
        comp = spec.computations[comp_name]
        # Evidencia experimental: intérprete sobre entradas de borde y aleatorias.
        rng = random.Random(20261021)
        for args in edge_inputs(comp, rng, 500):
            self.assertEqual(interp.run(cands[0].body, comp.inputs, args), interp.run(comp, comp.inputs, args), args)
        # Prueba formal (Z3; si no termina, CBMC sobre el C).
        [(_, _, obligations, status)] = lang.verify(text, spec, smt_seconds=smt_seconds)
        self.assertEqual(status, "probado", obligations)

    def test_varint(self):
        self.check_example("varint.efl", "varint.efch", "varint-decode", 60)

    def test_trama(self):
        self.check_example("trama.efl", "trama.efch", "trama-decode", 20)

    def test_corpus_exp005_vectores(self):
        # Especificación y programa de cada función del corpus frente a los vectores de su fuente.
        import json
        vecs = json.loads((EXAMPLES / "corpus" / "vectores.json").read_text())
        for d in ("quic", "hpack", "cbor", "utf8", "base64", "ipv4", "compactsize", "msgpack"):
            spec = core.load_definition((EXAMPLES / "corpus" / d / "spec.efch").read_text())
            text = (EXAMPLES / "corpus" / d / "prog.efl").read_text()
            [cand] = core.load_candidates(lang.candidates_text(text, spec), spec)
            name = cand.implements
            comp = spec.computations[name]
            for case in vecs[name]["casos"]:
                buf = tuple(bytes.fromhex(case["in"].replace(" ", "")))
                args = [case["n"], buf] if "n" in case else [buf]
                want = None if case["out"] is None else tuple(case["out"])
                self.assertEqual(interp.run(comp, comp.inputs, args), want, (d, case))
                self.assertEqual(interp.run(cand.body, comp.inputs, args), want, (d, case))

    def test_equivalencia_por_casos_de_la_cota(self):
        # Z3 no decide ipv4 de una vez; partida por los valores del byte que fija la cota del
        # bucle, sí. Un error real (olvidar comprobar la longitud total) se sigue refutando.
        spec = core.load_definition((EXAMPLES / "corpus" / "ipv4" / "spec.efch").read_text())
        text = (EXAMPLES / "corpus" / "ipv4" / "prog.efl").read_text()
        [(_, _, obligations, status)] = lang.verify(text, spec, smt_seconds=30, cbmc_seconds=1)
        self.assertEqual(status, "probado", obligations)
        self.assertIn("por casos", obligations[-1]["obligacion"])
        buggy = text.replace(" || total < header_len", "")
        self.assertNotEqual(buggy, text)
        [(_, _, obligations, status)] = lang.verify(buggy, spec, smt_seconds=30, cbmc_seconds=1)
        self.assertEqual(status, "refutado", obligations)

    def test_interfaz_distinta_rechazada(self):
        spec = core.load_definition((EXAMPLES / "varint.efch").read_text())
        with self.assertRaises(core.EFCHError) as cm:
            lang.candidates_text("fn d(buf: bytes[10]) -> option(u64, u8) implements varint-decode { return none }",
                                 spec)
        self.assertIn("no coincide", str(cm.exception))


if __name__ == "__main__":
    unittest.main()
