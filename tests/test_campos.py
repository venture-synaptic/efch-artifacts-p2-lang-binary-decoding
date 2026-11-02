"""
Descomposición del acumulador en campos (efch/backend_campos.py): el C debe coincidir con el intérprete en pliegues
aleatorios con acumuladores empaquetados, incluidos acarreos entre campos, desplazamientos y operaciones sin regla.
python3 -m unittest tests.test_campos -v
"""

import random
import tempfile
import unittest

from efch import backend_c, core, interp, native

INPUTS = "(input x (bv 8)) (input y (bv 16)) (input b (bytes 6))"
W = 16
LOW = ["(bv 16 255)", "(bv 16 15)", "(bv 16 63)", "(bv 16 4095)"]          # campos numéricos
HIGH = ["(bv 16 65280)", "(bv 16 65520)", "(bv 16 61440)", "(bv 16 65472)"]  # el resto
BITS = ["(bv 16 256)", "(bv 16 512)", "(bv 16 768)", "(bv 16 32768)", "(bv 16 16)"]


def val(rng, d):
    """Expresión (bv 16) sobre `a`, para combinar."""
    if d >= 2 or rng.random() < 0.4:
        return rng.choice(["a", f"(and a {rng.choice(LOW)})", f"(and a {rng.choice(HIGH)})", "(zext 16 x)", "y",
                           f"(bv 16 {rng.choice([0, 1, 2, 254, 255, 256, 4095, 65535])})"])
    op = rng.choice(["add", "or", "and", "xor", "sub", "shl", "lshr"])
    if op in ("shl", "lshr"):
        return f"({op} {val(rng, d + 1)} (bv 16 {rng.choice([1, 3, 4, 8, 12])}))"
    return f"({op} {val(rng, d + 1)} {val(rng, d + 1)})"


def expr(rng, d=0):
    """Nuevo valor del acumulador `a` (bv 16)."""
    lo = rng.choice(LOW)
    k = rng.choice(["x", "(bv 8 1)", "(bv 8 255)", "(byte b (bv 16 0))"])
    opts = [
        val(rng, 0), val(rng, 0), val(rng, 0),
        f"(add a (bv 16 {rng.choice([1, 2, 3])}))", f"(add a (zext 16 x))",
        f"(or a {rng.choice(BITS)})",
        f"(add a (bv 16 {rng.choice([1, 2, 255, 256, 4095, 65535])}))",
        f"(or (and a {rng.choice(HIGH)}) (zext 16 (add (trunc 8 (and a {lo})) {k})))",
        f"(or (and a {rng.choice(HIGH)}) (and (add (and a {lo}) (zext 16 {k})) {lo}))",
        f"(xor a (shl (zext 16 {k}) (bv 16 {rng.choice([4, 8, 12])})))",
        f"(lshr a (bv 16 {rng.choice([1, 4, 8])}))",
        f"(sub a (zext 16 {k}))",
        f"(mul a (bv 16 3))",
        f"(add (and a {lo}) (and a {rng.choice(HIGH)}))",
        "(not a)",
        "(add a y)",
    ]
    e = rng.choice(opts)
    if d < 2 and rng.random() < 0.5:
        c = rng.choice([f"(ult (and a {lo}) (zext 16 x))", f"(eq (and a {rng.choice(BITS)}) (bv 16 0))",
                        f"(ugt (and a {lo}) (bv 16 {rng.randint(0, 300)}))", "(ult (zext 16 x) (bv 16 100))"])
        return f"(ite {c} {e} {expr(rng, d + 1)})"
    return e


def step(rng):
    lo = rng.choice(LOW)
    e = expr(rng)
    if rng.random() < 0.85:  # guarda absorbente sobre un indicador o la posición (activa la descomposición)
        g = rng.choice([f"(ne (and a {rng.choice(BITS)}) (bv 16 0))", f"(uge (and a {lo}) (zext 16 x))",
                        f"(any (ne (and a (bv 16 768)) (bv 16 0)) (uge (and a {lo}) (bv 16 {rng.randint(1, 60)})))"])
        e = f"(ite {g} a {e})"
    if rng.random() < 0.5:  # ligaduras como las que produce EFCH Lang
        e = f"(let ((s a) (q (trunc 8 (and s {lo})))) {e.replace(' a ', ' s ').replace(' a)', ' s)')})"
    return e


class TestCampos(unittest.TestCase):
    def test_aleatorio_c_igual_al_interprete(self):
        rng = random.Random(20261024)
        comps, activos = [], 0
        for n in range(300):
            body = f"(fold i 0 {rng.randint(2, 12)} (a {rng.choice(['(zext 16 x)', '(bv 16 20)', 'y'])}) {step(rng)})"
            name = f"g{n}"
            d = core.load_definition(f"(efch 0.1 (computation {name} {INPUTS} (output (bv 16)) (semantics {body})))")
            comps.append((d.computations[name], body))
        unit = backend_c.emit_unit([(c, c.semantics, f"efch_{c.name}") for c, _ in comps])
        activos = unit.count("uint64_t fc")
        self.assertGreater(activos, 40, "la descomposición casi no se activa")
        fallos = []
        with tempfile.TemporaryDirectory() as tmp:
            lib = native.build_library(tmp, unit)
            for c, body in comps:
                call = native.bind(lib, c, f"efch_{c.name}")
                for _ in range(600):
                    m = int(rng.choice(LOW)[7:-1])
                    edge = (rng.getrandbits(16) & ~m) | (m - rng.randint(0, 3)) & m
                    args = [rng.choice([rng.getrandbits(8), 255, 254, 1, 0, m & 255, (m - 1) & 255]),
                            rng.choice([0, 1, 255, 256, 65535, rng.getrandbits(16), edge, edge]),
                            tuple(rng.getrandbits(8) for _ in range(rng.randint(1, 6)))]
                    try:
                        ref = interp.run(c.semantics, c.inputs, args)
                    except interp.Undefined:
                        continue
                    if call(args) != ref:
                        fallos.append((body, args, ref, call(args)))
                        break
        self.assertEqual(fallos, [])

    def test_sin_descomposicion_igual(self):
        # Mismo C con la descomposición desactivada: el resultado no puede cambiar.
        body = ("(fold i 0 9 (a (bv 16 20)) (ite (uge (and a (bv 16 255)) (zext 16 x)) a "
                "(or (and a (bv 16 65280)) (zext 16 (add (trunc 8 (and a (bv 16 255))) (bv 8 7))))))")
        d = core.load_definition(f"(efch 0.1 (computation h {INPUTS} (output (bv 16)) (semantics {body})))")
        c = d.computations["h"]
        on = backend_c.emit_unit([(c, c.semantics, "h1")])
        backend_c.FIELD_SPLIT = False
        try:
            off = backend_c.emit_unit([(c, c.semantics, "h2")])
        finally:
            backend_c.FIELD_SPLIT = True
        self.assertIn("uint64_t fc", on)
        self.assertNotIn("uint64_t fc", off)
        with tempfile.TemporaryDirectory() as tmp:
            f1 = native.bind(native.build_library(tmp, on), c, "h1")
        with tempfile.TemporaryDirectory() as tmp:
            f2 = native.bind(native.build_library(tmp, off), c, "h2")
            for x in range(256):
                args = [x, 0, (0,)]
                self.assertEqual(f1(args), f2(args))
                self.assertEqual(f1(args), interp.run(c.semantics, c.inputs, args))

    def test_bordes_de_las_cotas_exhaustivo(self):
        """Casos en los que la decisión «sin acarreo» depende de la cota exacta: todo y (16 bits) para varios x,
        C con descomposición frente a C sin ella (y una muestra frente al intérprete)."""
        casos = [
            "(fold i 0 4 (a y) (ite (uge (and a (bv 16 255)) (zext 16 x)) a (add a (bv 16 2))))",
            "(fold i 0 4 (a y) (ite (uge (and a (bv 16 255)) (lshr y (bv 16 8))) a (add a (bv 16 129))))",
            "(fold i 0 4 (a y) (ite (ugt (and a (bv 16 15)) (zext 16 (and x (bv 8 15)))) a (add a (bv 16 1))))",
            "(fold i 0 4 (a y) (let ((q (trunc 8 (and a (bv 16 63))))) (ite (uge q x) a "
            "(or (and a (bv 16 65472)) (zext 16 (add q (bv 8 2)))))))",
        ]
        rng = random.Random(7)
        for body in casos:
            d = core.load_definition(f"(efch 0.1 (computation h {INPUTS} (output (bv 16)) (semantics {body})))")
            c = d.computations["h"]
            on = backend_c.emit_unit([(c, c.semantics, "h1")])
            self.assertIn("uint64_t fc", on, body)
            backend_c.FIELD_SPLIT = False
            try:
                off = backend_c.emit_unit([(c, c.semantics, "h2")])
            finally:
                backend_c.FIELD_SPLIT = True
            with tempfile.TemporaryDirectory() as t1, tempfile.TemporaryDirectory() as t2:
                f1 = native.bind(native.build_library(t1, on), c, "h1")
                f2 = native.bind(native.build_library(t2, off), c, "h2")
                for x in (0, 1, 2, 14, 15, 16, 62, 63, 64, 127, 128, 253, 254, 255):
                    for y in range(65536):
                        args = [x, y, (0,)]
                        if f1(args) != f2(args):
                            self.fail((body, args, f1(args), f2(args)))
                for _ in range(300):
                    args = [rng.getrandbits(8), rng.getrandbits(16), (0,)]
                    self.assertEqual(f2(args), interp.run(c.semantics, c.inputs, args))


if __name__ == "__main__":
    unittest.main()
