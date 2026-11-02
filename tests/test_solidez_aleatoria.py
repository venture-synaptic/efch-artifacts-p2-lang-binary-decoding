"""
Auditoría aleatoria de solidez: nombres y ámbitos (EXP-013, cuarta ronda).

Generador con semilla fija de definiciones bien tipadas del núcleo que estresa la resolución de nombres:
`let` anidados con sombreado, `match`, `fold` con y sin `invariant` (verdaderos y falsos), formas internas
`fold%`/`finv%`, `call` a computaciones auxiliares y nombres de usuario que parecen internos (`_0`, `x%1`,
`fold%0_0`, `acc%0_0`, `b.len`, `b[0]`...). Oráculos (cada uno con su contador en el informe final):

  O1  `smt.check_property` = `probado` => el intérprete da True en TODAS las entradas del dominio
      enumerado; `refutado` => el contraejemplo no evalúa a True (False o indefinido). Una inconsistencia
      Z3/intérprete (`desconocido` con detalle «inconsistencia») también cuenta como fallo.
  O2  `pipeline.verify_candidate` = `probado` (candidata reescrita o mutada) => intérprete(candidata) =
      intérprete(especificación) donde esta está definida, y la candidata está definida en todas partes.
  O3  el C de `backend_c.emit_unit` compilado con `native` coincide con el intérprete (especificaciones y
      candidatas aceptadas) en las entradas donde el intérprete está definido.
  O4  `core.canonical`: dos árboles con la misma clave canónica son semánticamente iguales (incluida la
      definición) en todas las entradas.

Todo es reproducible (SEMILLA) y acotado en tiempo. Un fallo real se deja como prueba con
`unittest.expectedFailure` y su reproductor mínimo (ver el final del archivo). No sustituye una prueba formal:
es evidencia experimental.
python3 -m unittest tests.test_solidez_aleatoria -v
"""

import itertools
import math
import os
import random
import sys
import tempfile
import time
import unittest

from efch import backend_c, core, interp, native, pipeline, smt

SEMILLA = int(os.environ.get("EFCH_ALEATORIA_SEMILLA", 20261023))
T = 4                     # segundos de SMT por obligación
N_PROP = int(os.environ.get("EFCH_ALEATORIA_PROP", 1400))
N_CAND = int(os.environ.get("EFCH_ALEATORIA_CAND", 800))
N_CANON = int(os.environ.get("EFCH_ALEATORIA_CANON", 9000))
C_MAX_FUNCIONES = 400     # tope de funciones C compiladas
FASE_MAX_S = {"prop": 60, "cand": 40, "c": 25, "canon": 25}   # cortafuegos, no el criterio habitual de parada
CAP_ENTRADAS = 1500       # entradas evaluadas por computación (si el dominio es mayor, muestra reproducible)
CAP_C = 300

NOMBRES = ["_0", "_1", "_2", "_0_0", "x%1", "x%2", "fold%0", "fold%1", "fold%0_0", "acc%0", "acc%0_0", "acc%1",
           "finv%0", "b.len", "b[0]", "b.n", "t", "i", "k", "x", "y", "a", "b", "e%1", "_"]
NOMBRES_ENTRADA = ["x", "y", "a", "b", "_0", "_1", "x%1", "fold%0", "acc%0", "b.len", "b[0]", "b.n", "k", "t", "i"]

BV = core.BV
BOOL = core.BOOL
COMM = ("add", "mul", "and", "or", "xor", "eq", "ne")


class Bad(Exception):
    """El nombre elegido no resuelve a su ligadura (sombreado): se descarta esta pintura del árbol."""


# --- Árbol del generador (con ligaduras por identidad, independiente de los nombres) --------------------

class B:
    _ids = itertools.count()

    def __init__(self, name, ty, kind="var"):
        self.id = next(B._ids)
        self.name, self.ty, self.kind = name, ty, kind     # kind: input | var | idx


class Nd:
    __slots__ = ("k", "ty", "a", "x")

    def __init__(self, k, ty, a=(), x=None):
        self.k, self.ty, self.a, self.x = k, ty, tuple(a), x


def walk(nd):
    yield nd
    for c in nd.a:
        if c is not None:
            yield from walk(c)


def const(w, v):
    return Nd("const", BV(w), (), v)


class Render:
    def __init__(self, naming=None):
        self.naming = naming or {}

    def nm(self, b):
        return b.name if b.kind == "input" else self.naming.get(b.id, b.name)

    def res(self, b, sc):
        n = self.nm(b)
        if sc.get(n) is not b:
            raise Bad(n)
        return n

    def r(self, nd, sc):
        k, a = nd.k, nd.a
        if k == "const":
            return f"(bv {nd.ty[1]} {nd.x})"
        if k == "bool":
            return "true" if nd.x else "false"
        if k == "none":
            return "none"
        if k == "raw":
            return nd.x
        if k == "ref":
            return self.res(nd.x, sc)
        if k == "idx":
            return f"(bv {nd.ty[1]} {self.res(nd.x, sc)})"
        if k == "idxnum":
            return self.res(nd.x, sc)
        if k == "app":
            return "(" + " ".join([nd.x] + [self.r(c, sc) for c in a]) + ")"
        if k == "some":
            return "(" + " ".join(["some"] + [self.r(c, sc) for c in a]) + ")"
        if k == "call":
            return "(" + " ".join(["call", nd.x] + [self.r(c, sc) for c in a]) + ")"
        if k == "let":
            parts, cur = [], sc
            for b, v in zip(nd.x, a[:-1]):
                parts.append(f"({self.nm(b)} {self.r(v, cur)})")
                cur = {**cur, self.nm(b): b}
            return f"(let ({' '.join(parts)}) {self.r(a[-1], cur)})"
        if k == "match":
            bs, none_first = nd.x
            inner = dict(sc)
            for b in bs:
                inner[self.nm(b)] = b
            some = f"((some {' '.join(self.nm(b) for b in bs)}) {self.r(a[1], inner)})"
            none = f"(none {self.r(a[2], sc)})"
            clauses = f"{none} {some}" if none_first else f"{some} {none}"
            return f"(match {self.r(a[0], sc)} {clauses})"
        if k == "fold":
            bi, lo, hi, bacc = nd.x
            init, step, inv = a
            ss = {**sc, self.nm(bi): bi}
            ss[self.nm(bacc)] = bacc
            hi_t = hi if isinstance(hi, int) else self.r(hi, sc)
            txt = f"(fold {self.nm(bi)} {lo} {hi_t} ({self.nm(bacc)} {self.r(init, sc)}) {self.r(step, ss)}"
            if inv is not None:
                txt += f" (invariant {self.r(inv, {**sc, self.nm(bacc): bacc})})"
            return txt + ")"
        if k == "foldraw":
            bacc = nd.x
            ss = {**sc, self.nm(bacc): bacc}
            return f"(fold% {self.nm(bacc)} {self.r(a[0], sc)} " + " ".join(self.r(s, ss) for s in a[1:]) + ")"
        if k == "finv":
            binv = nd.x
            return f"(finv% {self.nm(binv)} {self.r(a[0], sc)} {self.r(a[1], {**sc, self.nm(binv): binv})})"
        raise ValueError(k)


def scope_of(inputs):
    return {b.name: b for b in inputs}


def render(nd, inputs, naming=None):
    return Render(naming).r(nd, scope_of(inputs))


def tystr(t):
    return core.type_str(t)


# --- Generador de expresiones -----------------------------------------------------------------------

class Gen:
    def __init__(self, rng, aux=(), bm=2, folds=2, pool=None):
        self.r, self.aux, self.bm, self.folds = rng, list(aux), bm, folds
        self.pool = pool or NOMBRES

    # nombres y ámbito
    def vis(self, env):
        d = {}
        for b in env:
            d[b.name] = b
        return list(d.values())

    def bname(self, env):
        r = self.r
        if env and r.random() < 0.35:
            return r.choice(env).name           # sombrea una ligadura existente
        return r.choice(self.pool)

    def new(self, env, ty, kind="var"):
        return B(self.bname(env), ty, kind)

    def rbytes(self):
        return ("bytes", self.bm)

    # tipos
    def rscalar(self):
        return self.r.choice([BV(2), BV(2), BV(3), BV(3), BV(4), BOOL])

    def rtype(self, env):
        r = self.r.random()
        if r < 0.62:
            return self.rscalar()
        if r < 0.80:
            return self.rbytes()
        return ("option", tuple(self.rscalar() for _ in range(self.r.choice([1, 1, 2]))))

    def const_of(self, ty):
        r = self.r
        if ty == BOOL:
            return Nd("bool", BOOL, (), r.random() < 0.5)
        w = ty[1]
        v = r.choice([0, 1, (1 << w) - 1, r.randrange(1 << w), r.randrange(1 << w)])
        return const(w, v & ((1 << w) - 1))

    def gen(self, ty, env, d):
        if ty[0] == "bytes":
            return self.gen_bytes(env, d)
        if ty[0] == "option":
            return self.gen_opt(ty, env, d)
        return self.gen_scalar(ty, env, d)

    # hojas
    def leaf(self, ty, env):
        r, vis = self.r, self.vis(env)
        cands = [lambda: self.const_of(ty)]
        vs = [b for b in vis if b.ty == ty and b.kind != "idx"]
        for b in vs:
            cands += [lambda b=b: Nd("ref", ty, (), b)] * 3
        if ty[0] == "bv" and ty[1] >= 2:
            for b in [b for b in vis if b.kind == "idx"]:
                cands.append(lambda b=b: Nd("idx", ty, (), b))
        bs = [b for b in vis if b.ty[0] == "bytes"]
        if bs and ty[0] == "bv" and ty[1] <= 8:
            b = r.choice(bs)
            ref = Nd("ref", b.ty, (), b)
            cands.append(lambda: self.conv(Nd("app", BV(16), (ref,), "len"), ty))
            cands.append(lambda: self.conv(Nd("app", BV(8), (ref, self.index16(env)), "byte"), ty))
        if bs and ty == BOOL:
            b = r.choice(bs)
            ref = Nd("ref", b.ty, (), b)
            cands.append(lambda: Nd("app", BOOL, (Nd("app", BV(16), (ref,), "len"), const(16, r.randrange(self.bm + 2))),
                                    "eq"))
        return r.choice(cands)()

    def conv(self, e, ty):
        """Lleva un bv de ancho conocido al ancho `ty`."""
        w, t = e.ty[1], ty[1]
        if w == t:
            return e
        op = "trunc" if t < w else "zext"
        return Nd("app", ty, (Nd("raw", None, (), str(t)), e), op)

    def index16(self, env):
        r = self.r
        if r.random() < 0.45:
            return const(16, r.randrange(self.bm + 1))
        return self.conv(self.gen_scalar(BV(2), env, 1), BV(16))

    # bytes
    def gen_bytes(self, env, d):
        r, vis = self.r, self.vis(env)
        bt = self.rbytes()
        bs = [b for b in vis if b.ty[0] == "bytes"]
        c = r.random()
        if bs and (d <= 0 or c < 0.4):
            b = r.choice(bs)
            return Nd("ref", b.ty, (), b)
        if d <= 0 or c < 0.65:
            n = self.conv(self.gen_scalar(BV(2), env, max(d - 1, 0)), BV(16))
            es = [self.conv(self.gen_scalar(BV(3), env, max(d - 1, 0)), BV(8)) for _ in range(self.bm)]
            return Nd("app", bt, (n,) + tuple(es), "mkbytes")
        if c < 0.85:
            return Nd("app", bt, (self.gen_scalar(BOOL, env, d - 1), self.gen_bytes(env, d - 1),
                                  self.gen_bytes(env, d - 1)), "ite")
        return self.gen_let(bt, env, d)

    # option
    def gen_opt(self, ty, env, d):
        r, vis = self.r, self.vis(env)
        c = r.random()
        vs = [b for b in vis if b.ty == ty and b.kind == "var"]
        if vs and c < 0.3:
            b = r.choice(vs)
            return Nd("ref", ty, (), b)
        auxs = [a for a in self.aux if a["out"] == ty]
        if auxs and c < 0.7:
            return self.gen_call(r.choice(auxs), env, d)
        return Nd("some", ty, tuple(self.gen_scalar(t, env, d - 1) for t in ty[1]))

    def gen_call(self, a, env, d):
        args = tuple(self.gen(t, env, d - 1) for _, t in a["inputs"])
        return Nd("call", a["out"], args, a["name"])

    # let / match
    def gen_let(self, ty, env, d):
        r = self.r
        n = r.choice([1, 1, 2])
        bs, vals, cur = [], [], list(env)
        for _ in range(n):
            bt = self.rtype(cur)
            vals.append(self.gen(bt, cur, d - 1))
            b = self.new(cur, bt)
            bs.append(b)
            cur.append(b)
        body = self.gen(ty, cur, d - 1)
        return Nd("let", ty, tuple(vals) + (body,), bs)

    def gen_match(self, ty, env, d):
        r = self.r
        ot = ("option", tuple(self.rscalar() for _ in range(r.choice([1, 1, 2]))))
        scrut = self.gen_opt(ot, env, d - 1)
        cur, bs = list(env), []
        names = set()
        for t in ot[1]:
            b = self.new(cur, t)
            while b.name in names:
                b = self.new(cur, t)
            names.add(b.name)
            bs.append(b)
        some = self.gen(ty, list(env) + bs, d - 1)
        none = self.gen(ty, env, d - 1)
        return Nd("match", ty, (scrut, some, none), (bs, r.random() < 0.4))

    # fold
    def gen_fold(self, ty, env, d, masked=None):
        r = self.r
        self.folds -= 1
        bi = self.new(env, BV(4), "idx")
        bacc = self.new(env, ty)
        if r.random() < 0.07:
            bacc = B(bi.name, ty)               # acc y el índice con el mismo nombre
        lo = r.choice([0, 0, 1])
        hi = lo + r.randint(1, 4 - lo)       # el índice cabe en (bv 2)
        hi_nd = hi
        outer_idx = [b for b in self.vis(env) if b.kind == "idx"]
        if outer_idx and r.random() < 0.3:
            lo, hi_nd = 0, Nd("app", None, (Nd("idxnum", None, (), r.choice(outer_idx)), Nd("raw", None, (), "1")), "add")
        use_masked = ty[0] == "bv" and (masked if masked is not None else r.random() < 0.35)
        envs = list(env) + [bi, bacc]
        if use_masked:
            w = ty[1]
            m = r.choice([1, 2, (1 << w) - 1, r.randrange(1 << w)]) & ((1 << w) - 1)
            mk = const(w, m)
            init = Nd("app", ty, (self.gen_scalar(ty, env, d - 1), mk), "and")
            step = Nd("app", ty, (self.gen_scalar(ty, envs, d - 1), mk), "and")
            ref = Nd("ref", ty, (), bacc)
            inv = Nd("app", BOOL, (ref, mk), r.choice(["ule", "ule", "ult", "ule"]))
            if r.random() < 0.3:
                inv = self.gen_scalar(BOOL, list(env) + [bacc], 2)
            return Nd("fold", ty, (init, step, inv if r.random() < 0.85 else None), (bi, lo, hi_nd, bacc))
        init = self.gen(ty, env, d - 1)
        step = self.gen(ty, envs, d - 1)
        inv = None
        if r.random() < 0.5:
            c = r.random()
            ref = Nd("ref", ty, (), bacc)
            if c < 0.2:
                inv = Nd("bool", BOOL, (), r.random() < 0.7)
            elif c < 0.35 and ty[0] == "bv":
                inv = Nd("app", BOOL, (ref, const(ty[1], (1 << ty[1]) - 1)), "ule")      # tautología
            else:
                inv = self.gen_scalar(BOOL, list(env) + [bacc], 2)
        return Nd("fold", ty, (init, step, inv), (bi, lo, hi_nd, bacc))

    def gen_foldraw(self, ty, env, d):
        r = self.r
        self.folds -= 1
        bacc = self.new(env, ty)
        init = self.gen(ty, env, d - 1)
        steps = [self.gen(ty, list(env) + [bacc], d - 1) for _ in range(r.randint(1, 3))]
        fold = Nd("foldraw", ty, (init,) + tuple(steps), bacc)
        if r.random() < 0.6:
            # La mitad de las veces como `expand` (el invariante usa el nombre del acumulador del pliegue); la
            # otra mitad con un nombre distinto, el caso del hallazgo H1 ya corregido (ver el final del archivo).
            binv = bacc if r.random() < 0.5 else self.new(env, ty)
            ref = Nd("ref", ty, (), binv)
            if ty[0] == "bv" and r.random() < 0.4:
                inv = Nd("app", BOOL, (ref, const(ty[1], r.randrange(1 << ty[1]))), "ule")
            else:
                inv = self.gen_scalar(BOOL, list(env) + [binv], 2)
            return Nd("finv", ty, (fold, inv), binv)
        return fold

    # escalares
    def gen_scalar(self, ty, env, d):
        r = self.r
        if d <= 0 or r.random() < 0.12:
            return self.leaf(ty, env)
        opts = ["let", "let", "match", "ite", "ite"]
        if self.folds > 0:
            opts += ["fold", "fold", "fold"]
            if not any(b.kind == "idx" for b in env):
                opts += ["foldraw"]
        auxs = [a for a in self.aux if a["out"] == ty]
        if auxs:
            opts += ["call", "call"]
        if ty == BOOL:
            opts += ["cmp"] * 4 + ["logic", "logic", "not"]
        else:
            opts += ["bin"] * 5 + ["un", "ext", "wide"]
        k = r.choice(opts)
        if k in ("ext", "wide") and ty[1] >= 8:
            k = "bin"
        sub = d - 1
        if k == "let":
            return self.gen_let(ty, env, d)
        if k == "match":
            return self.gen_match(ty, env, d)
        if k == "ite":
            return Nd("app", ty, (self.gen_scalar(BOOL, env, sub), self.gen_scalar(ty, env, sub),
                                  self.gen_scalar(ty, env, sub)), "ite")
        if k == "fold":
            return self.gen_fold(ty, env, d)
        if k == "foldraw":
            return self.gen_foldraw(ty, env, d)
        if k == "call":
            return self.gen_call(r.choice(auxs), env, d)
        if k == "cmp":
            w = r.choice([2, 3, 4])
            op = r.choice(["eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sge"])
            if r.random() < 0.15:
                return Nd("app", BOOL, (self.gen_scalar(BOOL, env, sub), self.gen_scalar(BOOL, env, sub)),
                          r.choice(["eq", "ne"]))
            return Nd("app", BOOL, (self.gen_scalar(BV(w), env, sub), self.gen_scalar(BV(w), env, sub)), op)
        if k == "logic":
            n = r.choice([2, 2, 3])
            return Nd("app", BOOL, tuple(self.gen_scalar(BOOL, env, sub) for _ in range(n)), r.choice(["all", "any"]))
        if k == "not":
            return Nd("app", BOOL, (self.gen_scalar(BOOL, env, sub),), "not")
        w = ty[1]
        if k == "bin":
            op = r.choice(["add", "sub", "mul", "and", "or", "xor", "udiv", "urem", "shl", "lshr", "sdiv", "srem"])
            n = 3 if op in ("add", "mul", "and", "or", "xor") and r.random() < 0.2 else 2
            return Nd("app", ty, tuple(self.gen_scalar(ty, env, sub) for _ in range(n)), op)
        if k == "un":
            return Nd("app", ty, (self.gen_scalar(ty, env, sub),), r.choice(["not", "neg"]))
        if k == "ext":
            if w > 2 and r.random() < 0.5:
                return self.conv(self.gen_scalar(BV(r.randint(2, w - 1)), env, sub), ty)
            u = r.randint(w + 1, 8)
            return self.conv(self.gen_scalar(BV(u), env, sub), ty)
        # wide: operar en un ancho mayor y truncar
        u = r.randint(w + 1, 8)
        op = r.choice(["add", "mul", "sub", "xor"])
        a, b = (self.conv(self.gen_scalar(ty, env, sub), BV(u)) for _ in range(2))
        return self.conv(Nd("app", BV(u), (a, b), op), ty)


# --- Reescrituras (válidas) y mutaciones (no válidas) ----------------------------------------------------

def rebuild(nd, fn):
    """Reconstruye el árbol aplicando fn(nodo, hijos_nuevos); las ligaduras se comparten."""
    a = tuple(rebuild(c, fn) if c is not None else None for c in nd.a)
    return fn(nd, a)


def sound_rewrite(nd, rng, p=0.3):
    names = NOMBRES

    def fn(n, a):
        new = Nd(n.k, n.ty, a, n.x)
        if n.ty is None or n.k in ("raw", "idxnum", "foldraw", "finv", "some", "none", "call") \
                or (n.ty[0] == "option") or rng.random() > p:
            return new
        ty = n.ty
        c = rng.random()
        if new.k == "app" and new.x in COMM and len(a) == 2 and c < 0.4:
            return Nd("app", ty, a[::-1], new.x)
        if new.k == "app" and new.x == "ite" and c < 0.5:
            return Nd("app", ty, (Nd("app", BOOL, (a[0],), "not"), a[2], a[1]), "ite")
        if ty[0] == "bv" and c < 0.65:
            op, ident = rng.choice([("add", 0), ("xor", 0), ("or", 0), ("mul", 1)])
            return Nd("app", ty, (new, const(ty[1], ident)), op)
        if ty == BOOL and c < 0.65:
            return Nd("app", BOOL, (Nd("app", BOOL, (new,), "not"),), "not")
        if c < 0.85:                                        # (let ((n e)) n)
            b = B(rng.choice(names), ty)
            return Nd("let", ty, (new, Nd("ref", ty, (), b)), [b])
        if ty[0] in ("bv", "bool"):                         # ligadura muerta que puede sombrear
            b = B(rng.choice(names), ty)
            return Nd("let", ty, (Nd("bool", BOOL, (), True) if ty == BOOL else const(ty[1], 0), new), [b])
        return new

    return rebuild(nd, fn)


SWAPS = {"add": "sub", "sub": "add", "and": "or", "or": "xor", "xor": "and", "mul": "add", "ult": "ule",
         "ule": "ult", "ugt": "uge", "uge": "ugt", "eq": "ne", "ne": "eq", "all": "any", "any": "all",
         "shl": "lshr", "lshr": "shl", "udiv": "urem", "urem": "udiv", "slt": "sge", "sge": "slt"}


def mutate(nd, rng):
    targets = [n for n in walk(nd) if n.k in ("const", "bool") or (n.k == "app" and (n.x in SWAPS or n.x == "ite"))]
    if not targets:
        return nd
    t = rng.choice(targets)

    def fn(n, a):
        if n is not t:
            return Nd(n.k, n.ty, a, n.x)
        if n.k == "const":
            w = n.ty[1]
            return const(w, (n.x + rng.randint(1, (1 << w) - 1)) & ((1 << w) - 1))
        if n.k == "bool":
            return Nd("bool", BOOL, (), not n.x)
        if n.x == "ite":
            return Nd("app", n.ty, (a[0], a[2], a[1]), "ite")
        op = SWAPS[n.x]
        if op == "sub" and len(a) != 2:
            op = "or"
        return Nd("app", n.ty, a, op)

    return rebuild(nd, fn)


def paint(nd, inputs, rng, rename=0.6, tries=30):
    """Texto del árbol con nombres de ligadura reasignados al azar; None si no se encuentra pintura válida."""
    binders = {}
    for n in walk(nd):
        if n.k == "let" or n.k == "match":
            for b in (n.x if n.k == "let" else n.x[0]):
                binders[b.id] = b
        elif n.k == "fold":
            binders[n.x[0].id] = n.x[0]
            binders[n.x[3].id] = n.x[3]
        elif n.k in ("foldraw", "finv"):
            binders[n.x.id] = n.x
    for _ in range(tries):
        naming = {i: rng.choice(NOMBRES) for i in binders if rng.random() < rename}
        try:
            return Render(naming).r(nd, scope_of(inputs))
        except Bad:
            continue
    return None


# --- Aux, definiciones, entradas ------------------------------------------------------------------------

def make_inputs(rng, bm, allow_bytes=True, maxn=3):
    n = rng.randint(1, maxn)
    names = rng.sample(NOMBRES_ENTRADA, n + 1)
    ins = []
    for k in range(n):
        ins.append(B(names[k], rng.choice([BV(2), BV(2), BV(3), BV(3), BV(4), BOOL]), "input"))
    if allow_bytes and rng.random() < 0.55:
        ins.append(B(names[n], ("bytes", bm), "input"))
        rng.shuffle(ins)
    return ins


def opt_semantics(g, ty, env, d):
    """Semántica de salida option: (ite c (some ...) none) con variantes."""
    fields = lambda: Nd("some", ty, tuple(g.gen_scalar(t, env, d - 1) for t in ty[1]))
    e = Nd("app", ty, (g.gen_scalar(BOOL, env, d - 1), fields(), Nd("none", ty)), "ite")
    if g.r.random() < 0.4:
        e = Nd("app", ty, (g.gen_scalar(BOOL, env, d - 1), fields(), e), "ite")
    return e


def make_aux(rng, bm, count):
    aux, texts = [], []
    for k in range(count):
        ins = make_inputs(rng, bm, allow_bytes=True, maxn=2)
        out = rng.choice([BV(2), BV(3), BV(4), BOOL, BOOL, ("option", (BV(3),)), ("option", (BV(2), BOOL))])
        g = Gen(rng, aux, bm, folds=1)
        sem = opt_semantics(g, out, ins, 2) if out[0] == "option" else g.gen_scalar(out, ins, rng.randint(1, 3))
        name = f"g{k + 1}"
        txt = (f"(computation {name} " + " ".join(f"(input {b.name} {tystr(b.ty)})" for b in ins)
               + f" (output {tystr(out)}) (semantics {render(sem, ins)}))")
        aux.append({"name": name, "inputs": [(b.name, b.ty) for b in ins], "out": out})
        texts.append(txt)
    return aux, texts


def comp_text(name, ins, out, sem_text):
    return (f"(computation {name} " + " ".join(f"(input {b.name} {tystr(b.ty)})" for b in ins)
            + f" (output {tystr(out)}) (semantics {sem_text}))")


BYTES_R = [0, 1, 2, 3, 4, 7, 8, 15, 16, 127, 128, 255]


def domain(ty, bm):
    if ty[0] == "bv":
        return list(range(1 << ty[1]))
    if ty[0] == "bool":
        return [False, True]
    d = [()] + [(v,) for v in range(256)]
    if ty[1] >= 2:
        d += [(u, v) for u in BYTES_R for v in BYTES_R]
    return d


def input_space(types, rng, cap=CAP_ENTRADAS):
    """(entradas, exhaustivo): producto completo si cabe en `cap`; si no, muestra reproducible."""
    doms = [domain(t, 0) for t in types]
    size = math.prod(len(d) for d in doms)
    if size <= cap:
        return [tuple(c) for c in itertools.product(*doms)], True
    out = []
    for idx in rng.sample(range(size), cap):
        row = []
        for d in reversed(doms):
            idx, m = divmod(idx, len(d))
            row.append(d[m])
        out.append(tuple(reversed(row)))
    return out, False


def ev(node, names, args):
    try:
        return interp.evaluate(node, dict(zip(names, args)))
    except interp.Undefined:
        return UNDEF


UNDEF = object()


def tup(v):
    return tuple(v) if isinstance(v, list) else v


# --- Ejecución de las cuatro baterías ---------------------------------------------------------------------

class Informe:
    def __init__(self):
        self.stats = {}
        self.fallos = {"O1": [], "O2": [], "O3": [], "O4": []}
        self.rechazados = 0
        self.generados = 0
        self.tiempos = {}

    def cuenta(self, k, n=1):
        self.stats[k] = self.stats.get(k, 0) + n


def cobertura(inf, text):
    for clave, patron in (("fold", "(fold "), ("fold_con_invariant", "(invariant"), ("fold%", "(fold% "),
                          ("finv%", "(finv% "), ("match", "(match "), ("call", "(call "), ("let", "(let "),
                          ("nombre_interno_x%", "x%"), ("nombre__0", "_0"), ("nombre_b.len", "b.len")):
        if patron in text:
            inf.cuenta("cob_" + clave)


def definicion(texts, extra):
    return "(efch 0.1 " + " ".join(texts) + " " + extra + ")"


def correr_propiedades(inf, t_ini):
    t0 = time.time()
    for case in range(N_PROP):
        if time.time() - t0 > FASE_MAX_S["prop"]:
            inf.cuenta("prop_cortada_por_tiempo")
            break
        rng = random.Random(f"{SEMILLA}-p-{case}")
        bm = rng.choice([1, 2])
        aux, texts = make_aux(rng, bm, rng.choice([0, 1, 1, 2]))
        vs = make_inputs(rng, bm, maxn=3)
        g = Gen(rng, aux, bm)
        kind = rng.random()
        try:
            if rng.random() < 0.07:
                # Símbolos de Z3 de las entradas: `b.len` y `b[0]` frente a la longitud y el byte 0 de `b`.
                vs = [B("b", ("bytes", bm), "input")]
                if rng.random() < 0.5:
                    vs.append(B("b.len", BV(16), "input"))
                    body, tag = "(eq b.len (len b))", "colision-b.len"
                else:
                    vs.append(B("b[0]", BV(8), "input"))
                    body = "(ite (ugt (len b) (bv 16 0)) (eq b[0] (byte b (bv 16 0))) true)"
                    tag = "colision-b[0]"
                if rng.random() < 0.5:
                    vs.append(B("x", BV(2), "input"))
                    body = f"(all {body} (ule x (bv 2 3)))" if rng.random() < 0.5 else f"(any {body} (eq x x))"
                rng.shuffle(vs)
            elif kind < 0.40:
                ty = rng.choice([BV(2), BV(3), BV(4), BOOL])
                e = g.gen_scalar(ty, vs, rng.randint(2, 4))
                t1 = paint(e, vs, rng, rename=0.0)
                e2 = sound_rewrite(e, rng, 0.25) if rng.random() < 0.7 else e
                t2 = paint(e2, vs, rng, rename=0.7)
                if t1 is None or t2 is None:
                    inf.rechazados += 1
                    continue
                body = f"(eq {t1} {t2})"
                tag = "alfa/reescritura"
            elif kind < 0.50:
                ty = rng.choice([BV(2), BV(3), BV(4), BOOL])
                e = g.gen_scalar(ty, vs, rng.randint(2, 4))
                t1, t2 = paint(e, vs, rng, rename=0.0), paint(mutate(e, rng), vs, rng, rename=0.5)
                if t1 is None or t2 is None:
                    inf.rechazados += 1
                    continue
                body, tag = f"(eq {t1} {t2})", "mutada"
            elif kind < 0.62:
                w = rng.choice([2, 3, 4])
                e = g.gen_scalar(BV(w), vs, rng.randint(2, 4))
                t1 = paint(e, vs, rng)
                if t1 is None:
                    inf.rechazados += 1
                    continue
                body, tag = f"(ule {t1} (bv {w} {(1 << w) - 1}))", "tautologia-ule"
            elif kind < 0.72:
                p = g.gen_scalar(BOOL, vs, rng.randint(2, 3))
                t1 = paint(p, vs, rng)
                if t1 is None:
                    inf.rechazados += 1
                    continue
                body, tag = f"(or {t1} (not {t1}))", "tercio-excluso"
            elif kind < 0.86:
                w = rng.choice([2, 3, 4])
                g.folds = 3
                f = g.gen_fold(BV(w), vs, 3, masked=True)
                m = f.a[0].a[1].x
                t1 = paint(f, vs, rng)
                if t1 is None:
                    inf.rechazados += 1
                    continue
                op, bound = rng.choice([("ule", m), ("ult", m), ("ule", max(m - 1, 0))])
                body, tag = f"({op} {t1} (bv {w} {bound}))", "fold-enmascarado"
            else:
                p = g.gen_scalar(BOOL, vs, rng.randint(2, 4))
                body, tag = paint(p, vs, rng), "bool-aleatoria"
                if body is None:
                    inf.rechazados += 1
                    continue
            qv = " ".join(f"({b.name} {tystr(b.ty)})" for b in vs)
            text = definicion(texts, f"(property p (forall ({qv}) {body}))")
            try:
                d = core.load_definition(text)
            except core.EFCHError:
                inf.rechazados += 1
                continue
        except core.EFCHError:
            inf.rechazados += 1
            continue
        prop = d.properties[0]
        cobertura(inf, text)
        inf.generados += 1
        inf.cuenta("O1_propiedades")
        try:
            res = smt.check_property(prop, T)
        except Exception as e:      # noqa: BLE001  una excepción del verificador es un fallo, no un rechazo
            inf.fallos["O1"].append({"tag": tag, "texto": text, "estado": "excepción", "detalle": repr(e)[:300]})
            continue
        inf.cuenta(f"O1_{res.status}")
        names = [n for n, _ in prop.variables]
        types = [t for _, t in prop.variables]
        if res.status == "probado":
            space, exhaustivo = input_space(types, rng)
            inf.cuenta("O1_entradas_evaluadas", len(space))
            inf.cuenta("O1_probado_exhaustivo" if exhaustivo else "O1_probado_muestreado")
            for args in space:
                v = ev(prop.body, names, args)
                if v is not True:
                    inf.fallos["O1"].append({"tag": tag, "texto": text, "entrada": dict(zip(names, args)),
                                             "interprete": "indefinido" if v is UNDEF else v, "estado": "probado"})
                    break
        elif res.status == "refutado":
            ce = {k: tup(v) for k, v in (res.counterexample or {}).items()}
            v = ev(prop.body, names, [ce[n] for n in names])
            if v is True:
                inf.fallos["O1"].append({"tag": tag, "texto": text, "entrada": ce, "interprete": v,
                                         "estado": "refutado"})
            elif v is UNDEF:
                inf.cuenta("O1_refutado_por_indefinicion")
        elif "inconsistencia" in (res.detail or ""):
            inf.fallos["O1"].append({"tag": tag, "texto": text, "estado": "inconsistencia", "detalle": res.detail})
    inf.tiempos["O1"] = time.time() - t0


def correr_candidatas(inf, c_jobs):
    t0 = time.time()
    for case in range(N_CAND):
        if time.time() - t0 > FASE_MAX_S["cand"]:
            inf.cuenta("cand_cortada_por_tiempo")
            break
        rng = random.Random(f"{SEMILLA}-c-{case}")
        bm = rng.choice([1, 2])
        aux, texts = make_aux(rng, bm, rng.choice([0, 1, 1, 2]))
        ins = make_inputs(rng, bm, maxn=3)
        g = Gen(rng, aux, bm)
        r = rng.random()
        out = BOOL if r < 0.2 else rng.choice([BV(2), BV(3), BV(4)]) if r < 0.8 else \
            (g.rbytes() if r < 0.92 else ("option", (BV(3), BOOL)))
        try:
            if out[0] == "option":
                spec = opt_semantics(g, out, ins, 3)
            else:
                spec = g.gen(out, ins, rng.randint(2, 4))
            mode = rng.random()
            if mode < 0.55:
                cand = sound_rewrite(spec, rng, 0.25)
            elif mode < 0.8:
                cand = mutate(sound_rewrite(spec, rng, 0.15), rng)
            else:
                cand = mutate(spec, rng)
            ts, tc = paint(spec, ins, rng, rename=0.0), paint(cand, ins, rng, rename=0.7)
            if ts is None or tc is None:
                inf.rechazados += 1
                continue
            text = definicion(texts, comp_text("f", ins, out, ts))
            d = core.load_definition(text)
            ctext = f"(efch 0.1 (candidate c (implements f) (body {tc})))"
            [cd] = core.load_candidates(ctext, d)
        except core.EFCHError:
            inf.rechazados += 1
            continue
        comp = d.computations["f"]
        cobertura(inf, text)
        inf.generados += 1
        inf.cuenta("O2_candidatas")
        # La especificación sola también va al oráculo C.
        c_jobs.append((comp, comp.semantics, text, "spec"))
        try:
            rep = pipeline.verify_candidate(comp, cd.body, T)
        except Exception as e:      # noqa: BLE001
            inf.fallos["O2"].append({"texto": text, "candidata": ctext, "estado": "excepción", "detalle": repr(e)[:300]})
            continue
        inf.cuenta(f"O2_{rep['estado']}")
        if rep["estado"] != "probado":
            if any("inconsistencia" in (o.get("detalle") or "") for o in rep["obligaciones"]):
                inf.fallos["O2"].append({"texto": text, "candidata": ctext, "estado": "inconsistencia",
                                         "detalle": rep["obligaciones"]})
            continue
        names = [n for n, _ in comp.inputs]
        space, exhaustivo = input_space([t for _, t in comp.inputs], rng)
        inf.cuenta("O2_entradas_evaluadas", len(space))
        inf.cuenta("O2_probado_exhaustivo" if exhaustivo else "O2_probado_muestreado")
        c_jobs.append((comp, cd.body, text + "\n" + ctext, "cand"))
        for args in space:
            vc = ev(cd.body, names, args)
            vs = ev(comp.semantics, names, args)
            if vc is UNDEF or (vs is not UNDEF and vc != vs):
                inf.fallos["O2"].append({"texto": text, "candidata": ctext, "estado": "probado",
                                         "entrada": dict(zip(names, args)),
                                         "especificacion": "indefinida" if vs is UNDEF else vs,
                                         "candidata_valor": "indefinida" if vc is UNDEF else vc})
                break
    inf.tiempos["O2"] = time.time() - t0


def correr_c(inf, c_jobs):
    t0 = time.time()
    jobs = []
    for comp, body, text, kind in c_jobs:
        idents = ["in_" + backend_c.c_ident(n) for n, _ in comp.inputs]
        for n, t in comp.inputs:
            if t[0] == "bytes":
                idents.append("in_" + backend_c.c_ident(n) + "_len")
        if len(set(idents)) != len(idents):
            inf.cuenta("O3_omitido_colision_de_nombres_C")     # limitación conocida (EXP-013, no corregida)
            continue
        jobs.append((comp, body, text, kind))
    # Candidatas primero (más valiosas), luego especificaciones, con tope.
    jobs.sort(key=lambda j: j[3] != "cand")
    jobs = jobs[:C_MAX_FUNCIONES]
    rng = random.Random(f"{SEMILLA}-c-oraculo")
    with tempfile.TemporaryDirectory() as tmp:
        for start in range(0, len(jobs), 30):
            if time.time() - t0 > FASE_MAX_S["c"]:
                inf.cuenta("O3_cortada_por_tiempo")
                break
            batch = jobs[start:start + 30]
            funcs = [(c, b, f"efch_t{start + k}") for k, (c, b, _, _) in enumerate(batch)]
            try:
                lib = native.build_library(tmp, backend_c.emit_unit(funcs))
            except Exception as e:      # noqa: BLE001
                inf.fallos["O3"].append({"texto": "\n".join(j[2] for j in batch), "estado": "no compila",
                                         "detalle": str(e)[-1500:]})
                continue
            for (comp, body, text, kind), (_, _, fname) in zip(batch, funcs):
                call = native.bind(lib, comp, fname)
                names = [n for n, _ in comp.inputs]
                space, _ = input_space([t for _, t in comp.inputs], rng, CAP_C)
                inf.cuenta("O3_funciones_" + kind)
                for args in space:
                    v = ev(body, names, args)
                    if v is UNDEF:
                        continue
                    inf.cuenta("O3_entradas_comparadas")
                    got = call(args)
                    if got != v:
                        inf.fallos["O3"].append({"texto": text, "tipo": kind, "entrada": dict(zip(names, args)),
                                                 "interprete": v, "c": got})
                        break
    inf.tiempos["O3"] = time.time() - t0


def huella(node, names, types):
    """Valor del árbol en todo el dominio (escalares), para comparar semántica."""
    space, _ = input_space(types, random.Random(0), 100000)
    out = []
    for args in space:
        v = ev(node, names, args)
        out.append("U" if v is UNDEF else v)
    return tuple(out)


def correr_canonico(inf):
    t0 = time.time()
    sigs = [[("_0", BV(3)), ("_1", BV(3))], [("x", BV(3)), ("_0", BV(3))], [("_0", BV(3)), ("x", BV(3))],
            [("_1", BV(2)), ("_0", BOOL)]]
    pool = ["_0", "_1", "_2", "x", "x%1", "fold%0", "acc%0"]
    grupos = {}
    for case in range(N_CANON):
        if time.time() - t0 > FASE_MAX_S["canon"]:
            inf.cuenta("O4_cortada_por_tiempo")
            break
        rng = random.Random(f"{SEMILLA}-k-{case}")
        sig = rng.choice(sigs)
        ins = [B(n, t, "input") for n, t in sig]
        g = Gen(rng, [], 2, folds=1, pool=pool)
        out = rng.choice([BV(3), BV(3), BOOL])
        try:
            e = g.gen_scalar(out, ins, rng.randint(1, 3))
            for variante in range(2):
                e2 = e if variante == 0 else sound_rewrite(e, rng, 0.15)
                txt = paint(e2, ins, rng, rename=0.8)
                if txt is None:
                    inf.rechazados += 1
                    continue
                text = comp_text("f", ins, out, txt)
                d = core.load_definition("(efch 0.1 " + text + ")")
                comp = d.computations["f"]
                inf.cuenta("O4_arboles")
                key = (tuple(sig), out, core.canonical(comp.semantics, comp.inputs), comp.canonical())
                grupos.setdefault(key[:3], []).append((text, comp))
        except core.EFCHError:
            inf.rechazados += 1
    for key, items in grupos.items():
        if len(items) < 2:
            continue
        names = [n for n, _ in key[0]]
        types = [t for _, t in key[0]]
        ref_text, ref = items[0]
        base = huella(ref.semantics, names, types)
        for text, comp in items[1:]:
            inf.cuenta("O4_pares_misma_clave")
            if comp.canonical() != ref.canonical():
                inf.fallos["O4"].append({"texto": text, "otro": ref_text, "estado": "computation.canonical difiere"})
            if huella(comp.semantics, names, types) != base:
                inf.fallos["O4"].append({"texto": text, "otro": ref_text, "estado": "misma clave, semántica distinta",
                                         "clave": key[2]})
    inf.stats["O4_clases_con_colision"] = sum(1 for v in grupos.values() if len(v) > 1)
    inf.tiempos["O4"] = time.time() - t0


_INFORME = None


def informe():
    global _INFORME
    if _INFORME is None:
        t0 = time.time()
        inf = Informe()
        c_jobs = []
        correr_propiedades(inf, t0)
        correr_candidatas(inf, c_jobs)
        correr_c(inf, c_jobs)
        correr_canonico(inf)
        inf.tiempos["total"] = time.time() - t0
        print("\n[solidez aleatoria] semilla", SEMILLA, "rechazados por el generador:", inf.rechazados,
              file=sys.stderr)
        for k in sorted(inf.stats):
            print(f"  {k}: {inf.stats[k]}", file=sys.stderr)
        print("  tiempos (s):", {k: round(v, 1) for k, v in inf.tiempos.items()}, file=sys.stderr)
        print("  fallos:", {k: len(v) for k, v in inf.fallos.items()}, file=sys.stderr)
        _INFORME = inf
    return _INFORME


def resumen(f):
    return "\n".join(f"{k}: {v}" for k, v in f.items())


class TestSolidezAleatoria(unittest.TestCase):
    def test_o1_propiedades(self):
        inf = informe()
        self.assertGreater(inf.stats.get("O1_probado", 0), 20, inf.stats)
        self.assertGreater(inf.stats.get("O1_refutado", 0), 20, inf.stats)
        fs = [f for f in inf.fallos["O1"] if f not in KNOWN_O1]
        self.assertEqual(fs, [], "\n\n".join(resumen(f) for f in fs[:3]))

    def test_o2_candidatas(self):
        inf = informe()
        self.assertGreater(inf.stats.get("O2_probado", 0), 20, inf.stats)
        fs = inf.fallos["O2"]
        self.assertEqual(fs, [], "\n\n".join(resumen(f) for f in fs[:3]))

    def test_o3_c_coincide_con_interprete(self):
        inf = informe()
        self.assertGreater(inf.stats.get("O3_funciones_cand", 0), 10, inf.stats)
        fs = inf.fallos["O3"]
        self.assertEqual(fs, [], "\n\n".join(resumen(f) for f in fs[:3]))

    def test_o4_canonica(self):
        inf = informe()
        self.assertGreater(inf.stats.get("O4_pares_misma_clave", 0), 50, inf.stats)
        fs = inf.fallos["O4"]
        self.assertEqual(fs, [], "\n\n".join(resumen(f) for f in fs[:3]))


KNOWN_O1 = []


class TestHallazgosAbiertos(unittest.TestCase):
    """H1 (23/10/2026, hallado por este generador; corregido el mismo día con un nombre fresco para el
    acumulador de las subpruebas, `smt._invariant_obligations`): captura de nombres en
    `smt._invariant_obligations`. Hace `rename_free(paso, {f.attr: acc})` y `rename_free` no evita que el
    nombre nuevo (`g`, el del acumulador de `finv%`) sea capturado por un `match`/`let` del paso que liga
    ese mismo nombre. Solo es alcanzable con las formas internas `finv%`/`fold%` escritas a mano con
    nombres de acumulador distintos: `expand` (la sintaxis `(fold ... (invariant ...))`) usa el mismo nombre
    para ambas y el renombrado es la identidad. Causa probable: falta evitar la captura (como hace
    `Elaborator._fresh` en `call`) o usar un nombre fresco para el acumulador de las subpruebas."""

    # La propiedad es falsa: el valor es (3 + 1) mod 4 = 0, no 3. Con la captura, el paso se lee como
    # «g + 1» con g = 2 (valor del patrón), «conserva» el invariante `g = 3` y se acepta.
    PROP = ("(eq (finv% g (fold% x (bv 2 3) (match (some (bv 2 2)) ((some g) (add x (bv 2 1))) (none x))) "
            "(eq g (bv 2 3))) (bv 2 3))")

    def test_h1_probado_falso_por_captura_en_obligaciones_de_invariante(self):
        d = core.load_definition(f"(efch 0.1 (property q (forall ((p (bv 2))) {self.PROP})))")
        self.assertNotEqual(smt.check_property(d.properties[0], T).status, "probado")

    # Mismo origen con tipos distintos: Z3 lanza una excepción (sorts bv3 y bv2) en lugar de un estado.
    def test_h1_excepcion_de_z3_por_la_misma_captura(self):
        d = core.load_definition(
            "(efch 0.1 (property q (forall ((p (bv 2))) (eq (finv% g (fold% x (bv 2 1) "
            "(match (some (bv 3 7)) ((some g) x) (none p))) true) p))))")
        smt.check_property(d.properties[0], T)

    def test_h1_la_sintaxis_de_usuario_no_lo_alcanza(self):
        """Con `(fold ... (invariant ...))` el pliegue y el invariante comparten el nombre del acumulador."""
        d = core.load_definition("""(efch 0.1 (property q (forall ((p (bv 2)))
          (eq (fold i 0 1 (g (bv 2 3)) (match (some (bv 2 2)) ((some z) (add g (bv 2 1))) (none g))
                (invariant (eq g (bv 2 3))))
              (bv 2 3)))))""")
        self.assertNotEqual(smt.check_property(d.properties[0], T).status, "probado")

if __name__ == "__main__":
    unittest.main()
