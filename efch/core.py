"""
Núcleo semántico EFCH 0.1: tipos, elaboración y forma canónica.

Una definición (.efch) se lee como expresiones S, se expanden las formas
acotadas (`first`, `reduce`) y se elabora a un árbol tipado (`Node`) cuya
semántica definen `interp.py` (evaluación) y `smt.py` (lógica de vectores de
bits). La forma canónica de ese árbol, con nombres locales normalizados, da
la identidad semántica de cada computación.

Tipos:
    (bv N)            vector de N bits sin signo, 1 <= N <= 128 (las entradas
                      y salidas de una computación, como máximo 64)
    bool
    (bytes M)         cadena de 0..M bytes (M <= 64)
    (option T...)     ausencia o tupla de escalares (bv o bool)
"""

import re
import hashlib
from dataclasses import dataclass

from .sexpr import Num, SList, Str, Sym, SyntaxError_, dumps, parse

LANGUAGE_VERSION = "0.1"
MAX_BYTES = 64
MAX_BV = 128


class EFCHError(Exception):
    def __init__(self, msg, node=None):
        pos = getattr(node, "pos", None)
        super().__init__(f"{pos[0]}:{pos[1]}: {msg}" if pos else msg)
        self.pos = pos


# --- Tipos -------------------------------------------------------------------

def BV(w):
    return ("bv", w)


BOOL = ("bool",)
LEN_T = BV(16)
BYTE_T = BV(8)


def BYTES(m):
    return ("bytes", m)


def OPTION(*ts):
    return ("option", tuple(ts))


def is_bv(t):
    return t[0] == "bv"


def is_scalar(t):
    return t[0] in ("bv", "bool")


def type_str(t):
    if t[0] == "bv":
        return f"(bv {t[1]})"
    if t[0] == "bool":
        return "bool"
    if t[0] == "bytes":
        return f"(bytes {t[1]})"
    return "(option " + " ".join(type_str(x) for x in t[1]) + ")"


def parse_type(sx):
    if isinstance(sx, Sym) and sx.name == "bool":
        return BOOL
    if isinstance(sx, SList) and sx.head() in ("bv", "bytes") and len(sx.items) == 2 \
            and isinstance(sx.items[1], Num):
        n = sx.items[1].value
        if sx.head() == "bv" and 1 <= n <= MAX_BV:
            return BV(n)
        if sx.head() == "bytes" and 0 <= n <= MAX_BYTES:
            return BYTES(n)
    if isinstance(sx, SList) and sx.head() == "option":
        ts = tuple(parse_type(x) for x in sx.items[1:])
        if not all(is_scalar(t) for t in ts):
            raise EFCHError("los campos de option deben ser escalares", sx)
        return OPTION(*ts)
    raise EFCHError(f"tipo no reconocido: {dumps(sx)}", sx)


# --- Árbol tipado ------------------------------------------------------------

@dataclass(frozen=True)
class Node:
    op: str
    args: tuple
    ty: tuple
    attr: object = None


ARITH = ("add", "sub", "mul", "udiv", "urem", "and", "or", "xor", "shl", "lshr", "sdiv", "srem", "ashr")
ASSOC = ("add", "mul", "and", "or", "xor")
CMP = ("eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge")
SIGNED_CMP = ("slt", "sle", "sgt", "sge")
REDUCE_OPS = ASSOC + ("all", "any")


def mask(w):
    return (1 << w) - 1


# --- Expansión de formas acotadas ----------------------------------------------

def _const_eval(sx):
    if isinstance(sx, Num):
        return sx.value
    if isinstance(sx, SList) and sx.head() in ("add", "sub", "mul", "min", "max") and len(sx.items) == 3:
        a, b = _const_eval(sx.items[1]), _const_eval(sx.items[2])
        return {"add": a + b, "sub": a - b, "mul": a * b, "min": min(a, b), "max": max(a, b)}[sx.head()]
    raise EFCHError(f"se esperaba una cota constante, no {dumps(sx)}", sx)


def _subst(sx, name, value):
    """Sustituye el símbolo `name` por el número `value`, respetando ligaduras."""
    if isinstance(sx, Sym):
        return Num(value, sx.pos) if sx.name == name else sx
    if not isinstance(sx, SList) or not sx.items:
        return sx
    head = sx.head()
    if head in ("first", "each", "reduce"):
        var_pos = 2 if head == "reduce" else 1
        if isinstance(sx.items[var_pos], Sym) and sx.items[var_pos].name == name:
            # El cuerpo vuelve a ligar el nombre: solo se sustituyen las cotas.
            items = list(sx.items)
            for k in (var_pos + 1, var_pos + 2):
                items[k] = _subst(items[k], name, value)
            return SList(tuple(items), sx.pos)
    if head == "fold" and len(sx.items) == 7:
        inner = _subst(SList(sx.items[:6], sx.pos), name, value)
        inv = sx.items[6]
        acc = sx.items[4].items[0] if isinstance(sx.items[4], SList) and sx.items[4].items else None
        if not (isinstance(acc, Sym) and acc.name == name):
            inv = _subst(inv, name, value)
        return SList((*inner.items, inv), sx.pos)
    if head == "fold" and len(sx.items) == 6 and isinstance(sx.items[4], SList) and len(sx.items[4].items) == 2:
        # (fold i LO HI (acc INIT) STEP): i y acc se ligan en STEP; INIT y las cotas ven el exterior.
        _, var, lo, hi, (acc, init), step = sx.items[0], sx.items[1], sx.items[2], sx.items[3], \
            sx.items[4].items, sx.items[5]
        bound = {x.name for x in (var, acc) if isinstance(x, Sym)}
        items = (sx.items[0], var, _subst(lo, name, value), _subst(hi, name, value),
                 SList((acc, _subst(init, name, value)), sx.items[4].pos),
                 step if name in bound else _subst(step, name, value))
        return SList(items, sx.pos)
    if head == "let" and len(sx.items) == 3 and isinstance(sx.items[1], SList):
        new_bindings, shadowed = [], False
        for b in sx.items[1].items:
            if isinstance(b, SList) and len(b.items) == 2:
                val = b.items[1] if shadowed else _subst(b.items[1], name, value)
                new_bindings.append(SList((b.items[0], val), b.pos))
                if isinstance(b.items[0], Sym) and b.items[0].name == name:
                    shadowed = True
            else:
                new_bindings.append(b)
        body = sx.items[2] if shadowed else _subst(sx.items[2], name, value)
        return SList((sx.items[0], SList(tuple(new_bindings), sx.items[1].pos), body), sx.pos)
    if head == "match":
        items = [sx.items[0], _subst(sx.items[1], name, value)]
        for clause in sx.items[2:]:
            if isinstance(clause, SList) and len(clause.items) == 2:
                pat = clause.items[0]
                binds = [x.name for x in pat.items[1:]] if isinstance(pat, SList) else []
                body = clause.items[1] if name in binds else _subst(clause.items[1], name, value)
                items.append(SList((pat, body), clause.pos))
            else:
                items.append(clause)
        return SList(tuple(items), sx.pos)
    return SList(tuple(_subst(x, name, value) for x in sx.items), sx.pos)


def expand(sx):
    """Expande `first` y `reduce` (de arriba abajo) hasta que no quede ninguna."""
    if not isinstance(sx, SList) or not sx.items:
        return sx
    head = sx.head()
    if head == "first":
        # (first i LO HI cond then else): el primer i en [LO, HI) que cumple cond.
        if len(sx.items) != 7 or not isinstance(sx.items[1], Sym):
            raise EFCHError("forma: (first i LO HI cond entonces si-no)", sx)
        _, var, lo, hi, cond, then, other = sx.items
        lo, hi = _const_eval(lo), _const_eval(hi)
        result = other
        for i in range(hi - 1, lo - 1, -1):
            result = SList((Sym("ite", sx.pos), _subst(cond, var.name, i), _subst(then, var.name, i), result),
                           sx.pos)
        return expand(result)
    if head == "fold" and len(sx.items) == 7:
        # (fold i LO HI (acc INIT) PASO (invariant INV)) (EXP-013): el invariante es una anotación que
        # se demuestra (smt.check_fold_invariants); no cambia la semántica.
        inv = sx.items[6]
        if not (isinstance(inv, SList) and len(inv.items) == 2 and inv.head() == "invariant"):
            raise EFCHError("forma: (fold i LO HI (acc INIT) PASO (invariant INV))", sx)
        folded = expand(SList(sx.items[:6], sx.pos))
        return SList((Sym("finv%", sx.pos), sx.items[4].items[0], folded, expand(inv.items[1])), sx.pos)
    if head == "fold":
        # (fold i LO HI (acc INIT) STEP): acc := STEP[i := LO .. HI-1] desde INIT (núcleo 0.2, EXP-009).
        # Se conserva como forma interna (fold% acc INIT PASO...) con un paso por índice, para la
        # verificación modular (smt.py); su semántica es la cadena de let equivalente.
        if len(sx.items) != 6 or not isinstance(sx.items[1], Sym) or not isinstance(sx.items[4], SList) \
                or len(sx.items[4].items) != 2 or not isinstance(sx.items[4].items[0], Sym):
            raise EFCHError("forma: (fold i LO HI (acc INIT) PASO)", sx)
        _, var, lo, hi, (acc, init), step = sx.items[0], sx.items[1], sx.items[2], sx.items[3], \
            sx.items[4].items, sx.items[5]
        lo, hi = _const_eval(lo), _const_eval(hi)
        if hi <= lo:
            raise EFCHError("fold sobre un rango vacío", sx)
        if hi - lo > 256:
            raise EFCHError("fold admite como mucho 256 pasos", sx)
        steps = [expand(_subst(step, var.name, i)) if acc.name != var.name else expand(step) for i in range(lo, hi)]
        return SList((Sym("fold%", sx.pos), acc, expand(init), *steps), sx.pos)
    if head == "reduce":
        # (reduce OP i LO HI expr): OP sobre expr[i := LO .. HI-1].
        if len(sx.items) != 6 or not isinstance(sx.items[1], Sym) or not isinstance(sx.items[2], Sym):
            raise EFCHError("forma: (reduce OP i LO HI expr)", sx)
        _, op, var, lo, hi, body = sx.items
        if op.name not in REDUCE_OPS:
            raise EFCHError(f"reduce admite {', '.join(REDUCE_OPS)}", op)
        lo, hi = _const_eval(lo), _const_eval(hi)
        terms = [_subst(body, var.name, i) for i in range(lo, hi)]
        if not terms:
            if op.name in ("all", "any"):
                return Sym("true" if op.name == "all" else "false", sx.pos)
            raise EFCHError("reduce sobre un rango vacío", sx)
        if len(terms) == 1 and op.name not in ("all", "any"):
            return expand(terms[0])
        return expand(SList((Sym(op.name, op.pos), *terms), sx.pos))
    items = []
    for x in sx.items:
        if isinstance(x, SList) and x.head() == "each":
            # (each i LO HI expr) se sustituye por expr[i := LO], ..., expr[i := HI-1].
            if len(x.items) != 5 or not isinstance(x.items[1], Sym):
                raise EFCHError("forma: (each i LO HI expr)", x)
            _, var, lo, hi, body = x.items
            items += [expand(_subst(body, var.name, i)) for i in range(_const_eval(lo), _const_eval(hi))]
        else:
            items.append(expand(x))
    return SList(tuple(items), sx.pos)


# --- Elaboración -------------------------------------------------------------

@dataclass(frozen=True)
class Dependency:
    """Dependencia directa resuelta de un objeto elaborado: el `call` a `name` se resolvió a la computación de
    identidad `identity` (su contenido canónico). Es el contexto de resolución del objeto (diseño de identidad,
    §3): si más tarde se elabora el mismo texto frente a otra definición, la identidad registrada lo delata."""
    name: str
    identity: str


class Collector:
    """Dependencias directas de UN objeto (computación, propiedad o candidata), en orden de resolución. Incluye las
    llamadas que aparecen en los argumentos de otra llamada; no las de los cuerpos ya elaborados de las llamadas
    (esas son dependencias de la computación llamada)."""

    def __init__(self):
        self._deps = {}

    def record(self, comp, identity):
        self._deps.setdefault(comp.name, Dependency(comp.name, identity))

    def dependencies(self):
        return tuple(self._deps.values())


def call_marker(name):
    """Variable libre que ocupa el lugar de `(call name ...)` en la forma fuente (sin expandir). Contiene espacios y
    paréntesis, así que ningún símbolo del lenguaje puede llamarse igual."""
    return f"(ranura computacion {name})"


class Elaborator:
    def __init__(self, computations, expand_calls=True):
        self.computations = computations  # nombre -> Computation (ya elaboradas)
        self.fresh = 0
        # Con expand_calls=False, `(call f a...)` se elabora como Node("call", (marcador de f, a...)) en vez de
        # sustituirse por el cuerpo de f: es la forma fuente del diseño de identidad (§2.2). No cambia la forma
        # canónica ni la identidad de nada: solo se usa para calcular la forma fuente.
        self.expand_calls = expand_calls
        self.collector = None
        self._identities = {}

    def collect(self):
        """Abre un colector nuevo para el próximo objeto que se elabore (uno por objeto)."""
        self.collector = Collector()
        return self.collector

    def _identity(self, comp):
        key = id(comp)
        if key not in self._identities:
            self._identities[key] = (comp, comp.identity())
        return self._identities[key][1]

    def _fresh(self, base, avoid=()):
        self.fresh += 1
        while f"{base}%{self.fresh}" in avoid:
            self.fresh += 1
        return f"{base}%{self.fresh}"

    def check(self, sx, expected, env):
        if isinstance(sx, Num):
            if not isinstance(sx.value, int):
                raise EFCHError("los decimales solo se admiten en (budget ...)", sx)
            if not is_bv(expected):
                raise EFCHError(f"un literal entero no puede tener tipo {type_str(expected)}", sx)
            if not 0 <= sx.value <= mask(expected[1]):
                raise EFCHError(f"{sx.value} no cabe en {type_str(expected)}", sx)
            return Node("const", (), expected, sx.value)
        node = self.infer(sx, env, expected)
        return self.coerce(node, expected, sx)

    def coerce(self, node, expected, sx):
        if node.ty == expected:
            return node
        if node.ty[0] == expected[0] == "bytes" and node.ty[1] <= expected[1]:
            return Node("widen", (node,), expected, expected[1])
        raise EFCHError(f"se esperaba {type_str(expected)}, no {type_str(node.ty)}", sx)

    def _infer_same(self, items, env, expected=None):
        """Elabora operandos que deben compartir tipo; los literales lo toman del resto."""
        nodes = [None] * len(items)
        known = None
        for k, it in enumerate(items):
            if not _context_typed(it):
                nodes[k] = self.infer(it, env)
                known = nodes[k].ty
                break
        if known is None:
            known = expected
        if known is None:
            raise EFCHError("no se puede deducir el ancho: usa (bv N valor)", items[0])
        for k, it in enumerate(items):
            nodes[k] = self.coerce(nodes[k], known, it) if nodes[k] is not None else self.check(it, known, env)
        return nodes, known

    def infer(self, sx, env, expected=None):
        if isinstance(sx, Num):
            if expected and is_bv(expected):
                return self.check(sx, expected, env)
            raise EFCHError("no se puede deducir el ancho del literal: usa (bv N valor)", sx)
        if isinstance(sx, Str):
            raise EFCHError("las cadenas solo se admiten en (doc ...)", sx)
        if isinstance(sx, Sym):
            if sx.name in ("true", "false"):
                return Node("bool", (), BOOL, sx.name == "true")
            if sx.name == "none":
                if not expected or expected[0] != "option":
                    raise EFCHError("none necesita un tipo option esperado", sx)
                return Node("none", (), expected)
            if sx.name not in env:
                raise EFCHError(f"nombre no ligado: {sx.name}", sx)
            return Node("var", (), env[sx.name], sx.name)
        if not isinstance(sx, SList) or not sx.items or not isinstance(sx.items[0], Sym):
            raise EFCHError(f"expresión no reconocida: {dumps(sx)}", sx)

        head, args = sx.head(), sx.items[1:]
        arity = len(args)

        def need(n):
            if arity != n:
                raise EFCHError(f"{head} espera {n} argumentos, recibe {arity}", sx)

        if head == "bv":
            need(2)
            w, v = args
            if not isinstance(w, Num) or not isinstance(v, Num):
                raise EFCHError("forma: (bv N valor)", sx)
            return self.check(v, BV(w.value), env)

        if head in ARITH:
            if arity < 2 or (arity > 2 and head not in ASSOC):
                raise EFCHError(f"{head} espera 2 argumentos" + (" o más" if head in ASSOC else ""), sx)
            exp = expected if expected and is_bv(expected) else None
            nodes, t = self._infer_same(args, env, exp)
            if not is_bv(t):
                raise EFCHError(f"{head} opera sobre vectores de bits, no {type_str(t)}", sx)
            node = nodes[0]
            for other in nodes[1:]:
                node = Node(head, (node, other), t)
            return node

        if head == "neg":
            need(1)
            a = self.infer(args[0], env, expected if expected and is_bv(expected) else None)
            if not is_bv(a.ty):
                raise EFCHError("neg opera sobre vectores de bits", sx)
            return Node("neg", (a,), a.ty)

        if head == "not":
            need(1)
            a = self.infer(args[0], env, expected)
            if a.ty == BOOL:
                return Node("lnot", (a,), BOOL)
            if is_bv(a.ty):
                return Node("bnot", (a,), a.ty)
            raise EFCHError("not opera sobre bool o vectores de bits", sx)

        if head in CMP:
            need(2)
            if all(isinstance(x, Num) for x in args) and head not in SIGNED_CMP:
                # Comparación entre constantes (habitual tras expandir first/reduce). Las comparaciones
                # con signo necesitan el ancho, que dos literales sueltos no tienen.
                x, y = args[0].value, args[1].value
                return Node("bool", (), BOOL, {"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y,
                                               "ugt": x > y, "uge": x >= y}[head])
            nodes, t = self._infer_same(args, env)
            if head in ("eq", "ne") and not is_scalar(t):
                raise EFCHError("eq/ne comparan escalares", sx)
            if head not in ("eq", "ne") and not is_bv(t):
                raise EFCHError(f"{head} compara vectores de bits", sx)
            return Node(head, tuple(nodes), BOOL)

        if head in ("all", "any"):
            nodes = tuple(self.check(a, BOOL, env) for a in args)
            if not nodes:
                return Node("bool", (), BOOL, head == "all")
            return nodes[0] if len(nodes) == 1 else Node(head, nodes, BOOL)

        if head == "ite":
            need(3)
            c = self.check(args[0], BOOL, env)
            if expected is not None:
                a, b = self.check(args[1], expected, env), self.check(args[2], expected, env)
                return Node("ite", (c, a, b), expected)
            if _context_typed(args[1]) and _context_typed(args[2]):
                raise EFCHError("no se puede deducir el ancho de ite: usa (bv N valor)", sx)
            branches = [None, None]
            k0 = 0 if not _context_typed(args[1]) else 1
            branches[k0] = self.infer(args[1 + k0], env)
            t = branches[k0].ty
            other = args[2 - k0]
            branches[1 - k0] = self.check(other, t, env) if _context_typed(other) else self.infer(other, env)
            if t[0] == "bytes" and branches[1 - k0].ty[0] == "bytes":
                t = BYTES(max(t[1], branches[1 - k0].ty[1]))
            a, b = (self.coerce(n, t, s) for n, s in zip(branches, args[1:]))
            return Node("ite", (c, a, b), t)

        if head == "let":
            need(2)
            if not isinstance(args[0], SList):
                raise EFCHError("forma: (let ((nombre expr) ...) cuerpo)", sx)
            binds = []
            inner = dict(env)
            for b in args[0].items:
                if not (isinstance(b, SList) and len(b.items) == 2 and isinstance(b.items[0], Sym)):
                    raise EFCHError("ligadura: (nombre expr)", b)
                val = self.infer(b.items[1], inner)
                binds.append((b.items[0].name, val))
                inner[b.items[0].name] = val.ty
            body = self.infer(args[1], inner, expected) if expected is None else self.check(args[1], expected, inner)
            for name, val in reversed(binds):
                body = Node("let", (val, body), body.ty, name)
            return body

        if head in ("zext", "sext", "trunc"):
            need(2)
            if not isinstance(args[0], Num):
                raise EFCHError(f"forma: ({head} N expr)", sx)
            w = args[0].value
            a = self.infer(args[1], env)
            if not is_bv(a.ty):
                raise EFCHError(f"{head} opera sobre vectores de bits", sx)
            if (head in ("zext", "sext") and w < a.ty[1]) or (head == "trunc" and w > a.ty[1]) or not 1 <= w <= MAX_BV:
                raise EFCHError(f"{head} de {type_str(a.ty)} a (bv {w}) no es válido", sx)
            return a if w == a.ty[1] else Node(head, (a,), BV(w), w)

        if head == "len":
            need(1)
            b = self.infer(args[0], env)
            if b.ty[0] != "bytes":
                raise EFCHError("len opera sobre bytes", sx)
            return Node("len", (b,), LEN_T)

        if head == "byte":
            need(2)
            b = self.infer(args[0], env)
            if b.ty[0] != "bytes":
                raise EFCHError("byte opera sobre bytes", sx)
            return Node("byte", (b, self.check(args[1], LEN_T, env)), BYTE_T)

        if head == "mkbytes":
            if arity < 1:
                raise EFCHError("forma: (mkbytes LONGITUD b0 b1 ...)", sx)
            m = expected[1] if expected and expected[0] == "bytes" else arity - 1
            if arity - 1 > m:
                raise EFCHError(f"mkbytes con {arity - 1} elementos no cabe en (bytes {m})", sx)
            n = self.check(args[0], LEN_T, env)
            elems = tuple(self.check(e, BYTE_T, env) for e in args[1:])
            return Node("mkbytes", (n,) + elems, BYTES(m), m)

        if head == "some":
            if expected and expected[0] == "option":
                if len(expected[1]) != arity:
                    raise EFCHError(f"some con {arity} campos para {type_str(expected)}", sx)
                return Node("some", tuple(self.check(a, t, env) for a, t in zip(args, expected[1])), expected)
            fields = tuple(self.infer(a, env) for a in args)
            if not all(is_scalar(f.ty) for f in fields):
                raise EFCHError("los campos de some deben ser escalares", sx)
            return Node("some", fields, OPTION(*(f.ty for f in fields)))

        if head == "match":
            if arity != 3:
                raise EFCHError("forma: (match e ((some x ...) cuerpo) (none cuerpo))", sx)
            scrut = self.infer(args[0], env)
            if scrut.ty[0] != "option":
                raise EFCHError("match opera sobre option", sx)
            some_clause = none_clause = None
            for clause in args[1:]:
                if not (isinstance(clause, SList) and len(clause.items) == 2):
                    raise EFCHError("cláusula: (patrón cuerpo)", clause)
                pat = clause.items[0]
                if isinstance(pat, Sym) and pat.name == "none":
                    none_clause = clause.items[1]
                elif isinstance(pat, SList) and pat.head() == "some":
                    names = [x.name for x in pat.items[1:] if isinstance(x, Sym)]
                    if len(names) != len(scrut.ty[1]):
                        raise EFCHError("el patrón some no coincide con los campos", pat)
                    some_clause = (names, clause.items[1])
            if some_clause is None or none_clause is None:
                raise EFCHError("match necesita una cláusula some y otra none", sx)
            names, body = some_clause
            inner = dict(env)
            inner.update(zip(names, scrut.ty[1]))
            if expected is None:
                some_body = self.infer(body, inner)
                expected = some_body.ty
            else:
                some_body = self.check(body, expected, inner)
            none_body = self.check(none_clause, expected, env)
            return Node("match", (scrut, some_body, none_body), expected, tuple(names))

        if head == "fold%":
            # Forma interna producida por expand (ver arriba): acc INIT PASO...
            acc, init_sx, steps = args[0], args[1], args[2:]
            init = self.infer(init_sx, env, expected if expected and is_scalar(expected) else None)
            if not is_scalar(init.ty) or init.ty[0] == "option":
                raise EFCHError(f"el acumulador de fold debe ser escalar (bv o bool), no {type_str(init.ty)}", sx)
            inner = {**env, acc.name: init.ty}
            nodes = [self.check(st, init.ty, inner) for st in steps]
            return Node("fold", (init, *nodes), init.ty, acc.name)

        if head == "finv%":
            # Forma interna: acc, el pliegue expandido y el invariante (que ve acc).
            fold = self.infer(args[1], env, expected)
            inv = self.check(args[2], BOOL, {**env, args[0].name: fold.ty})
            return Node("finv", (fold, inv), fold.ty, args[0].name)

        if head == "call":
            if arity < 1 or not isinstance(args[0], Sym):
                raise EFCHError("forma: (call computación argumentos...)", sx)
            comp = self.computations.get(args[0].name)
            if comp is None:
                raise EFCHError(f"computación desconocida o definida después: {args[0].name}", sx)
            if arity - 1 != len(comp.inputs):
                raise EFCHError(f"{comp.name} espera {len(comp.inputs)} argumentos", sx)
            vals = [self.check(a, t, env) for a, (_, t) in zip(args[1:], comp.inputs)]
            if self.collector is not None:
                self.collector.record(comp, self._identity(comp))
            if not self.expand_calls:
                return Node("call", (Node("var", (), comp.output, call_marker(comp.name)), *vals), comp.output)
            # Los nombres nuevos no pueden capturar un `let` del cuerpo llamado igual ni una variable de los
            # argumentos, que quedan dentro de los `let` de las entradas anteriores (auditoría de Codex Astra).
            avoid = set(_all_names(comp.semantics)).union(*(_all_names(v) for v in vals))
            fresh = {name: self._fresh(name, avoid) for name, _ in comp.inputs}
            body = rename_free(comp.semantics, fresh)
            for (name, _), val in reversed(list(zip(comp.inputs, vals))):
                body = Node("let", (val, body), body.ty, fresh[name])
            return body

        raise EFCHError(f"operación desconocida: {head}", sx)


def _all_names(node, out=None):
    """Todos los nombres de variables y ligaduras que aparecen en `node`."""
    out = set() if out is None else out
    if node.op in ("var", "let", "fold", "finv"):
        out.add(node.attr)
    elif node.op == "match":
        out.update(node.attr)
    for a in node.args:
        _all_names(a, out)
    return out


def _context_typed(sx):
    """Expresión cuyo ancho solo puede venir del contexto: literales y operaciones sobre ellos."""
    if isinstance(sx, Num):
        return True
    if isinstance(sx, SList) and sx.head() in ARITH + ("neg", "not"):
        return all(_context_typed(x) for x in sx.items[1:])
    if isinstance(sx, SList) and sx.head() == "ite" and len(sx.items) == 4:
        return _context_typed(sx.items[2]) and _context_typed(sx.items[3])
    return False


def rename_free(node, mapping):
    if node.op == "var":
        return Node("var", (), node.ty, mapping.get(node.attr, node.attr))
    if node.op == "let":
        val = rename_free(node.args[0], mapping)
        inner = {k: v for k, v in mapping.items() if k != node.attr}
        return Node("let", (val, rename_free(node.args[1], inner)), node.ty, node.attr)
    if node.op == "finv":
        inner = {k: v for k, v in mapping.items() if k != node.attr}
        return Node("finv", (rename_free(node.args[0], mapping), rename_free(node.args[1], inner)), node.ty, node.attr)
    if node.op == "fold":
        inner = {k: v for k, v in mapping.items() if k != node.attr}
        return Node("fold", (rename_free(node.args[0], mapping), *(rename_free(st, inner) for st in node.args[1:])),
                    node.ty, node.attr)
    if node.op == "match":
        inner = {k: v for k, v in mapping.items() if k not in node.attr}
        scrut, some_body, none_body = node.args
        return Node("match", (rename_free(scrut, mapping), rename_free(some_body, inner),
                              rename_free(none_body, mapping)), node.ty, node.attr)
    if not node.args:
        return node
    return Node(node.op, tuple(rename_free(a, mapping) for a in node.args), node.ty, node.attr)


# --- Forma canónica e identidad ------------------------------------------------

def canonical(node, inputs=()):
    """Texto canónico: nombres locales numerados por orden de ligadura."""
    counter = [0]

    def go(n, names):
        if n.op == "const":
            return f"(const {n.ty[1]} {n.attr})"
        if n.op == "bool":
            return "true" if n.attr else "false"
        if n.op == "none":
            return f"(none {type_str(n.ty)})"
        if n.op == "var":
            return names.get(n.attr, _free_name(n.attr))
        if n.op == "let":
            val = go(n.args[0], names)
            local = f"_{counter[0]}"
            counter[0] += 1
            return f"(let {local} {val} {go(n.args[1], {**names, n.attr: local})})"
        if n.op == "finv":
            fold = go(n.args[0], names)
            local = f"_{counter[0]}"
            counter[0] += 1
            return f"(finv {local} {fold} {go(n.args[1], {**names, n.attr: local})})"
        if n.op == "fold":
            init = go(n.args[0], names)
            local = f"_{counter[0]}"
            counter[0] += 1
            inner = {**names, n.attr: local}
            return f"(fold {local} {init} " + " ".join(go(st, inner) for st in n.args[1:]) + ")"
        if n.op == "match":
            scrut = go(n.args[0], names)
            locals_ = []
            inner = dict(names)
            for name in n.attr:
                locals_.append(f"_{counter[0]}")
                inner[name] = locals_[-1]
                counter[0] += 1
            return f"(match {scrut} ({' '.join(locals_)}) {go(n.args[1], inner)} {go(n.args[2], names)})"
        extra = ""
        if n.op in ("zext", "sext", "trunc", "widen", "mkbytes"):
            extra = f" {n.attr}"
        elif n.op == "some":
            extra = f" {type_str(n.ty)}"
        return f"({n.op}{extra} " + " ".join(go(a, names) for a in n.args) + ")" if n.args \
            else f"({n.op}{extra})"

    return go(node, {name: _free_name(name) for name, _ in inputs})


def _free_name(name):
    """Una variable libre o de entrada llamada como un local canónico (`_0`, `_1`…) se marca para que no se
    confunda con él (auditoría de Codex Astra, 23/10/2026). Las demás se imprimen igual: las identidades de
    las definiciones existentes no cambian."""
    return f"(free {name})" if re.fullmatch(r"_[0-9]+", name) else name


def node_count(node):
    return 1 + sum(node_count(a) for a in node.args)


# --- Definiciones --------------------------------------------------------------

@dataclass
class Computation:
    name: str
    inputs: list          # [(nombre, tipo)]
    output: tuple
    semantics: Node
    doc: str = ""
    workload: object = None
    objectives: tuple = ()
    budget: dict = None
    source: object = None
    dependencies: tuple = ()      # (Dependency, ...) directas, del colector del elaborador
    source_form: Node = None      # semántica con las llamadas sin expandir (forma fuente, diseño de identidad §2.2)

    def signature(self):
        ins = " ".join(f"({n} {type_str(t)})" for n, t in self.inputs)
        return f"(computation {self.name} ({ins}) {type_str(self.output)})"

    def canonical(self):
        return f"(efch {LANGUAGE_VERSION} {self.signature()} {canonical(self.semantics, self.inputs)})"

    def identity(self):
        return hashlib.sha256(self.canonical().encode()).hexdigest()


@dataclass
class Property:
    name: str
    variables: list
    body: Node
    source: object = None
    dependencies: tuple = ()
    source_form: Node = None


@dataclass
class Candidate:
    name: str
    implements: str
    body: Node
    origin: str = ""
    source_text: str = ""
    dependencies: tuple = ()
    source_form: Node = None

    def canonical(self, comp):
        return f"(efch {LANGUAGE_VERSION} {comp.signature()} {canonical(self.body, comp.inputs)})"

    def identity(self, comp):
        return hashlib.sha256(self.canonical(comp).encode()).hexdigest()


@dataclass
class Definition:
    computations: dict
    properties: list
    baseline_c: str = None
    path: str = None


DEFAULT_BUDGET = {"llm-calls": 8, "llm-usd": 3.0, "llm-seconds": 1800, "smt-seconds": 120}


def _section(items, name):
    return [x for x in items if isinstance(x, SList) and x.head() == name]


def _one(items, name, parent, required=True):
    found = _section(items, name)
    if len(found) > 1:
        raise EFCHError(f"({name} ...) aparece más de una vez", parent)
    if required and not found:
        raise EFCHError(f"falta ({name} ...)", parent)
    return found[0] if found else None


def _check_header(top):
    if len(top) != 1 or not isinstance(top[0], SList) or top[0].head() != "efch":
        raise EFCHError("el archivo debe contener una única forma (efch 0.1 ...)")
    root = top[0]
    if len(root.items) < 2 or not isinstance(root.items[1], Num) and not isinstance(root.items[1], Sym):
        raise EFCHError("falta la versión del lenguaje", root)
    version = dumps(root.items[1])
    if version != LANGUAGE_VERSION:
        raise EFCHError(f"versión {version} no soportada; se admite {LANGUAGE_VERSION}", root)
    return root.items[2:]


def _parse_computation(sx, elab):
    items = sx.items
    if len(items) < 2 or not isinstance(items[1], Sym):
        raise EFCHError("forma: (computation nombre ...)", sx)
    name = items[1].name
    if name in elab.computations:
        raise EFCHError(f"computación duplicada: {name}", sx)
    body = items[2:]
    inputs = []
    for inp in _section(body, "input"):
        if len(inp.items) != 3 or not isinstance(inp.items[1], Sym):
            raise EFCHError("forma: (input nombre tipo)", inp)
        t = parse_type(inp.items[2])
        if t[0] == "option":
            raise EFCHError("las entradas no pueden ser option", inp)
        inputs.append((inp.items[1].name, t))
    if len({n for n, _ in inputs}) != len(inputs):
        raise EFCHError("entradas con nombres repetidos", sx)
    out = _one(body, "output", sx)
    output = parse_type(out.items[1])
    sem = _one(body, "semantics", sx)
    if len(sem.items) != 2:
        raise EFCHError("forma: (semantics expr)", sem)
    semantics, deps, source_form = _elaborate_object(elab, expand(sem.items[1]), output, dict(inputs))
    doc = _one(body, "doc", sx, required=False)
    budget = dict(DEFAULT_BUDGET)
    bsec = _one(body, "budget", sx, required=False)
    if bsec:
        for entry in bsec.items[1:]:
            if not (isinstance(entry, SList) and len(entry.items) == 2 and entry.head() in DEFAULT_BUDGET
                    and isinstance(entry.items[1], Num)):
                raise EFCHError(f"entrada de presupuesto no reconocida; claves: {', '.join(DEFAULT_BUDGET)}", entry)
            budget[entry.head()] = entry.items[1].value
    objectives = tuple(dumps(o) for o in _section(body, "objective"))
    known = {"input", "output", "semantics", "doc", "workload", "objective", "budget"}
    for x in body:
        if not isinstance(x, SList) or x.head() not in known:
            raise EFCHError(f"sección desconocida en computation: {dumps(x)[:40]}", x)
    return Computation(name, inputs, output, semantics,
                       doc=doc.items[1].value if doc and isinstance(doc.items[1], Str) else "",
                       workload=_one(body, "workload", sx, required=False),
                       objectives=objectives, budget=budget, source=sx, dependencies=deps,
                       source_form=source_form)


def _parse_property(sx, elab):
    if len(sx.items) != 3 or not isinstance(sx.items[1], Sym):
        raise EFCHError("forma: (property nombre (forall ((x tipo) ...) expr))", sx)
    fa = sx.items[2]
    if not (isinstance(fa, SList) and fa.head() == "forall" and len(fa.items) == 3 and isinstance(fa.items[1], SList)):
        raise EFCHError("forma: (forall ((x tipo) ...) expr)", fa)
    variables = []
    for v in fa.items[1].items:
        if not (isinstance(v, SList) and len(v.items) == 2 and isinstance(v.items[0], Sym)):
            raise EFCHError("variable: (nombre tipo)", v)
        variables.append((v.items[0].name, parse_type(v.items[1])))
    if len({n for n, _ in variables}) != len(variables):
        # Con nombres repetidos, el cuerpo ve solo una de las dos variables; Z3 y el intérprete no coinciden
        # en cuál (auditoría de Codex Astra, 23/10/2026).
        raise EFCHError("variables cuantificadas con nombres repetidos", fa)
    body, deps, source_form = _elaborate_object(elab, expand(fa.items[2]), BOOL, dict(variables))
    return Property(sx.items[1].name, variables, body, source=sx, dependencies=deps, source_form=source_form)


def _elaborate_object(elab, sx, expected, env):
    """Elabora un objeto con su propio colector: (árbol con las llamadas expandidas, dependencias directas
    resueltas, forma fuente). La forma fuente se elabora aparte, sin expandir, frente a las mismas computaciones."""
    collector = elab.collect()
    try:
        node = elab.check(sx, expected, env)
    finally:
        elab.collector = None
    source_form = Elaborator(elab.computations, expand_calls=False).check(sx, expected, env)
    return node, collector.dependencies(), source_form


def parse_computation(sx, computations):
    """Elabora una forma `(computation ...)` frente a `computations` (nombre -> Computation). La usa el registro
    semántico para obtener la revisión de una ranura en otra instantánea (store, D8)."""
    return _parse_computation(sx, Elaborator(dict(computations)))


def parse_property(sx, computations):
    """Elabora una forma `(property ...)` frente a `computations`."""
    return _parse_property(sx, Elaborator(dict(computations)))


def load_definition(text, path=None):
    try:
        top = parse(text)
    except SyntaxError_ as e:
        raise EFCHError(str(e)) from None
    elab = Elaborator({})
    comps, props, baseline = {}, [], None
    for sx in _check_header(top):
        head = sx.head() if isinstance(sx, SList) else None
        if head == "computation":
            comp = _parse_computation(sx, elab)
            comps[comp.name] = comp
            elab.computations[comp.name] = comp
        elif head == "property":
            props.append(_parse_property(sx, elab))
        elif head == "baseline-c":
            if len(sx.items) != 2 or not isinstance(sx.items[1], Str):
                raise EFCHError('forma: (baseline-c "archivo.c")', sx)
            baseline = sx.items[1].value
        else:
            raise EFCHError(f"forma de nivel superior desconocida: {dumps(sx)[:40]}", sx)
    return Definition(comps, props, baseline, path)


def load_candidates(text, definition, origin=""):
    """Lee (efch 0.1 (candidate nombre (implements comp) (body expr)) ...)."""
    try:
        top = parse(text)
    except SyntaxError_ as e:
        raise EFCHError(str(e)) from None
    elab = Elaborator(definition.computations)
    out = []
    for sx in _check_header(top):
        if not (isinstance(sx, SList) and sx.head() == "candidate" and len(sx.items) == 4
                and isinstance(sx.items[1], Sym)):
            raise EFCHError("forma: (candidate nombre (implements computación) (body expr))", sx)
        impl, body = sx.items[2], sx.items[3]
        if not (isinstance(impl, SList) and impl.head() == "implements" and len(impl.items) == 2):
            raise EFCHError("forma: (implements computación)", impl)
        comp = definition.computations.get(dumps(impl.items[1]))
        if comp is None:
            raise EFCHError(f"computación desconocida: {dumps(impl.items[1])}", impl)
        if not (isinstance(body, SList) and body.head() == "body" and len(body.items) == 2):
            raise EFCHError("forma: (body expr)", body)
        node, deps, source_form = _elaborate_object(elab, expand(body.items[1]), comp.output, dict(comp.inputs))
        out.append(Candidate(sx.items[1].name, comp.name, node, origin, dumps(sx), dependencies=deps,
                             source_form=source_form))
    return out
