"""
EFCH Lang 0.1: interfaz de programación sobre el núcleo semántico (manifiesto v0.5, §22).

Un programa EFCH Lang es una lista de funciones con sintaxis de la familia de Rust y Go:
variables mutables, `if`, `for` acotado y `return` temprano. No tiene semántica propia: se
traduce a una expresión del núcleo EFCH 0.1 (`docs/lenguaje-efch-lang-0.1.md`), que es la
única definición del significado. De ahí salen las dos rutas de §22.3:

- ordinaria: núcleo → buena definición → C (`efch lang build`);
- investigación: núcleo → equivalencia con una especificación (`efch lang verify`).

La traducción es una ejecución simbólica en estilo de continuaciones: los bucles se
desenrollan (su cota se deduce sin SMT) y cada asignación es una ligadura nueva.
"""

import re
from dataclasses import dataclass, field

from . import core
from .core import BOOL, BV, BYTES, OPTION, EFCHError
from .sexpr import Num, SList, Sym, dumps

MAX_ITERATIONS = 64

# --- Léxico --------------------------------------------------------------------

KEYWORDS = {"fn", "let", "var", "if", "else", "for", "in", "return", "true", "false", "none", "some", "fold", "from", "with", "invariant",
            "as", "implements", "bool", "bytes", "option"}
OPERATORS = ["..=", "<<=", ">>=", "..", "->", "==", "!=", "<=", ">=", "<<", ">>", "&&", "||", "+=", "-=",
             "*=", "|=", "&=", "^=", "%=", "/=", "+", "-", "*", "/", "%", "&", "|", "^", "~", "!", "<",
             ">", "=", "(", ")", "{", "}", "[", "]", ",", ":", ";", "."]
_TOKEN = re.compile(r"\s+|//[^\n]*|(?P<int>0[xX][0-9a-fA-F_]+|0[bB][01_]+|[0-9][0-9_]*)"
                    r"|(?P<name>[A-Za-z_][A-Za-z0-9_]*)|(?P<op>" +
                    "|".join(re.escape(o) for o in OPERATORS) + ")")


@dataclass
class Tok:
    kind: str     # int, name, kw, op, eof
    text: str
    pos: tuple
    value: int = None


def _pos(text, i):
    line = text.count("\n", 0, i) + 1
    return line, i - (text.rfind("\n", 0, i) + 1) + 1


def tokenize(text):
    toks, i = [], 0
    while i < len(text):
        m = _TOKEN.match(text, i)
        if not m:
            raise LangError(f"carácter inesperado {text[i]!r}", _pos(text, i))
        if m.lastgroup == "int":
            toks.append(Tok("int", m.group(), _pos(text, i), int(m.group().replace("_", ""), 0)))
        elif m.lastgroup == "name":
            toks.append(Tok("kw" if m.group() in KEYWORDS else "name", m.group(), _pos(text, i)))
        elif m.lastgroup == "op":
            toks.append(Tok("op", m.group(), _pos(text, i)))
        i = m.end()
    toks.append(Tok("eof", "", _pos(text, len(text))))
    return toks


class LangError(EFCHError):
    def __init__(self, msg, pos=None):
        Exception.__init__(self, f"{pos[0]}:{pos[1]}: {msg}" if pos else msg)
        self.pos = pos


# --- Sintaxis ------------------------------------------------------------------
# Expresiones: tuplas (clase, posición, ...). Instrucciones: igual.

@dataclass
class Function:
    name: str
    params: list
    ret: tuple
    implements: str
    body: list
    pos: tuple


BINARY = [("||",), ("&&",), ("==", "!=", "<", "<=", ">", ">="), ("|",), ("^",), ("&",), ("<<", ">>"),
          ("+", "-"), ("*", "/", "%")]
ASSIGN_OPS = {"=", "+=", "-=", "*=", "|=", "&=", "^=", "%=", "/=", "<<=", ">>="}


class Parser:
    def __init__(self, text):
        self.toks = tokenize(text)
        self.i = 0

    def peek(self, k=0):
        return self.toks[self.i + k]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def at(self, text):
        t = self.peek()
        return t.kind in ("op", "kw") and t.text == text

    def accept(self, text):
        if self.at(text):
            return self.next()
        return None

    def expect(self, text):
        t = self.next()
        if t.kind not in ("op", "kw") or t.text != text:
            raise LangError(f"se esperaba «{text}», se encontró «{t.text or 'fin'}»", t.pos)
        return t

    def name(self):
        t = self.next()
        if t.kind != "name":
            raise LangError(f"se esperaba un nombre, se encontró «{t.text or 'fin'}»", t.pos)
        return t

    def program(self):
        fns = []
        while self.peek().kind != "eof":
            fns.append(self.function())
        return fns

    def function(self):
        start = self.expect("fn").pos
        name = self.name().text
        self.expect("(")
        params = []
        while not self.at(")"):
            p = self.name()
            self.expect(":")
            params.append((p.text, self.type(), p.pos))
            if not self.accept(","):
                break
        self.expect(")")
        self.expect("->")
        ret = self.type()
        impl = self.name().text if self.accept("implements") else None
        if impl is not None:
            while self.at("-"):           # los nombres del núcleo admiten guiones: varint-decode
                self.next()
                impl += "-" + self.name().text
        return Function(name, params, ret, impl, self.block(tail_return=True), start)

    def type(self):
        t = self.next()
        if t.kind == "name" and re.fullmatch(r"u[0-9]+", t.text):
            w = int(t.text[1:])
            if not 1 <= w <= 64:
                raise LangError(f"ancho no admitido: {t.text} (u1 a u64)", t.pos)
            return BV(w)
        if t.text == "bool":
            return BOOL
        if t.text == "bytes":
            self.expect("[")
            m = self.next()
            if m.kind != "int":
                raise LangError("forma: bytes[N]", m.pos)
            self.expect("]")
            return BYTES(m.value)
        if t.text == "option":
            self.expect("(")
            fields = [self.type()]
            while self.accept(","):
                fields.append(self.type())
            self.expect(")")
            return OPTION(*fields)
        raise LangError(f"tipo desconocido «{t.text}»", t.pos)

    def block(self, tail_return=False):
        self.expect("{")
        stmts = []
        while not self.at("}"):
            stmts.append(self.statement(tail_return))
            self.accept(";")
        self.expect("}")
        return stmts

    def statement(self, tail_return):
        t = self.peek()
        if self.accept("let") or self.accept("var"):
            n = self.name()
            ty = self.type() if self.accept(":") else None
            self.expect("=")
            return ("let", n.pos, n.text, ty, self.expr(), t.text == "var")
        if self.accept("if"):
            return self.if_rest(t.pos, tail_return)
        if self.accept("for"):
            v = self.name()
            self.expect("in")
            lo = self.expr()
            if self.accept("..="):
                inclusive = True
            else:
                self.expect("..")
                inclusive = False
            hi = self.expr()
            return ("for", v.pos, v.text, lo, hi, inclusive, self.block(tail_return))
        if self.accept("return"):
            return ("return", t.pos, self.expr())
        if t.kind == "name" and self.peek(1).kind == "op" and self.peek(1).text in ASSIGN_OPS:
            self.next()
            op = self.next().text
            return ("assign", t.pos, t.text, op, self.expr())
        e = self.expr()
        if tail_return and self.at("}"):
            return ("return", t.pos, e)                  # expresión final del cuerpo
        raise LangError("una expresión suelta solo puede ir al final del cuerpo de la función", t.pos)

    def if_rest(self, pos, tail_return):
        cond = self.expr()
        then = self.block(tail_return)
        other = None
        if self.accept("else"):
            other = [self.if_rest(self.toks[self.i - 1].pos, tail_return)] if self.accept("if") \
                else self.block(tail_return)
        return ("if", pos, cond, then, other)

    def expr(self, level=0):
        if level == len(BINARY):
            return self.unary()
        left = self.expr(level + 1)
        while self.peek().kind == "op" and self.peek().text in BINARY[level]:
            t = self.next()
            left = ("bin", t.pos, t.text, left, self.expr(level + 1))
        return left

    def unary(self):
        t = self.peek()
        if t.kind == "op" and t.text in ("!", "~", "-"):
            self.next()
            return ("un", t.pos, t.text, self.unary())
        return self.postfix(self.primary())

    def postfix(self, e):
        while True:
            t = self.peek()
            if self.accept("["):
                idx = self.expr()
                self.expect("]")
                e = ("index", t.pos, e, idx)
            elif self.accept("."):
                f = self.name()
                if f.text != "len":
                    raise LangError(f"campo desconocido «{f.text}» (solo .len)", f.pos)
                e = ("len", t.pos, e)
            elif self.accept("as"):
                e = ("cast", t.pos, e, self.type())
            else:
                return e

    def primary(self):
        t = self.next()
        if t.kind == "int":
            return ("int", t.pos, t.value)
        if t.text in ("true", "false"):
            return ("boolc", t.pos, t.text == "true")
        if t.text == "none":
            return ("none", t.pos)
        if t.text == "some":
            return ("some", t.pos, self.args())
        if t.text == "if":
            cond = self.expr()
            self.expect("{")
            a = self.expr()
            self.expect("}")
            self.expect("else")
            if self.at("if"):  # «else if» encadenado (EXP-005)
                b = self.primary()
            else:
                self.expect("{")
                b = self.expr()
                self.expect("}")
            return ("ite", t.pos, cond, a, b)
        if t.text == "fold":
            # fold k in A..B from INIT with s { EXPR }  (núcleo 0.2, EXP-009)
            k = self.name()
            self.expect("in")
            lo = self.expr()
            self.expect("..")
            hi = self.expr()
            self.expect("from")
            init = self.expr()
            self.expect("with")
            acc = self.name()
            inv = self.expr() if self.accept("invariant") else None
            self.expect("{")
            body = self.expr()
            self.expect("}")
            return ("fold", t.pos, k.text, lo, hi, init, acc.text, body, inv)
        if t.text == "(":
            e = self.expr()
            self.expect(")")
            return e
        if t.kind == "name":
            if self.at("("):
                args = self.args()
                if re.fullmatch(r"u[0-9]+", t.text):
                    if len(args) != 1:
                        raise LangError(f"{t.text}(x) recibe un argumento", t.pos)
                    return ("cast", t.pos, args[0], Parser(t.text + " ").type())
                return ("call", t.pos, t.text, args)
            return ("name", t.pos, t.text)
        raise LangError(f"expresión inesperada «{t.text or 'fin'}»", t.pos)

    def args(self):
        self.expect("(")
        out = []
        while not self.at(")"):
            out.append(self.expr())
            if not self.accept(","):
                break
        self.expect(")")
        return out


def parse_program(text):
    fns = Parser(text).program()
    seen = set()
    for f in fns:
        if f.name in seen:
            raise LangError(f"función duplicada: {f.name}", f.pos)
        seen.add(f.name)
    return fns


# --- Traducción al núcleo ------------------------------------------------------

def L(*items):
    return SList(tuple(items))


def S(name):
    return Sym(name)


def lit(v, w):
    return L(S("bv"), Num(w), Num(v))


def tmax(ty):
    return (1 << ty[1]) - 1 if ty and ty[0] == "bv" else None


@dataclass
class TE:
    """Expresión traducida: forma del núcleo, tipo y cota superior conocida (si es entero)."""
    sx: object
    ty: tuple                 # None: literal entero sin ancho todavía
    const: int = None
    mx: int = None

    @property
    def bound(self):
        if self.const is not None:
            return self.const
        return self.mx if self.mx is not None else tmax(self.ty)


@dataclass
class Var:
    sym: str
    ty: tuple
    mutable: bool = False
    mx: int = None
    const: int = None         # variable de bucle: literal
    sx: object = None         # forma fija del núcleo (índice de fold: (bv 16 k), que expand vuelve literal)


ARITH_OPS = {"+": "add", "-": "sub", "*": "mul", "/": "udiv", "%": "urem", "&": "and", "|": "or",
             "^": "xor", "<<": "shl", ">>": "lshr"}
CMP_OPS = {"==": "eq", "!=": "ne", "<": "ult", "<=": "ule", ">": "ugt", ">=": "uge"}
FOLD = {"+": lambda a, b: a + b, "-": lambda a, b: a - b, "*": lambda a, b: a * b,
        "/": lambda a, b: a // b if b else None, "%": lambda a, b: a % b if b else None,
        "&": lambda a, b: a & b, "|": lambda a, b: a | b, "^": lambda a, b: a ^ b,
        "<<": lambda a, b: a << b, ">>": lambda a, b: a >> b,
        "==": lambda a, b: a == b, "!=": lambda a, b: a != b, "<": lambda a, b: a < b,
        "<=": lambda a, b: a <= b, ">": lambda a, b: a > b, ">=": lambda a, b: a >= b}


def _returns(stmts):
    for s in stmts:
        if s[0] == "return":
            return True
        if s[0] == "if" and (_returns(s[3]) or _returns(s[4] or [])):
            return True
        if s[0] in ("for", "block", "dynloop") and _returns(s[-1]):
            return True
    return False


def _partial(sx):
    """¿Puede la forma quedar indefinida? (lectura fuera de rango, mkbytes demasiado largo, otra computación)"""
    if isinstance(sx, SList):
        it = sx.items
        if it and isinstance(it[0], Sym) and it[0].name in ("byte", "mkbytes", "call"):
            return True
        return any(_partial(x) for x in it)
    return False


def _neutral(ty):
    """Un valor cualquiera del tipo: ocupa el lugar de una expresión que la guarda no deja evaluar."""
    if ty[0] == "bv":
        return lit(0, ty[1])
    if ty[0] == "bool":
        return S("false")
    if ty[0] == "bytes":
        return L(S("mkbytes"), lit(0, 16))
    # Una ligadura no da tipo esperado a su ite, y none lo necesita (Codex Astra, EXP-017): some de neutros.
    return L(S("some"), *(_neutral(t) for t in ty[1]))


def _assigned(stmts, out):
    for s in stmts:
        if s[0] == "assign":
            out.add(s[2])
        elif s[0] == "if":
            _assigned(s[3], out)
            _assigned(s[4] or [], out)
        elif s[0] in ("for", "block", "dynloop"):
            _assigned(s[-1], out)
    return out


class Translator:
    def __init__(self, fns):
        self.fns = {f.name: f for f in fns}
        self.order = [f.name for f in fns]
        self.counter = 0
        self.stack = []           # funciones en traducción (para detectar recursión)
        self.loop_bounds = []     # (símbolo del núcleo, cota, tipo) de cada bucle con límite dinámico
        self.guard = None         # dentro de una rama predicada: forma booleana bajo la que se ejecuta

    def fresh(self, base):
        self.counter += 1
        return f"{base}.{self.counter}"

    # Punto de entrada: una función con sus parámetros libres.
    def function(self, fn, args=None, pos=None):
        if fn.name in self.stack:
            raise LangError(f"recursión no admitida en 0.1: {' → '.join(self.stack + [fn.name])}", pos or fn.pos)
        self.stack.append(fn.name)
        guard, self.guard = self.guard, None
        env, binds = {}, []
        for k, (pname, pty, ppos) in enumerate(fn.params):
            if args is None:
                env[pname] = Var(pname, pty)
            else:
                te = self.coerce(args[k], pty, pos)
                sym = self.fresh(pname)
                binds.append((sym, te.sx))
                env[pname] = Var(sym, pty, mx=te.mx)

        def fallthrough(_env):
            raise LangError(f"la función {fn.name} puede terminar sin return", fn.pos)

        body = self.seq(fn.body, env, fallthrough, fn)
        self.stack.pop()
        self.guard = guard
        for sym, sx in reversed(binds):
            body = L(S("let"), L(L(S(sym), sx)), body)
        return body

    # Instrucciones, en estilo de continuaciones: k(env) produce el resto de la función.
    def seq(self, stmts, env, k, fn):
        if not stmts:
            return k(env)
        s, rest_stmts = stmts[0], stmts[1:]

        def rest(e):
            return self.seq(rest_stmts, e, k, fn)

        kind, pos = s[0], s[1]
        if kind == "let":
            _, _, name, ty, e, mutable = s
            self.fresh_name_ok(name, env, pos)
            te = self.expr(e, env, ty)
            if ty is not None:
                te = self.coerce(te, ty, pos)
            elif te.ty is None:
                raise LangError(f"no se puede deducir el tipo de {name}: escribe {name}: uN", pos)
            sym = self.fresh(name)
            sx = te.sx
            if self.guard is not None and _partial(sx):
                sx = self.select(sx, _neutral(te.ty))
            if name.startswith("$hi"):
                self.loop_bounds.append((sym, te.bound, te.ty))
            inner = {**env, name: Var(sym, te.ty, mutable, None if mutable else te.mx,
                                      None)}
            return L(S("let"), L(L(S(sym), sx)), rest(inner))
        if kind == "bindconst":
            _, _, name, value = s
            self.fresh_name_ok(name, env, pos)
            return rest({**env, name: Var(None, None, const=value)})
        if kind == "assign":
            _, _, name, op, e = s
            var = env.get(name)
            if var is None:
                raise LangError(f"nombre no declarado: {name}", pos)
            if not var.mutable:
                raise LangError(f"{name} no es mutable: decláralo con var", pos)
            if op == "=":
                te = self.expr(e, env, var.ty)
            else:
                te = self.binary(op[:-1], self.var_te(var), self.expr(e, env, var.ty), pos, var.ty)
            te = self.coerce(te, var.ty, pos)
            sx = te.sx if self.guard is None else self.select(te.sx, self.var_te(var).sx)
            sym = self.fresh(name)
            return L(S("let"), L(L(S(sym), sx)), rest({**env, name: Var(sym, var.ty, True)}))
        if kind == "return":
            return self.coerce(self.expr(s[2], env, fn.ret), fn.ret, pos).sx
        if kind == "block":
            outer = set(env)
            return self.seq(s[2], env, lambda e: rest(self.restrict(e, env, outer)), fn)
        if kind == "dynloop":
            # Vuelta j de un bucle con cota dinámica. Las guardas son monótonas (si j < hi falla, fallan
            # todas las siguientes), así que la rama falsa salta al final del bucle: el resto del bucle
            # aparece una sola vez y el código posterior, una vez por vuelta.
            _, _, hsym, op, var, js, body = s
            if not js:
                return rest(env)
            guard = ("bin", pos, op, ("int", pos, js[0]), ("name", pos, hsym))
            nxt = ("dynloop", pos, hsym, op, var, js[1:], body)
            if not _returns(body):
                return self.seq([("if", pos, guard, [("bindconst", pos, var, js[0])] + body, None), nxt]
                                + list(rest_stmts), env, k, fn)
            c = self.coerce(self.expr(guard, env, BOOL), BOOL, pos)
            outer = set(env)
            inside = self.seq([("bindconst", pos, var, js[0])] + body, env,
                              lambda e: self.seq([nxt] + list(rest_stmts), self.restrict(e, env, outer), k, fn), fn)
            return L(S("ite"), c.sx, inside, rest(env))
        if kind == "for":
            return self.seq(self.unroll(s, env) + list(rest_stmts), env, k, fn)
        if kind == "if":
            _, _, cond, then, other = s
            c = self.coerce(self.expr(cond, env, BOOL), BOOL, pos)
            if isinstance(c.sx, Sym) and c.sx.name in ("true", "false"):
                chosen = then if c.sx.name == "true" else (other or [])
                return self.seq([("block", pos, chosen)] + list(rest_stmts), env, k, fn)
            outer = set(env)
            after = lambda e: rest(self.restrict(e, env, outer))
            if _returns(then) or _returns(other or []):
                # Alguna rama termina la función: se bifurca la continuación.
                return L(S("ite"), c.sx, self.seq(then, env, after, fn), self.seq(other or [], env, after, fn))
            # Sin return: las dos ramas se predican una tras otra. Cada asignación de la rama pasa a ser
            # x' = ite(guarda, e, x) y cada ligadura que puede quedar indefinida, ite(guarda, e, neutro).
            # Cada rama se traduce una sola vez y el tamaño crece de forma lineal con el anidamiento.
            g = self.guard
            csx = c.sx if g is None or not _partial(c.sx) else self.select(c.sx, S("false"))
            csym = self.fresh("c")
            binds = [(csym, csx)]
            if g is None:
                g_then, g_else = S(csym), L(S("not"), S(csym))
            else:
                g_then, g_else = S(self.fresh("g")), S(self.fresh("g"))
                binds += [(g_then.name, L(S("all"), g, S(csym))), (g_else.name, L(S("all"), g, L(S("not"), S(csym))))]

            def after_then(e):
                self.guard = g_else
                return self.seq(other or [], self.restrict(e, env, outer), after_else, fn)

            def after_else(e):
                self.guard = g
                return rest(self.restrict(e, env, outer))

            self.guard = g_then
            body = self.seq(then, env, after_then, fn)
            for sym, sx in reversed(binds):
                body = L(S("let"), L(L(S(sym), sx)), body)
            return body
        raise LangError(f"instrucción desconocida {kind}", pos)

    def select(self, sx, otherwise):
        """sx si se cumple la guarda; si no, otherwise. Con guarda (not c) se escribe ite(c, otherwise, sx)."""
        g = self.guard
        if isinstance(g, SList) and len(g.items) == 2 and g.items[0] == S("not"):
            return L(S("ite"), g.items[1], otherwise, sx)
        return L(S("ite"), g, sx, otherwise)

    def restrict(self, inner, env, outer):
        """Al salir de un bloque: las variables exteriores con su valor nuevo; las locales desaparecen."""
        return {n: inner[n] for n in outer}

    def fresh_name_ok(self, name, env, pos):
        if name in env:
            raise LangError(f"{name} ya está declarado: EFCH Lang 0.1 no admite sombrear nombres", pos)

    def unroll(self, s, env):
        _, pos, var, lo_e, hi_e, inclusive, body = s
        lo = self.expr(lo_e, env)
        if lo.const is None:
            raise LangError("el límite inferior del bucle debe ser constante", pos)
        hi = self.expr(hi_e, env)
        top = hi.bound
        if top is None or top + inclusive - lo.const > MAX_ITERATIONS:
            raise LangError(f"no se puede acotar el bucle con a lo sumo {MAX_ITERATIONS} vueltas: el límite "
                            "superior debe ser una constante, .len, una máscara (x & c), min(...) o una "
                            "variable inmutable con cota conocida", pos)
        out = []
        if hi.const is not None:
            for j in range(lo.const, hi.const + inclusive):
                out.append(("block", pos, [("bindconst", pos, var, j)] + body))
            return out
        hsym = f"$hi{self.fresh('')}"
        out.append(("let", pos, hsym, None, hi_e, False))
        op = "<=" if inclusive else "<"
        out.append(("dynloop", pos, hsym, op, var, list(range(lo.const, top + inclusive)), body))
        return out

    # Expresiones.
    def var_te(self, var):
        if var.const is not None:
            return TE(None, None, const=var.const)
        if var.sx is not None:
            return TE(var.sx, var.ty, mx=var.mx)
        return TE(S(var.sym), var.ty, mx=var.mx)

    def coerce(self, te, ty, pos):
        if te.ty is None:
            if ty is None or ty[0] != "bv":
                raise LangError(f"un literal entero no puede ser {core.type_str(ty) if ty else 'de tipo desconocido'}", pos)
            if not 0 <= te.const <= tmax(ty):
                raise LangError(f"el literal {te.const} no cabe en u{ty[1]}", pos)
            return TE(lit(te.const, ty[1]), ty, const=te.const)
        if te.ty == ty:
            return te
        if te.ty[0] == "bv" and ty[0] == "bv":
            if te.ty[1] < ty[1]:
                return TE(L(S("zext"), Num(ty[1]), te.sx), ty, mx=te.bound)
            raise LangError(f"conversión con pérdida de u{te.ty[1]} a u{ty[1]}: usa «as u{ty[1]}»", pos)
        if te.ty[0] == "bytes" and ty[0] == "bytes" and te.ty[1] <= ty[1]:
            return TE(te.sx, ty)
        raise LangError(f"se esperaba {core.type_str(ty)}, la expresión es {core.type_str(te.ty)}", pos)

    def unify(self, a, b, pos, expect=None):
        """Lleva dos enteros al mismo ancho (el mayor; los literales toman el del otro)."""
        if a.ty is None and b.ty is None:
            if expect and expect[0] == "bv":
                return self.coerce(a, expect, pos), self.coerce(b, expect, pos)
            raise LangError("no se puede deducir el ancho de la operación entre literales", pos)
        if a.ty is None:
            return self.coerce(a, b.ty, pos), b
        if b.ty is None:
            return a, self.coerce(b, a.ty, pos)
        if a.ty[0] != "bv" or b.ty[0] != "bv":
            if a.ty == b.ty:
                return a, b
            raise LangError(f"tipos incompatibles: {core.type_str(a.ty)} y {core.type_str(b.ty)}", pos)
        w = max(a.ty[1], b.ty[1])
        return self.coerce(a, BV(w), pos), self.coerce(b, BV(w), pos)

    def binary(self, op, a, b, pos, expect=None):
        if a.const is not None and b.const is not None and a.ty is None and b.ty is None:
            v = FOLD[op](a.const, b.const)
            if v is None or (not isinstance(v, bool) and v < 0):
                raise LangError(f"operación entre literales sin valor natural: {a.const} {op} {b.const}", pos)
            if isinstance(v, bool):
                return TE(S("true" if v else "false"), BOOL)
            return TE(None, None, const=v)
        if op in CMP_OPS:
            if a.ty == BOOL or b.ty == BOOL:
                if op not in ("==", "!=") or a.ty != b.ty:
                    raise LangError(f"«{op}» no se aplica a bool", pos)
            else:
                a, b = self.unify(a, b, pos)
            return TE(L(S(CMP_OPS[op]), a.sx, b.sx), BOOL)
        if op in ("<<", ">>"):
            if a.ty is None:
                a = self.coerce(a, expect if expect and expect[0] == "bv" else b.ty, pos)
            self.need_int(a, pos)
            b = self.shift_amount(b, a.ty, pos)
            mx = a.bound >> b.const if op == ">>" and b.const is not None else (
                a.bound >> 0 if op == ">>" else None)
            # Cota de «<<»: la del valor desplazada por la mayor cantidad posible (EXP-005).
            shift = b.const if b.const is not None else b.bound
            if op == "<<" and shift is not None and shift < 128 and a.bound is not None \
                    and a.bound << shift <= tmax(a.ty):
                mx = a.bound << shift
            return TE(L(S(ARITH_OPS[op]), a.sx, b.sx), a.ty, mx=mx)
        a, b = self.unify(a, b, pos, expect)
        self.need_int(a, pos)
        top = tmax(a.ty)
        mx = None
        if op == "&":
            mx = min(a.bound, b.bound)
        elif op in ("|", "^"):
            mx = (1 << max(a.bound, b.bound).bit_length()) - 1
        elif op == "+":
            mx = a.bound + b.bound
        elif op == "*":
            mx = a.bound * b.bound
        elif op == "%":
            mx = b.bound - 1 if b.const else min(a.bound, b.bound)
        elif op == "/":
            mx = a.bound
        if mx is not None and mx > top:
            mx = None
        return TE(L(S(ARITH_OPS[op]), a.sx, b.sx), a.ty, mx=mx)

    def shift_amount(self, b, ty, pos):
        if b.ty is None:
            return TE(lit(min(b.const, tmax(ty)), ty[1]), ty, const=b.const if b.const <= tmax(ty) else None)
        self.need_int(b, pos)
        if b.ty[1] <= ty[1]:
            return self.coerce(b, ty, pos)
        # Desplazamiento más ancho que el valor: se satura al ancho (el resultado ya es 0).
        cap = lit(ty[1], b.ty[1])
        return TE(L(S("trunc"), Num(ty[1]), L(S("ite"), L(S("ult"), b.sx, cap), b.sx, cap)), ty)

    def need_int(self, te, pos):
        if te.ty is None or te.ty[0] != "bv":
            raise LangError(f"se esperaba un entero, la expresión es {core.type_str(te.ty)}", pos)

    def expr(self, e, env, expect=None):
        kind, pos = e[0], e[1]
        if kind == "int":
            return TE(None, None, const=e[2])
        if kind == "boolc":
            return TE(S("true" if e[2] else "false"), BOOL)
        if kind == "name":
            var = env.get(e[2])
            if var is None:
                raise LangError(f"nombre no declarado: {e[2]}", pos)
            return self.var_te(var)
        if kind == "bin":
            _, _, op, a_e, b_e = e
            if op in ("&&", "||"):
                a = self.coerce(self.expr(a_e, env, BOOL), BOOL, pos)
                b = self.coerce(self.expr(b_e, env, BOOL), BOOL, pos)
                return TE(L(S("all" if op == "&&" else "any"), a.sx, b.sx), BOOL)
            sub = expect if op not in CMP_OPS else None
            return self.binary(op, self.expr(a_e, env, sub), self.expr(b_e, env, sub), pos, expect)
        if kind == "un":
            _, _, op, a_e = e
            a = self.expr(a_e, env, expect)
            if op == "!":
                return TE(L(S("not"), self.coerce(a, BOOL, pos).sx), BOOL)
            if a.ty is None:
                a = self.coerce(a, expect, pos)
            self.need_int(a, pos)
            return TE(L(S("not" if op == "~" else "neg"), a.sx), a.ty)
        if kind == "cast":
            _, _, a_e, ty = e
            a = self.expr(a_e, env)
            if ty[0] != "bv":
                raise LangError("«as» solo convierte a enteros uN", pos)
            if a.ty is None:
                return self.coerce(TE(None, None, const=a.const & tmax(ty)), ty, pos)
            if a.ty == BOOL:
                return TE(L(S("ite"), a.sx, lit(1, ty[1]), lit(0, ty[1])), ty, mx=1)
            self.need_int(a, pos)
            if a.ty[1] <= ty[1]:
                return self.coerce(a, ty, pos)
            mx = a.bound if a.bound is not None and a.bound <= tmax(ty) else None
            return TE(L(S("trunc"), Num(ty[1]), a.sx), ty, mx=mx)
        if kind == "index":
            _, _, b_e, i_e = e
            b = self.expr(b_e, env)
            if b.ty is None or b.ty[0] != "bytes":
                raise LangError("solo se indexan valores bytes[N]", pos)
            i = self.expr(i_e, env, BV(16))
            if i.ty is not None:
                self.need_int(i, pos)
                if i.ty[1] > 16:
                    raise LangError(f"el índice es u{i.ty[1]}; los índices son como mucho u16: usa «as u16» "
                                    "después de acotarlo", pos)
            return TE(L(S("byte"), b.sx, self.coerce(i, BV(16), pos).sx), BV(8))
        if kind == "len":
            b = self.expr(e[2], env)
            if b.ty is None or b.ty[0] != "bytes":
                raise LangError(".len solo se aplica a bytes[N]", pos)
            return TE(L(S("len"), b.sx), BV(16), mx=b.ty[1])
        if kind == "ite":
            _, _, c_e, a_e, b_e = e
            c = self.coerce(self.expr(c_e, env, BOOL), BOOL, pos)
            a, b = self.expr(a_e, env, expect), self.expr(b_e, env, expect)
            if a.ty is not None and a.ty[0] == "option" or b.ty is not None and b.ty[0] == "option":
                ty = expect or a.ty or b.ty
                a, b = self.coerce(a, ty, pos), self.coerce(b, ty, pos)
            elif a.ty == BOOL or b.ty == BOOL:
                a, b = self.coerce(a, BOOL, pos), self.coerce(b, BOOL, pos)
            else:
                a, b = self.unify(a, b, pos, expect)
            mx = max(a.bound, b.bound) if a.ty and a.ty[0] == "bv" else None
            return TE(L(S("ite"), c.sx, a.sx, b.sx), a.ty, mx=mx)
        if kind == "fold":
            _, _, k, lo_e, hi_e, init_e, acc, body_e, inv_e = e
            lo, hi = self.expr(lo_e, env), self.expr(hi_e, env)
            if lo.const is None or hi.const is None:
                raise LangError("las cotas de fold deben ser constantes", pos)
            if not 0 < hi.const - lo.const <= MAX_ITERATIONS:
                raise LangError(f"fold admite de 1 a {MAX_ITERATIONS} pasos", pos)
            init = self.expr(init_e, env, expect)
            ty = init.ty or expect
            if ty is None:
                raise LangError("no se puede deducir el tipo del acumulador de fold: usa uN(...)", pos)
            if ty[0] not in ("bv", "bool"):
                raise LangError("el acumulador de fold debe ser un entero uN o bool", pos)
            init = self.coerce(init, ty, pos)
            self.fresh_name_ok(k, env, pos)
            self.fresh_name_ok(acc, env, pos)
            ksym, asym = self.fresh(k), self.fresh(acc)
            # El índice se sustituye por un literal en cada paso: se envuelve en (bv 16 k) para que tenga
            # ancho en cualquier contexto (conversiones, argumentos de funciones).
            inner = {**env, k: Var(ksym, BV(16), mx=hi.const - 1, sx=L(S("bv"), Num(16), S(ksym))),
                     acc: Var(asym, ty)}
            body = self.coerce(self.expr(body_e, inner, ty), ty, pos)
            parts = [S("fold"), S(ksym), Num(lo.const), Num(hi.const), L(S(asym), init.sx), body.sx]
            if inv_e is not None:
                # El invariante ve el acumulador, no el índice (EXP-013).
                inv = self.coerce(self.expr(inv_e, {**env, acc: Var(asym, ty)}, BOOL), BOOL, pos)
                parts.append(L(S("invariant"), inv.sx))
            return TE(L(*parts), ty)
        if kind == "none":
            if not expect or expect[0] != "option":
                raise LangError("none necesita un tipo option esperado", pos)
            return TE(S("none"), expect)
        if kind == "some":
            args = e[2]
            if expect and expect[0] == "option":
                if len(args) != len(expect[1]):
                    raise LangError(f"some con {len(args)} campos para {core.type_str(expect)}", pos)
                fields = [self.coerce(self.expr(a, env, t), t, pos) for a, t in zip(args, expect[1])]
                return TE(L(S("some"), *(f.sx for f in fields)), expect)
            fields = [self.expr(a, env) for a in args]
            if any(f.ty is None for f in fields):
                raise LangError("los campos literales de some necesitan un tipo option esperado", pos)
            return TE(L(S("some"), *(f.sx for f in fields)), OPTION(*(f.ty for f in fields)))
        if kind == "call":
            _, _, name, args = e
            if name in ("min", "max") and name not in self.fns:
                if len(args) != 2:
                    raise LangError(f"{name}(a, b) recibe dos argumentos", pos)
                a, b = self.expr(args[0], env, expect), self.expr(args[1], env, expect)
                if a.ty is None and b.ty is None:
                    return TE(None, None, const=(min if name == "min" else max)(a.const, b.const))
                a, b = self.unify(a, b, pos, expect)
                self.need_int(a, pos)
                first, second = (a, b) if name == "min" else (b, a)
                mx = min(a.bound, b.bound) if name == "min" else max(a.bound, b.bound)
                return TE(L(S("ite"), L(S("ult"), a.sx, b.sx), first.sx, second.sx), a.ty, mx=mx)
            fn = self.fns.get(name)
            if fn is None or self.order.index(name) >= self.order.index(self.stack[-1]):
                raise LangError(f"función desconocida o definida después: {name}", pos)
            if len(args) != len(fn.params):
                raise LangError(f"{name} espera {len(fn.params)} argumentos", pos)
            vals = [self.expr(a, env, t) for a, (_, t, _) in zip(args, fn.params)]
            return TE(self.function(fn, vals, pos), fn.ret)
        raise LangError(f"expresión desconocida {kind}", pos)


# --- Productos de la traducción --------------------------------------------------

def _core_name(fn):
    return fn.name


def translate(text):
    """Devuelve [(función, cuerpo del núcleo como expresión S)] en orden de definición."""
    return [(fn, body) for fn, body, _ in translate_with_bounds(text)]


def translate_with_bounds(text):
    """Como translate, más las cotas de los bucles dinámicos de cada función como expresiones
    cerradas sobre sus parámetros: [(función, cuerpo, [(expresión, cota máxima, tipo)])]."""
    fns = parse_program(text)
    tr = Translator(fns)
    out = []
    for fn in fns:
        start = len(tr.loop_bounds)
        body = tr.function(fn)
        out.append((fn, body, _closed_bounds(body, tr.loop_bounds[start:])))
    return out


def _bytes_read(node):
    """Lecturas (byte entrada índice-constante) de una expresión cerrada: [(entrada, índice)]."""
    out = []
    if isinstance(node, SList):
        it = node.items
        if len(it) == 3 and isinstance(it[0], Sym) and it[0].name == "byte" and isinstance(it[1], Sym):
            k = it[2].items[-1] if isinstance(it[2], SList) else it[2]
            if isinstance(k, Num) and (it[1].name, k.value) not in out:
                out.append((it[1].name, k.value))
        for x in it:
            out += [b for b in _bytes_read(x) if b not in out]
    return out


def _sx_size(node):
    return 1 + sum(_sx_size(x) for x in node.items) if isinstance(node, SList) else 1


def _closed_bounds(body, bounds, max_nodes=4000):
    """Sustituye las ligaduras let (nombres únicos) hasta dejar cada cota en función de los parámetros."""
    defs = {}

    def collect(node):
        if isinstance(node, SList):
            items = node.items
            if items and isinstance(items[0], Sym) and items[0].name == "let":
                for b in items[1].items:
                    defs[b.items[0].name] = b.items[1]
            for x in items:
                collect(x)

    collect(body)
    memo = {}

    def subst(node):
        if isinstance(node, Sym):
            if node.name in defs:
                if node.name not in memo:
                    memo[node.name] = subst(defs[node.name])
                return memo[node.name]
            return node
        if isinstance(node, SList):
            return L(*[subst(x) for x in node.items])
        return node

    out, seen = [], set()
    for sym, mx, ty in bounds:
        if mx is None or sym not in defs:
            continue
        e = subst(S(sym))
        key = dumps(e)
        if key not in seen and _sx_size(e) <= max_nodes:
            seen.add(key)
            out.append((e, mx, ty))
    return out


def _type_sx(ty):
    if ty[0] == "bv":
        return f"(bv {ty[1]})"
    if ty[0] == "bool":
        return "bool"
    if ty[0] == "bytes":
        return f"(bytes {ty[1]})"
    return "(option " + " ".join(_type_sx(t) for t in ty[1]) + ")"


def core_definition_text(text, origin="", smt_seconds=120):
    """Una computation del núcleo por función: es lo que compila la ruta ordinaria."""
    parts = [f"; Traducción de {origin or 'un programa EFCH Lang'} al núcleo EFCH 0.1 (generado; no editar).",
             "(efch 0.1"]
    for fn, body in translate(text):
        inputs = " ".join(f"(input {n} {_type_sx(t)})" for n, t, _ in fn.params)
        parts.append(f"  (computation {_core_name(fn)} {inputs} (output {_type_sx(fn.ret)})\n"
                     f"    (semantics {dumps(body)})\n"
                     f"    (budget (llm-calls 0) (smt-seconds {smt_seconds})))")
    parts.append(")")
    return "\n".join(parts) + "\n"


def candidates_text(text, spec, origin=""):
    """Candidatas para las funciones con `implements`, comprobando la interfaz frente a la especificación."""
    out = [f"; Candidatas traducidas de {origin or 'un programa EFCH Lang'} (generado; no editar).", "(efch 0.1"]
    found = False
    for fn, body in translate(text):
        if fn.implements is None:
            continue
        comp = spec.computations.get(fn.implements)
        if comp is None:
            raise LangError(f"{fn.name} implementa {fn.implements}, que no está en la especificación", fn.pos)
        mine = [(n, t) for n, t, _ in fn.params]
        if mine != list(comp.inputs) or fn.ret != comp.output:
            want = ", ".join(f"{n}: {core.type_str(t)}" for n, t in comp.inputs)
            raise LangError(f"la interfaz de {fn.name} no coincide con {comp.name}: se espera "
                            f"({want}) -> {core.type_str(comp.output)}", fn.pos)
        out.append(f"  (candidate {fn.name}-lang (implements {comp.name})\n    (body {dumps(body)}))")
        found = True
    if not found:
        raise LangError("ninguna función declara «implements»")
    out.append(")")
    return "\n".join(out) + "\n"


def verify(text, spec, origin="", smt_seconds=None, cbmc_seconds=600):
    """Ruta de investigación: cada función con `implements` frente a su especificación.

    Primero Z3 sobre el núcleo (buena definición y equivalencia). Si la equivalencia queda
    `desconocido`, se intenta CBMC sobre el C de las dos (oráculo independiente; supuestos en
    efch/cbmc.py). Devuelve [(candidata, computación, obligaciones, estado)]."""
    from . import backend_c, cbmc, pipeline, smt
    bounds = {f"{fn.name}-lang": b for fn, _, b in translate_with_bounds(text)}
    out = []
    for cand in core.load_candidates(candidates_text(text, spec, origin), spec, origin):
        comp = spec.computations[cand.implements]
        seconds = smt_seconds or comp.budget["smt-seconds"]
        # Con bucles dinámicos, la prueba por casos suele ser mucho más rápida: el intento
        # monolítico se limita a 5 s (y se repite entero si la buena definición no se decide).
        v = pipeline.verify_candidate(comp, cand.body, min(seconds, 5) if bounds.get(cand.name) else seconds)
        if v["obligaciones"][0]["estado"] == "desconocido" and bounds.get(cand.name):
            v = pipeline.verify_candidate(comp, cand.body, seconds)
        obligations, status = list(v["obligaciones"]), v["estado"]
        wd_ok = obligations[0]["estado"] == "probado"
        if status == "desconocido" and bounds.get(cand.name):
            # Equivalencia por casos según el valor de la cota de un bucle dinámico (EXP-005).
            for expr, mx, ty in bounds[cand.name]:
                split = core.Elaborator(spec.computations).check(core.expand(expr), ty, dict(comp.inputs))
                r = smt.check_equivalence_by_cases(comp, cand.body, split, mx, seconds, _bytes_read(expr))
                obligations.append({"obligacion": f"equivalente a la semántica, por casos de {dumps(expr)[:80]}",
                                    "estado": r.status, "detalle": r.detail, "segundos": round(r.seconds, 3),
                                    "contraejemplo": r.counterexample})
                if r.status != "desconocido":
                    status = r.status if wd_ok or r.status == "refutado" else "desconocido"
                    break
        if status == "desconocido" and cbmc.CBMC.exists():
            unit = backend_c.emit_unit([(comp, cand.body, "efch_lang_impl")])
            r = cbmc.check_equivalence(comp, unit, "efch_lang_impl", timeout_s=cbmc_seconds)
            obligations.append({"obligacion": "equivalente a la semántica, en C (CBMC)", "estado": r["estado"],
                                "detalle": r["detalle"][:300], "segundos": r["segundos"],
                                "contraejemplo": r.get("traza")})
            status = r["estado"] if wd_ok or r["estado"] == "refutado" else "desconocido"
        out.append((cand, comp, obligations, status))
    return out
