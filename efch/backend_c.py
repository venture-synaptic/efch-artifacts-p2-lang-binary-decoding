"""
Materialización en C de un cuerpo EFCH 0.1.

ABI de una computación `nombre-x` (el guion pasa a guion bajo):
    entradas  (bv N)     -> uint64_t
              bool       -> int (0 o 1)
              (bytes M)  -> const uint8_t *e, size_t e_len   (precondición: e_len <= M)
    salida    (bv N)     -> devuelve uint64_t
              bool       -> devuelve int
              (bytes M)  -> parámetro final uint8_t *out (capacidad M); devuelve la longitud
              (option T1..Tk) -> parámetros finales uint64_t *out0..*outk-1; devuelve 1 (some) o 0 (none)

Las expresiones se traducen preservando la semántica de interp.py: `ite`,
`all`, `any`, `match` y los elementos de `mkbytes` más allá de la longitud se
evalúan de forma perezosa, de modo que solo se leen los bytes que la
obligación de buena definición garantiza dentro de rango. Los anchos menores
que el tipo C se enmascaran tras cada operación que puede desbordar.

La corrección de esta traducción no está demostrada: se contrasta con el
intérprete mediante pruebas diferenciales (evidencia experimental).
"""

import re

from .backend_campos import CamposMixin
from .core import EFCHError, canonical, mask

FIELD_SPLIT = True  # descomposición del acumulador en campos (backend_campos)

PRELUDE = """\
#include <stddef.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 efch_u128;

/* Operaciones con signo sobre valores de w bits guardados sin signo y enmascarados. Solo usan
   aritmética sin signo: no hay comportamiento indefinido ni dependiente de la implementación. */
#define EFCH_SIGNED_OPS(T, SUF)                                                               \\
static inline T efch_mask##SUF(unsigned w) { return w >= 8 * sizeof(T) ? (T)~(T)0 : (((T)1 << w) - 1); } \\
static inline int efch_slt##SUF(T x, T y, unsigned w) { T s = (T)1 << (w - 1); return (x ^ s) < (y ^ s); } \\
static inline T efch_sext##SUF(T x, unsigned w, unsigned n) {                                 \\
    return (x & ((T)1 << (w - 1))) ? (x | (efch_mask##SUF(n) & ~efch_mask##SUF(w))) : x; }    \\
static inline T efch_ashr##SUF(T x, T k, unsigned w) {                                        \\
    T m = efch_mask##SUF(w); int neg = (x >> (w - 1)) & 1;                                    \\
    if (k >= w) return neg ? m : 0;                                                           \\
    return (x >> k) | (neg ? (m & ~(m >> k)) : 0); }                                          \\
static inline T efch_sdiv##SUF(T x, T y, unsigned w) {                                        \\
    T m = efch_mask##SUF(w); int nx = (x >> (w - 1)) & 1, ny = (y >> (w - 1)) & 1;            \\
    if (y == 0) return nx ? 1 : m;                                                            \\
    T ax = nx ? ((T)-x & m) : x, ay = ny ? ((T)-y & m) : y, q = ax / ay;                     \\
    return (nx != ny) ? ((T)-q & m) : q; }                                                    \\
static inline T efch_srem##SUF(T x, T y, unsigned w) {                                        \\
    T m = efch_mask##SUF(w); int nx = (x >> (w - 1)) & 1, ny = (y >> (w - 1)) & 1;            \\
    if (y == 0) return x;                                                                     \\
    T ax = nx ? ((T)-x & m) : x, ay = ny ? ((T)-y & m) : y, r = ax % ay;                     \\
    return nx ? ((T)-r & m) : r; }
EFCH_SIGNED_OPS(uint64_t, 64)
EFCH_SIGNED_OPS(efch_u128, 128)
"""


def c_ident(name):
    return re.sub(r"[^0-9A-Za-z_]", "_", name)


def function_name(comp_name, candidate=None):
    base = "efch_" + c_ident(comp_name)
    return base + "__" + c_ident(candidate) if candidate else base


def ctype(ty):
    if ty[0] == "bool":
        return "int"
    return "uint64_t" if ty[1] <= 64 else "efch_u128"


def _check_interface(comp):
    for name, ty in comp.inputs:
        if ty[0] == "bv" and ty[1] > 64:
            raise EFCHError(f"la entrada {name} supera 64 bits: no se puede materializar en C")
    out = comp.output
    fields = out[1] if out[0] == "option" else ([out] if out[0] == "bv" else [])
    if any(t[0] == "bv" and t[1] > 64 for t in fields):
        raise EFCHError("la salida supera 64 bits: no se puede materializar en C")


def signature(comp, fname):
    params = []
    for name, ty in comp.inputs:
        v = "in_" + c_ident(name)
        if ty[0] == "bytes":
            params += [f"const uint8_t *{v}", f"size_t {v}_len"]
        else:
            params.append(f"{ctype(ty)} {v}")
    out = comp.output
    if out[0] == "bytes":
        ret = "size_t"
        params.append("uint8_t *out")
    elif out[0] == "option":
        ret = "int"
        params += [f"uint64_t *out{k}" for k in range(len(out[1]))]
    else:
        ret = ctype(out)
    return f"{ret} {fname}({', '.join(params) or 'void'})"


class _Emitter:
    def __init__(self):
        self.lines = []
        self.depth = 1
        self.counter = 0

    def tmp(self, prefix="t"):
        self.counter += 1
        return f"{prefix}{self.counter}"

    def emit(self, line):
        self.lines.append("    " * self.depth + line)

    def capture(self, fn):
        """Compila fn() en un búfer aparte; devuelve (resultado, líneas)."""
        saved, self.lines = self.lines, []
        self.depth += 1
        try:
            result = fn()
        finally:
            inner, self.lines = self.lines, saved
            self.depth -= 1
        return result, inner


def _const(value, ty):
    if ty[0] == "bool":
        return "1" if value else "0"
    lit = lambda v: f"UINT64_C({v:#x})" if v > 255 else f"UINT64_C({v})"
    if ty[1] <= 64:
        return lit(value)
    hi, lo = value >> 64, value & mask(64)
    return f"(((efch_u128){lit(hi)} << 64) | {lit(lo)})"


def _suf(ty):
    return "64" if ty[1] <= 64 else "128"


def _masked(expr, w):
    if w in (64, 128):
        return f"({expr})"
    return f"(({expr}) & {_const(mask(w), ('bv', w))})"


class _Compiler(CamposMixin):
    def __init__(self, em):
        self.em = em

    def scalar_ite(self, cond, a_fn, b_fn, ty):
        (a, a_lines), (b, b_lines) = self.em.capture(a_fn), self.em.capture(b_fn)
        if not a_lines and not b_lines:
            return f"({cond} ? {a} : {b})"
        t = self.em.tmp()
        self.em.emit(f"{ctype(ty)} {t};")
        self.em.emit(f"if ({cond}) {{")
        self.em.lines += a_lines
        self.em.emit(f"    {t} = {a};")
        self.em.emit("} else {")
        self.em.lines += b_lines
        self.em.emit(f"    {t} = {b};")
        self.em.emit("}")
        return t

    def bind(self, node, env):
        """Emite la ligadura de un `let` y devuelve el entorno del cuerpo. Un escalar ligado a una variable es un
        alias: el valor no cambia dentro del cuerpo (los acumuladores solo se reasignan entre pasos)."""
        a, em = node.args, self.em
        if a[0].op == "var" and a[0].ty[0] in ("bv", "bool"):
            return {**env, node.attr: env[a[0].attr]}
        if self.fm is not None and a[0].ty[0] == "bv" and self.mentions(a[0], env):
            return self.bind_fields(node, env)
        val = self.compile(a[0], env)
        name = em.tmp("v")
        if a[0].ty[0] == "bytes":
            n, p, m = val
            em.emit(f"uint64_t {name}_n = {n};")
            em.emit(f"const uint8_t *{name} = {p};")
            bound = (f"{name}_n", name, m)
        elif a[0].ty[0] == "option":
            tag, fields = val
            em.emit(f"int {name}_tag = {tag};")
            for k, (f, t) in enumerate(zip(fields, a[0].ty[1])):
                em.emit(f"{ctype(t)} {name}_{k} = {f};")
            bound = (f"{name}_tag", [f"{name}_{k}" for k in range(len(fields))])
        else:
            em.emit(f"{ctype(a[0].ty)} {name} = {val};")
            bound = name
        return {**env, node.attr: bound}

    def guarded_step(self, step, env, acc):
        """Paso de la forma (let ... (ite G acc E)): si G vale, el paso es la identidad y, como no depende del índice,
        también todos los siguientes, así que se sale del bucle; si no, acc := E. Devuelve False sin emitir nada si el
        paso no tiene esa forma (y quien llama descarta lo que se haya emitido)."""
        probe, peeled = step, []
        while probe.op == "let":
            peeled.append(probe)
            probe = probe.args[1]
        if probe.op != "ite" or probe.ty[0] not in ("bv", "bool") or probe.args[1].op != "var":
            return False
        for lt in peeled:
            env = self.bind(lt, env)
        if env.get(probe.args[1].attr) != acc:
            return False  # quien llama descarta lo emitido
        self.em.emit(f"if ({self.compile(probe.args[0], env)}) break;")
        self.em.emit(f"{acc} = {self.compile(probe.args[2], env)};")
        return True

    def compile(self, node, env):
        if (self.fm is not None and node.ty[0] == "bv" and node.op not in ("const", "var", "let")
                and self.mentions(node, env)):
            return self.assemble(list(zip(self.ivs_for(node.ty[1]), self.pieces(node, env, self.ivs_for(node.ty[1])))))
        return self._compile_plain(node, env)

    def _compile_plain(self, node, env):
        op, a, ty = node.op, node.args, node.ty
        em = self.em

        if op == "const":
            return _const(node.attr, ty)
        if op == "bool":
            return "1" if node.attr else "0"
        if op == "var":
            return env[node.attr]
        if op == "let":
            return self.compile(a[1], self.bind(node, env))
        if op == "finv":
            return self.compile(a[0], env)
        if op == "fold":
            steps = a[1:]
            uniform = len(steps) > 1 and len({canonical(st) for st in steps}) == 1
            ivs = self.field_plan(node, steps[0]) if uniform and FIELD_SPLIT else None
            if ivs:
                return self.fold_fields(node, env, ivs)
            acc = em.tmp("f")
            em.emit(f"{ctype(ty)} {acc} = {self.compile(a[0], env)};")
            if uniform:
                # Paso independiente del índice: un bucle, y si el acumulador no cambia ya no cambiará.
                k = em.tmp("k")
                em.emit(f"for (int {k} = 0; {k} < {len(steps)}; {k}++) {{")
                guarded, lines = em.capture(lambda: self.guarded_step(steps[0], {**env, node.attr: acc}, acc))
                if guarded:
                    em.lines += lines
                else:
                    val, lines = em.capture(lambda: self.compile(steps[0], {**env, node.attr: acc}))
                    em.lines += lines
                    nxt = em.tmp("n")
                    em.emit(f"    {ctype(ty)} {nxt} = {val};")
                    em.emit(f"    if ({nxt} == {acc}) break;")
                    em.emit(f"    {acc} = {nxt};")
                em.emit("}")
            else:
                for st in steps:
                    em.emit(f"{acc} = {self.compile(st, {**env, node.attr: acc})};")
            return acc
        if op == "ite":
            c = self.compile(a[0], env)
            if ty[0] in ("bv", "bool"):
                return self.scalar_ite(c, lambda: self.compile(a[1], env), lambda: self.compile(a[2], env), ty)
            return self.composite_branch(c, lambda: self.compile(a[1], env), lambda: self.compile(a[2], env), ty)
        if op in ("all", "any"):
            parts = []
            result = None
            for x in a:
                val, lines = em.capture(lambda x=x: self.compile(x, env))
                parts.append((val, lines))
            if not any(lines for _, lines in parts):
                joiner = " && " if op == "all" else " || "
                return "(" + joiner.join(v for v, _ in parts) + ")"
            result = em.tmp()
            first_val, first_lines = parts[0]
            em.lines += first_lines
            em.emit(f"int {result} = {first_val};")
            for val, lines in parts[1:]:
                em.emit(f"if ({'' if op == 'all' else '!'}{result}) {{")
                em.lines += lines
                em.emit(f"    {result} = {val};")
                em.emit("}")
            return result
        if op == "lnot":
            return f"(!{self.compile(a[0], env)})"
        if op == "none":
            return ("0", ["0"] * len(ty[1]))
        if op == "some":
            return ("1", [self.compile(x, env) for x in a])
        if op == "match":
            tag, fields = self.compile(a[0], env)
            names = []
            for k, (f, t) in enumerate(zip(fields, a[0].ty[1])):
                name = em.tmp("m")
                em.emit(f"{ctype(t)} {name} = {f};")
                names.append(name)
            inner = {**env, **dict(zip(node.attr, names))}
            some_fn = lambda: self.compile(a[1], inner)
            none_fn = lambda: self.compile(a[2], env)
            if ty[0] in ("bv", "bool"):
                return self.scalar_ite(tag, some_fn, none_fn, ty)
            return self.composite_branch(tag, some_fn, none_fn, ty)
        if op == "len":
            return f"((uint64_t){self.compile(a[0], env)[0]})"
        if op == "byte":
            _, p, _ = self.compile(a[0], env)
            return f"((uint64_t){p}[{self.compile(a[1], env)}])"
        if op == "widen":
            n, p, _ = self.compile(a[0], env)
            return (n, p, node.attr)
        if op == "mkbytes":
            m = node.attr
            n = self.compile(a[0], env)
            arr = em.tmp("b")
            em.emit(f"uint8_t {arr}[{max(m, 1)}] = {{0}};")  # los omitidos valen 0, como en la semántica
            em.emit(f"uint64_t {arr}_n = {n};")
            for k, elem in enumerate(a[1:]):
                val, lines = em.capture(lambda elem=elem: self.compile(elem, env))
                em.emit(f"if ({arr}_n > {k}) {{")
                em.lines += lines
                em.emit(f"    {arr}[{k}] = (uint8_t)({val});")
                em.emit("}")
            return (f"{arr}_n", arr, m)
        if op == "zext":
            v = self.compile(a[0], env)
            return f"(({ctype(ty)}){v})"
        if op == "sext":
            v = self.compile(a[0], env)
            return f"efch_sext{_suf(ty)}(({ctype(ty)}){v}, {a[0].ty[1]}, {ty[1]})"
        if op == "trunc":
            v = self.compile(a[0], env)
            return _masked(f"({ctype(ty)}){v}", ty[1])
        if op in ("bnot", "neg"):
            v = self.compile(a[0], env)
            return _masked(("~" if op == "bnot" else "-") + v, ty[1])

        x, y = self.compile(a[0], env), self.compile(a[1], env)
        if op in ("slt", "sle", "sgt", "sge"):
            t, w0 = a[0].ty, a[0].ty[1]
            lt = lambda p, q: f"efch_slt{_suf(t)}({p}, {q}, {w0})"
            return {"slt": lt(x, y), "sgt": lt(y, x), "sle": f"(!{lt(y, x)})", "sge": f"(!{lt(x, y)})"}[op]
        if op in ("eq", "ne", "ult", "ule", "ugt", "uge"):
            sym = {"eq": "==", "ne": "!=", "ult": "<", "ule": "<=", "ugt": ">", "uge": ">="}[op]
            return f"({x} {sym} {y})"
        w = ty[1]
        if op in ("add", "sub", "mul"):
            sym = {"add": "+", "sub": "-", "mul": "*"}[op]
            return _masked(f"{x} {sym} {y}", w)
        if op in ("and", "or", "xor"):
            sym = {"and": "&", "or": "|", "xor": "^"}[op]
            return f"({x} {sym} {y})"
        if op in ("shl", "lshr"):
            sym = "<<" if op == "shl" else ">>"
            amount = a[1]
            if amount.op == "const":
                if amount.attr >= w:
                    return _const(0, ty)
                expr = f"{x} {sym} {amount.attr}"
            else:
                expr = f"({y} >= {w} ? 0 : {x} {sym} {y})"
            return _masked(expr, w) if op == "shl" else f"({expr})"
        if op in ("sdiv", "srem", "ashr"):
            return f"efch_{op}{_suf(ty)}({x}, {y}, {w})"
        if op == "udiv":
            return f"({y} == 0 ? {_const(mask(w), ty)} : {x} / {y})"
        if op == "urem":
            return f"({y} == 0 ? {x} : {x} % {y})"
        raise EFCHError(f"operación sin traducción a C: {op}")

    def composite_branch(self, cond, a_fn, b_fn, ty):
        em = self.em
        if ty[0] == "bytes":
            m = ty[1]
            arr = em.tmp("b")
            em.emit(f"uint8_t {arr}[{max(m, 1)}];")
            em.emit(f"uint64_t {arr}_n;")
            for k, fn in enumerate((a_fn, b_fn)):
                em.emit(f"if ({cond}) {{" if k == 0 else "} else {")
                (n, p, _), lines = em.capture(fn)
                em.lines += lines
                em.emit(f"    {arr}_n = {n};")
                em.emit(f"    memcpy({arr}, {p}, (size_t){arr}_n);")
            em.emit("}")
            return (f"{arr}_n", arr, m)
        tag = em.tmp("o")
        em.emit(f"int {tag}_tag;")
        fields = [f"{tag}_{k}" for k in range(len(ty[1]))]
        for f, t in zip(fields, ty[1]):
            em.emit(f"{ctype(t)} {f} = 0;")
        for k, fn in enumerate((a_fn, b_fn)):
            em.emit(f"if ({cond}) {{" if k == 0 else "} else {")
            (vt, vf), lines = em.capture(fn)
            em.lines += lines
            em.emit(f"    {tag}_tag = {vt};")
            for f, v in zip(fields, vf):
                em.emit(f"    {f} = {v};")
        em.emit("}")
        return (f"{tag}_tag", fields)


def emit_function(comp, body, fname):
    """Devuelve el texto C de una función que materializa `body` para `comp`."""
    _check_interface(comp)
    em = _Emitter()
    env = {}
    for name, ty in comp.inputs:
        v = "in_" + c_ident(name)
        env[name] = (f"((uint64_t){v}_len)", v, ty[1]) if ty[0] == "bytes" else v
    result = _Compiler(em).compile(body, env)
    out = comp.output
    if out[0] == "bytes":
        n, p, _ = result
        em.emit(f"memcpy(out, {p}, (size_t)({n}));")
        em.emit(f"return (size_t)({n});")
    elif out[0] == "option":
        tag, fields = result
        em.emit(f"if ({tag}) {{")
        for k, f in enumerate(fields):
            em.emit(f"    *out{k} = (uint64_t)({f});")
        em.emit("}")
        em.emit(f"return {tag};")
    else:
        em.emit(f"return {result};")
    return signature(comp, fname) + "\n{\n" + "\n".join(em.lines) + "\n}\n"


def emit_unit(functions):
    """functions: [(comp, body, fname)] -> unidad de traducción completa."""
    return PRELUDE + "\n" + "\n".join(emit_function(c, b, f) for c, b, f in functions)
