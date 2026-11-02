"""
Intérprete del núcleo EFCH 0.1: la semántica operacional de referencia.

Valores: bv -> int en [0, 2^N), bool -> bool, bytes -> tuple de ints,
option -> None o tuple. Una expresión está indefinida si lee un byte fuera de
la longitud o construye bytes más largos que su máximo; en ese caso se lanza
`Undefined`. `ite`, `all`, `any` y `match` son perezosos (solo evalúan la rama
tomada); `let` es estricto. Para la división entre cero se sigue SMT-LIB:
udiv x 0 = 2^N - 1 y urem x 0 = x. Los desplazamientos >= N dan 0.
Con signo (complemento a dos, como bvsdiv, bvsrem y bvashr de SMT-LIB): la división trunca hacia
cero; sdiv x 0 = -1 si x >= 0 y 1 si x < 0; srem x 0 = x; srem lleva el signo del dividendo;
sdiv(-2^(N-1), -1) = -2^(N-1); ashr con k >= N replica el bit de signo.
"""

from .core import mask


def signed(x, w):
    return x - (1 << w) if x >> (w - 1) else x


class Undefined(Exception):
    pass


def evaluate(node, env):
    op, a = node.op, node.args
    if op == "const":
        return node.attr
    if op == "bool":
        return node.attr
    if op == "var":
        return env[node.attr]
    if op == "let":
        return evaluate(a[1], {**env, node.attr: evaluate(a[0], env)})
    if op == "finv":
        return evaluate(a[0], env)
    if op == "fold":
        acc = evaluate(a[0], env)
        for step in a[1:]:
            acc = evaluate(step, {**env, node.attr: acc})
        return acc
    if op == "ite":
        return evaluate(a[1] if evaluate(a[0], env) else a[2], env)
    if op == "all":
        return all(evaluate(x, env) for x in a)
    if op == "any":
        return any(evaluate(x, env) for x in a)
    if op == "lnot":
        return not evaluate(a[0], env)
    if op == "match":
        v = evaluate(a[0], env)
        if v is None:
            return evaluate(a[2], env)
        return evaluate(a[1], {**env, **dict(zip(node.attr, v))})
    if op == "none":
        return None
    if op == "some":
        return tuple(evaluate(x, env) for x in a)
    if op == "len":
        return len(evaluate(a[0], env))
    if op == "byte":
        b, i = evaluate(a[0], env), evaluate(a[1], env)
        if i >= len(b):
            raise Undefined(f"lectura del byte {i} con longitud {len(b)}")
        return b[i]
    if op == "mkbytes":
        n = evaluate(a[0], env)
        if n > node.attr:
            raise Undefined(f"mkbytes de longitud {n} supera el máximo {node.attr}")
        elems = a[1:]
        return tuple(evaluate(elems[k], env) if k < len(elems) else 0 for k in range(n))
    if op == "widen":
        return evaluate(a[0], env)
    if op == "zext":
        return evaluate(a[0], env)
    if op == "sext":
        return signed(evaluate(a[0], env), a[0].ty[1]) & mask(node.attr)
    if op in ("slt", "sle", "sgt", "sge"):
        w = a[0].ty[1]
        x, y = signed(evaluate(a[0], env), w), signed(evaluate(a[1], env), w)
        return {"slt": x < y, "sle": x <= y, "sgt": x > y, "sge": x >= y}[op]
    if op == "trunc":
        return evaluate(a[0], env) & mask(node.attr)
    if op in ("eq", "ne", "ult", "ule", "ugt", "uge"):
        x, y = evaluate(a[0], env), evaluate(a[1], env)
        return {"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y, "ugt": x > y, "uge": x >= y}[op]
    w = node.ty[1]
    m = mask(w)
    if op == "bnot":
        return ~evaluate(a[0], env) & m
    if op == "neg":
        return -evaluate(a[0], env) & m
    x, y = evaluate(a[0], env), evaluate(a[1], env)
    if op == "add":
        return (x + y) & m
    if op == "sub":
        return (x - y) & m
    if op == "mul":
        return (x * y) & m
    if op == "udiv":
        return m if y == 0 else x // y
    if op == "urem":
        return x if y == 0 else x % y
    if op == "and":
        return x & y
    if op == "or":
        return x | y
    if op == "xor":
        return x ^ y
    if op == "shl":
        return 0 if y >= w else (x << y) & m
    if op == "lshr":
        return 0 if y >= w else x >> y
    if op == "ashr":
        return (signed(x, w) >> min(y, w)) & m
    if op in ("sdiv", "srem"):
        sx, sy = signed(x, w), signed(y, w)
        if sy == 0:
            return ((1 if sx < 0 else m) if op == "sdiv" else x)
        q, r = abs(sx) // abs(sy), abs(sx) % abs(sy)
        if op == "sdiv":
            return (-q if (sx < 0) != (sy < 0) else q) & m
        return (-r if sx < 0 else r) & m
    raise ValueError(f"operación sin semántica: {op}")


def run(comp_or_body, inputs, args):
    """Evalúa una computación (o un cuerpo de candidata) con argumentos posicionales."""
    body = getattr(comp_or_body, "semantics", comp_or_body)
    return evaluate(body, {name: v for (name, _), v in zip(inputs, args)})
