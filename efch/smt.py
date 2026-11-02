"""
Semántica del núcleo EFCH 0.1 en lógica de vectores de bits (SMT, Z3).

Cada expresión se traduce a un valor simbólico y a una condición de buena
definición D. Las obligaciones de prueba se formulan como «para toda entrada
del dominio declarado» y se comprueban refutando su negación:

    unsat    -> probado     (bajo los supuestos registrados)
    sat      -> refutado    (con contraejemplo, confirmado con el intérprete)
    unknown  -> desconocido (tiempo agotado o el solver no decide)

Supuestos de toda prueba: la semántica del núcleo EFCH 0.1 definida aquí y en
interp.py, el dominio declarado de las entradas (p. ej. bytes de longitud
<= M) y la corrección de Z3.
"""

import functools
import time
from dataclasses import dataclass

from . import _z3
from .core import Node, canonical, mask, rename_free
from .interp import Undefined, evaluate

z3 = _z3.z3


@dataclass
class SymBytes:
    n: object        # BitVec 16
    b: list          # BitVec 8, longitud = máximo


@dataclass
class SymOpt:
    tag: object      # Bool
    fields: list


def _bool_val(v):
    return z3.BoolVal(v)


def make_input(name, ty):
    if ty[0] == "bv":
        return z3.BitVec(name, ty[1]), []
    if ty[0] == "bool":
        return z3.Bool(name), []
    if ty[0] == "bytes":
        # El espacio no puede aparecer en un nombre de EFCH: así la longitud y los bytes de `b` no comparten
        # símbolo con una entrada llamada `b.len` o `b[0]` (auditoría de Codex Astra, 23/10/2026).
        n = z3.BitVec(f"{name} len", 16)
        return SymBytes(n, [z3.BitVec(f"{name} [{k}]", 8) for k in range(ty[1])]), \
            [z3.ULE(n, z3.BitVecVal(ty[1], 16))]
    raise ValueError(ty)


def merge(c, a, b, ty):
    if ty[0] in ("bv", "bool"):
        return z3.If(c, a, b)
    if ty[0] == "bytes":
        return SymBytes(z3.If(c, a.n, b.n), [z3.If(c, x, y) for x, y in zip(a.b, b.b)])
    return SymOpt(z3.If(c, a.tag, b.tag), [z3.If(c, x, y) for x, y in zip(a.fields, b.fields)])


def obs_eq(x, y, ty):
    """Igualdad observable: ignora bytes tras la longitud y campos de none."""
    if ty[0] in ("bv", "bool"):
        return x == y
    if ty[0] == "bytes":
        same = [z3.Implies(z3.ULT(z3.BitVecVal(k, 16), x.n), bx == by) for k, (bx, by) in enumerate(zip(x.b, y.b))]
        return z3.And(x.n == y.n, *same)
    fields = [fx == fy for fx, fy in zip(x.fields, y.fields)]
    return z3.And(x.tag == y.tag, z3.Implies(x.tag, z3.And(*fields)) if fields else z3.BoolVal(True))


def _widen(v, m):
    return SymBytes(v.n, v.b + [z3.BitVecVal(0, 8)] * (m - len(v.b)))


class _TranslationTimeout(Exception):
    pass


_deadline = None   # instante (time.monotonic) en que la traducción en curso agota su presupuesto


def _bounded(as_list=False, label=None):
    """La traducción a Z3 de una obligación también consume su presupuesto `timeout_s`.

    Sin esto, una traducción que crece de forma exponencial (DNS de EXP-007) no termina y no deja
    ni un «desconocido». Agotado el plazo, la obligación queda «desconocido» con motivo. Cada
    llamada anidada tiene su propio plazo y restaura el de la exterior. `label(args)` da el nombre de la
    obligación, el mismo que tendría sin cortar: con él la clasifica el exportador (efch/evidencia.py)."""
    def wrap(fn):
        pos = fn.__code__.co_varnames.index("timeout_s")

        @functools.wraps(fn)
        def inner(*args, **kwargs):
            global _deadline
            timeout_s = kwargs["timeout_s"] if "timeout_s" in kwargs else args[pos]
            saved, t0 = _deadline, time.perf_counter()
            _deadline = time.monotonic() + timeout_s
            try:
                return fn(*args, **kwargs)
            except _TranslationTimeout:
                name = label(args) if label else args[0]
                r = Result(name, "desconocido", time.perf_counter() - t0,
                           f"la traducción a Z3 agotó el límite de {timeout_s} s")
                return [r] if as_list else r
            finally:
                _deadline = saved
        return inner
    return wrap


def _value(v):
    return z3.is_bv_value(v) or z3.is_true(v) or z3.is_false(v)


def _fold(r, *args):
    """Con todos los operandos constantes, el resultado ya es un valor (simplify sobre un término mínimo).

    Así `byte` reconoce un índice constante sin llamar a simplify sobre el índice entero, que recorre
    cada vez todo el estado anterior y hacía cuadrática la traducción (DNS de EXP-007, EXP-017)."""
    return z3.simplify(r) if all(_value(x) for x in args) else r


def translate(node, env):
    """Devuelve (valor simbólico, condición de buena definición)."""
    if _deadline is not None and time.monotonic() > _deadline:
        raise _TranslationTimeout()
    op, a = node.op, node.args
    T = z3.BoolVal(True)
    if op == "const":
        return z3.BitVecVal(node.attr, node.ty[1]), T
    if op == "bool":
        return _bool_val(node.attr), T
    if op == "var":
        return env[node.attr], T
    if op == "let":
        v, d1 = translate(a[0], env)
        body, d2 = translate(a[1], {**env, node.attr: v})
        return body, z3.And(d1, d2)
    if op == "finv":
        return translate(a[0], env)
    if op == "fold":
        acc, d = translate(a[0], env)
        for step in a[1:]:
            acc, ds = translate(step, {**env, node.attr: acc})
            d = z3.And(d, ds)
        return acc, d
    if op == "ite":
        c, dc = translate(a[0], env)
        x, dx = translate(a[1], env)
        y, dy = translate(a[2], env)
        if z3.is_true(c) or z3.is_false(c):
            return (x, z3.And(dc, dx)) if z3.is_true(c) else (y, z3.And(dc, dy))
        return merge(c, x, y, node.ty), z3.And(dc, z3.If(c, dx, dy))
    if op in ("all", "any"):
        vals, defs = zip(*(translate(x, env) for x in a))
        # Cortocircuito: x_k solo necesita estar definido si los anteriores no deciden.
        d = T
        for k in range(len(vals) - 1, -1, -1):
            cont = vals[k] if op == "all" else z3.Not(vals[k])
            d = z3.And(defs[k], z3.Implies(cont, d)) if k < len(vals) - 1 else defs[k]
        return (z3.And(*vals) if op == "all" else z3.Or(*vals)), d
    if op == "lnot":
        v, d = translate(a[0], env)
        return _fold(z3.Not(v), v), d
    if op == "none":
        return SymOpt(z3.BoolVal(False), [_default(t) for t in node.ty[1]]), T
    if op == "some":
        vals, defs = zip(*(translate(x, env) for x in a)) if a else ((), ())
        return SymOpt(z3.BoolVal(True), list(vals)), z3.And(T, *defs)
    if op == "match":
        s, ds = translate(a[0], env)
        x, dx = translate(a[1], {**env, **dict(zip(node.attr, s.fields))})
        y, dy = translate(a[2], env)
        return merge(s.tag, x, y, node.ty), z3.And(ds, z3.If(s.tag, dx, dy))
    if op == "len":
        v, d = translate(a[0], env)
        return v.n, d
    if op == "byte":
        v, d1 = translate(a[0], env)
        i, d2 = translate(a[1], env)
        if z3.is_bv_value(i):
            k = i.as_long()
            val = v.b[k] if k < len(v.b) else z3.BitVecVal(0, 8)
        else:
            val = z3.BitVecVal(0, 8)
            for k in range(len(v.b) - 1, -1, -1):
                val = z3.If(i == k, v.b[k], val)
        return val, z3.And(d1, d2, z3.ULT(i, v.n))
    if op == "mkbytes":
        n, dn = translate(a[0], env)
        m = node.attr
        elems, defs = [], [dn, z3.ULE(n, z3.BitVecVal(m, 16))]
        for k in range(m):
            if k + 1 < len(a):
                e, de = translate(a[k + 1], env)
                elems.append(e)
                defs.append(z3.Implies(z3.ULT(z3.BitVecVal(k, 16), n), de))
            else:
                elems.append(z3.BitVecVal(0, 8))
        return SymBytes(n, elems), z3.And(*defs)
    if op == "widen":
        v, d = translate(a[0], env)
        return _widen(v, node.attr), d
    if op == "zext":
        v, d = translate(a[0], env)
        return _fold(z3.ZeroExt(node.attr - a[0].ty[1], v), v), d
    if op == "sext":
        v, d = translate(a[0], env)
        return _fold(z3.SignExt(node.attr - a[0].ty[1], v), v), d
    if op == "trunc":
        v, d = translate(a[0], env)
        return _fold(z3.Extract(node.attr - 1, 0, v), v), d
    if op in ("bnot", "neg"):
        v, d = translate(a[0], env)
        return _fold(~v if op == "bnot" else -v, v), d
    x, dx = translate(a[0], env)
    y, dy = translate(a[1], env)
    d = z3.And(dx, dy)
    if op in ("eq", "ne"):
        return _fold(x == y if op == "eq" else x != y, x, y), d
    cmp = {"ult": z3.ULT, "ule": z3.ULE, "ugt": z3.UGT, "uge": z3.UGE,
           "slt": lambda p, q: p < q, "sle": lambda p, q: p <= q, "sgt": lambda p, q: p > q, "sge": lambda p, q: p >= q}
    if op in cmp:
        return _fold(cmp[op](x, y), x, y), d
    arith = {
        "add": lambda: x + y, "sub": lambda: x - y, "mul": lambda: x * y,
        "udiv": lambda: z3.UDiv(x, y), "urem": lambda: z3.URem(x, y),
        "and": lambda: x & y, "or": lambda: x | y, "xor": lambda: x ^ y,
        "shl": lambda: x << y, "lshr": lambda: z3.LShR(x, y),
        # En z3py, / y >> sobre vectores de bits son bvsdiv y bvashr.
        "sdiv": lambda: x / y, "srem": lambda: z3.SRem(x, y), "ashr": lambda: x >> y,
    }
    return _fold(arith[op](), x, y), d


def _default(t):
    return z3.BitVecVal(0, t[1]) if t[0] == "bv" else z3.BoolVal(False)


# --- Obligaciones ------------------------------------------------------------

@dataclass
class Result:
    obligation: str
    status: str            # probado | refutado | desconocido
    seconds: float
    detail: str = ""
    counterexample: dict = None

    def as_dict(self):
        return {"obligacion": self.obligation, "estado": self.status, "segundos": round(self.seconds, 3),
                "detalle": self.detail, "contraejemplo": self.counterexample}


def _model_value(model, sym, ty):
    if ty[0] == "bv":
        return model.eval(sym, model_completion=True).as_long()
    if ty[0] == "bool":
        return z3.is_true(model.eval(sym, model_completion=True))
    n = model.eval(sym.n, model_completion=True).as_long()
    return tuple(model.eval(sym.b[k], model_completion=True).as_long() for k in range(n))


def prove(name, claim, domain, timeout_s, variables, confirm=None):
    """Prueba `claim` para todas las asignaciones que cumplen `domain`.

    variables: [(nombre, tipo, símbolo)] para reconstruir contraejemplos.
    confirm(valores) -> (refutado_confirmado: bool, detalle) re-evalúa el
    contraejemplo con el intérprete, para no fiarse solo de la traducción.
    """
    solver = z3.SolverFor("QF_BV")
    solver.set("timeout", int(timeout_s * 1000))
    solver.add(*domain)
    solver.add(z3.Not(claim))
    t0 = time.perf_counter()
    answer = solver.check()
    elapsed = time.perf_counter() - t0
    if answer == z3.unsat:
        return Result(name, "probado", elapsed)
    if answer == z3.unknown:
        return Result(name, "desconocido", elapsed, f"Z3: {solver.reason_unknown()}")
    model = solver.model()
    values = {n: _model_value(model, s, t) for n, t, s in variables}
    shown = {n: (list(v) if isinstance(v, tuple) else v) for n, v in values.items()}
    if confirm is not None:
        ok, detail = confirm(values)
        if not ok:
            return Result(name, "desconocido", elapsed,
                          "inconsistencia: Z3 halló un contraejemplo que el intérprete no reproduce: " + detail, shown)
        return Result(name, "refutado", elapsed, detail, shown)
    return Result(name, "refutado", elapsed, "", shown)


def _symbolic_inputs(inputs):
    env, domain, variables = {}, [], []
    for name, ty in inputs:
        sym, dom = make_input(name, ty)
        env[name] = sym
        domain += dom
        variables.append((name, ty, sym))
    return env, domain, variables


def _eval_or_undefined(node, env):
    try:
        return evaluate(node, env)
    except Undefined as e:
        return Undefined(str(e))


def py_obs_eq(x, y, ty):
    if isinstance(x, Undefined) or isinstance(y, Undefined):
        return False
    return x == y


# --- Pliegues: verificación modular (núcleo 0.2, EXP-009) -------------------------------------
#
# Un `fold` es semánticamente la cadena de let de sus pasos (translate lo traduce así). Estas dos vías
# solo intentan probarlo sin expandir; si cualquier subprueba no sale «probado», devuelven None y el
# llamante sigue por la vía de siempre. Nunca concluyen «refutado».

def _folds(node, out, bound=frozenset()):
    """Pliegues más externos (con su anotación de invariante, si la tienen), en orden de recorrido, cada uno
    con los nombres que ligan los `let`, `match`, `fold` y `finv` que lo rodean."""
    if node.op in ("fold", "finv"):
        out.append((node, bound))
        return out
    if node.op == "let":
        _folds(node.args[0], out, bound)
        _folds(node.args[1], out, bound | {node.attr})
        return out
    if node.op == "match":
        _folds(node.args[0], out, bound)
        _folds(node.args[1], out, bound | set(node.attr))
        _folds(node.args[2], out, bound)
        return out
    for a in node.args:
        _folds(a, out, bound)
    return out


def free_vars(node):
    if node.op == "var":
        return {node.attr}
    if node.op == "let":
        return free_vars(node.args[0]) | (free_vars(node.args[1]) - {node.attr})
    if node.op == "match":
        return free_vars(node.args[0]) | (free_vars(node.args[1]) - set(node.attr)) | free_vars(node.args[2])
    if node.op == "finv":
        return free_vars(node.args[0]) | (free_vars(node.args[1]) - {node.attr})
    if node.op == "fold":
        out = free_vars(node.args[0])
        for st in node.args[1:]:
            out |= free_vars(st) - {node.attr}
        return out
    out = set()
    for a in node.args:
        out |= free_vars(a)
    return out


def _abstract(node, table):
    """Sustituye cada pliegue de `table` (por identidad) por una variable libre."""
    for f, name in table:
        if node is f:
            return Node("var", (), f.ty, name)
    if not node.args:
        return node
    return Node(node.op, tuple(_abstract(a, table) for a in node.args), node.ty, node.attr)


def _fold_of(u):
    return u.args[0] if u.op == "finv" else u


def _bound_names(node, out=None):
    out = set() if out is None else out
    if node.op in ("let", "fold", "finv"):
        out.add(node.attr)
    elif node.op == "match":
        out.update(node.attr)
    for a in node.args:
        _bound_names(a, out)
    return out


def _inline_aliases(node):
    """(let ((x y)) cuerpo) con y variable → cuerpo[x := y], si y no se vuelve a ligar dentro (EXP-013).
    Así el pliegue de una computación llamada queda expresado sobre las variables de quien llama."""
    if node.op == "let" and node.args[0].op == "var":
        y = node.args[0].attr
        body = node.args[1]
        if y not in _bound_names(body):
            return _inline_aliases(rename_free(body, {node.attr: y}))
    if not node.args:
        return node
    return Node(node.op, tuple(_inline_aliases(a) for a in node.args), node.ty, node.attr)


def _distinct_steps(f):
    seen, out = set(), []
    for st in f.args[1:]:
        key = canonical(st)
        if key not in seen:
            seen.add(key)
            out.append(st)
    return out


def _closed_folds(node, inputs):
    """Pliegues cuyas variables libres son entradas; None si alguno no lo es (no se intenta)."""
    names = {n for n, _ in inputs}
    found = _folds(node, [])
    # Una variable libre del pliegue ligada por un `let` o `match` que lo rodea no es la entrada del mismo
    # nombre: abstraerlo o demostrar su invariante sobre la entrada daría un «probado» falso (revisión de
    # Codex Astra, 23/10/2026).
    if not found or any(free_vars(f) - names or free_vars(f) & bound or f.attr in names for f, bound in found):
        return None
    return [f for f, _ in found]


def _fresh(base, *nodes, inputs=()):
    """Nombre que no aparece en `nodes` ni en `inputs`: un nombre interno que coincida con uno del usuario
    lo capturaría y daría un «probado» falso (auditoría de Codex Astra, 23/10/2026)."""
    used = {n for n, _ in inputs}
    for node in nodes:
        used |= free_vars(node) | _bound_names(node)
    k = 0
    while f"{base}{k}" in used:
        k += 1
    return f"{base}{k}"


def _sum(results):
    return sum(r.seconds for r in results)


def check_well_defined_modular(label, body, inputs, timeout_s):
    """Buena definición sin expandir: INIT bien definido, cada paso distinto bien definido para TODO
    acumulador (sobreaproximación) y el resto bien definido para todo valor del pliegue."""
    body = _inline_aliases(body)
    units = _closed_folds(body, inputs)
    if units is None:
        return None
    folds = units
    done, table = [], []
    for k, u in enumerate(units):
        f = _fold_of(u)
        r = check_well_defined(f"{label}: valor inicial del pliegue {k}", f.args[0], inputs, timeout_s)
        done.append(r)
        if r.status != "probado":
            return None
        for st in _distinct_steps(f):
            r = check_well_defined(f"{label}: paso del pliegue {k}", st, list(inputs) + [(f.attr, f.ty)], timeout_s)
            done.append(r)
            if r.status != "probado":
                return None
        table.append((u, _fresh(f"fold%{k}_", body, inputs=list(inputs) + [(n, None) for _, n in table])))
    rest = check_well_defined(label, _abstract(body, table), list(inputs) + [(n, f.ty) for f, n in table],
                              timeout_s, modular=False)
    if rest.status != "probado":
        return None
    return Result(label, "probado", _sum(done) + rest.seconds,
                  f"vía modular: {len(folds)} pliegue(s), {len(done)} subpruebas")


def check_equivalence_congruence(comp, body, timeout_s):
    """Congruencia de pliegues: los de la semántica y los de la candidata se emparejan en orden. Si los
    valores iniciales coinciden (donde el de la semántica está definido) y, para TODO acumulador, cada
    paso de la candidata coincide con el de la semántica donde este está definido, los dos pliegues
    valen lo mismo siempre que el de la semántica esté definido (inducción sobre los pasos). Entonces
    se sustituyen por la misma variable libre y basta probar el resto para todo valor de ella."""
    sem, body = _inline_aliases(comp.semantics), _inline_aliases(body)
    us, uc = _closed_folds(sem, comp.inputs), _closed_folds(body, comp.inputs)
    if us is None or uc is None or len(us) != len(uc):
        return None
    fs = us
    done, ts, tc = [], [], []
    for k, (ua, ub) in enumerate(zip(us, uc)):
        a, b = _fold_of(ua), _fold_of(ub)
        if a.ty != b.ty or len(a.args) != len(b.args):
            return None
        pairs = [(a.args[0], b.args[0], list(comp.inputs), {})]
        acc = _fresh(f"acc%{k}_", a, b, inputs=comp.inputs)
        for sa, sb in zip(a.args[1:], b.args[1:]):
            pairs.append((rename_free(sa, {a.attr: acc}), rename_free(sb, {b.attr: acc}),
                          list(comp.inputs) + [(acc, a.ty)], {}))
        seen = set()
        for x, y, ins, _ in pairs:
            key = (canonical(x), canonical(y))
            if key in seen:
                continue
            seen.add(key)
            env, domain, variables = _symbolic_inputs(ins)
            vx, dx = translate(x, env)
            vy, _ = translate(y, env)
            r = prove(f"congruencia del pliegue {k}", z3.Implies(dx, vx == vy), domain, timeout_s, variables)
            done.append(r)
            if r.status != "probado":
                return None
        name = _fresh(f"fold%{k}_", sem, body, inputs=list(comp.inputs) + [(n, None) for _, n in ts])
        ts.append((ua, name))
        tc.append((ub, name))
    ins = list(comp.inputs) + [(n, f.ty) for f, n in ts]
    env, domain, variables = _symbolic_inputs(ins)
    spec, ds = translate(_abstract(sem, ts), env)
    cand, _ = translate(_abstract(body, tc), env)
    rest = prove("equivalente a la semántica", z3.Implies(ds, obs_eq(spec, cand, comp.output)), domain,
                 timeout_s, variables)
    if rest.status != "probado":
        return None
    return Result("equivalente a la semántica", "probado", _sum(done) + rest.seconds,
                  f"vía modular: congruencia de {len(fs)} pliegue(s), {len(done)} subpruebas")


def _invariant_obligations(u, k, inputs, timeout_s):
    """(a) el valor inicial cumple el invariante; (b) cada paso distinto lo conserva para todo acumulador."""
    f, inv = u.args[0], u.args[1]
    # El paso y el invariante pueden nombrar distinto su acumulador (formas internas fold%/finv%); se pasan
    # los dos a un nombre que no aparece en ninguno, para que ningún let o match lo capture (EXP-013).
    acc = _fresh("acc%inv_", f, inv, inputs=inputs)
    inv = rename_free(inv, {u.attr: acc})
    out = []
    env, domain, variables = _symbolic_inputs(inputs)
    v0, d0 = translate(f.args[0], env)
    vi, di = translate(inv, {**env, acc: v0})
    out.append(prove(f"invariante del pliegue {k}: valor inicial", z3.Implies(d0, z3.And(di, vi)), domain,
                     timeout_s, variables))
    ins = list(inputs) + [(acc, f.ty)]
    for st in _distinct_steps(f):
        st = rename_free(st, {f.attr: acc})
        env, domain, variables = _symbolic_inputs(ins)
        vi, di = translate(inv, env)
        vs, ds = translate(st, env)
        vn, dn = translate(inv, {**env, acc: vs})
        out.append(prove(f"invariante del pliegue {k}: el paso lo conserva",
                         z3.Implies(z3.And(di, vi, ds), z3.And(dn, vn)), domain, timeout_s, variables))
    return out


@_bounded(as_list=True, label=lambda args: "invariantes de los pliegues")
def check_fold_invariants(body, inputs, timeout_s):
    """Obligaciones de los invariantes declarados (EXP-013), para informarlas con su estado."""
    units = _closed_folds(_inline_aliases(body), inputs) or []
    out = []
    for k, u in enumerate(units):
        if u.op == "finv":
            out += _invariant_obligations(u, k, inputs, timeout_s)
    return out


def relation(text, prop):
    """Elabora la relación R de un plan de prueba relacional (EXP-014): booleana, sobre las variables de la
    propiedad."""
    from .core import BOOL, Elaborator, expand
    from .sexpr import parse
    return Elaborator({}).check(expand(parse(text)[0]), BOOL, dict(prop.variables))


def _relational_lemma(prop, units, i, j, rel, timeout_s):
    """Congruencia condicional (EXP-014): si R está bien definida, R ⇒ I₁ = I₂ y, para cada posición,
    R ⇒ ∀s. T₁(s) = T₂(s), entonces R ⇒ F₁ = F₂ (inducción sobre los pasos; los pasos están bien definidos
    para todo acumulador, lo comprueba quien llama). Devuelve (subpruebas, válido)."""
    if not (0 <= i < len(units) and 0 <= j < len(units)) or i == j:
        return [], False
    if _folds(rel, []) or free_vars(rel) - {n for n, _ in prop.variables}:
        return [], False
    a, b = _fold_of(units[i]), _fold_of(units[j])
    if a.ty != b.ty or len(a.args) != len(b.args):
        return [], False
    done = [check_well_defined(f"propiedad {prop.name}: relación R bien definida", rel, prop.variables, timeout_s,
                               modular=False)]
    if done[-1].status != "probado":
        return done, False
    acc = _fresh("acc%rel_", a, b, rel, inputs=prop.variables)
    pairs = [(a.args[0], b.args[0], list(prop.variables))]
    pairs += [(rename_free(x, {a.attr: acc}), rename_free(y, {b.attr: acc}), list(prop.variables) + [(acc, a.ty)])
              for x, y in zip(a.args[1:], b.args[1:])]
    seen = set()
    for k, (x, y, ins) in enumerate(pairs):
        key = (canonical(x), canonical(y))
        if key in seen:
            continue
        seen.add(key)
        env, domain, variables = _symbolic_inputs(ins)
        vr, dr = translate(rel, env)
        vx, _ = translate(x, env)
        vy, _ = translate(y, env)
        what = "valor inicial" if k == 0 else f"paso {k - 1}"
        done.append(prove(f"propiedad {prop.name}: congruencia condicional, {what}",
                          z3.Implies(z3.And(dr, vr), vx == vy), domain, timeout_s, variables))
        if done[-1].status != "probado":
            return done, False
    return done, True


def check_property_modular(prop, timeout_s, relations=()):
    """Propiedad con cada pliegue cerrado sustituido por una variable libre, restringida por su invariante
    si este está demostrado (EXP-013) y por R ⇒ fᵢ = fⱼ si la congruencia condicional de un plan relacional
    está demostrada (EXP-014). Exige la buena definición modular de cada pliegue. Solo concluye «probado»
    (la abstracción es más débil que la semántica); si no, None."""
    body = _inline_aliases(prop.body)
    units = _closed_folds(body, prop.variables)
    if units is None:
        return None
    done, table, invs = [], [], []
    for k, u in enumerate(units):
        f = _fold_of(u)
        parts = [check_well_defined(f"propiedad {prop.name}: valor inicial del pliegue {k}", f.args[0],
                                    prop.variables, timeout_s)]
        parts += [check_well_defined(f"propiedad {prop.name}: paso del pliegue {k}", st,
                                     list(prop.variables) + [(f.attr, f.ty)], timeout_s) for st in _distinct_steps(f)]
        done += parts
        if any(r.status != "probado" for r in parts):
            return None
        name = _fresh(f"fold%{k}_", body, inputs=list(prop.variables) + [(n, None) for _, n in table])
        table.append((u, name))
        if u.op == "finv":
            obligations = _invariant_obligations(u, k, prop.variables, timeout_s)
            done += obligations
            if all(r.status == "probado" for r in obligations):
                invs.append(rename_free(u.args[1], {u.attr: name}))
    lemmas = []
    for i, j, rel in relations:
        parts, ok = _relational_lemma(prop, units, i, j, rel, timeout_s)
        done += parts
        if ok:
            lemmas.append((rel, table[i][1], table[j][1]))
    ins = list(prop.variables) + [(n, _fold_of(u).ty) for u, n in table]
    env, domain, variables = _symbolic_inputs(ins)
    v, d = translate(_abstract(body, table), env)
    assumptions = []
    for inv in invs:
        vi, di = translate(inv, env)
        assumptions.append(z3.And(di, vi))
    for rel, fi, fj in lemmas:
        vr, dr = translate(rel, env)
        assumptions.append(z3.Implies(z3.And(dr, vr), env[fi] == env[fj]))
    rest = prove(f"propiedad {prop.name}", z3.Implies(z3.And(*assumptions), z3.And(d, v)), domain, timeout_s, variables)
    if rest.status != "probado":
        return None
    return Result(f"propiedad {prop.name}", "probado", _sum(done) + rest.seconds,
                  f"vía modular: {len(units)} pliegue(s) abstraído(s), {len(invs)} invariante(s), "
                  + (f"{len(lemmas)} congruencia(s) condicional(es), " if relations else "")
                  + f"{len(done)} subpruebas")


@_bounded()
def check_well_defined(label, body, inputs, timeout_s, modular=True):
    if modular:
        r = check_well_defined_modular(label, body, inputs, timeout_s)
        if r is not None:
            return r
    env, domain, variables = _symbolic_inputs(inputs)
    _, d = translate(body, env)

    def confirm(values):
        r = _eval_or_undefined(body, values)
        return (isinstance(r, Undefined), f"indefinida para esta entrada: {r}" if isinstance(r, Undefined)
                else f"el intérprete devuelve {r!r}")

    return prove(label, d, domain, timeout_s, variables, confirm)


@_bounded(label=lambda args: "equivalente a la semántica")
def check_equivalence(comp, body, timeout_s):
    """La candidata coincide observablemente con la semántica en todo el dominio."""
    r = check_equivalence_congruence(comp, body, timeout_s)
    if r is not None:
        return r
    env, domain, variables = _symbolic_inputs(comp.inputs)
    spec, ds = translate(comp.semantics, env)
    cand, dc = translate(body, env)
    claim = z3.Implies(ds, obs_eq(spec, cand, comp.output))

    def confirm(values):
        s, c = _eval_or_undefined(comp.semantics, values), _eval_or_undefined(body, values)
        if isinstance(s, Undefined):
            return False, "la semántica está indefinida en el contraejemplo"
        return (not py_obs_eq(s, c, comp.output), f"esperado {_show(s)}, obtenido {_show(c)}")

    return prove("equivalente a la semántica", claim, domain, timeout_s, variables, confirm)


@_bounded(label=lambda args: "equivalente a la semántica")
def check_equivalence_by_cases(comp, body, split, mx, timeout_s, bytes_read=()):
    """Equivalencia partida en casos que cubren todo el dominio (EXP-005).

    Si `split` (la cota de un bucle dinámico, expresión sobre las entradas) depende de algún byte
    leído en posición constante, un caso por cada uno de los 256 valores del primero de ellos: fijar
    el byte deja la estructura del bucle concreta. Si no, un caso por cada valor 0..mx de split y
    otro para split > mx, así que la partición es completa aunque mx no lo fuera. Probado si todos
    los casos lo están; el primer caso que no se prueba decide."""
    env, domain, variables = _symbolic_inputs(comp.inputs)
    spec, ds = translate(comp.semantics, env)
    cand, dc = translate(body, env)
    claim = z3.Implies(ds, obs_eq(spec, cand, comp.output))

    def confirm(values):
        s, c = _eval_or_undefined(comp.semantics, values), _eval_or_undefined(body, values)
        if isinstance(s, Undefined):
            return False, "la semántica está indefinida en el contraejemplo"
        return (not py_obs_eq(s, c, comp.output), f"esperado {_show(s)}, obtenido {_show(c)}")

    if bytes_read:
        name, index = bytes_read[0]
        byte = env[name].b[index]
        cases = [byte == v for v in range(256)]
    else:
        value, _ = translate(split, env)
        width = value.size()
        cases = [value == z3.BitVecVal(k, width) for k in range(mx + 1)]
        if mx < (1 << width) - 1:
            cases.append(z3.UGT(value, z3.BitVecVal(mx, width)))
    total = 0.0
    for case in cases:
        r = prove("equivalente a la semántica", claim, domain + [case], timeout_s, variables, confirm)
        total += r.seconds
        if r.status != "probado":
            return Result(r.obligation, r.status, total, f"caso {case}: {r.detail}", r.counterexample)
    return Result("equivalente a la semántica", "probado", total, f"{len(cases)} casos")


@_bounded(label=lambda args: f"propiedad {args[0].name}")
def check_property(prop, timeout_s, relations=()):
    r = check_property_modular(prop, timeout_s, relations)
    if r is not None:
        return r
    env, domain, variables = _symbolic_inputs(prop.variables)
    v, d = translate(prop.body, env)

    def confirm(values):
        r = _eval_or_undefined(prop.body, values)
        return (r is not True, f"el intérprete evalúa la propiedad a {_show(r)}")

    return prove(f"propiedad {prop.name}", z3.And(d, v), domain, timeout_s, variables, confirm)


def _show(v):
    if isinstance(v, Undefined):
        return f"indefinido ({v})"
    if isinstance(v, tuple):
        return "(" + " ".join(str(x) for x in v) + ")"
    return repr(v)
