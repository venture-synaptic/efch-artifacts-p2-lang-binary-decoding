"""
Descomposición del acumulador de un `fold` en campos de bits (línea B del 24/10/2026; RESEARCH_PROTOCOL.md, M9).

Un programa que guarda varios datos en un acumulador `(bv 64)` (posición, indicadores, campos) obliga al C a
extraer la parte numérica en cada vuelta. Si el paso extrae un campo con una máscara contigua para usarlo como
número (posición, contador), el backend guarda ese campo en una variable aparte y el resto del acumulador en otra (o
en varias), y solo lo reconstruye al salir del bucle. Las sumas se reparten por campos cuando las cotas descartan
el acarreo; si no, se calculan enteras.

Invariante de corrección: `pieces(E, [(lo, hi)])` devuelve una expresión C cuyo valor es exactamente
`(E >> lo) & (2^(hi-lo) - 1)` y es menor que `2^(hi-lo)`. Cada regla conserva esa igualdad localmente; lo que no
cubre ninguna regla se calcula entero (con el acumulador reconstruido) y se extrae, que siempre es correcto. Las
cotas superiores (`ubp`) solo se usan para descartar acarreos y se refinan con las condiciones de las ramas.
"""

ZERO = "UINT64_C(0)"
MAX_CAMPOS = 16


def _m(n):
    return (1 << n) - 1 if n > 0 else 0


def _lit(v):
    return f"UINT64_C({v:#x})" if v > 255 else f"UINT64_C({v})"


def _is_ident(s):
    return s.replace("_", "a").isalnum() and not s[0].isdigit()


class _Parts:
    """Valor de `w` bits repartido en campos [(lo, hi, expr)]; cada expr vale menos que 2^(hi-lo)."""

    def __init__(self, w, parts):
        self.w, self.parts = w, parts


class _Estado:
    def __init__(self, ivs):
        self.ivs = ivs          # partición del acumulador [(lo, hi)]
        self.pv = {}            # expresión C reconstruida -> _Parts
        self.bound = {}         # expresión C -> cota superior conocida


def _run(c, w):
    """[lo, hi) si c es una racha contigua de unos dentro de w bits; si no, None."""
    if c <= 0 or c >= (1 << w):
        return None
    lo = (c & -c).bit_length() - 1
    hi = (c >> lo).bit_length() + lo
    return (lo, hi) if c == _m(hi) ^ _m(lo) else None


def _numeric_cuts(node, w, aliases, out, flag_test=False):
    """Fronteras de los campos que el paso extrae del acumulador con una máscara contigua para usarlos como número.
    Una extracción que solo se compara con 0 es una prueba de indicador y no parte el acumulador (EXP del 24/10:
    partir también los indicadores y los huecos hace el C más lento que no partir)."""
    op, a, ty = node.op, node.args, node.ty
    if op == "let":
        _numeric_cuts(a[0], w, aliases, out)
        inner = aliases | {node.attr} if a[0].op == "var" and a[0].attr in aliases else aliases - {node.attr}
        _numeric_cuts(a[1], w, inner, out)
        return
    if op == "match":
        _numeric_cuts(a[0], w, aliases, out)
        _numeric_cuts(a[1], w, aliases - set(node.attr), out)
        _numeric_cuts(a[2], w, aliases, out)
        return
    if op == "and" and ty == ("bv", w) and len(a) == 2 and not flag_test:
        for x, c in ((a[0], a[1]), (a[1], a[0])):
            if x.op == "var" and x.attr in aliases and c.op == "const":
                r = _run(c.attr, w)
                if r:
                    out.update(r)
    test = op in ("eq", "ne") and any(x.op == "const" and x.attr == 0 for x in a)
    for x in a:
        if hasattr(x, "op"):
            _numeric_cuts(x, w, aliases, out, flag_test=test)


def _has_fold(node):
    return node.op == "fold" or any(hasattr(x, "op") and _has_fold(x) for x in node.args)


class CamposMixin:
    """Métodos de _Compiler para la descomposición en campos. `self.fm` es el _Estado activo o None."""

    fm = None

    # --- plan ---------------------------------------------------------------------------------------------------
    def field_plan(self, node, step):
        ty = node.ty
        if ty[0] != "bv" or ty[1] > 64 or _has_fold(step) or self.fm is not None:
            return None
        w = ty[1]
        b = set()
        _numeric_cuts(step, w, frozenset({node.attr}), b)
        cuts = sorted({0, w} | {x for x in b if 0 < x < w})
        ivs = list(zip(cuts, cuts[1:]))
        return ivs if 2 <= len(ivs) <= MAX_CAMPOS else None

    def ivs_for(self, w):
        out = [(lo, min(hi, w)) for lo, hi in self.fm.ivs if lo < w]
        return out

    # --- utilidades -----------------------------------------------------------------------------------------------
    def assemble(self, parts):
        terms = [p if lo == 0 else f"({p} << {lo})" for (lo, _), p in parts if p != ZERO]
        if not terms:
            return ZERO
        return terms[0] if len(terms) == 1 else "(" + " | ".join(terms) + ")"

    def mentions(self, node, env):
        if node.op == "var":
            return env.get(node.attr) in self.fm.pv
        return any(hasattr(x, "op") and self.mentions(x, env) for x in node.args)

    @staticmethod
    def ext(v, lo, hi, w):
        if lo == 0 and hi >= w:
            return v
        if lo == 0:
            return f"(({v}) & {_lit(_m(hi))})"
        return f"((({v}) >> {lo}) & {_lit(_m(hi - lo))})"

    def pv_slice(self, pv, lo, hi):
        """Bits [lo, hi) de un valor repartido en campos."""
        terms = []
        for plo, phi, s in pv.parts:
            if s == ZERO or phi <= lo or plo >= hi:
                continue
            a, b = max(lo, plo), min(hi, phi)
            piece = s if (a, b) == (plo, phi) else self.ext(s, a - plo, b - plo, phi - plo)
            terms.append(piece if a == lo else f"({piece} << {a - lo})")
        if not terms:
            return ZERO
        return terms[0] if len(terms) == 1 else "(" + " | ".join(terms) + ")"

    # --- cotas superiores (no emiten código) ----------------------------------------------------------------------
    def ubp(self, node, env, lo, hi):
        op, a, ty = node.op, node.args, node.ty
        if ty[0] == "bool":
            return 1
        w = ty[1]
        hi = min(hi, w)
        if lo >= hi:
            return 0
        m = _m(hi - lo)
        if op == "const":
            return (node.attr >> lo) & m
        if op == "var":
            v = env.get(node.attr)
            if v in self.fm.pv:
                tot = 0
                for plo, phi, s in self.fm.pv[v].parts:
                    if s == ZERO or phi <= lo or plo >= hi:
                        continue
                    a_, b_ = max(lo, plo), min(hi, phi)
                    pb = min(self.fm.bound.get(s, _m(phi - plo)), _m(phi - plo))
                    pb = pb if (a_, b_) == (plo, phi) else _m(b_ - a_)
                    tot += pb << (a_ - lo)
                if lo == 0 and v in self.fm.bound:
                    tot = min(tot, self.fm.bound[v])
                return min(m, tot)
            b = self.fm.bound.get(v, _m(w)) if isinstance(v, str) else _m(w)
            return min(m, b >> lo)
        if op == "and":
            return min(self.ubp(x, env, lo, hi) for x in a)
        if op in ("or", "xor"):
            u = 0
            for x in a:
                u |= self.ubp(x, env, lo, hi)
            return min(m, _m(u.bit_length()))
        if op in ("add", "mul"):
            if lo > 0:
                return min(m, self.ubp(node, env, 0, hi) >> lo)
            us = [self.ubp(x, env, 0, hi) for x in a]
            tot = 0 if op == "add" else 1
            for u in us:
                tot = tot + u if op == "add" else tot * u
            return tot if tot <= m else m
        if op == "zext":
            w0 = a[0].ty[1]
            return 0 if lo >= w0 else self.ubp(a[0], env, lo, min(hi, w0))
        if op == "trunc":
            return self.ubp(a[0], env, lo, hi)
        if op in ("lshr", "shl") and a[1].op == "const":
            k = a[1].attr
            if op == "lshr":
                return 0 if lo + k >= w else self.ubp(a[0], env, lo + k, min(hi + k, w))
            if hi <= k:
                return 0
            if lo >= k:
                return self.ubp(a[0], env, lo - k, hi - k)
            return min(m, self.ubp(a[0], env, 0, hi - k) << (k - lo))
        if op == "byte":
            return min(m, 255 >> lo)
        if op == "len":
            return min(m, a[0].ty[1] >> lo)
        if op == "ite":
            return max(self.ubp(a[1], env, lo, hi), self.ubp(a[2], env, lo, hi))
        return m

    # --- refinamiento por condiciones -----------------------------------------------------------------------------
    def field_of(self, x, env):
        """Variable de campo cuyo valor es exactamente x: (and ACC racha-baja) o una ligadura de un solo campo,
        a través de zext/trunc que no recortan el campo."""
        cut = 64
        while x.op in ("zext", "trunc"):
            cut = min(cut, x.attr if x.op == "trunc" else 64)
            x = x.args[0]
        if x.op == "and" and len(x.args) == 2:
            v, c = x.args if x.args[1].op == "const" else x.args[::-1]
            if v.op == "var" and c.op == "const" and env.get(v.attr) in self.fm.pv:
                r = _run(c.attr, v.ty[1])
                if r and r[0] == 0:
                    for lo, hi, s in self.fm.pv[env[v.attr]].parts:
                        if (lo, hi) == r and hi <= cut and _is_ident(s):
                            return s
        if x.op == "var" and env.get(x.attr) in self.fm.pv:
            live = [(lo, hi, s) for lo, hi, s in self.fm.pv[env[x.attr]].parts if s != ZERO]
            if len(live) == 1 and live[0][0] == 0 and live[0][1] <= cut and _is_ident(live[0][2]):
                return live[0][2]
        return None

    def set_ub(self, x, env, b):
        if b < 0:
            return
        s = self.field_of(x, env)
        if s is not None:
            self.fm.bound[s] = min(self.fm.bound.get(s, b), b)
        if x.op != "var":
            return
        v = env.get(x.attr)
        if not isinstance(v, str):
            return
        self.fm.bound[v] = min(self.fm.bound.get(v, b), b)

    def refine(self, c, truth, env):
        op, a = c.op, c.args
        if op == "any" and not truth or op == "all" and truth:
            for x in a:
                self.refine(x, truth, env)
        elif op == "lnot":
            self.refine(a[0], not truth, env)
        elif op in ("uge", "ult") and (op == "ult") == truth:      # x < y
            self.set_ub(a[0], env, self.ubp(a[1], env, 0, a[1].ty[1]) - 1)
        elif op in ("ugt", "ule") and (op == "ule") == truth:      # x <= y
            self.set_ub(a[0], env, self.ubp(a[1], env, 0, a[1].ty[1]))
        elif op == "eq" and truth and a[1].op == "const":
            self.set_ub(a[0], env, a[1].attr)

    # --- piezas -------------------------------------------------------------------------------------------------
    def pieces(self, node, env, ivs):
        op, a, ty = node.op, node.args, node.ty
        w = ty[1]
        ivs = [(lo, min(hi, w)) for lo, hi in ivs]
        if all(lo >= hi for lo, hi in ivs):
            return [ZERO] * len(ivs)
        if op == "const":
            return [_lit((node.attr >> lo) & _m(hi - lo)) if lo < hi else ZERO for lo, hi in ivs]
        if op == "var":
            v = env[node.attr]
            if v in self.fm.pv:
                return [self.pv_slice(self.fm.pv[v], lo, hi) if lo < hi else ZERO for lo, hi in ivs]
            return [self.ext(v, lo, hi, w) if lo < hi else ZERO for lo, hi in ivs]
        if op == "let":
            return self.pieces(a[1], self.bind(node, env), ivs)
        if not self.mentions(node, env):
            v = self._compile_plain(node, env)
            return [self.ext(v, lo, hi, w) if lo < hi else ZERO for lo, hi in ivs]
        if op in ("and", "or", "xor"):
            cols = [self.pieces(x, env, ivs) for x in a]
            out = []
            for k, (lo, hi) in enumerate(ivs):
                ps = [c[k] for c in cols]
                full = _lit(_m(hi - lo))
                if op == "and":
                    if ZERO in ps:
                        out.append(ZERO)
                        continue
                    ps = [p for p in ps if p != full] or [full]
                else:
                    ps = [p for p in ps if p != ZERO] or [ZERO]
                sym = {"and": " & ", "or": " | ", "xor": " ^ "}[op]
                out.append(ps[0] if len(ps) == 1 else "(" + sym.join(ps) + ")")
            return out
        if op == "bnot":
            return [f"((~{p}) & {_lit(_m(hi - lo))})" if lo < hi else ZERO
                    for (lo, hi), p in zip(ivs, self.pieces(a[0], env, ivs))]
        if op in ("shl", "lshr") and a[1].op == "const":
            k = a[1].attr
            need, plan = [], []
            for lo, hi in ivs:
                if lo >= hi:
                    plan.append(None)
                elif op == "lshr":
                    plan.append(None if lo + k >= w else (len(need), 0))
                    if lo + k < w:
                        need.append((lo + k, min(hi + k, w)))
                elif hi <= k:
                    plan.append(None)
                elif lo >= k:
                    plan.append((len(need), 0))
                    need.append((lo - k, hi - k))
                else:
                    plan.append((len(need), k - lo))
                    need.append((0, hi - k))
            got = self.pieces(a[0], env, need) if need else []
            return [ZERO if p is None or got[p[0]] == ZERO else (got[p[0]] if p[1] == 0 else f"({got[p[0]]} << {p[1]})")
                    for p in plan]
        if op in ("zext", "trunc"):
            w0 = a[0].ty[1]
            need = [(lo, min(hi, w0)) if lo < min(hi, w0) else (0, 0) for lo, hi in ivs]
            got = self.pieces(a[0], env, need)
            return [g if lo < hi else ZERO for (lo, hi), g in zip(need, got)]
        if op == "add" and len(a) == 2:
            out = []
            for lo, hi in ivs:
                if lo >= hi:
                    out.append(ZERO)
                elif lo == 0:
                    x, y = self.pieces(a[0], env, [(0, hi)])[0], self.pieces(a[1], env, [(0, hi)])[0]
                    out.append(f"(({x} + {y}) & {_lit(_m(hi))})")
                elif self.ubp(a[0], env, 0, lo) + self.ubp(a[1], env, 0, lo) <= _m(lo):
                    x, y = self.pieces(a[0], env, [(lo, hi)])[0], self.pieces(a[1], env, [(lo, hi)])[0]
                    if y == ZERO:
                        out.append(x)
                    elif x == ZERO:
                        out.append(y)
                    else:
                        out.append(f"(({x} + {y}) & {_lit(_m(hi - lo))})")
                else:
                    out.append(None)
            if None in out:
                v = self._compile_plain(node, env)
                out = [self.ext(v, lo, hi, w) if p is None else p for (lo, hi), p in zip(ivs, out)]
            return out
        if op == "ite":
            c = self.compile(a[0], env)
            saved = dict(self.fm.bound)
            self.refine(a[0], True, env)
            ta, la = self.em.capture(lambda: self.pieces(a[1], env, ivs))
            self.fm.bound = dict(saved)
            self.refine(a[0], False, env)
            tb, lb = self.em.capture(lambda: self.pieces(a[2], env, ivs))
            self.fm.bound = saved
            if not la and not lb:
                return [x if x == y else f"({c} ? {x} : {y})" for x, y in zip(ta, tb)]
            ts = [self.em.tmp("p") for _ in ivs]
            for t in ts:
                self.em.emit(f"uint64_t {t};")
            self.em.emit(f"if ({c}) {{")
            self.em.lines += la
            for t, x in zip(ts, ta):
                self.em.emit(f"    {t} = {x};")
            self.em.emit("} else {")
            self.em.lines += lb
            for t, y in zip(ts, tb):
                self.em.emit(f"    {t} = {y};")
            self.em.emit("}")
            return ts
        v = self._compile_plain(node, env)
        return [self.ext(v, lo, hi, w) if lo < hi else ZERO for lo, hi in ivs]

    def bind_fields(self, node, env):
        """`let` escalar que depende del acumulador: se guarda repartido en campos."""
        val = node.args[0]
        w = val.ty[1]
        ivs = self.ivs_for(w)
        bounds = [self.ubp(val, env, lo, hi) for lo, hi in ivs]
        ps = self.pieces(val, env, ivs)
        parts = []
        for (lo, hi), p, b in zip(ivs, ps, bounds):
            if p != ZERO and not _is_ident(p):
                t = self.em.tmp("c")
                self.em.emit(f"uint64_t {t} = {p};")
                p = t
            if p != ZERO:
                self.fm.bound[p] = min(self.fm.bound.get(p, b), b)
            parts.append((lo, hi, p))
        pv = _Parts(w, parts)
        key = self.assemble([((lo, hi), p) for lo, hi, p in parts])
        self.fm.pv.setdefault(key, pv)  # misma expresión C = mismo valor
        return {**env, node.attr: key}

    # --- el bucle -----------------------------------------------------------------------------------------------
    def fold_fields(self, node, env, ivs):
        em = self.em
        a, ty = node.args, node.ty
        steps = a[1:]
        self.fm = _Estado(ivs)
        try:
            init = self.pieces(a[0], env, ivs)
            fields = [em.tmp("fc") for _ in ivs]
            for f, p in zip(fields, init):
                em.emit(f"uint64_t {f} = {p};")
            acc_str = self.assemble(list(zip(ivs, fields)))
            self.fm.pv[acc_str] = _Parts(ty[1], [(lo, hi, f) for (lo, hi), f in zip(ivs, fields)])
            k = em.tmp("k")
            em.emit(f"for (int {k} = 0; {k} < {len(steps)}; {k}++) {{")

            def body():
                benv = {**env, node.attr: acc_str}
                probe = steps[0]
                while probe.op == "let":
                    benv = self.bind(probe, benv)
                    probe = probe.args[1]
                guarded = probe.op == "ite" and probe.args[1].op == "var" and benv.get(probe.args[1].attr) == acc_str
                if guarded:
                    em.emit(f"if ({self.compile(probe.args[0], benv)}) break;")
                    self.refine(probe.args[0], False, benv)
                    new = self.pieces(probe.args[2], benv, ivs)
                else:
                    new = self.pieces(probe, benv, ivs)
                nts = [em.tmp("nc") for _ in ivs]
                for t, p in zip(nts, new):
                    em.emit(f"uint64_t {t} = {p};")
                if not guarded:
                    em.emit("if (" + " && ".join(f"{t} == {f}" for t, f in zip(nts, fields)) + ") break;")
                for t, f in zip(nts, fields):
                    em.emit(f"{f} = {t};")
            _, lines = em.capture(body)
            em.lines += lines
            em.emit("}")
            res = em.tmp("f")
            em.emit(f"uint64_t {res} = {acc_str};")
            return res
        finally:
            self.fm = None
