"""
Cargas de trabajo declaradas en una definición.

    (workload
      (seeds 20261020 1 2)
      (count 10000)
      (input NOMBRE GENERADOR) ...)

Generadores:
    (bits N)              entero uniforme de N bits
    (mix (PESO GEN) ...)  elige un generador según pesos enteros
    (via COMP GEN ...)    aplica otra computación (por su semántica) a los valores generados
    (random-bytes A B)    longitud uniforme en [A, B] y contenido uniforme
"""

import random

from .core import EFCHError
from .interp import run
from .sexpr import Num, SList, Sym

DEFAULT_SEEDS = (20261020, 1, 2)
DEFAULT_COUNT = 10_000


def _generator(sx, definition):
    head = sx.head() if isinstance(sx, SList) else None
    args = sx.items[1:] if head else ()
    if head == "bits" and len(args) == 1 and isinstance(args[0], Num):
        bits = args[0].value
        return lambda rng: rng.getrandbits(bits) if bits else 0
    if head == "mix":
        weights, gens = [], []
        for opt in args:
            if not (isinstance(opt, SList) and len(opt.items) == 2 and isinstance(opt.items[0], Num)):
                raise EFCHError("forma: (mix (PESO GEN) ...)", opt)
            weights.append(opt.items[0].value)
            gens.append(_generator(opt.items[1], definition))
        return lambda rng: rng.choices(gens, weights)[0](rng)
    if head == "via" and args and isinstance(args[0], Sym):
        comp = definition.computations.get(args[0].name)
        if comp is None:
            raise EFCHError(f"computación desconocida en via: {args[0].name}", args[0])
        gens = [_generator(g, definition) for g in args[1:]]
        if len(gens) != len(comp.inputs):
            raise EFCHError(f"via {comp.name} necesita {len(comp.inputs)} generadores", sx)
        return lambda rng: run(comp, comp.inputs, [g(rng) for g in gens])
    if head == "random-bytes" and len(args) == 2 and all(isinstance(a, Num) for a in args):
        lo, hi = args[0].value, args[1].value
        return lambda rng: tuple(rng.getrandbits(8) for _ in range(rng.randint(lo, hi)))
    raise EFCHError("generador no reconocido; se admiten bits, mix, via y random-bytes", sx)


def parse(comp, definition):
    """Devuelve (semillas, cantidad, generadores por entrada) de la carga de comp."""
    sx = comp.workload
    if sx is None:
        raise EFCHError(f"{comp.name} no declara (workload ...)")
    seeds, count, gens = DEFAULT_SEEDS, DEFAULT_COUNT, {}
    for item in sx.items[1:]:
        head = item.head() if isinstance(item, SList) else None
        if head == "seeds":
            seeds = tuple(x.value for x in item.items[1:])
        elif head == "count":
            count = item.items[1].value
        elif head == "input" and len(item.items) == 3 and isinstance(item.items[1], Sym):
            gens[item.items[1].name] = _generator(item.items[2], definition)
        else:
            raise EFCHError("en workload se admiten seeds, count e input", item)
    missing = [n for n, _ in comp.inputs if n not in gens]
    if missing:
        raise EFCHError(f"la carga no define generador para: {', '.join(missing)}", sx)
    return seeds, count, gens


def generate(comp, definition, seed, count=None):
    """Lista de tuplas de argumentos (en el orden de las entradas) para una semilla."""
    seeds, default_count, gens = parse(comp, definition)
    rng = random.Random(seed)
    return [tuple(gens[name](rng) for name, _ in comp.inputs) for _ in range(count or default_count)]


def edge_inputs(comp, rng, n_random=2000):
    """Entradas de borde y aleatorias para las pruebas diferenciales del backend."""
    per_input = []
    for _, ty in comp.inputs:
        if ty[0] == "bv":
            w = ty[1]
            vals = {0, 1, (1 << w) - 1}
            for k in range(w):
                for d in (-1, 0, 1):
                    v = (1 << k) + d
                    if 0 <= v < (1 << w):
                        vals.add(v)
            vals = sorted(vals)
            gen = lambda rng, w=w: rng.getrandbits(rng.randint(1, w))
        elif ty[0] == "bool":
            vals, gen = [False, True], lambda rng: rng.random() < 0.5
        else:
            m = ty[1]
            vals = [()] + [tuple([b] * k) for k in range(1, m + 1) for b in (0x00, 0x7F, 0x80, 0xFF)]
            gen = lambda rng, m=m: tuple(rng.randrange(0x80, 0x100) if rng.random() < 0.7 else rng.randrange(0x80)
                                         for _ in range(rng.randint(0, m)))
        per_input.append((vals, gen))
    cases = []
    longest = max((len(v) for v, _ in per_input), default=0)
    for k in range(longest):
        cases.append(tuple(v[k % len(v)] for v, _ in per_input))
    for _ in range(n_random):
        cases.append(tuple(g(rng) for _, g in per_input))
    return cases
