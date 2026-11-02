"""
EXP-015: la generación B en dos funciones reservadas, IPv4 y varint (docs/experimentos/EXP-015.md).

    python3 experimentos/exp015.py cargas   --salida resultados/exp-015      # genera y archiva las cargas
    python3 experimentos/exp015.py d0       --salida resultados/exp-015      # vectores y diferenciales
    python3 experimentos/exp015.py d2       --salida resultados/exp-015      # check + lang verify
    python3 experimentos/exp015.py fuentes  --salida resultados/exp-015      # C de EFCH Lang (con y sin campos)
    (D3: experimentos/m9.py con las cargas y fuentes archivadas; ver la ficha)

Cargas: 3 semillas × 10 000 entradas, en tercios de bytes aleatorios, válidas y alteradas.
"""

import argparse
import json
import pathlib
import random
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from efch import backend_c, core, interp, lang, native  # noqa: E402

G4 = ROOT / "ejemplos" / "corpus-g4"
FUNCS = {"ipv4": ("ipv4-header", "baseline_ipv4_header"), "varint": ("varint-u64", "baseline_varint_u64")}
SEEDS = (20261024, 1, 2)
COUNT = 10000


def checksum_fix(h):
    h = bytearray(h)
    hl = (h[0] & 15) * 4
    h[10:12] = b"\0\0"
    s = sum((h[i] << 8 | h[i + 1]) for i in range(0, hl, 2))
    while s >> 16:
        s = (s & 0xffff) + (s >> 16)
    c = ~s & 0xffff
    h[10], h[11] = c >> 8, c & 0xff
    return bytes(h)


OPTS = [b"\x01", b"\x01", b"\x00", b"\x07\x07\x04" + bytes(4), b"\x83\x07\x04" + bytes(4), b"\x89\x07\x04" + bytes(4),
        b"\x94\x04\x00\x00", b"\x94\x04\x12\x34", b"\x44\x08\x05\x00" + bytes(4), b"\x82\x0b" + bytes(9)]


def ipv4_valid(rng):
    opts, sr, ra = b"", False, False
    for _ in range(rng.randint(0, 6)):
        o = rng.choice(OPTS)
        if o[0] in (0x83, 0x89):
            if sr:
                continue
            sr = True
        if o[0] == 0x94:
            if ra:
                continue
            ra = True
        if len(opts) + len(o) > 40:
            break
        opts += o
    opts += bytes((-len(opts)) % 4)
    hl = 20 + len(opts)
    total = hl + rng.randint(0, 200)
    h = bytes([0x40 | hl // 4, rng.getrandbits(8), total >> 8, total & 255]) + rng.randbytes(4) + \
        bytes([rng.getrandbits(8), rng.choice([1, 6, 17])]) + b"\0\0" + rng.randbytes(8) + opts
    return checksum_fix(h) + rng.randbytes(rng.randint(0, 60 - hl))


def ipv4_altered(rng):
    h = bytearray(ipv4_valid(rng))
    kind = rng.randrange(4)
    if kind == 0:
        h[rng.randrange(len(h))] = rng.getrandbits(8)
    elif kind == 1:
        h = h[:rng.randrange(1, len(h) + 1)]
    elif kind == 2 and (h[0] & 15) > 5:   # opción alterada con la suma recalculada
        hl = (h[0] & 15) * 4
        h[rng.randrange(20, hl)] = rng.choice([0, 1, 2, 0x83, 0x89, 0x94, 0xff])
        h = bytearray(checksum_fix(h))
    else:
        h[2:4] = b"\0\x0c"
        h = bytearray(checksum_fix(h))
    return bytes(h[:60])


def varint_valid(rng):
    v = rng.choice([rng.getrandbits(rng.randint(1, 64)), 0, 1, 127, 128, (1 << 64) - 1])
    out = bytearray()
    while True:
        x = v & 0x7f
        v >>= 7
        if v:
            out.append(x | 0x80)
        else:
            out.append(x)
            break
    if rng.random() < 0.1 and len(out) < 10:   # no mínima
        out[-1] |= 0x80
        out.append(0)
    return bytes(out) + rng.randbytes(rng.randint(0, 16 - len(out)))


def varint_altered(rng):
    b = bytearray(varint_valid(rng))
    kind = rng.randrange(3)
    if kind == 0:
        b = bytearray([0x80 | rng.getrandbits(7) for _ in range(rng.randint(1, 16))])
    elif kind == 1:
        b = bytearray([0xff] * 9 + [rng.randint(2, 255)]) + b[:6]
    else:
        b[rng.randrange(len(b))] = rng.getrandbits(8)
    return bytes(b[:16])


GEN = {"ipv4": (60, ipv4_valid, ipv4_altered), "varint": (16, varint_valid, varint_altered)}


def generate(d, seed, count=COUNT):
    m, valid, altered = GEN[d]
    rng = random.Random(f"exp015-{d}-{seed}")
    out = []
    for i in range(count):
        if i % 3 == 0:
            out.append(tuple(rng.randbytes(rng.randint(0 if d == "varint" else 1, m))))
        elif i % 3 == 1:
            out.append(tuple(valid(rng)))
        else:
            out.append(tuple(altered(rng)))
    return out


def load(d):
    spec = core.load_definition((G4 / d / "spec.efch").read_text(), str(G4 / d / "spec.efch"))
    comp = spec.computations[FUNCS[d][0]]
    body = core.load_candidates(lang.candidates_text((G4 / d / "prog.efl").read_text(), spec), spec)[0].body
    return spec, comp, body


def cmd_cargas(out):
    for d in GEN:
        _, comp, _ = load(d)
        for s in SEEDS:
            p = out / d / f"carga-{s}.bin"
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(native._pack_inputs(comp, [(x,) for x in generate(d, s)]))
            print(p, flush=True)


def cmd_fuentes(out):
    for d in GEN:
        spec, comp, body = load(d)
        fn = backend_c.function_name(comp.name, "lang")
        for split in (True, False):
            backend_c.FIELD_SPLIT = split
            unit = backend_c.emit_unit([(comp, body, fn)])
            p = out / "fuentes" / f"{d}-lang{'' if split else '-sin-campos'}.c"
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(unit)
            print(p, "campos:", unit.count("uint64_t fc"))
        backend_c.FIELD_SPLIT = True


def cmd_d0(out):
    vec = json.loads((G4 / "vectores.json").read_text())
    res = {}
    for d, (cname, bname) in FUNCS.items():
        spec, comp, body = load(d)
        fn = backend_c.function_name(comp.name, "lang")
        r = {"vectores": [], "diferencial": {}}
        for v in vec[cname]:
            x = tuple(bytes.fromhex(v["entrada"]))
            got = interp.run(comp.semantics, comp.inputs, [x])
            exp = None if v["esperado"] is None else tuple(int(t) for t in v["esperado"])
            g = None if got is None else tuple(int(t) for t in got)
            if g != exp:
                r["vectores"].append({"entrada": v["entrada"], "esperado": v["esperado"], "especificacion": g,
                                      "fuente": v.get("fuente")})
        r["vectores_total"] = len(vec[cname])
        unit = backend_c.emit_unit([(comp, body, fn)])
        tmp = out / "d0" / d
        tmp.mkdir(parents=True, exist_ok=True)
        lib = native.build_library(tmp, unit)
        call = native.bind(lib, comp, fn)
        (tmp / "base").mkdir(exist_ok=True)
        blib = native.build_library(tmp / "base", (G4 / d / "baseline.c").read_text())
        bcall = native.bind(blib, comp, bname)
        rng = random.Random(f"exp015-d0-{d}")
        n = fc = fb = 0
        ej = []
        cases = generate(d, 777, 60000) + [tuple(rng.randbytes(rng.randint(0, GEN[d][0]))) for _ in range(50000)]
        for x in cases:
            try:
                ref = interp.run(comp.semantics, comp.inputs, [x])
            except interp.Undefined:
                continue
            n += 1
            c, b = call([x]), bcall([x])
            if c != ref:
                fc += 1
            if b != ref:
                fb += 1
                if len(ej) < 5:
                    ej.append({"entrada": bytes(x).hex(), "especificacion": ref, "baseline": b})
        r["diferencial"] = {"entradas": n, "fallos_c_efch": fc, "fallos_baseline": fb, "ejemplos_baseline": ej}
        res[d] = r
        print(d, json.dumps({k: v for k, v in r.items() if k != "vectores"}, default=str),
              "vectores discrepantes:", len(r["vectores"]), flush=True)
    (out / "d0.json").write_text(json.dumps(res, ensure_ascii=False, indent=1, default=str))


def cmd_d2(out):
    res = {}
    for d in GEN:
        spec_p, prog_p = G4 / d / "spec.efch", G4 / d / "prog.efl"
        for name, cmd in (("check", ["check", str(spec_p)]), ("verify", ["lang", "verify", str(prog_p), str(spec_p),
                                                                         "--smt-segundos", "60"])):
            t0 = time.perf_counter()
            p = subprocess.run(["timeout", "-k", "5", "600", sys.executable, "-m", "efch", *cmd], cwd=ROOT,
                               capture_output=True, text=True)
            secs = round(time.perf_counter() - t0, 2)
            ok = "⇒ probado" in p.stdout if name == "verify" else ("desconocido" not in p.stdout
                                                                   and "refutado" not in p.stdout and p.returncode == 0)
            res[f"{d}-{name}"] = {"probado": ok, "segundos": secs, "codigo": p.returncode, "salida": p.stdout[-1500:]}
            print(d, name, ok, secs, flush=True)
    (out / "d2.json").write_text(json.dumps(res, ensure_ascii=False, indent=1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("orden", choices=["cargas", "d0", "d2", "fuentes"])
    ap.add_argument("--salida", default="resultados/exp-015")
    args = ap.parse_args()
    out = ROOT / args.salida
    out.mkdir(parents=True, exist_ok=True)
    {"cargas": cmd_cargas, "d0": cmd_d0, "d2": cmd_d2, "fuentes": cmd_fuentes}[args.orden](out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
