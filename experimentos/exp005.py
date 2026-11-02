"""
EXP-005: viabilidad de EFCH Lang frente a Rust + Kani y Dafny (docs/experimentos/EXP-005.md).

    python3 experimentos/exp005.py vectores                       # especificaciones frente a los vectores
    python3 experimentos/exp005.py todo --salida resultados/exp-005

Corpus en ejemplos/corpus/<función>/: spec.efch, prog.efl, baseline.c, impl.rs, impl.go, impl.dfy.
Para cada función y cada implementación:
1. verificación formal (EFCH: Z3 y después CBMC; Rust: Kani; Dafny), con su tiempo de reloj,
   ejecutada como subproceso con 2,5 GB de memoria como máximo;
2. vectores de la fuente y pruebas diferenciales frente al intérprete de la especificación
   (C de EFCH Lang, C a mano, Rust, Go y Dafny traducido a Python);
3. medición ns/op (`-O3 -march=native`; Rust con opt-level=3 y target-cpu=native, enlazado en el
   mismo arnés en C; Go con su propio bucle, sin inlining);
4. líneas escritas a mano (esfuerzo para obtener la garantía).
"""

import argparse
import json
import os
import pathlib
import platform
import random
import re
import shutil
import statistics
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from efch import backend_c, cbmc, core, interp, lang, native, workload  # noqa: E402

CORPUS = ROOT / "ejemplos" / "corpus"
OPT = pathlib.Path.home() / ".local" / "opt"
DAFNY = OPT / "dafny" / "dafny"
KANI_PATH = f"{OPT / 'kani-cli' / 'bin'}:{pathlib.Path.home() / '.cargo' / 'bin'}"
MEMORY = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=2500M", "-p", "MemorySwapMax=0"]
CFLAGS = ["-O3", "-march=native"]
RUST_LINK = ["-lpthread", "-ldl", "-lm", "-lrt", "-lutil", "-lgcc_s"]

# (directorio, computación, función de Go); el orden es el de la ficha.
FUNCTIONS = [
    ("quic", "quic-varint-decode", "QuicVarintDecode"),
    ("hpack", "hpack-int-decode", "HpackIntDecode"),
    ("cbor", "cbor-head-decode", "CborHeadDecode"),
    ("utf8", "utf8-decode", "Utf8Decode"),
    ("base64", "base64-block-decode", "Base64BlockDecode"),
    ("ipv4", "ipv4-header-check", "Ipv4HeaderCheck"),
    ("compactsize", "compactsize-decode", "CompactsizeDecode"),
    ("msgpack", "msgpack-int-decode", "MsgpackIntDecode"),
]


# --- Vectores ------------------------------------------------------------------

def vectors():
    return json.loads((CORPUS / "vectores.json").read_text())


def vector_args(comp_name, case):
    """Argumentos en el orden de las entradas de la computación."""
    buf = tuple(bytes.fromhex(case["in"].replace(" ", "")))
    return [case["n"], buf] if comp_name == "hpack-int-decode" else [buf]


def load_spec(d):
    path = CORPUS / d / "spec.efch"
    return core.load_definition(path.read_text(), str(path))


def check_vectors(run, comp_name):
    """Devuelve la lista de vectores que fallan con run(args)."""
    fails = []
    for case in vectors()[comp_name]["casos"]:
        expected = None if case["out"] is None else tuple(case["out"])
        try:
            got = run(vector_args(comp_name, case))
        except Exception as e:  # una lectura indefinida también es un fallo
            got = f"error: {e}"
        if got != expected:
            fails.append({"in": case["in"], "esperado": case["out"], "obtenido": got})
    return fails


def cmd_vectores(_args):
    ok = True
    for d, name, _ in FUNCTIONS:
        comp = load_spec(d).computations[name]
        fails = check_vectors(lambda a: interp.run(comp, comp.inputs, a), name)
        n = len(vectors()[name]["casos"])
        print(f"{name}: {n - len(fails)}/{n}")
        for f in fails:
            print("   ", f)
        ok &= not fails
    return 0 if ok else 1


# --- Utilidades ----------------------------------------------------------------

def timed(cmd, cwd=ROOT, env=None, timeout=900):
    """Ejecuta con el límite de memoria; devuelve (segundos de reloj, código, salida)."""
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(MEMORY + cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        rc, out = proc.returncode, proc.stdout + proc.stderr
    except subprocess.TimeoutExpired as e:
        rc, out = "timeout", (e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
    return round(time.perf_counter() - t0, 2), rc, out


def code_lines(text, comment):
    return sum(1 for l in text.splitlines() if l.strip() and not l.strip().startswith(comment))


def spec_lines(text):
    """Líneas de las computaciones (entradas, salida y semántica), sin carga, objetivo ni presupuesto."""
    n, skip = 0, 0
    for line in text.splitlines():
        s = line.strip()
        if skip:
            skip += s.count("(") - s.count(")")
            continue
        if not s or s.startswith(";") or s.startswith("(efch") or s.startswith("(baseline-c"):
            continue
        if s.startswith(("(doc", "(workload", "(objective", "(budget")):
            skip = s.count("(") - s.count(")")
            continue
        n += 1
    return n


def dafny_annotations(text):
    """Anotaciones de prueba de Dafny: todo lo que no es código ni la postcondición principal."""
    pat = re.compile(r"^\s*(invariant|decreases|assert|requires|ensures|ghost|lemma)\b")
    return sum(1 for l in text.splitlines() if pat.match(l) and "== Spec(" not in l)


def encode_line(args):
    n = args[0] if len(args) == 2 else 0
    buf = bytes(args[-1]).hex() or "-"
    return f"{n} {buf}"


def decode_line(line):
    line = line.strip()
    if line == "null":
        return None
    return tuple({"true": True, "false": False}.get(t, None) if t in ("true", "false") else int(t)
                 for t in line.split())


def differential_inputs(comp, spec):
    rng = random.Random(20261021)
    cases = workload.edge_inputs(comp, rng, 3000)
    cases += workload.generate(comp, spec, 20261021, 2000)
    return [list(c) for c in cases]


def external_differential(comp, spec, runner_cmd, cwd):
    """Pruebas diferenciales de un programa externo con el protocolo de líneas."""
    cases = differential_inputs(comp, spec)
    proc = subprocess.run(runner_cmd, cwd=cwd, input="\n".join(encode_line(c) for c in cases) + "\n",
                          capture_output=True, text=True, timeout=600)
    outs = proc.stdout.splitlines()
    fails = []
    for args, line in zip(cases, outs):
        exp = interp.run(comp, comp.inputs, args)
        got = decode_line(line)
        if got != exp:
            fails.append({"entrada": encode_line(args), "esperado": exp, "obtenido": got})
    if len(outs) != len(cases):
        fails.append({"error": f"{len(outs)} salidas para {len(cases)} casos", "stderr": proc.stderr[-500:]})
    return {"casos": len(cases), "fallos": len(fails), "ejemplos": fails[:3]}


def external_vectors(name, runner_cmd, cwd):
    cases = vectors()[name]["casos"]
    lines = [encode_line(vector_args(name, c)) for c in cases]
    proc = subprocess.run(runner_cmd, cwd=cwd, input="\n".join(lines) + "\n", capture_output=True, text=True)
    outs = dict(zip(lines, map(decode_line, proc.stdout.splitlines())))
    return check_vectors(lambda a: outs.get(encode_line(a), "sin salida"), name)


# --- Implementaciones ----------------------------------------------------------

def efch_part(d, name, spec, comp, out):
    prog = CORPUS / d / "prog.efl"
    text = prog.read_text()
    cands = core.load_candidates(lang.candidates_text(text, spec), spec)
    body = cands[0].body
    row = {"vectores_fallidos": check_vectors(lambda a: interp.run(body, comp.inputs, a), name)}
    secs, rc, log = timed([sys.executable, "-m", "efch", "lang", "verify", str(prog), str(CORPUS / d / "spec.efch"),
                           "--smt-segundos", "60"], env={**os.environ, "PYTHONPATH": str(ROOT)})
    (out / "efch-verify.txt").write_text(log)
    m = re.search(r"⇒ (\w+)", log)
    row["verificacion"] = {"estado": m.group(1) if m else f"error ({rc})", "segundos": secs,
                           "herramienta": "CBMC" if "CBMC" in log and "probado" in log.split("CBMC")[-1][:80] else "Z3"}
    fname = backend_c.function_name(comp.name, "lang")
    (out / "dif-efch").mkdir(exist_ok=True)
    lib = native.build_library(out / "dif-efch", backend_c.emit_unit([(comp, body, fname)]))
    row["diferencial"] = native.differential(comp, spec, native.bind(lib, comp, fname))
    row["lineas"] = {"especificacion": spec_lines((CORPUS / d / "spec.efch").read_text()),
                     "programa": code_lines(text, "//")}
    row["lineas"]["total"] = row["lineas"]["especificacion"] + row["lineas"]["programa"]
    # Variante «solo especificación»: la ruta ordinaria compila la propia especificación.
    secs2, rc2, log2 = timed([sys.executable, "-m", "efch", "check", str(CORPUS / d / "spec.efch")],
                             env={**os.environ, "PYTHONPATH": str(ROOT)})
    row["solo_especificacion"] = {"estado": "probado" if "✓ probado      semántica bien definida" in log2
                                  and "desconocido" not in log2 else f"desconocido ({rc2})",
                                  "segundos": secs2, "lineas": row["lineas"]["especificacion"]}
    return row, body, fname


def c_part(d, name, spec, comp, out):
    fname = f"baseline_{backend_c.c_ident(comp.name)}"
    (out / "dif-c").mkdir(exist_ok=True)
    lib = native.build_library(out / "dif-c", "", CORPUS / d / "baseline.c")
    call = native.bind(lib, comp, fname)
    return {"vectores_fallidos": check_vectors(call, name),
            "diferencial": native.differential(comp, spec, call),
            "lineas": code_lines((CORPUS / d / "baseline.c").read_text(), ("/*", "*", "//", "#include"))}, fname


def rust_part(d, name, spec, comp, out):
    src = CORPUS / d / "impl.rs"
    text = src.read_text()
    fname = f"rust_{backend_c.c_ident(comp.name)}"
    lib_path = out / f"lib{d}-rust.so"
    subprocess.run(["rustc", "--edition", "2021", "--crate-type", "cdylib", "-C", "opt-level=3",
                    "-o", str(lib_path), str(src)], check=True, capture_output=True)
    import ctypes
    call = native.bind(ctypes.CDLL(str(lib_path)), comp, fname)
    static = out / f"lib{d}-rust.a"
    subprocess.run(["rustc", "--edition", "2021", "--crate-type", "staticlib", "-C", "opt-level=3",
                    "-C", "target-cpu=native", "-C", "panic=abort", "-o", str(static), str(src)],
                   check=True, capture_output=True)
    env = {**os.environ, "PATH": f"{KANI_PATH}:{os.environ['PATH']}", "RUSTFLAGS": "--edition=2021"}
    secs, rc, log = timed(["timeout", "600", "kani", str(src), "--target-dir", str(out / "kani-target")], env=env)
    (out / "kani.txt").write_text(log)
    shutil.rmtree(out / "kani-target", ignore_errors=True)
    estado = "probado" if "VERIFICATION:- SUCCESSFUL" in log else (
        "refutado" if "VERIFICATION:- FAILED" in log else f"desconocido ({rc})")
    effort = text.split("// --- ABI")[0]
    return {"vectores_fallidos": check_vectors(call, name),
            "diferencial": native.differential(comp, spec, call),
            "verificacion": {"estado": estado, "segundos": secs},
            "lineas": code_lines(effort, "//")}, fname, static


def dafny_part(d, name, spec, comp, out):
    src = CORPUS / d / "impl.dfy"
    text = src.read_text()
    secs, rc, log = timed(["timeout", "600", str(DAFNY), "verify", str(src)])
    (out / "dafny.txt").write_text(log)
    m = re.search(r"finished with (\d+) verified, (\d+) error", log)
    estado = "probado" if m and m.group(2) == "0" else f"desconocido ({rc})"
    tdir = out / "dafny-py"
    shutil.rmtree(tdir, ignore_errors=True)
    subprocess.run([str(DAFNY), "translate", "py", str(src), "--no-verify", "--include-runtime",
                    "-o", str(tdir / "m")], check=True, capture_output=True)
    pydir = tdir / "m-py"
    method = re.search(r"^method (\w+)\(", text, re.M).group(1)
    (pydir / "runner.py").write_text(f"""import sys
sys.path.insert(0, {str(pydir)!r})
import _dafny, module_
from module_ import default__
two = {name == "hpack-int-decode"}
for line in sys.stdin:
    n, h = line.split()
    buf = _dafny.Seq(list(bytes.fromhex('' if h == '-' else h)))
    r = default__.{method}(int(n), buf) if two else default__.{method}(buf)
    if r.is_None:
        print("null")
    else:
        print(" ".join(("true" if x else "false") if isinstance(x, bool) else str(int(x)) for x in r.value))
""")
    runner = [sys.executable, str(pydir / "runner.py")]
    # Variante «solo especificación» (revisión de Codex, hallazgo 5): las funciones de Dafny son
    # ejecutables, así que el método puede devolver Spec(...) sin invariantes.
    m2 = re.search(r"^method \w+\((.*?)\)[^\n]*\n\s*ensures r == (Spec\(.*?\))\n\{", text, re.M | re.S)
    head = text[:m2.end()]
    spec_only = head + f"\n  return {m2.group(2)};\n}}\n"
    spec_only = re.sub(r"\n// .*?\n", "\n", spec_only)
    (out / "dafny-solo-spec.dfy").write_text(spec_only)
    secs2, rc2, log2 = timed(["timeout", "600", str(DAFNY), "verify", str(out / "dafny-solo-spec.dfy")])
    m3 = re.search(r"finished with (\d+) verified, (\d+) error", log2)
    return {"vectores_fallidos": external_vectors(name, runner, pydir),
            "diferencial": external_differential(comp, spec, runner, pydir),
            "verificacion": {"estado": estado, "segundos": secs},
            "lineas": code_lines(text, "//"),
            "anotaciones": dafny_annotations(text),
            "solo_especificacion": {"estado": "probado" if m3 and m3.group(2) == "0" else f"desconocido ({rc2})",
                                    "segundos": secs2, "lineas": code_lines(spec_only, "//")}}


GO_MAIN = """package corpus

import (
	"bufio"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"os"
	"sort"
	"strconv"
	"strings"
	"time"
)

var fn = {func}

func Main() {{
	if len(os.Args) == 4 && os.Args[1] == "bench" {{
		bench(os.Args[2], os.Args[3])
		return
	}}
	sc := bufio.NewScanner(os.Stdin)
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	for sc.Scan() {{
		f := strings.Fields(sc.Text())
		n, _ := strconv.ParseUint(f[0], 10, 8)
		_ = n
		b, _ := hex.DecodeString(strings.TrimPrefix(f[1], "-"))
		{outs}, ok := fn({args})
		if ok {{
			fmt.Fprintln(w, {outs})
		}} else {{
			fmt.Fprintln(w, "null")
		}}
	}}
}}

func bench(path, reps string) {{
	data, err := os.ReadFile(path)
	if err != nil {{
		panic(err)
	}}
	count := int(binary.LittleEndian.Uint64(data))
	off := 8
	var ns []uint64
	if {has_n} {{
		ns = make([]uint64, count)
		for i := range ns {{
			ns[i] = binary.LittleEndian.Uint64(data[off:])
			off += 8
		}}
	}}
	lens := make([]int, count)
	for i := range lens {{
		lens[i] = int(binary.LittleEndian.Uint64(data[off:]))
		off += 8
	}}
	bufs := make([][]byte, count)
	for i := range bufs {{
		bufs[i] = data[off+i*{m} : off+i*{m}+lens[i]]
	}}
	r, _ := strconv.Atoi(reps)
	samples := make([]float64, r)
	var sink uint64
	for k := 0; k < r; k++ {{
		var acc uint64
		t0 := time.Now()
		for i := 0; i < count; i++ {{
			b := bufs[i]
			n := uint64(0)
			if {has_n} {{
				n = ns[i]
			}}
			_ = n
			o0, {rest}ok := fn({args})
			if ok {{
				acc += uint64({o0num})
			}}
		}}
		samples[k] = float64(time.Since(t0).Nanoseconds()) / float64(count)
		sink += acc
	}}
	sort.Float64s(samples)
	fmt.Printf("{{\\"mediana\\": %.4f, \\"min\\": %.4f, \\"max\\": %.4f, \\"sink\\": %d}}\\n", samples[r/2], samples[0], samples[r-1], sink%2)
}}
"""


def go_part(d, name, gofunc, spec, comp, out):
    src = CORPUS / d / "impl.go"
    gdir = out / "go"
    shutil.rmtree(gdir, ignore_errors=True)
    (gdir / "corpus").mkdir(parents=True)
    shutil.copy(src, gdir / "corpus" / "impl.go")
    k = len(comp.output[1])
    outs = ", ".join(f"o{i}" for i in range(k))
    has_n = name == "hpack-int-decode"
    args = "uint8(n), b" if has_n else "b"
    o0num = "o0"
    (gdir / "corpus" / "main_gen.go").write_text(GO_MAIN.format(
        func=gofunc, outs=outs, args=args, has_n="true" if has_n else "false",
        m=comp.inputs[-1][1][1], rest="".join(f"_, " for _ in range(k - 1)), o0num=o0num))
    (gdir / "go.mod").write_text("module exp005\n\ngo 1.26\n")
    (gdir / "main.go").write_text('package main\n\nimport "exp005/corpus"\n\nfunc main() { corpus.Main() }\n')
    subprocess.run(["go", "build", "-o", "runner", "."], cwd=gdir, check=True, capture_output=True)
    runner = [str(gdir / "runner")]
    return {"vectores_fallidos": external_vectors(name, runner, gdir),
            "diferencial": external_differential(comp, spec, runner, gdir),
            "lineas": code_lines(src.read_text(), "//")}, gdir / "runner"


# --- Medición ------------------------------------------------------------------

def measure(d, spec, comp, out, lang_body, lang_fname, c_fname, rust_fname, rust_static, go_runner):
    fspec = backend_c.function_name(comp.name)
    unit = backend_c.emit_unit([(comp, comp.semantics, fspec), (comp, lang_body, lang_fname)])
    names = [fspec, lang_fname, c_fname, rust_fname]
    mdir = out / "medicion"
    mdir.mkdir(exist_ok=True)
    results, _ = native.benchmark(mdir, comp, spec, unit, names, CORPUS / d / "baseline.c",
                                  extra_objects=[rust_static], link_flags=RUST_LINK)
    labels = {fspec: "especificacion", lang_fname: "efch_lang", c_fname: "c_a_mano", rust_fname: "rust"}
    res = {labels[f]: r for f, r in results.items()}
    res["go"] = {}
    seeds, _, _ = workload.parse(comp, spec)
    for seed in seeds:
        proc = subprocess.run([str(go_runner), "bench", str(mdir / f"carga-{seed}.bin"), "15"],
                              capture_output=True, text=True, check=True)
        r = json.loads(proc.stdout)
        res["go"][str(seed)] = {k: round(r[k], 3) for k in ("mediana", "min", "max")}
    return res


def mean_median(per_seed):
    return round(statistics.mean(v["mediana"] for v in per_seed.values()), 3)


# --- Orquestación --------------------------------------------------------------

def run_function(d, name, gofunc, out_root):
    out = out_root / d
    out.mkdir(parents=True, exist_ok=True)
    spec = load_spec(d)
    comp = spec.computations[name]
    row = {"computacion": name, "fuente": vectors()[name]["fuente"]}
    row["efch"], body, lang_fname = efch_part(d, name, spec, comp, out)
    row["c"], c_fname = c_part(d, name, spec, comp, out)
    row["rust_kani"], rust_fname, rust_static = rust_part(d, name, spec, comp, out)
    row["dafny"] = dafny_part(d, name, spec, comp, out)
    row["go"], go_runner = go_part(d, name, gofunc, spec, comp, out)
    row["medicion_ns_op"] = measure(d, spec, comp, out, body, lang_fname, c_fname, rust_fname, rust_static, go_runner)
    row["ns_op"] = {k: mean_median(v) for k, v in row["medicion_ns_op"].items()}
    for f in (rust_static, out / f"lib{d}-rust.so"):  # binarios reproducibles: no se guardan
        f.unlink(missing_ok=True)
    return row


def geomean(xs):
    xs = list(xs)
    p = 1.0
    for x in xs:
        p *= x
    return p ** (1 / len(xs)) if xs else None


def criteria(rows):
    n = len(FUNCTIONS)
    ok = lambda r, k: r[k]["verificacion"]["estado"] == "probado"
    covered = [r for r in rows.values() if r.get("efch")]
    v1 = len(covered)
    v2 = sum(1 for r in covered if ok(r, "efch"))
    ratios = {d: r["ns_op"]["efch_lang"] / r["ns_op"]["c_a_mano"] for d, r in rows.items() if "ns_op" in r}
    v3 = {"media_geometrica": geomean(ratios.values()), "maximo": max(ratios.values()),
          "por_funcion": ratios}
    v3["cumple"] = v3["media_geometrica"] <= 1.10 and v3["maximo"] <= 1.25
    v4 = {}
    for comp_key in ("rust_kani", "dafny"):
        effort = geomean(r["efch"]["lineas"]["total"] / r[comp_key]["lineas"] for r in rows.values())
        only_efch = [d for d, r in rows.items() if ok(r, "efch") and not ok(r, comp_key)]
        faster = [d for d, r in rows.items() if ok(r, "efch") and ok(r, comp_key)
                  and r["efch"]["verificacion"]["segundos"] <= 0.5 * r[comp_key]["verificacion"]["segundos"]]
        v4[comp_key] = {"a_esfuerzo_relativo": effort, "a": effort <= 0.80,
                        "b_solo_efch": only_efch, "b": len(only_efch) >= 2,
                        "c_mas_rapido_x2": faster, "c": len(faster) >= 6}
        v4[comp_key]["cumple"] = v4[comp_key]["a"] or v4[comp_key]["b"] or v4[comp_key]["c"]
    res = {"V1": {"valor": f"{v1}/{n}", "cumple": v1 >= 6}, "V2": {"valor": f"{v2}/{n}", "cumple": v2 >= 6},
           "V3": v3, "V4": {**v4, "cumple": all(v["cumple"] for v in v4.values())}}
    # Condición previa (revisión de Codex, hallazgo 7): ningún fallo de corrección experimental.
    bad = {d: k for d, r in rows.items() for k in ("efch", "c", "rust_kani", "dafny", "go")
           if r[k]["vectores_fallidos"] or r[k]["diferencial"]["fallos"]}
    res["integridad"] = {"fallos": bad, "cumple": not bad}
    # Sensibilidad (no entra en la decisión registrada): variantes «solo especificación».
    res["sensibilidad_solo_especificacion"] = {
        "esfuerzo_efch_spec_frente_a_dafny_spec": geomean(r["efch"]["solo_especificacion"]["lineas"]
                                                          / r["dafny"]["solo_especificacion"]["lineas"] for r in rows.values()),
        "esfuerzo_efch_completo_frente_a_dafny_spec": geomean(r["efch"]["lineas"]["total"]
                                                              / r["dafny"]["solo_especificacion"]["lineas"] for r in rows.values()),
        "segundos_totales": {"efch_programa": sum(r["efch"]["verificacion"]["segundos"] for r in rows.values()),
                             "efch_solo_spec": sum(r["efch"]["solo_especificacion"]["segundos"] for r in rows.values()),
                             "dafny": sum(r["dafny"]["verificacion"]["segundos"] for r in rows.values()),
                             "dafny_solo_spec": sum(r["dafny"]["solo_especificacion"]["segundos"] for r in rows.values()),
                             "kani": sum(r["rust_kani"]["verificacion"]["segundos"] for r in rows.values())}}
    if not bad and res["V1"]["cumple"] and res["V2"]["cumple"] and res["V4"]["cumple"]:
        res["decision"] = "viable" if v3["cumple"] else "viable con deuda"
    else:
        res["decision"] = "no viable"
    return res


def report_md(ev):
    rows, c = ev["funciones"], ev["criterios"]
    L = ["# EXP-005: EFCH Lang frente a Rust + Kani, Dafny, C y Go", "",
         f"Fecha: {ev['fecha']}. {ev['entorno']['cpu']}; gcc {ev['entorno']['gcc']} `{' '.join(CFLAGS)}`; "
         f"{ev['entorno']['rustc']}; {ev['entorno']['go']}; Dafny {ev['entorno']['dafny']}; Kani {ev['entorno']['kani']}.", "",
         "## Verificación (segundos de reloj, con arranque de cada herramienta)", "",
         "| Función | EFCH | Kani | Dafny (anotaciones) |", "|---|---|---|---|"]
    for d, r in rows.items():
        e, k, f = r["efch"]["verificacion"], r["rust_kani"]["verificacion"], r["dafny"]["verificacion"]
        L.append(f"| {d} | {e['estado']} ({e['herramienta']}) {e['segundos']} | {k['estado']} {k['segundos']} | "
                 f"{f['estado']} {f['segundos']} ({r['dafny']['anotaciones']}) |")
    L += ["", "## Esfuerzo (líneas escritas a mano para obtener la garantía; C y Go no la tienen)", "",
          "| Función | EFCH (espec. + programa) | Rust + Kani | Dafny | C | Go |", "|---|---|---|---|---|---|"]
    for d, r in rows.items():
        el = r["efch"]["lineas"]
        L.append(f"| {d} | {el['total']} ({el['especificacion']} + {el['programa']}) | {r['rust_kani']['lineas']} | "
                 f"{r['dafny']['lineas']} | {r['c']['lineas']} | {r['go']['lineas']} |")
    L += ["", "## Variantes «solo especificación» (sensibilidad; no entra en la decisión)", "",
          "| Función | EFCH espec. (líneas, s) | Dafny Spec + `return Spec(...)` (líneas, s) |", "|---|---|---|"]
    for d, r in rows.items():
        e, f = r["efch"]["solo_especificacion"], r["dafny"]["solo_especificacion"]
        L.append(f"| {d} | {e['lineas']}, {e['segundos']} ({e['estado']}) | {f['lineas']}, {f['segundos']} ({f['estado']}) |")
    L += ["", "## Rendimiento (ns/op, media de las medianas por semilla)", "",
          "| Función | EFCH Lang | C a mano | Rust | Go | C de la especificación |", "|---|---|---|---|---|---|"]
    for d, r in rows.items():
        n = r["ns_op"]
        L.append(f"| {d} | {n['efch_lang']} | {n['c_a_mano']} | {n['rust']} | {n['go']} | {n['especificacion']} |")
    L += ["", "## Corrección experimental (fallos en vectores / pruebas diferenciales)", "",
          "| Función | EFCH | C | Rust | Dafny | Go |", "|---|---|---|---|---|---|"]
    for d, r in rows.items():
        cell = lambda k: f"{len(r[k]['vectores_fallidos'])} / {r[k]['diferencial']['fallos']} de {r[k]['diferencial']['casos']}"
        L.append(f"| {d} | {cell('efch')} | {cell('c')} | {cell('rust_kani')} | {cell('dafny')} | {cell('go')} |")
    L += ["", "## Criterios registrados", "", "```json", json.dumps(c, ensure_ascii=False, indent=2), "```"]
    return "\n".join(L) + "\n"


def tool_version(cmd, env=None):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, env=env).stdout.strip().splitlines()[0]
    except Exception:
        return None


def cmd_todo(args):
    native.set_optimization(CFLAGS)
    out = (ROOT / args.salida).resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "PATH": f"{KANI_PATH}:{os.environ['PATH']}"}
    ev = {"fecha": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
          "entorno": {"cpu": next((l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo")
                                   if l.startswith("model name")), "?"),
                      "gcc": native.compiler_version(), "python": platform.python_version(),
                      "rustc": tool_version(["rustc", "--version"]), "go": tool_version(["go", "version"]),
                      "dafny": tool_version([str(DAFNY), "--version"]), "kani": tool_version(["kani", "--version"], env),
                      "cbmc": cbmc.version() if cbmc.CBMC.exists() else None},
          "funciones": {}}
    import hashlib
    files = sorted(list((ROOT / "efch").glob("*.py")) + [p for p in CORPUS.rglob("*") if p.is_file()]
                   + [pathlib.Path(__file__)])
    ev["huellas_sha256"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    from efch._z3 import z3 as _z3mod
    ev["entorno"]["z3"] = _z3mod.get_version_string()
    only = set(args.solo.split(",")) if args.solo else None
    for d, name, gofunc in FUNCTIONS:
        if only and d not in only:
            continue
        print(f"== {d}", flush=True)
        ev["funciones"][d] = run_function(d, name, gofunc, out)
        r = ev["funciones"][d]
        print(json.dumps({"efch": r["efch"]["verificacion"], "kani": r["rust_kani"]["verificacion"],
                          "dafny": r["dafny"]["verificacion"], "ns_op": r["ns_op"]}, ensure_ascii=False), flush=True)
        (out / "evidencia.json").write_text(json.dumps(ev, ensure_ascii=False, indent=2, default=str))
    if not only:
        ev["criterios"] = criteria(ev["funciones"])
        (out / "evidencia.json").write_text(json.dumps(ev, ensure_ascii=False, indent=2, default=str))
        (out / "informe.md").write_text(report_md(ev))
        print(report_md(ev))
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("orden", choices=["vectores", "todo"])
    ap.add_argument("--salida", default="resultados/exp-005")
    ap.add_argument("--solo", help="funciones separadas por comas (prueba del script; no calcula criterios)")
    args = ap.parse_args()
    return {"vectores": cmd_vectores, "todo": cmd_todo}[args.orden](args)


if __name__ == "__main__":
    sys.exit(main())
