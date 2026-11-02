"""
EXP-005, sensibilidad (revisión de Codex, hallazgo 5): rendimiento de las especificaciones
ejecutables.

    python3 experimentos/exp005_dafny_rendimiento.py --salida resultados/exp-005-sensibilidad

Para cada función del corpus mide, sobre las mismas cargas de EXP-005:
- la especificación Dafny ejecutable («método que devuelve Spec(...)», sin invariantes),
  compilada con `dafny translate go` y medida con un bucle en Go (las secuencias se construyen
  fuera del bucle, lo que favorece a Dafny);
- el C que la ruta ordinaria de EFCH genera de la propia especificación (`-O3 -march=native`),
  medido con el arnés en C de EXP-004.
"""

import argparse
import json
import os
import pathlib
import re
import shutil
import statistics
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "experimentos"))

import exp005 as E  # noqa: E402
from efch import backend_c, native, workload  # noqa: E402

GO_BENCH = """package main

import (
	"encoding/binary"
	"fmt"
	"os"
	"sort"
	"strconv"
	"time"

	_dafny "dafny"
	m "m"
)

func main() {
	data, err := os.ReadFile(os.Args[1])
	if err != nil {
		panic(err)
	}
	reps, _ := strconv.Atoi(os.Args[2])
	count := int(binary.LittleEndian.Uint64(data))
	off := 8
	ns := make([]uint64, count)
	if HAS_N {
		for i := range ns {
			ns[i] = binary.LittleEndian.Uint64(data[off:])
			off += 8
		}
	}
	lens := make([]int, count)
	for i := range lens {
		lens[i] = int(binary.LittleEndian.Uint64(data[off:]))
		off += 8
	}
	seqs := make([]_dafny.Sequence, count)
	nint := make([]_dafny.Int, count)
	for i := range seqs {
		seqs[i] = _dafny.SeqOfBytes(data[off+i*M : off+i*M+lens[i]])
		nint[i] = _dafny.IntOfUint64(ns[i])
	}
	samples := make([]float64, reps)
	var sink uint64
	for k := 0; k < reps; k++ {
		var acc uint64
		t0 := time.Now()
		for i := 0; i < count; i++ {
			_ = nint[i]
			r := m.Companion_Default___.METHOD(ARGS)
			if r.Is_Some() {
				acc++
			}
		}
		samples[k] = float64(time.Since(t0).Nanoseconds()) / float64(count)
		sink += acc
	}
	sort.Float64s(samples)
	fmt.Printf("{\\"mediana\\": %.4f, \\"min\\": %.4f, \\"max\\": %.4f, \\"sink\\": %d}\\n", samples[reps/2], samples[0], samples[reps-1], sink%2)
}
"""


def dafny_go(d, name, spec_only_dfy, out, carga_files):
    """Compila la especificación Dafny a Go y la mide sobre cada fichero de carga."""
    gdir = out / f"{d}-dafny-go"
    shutil.rmtree(gdir, ignore_errors=True)
    gdir.mkdir(parents=True)
    # Sin goimports, Dafny termina con código 3 tras generar el código (solo falla el formato).
    subprocess.run([str(E.DAFNY), "translate", "go", str(spec_only_dfy), "--no-verify", "--include-runtime",
                    "-o", str(gdir / "t")], capture_output=True)
    src = gdir / "t-go" / "src"
    if not list(src.glob("*.go")):
        raise RuntimeError(f"dafny translate go no generó código para {d}")
    gen = next(p for p in src.glob("*.go"))
    (src / "m").mkdir()
    gen.rename(src / "m" / "m.go")
    text = (src / "m" / "m.go").read_text()
    method = re.search(r"func \(_static \*CompanionStruct_Default___\) (Decode|Check)\(", text).group(1)
    has_n = name == "hpack-int-decode"
    comp = E.load_spec(d.split("-")[0]).computations[name]
    (src / "bench").mkdir()
    (src / "bench" / "main.go").write_text(
        GO_BENCH.replace("HAS_N", "true" if has_n else "false").replace("METHOD", method)
        .replace("ARGS", "nint[i], seqs[i]" if has_n else "seqs[i]").replace("M ", f"{comp.inputs[-1][1][1]} ")
        .replace("*M", f"*{comp.inputs[-1][1][1]}"))
    env = {**os.environ, "GO111MODULE": "off", "GOPATH": str(gdir / "t-go")}
    subprocess.run(["go", "build", "-o", str(gdir / "bench"), "bench"], cwd=src, env=env, check=True,
                   capture_output=True)
    res = {}
    for seed, path in carga_files.items():
        proc = subprocess.run([str(gdir / "bench"), str(path), "15"], capture_output=True, text=True, check=True)
        r = json.loads(proc.stdout)
        res[seed] = {k: round(r[k], 3) for k in ("mediana", "min", "max")}
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--salida", default="resultados/exp-005-sensibilidad")
    args = ap.parse_args()
    native.set_optimization(E.CFLAGS)
    out = (ROOT / args.salida).resolve()
    out.mkdir(parents=True, exist_ok=True)
    rows = {}
    for d, name, _ in E.FUNCTIONS:
        spec_def = E.load_spec(d)
        comp = spec_def.computations[name]
        mdir = out / f"{d}-c-espec"
        mdir.mkdir(exist_ok=True)
        fspec = backend_c.function_name(comp.name)
        c_res, _ = native.benchmark(mdir, comp, spec_def, backend_c.emit_unit([(comp, comp.semantics, fspec)]),
                                    [fspec])
        seeds, _, _ = workload.parse(comp, spec_def)
        cargas = {str(s): mdir / f"carga-{s}.bin" for s in seeds}
        dfy = out / f"{d}-dafny-solo-spec.dfy"
        go_res = dafny_go(d, name, dfy, out, cargas)
        mean = lambda r: statistics.mean(v["mediana"] for v in r.values())
        rows[d] = {"c_de_la_especificacion_efch": c_res[fspec], "dafny_especificacion_go": go_res,
                   "ns_op": {"efch_espec_c": round(mean(c_res[fspec]), 3), "dafny_espec_go": round(mean(go_res), 3)}}
        rows[d]["ns_op"]["cociente_dafny_efch"] = round(rows[d]["ns_op"]["dafny_espec_go"] / rows[d]["ns_op"]["efch_espec_c"], 2)
        print(d, json.dumps(rows[d]["ns_op"]), flush=True)
        shutil.rmtree(out / f"{d}-dafny-go", ignore_errors=True)
    ratios = [r["ns_op"]["cociente_dafny_efch"] for r in rows.values()]
    summary = {"media_geometrica_dafny_sobre_efch": round(E.geomean(ratios), 2), "min": min(ratios), "max": max(ratios)}
    print(json.dumps(summary))
    (out / "rendimiento-especificaciones.json").write_text(json.dumps(
        {"entorno": {"dafny": E.tool_version([str(E.DAFNY), "--version"]), "go": E.tool_version(["go", "version"]),
                     "gcc": native.compiler_version(), "cflags": E.CFLAGS,
                     "nota": "medido con la fase 3 de EXP-003 en marcha (máquina con carga)"},
         "funciones": rows, "resumen": summary}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
