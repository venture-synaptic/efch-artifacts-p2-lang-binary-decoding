"""
Interfaz de línea de órdenes de EFCH.

    python3 -m efch check  DEF.efch
    python3 -m efch eval   DEF.efch COMP ARG...          (bytes como b:ac02, enteros en decimal o 0x..)
    python3 -m efch verify DEF.efch CANDIDATAS.efch
    python3 -m efch build  DEF.efch COMP [--candidata F] [-o salida.c]
    python3 -m efch synth  DEF.efch COMP [--sin-llm] [--linajes N] [--rondas N] [--candidata F ...] [-o DIR]
    python3 -m efch store [--almacen DIR] register DEF.efch COMP     primera revisión
    python3 -m efch store [--almacen DIR] realize  DEF.efch CANDIDATAS.efch
    python3 -m efch store [--almacen DIR] evolve   DEF.efch COMP     nueva revisión y sus consecuencias
    python3 -m efch store [--almacen DIR] status
    python3 -m efch lang core   PROG.efl                       traducción al núcleo
    python3 -m efch lang build  PROG.efl [-o salida.c]         ruta ordinaria (sin LLM)
    python3 -m efch lang verify PROG.efl ESPEC.efch [--emitir DIR]   ruta de investigación
    python3 -m efch export check DEF.efch | lang PROG.efl ESPEC.efch [-o evidencia.json]   contrato efch-evidencia/1.0

Código de salida: 0 si todo lo comprobado está probado, 1 si algo quedó
refutado o desconocido, 2 ante errores de uso o de la definición.
"""

import argparse
import json
import pathlib
import sys
import threading
import time

from . import backend_c, core, interp, lang, native, pipeline


def _load(path):
    text = pathlib.Path(path).read_text()
    return core.load_definition(text, str(path)), text


def _status_line(label, status, detail=""):
    mark = {"probado": "✓", "refutado": "✗", "desconocido": "?"}.get(status, "·")
    return f"  {mark} {status:<12} {label}" + (f" — {detail}" if detail else "")


def cmd_check(args):
    defn, _ = _load(args.definicion)
    report = pipeline.check_definition(defn, args.smt_segundos)
    ok = True
    for name, info in report["computaciones"].items():
        print(f"{name}  {info['firma']}")
        print(f"  identidad {info['identidad']}  ({info['nodos']} nodos)")
        r = info["bien_definida"]
        print(_status_line(r["obligacion"], r["estado"], r["detalle"]))
        ok &= r["estado"] == "probado"
        for inv in info.get("invariantes", []):
            print(_status_line(inv["obligacion"], inv["estado"], inv["detalle"]))
            ok &= inv["estado"] == "probado"
    for p in report["propiedades"]:
        detail = p["detalle"] + (f" contraejemplo {json.dumps(p['contraejemplo'])}" if p["contraejemplo"] else "")
        print(_status_line(f"propiedad {p['nombre']} ({p['segundos']} s)", p["estado"], detail))
        ok &= p["estado"] == "probado"
    if args.json:
        pathlib.Path(args.json).write_text(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if ok else 1


def _parse_arg(text, ty):
    if ty[0] == "bytes":
        if not text.startswith("b:"):
            raise SystemExit(f"los bytes se escriben como b:HEX, no {text!r}")
        return tuple(bytes.fromhex(text[2:]))
    if ty[0] == "bool":
        return text in ("true", "1")
    return int(text, 0)


def cmd_eval(args):
    defn, _ = _load(args.definicion)
    comp = defn.computations[args.computacion]
    values = [_parse_arg(a, t) for a, (_, t) in zip(args.argumentos, comp.inputs)]
    try:
        r = interp.run(comp, comp.inputs, values)
    except interp.Undefined as e:
        print(f"indefinido: {e}")
        return 1
    print(f"b:{bytes(r).hex()}" if isinstance(r, tuple) and comp.output[0] == "bytes" else r)
    return 0


def cmd_verify(args):
    defn, _ = _load(args.definicion)
    text = pathlib.Path(args.candidatas).read_text()
    ok = True
    for cand in core.load_candidates(text, defn, args.candidatas):
        comp = defn.computations[cand.implements]
        print(f"{cand.name} implementa {comp.name}  (identidad {cand.identity(comp)[:16]}…)")
        v = pipeline.verify_candidate(comp, cand.body, args.smt_segundos or comp.budget["smt-seconds"])
        for o in v["obligaciones"]:
            detail = o["detalle"] + (f" contraejemplo {json.dumps(o['contraejemplo'])}" if o["contraejemplo"] else "")
            print(_status_line(f"{o['obligacion']} ({o['segundos']} s)", o["estado"], detail))
        ok &= v["estado"] == "probado"
    return 0 if ok else 1


def cmd_build(args):
    defn, _ = _load(args.definicion)
    comp = defn.computations[args.computacion]
    body = comp.semantics
    if args.candidata:
        cands = [c for c in core.load_candidates(pathlib.Path(args.candidata).read_text(), defn)
                 if c.implements == comp.name]
        if not cands:
            raise SystemExit(f"{args.candidata} no contiene candidatas para {comp.name}")
        v = pipeline.verify_candidate(comp, cands[0].body, comp.budget["smt-seconds"])
        if v["estado"] != "probado":
            print(f"la candidata no está probada ({v['estado']}): no se materializa", file=sys.stderr)
            return 1
        body = cands[0].body
    unit = backend_c.emit_unit([(comp, body, args.funcion or backend_c.function_name(comp.name))])
    if args.salida:
        pathlib.Path(args.salida).write_text(unit)
        print(f"escrito {args.salida}")
    else:
        print(unit)
    return 0


def cmd_synth(args):
    defn, text = _load(args.definicion)
    out = pathlib.Path(args.salida or f"resultados/{args.computacion}-{time.strftime('%Y%m%dT%H%M%S')}")
    if args.cflags:
        native.set_optimization(args.cflags.split())
    ev = pipeline.synthesize(defn, text, args.computacion, out, use_llm=not args.sin_llm,
                             lineages=args.linajes, rounds=args.rondas, extra=args.candidata or ())
    print()
    print(pipeline.report_markdown(ev))
    print(f"Evidencia en {out}/")
    return 0 if ev["seleccion"] else 1


def cmd_store(args):
    from . import store as st
    s = st.Store(args.almacen)
    if args.accion == "status":
        for name, info in s.names.items():
            print(f"{name}: vigente {(info['vigente'] or 'ninguna')[:16]}")
            for e in info["historial"]:
                mark = "✓" if e["aceptada"] else "✗"
                rel = e.get("relacion_con_padre") or "inicial"
                print(f"  {mark} {(e.get('identidad') or e['definicion'])[:16]}  {rel:<17} {e.get('nota', '')}")
        # Vigencia en la instantánea actual (contrato v2.5; se calcula, no se guarda).
        v = s.vigencia()
        print(f"instantánea {v['instantanea'][:16]}")
        if s.descartados:
            print(f"  objetos descartados por no ser válidos: {len(s.descartados)}")
        for x in v["afirmaciones"]:
            suj = ", ".join(f"{p}={t.rsplit(':', 1)[0]}" for p, t in sorted(x["sujetos"].items()))
            print(f"  {x['clase']:<6} {suj:<52} {x['estado']}" + (f" ({x['regla']})" if x["regla"] else ""))
        for x in v["obsoletas"]:
            suj = ", ".join(f"{p}={t}" for p, t in sorted(x["sujetos"].items()))
            print(f"  no vigente: {x['clase']} {suj} ({x['estado']} para esa revisión)")
        for x in v["indeterminadas"]:
            print(f"  indeterminada: {x}")
        return 0
    defn, text = _load(args.definicion)
    if args.accion == "register":
        r = st.register(s, defn, text, args.objetivo, note=args.definicion)
        print(f"{'aceptada' if r['aceptada'] else 'NO aceptada'}: {r['identidad'][:16]}")
        for p in r["propiedades"]:
            print(_status_line(f"propiedad {p['nombre']}", p["estado"], p["detalle"]))
        return 0 if r["aceptada"] else 1
    if args.accion == "realize":
        ok = True
        for cand in st.candidatas_unicas(defn, core.load_candidates(pathlib.Path(args.objetivo).read_text(), defn,
                                                                     args.objetivo)):
            rid, v = st.realize(s, defn, cand, defn_text=text)
            print(_status_line(f"{cand.name} realiza {cand.implements}", v["estado"]))
            ok &= v["estado"] == "probado"
        return 0 if ok else 1
    r = st.evolve(s, defn, text, args.objetivo, note=args.definicion)
    print(f"revisión {r['identidad'][:16]}: {r['relacion']} respecto a {r.get('anterior', '')[:16]}")
    if r.get("testigo"):
        print(f"  testigo de cambio de comportamiento: {json.dumps(r['testigo'])}")
    if r.get("equivalente_en_historial"):
        print(f"  equivalente a la revisión anterior {r['equivalente_en_historial'][:16]}")
    for row in r["realizaciones"]:
        ce = f" contraejemplo {json.dumps(row['contraejemplo'])}" if row.get("contraejemplo") else ""
        print(_status_line(f"{row['nombre']} ({row['via']})", row["estado"], ce.strip()))
    for p in r["propiedades"]:
        print(_status_line(f"propiedad {p['nombre']}", p["estado"], p["detalle"]))
    if r["propiedades_retiradas"]:
        print(f"  propiedades retiradas: {', '.join(r['propiedades_retiradas'])}")
    for x in r.get("obsoletas", []):
        print(f"  obsoleta en la instantánea nueva: {x['clase']} " + ", ".join(sorted(x["sujetos"].values())))
    for x in r.get("pendientes", []):
        print(f"  no comprobado en la instantánea nueva: {x['clase']} " + ", ".join(sorted(x["sujetos"].values())))
    print("ACEPTADA" if r["aceptada"] else f"RECHAZADA: {r['motivo_rechazo']}")
    return 0 if r["aceptada"] else 1


def cmd_lang(args):
    text = pathlib.Path(args.programa).read_text()
    core_text = lang.core_definition_text(text, args.programa)
    if args.accion == "core":
        print(core_text, end="")
        return 0
    if args.accion == "build":
        # Ruta ordinaria: núcleo → buena definición → C. Sin LLM ni búsqueda.
        defn = core.load_definition(core_text, args.programa)
        report = pipeline.check_definition(defn, args.smt_segundos)
        ok = True
        for name, info in report["computaciones"].items():
            r = info["bien_definida"]
            if r["estado"] != "probado":
                ok = False
                ce = f" contraejemplo {json.dumps(r['contraejemplo'])}" if r.get("contraejemplo") else ""
                print(f"error: {name}: {r['estado']} — {r['detalle']}{ce}", file=sys.stderr)
        if not ok:
            return 1
        unit = backend_c.emit_unit([(c, c.semantics, backend_c.function_name(c.name))
                                    for c in defn.computations.values()])
        if args.salida:
            pathlib.Path(args.salida).write_text(unit)
            print(f"escrito {args.salida}")
        else:
            print(unit)
        return 0
    if not args.especificacion:
        raise SystemExit("lang verify necesita la especificación: efch lang verify PROG.efl ESPEC.efch")
    spec, _ = _load(args.especificacion)
    cands_text = lang.candidates_text(text, spec, args.programa)
    if args.emitir:
        out = pathlib.Path(args.emitir)
        out.mkdir(parents=True, exist_ok=True)
        stem = pathlib.Path(args.programa).stem
        (out / f"{stem}.nucleo.efch").write_text(core_text)
        (out / f"{stem}.candidatas.efch").write_text(cands_text)
        print(f"núcleo y candidatas en {out}/")
    ok = True
    for cand, comp, obligations, status in lang.verify(text, spec, args.programa, args.smt_segundos):
        print(f"{cand.name} implementa {comp.name}  (identidad {cand.identity(comp)[:16]}…)")
        for o in obligations:
            detail = o["detalle"] + (f" contraejemplo {json.dumps(o['contraejemplo'])}" if o["contraejemplo"] else "")
            print(_status_line(f"{o['obligacion']} ({o['segundos']} s)", o["estado"], detail))
        print(f"  ⇒ {status}")
        ok &= status == "probado"
    return 0 if ok else 1


def cmd_export(args):
    from . import evidencia
    if args.modo == "check":
        doc = evidencia.from_check(args.archivos[0], args.smt_segundos)
    else:
        if len(args.archivos) != 2:
            raise SystemExit("export lang necesita PROG.efl ESPEC.efch")
        doc = evidencia.from_lang(args.archivos[0], args.archivos[1], args.smt_segundos)
    text = json.dumps(doc, ensure_ascii=False, indent=2) + "\n"
    if args.salida:
        pathlib.Path(args.salida).write_text(text)
        print(f"escrito {args.salida}  (veredicto {doc['veredicto']})")
    else:
        print(text, end="")
    return 0 if doc["veredicto"] == "probado" else 1


def main(argv=None):
    ap = argparse.ArgumentParser(prog="efch", description="EFCH: sistema de computación sintética verificable")
    sub = ap.add_subparsers(dest="orden", required=True)

    p = sub.add_parser("check", help="comprueba una definición y demuestra sus obligaciones")
    p.add_argument("definicion")
    p.add_argument("--smt-segundos", type=float)
    p.add_argument("--json", help="guarda el informe en este archivo")
    p.set_defaults(fn=cmd_check)

    p = sub.add_parser("export", help="evidencia con el contrato efch-evidencia/1.0 (contracts/evidencia/1.0)")
    p.add_argument("modo", choices=["check", "lang"])
    p.add_argument("archivos", nargs="+", help="DEF.efch (check) o PROG.efl ESPEC.efch (lang)")
    p.add_argument("-o", "--salida")
    p.add_argument("--smt-segundos", type=float)
    p.set_defaults(fn=cmd_export)

    p = sub.add_parser("eval", help="evalúa la semántica con el intérprete")
    p.add_argument("definicion")
    p.add_argument("computacion")
    p.add_argument("argumentos", nargs="*")
    p.set_defaults(fn=cmd_eval)

    p = sub.add_parser("verify", help="verifica candidatas frente a la semántica")
    p.add_argument("definicion")
    p.add_argument("candidatas")
    p.add_argument("--smt-segundos", type=float)
    p.set_defaults(fn=cmd_verify)

    p = sub.add_parser("build", help="materializa en C la semántica o una candidata probada")
    p.add_argument("definicion")
    p.add_argument("computacion")
    p.add_argument("--candidata")
    p.add_argument("--funcion", help="nombre de la función C (por defecto efch_<computación>)")
    p.add_argument("-o", "--salida")
    p.set_defaults(fn=cmd_build)

    p = sub.add_parser("synth", help="canalización completa con evidencia")
    p.add_argument("definicion")
    p.add_argument("computacion")
    p.add_argument("--sin-llm", action="store_true", help="solo semántica directa y candidatas dadas")
    p.add_argument("--linajes", type=int, default=2)
    p.add_argument("--rondas", type=int, default=2)
    p.add_argument("--candidata", action="append", help="archivo de candidatas adicional (repetible)")
    p.add_argument("--cflags", help='opciones de optimización de gcc para todas las funciones, p. ej. "-O3 -march=native"')
    p.add_argument("-o", "--salida")
    p.set_defaults(fn=cmd_synth)

    p = sub.add_parser("store", help="registro semántico: revisiones, realizaciones y evolución")
    p.add_argument("--almacen", default=".efch-almacen")
    p.add_argument("accion", choices=["register", "realize", "evolve", "status"])
    p.add_argument("definicion", nargs="?")
    p.add_argument("objetivo", nargs="?", help="computación (register, evolve) o archivo de candidatas (realize)")
    p.set_defaults(fn=cmd_store)

    p = sub.add_parser("lang", help="EFCH Lang: traducción al núcleo, ruta ordinaria y verificación")
    p.add_argument("accion", choices=["core", "build", "verify"])
    p.add_argument("programa")
    p.add_argument("especificacion", nargs="?", help="definición .efch (solo verify)")
    p.add_argument("-o", "--salida")
    p.add_argument("--emitir", help="directorio donde guardar el núcleo y las candidatas (verify)")
    p.add_argument("--smt-segundos", type=float)
    p.set_defaults(fn=cmd_lang)

    args = ap.parse_args(argv)
    try:
        return args.fn(args)
    except core.EFCHError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    except RecursionError:
        print(f"error: anidamiento demasiado profundo (límite de recursión {sys.getrecursionlimit()})", file=sys.stderr)
        return 2


# El traductor de EFCH Lang y los recorridos del núcleo son recursivos: un bucle desenrollado de 64 vueltas con
# guardas supera los 1 000 marcos por defecto (EXP-008). La CLI corre en un hilo con pila propia.
PILA_BYTES = 512 * 1024 * 1024
LIMITE_RECURSION = 200_000


def main_con_pila(argv=None):
    sys.setrecursionlimit(LIMITE_RECURSION)
    threading.stack_size(PILA_BYTES)
    box = {}

    def run():
        try:
            box["r"] = main(argv)
        except SystemExit as e:  # argparse: --help (0) y errores de uso (2) (Codex Astra, EXP-017)
            box["r"] = e.code

    t = threading.Thread(target=run)
    t.start()
    t.join()
    return box.get("r", 1)


if __name__ == "__main__":
    sys.exit(main_con_pila())
