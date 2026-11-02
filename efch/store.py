"""
Registro semántico de EFCH (manifiesto §11; EXP-002) sobre el contrato de evidencias v2.7
(especificacion/ESPECIFICACION.md). Modelo de evolución de §9 (decisiones del autor D8 y D9), con cinco cosas
separadas que el registro no confunde:

| Concepto | Dónde vive | Al evolucionar `f` |
|---|---|---|
| Definición registrada (fuente de la ranura) | `definiciones/<id>.json`; vigente en `nombres.json`, `propiedades.json`, `realizaciones.json` | Solo cambia la de `f` |
| Dependencias efectivas | `revision.dependencias` en la instantánea | Cambian las de todo lo que expande `f` |
| Identidad | `revision.id` (y su `contenido`), elaborada desde las definiciones vigentes | Cambia la de `f` y la de su cierre inverso |
| Evidencia histórica | `objetos/<tabla>/<id>.json` (objetos del contrato, inmutables) | Nunca cambia ni se borra |
| Vigencia | `reglas.Almacen.reutilizable(cert, S)` | Se calcula; no se guarda |

- **D8.** Evolucionar `f` deja obsoleta toda evidencia cuyo cierre contenga `f` (WD, propiedades, realizaciones y
  refutaciones de `f`, de quien la llama y de las candidatas que la llaman), aunque siga siendo válida en su
  instantánea. Las propiedades afectadas se verifican directamente; el resto queda `no comprobado` (o se revalida
  directamente con `revalidar`).
- **D9.** Un cuerpo nuevo es otra revisión: la identidad de una realización es el `id` de la revisión de su ranura en
  la instantánea donde se verificó, y nunca se asocia a otra. Una hoja directa se publica solo si su
  `objeto_verificado` es el contenido del sujeto (lo comprueba `efch.reglas`). `load_realization(rid)` devuelve el
  cuerpo de esa revisión, reconstruido desde sus propias dependencias y cotejado byte a byte.
- **Reutilización solo por `efch.reglas` (§11.2).** R-REAL y R-REFUT en `evolve` se construyen con
  `reglas.r_real` / `reglas.r_refut` y se publican solo si el comprobador acepta toda la cadena.
- **D-3.** `desconocido` y lo que la clase no admite como certificado (REAL `refutado`) son registros históricos.

Cada operación exporta su paquete de intercambio (§2.3) en `pasos/<n>-<operación>.json`. Git puede guardar este
directorio, pero no es la fuente de verdad: lo son los objetos y sus enlaces.
"""

import hashlib
import json
import pathlib
import platform
import subprocess
import time

from . import core, identidad as I, interp, pipeline, reglas, sexpr, smt
from ._z3 import VERSION as Z3_VERSION
from .identidad import Rechazo

RAIZ = pathlib.Path(__file__).resolve().parent
# Qué identifica cada componente de la base de las instantáneas del registro (§3.3, §11.4; resultados/p1/bases.md).
MODULOS = {"efch-core": ["core", "sexpr"], "efch-smt": ["smt", "_z3"], "efch-interp": ["interp"],
           "efch-c": ["backend_c", "backend_campos", "cbmc", "native"], "reglas": ["reglas", "identidad"],
           "ejecutor": ["store", "pipeline"], "traductor": ["lang"]}


class IdentidadDistinta(core.EFCHError):
    """Se intentó recargar o verificar un objeto y la identidad recalculada no es la registrada (D9)."""


class RanuraRepetida(IdentidadDistinta):
    """Dos objetos de la misma entrada ocupan una ranura con revisiones distintas (K2, v2.7, §2.2)."""


class FueraDeOrden(core.EFCHError):
    """El grafo de llamadas del registro vigente o el que resultaría de la propuesta no se puede elaborar
    coherentemente; `nombres`: las computaciones implicadas. `evolve` lo rechaza en su precontrol, antes de elaborar
    ninguna instantánea: no se promueve ni se escribe nada."""

    def __init__(self, mensaje, nombres):
        super().__init__(mensaje)
        self.nombres = list(nombres)


class CicloEfectivo(FueraDeOrden):
    """Sobre un registro vigente acíclico, el grafo propuesto (vigentes + propuesta) tiene un ciclo, incluya o no a la
    computación evolucionada; `nombres`: el ciclo, en orden de llamada (desde la evolucionada si está en él)."""


class LlamadaAusente(FueraDeOrden):
    """El cierre efectivo llama a computaciones sin definición vigente ni propuesta; `nombres`: las ausentes."""


class RegistroInconsistente(FueraDeOrden):
    """El registro vigente, antes de la propuesta, no se elabora por sí mismo. `motivo`: `definicion` (una definición
    vigente falta o no es la registrada), `ciclo` (entre vigentes; `nombres`: el ciclo) o `llamada-ausente` (una vigente
    llama a una computación sin definición vigente; `nombres`: las ausentes)."""

    def __init__(self, mensaje, nombres, motivo):
        super().__init__(mensaje, nombres)
        self.motivo = motivo


def _una_por_ranura(fijar, objs):
    """Los objetos, uno por ranura (`fijar(obj)` da su revisión en una misma elaboración). Una ranura con otra
    revisión se rechaza (K2); con la misma, es un único objeto."""
    out = {}
    for x in objs:
        try:
            out.setdefault(fijar(x)["ranura"], x)
        except I.RanuraRepetida as e:
            raise RanuraRepetida(str(e)) from None
    return list(out.values())


def candidatas_unicas(defn, cands):
    """Las candidatas de una entrada (p. ej., un archivo de `store realize`), una por ranura: dos `c` de f y de g son
    dos ranuras (K1); dos `c` de f con cuerpos distintos se rechazan antes de registrar nada (K2)."""
    return _una_por_ranura(I.Formas(defn).candidata, cands)


def _huella(nombres):
    h = hashlib.sha256()
    for n in nombres:
        h.update(n.encode() + b"\0" + hashlib.sha256((RAIZ / f"{n}.py").read_bytes()).digest())
    return h.hexdigest()[:16]


_BASE_FIJA = {}


def base_registro(workload="sin-workload"):
    """Base de la instantánea del registro en este proceso: una huella por componente de §3.3."""
    if not _BASE_FIJA:
        b = {c: _huella(m) for c, m in MODULOS.items()}
        import z3
        lib = pathlib.Path(z3.__file__).parent / "lib" / "libz3.so"
        b["z3"] = f"{Z3_VERSION}:{hashlib.sha256(lib.read_bytes()).hexdigest()[:16] if lib.exists() else 'sin-libz3'}"
        cbmc = RAIZ.parent / ".vendor" / "cbmc-6.11.0" / "usr" / "bin" / "cbmc"
        b["cbmc"] = hashlib.sha256(cbmc.read_bytes()).hexdigest()[:16] if cbmc.exists() else "sin-cbmc"
        try:
            b["gcc"] = subprocess.run(["gcc", "--version"], capture_output=True, text=True).stdout.splitlines()[0]
        except (OSError, IndexError):
            b["gcc"] = "sin-gcc"
        b["abi"] = f"{platform.machine()}|{'-'.join(platform.libc_ver())}"
        b["cpu"] = platform.processor() or platform.machine()
        _BASE_FIJA.update(b)
    return {**_BASE_FIJA, "workload": workload}


def _orden_topologico(fuentes):
    """{nombre: s-expr (computation …)} → nombres en orden de llamada; los que llaman a algo ausente (o en ciclo)
    quedan fuera, con sus dependientes."""
    llam = {n: I.llamadas(sx) for n, sx in fuentes.items()}
    orden, hecho, fuera = [], set(), set()

    def visitar(n, pila=()):
        if n in hecho or n in fuera:
            return n in hecho
        if n in pila or n not in fuentes:
            return False
        ok = all(visitar(m, pila + (n,)) for m in sorted(llam[n]))
        (hecho if ok else fuera).add(n)
        if ok:
            orden.append(n)
        return ok
    for n in sorted(fuentes):
        visitar(n)
    return orden, sorted(fuera)


def _defectos(fuentes, primero=None):
    """Defectos del grafo de llamadas de `fuentes` ({nombre: s-expr}), sin elaborar: (el primer ciclo, en orden de
    llamada, buscando desde `primero` y después en orden alfabético, o []; {ausente: [quienes la llaman]})."""
    llam = {n: sorted(I.llamadas(sx)) for n, sx in fuentes.items()}
    ausentes = {}
    for n in sorted(llam):
        for m in llam[n]:
            if m not in fuentes:
                ausentes.setdefault(m, []).append(n)
    hecho, pila = set(), []

    def ciclo(n):
        pila.append(n)
        for m in llam[n]:
            if m in pila:
                return pila[pila.index(m):]
            if m in fuentes and m not in hecho:
                c = ciclo(m)
                if c:
                    return c
        hecho.add(pila.pop())
        return []
    for n in ([primero] if primero in fuentes else []) + sorted(fuentes):
        c = [] if n in hecho else ciclo(n)
        if c:
            return c, ausentes
    return [], ausentes


def _flechas(c):
    return " → ".join(c + c[:1])


def _fuentes_vigentes(store, metadatos=True):
    """{nombre: s-expr} de las computaciones vigentes, comprobando antes que cada definición vigente (computación,
    propiedad o realización) existe, que su huella es la registrada y que su tipo es coherente (en una computación, también
    el nombre). Si no, `RegistroInconsistente` (`definicion`). Solo lee.

    Con `metadatos=False` (`register`) se comprueba solo lo que `instantanea` ya exigía al leerlas: que existan, que
    tengan fuente y que esta se lea (lo que antes era una excepción interna pasa a `RegistroInconsistente`), y su huella
    (`IdentidadDistinta`, la misma excepción de antes). El tipo y el nombre de los metadatos no se comprueban: `register`
    no los usa y puede sustituir la definición."""
    fuentes = {}
    for idx, tipo in ((store.names, "computacion"), (store.props, "propiedad"), (store.reals, "candidata")):
        for n, i in sorted(idx.items()):
            if not i.get("vigente"):
                continue
            try:
                d = store.definicion(i["vigente"])              # existe y su huella es la registrada
                if metadatos and d.get("tipo") != tipo:
                    raise IdentidadDistinta(f"la definición {i['vigente'][:12]} es de tipo {d.get('tipo')}")
                if tipo == "computacion":
                    sx = sexpr.parse(d["fuente"])[0]
                    if metadatos and (d["nombre"] != n or sx.head() != "computation" or
                                      getattr(sx.items[1], "name", None) != n):
                        raise IdentidadDistinta(f"la definición {i['vigente'][:12]} no es la de {n}")
                    fuentes[n] = sx
                elif not metadatos:
                    d["fuente"]                                 # `instantanea` la lee
            except (OSError, ValueError, KeyError, TypeError, IndexError, AttributeError, sexpr.SyntaxError_,
                    core.EFCHError) as e:
                if not metadatos and isinstance(e, core.EFCHError):
                    raise
                raise RegistroInconsistente(f"registro vigente inconsistente: la definición vigente de {tipo} {n} no "
                                            f"se puede usar ({e})", [n], "definicion") from None
    return fuentes


def _ciclo_en_registro(c):
    return RegistroInconsistente(f"registro vigente inconsistente: ciclo de llamadas entre definiciones vigentes: "
                                 f"{_flechas(c)}", c, "ciclo")


def _ausentes_en_registro(ausentes):
    return RegistroInconsistente("registro vigente inconsistente: definiciones vigentes que llaman a computaciones "
                                 "sin definición vigente: " + "; ".join(f"{m} (desde {', '.join(q)})"
                                                                       for m, q in sorted(ausentes.items())),
                                 sorted(ausentes), "llamada-ausente")


def _ciclo_efectivo(nombre, c):
    return CicloEfectivo(f"ciclo efectivo de llamadas al combinar la propuesta de {nombre} con las definiciones "
                         f"vigentes: {_flechas(c)}", c)


def _llamada_ausente(nombre, ausentes):
    return LlamadaAusente(f"{nombre}: la propuesta combinada con las definiciones vigentes llama a computaciones "
                          f"sin definición: {', '.join(sorted(ausentes))}", sorted(ausentes))


def _precontrol(store, sust, nombre):
    """Precontrol de `evolve` (decisión del autor tras la auditoría de Sol), antes de cualquier instantánea o efecto:
    (1) el registro vigente: cada definición vigente existe y es la registrada, y su grafo de llamadas es completo y
    acíclico (si no, `RegistroInconsistente`, aunque la propuesta lo repare); (2) el grafo propuesto (vigentes con
    `sust` encima): sin ciclos, alcancen o no a `nombre` (`CicloEfectivo`), y sin llamadas ausentes (`LlamadaAusente`).
    Solo lee: no elabora ni escribe nada."""
    c, ausentes = _defectos(_fuentes_vigentes(store))
    if c:
        raise _ciclo_en_registro(c)
    if ausentes:
        raise _ausentes_en_registro(ausentes)
    c, ausentes = _defectos(store.fuentes(sust), nombre)
    if c:
        raise _ciclo_efectivo(nombre, c)
    if ausentes:
        raise _llamada_ausente(nombre, ausentes)


def _alcanzables(fuentes, nombre):
    """Las computaciones de `fuentes` a las que se llega por llamadas desde `nombre` (incluida)."""
    vistos, pila = set(), [nombre]
    while pila:
        n = pila.pop()
        if n in fuentes and n not in vistos:
            vistos.add(n)
            pila.extend(I.llamadas(fuentes[n]))
    return vistos


def _precontrol_register(store, sust, nombre):
    """Precontrol de `register`, antes de cualquier instantánea o efecto; solo lee. A diferencia de `evolve`, no rechaza
    por el estado previo en sí: `register` puede restaurar una definición vigente que falta (ver
    resultados/correccion-store-register/dudas.md). Rechaza solo lo que haría que `nombre` no se elaborase, es decir,
    un defecto del grafo efectivo (vigentes con `sust` encima) alcanzable desde `nombre`, que antes terminaba en
    `KeyError`:
    - un ciclo: `CicloEfectivo` si pasa por alguna fuente de la entrada (`sust`), `RegistroInconsistente` (`ciclo`) si es
      del registro previo;
    - una llamada ausente: `RegistroInconsistente` (`llamada-ausente`) si la hace una vigente que la entrada no
      restaura, `LlamadaAusente` si la hace una fuente de la entrada.
    Una definición vigente que `instantanea` no podría leer es `RegistroInconsistente` (`definicion`); no se comprueban
    sus metadatos (`_fuentes_vigentes(metadatos=False)`)."""
    _fuentes_vigentes(store, metadatos=False)
    efectivo = store.fuentes(sust)
    c, ausentes = _defectos({n: efectivo[n] for n in _alcanzables(efectivo, nombre)}, nombre)
    if c:
        raise _ciclo_efectivo(nombre, c) if set(c) & set(sust) else _ciclo_en_registro(c)
    previas = {m: q for m, q in ausentes.items() if not set(q) & set(sust)}
    if previas:
        raise _ausentes_en_registro(previas)
    if ausentes:
        raise _llamada_ausente(nombre, ausentes)


def _indeterminada(tipo, nombre, motivo, implementa=None):
    """Lo que una instantánea no elabora, como dato (D10): `tipo` (computacion, propiedad o realizacion), `nombre`
    (de la computación o la propiedad; la clave «implementa/nombre» del índice si es una realización), `ranura` (id;
    la de una realización no se calcula: el nombre de la candidata está en su fuente) y `motivo` (fuera-de-orden,
    no-elabora o implementa-ausente). Las decisiones leen estos campos, nunca el texto de `_texto_indeterminada`."""
    ranura = {"computacion": I.ranura_computacion, "propiedad": I.ranura_propiedad}.get(tipo)
    return {"tipo": tipo, "nombre": nombre, "ranura": ranura(nombre)["id"] if ranura else None, "motivo": motivo,
            **({"implementa": implementa} if implementa is not None else {})}


def _texto_indeterminada(x):
    """Texto de `indeterminadas` en los informes (formato externo, sin cambios): solo presentación."""
    return x["nombre"] if x["tipo"] == "computacion" else f"{x['tipo']} {x['nombre']}"


class Store:
    def __init__(self, root):
        self.root = pathlib.Path(root)
        for t in I.TABLAS:
            (self.root / "objetos" / t).mkdir(parents=True, exist_ok=True)
        (self.root / "definiciones").mkdir(exist_ok=True)
        (self.root / "pasos").mkdir(exist_ok=True)
        self.names = self._leer("nombres.json")
        self.props = self._leer("propiedades.json")
        self.reals = self._leer("realizaciones.json")
        self.costes = self._leer("costes.json")
        self.alm = reglas.Almacen()
        self.descartados = []
        self._en_disco = set()
        for t in sorted(I.TABLAS):
            for p in sorted((self.root / "objetos" / t).glob("*.json")):
                try:
                    obj = I.decodificar(p.read_bytes())
                    I.VALIDAR[I.TABLAS[t]](obj, f"{t}/{p.stem[:12]}")
                    if obj["id"] != p.stem:
                        raise Rechazo("hash_invalido", p.name, "nombre distinto del id")
                    self.alm.poner(I.TABLAS[t], obj)
                    self._en_disco.add(obj["id"])
                except (I.NoCanonico, Rechazo) as e:      # objeto alterado o mal formado: no se usa (§4)
                    self.descartados.append((t, p.stem, getattr(e, "codigo", "no_canonico")))

    def _leer(self, nombre):
        p = self.root / nombre
        return json.loads(p.read_text()) if p.exists() else {}

    def guardar(self):
        """Escribe los objetos nuevos (inmutables: nunca se sobrescribe uno existente) y los índices."""
        for t in I.TABLAS:
            for oid, obj in self.alm.t[t].items():
                if oid not in self._en_disco:
                    p = self.root / "objetos" / t / f"{oid}.json"
                    if not p.exists():
                        p.write_bytes(I.canonico(obj))
                    self._en_disco.add(oid)
        for nombre, d in (("nombres.json", self.names), ("propiedades.json", self.props),
                          ("realizaciones.json", self.reals), ("costes.json", self.costes)):
            (self.root / nombre).write_text(json.dumps(d, ensure_ascii=False, indent=1))

    save_names = guardar

    def exportar(self, operacion, ids, instantaneas=()):
        """Paquete del paso (§2.3): todo lo que referencian los certificados y registros `ids`."""
        paq = self.alm.paquete_de(sorted(set(ids)), list(instantaneas))
        reglas.Validador(paq)                                   # forma del paquete entero
        n = len(list((self.root / "pasos").glob("*.json"))) + 1
        path = self.root / "pasos" / f"{n:04d}-{operacion}.json"
        path.write_bytes(I.canonico(paq))
        return path

    # --- definiciones registradas ---------------------------------------------------------------------------

    def put_definicion(self, tipo, nombre, fuente, implementa=None):
        d = {"tipo": tipo, "nombre": nombre, "fuente": fuente, **({"implementa": implementa} if implementa else {})}
        did = I.sha(I.canonico(d))
        p = self.root / "definiciones" / f"{did}.json"
        if not p.exists():
            p.write_text(json.dumps(d, ensure_ascii=False))
        return did

    def definicion(self, did):
        d = json.loads((self.root / "definiciones" / f"{did}.json").read_text())
        if I.sha(I.canonico(d)) != did:
            raise IdentidadDistinta(f"la definición {did[:12]} no es la registrada")
        return d

    def current(self, name):
        """Definición registrada vigente de la computación (id de definición, no de revisión: D8)."""
        return self.names.get(name, {}).get("vigente")

    def history(self, name):
        return self.names.get(name, {}).get("historial", [])

    # --- instantánea --------------------------------------------------------------------------------------

    def fuentes(self, sustituir=None):
        """{nombre: s-expr} de las computaciones vigentes, con `sustituir` {nombre: fuente} encima (sin elaborar)."""
        comps = {n: sexpr.parse(self.definicion(i["vigente"])["fuente"])[0]
                 for n, i in self.names.items() if i.get("vigente")}
        comps.update({n: sexpr.parse(f)[0] for n, f in (sustituir or {}).items()})
        return comps

    def instantanea(self, sustituir=None, propiedades=None, retirar=(), realizaciones=None):
        """Elabora las definiciones vigentes (con `sustituir` {nombre: fuente (computation …)}, `propiedades`
        {nombre: fuente (property …)} que sustituyen o se añaden, `retirar` propiedades y `realizaciones`
        {clave: (implementa, fuente)} añadidas) y devuelve (instantánea, objetos). Lo que no elabora queda en
        `indeterminaciones` (datos, `_indeterminada`) y, como texto para los informes, en `indeterminadas`."""
        comps = self.fuentes(sustituir)
        orden, fuera = _orden_topologico(comps)
        indeterminaciones = [_indeterminada("computacion", n, "fuera-de-orden") for n in fuera]
        props = {n: self.definicion(i["vigente"])["fuente"] for n, i in self.props.items()
                 if i.get("vigente") and n not in retirar}
        props.update(propiedades or {})
        texto = "(efch 0.1\n" + "\n".join(sexpr.dumps(comps[n]) for n in orden) + "\n)"
        defn = core.load_definition(texto)
        props_ok = {}
        for n, f in sorted(props.items()):
            try:
                props_ok[n] = core.parse_property(sexpr.parse(f)[0], defn.computations)
            except (core.EFCHError, IndexError):
                indeterminaciones.append(_indeterminada("propiedad", n, "no-elabora"))
        defn.properties = list(props_ok.values())
        cands = {}
        reals = {k: (i["implementa"], self.definicion(i["vigente"])["fuente"]) for k, i in self.reals.items()
                 if i.get("vigente")}
        reals.update(realizaciones or {})
        for k, (impl, fuente) in sorted(reals.items()):
            if impl not in defn.computations:
                indeterminaciones.append(_indeterminada("realizacion", k, "implementa-ausente", impl))
                continue
            try:
                [cand] = core.load_candidates(f"(efch 0.1 {fuente})", defn)
            except core.EFCHError:
                indeterminaciones.append(_indeterminada("realizacion", k, "no-elabora", impl))
                continue
            cands[k] = cand
        f = I.Formas(defn).todas(cands.values())
        self.alm.poner_formas(f)
        wl = {n: core.dumps(c.workload) if c.workload is not None else None for n, c in defn.computations.items()}
        S = self.alm.instantanea(I.instantanea(f.revisiones.values(), base_registro(I.sha(I.canonico(wl)))))
        return S, {"defn": defn, "formas": f, "comps": defn.computations, "props": props_ok, "cands": cands,
                   "indeterminadas": [_texto_indeterminada(x) for x in indeterminaciones],
                   "indeterminaciones": indeterminaciones}

    def revision_actual(self, name, S=None, objs=None):
        if S is None:
            S, objs = self.instantanea()
        return self.alm.get("revisiones", S["revisiones"].get(I.ranura_computacion(name)["id"]))

    # --- recarga por identidad (D9) -------------------------------------------------------------------------

    def _definicion_de_revisiones(self, rev_ids):
        """Definición elaborada desde las fuentes de unas revisiones de computación y sus dependencias."""
        fuentes = {}
        for rid in rev_ids:
            for x in [rid, *self.alm.t["revisiones"][rid]["dependencias"].values()]:
                v = self.alm.t["revisiones"][x]
                sx = sexpr.parse(v["fuente"])[0]
                fuentes[self.alm.t["ranuras"][v["ranura"]]["nombre"]] = sx
        orden, fuera = _orden_topologico(fuentes)
        if fuera:
            raise IdentidadDistinta(f"no se pueden elaborar {fuera}")
        return core.load_definition("(efch 0.1\n" + "\n".join(sexpr.dumps(fuentes[n]) for n in orden) + "\n)")

    def load_computation(self, rev_id):
        """La computación de la revisión `rev_id`, reelaborada desde su fuente y las de sus dependencias; si la forma
        canónica recalculada no es la registrada, se rechaza (D9)."""
        v = self.alm.get("revisiones", rev_id)
        if v is None:
            raise IdentidadDistinta(f"no hay revisión {rev_id[:12]}")
        nombre = self.alm.t["ranuras"][v["ranura"]]["nombre"]
        comp = self._definicion_de_revisiones([rev_id]).computations[nombre]
        if comp.canonical() != v["forma_canonica"] or comp.signature() != v["firma"]:
            raise IdentidadDistinta(f"la computación {nombre} recargada no es la revisión {rev_id[:12]}")
        return comp, v

    def load_realization(self, rid, defn=None):
        """La realización de revisión `rid`. Con `defn`, se elabora su fuente frente a ella y se exige la forma
        canónica registrada; sin ella, se reconstruye desde sus dependencias registradas. Nunca devuelve otro cuerpo
        que el de esa revisión (D9)."""
        v = self.alm.get("revisiones", rid)
        if v is None:
            raise IdentidadDistinta(f"no hay revisión {rid[:12]}")
        r = self.alm.t["ranuras"][v["ranura"]]
        impl = self.alm.t["ranuras"][r["ambito"]]["nombre"]
        if defn is None:
            # La computación que implementa: cualquier revisión registrada de esa ranura con la misma firma (la
            # forma canónica de la candidata solo depende de su firma).
            comp_rev = next((x for x in self.alm.t["revisiones"].values()
                             if x["ranura"] == r["ambito"] and x["firma"] == v["firma"]), None)
            if comp_rev is None:
                raise IdentidadDistinta(f"no hay una revisión registrada de {impl} con la firma de {r['nombre']}")
            defn = self._definicion_de_revisiones([comp_rev["id"], *v["dependencias"].values()])
        try:
            [cand] = core.load_candidates(f"(efch 0.1 {v['fuente']})", defn)
        except core.EFCHError as e:
            raise IdentidadDistinta(f"la realización {r['nombre']} no elabora: {e}") from None
        comp = defn.computations[cand.implements]
        if cand.canonical(comp) != v["forma_canonica"]:
            raise IdentidadDistinta(f"la realización {r['nombre']} recargada no es la revisión {rid[:12]} (otra "
                                    "resolución de sus llamadas)")
        return cand, v

    # --- evidencia ----------------------------------------------------------------------------------------

    def anotar_coste(self, oid, coste):
        """El coste va fuera de los objetos del contrato (no entra en ningún hash)."""
        self.costes.setdefault(oid, {"orden": time.time_ns(), **(coste or {})})

    def vigente(self, af, S):
        """El certificado de `af` reutilizable en S (§6) más reciente, o None."""
        best = None
        for c in self.alm.t["certificados"].values():
            if c["afirmacion"] == af["id"] and self.alm.reutilizable(c["id"], S) is None:
                if best is None or self.costes.get(c["id"], {}).get("orden", 0) > \
                        self.costes.get(best["id"], {}).get("orden", 0):
                    best = c
        return best

    def registro_de(self, af, S):
        regs = [r for r in self.alm.t["registros"].values() if r["afirmacion"] == af["id"]
                and r["instantanea"] == S["id"]]
        return max(regs, key=lambda r: self.costes.get(r["id"], {}).get("orden", 0)) if regs else None

    def afirmaciones(self, S, objs):
        """Afirmaciones de la instantánea: WD de cada computación, PROP de cada propiedad, WD y REAL de cada
        realización, y las REFUT del almacén sobre esas revisiones."""
        rev = lambda r: self.alm.t["revisiones"][S["revisiones"][r["id"]]]  # noqa: E731
        out = [I.afirmacion("WD", objeto=rev(I.ranura_computacion(n))) for n in sorted(objs["comps"])]
        out += [I.afirmacion("PROP", propiedad=rev(I.ranura_propiedad(n))) for n in sorted(objs["props"])]
        for k, cand in sorted(objs["cands"].items()):
            rc, rf = rev(I.ranura_candidata(cand.name, cand.implements)), rev(I.ranura_computacion(cand.implements))
            out += [I.afirmacion("WD", objeto=rc), I.afirmacion("REAL", candidata=rc, computacion=rf)]
            for a in sorted(self.alm.t["afirmaciones"].values(), key=lambda a: a["id"]):
                if a["clase"] == "REFUT" and a["sujetos"] == {"candidata": rc["id"], "computacion": rf["id"]}:
                    out.append(a)
        for a in out:
            self.alm.afirmacion(a)
        return out

    def etiquetas(self, af):
        out = {}
        for p, i in af["sujetos"].items():
            v = self.alm.t["revisiones"][i]
            r = self.alm.t["ranuras"][v["ranura"]]
            amb = f"@{self.alm.t['ranuras'][r['ambito']]['nombre']}" if r["tipo"] in I.CANDIDATAS else ""
            out[p] = f"{r['tipo']}:{r['nombre']}{amb}:{v['contenido'][:12]}"
        return out

    def vigencia(self, S=None, objs=None):
        """Estado de cada afirmación de la instantánea (el de su certificado reutilizable; si no hay, el último
        registro de esa instantánea o `no comprobado`) y las evidencias concluyentes de esas obligaciones que ya no
        son reutilizables en ella (obsoletas)."""
        if S is None:
            S, objs = self.instantanea()
        filas, actuales, obligaciones = [], set(), set()
        for a in self.afirmaciones(S, objs):
            c = self.vigente(a, S)
            r = None if c else self.registro_de(a, S)
            actuales.add(c["id"] if c else None)
            obligaciones.add(I.obligacion(a, self.alm.t["revisiones"]))
            filas.append({"afirmacion": a["id"], "clase": a["clase"], "sujetos": self.etiquetas(a),
                          "estado": c["estado"] if c else (r["resultado"] if r else "no comprobado"),
                          "certificado": c["id"] if c else None, "regla": c["regla"] if c else None,
                          "registro": r["id"] if r else None})
        obsoletas = []
        for c in sorted(self.alm.t["certificados"].values(), key=lambda c: c["id"]):
            a = self.alm.t["afirmaciones"].get(c["afirmacion"])
            if a is None or c["id"] in actuales or I.obligacion(a, self.alm.t["revisiones"]) not in obligaciones:
                continue
            if self.alm.reutilizable(c["id"], S) is not None:
                obsoletas.append({"afirmacion": a["id"], "clase": a["clase"], "sujetos": self.etiquetas(a),
                                  "estado": c["estado"], "certificado": c["id"]})
        return {"instantanea": S["id"], "afirmaciones": filas, "obsoletas": obsoletas,
                "indeterminadas": objs["indeterminadas"]}


# --- evidencia directa -------------------------------------------------------------------------------------

def _evidencia(store, af, S, estado, objeto, coste=None, mediciones=None):
    """Hoja directa si la clase admite el estado (§3.4) — `efch.reglas` exige objeto verificado = contenido del sujeto
    (D9) —; si no, registro histórico (D-3). Devuelve {"certificado": c} o {"registro": r}."""
    store.alm.afirmacion(af)
    if estado in I.ESTADOS_POR_CLASE[af["clase"]]:
        c = reglas.directa(store.alm, af, S, estado, objeto)
        store.anotar_coste(c["id"], coste)
        return {"certificado": c}
    r = store.alm.anotar(I.registro(af, estado if estado in I.ESTADOS_REGISTRO else "desconocido", "directa", S,
                                    mediciones=mediciones or {}))
    store.anotar_coste(r["id"], coste)
    return {"registro": r}


def _id(ev):
    return (ev.get("certificado") or ev.get("registro"))["id"]


def _rev(store, S, ranura_):
    return store.alm.t["revisiones"][S["revisiones"][ranura_["id"]]]


def _testigo_refuta(cand, comp, testigo):
    """Hoja del intérprete para REFUT (§3.2): c(w) y f(w) definidas y distintas."""
    if not isinstance(testigo, dict) or set(testigo) != {n for n, _ in comp.inputs}:
        return False
    args = [tuple(testigo[n]) if isinstance(testigo[n], list) else testigo[n] for n, _ in comp.inputs]
    try:
        return interp.run(cand.body, comp.inputs, args) != interp.run(comp, comp.inputs, args)
    except interp.Undefined:
        return False
    except Exception:  # noqa: BLE001 — testigo que no se ajusta a la firma: no hay hoja
        return False


def _certificar_realizacion(store, S, cand, comp, v, secs):
    """WD(c), REAL(c, f) y, si la equivalencia se refuta con un testigo que el intérprete confirma, REFUT(c, f, w),
    sobre las revisiones de S (D9: el objeto verificado es el contenido de la revisión de c en S)."""
    rc = _rev(store, S, I.ranura_candidata(cand.name, comp.name))
    rf = _rev(store, S, I.ranura_computacion(comp.name))
    if rc["contenido"] != cand.identity(comp) or rf["contenido"] != comp.identity():
        raise IdentidadDistinta(f"{cand.name}: la candidata verificada no es la de la instantánea")
    obls = v["obligaciones"]
    out = {"WD": _evidencia(store, I.afirmacion("WD", objeto=rc), S, obls[0]["estado"], rc["contenido"],
                            {"segundos": obls[0].get("segundos")}),
           "REAL": _evidencia(store, I.afirmacion("REAL", candidata=rc, computacion=rf), S, v["estado"],
                              rc["contenido"], {"segundos": secs}, {"estado": v["estado"]})}
    eq = next((o for o in obls[1:] if o["estado"] == "refutado" and o.get("contraejemplo")), None)
    if eq is not None and obls[0]["estado"] == "probado" and _testigo_refuta(cand, comp, eq["contraejemplo"]):
        try:
            af = I.afirmacion("REFUT", {"testigo": eq["contraejemplo"]}, candidata=rc, computacion=rf)
            out["REFUT"] = _evidencia(store, af, S, "probado", rc["contenido"], {"segundos": eq.get("segundos")})
        except Rechazo:
            pass                                # testigo fuera del dominio del contrato: queda el registro de REAL
    return out


# --- operaciones -------------------------------------------------------------------------------------------

def _propiedades_de(defn, names):
    """Propiedades de la definición cuyo cierre de llamadas contiene alguna de las computaciones dadas, una por
    ranura. Dos propiedades homónimas con revisiones distintas se rechazan (`RanuraRepetida`, K2 de la v2.7, §2.2);
    con la misma revisión son un único objeto. La ranura de una propiedad es (propiedad, "", nombre): por eso los
    índices del registro (`propiedades.json`, `propiedades=`) pueden usar el nombre."""
    return [p for p in _una_por_ranura(I.Formas(defn).propiedad, defn.properties)
            if set(pipeline.property_closure(defn, p)) & set(names)]


def _cierre_llamadas(defn, nombre):
    vistos, pila = set(), [nombre]
    while pila:
        n = pila.pop()
        if n not in vistos and n in defn.computations:
            vistos.add(n)
            pila.extend(I.llamadas(defn.computations[n].source))
    return vistos


def _check_property(store, S, prop, timeout):
    r = smt.check_property(prop, timeout)
    af = I.afirmacion("PROP", propiedad=_rev(store, S, I.ranura_propiedad(prop.name)))
    ev = _evidencia(store, af, S, r.status, I.contenido_propiedad(prop), {"segundos": r.seconds},
                    {"detalle": (r.detail or "")[:300]})
    return {"nombre": prop.name, **r.as_dict(), "certificado": _id(ev)}


def _registrar_propiedades(store, props, dueno):
    """Una propiedad sigue vigente mientras tenga algún dueño."""
    for p in props:
        did = store.put_definicion("propiedad", p.name, sexpr.dumps(p.source))
        e = store.props.setdefault(p.name, {"vigente": None, "duenos": [], "historial": []})
        e["historial"].append({"definicion": did, "dueno": dueno, "fecha": time.strftime("%Y-%m-%dT%H:%M:%S")})
        e["vigente"] = did
        if dueno not in e["duenos"]:
            e["duenos"].append(dueno)


def _nuevas_definiciones(store, defn, nombres):
    """Fuentes de `nombres` y de las computaciones de su cierre de llamadas aún no registradas."""
    out = {}
    for n in nombres:
        for m in _cierre_llamadas(defn, n):
            if m == n or not store.current(m):
                out[m] = sexpr.dumps(defn.computations[m].source)
    return out


def register(store, defn, defn_text, name, timeout=120, note=""):
    """Primera revisión de una computación: se registra su definición (y las de lo que llama que aún no esté
    registrado), se elabora la instantánea y se verifican directamente WD y sus propiedades."""
    comp = defn.computations[name]
    props = _propiedades_de(defn, [name])
    sust = _nuevas_definiciones(store, defn, [name] + [n for p in props for n in pipeline.property_closure(defn, p)])
    _precontrol_register(store, sust, name)     # antes de elaborar ninguna instantánea: no se toca el almacén
    S, objs = store.instantanea(sustituir=sust, propiedades={p.name: sexpr.dumps(p.source) for p in props})
    rev = _rev(store, S, I.ranura_computacion(name))
    scomp = objs["comps"][name]
    wd = smt.check_well_defined("semántica bien definida", scomp.semantics, scomp.inputs, timeout)
    ids = [_id(_evidencia(store, I.afirmacion("WD", objeto=rev), S, wd.status, rev["contenido"],
                          {"segundos": wd.seconds}))]
    checked = [_check_property(store, S, objs["props"][p.name], timeout) for p in props if p.name in objs["props"]]
    ids += [p["certificado"] for p in checked]
    accepted = wd.status == "probado" and all(p["estado"] == "probado" for p in checked) and len(checked) == len(props)
    did = store.put_definicion("computacion", name, sust.get(name, sexpr.dumps(comp.source)))
    entry = {"definicion": did, "identidad": rev["id"], "contenido": rev["contenido"], "padre": None,
             "aceptada": accepted, "nota": note, "propiedades": [p.name for p in props],
             "fecha": time.strftime("%Y-%m-%dT%H:%M:%S")}
    store.names.setdefault(name, {"vigente": None, "historial": []})["historial"].append(entry)
    if accepted:
        store.names[name]["vigente"] = did
        for m, f in sust.items():
            if m != name:
                dm = store.put_definicion("computacion", m, f)
                store.names.setdefault(m, {"vigente": None, "historial": []})["historial"].append(
                    {"definicion": dm, "identidad": _rev(store, S, I.ranura_computacion(m))["id"], "padre": None,
                     "aceptada": True, "nota": f"dependencia de {name}", "propiedades": [],
                     "fecha": entry["fecha"]})
                store.names[m]["vigente"] = dm
        _registrar_propiedades(store, props, name)
    store.exportar("register", ids, [S["id"]])
    store.guardar()
    return {"identidad": rev["id"], "contenido": rev["contenido"], "definicion": did,
            "bien_definida": wd.as_dict(), "propiedades": checked, "aceptada": accepted,
            "dependencias_no_vigentes": rev["contenido"] != comp.identity()}


def realize(store, defn, cand, timeout=120, defn_text=None):
    """Registra y verifica una candidata en la instantánea del registro. Si llama a una computación registrada con
    otra revisión que la de `defn`, se rechaza (D9) en lugar de verificar un cuerpo y anotar otro. Devuelve
    (rid, verificación), con rid = id de la revisión de la candidata en la instantánea."""
    if store.current(cand.implements) is None:
        raise core.EFCHError(f"{cand.implements} no tiene revisión vigente aceptada en el almacén")
    [sx] = sexpr.parse(cand.source_text)
    sust = {}
    for n in sorted(I.llamadas(sx)):
        if store.current(n) is None:
            if defn_text is None or n not in defn.computations:
                raise IdentidadDistinta(f"{cand.name} llama a {n}, que no está registrada; pase defn_text")
            sust.update(_nuevas_definiciones(store, defn, [n]))
    clave = f"{cand.implements}/{cand.name}"
    previa = store.reals.get(clave)
    if previa is not None and previa["implementa"] != cand.implements:
        # La clave textual no separa computación y nombre si alguno contiene «/» (a/b + c = a + b/c): sería otra
        # ranura con la misma entrada del índice. Se rechaza en vez de mezclar sus historias (K1, v2.7).
        raise IdentidadDistinta(f"la clave {clave!r} ya es de una candidata de {previa['implementa']}")
    S, objs = store.instantanea(sustituir=sust, realizaciones={clave: (cand.implements, cand.source_text)})
    scand = objs["cands"].get(clave)
    comp = defn.computations[cand.implements]
    if scand is None or scand.canonical(objs["comps"][cand.implements]) != cand.canonical(comp):
        raise IdentidadDistinta(f"{cand.name}: la candidata resuelta en el registro no es la dada")
    scomp = objs["comps"][cand.implements]
    t0 = time.perf_counter()
    v = pipeline.verify_candidate(scomp, scand.body, timeout)
    secs = round(time.perf_counter() - t0, 3)
    evs = _certificar_realizacion(store, S, scand, scomp, v, secs)
    for m, f in sust.items():
        store.names.setdefault(m, {"vigente": None, "historial": []})["historial"].append(
            {"definicion": store.put_definicion("computacion", m, f), "padre": None, "aceptada": True,
             "nota": f"dependencia de la candidata {cand.name}", "propiedades": []})
        store.names[m]["vigente"] = store.put_definicion("computacion", m, f)
    did = store.put_definicion("candidata", cand.name, cand.source_text, cand.implements)
    e = store.reals.setdefault(clave, {"implementa": cand.implements, "vigente": None, "historial": []})
    rid = _rev(store, S, I.ranura_candidata(cand.name, cand.implements))["id"]
    e["historial"].append({"definicion": did, "revision": rid, "fecha": time.strftime("%Y-%m-%dT%H:%M:%S")})
    e["vigente"] = did
    v["certificados"] = {k: _id(x) for k, x in evs.items()}
    store.exportar("realize", v["certificados"].values(), [S["id"]])
    store.guardar()
    return rid, v


def _counterexample(v):
    for o in v.get("obligaciones", []):
        if o.get("contraejemplo"):
            return o["contraejemplo"]
    return None


def _compare(store, old_comp, old_rev, new_comp, new_rev, timeout, S_d=None):
    """Relación entre dos revisiones: equivalente | difiere | desconocido | interfaz-distinta. Devuelve
    (relación, certificado EQ(nueva → anterior) probado o None, testigo, segundos)."""
    if old_comp.signature() != new_comp.signature():
        return "interfaz-distinta", None, None, 0.0
    r = smt.check_equivalence(new_comp, old_comp.semantics, timeout)
    eq = None
    if S_d is not None:
        af = I.afirmacion("EQ", nueva=new_rev, anterior=old_rev)
        ev = _evidencia(store, af, S_d, r.status, new_rev["contenido"], {"segundos": r.seconds},
                        {"detalle": (r.detail or "")[:300]})
        eq = ev.get("certificado") if r.status == "probado" else None
    rel = {"probado": "equivalente", "refutado": "difiere"}.get(r.status, "desconocido")
    return rel, eq, r.counterexample if r.status == "refutado" else None, r.seconds


def _verificar_directa(store, S, cand, comp, timeout):
    t0 = time.perf_counter()
    v = pipeline.verify_candidate(comp, cand.body, timeout)
    secs = round(time.perf_counter() - t0, 3)
    evs = _certificar_realizacion(store, S, cand, comp, v, secs)
    return {"estado": v["estado"], "via": "verificacion directa", "segundos": secs, "evidencia": _id(evs["REAL"]),
            "certificados": {k: _id(x) for k, x in evs.items()}, "contraejemplo": _counterexample(v)}


def _transferir(store, S_d, rc_d, rf_d, cand, comp, eqs):
    """R-REAL o R-REFUT hacia (rc_d, rf_d) en S_d, solo por `efch.reglas`. `eqs`: {id de revisión f_x: EQ(f_d → f_x)
    probado}. Los orígenes son certificados del almacén sobre la **misma revisión** de la candidata (D9).
    Devuelve (certificado, regla) o (None, rechazos)."""
    alm = store.alm
    rechazos = []
    afs = alm.t["afirmaciones"]
    for o in sorted(alm.t["certificados"].values(), key=lambda c: c["id"]):
        a = afs.get(o["afirmacion"])
        if a is None or a["clase"] != "REAL" or o["estado"] != "probado" or a["sujetos"]["candidata"] != rc_d["id"]:
            continue
        fx = a["sujetos"]["computacion"]
        if fx not in eqs:
            continue
        S_x = alm.t["instantaneas"][o["instantanea"]]
        wd_a = store.vigente(I.afirmacion("WD", objeto=alm.t["revisiones"][fx]), S_x)
        wd_c = store.vigente(I.afirmacion("WD", objeto=rc_d), S_d)
        if wd_a is None or wd_c is None:
            rechazos.append({"regla": "R-REAL", "codigo": "premisa_ausente", "detalle": "WD(f_a) o WD(c)"})
            continue
        try:
            af = alm.afirmacion(I.afirmacion("REAL", candidata=rc_d, computacion=rf_d))
            return reglas.r_real(alm, af, o, eqs[fx], wd_a, wd_c, S_d), "R-REAL"
        except Rechazo as e:
            rechazos.append({"regla": "R-REAL", **e.a_dict()})
    for o in sorted(alm.t["certificados"].values(), key=lambda c: c["id"]):
        a = afs.get(o["afirmacion"])
        if a is None or a["clase"] != "REFUT" or a["sujetos"]["candidata"] != rc_d["id"] \
                or alm.t["revisiones"][a["sujetos"]["computacion"]]["ranura"] != rf_d["ranura"]:
            continue
        if a["sujetos"]["computacion"] not in eqs:
            continue                  # la EQ es opcional en el contrato; la política de EXP-002/018 la exige
        testigo = a["contexto"]["testigo"]
        if not _testigo_refuta(cand, comp, testigo):
            rechazos.append({"regla": "R-REFUT", "codigo": "evaluacion", "detalle": "el intérprete no refuta en S_d"})
            continue
        try:
            af = alm.afirmacion(I.afirmacion("REFUT", a["contexto"], candidata=rc_d, computacion=rf_d))
            ev = reglas.directa(alm, af, S_d, "probado", rc_d["contenido"])        # reevaluación del testigo
            return reglas.r_refut(alm, af, o, ev, S_d, eqs[a["sujetos"]["computacion"]]), "R-REFUT"
        except Rechazo as e:
            rechazos.append({"regla": "R-REFUT", **e.a_dict()})
    return None, rechazos


def evolve(store, defn, defn_text, name, timeout=120, note="", reverify_all=False, revalidar=False):
    """Propone una definición nueva de `name` y calcula sus consecuencias (§9).

    Se verifican directamente WD(f_d) y las propiedades de la instantánea nueva sin certificado reutilizable (las que
    dependen de f a través de otra computación incluidas: D8), y con ellas se decide la aceptación. Las realizaciones
    de f se transfieren por R-REAL / R-REFUT (solo `efch.reglas`) o se verifican directamente. Las demás afirmaciones
    cuyo cierre contiene f quedan `no comprobado` en la instantánea nueva salvo `revalidar`.

    reverify_all: además de transferir, verifica cada realización directamente (para evaluar la transferencia).
    """
    new = defn.computations[name]
    old_did = store.current(name)
    if old_did is None:
        raise core.EFCHError(f"{name} no tiene revisión vigente aceptada en el almacén: use register")
    props_nuevas = _propiedades_de(defn, [name])
    nuevas = {p.name for p in props_nuevas}
    retirar = sorted(n for n, e in store.props.items() if e.get("vigente") and n not in nuevas
                     and set(e.get("duenos", [])) == {name})
    sust = {**_nuevas_definiciones(store, defn, [name]), name: sexpr.dumps(new.source)}
    _precontrol(store, sust, name)          # antes de elaborar ninguna instantánea: no se toca el almacén
    S_a, objs_a = store.instantanea()
    S_d, objs_d = store.instantanea(sustituir=sust, propiedades={p.name: sexpr.dumps(p.source) for p in props_nuevas},
                                    retirar=retirar)
    f_ranura = I.ranura_computacion(name)
    f_a, f_d = _rev(store, S_a, f_ranura), _rev(store, S_d, f_ranura)
    base = {"identidad": f_d["id"], "contenido": f_d["contenido"], "anterior": f_a["id"],
            "instantanea_anterior": S_a["id"], "instantanea_nueva": S_d["id"]}
    if S_a["id"] == S_d["id"]:
        return {**base, "relacion": "misma identidad", "aceptada": True, "realizaciones": [], "propiedades": [],
                "propiedades_retiradas": [], "propiedades_nuevas": [], "obsoletas": [], "pendientes": []}
    vig_a = store.vigencia(S_a, objs_a)
    report = dict(base)
    ids = []
    old, new_s = objs_a["comps"][name], objs_d["comps"][name]
    wd = smt.check_well_defined("semántica bien definida", new_s.semantics, new_s.inputs, timeout)
    ids.append(_id(_evidencia(store, I.afirmacion("WD", objeto=f_d), S_d, wd.status, f_d["contenido"],
                              {"segundos": wd.seconds})))
    relation, eq, witness, rel_secs = _compare(store, old, f_a, new_s, f_d, timeout, S_d)
    report.update({"bien_definida": wd.as_dict(), "relacion": relation, "testigo": witness,
                   "segundos_relacion": rel_secs})
    eqs = {f_a["id"]: eq} if eq is not None else {}
    # Revisión aceptada equivalente en el historial (identidad por equivalencia): otra EQ(f_d → f_x) directa.
    searched = []
    if not eqs and relation != "interfaz-distinta":
        for entry in reversed(store.history(name)):
            rx = entry.get("identidad")
            if not entry.get("aceptada") or rx in (f_a["id"], f_d["id"], None) or rx not in store.alm.t["revisiones"]:
                continue
            try:
                prev, vx = store.load_computation(rx)
            except (IdentidadDistinta, core.EFCHError):
                continue
            rel, eqx, _, secs = _compare(store, prev, vx, new_s, f_d, timeout, S_d)
            searched.append({"revision": rx, "relacion": rel, "segundos": secs})
            if eqx is not None:
                eqs[rx] = eqx
                break
    report["equivalente_en_historial"] = next((x for x in eqs if x != f_a["id"]), None)
    report["busqueda_historial"] = searched
    ids += [c["id"] for c in eqs.values()]

    results = []
    for k, cand in sorted(objs_d["cands"].items()):
        if cand.implements != name:
            continue
        rc_d = _rev(store, S_d, I.ranura_candidata(cand.name, name))
        row = None
        if eqs:
            cert, regla = _transferir(store, S_d, rc_d, f_d, cand, new_s, eqs)
            if cert is not None:
                store.anotar_coste(cert["id"], {"segundos": 0.0})
                ids.append(cert["id"])
                status = "probado" if regla == "R-REAL" else "refutado"
                via = "composicion: " + ("realiza" if regla == "R-REAL" else "difiere") + " + equivalente"
                testigo = store.alm.t["afirmaciones"][cert["afirmacion"]]["contexto"].get("testigo") \
                    if regla == "R-REFUT" else None
                row = {"realizacion": rc_d["id"], "nombre": cand.name, "estado": status, "via": via, "regla": regla,
                       "segundos": 0.0, "evidencia": cert["id"], "contraejemplo": testigo}
            elif regla:
                report.setdefault("rechazos_transferencia", {})[cand.name] = regla
        if row is None or reverify_all:
            direct = _verificar_directa(store, S_d, cand, new_s, timeout)
            ids += list(direct["certificados"].values())
            direct.update({"realizacion": rc_d["id"], "nombre": cand.name})
            if row is None:
                row = direct
            else:
                row["comprobacion_directa"] = {"estado": direct["estado"], "segundos": direct["segundos"]}
        results.append(row)
    report["realizaciones"] = results

    # Propiedades de S_d sin certificado reutilizable (su cierre contiene f, también a través de otra computación:
    # D8): se verifican directamente.
    checked = []
    for n, p in sorted(objs_d["props"].items()):
        af = I.afirmacion("PROP", propiedad=_rev(store, S_d, I.ranura_propiedad(n)))
        if store.vigente(af, S_d) is None:
            checked.append(_check_property(store, S_d, p, timeout))
    ids += [p["certificado"] for p in checked]
    previous_props = set(next((e["propiedades"] for e in reversed(store.history(name))
                               if e.get("definicion") == old_did), []))
    report["propiedades"] = checked
    report["propiedades_retiradas"] = sorted(previous_props - nuevas)
    report["propiedades_nuevas"] = sorted(nuevas - previous_props)
    report["indeterminadas"] = objs_d["indeterminadas"]
    broken = [p["nombre"] for p in checked if p["estado"] != "probado"]
    # Una propiedad que no se elabora impide aceptar; se decide por el tipo de la indeterminación, no por su texto.
    sin_elaborar = [x["nombre"] for x in objs_d["indeterminaciones"] if x["tipo"] == "propiedad"]
    accepted = wd.status == "probado" and not broken and not sin_elaborar
    report["aceptada"] = accepted
    report["motivo_rechazo"] = (f"propiedades no probadas: {', '.join(broken)}" if broken else
                                ("semántica no probada como bien definida" if wd.status != "probado" else
                                 (None if accepted else "propiedades que no se pueden elaborar en la instantánea nueva")))
    did = store.put_definicion("computacion", name, sust[name])
    entry = {"definicion": did, "identidad": f_d["id"], "contenido": f_d["contenido"], "padre": f_a["id"],
             "aceptada": accepted, "nota": note, "relacion_con_padre": relation, "propiedades": sorted(nuevas),
             "fecha": time.strftime("%Y-%m-%dT%H:%M:%S")}
    store.names[name]["historial"].append(entry)
    if accepted:
        store.names[name]["vigente"] = did
        for m, f in sust.items():
            if m != name:
                store.names.setdefault(m, {"vigente": None, "historial": []})["vigente"] = \
                    store.put_definicion("computacion", m, f)
        _registrar_propiedades(store, props_nuevas, name)
        for n, e in store.props.items():
            if name in e.get("duenos", []) and n not in nuevas:
                e["duenos"].remove(name)
                if not e["duenos"]:
                    e["vigente"] = None
    S_n, objs_n = store.instantanea()
    if revalidar and accepted:
        report["revalidadas"], extra = _revalidar(store, S_n, objs_n, name, timeout)
        ids += extra
    vig_n = store.vigencia(S_n, objs_n)
    antes = {x["certificado"] for x in vig_a["afirmaciones"] if x["certificado"]}
    ahora = {x["certificado"] for x in vig_n["afirmaciones"] if x["certificado"]}
    report["obsoletas"] = [x for x in vig_a["afirmaciones"] if x["certificado"] in antes - ahora]
    report["pendientes"] = [x for x in vig_n["afirmaciones"] if x["estado"] == "no comprobado"]
    report["instantanea_vigente"] = S_n["id"]
    report["intercambio"] = str(store.exportar("evolve", ids, [S_a["id"], S_d["id"], S_n["id"]]))
    store.guardar()
    return report


def _revalidar(store, S, objs, name, timeout):
    """Verificación directa de las afirmaciones WD y REAL de S sin certificado reutilizable (D8)."""
    out, ids = [], []
    for n, comp in sorted(objs["comps"].items()):
        rev = _rev(store, S, I.ranura_computacion(n))
        af = I.afirmacion("WD", objeto=rev)
        if n == name or store.vigente(af, S) is not None:
            continue
        r = smt.check_well_defined("semántica bien definida", comp.semantics, comp.inputs, timeout)
        ids.append(_id(_evidencia(store, af, S, r.status, rev["contenido"], {"segundos": r.seconds})))
        out.append({"afirmacion": "WD", "objeto": n, "estado": r.status})
    for k, cand in sorted(objs["cands"].items()):
        comp = objs["comps"][cand.implements]
        rc = _rev(store, S, I.ranura_candidata(cand.name, cand.implements))
        af = I.afirmacion("REAL", candidata=rc, computacion=_rev(store, S, I.ranura_computacion(comp.name)))
        if cand.implements == name or store.vigente(af, S) is not None:
            continue
        d = _verificar_directa(store, S, cand, comp, timeout)
        ids += list(d["certificados"].values())
        out.append({"afirmacion": "REAL", "objeto": cand.name, "computacion": comp.name, "estado": d["estado"]})
    return out, ids
