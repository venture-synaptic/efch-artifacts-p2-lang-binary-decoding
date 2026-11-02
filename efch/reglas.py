"""
Comprobador de la referencia (especificacion/ESPECIFICACION.md v2.7, §5–§6): cierre, base, vigencia y reglas de
inferencia sobre un paquete de intercambio. Es la **única** vía de reutilización de B1-v2 y de `store` (§11.2): toda
conservación, caché o transferencia se construye aquí y solo se publica si `Validador` la acepta con toda su cadena.

- `Validador(paquete).validar(cid)`: el certificado y **toda** su cadena (procedencia y premisas, recursivamente hasta
  hojas directas), en postorden y sin recursión de Python; el contexto fijo (§3.2) se exige a cada afirmación del
  paquete, también a las de las premisas (prevalidación global de §4.1).
- `Validador(paquete).reutilizable(cid, S)`: validez y, después, vigencia en S (§5.2).
- `Almacen`: objetos del contrato por tabla; exporta el paquete con todo lo que referencian unos certificados.
- `directa`, `conservar`, `r_prop`, `r_real`, `r_refut`: construyen el certificado con el cierre y la base que
  corresponden y lo validan en el paquete de su cadena antes de publicarlo; si no, `Rechazo` con su código (§7).

No verifica nada: las hojas directas las producen los verificadores (Z3, intérprete, CBMC, gcc) a través del
ejecutor, que declara `objeto_verificado`. No importa `especificacion`.
"""

from . import identidad as I
from .identidad import Rechazo

REGLA_CLASE = {"R-PROP": "PROP", "R-REAL": "REAL", "R-REFUT": "REFUT"}


class Validador:
    def __init__(self, paquete):
        I.prevalidar(paquete)
        self.p = paquete
        self._validos = {}
        self._en_curso = set()
        self._revs_ok = set()
        self._ambitos_ok = set()
        self._afs = {}

    # --- objetos (ya prevalidados en su forma) -------------------------------------------------------------

    def _obj(self, tabla, oid, ruta):
        if not isinstance(oid, str) or oid not in self.p[tabla]:
            raise Rechazo("referencia_desconocida", ruta, f"{tabla}/{str(oid)[:12]}")
        return self.p[tabla][oid]

    def ranura(self, oid, ruta):
        """La ranura; la de una candidata, con su ámbito resuelto en una ranura de computación del paquete
        (`referencia_desconocida`, `ambito_invalido`; v2.7, §2.2 y §6.1)."""
        r = self._obj("ranuras", oid, ruta)
        if r["tipo"] in I.CANDIDATAS and oid not in self._ambitos_ok:
            if self._obj("ranuras", r["ambito"], f"{ruta}.ambito")["tipo"] != "computacion":
                raise Rechazo("ambito_invalido", ruta, f"el ámbito de {r['nombre']!r} no es una ranura de computación")
            self._ambitos_ok.add(oid)
        return r

    def instantanea(self, oid, ruta):
        return self._obj("instantaneas", oid, ruta)

    def revision(self, oid, ruta):
        """La revisión y su ranura; cada dependencia, en orden: computación, existente, de esa ranura, y el mapa
        transitivo y coherente (§6.1, 2)."""
        v = self._obj("revisiones", oid, ruta)
        if oid in self._revs_ok:
            return v
        self.ranura(v["ranura"], ruta)
        deps = v["dependencias"]
        for rk in sorted(deps):
            if self.ranura(rk, ruta)["tipo"] != "computacion":
                raise Rechazo("tipo_invalido", ruta, "solo se depende de computaciones")
            d = self._obj("revisiones", deps[rk], ruta)
            if d["ranura"] != rk:
                raise Rechazo("cierre_incoherente", ruta, "la dependencia es de otra ranura")
            for dk in sorted(d["dependencias"]):
                if dk == v["ranura"] or deps.get(dk) != d["dependencias"][dk]:
                    raise Rechazo("cierre_incoherente", ruta, "dependencias no transitivas o incoherentes")
        self._revs_ok.add(oid)
        return v

    def afirmacion(self, oid, ruta):
        """(afirmación, {papel: revisión}) con sus sujetos comprobados (§3.1)."""
        if oid in self._afs:
            return self._afs[oid]
        a = self._obj("afirmaciones", oid, ruta)
        suj = {}
        for papel in sorted(a["sujetos"]):
            v = self.revision(a["sujetos"][papel], f"{ruta}.{papel}")
            if v["semantica"] != a["semantica"]:
                raise Rechazo("semantica_distinta", ruta, papel)
            tipo = self.ranura(v["ranura"], ruta)["tipo"]
            if tipo not in I.PAPELES[a["clase"]][papel]:
                raise Rechazo("tipo_sujeto_invalido", ruta, f"{papel}: {tipo}")
            suj[papel] = v
        if "candidata" in suj and self.ranura(suj["candidata"]["ranura"], ruta)["ambito"] != suj["computacion"]["ranura"]:
            raise Rechazo("tipo_sujeto_invalido", ruta, "la candidata no implementa esa computación")
        if a["clase"] == "EQ":
            if suj["nueva"]["ranura"] != suj["anterior"]["ranura"]:
                raise Rechazo("ranura_distinta", ruta, "EQ entre ranuras distintas")
            if suj["nueva"]["firma"] != suj["anterior"]["firma"]:
                raise Rechazo("firma_distinta", ruta, "EQ entre firmas distintas")
        self._afs[oid] = (a, suj)
        return a, suj

    # --- cierre, base y vigencia (§5) -------------------------------------------------------------------------

    def cierre(self, a, suj, ruta):
        c = I.cierre_de([suj[p] for p in I.PAPELES_CIERRE[a["clase"]]])
        if c is None:
            raise Rechazo("cierre_incoherente", ruta, "una ranura con dos revisiones")
        return c

    def base_de_clase(self, a, suj, S, ruta):
        comps = componentes_de_clase(a["clase"], {self.ranura(v["ranura"], ruta)["tipo"] for v in suj.values()})
        falta = [c for c in comps if c not in S["base"]]
        if falta:
            raise Rechazo("base_incompleta", ruta, ", ".join(falta))
        return {c: S["base"][c] for c in comps}

    def vigente(self, c, S, ruta):
        a, suj = self.afirmacion(c["afirmacion"], ruta)
        for rk in sorted(c["cierre"]):
            if S["revisiones"].get(rk) != c["cierre"][rk]:
                raise Rechazo("no_vigente", ruta, f"ranura {rk[:12]}")
        if c["base"] != self.base_de_clase(a, suj, S, ruta):
            raise Rechazo("no_vigente", ruta, "base de la clase distinta")

    # --- cadena (§6.1, 1) ---------------------------------------------------------------------------------

    def validar(self, cid, ruta="certificado"):
        if cid not in self._validos and cid not in self._en_curso:
            for x in self._postorden(cid):
                self._uno(x, ruta)
        return self._uno(cid, ruta)

    def _postorden(self, cid):
        """Certificados alcanzables desde `cid` (procedencia y premisas por nombre), hijos antes que su consumidor;
        sin `cid`. Los ausentes y los registros se quedan en la lista: dan su código en su turno."""
        orden, visto, pila = [], set(), [(cid, False)]
        while pila:
            x, hecho = pila.pop()
            if hecho:
                orden.append(x)
                continue
            if x in visto or x in self._validos:
                continue
            visto.add(x)
            pila.append((x, True))
            c = self.p["certificados"].get(x)
            if not isinstance(c, dict):
                continue
            hijos = [c["procedencia"]] + [c["premisas"][n] for n in sorted(c["premisas"])]
            for h in reversed([h for h in hijos if isinstance(h, str)]):
                pila.append((h, False))
        return [x for x in orden if x != cid]

    def _uno(self, cid, ruta):
        if cid in self._validos:
            return self._validos[cid]
        if cid in self.p["registros"]:
            raise Rechazo("registro_como_premisa", ruta, "un registro histórico no es un certificado")
        if cid in self._en_curso:
            raise Rechazo("ciclo", ruta, cid[:12])
        self._en_curso.add(cid)
        try:
            c = self._obj("certificados", cid, ruta)
            self._certificado(c, ruta)
        finally:
            self._en_curso.discard(cid)
        self._validos[cid] = c
        return c

    # --- cada certificado (§6.1, 2–3) ---------------------------------------------------------------------

    def _certificado(self, c, ruta):
        a, suj = self.afirmacion(c["afirmacion"], ruta)
        S = self.instantanea(c["instantanea"], ruta)
        if c["semantica"] != a["semantica"] or S["semantica"] != a["semantica"]:
            raise Rechazo("semantica_distinta", ruta)
        if c["estado"] not in I.ESTADOS_POR_CLASE[a["clase"]]:
            raise Rechazo("estado_invalido", ruta, f"{a['clase']}: {c['estado']}")
        if c["cierre"] != self.cierre(a, suj, ruta):
            raise Rechazo("cierre_distinto", ruta)
        if c["base"] != self.base_de_clase(a, suj, S, ruta):
            raise Rechazo("base_distinta", ruta)
        self.vigente(c, S, ruta)
        regla = c["regla"]
        if regla == "directa":
            if c["objeto_verificado"] != suj[I.PRINCIPAL[a["clase"]]]["contenido"]:
                raise Rechazo("objeto_verificado_distinto", ruta)
            return
        if regla == "conservacion":
            o = self.validar(c["procedencia"], f"{ruta}/procedencia")
            if o["afirmacion"] != c["afirmacion"]:
                raise Rechazo("conservacion_afirmacion_distinta", ruta)
            if o["estado"] != c["estado"]:
                raise Rechazo("conservacion_estado_distinto", ruta)
            if o["base"] != c["base"]:
                raise Rechazo("base_distinta", ruta, "la conservación exige la misma base")
            return
        if a["clase"] != REGLA_CLASE[regla]:
            raise Rechazo("regla_clase_incompatible", ruta, f"{regla} sobre {a['clase']}")
        if a["clase"] not in I.TRANSFERIBLES:
            raise Rechazo("clase_no_transferible", ruta, a["clase"])
        {"R-PROP": self._r_prop, "R-REAL": self._r_real, "R-REFUT": self._r_refut}[regla](c, a, suj, S, ruta)

    def _origen(self, c, clase, ruta, usados):
        usados.add("origen")
        if "origen" not in c["premisas"]:
            raise Rechazo("premisa_ausente", ruta, "origen")
        rp = f"{ruta}/origen"
        o = self.validar(c["premisas"]["origen"], rp)
        oa, osuj = self.afirmacion(o["afirmacion"], rp)
        if oa["clase"] != clase:
            raise Rechazo("premisa_clase", rp, oa["clase"])
        if o["estado"] != c["estado"]:
            raise Rechazo("premisa_estado", rp, "el origen tiene otro estado")
        if o["base"] != c["base"]:
            raise Rechazo("base_distinta", ruta, "la base de la clase cambió entre S_a y S_d")
        return o, oa, osuj, self.instantanea(o["instantanea"], rp)

    def _premisa(self, c, nombre, clase, sujetos, S, ruta, usados):
        """Premisa `nombre`: válida, de `clase` con exactamente esos sujetos (por id de revisión), `probado` y
        vigente en S. Devuelve (certificado, afirmación)."""
        usados.add(nombre)
        if nombre not in c["premisas"]:
            raise Rechazo("premisa_ausente", ruta, nombre)
        rp = f"{ruta}/{nombre}"
        p = self.validar(c["premisas"][nombre], rp)
        pa, psuj = self.afirmacion(p["afirmacion"], rp)
        if pa["clase"] != clase or set(psuj) != set(sujetos) or any(psuj[x]["id"] != v["id"]
                                                                    for x, v in sujetos.items()):
            raise Rechazo("premisa_clase", rp, f"se esperaba {clase} sobre {sorted(sujetos)}")
        if p["estado"] != "probado":
            raise Rechazo("premisa_estado", rp, p["estado"])
        self.vigente(p, S, rp)
        return p, pa

    def _sobrantes(self, c, usados, ruta):
        sobra = set(c["premisas"]) - usados
        if sobra:
            raise Rechazo("premisa_sobrante", ruta, ", ".join(sorted(sobra)))

    def _misma_ranura_y_firma(self, va, vd, ruta):
        if va["ranura"] != vd["ranura"]:
            raise Rechazo("ranura_distinta", ruta)
        if va["firma"] != vd["firma"]:
            raise Rechazo("firma_distinta", ruta)

    def _r_prop(self, c, a, suj, Sd, ruta):
        usados = set()
        o, oa, osuj, Sa = self._origen(c, "PROP", ruta, usados)
        pa, pd = osuj["propiedad"], suj["propiedad"]
        self._misma_ranura_y_firma(pa, pd, ruta)
        if pa["forma_fuente"] != pd["forma_fuente"]:
            raise Rechazo("fuente_distinta", ruta, "la propiedad cambió de fuente")
        ca, cd = o["cierre"], c["cierre"]
        if set(ca) != set(cd):
            raise Rechazo("ranura_nueva", ruta, "el cierre gana o pierde ranuras")
        for r in sorted(x for x in ca if ca[x] != cd[x]):
            if r == pd["ranura"]:
                continue                     # la propia propiedad: su fuente ya se comprobó
            if self.ranura(r, ruta)["tipo"] != "computacion":
                raise Rechazo("cambio_no_cubierto", ruta, r[:12])
            va, vd = self.revision(ca[r], ruta), self.revision(cd[r], ruta)
            self._premisa(c, f"eq:{r}", "EQ", {"nueva": vd, "anterior": va}, Sd, ruta, usados)
            self._premisa(c, f"wd_a:{r}", "WD", {"objeto": va}, Sa, ruta, usados)
            self._premisa(c, f"wd_d:{r}", "WD", {"objeto": vd}, Sd, ruta, usados)
        self._sobrantes(c, usados, ruta)

    def _candidata_y_f(self, osuj, suj, ruta):
        if osuj["candidata"]["id"] != suj["candidata"]["id"]:
            raise Rechazo("candidata_distinta", ruta)
        fa, fd = osuj["computacion"], suj["computacion"]
        self._misma_ranura_y_firma(fa, fd, ruta)
        return fa, fd

    def _r_real(self, c, a, suj, Sd, ruta):
        usados = set()
        o, oa, osuj, Sa = self._origen(c, "REAL", ruta, usados)
        fa, fd = self._candidata_y_f(osuj, suj, ruta)
        # Todo cambio del cierre (ganado, perdido o distinto) está en f o en lo que expande f (§6, R-REAL).
        cubiertas = {fd["ranura"], *fa["dependencias"], *fd["dependencias"]}
        ca, cd = o["cierre"], c["cierre"]
        for r in sorted(set(ca) | set(cd)):
            if ca.get(r) != cd.get(r) and r not in cubiertas:
                raise Rechazo("cambio_no_cubierto", ruta, r[:12])
        self._premisa(c, "eq", "EQ", {"nueva": fd, "anterior": fa}, Sd, ruta, usados)
        self._premisa(c, "wd_a", "WD", {"objeto": fa}, Sa, ruta, usados)
        self._premisa(c, "wd_c", "WD", {"objeto": suj["candidata"]}, Sd, ruta, usados)
        self._sobrantes(c, usados, ruta)

    def _r_refut(self, c, a, suj, Sd, ruta):
        usados = set()
        o, oa, osuj, Sa = self._origen(c, "REFUT", ruta, usados)
        fa, fd = self._candidata_y_f(osuj, suj, ruta)
        if not I.iguales(oa["contexto"], a["contexto"]):
            raise Rechazo("testigo_distinto", ruta)
        e, ea = self._premisa(c, "evaluacion", "REFUT", suj, Sd, ruta, usados)
        if ea["id"] != a["id"] or e["regla"] != "directa":
            raise Rechazo("evaluacion_no_directa", f"{ruta}/evaluacion",
                          "hace falta la reevaluación directa del mismo testigo en S_d")
        if "eq" in c["premisas"]:                      # premisa opcional admitida (§6, R-REFUT)
            self._premisa(c, "eq", "EQ", {"nueva": fd, "anterior": fa}, Sd, ruta, usados)
        self._sobrantes(c, usados, ruta)

    # --- uso (§6.1, 4) ------------------------------------------------------------------------------------

    def reutilizable(self, cid, instantanea_id, ruta="uso"):
        c = self.validar(cid, ruta)
        self.vigente(c, self.instantanea(instantanea_id, ruta), ruta)
        return c


def componentes_de_clase(clase, tipos_sujetos):
    """Componentes de la base de una clase (§3.3) dados los tipos de ranura de sus sujetos, en orden."""
    comps = set(I.BASE_POR_CLASE[clase])
    if "candidata-lang" in tipos_sujetos:
        comps |= set(I.EXTRA_LANG)
        if clase == "REAL":
            comps |= set(I.EXTRA_REAL_LANG)
    return sorted(comps)


def validar(paquete, cid):
    """None si el certificado es válido en el paquete; si no, el Rechazo."""
    try:
        Validador(paquete).validar(cid)
    except Rechazo as e:
        return e
    return None


# --- almacén y constructores ---------------------------------------------------------------------------------

class Almacen:
    """Objetos del contrato por tabla (en memoria). Solo se añaden; un objeto con el mismo id y otro contenido es un
    error (`hash_invalido`). `paquete_de(ids)` exporta todo lo que referencian esos certificados y registros."""

    def __init__(self):
        self.t = {t: {} for t in I.TABLAS}

    def poner(self, tipo, obj):
        tabla = I.TABLA_DE[tipo]
        previo = self.t[tabla].get(obj["id"])
        if previo is not None and previo != obj:
            raise Rechazo("hash_invalido", "almacen", f"{tipo} {obj['id'][:12]} ya existe con otro contenido")
        self.t[tabla][obj["id"]] = obj
        return obj

    def ranura(self, x):
        return self.poner("ranura", x)

    def revision(self, x):
        return self.poner("revision", x)

    def instantanea(self, x):
        return self.poner("instantanea", x)

    def afirmacion(self, x):
        return self.poner("afirmacion", x)

    def get(self, tabla, oid):
        return self.t[tabla].get(oid)

    def poner_formas(self, formas):
        for r in formas.ranuras.values():
            self.ranura(r)
        for v in formas.revisiones.values():
            self.revision(v)

    def cargar(self, paquete, validar_forma=True):
        """Añade las filas de un paquete; con `validar_forma`, descarta (y devuelve) las mal formadas o cuyo índice
        no es su id, para que una fila dañada no rechace el resto."""
        descartados = []
        for t in sorted(I.TABLAS):
            for i, x in sorted((paquete or {}).get(t, {}).items()):
                try:
                    if validar_forma:
                        I.VALIDAR[I.TABLAS[t]](x, f"{t}/{i[:12]}")
                        if x["id"] != i:
                            raise Rechazo("hash_invalido", f"{t}/{i[:12]}", "índice distinto del id")
                    self.poner(I.TABLAS[t], x)
                except Rechazo as e:
                    descartados.append((t, i, e.codigo))
        return descartados

    def paquete(self):
        return I.paquete(*(self.t[t].values() for t in ("ranuras", "revisiones", "instantaneas", "afirmaciones",
                                                        "certificados", "registros")))

    def paquete_de(self, ids, extra_instantaneas=()):
        """Paquete con los certificados y registros `ids`, toda su cadena y lo que referencian (afirmaciones,
        revisiones con sus dependencias, ranuras e instantáneas), más las instantáneas `extra_instantaneas`."""
        certs, regs, afs, revs, insts = {}, {}, {}, {}, {}
        pila = list(ids)
        while pila:
            x = pila.pop()
            if x in certs or x in regs:
                continue
            c = self.t["certificados"].get(x)
            if c is not None:
                certs[x] = c
                pila += [h for h in [c["procedencia"], *c["premisas"].values()] if h]
                afs[c["afirmacion"]] = self.t["afirmaciones"].get(c["afirmacion"])
                insts[c["instantanea"]] = self.t["instantaneas"].get(c["instantanea"])
                continue
            r = self.t["registros"].get(x)
            if r is not None:
                regs[x] = r
                if r["origen"]:
                    pila.append(r["origen"])
                afs[r["afirmacion"]] = self.t["afirmaciones"].get(r["afirmacion"])
                insts[r["instantanea"]] = self.t["instantaneas"].get(r["instantanea"])
        for s in extra_instantaneas:
            insts[s] = self.t["instantaneas"].get(s)
        for a in afs.values():
            if a is not None:
                for v in a["sujetos"].values():
                    revs[v] = self.t["revisiones"].get(v)
        for v in list(revs.values()):
            if v is not None:
                for d in v["dependencias"].values():
                    revs[d] = self.t["revisiones"].get(d)
        ranuras = {}
        for v in revs.values():
            if v is not None:
                for rk in [v["ranura"], *v["dependencias"]]:
                    ranuras[rk] = self.t["ranuras"].get(rk)
        for r in list(ranuras.values()):            # el ámbito de cada candidata (v2.7, §2.2)
            if r is not None and r["tipo"] in I.CANDIDATAS:
                ranuras[r["ambito"]] = self.t["ranuras"].get(r["ambito"])
        quitar_nulos = lambda d: [x for x in d.values() if x is not None]  # noqa: E731
        return I.paquete(quitar_nulos(ranuras), quitar_nulos(revs), quitar_nulos(insts), quitar_nulos(afs),
                         certs.values(), regs.values())

    # --- consultas ---------------------------------------------------------------------------------------------

    def sujetos(self, af):
        return {p: self.t["revisiones"][i] for p, i in af["sujetos"].items()}

    def cierre(self, af):
        c = I.cierre_de([self.t["revisiones"][af["sujetos"][p]] for p in I.PAPELES_CIERRE[af["clase"]]])
        if c is None:
            raise Rechazo("cierre_incoherente", "almacen", "una ranura con dos revisiones")
        return c

    def base(self, af, S):
        tipos = {self.t["ranuras"][v["ranura"]]["tipo"] for v in self.sujetos(af).values()}
        return {c: S["base"][c] for c in componentes_de_clase(af["clase"], tipos) if c in S["base"]}

    def reutilizable(self, cid, S):
        """None si `cid` es reutilizable en la instantánea S (validez de toda su cadena y vigencia); si no, el
        Rechazo. Es la comprobación que exige §6 antes de reutilizar nada, también desde la caché."""
        sid = S if isinstance(S, str) else S["id"]
        try:
            Validador(self.paquete_de([cid], [sid])).reutilizable(cid, sid)
        except Rechazo as e:
            return e
        return None

    def publicar(self, c):
        """Añade el certificado solo si es válido con toda su cadena. Devuelve el certificado o lanza Rechazo."""
        previo = self.t["certificados"].get(c["id"])
        if previo is not None and previo != c:
            raise Rechazo("hash_invalido", "publicar", "id ya publicado con otro contenido")
        self.t["certificados"][c["id"]] = c
        try:
            Validador(self.paquete_de([c["id"]])).validar(c["id"])
        except Rechazo:
            if previo is None:
                del self.t["certificados"][c["id"]]
            raise
        return c

    def anotar(self, r):
        """Añade un registro histórico (§3.4) tras validar su forma; su origen, si lo hay, tiene que ser un registro
        del almacén de la misma afirmación."""
        I.validar_registro(r)
        if r["origen"] is not None:
            o = self.t["registros"].get(r["origen"])
            if o is None or o["afirmacion"] != r["afirmacion"]:
                raise Rechazo("procedencia_invalida", "anotar", "el origen de un registro es un registro de la "
                                                                "misma afirmación")
        return self.poner("registro", r)


def _certificado(alm, af, estado, via, regla, S, objeto_verificado=None, premisas=None, procedencia=None):
    alm.afirmacion(af)
    alm.instantanea(S)
    return alm.publicar(I.certificado(af, estado, via, regla, S, alm.base(af, S), alm.cierre(af), objeto_verificado,
                                      premisas, procedencia))


def directa(alm, af, S, estado, objeto_verificado):
    """Hoja directa: el veredicto de un verificador sobre `objeto_verificado`, que tiene que ser el contenido del
    sujeto principal (D9). Solo `probado`/`refutado` admitidos por la clase; lo demás es un registro."""
    return _certificado(alm, af, estado, "directa", "directa", S, objeto_verificado)


def conservar(alm, af, origen, S, via="conservada"):
    """Conservación (`conservada` o `cache`): misma afirmación, estado y base que el origen, vigente en S."""
    origen = origen if isinstance(origen, dict) else alm.t["certificados"][origen]
    return _certificado(alm, af, origen["estado"], via, "conservacion", S, procedencia=origen)


def r_prop(alm, af_d, origen, premisas, S_d):
    """`premisas`: {"eq:<ranura>", "wd_a:<ranura>", "wd_d:<ranura>": certificado} (sin `origen`)."""
    return _certificado(alm, af_d, origen["estado"], "transferida", "R-PROP", S_d,
                        premisas={"origen": origen, **premisas}, procedencia=origen)


def r_real(alm, af_d, origen, eq, wd_a, wd_c, S_d):
    return _certificado(alm, af_d, "probado", "transferida", "R-REAL", S_d,
                        premisas={"origen": origen, "eq": eq, "wd_a": wd_a, "wd_c": wd_c}, procedencia=origen)


def r_refut(alm, af_d, origen, evaluacion, S_d, eq=None):
    prem = {"origen": origen, "evaluacion": evaluacion, **({"eq": eq} if eq is not None else {})}
    return _certificado(alm, af_d, "probado", "transferida", "R-REFUT", S_d, premisas=prem, procedencia=origen)
