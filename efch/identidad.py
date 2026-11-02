"""
Identidad y contrato de intercambio de la referencia (especificacion/ESPECIFICACION.md v2.5, §2–§4). Puro: sin E/S,
sin solucionador y sin intérprete. Lo usan `efch.reglas` (el comprobador propio de §5–§6), B1-v2, `store` y
`pipeline`. No importa `especificacion`: está escrito desde el texto y el código normativos y se contrasta con los
97 vectores, `canonicos.json` y la muestra de la exploración (tests/test_conformidad_referencia.py).

Tres partes:
1. **Forma canónica y entrada textual** (§2.1): dominio canónico (profundidad ≤ 32 comprobada sin recursión,
   enteros en [-2^63, 2^128), texto UTF-8 sin normalizar, sin coma flotante), bytes canónicos, ids y el decodificador
   de bytes (UTF-8 estricto; profundidad y cifras antes de convertir; un único valor sin duplicados ni no enteros).
2. **Objetos y validación de forma** (§2.2, §2.3, §3, §4): ranura, revisión, instantánea, afirmación, certificado,
   registro y paquete, como diccionarios JSON; la validación sigue la precedencia normativa de 9 pasos y da siempre
   el mismo código (`Rechazo.codigo`, §7).
3. **Formas de EFCH 0.1** (§2.2, procedimiento único): `forma_canonica`, `fuente`, `firma` y `dependencias` de
   computaciones, propiedades y candidatas (también las traducidas desde EFCH Lang), con `efch.core` y
   `efch.sexpr`; las dependencias son las listas `(call NOMBRE …)` de la fuente, como árbol, resueltas en la
   definición y cerradas transitivamente.

Los identificadores solo se comparan; nunca se analizan.
"""

import hashlib
import json

from . import core, sexpr

# --- 1. Forma canónica y entrada textual (§2.1) ----------------------------------------------------------

ENTERO_MIN, ENTERO_MAX = -(2 ** 63), 2 ** 128
PROFUNDIDAD_MAX = 32
CIFRAS_MAX = 39                    # 2^128 tiene 39 cifras


class NoCanonico(ValueError):
    """Valor fuera del dominio canónico, o entrada textual que no lo decodifica (§2.1)."""


def _profundidad(x):
    pila = [(x, 1)]
    while pila:
        v, d = pila.pop()
        if isinstance(v, (dict, list)):
            if d > PROFUNDIDAD_MAX:
                raise NoCanonico(f"anidamiento de más de {PROFUNDIDAD_MAX} niveles")
            pila.extend((h, d + 1) for h in (v.values() if isinstance(v, dict) else v))


def comprobar_dominio(x):
    """Primero la profundidad; después, en preorden y con las claves de cada objeto ordenadas, el primer valor fuera
    del dominio (§2.1)."""
    _profundidad(x)
    pila = [(x, "$")]
    while pila:
        v, ruta = pila.pop()
        if v is None or isinstance(v, bool):
            continue
        if isinstance(v, int):
            if not ENTERO_MIN <= v < ENTERO_MAX:
                raise NoCanonico(f"{ruta}: entero fuera de [-2^63, 2^128)")
        elif isinstance(v, float):
            raise NoCanonico(f"{ruta}: número de coma flotante")
        elif isinstance(v, str):
            try:
                v.encode("utf-8")
            except UnicodeEncodeError:
                raise NoCanonico(f"{ruta}: sustituto Unicode aislado") from None
        elif isinstance(v, list):
            for i in range(len(v) - 1, -1, -1):
                pila.append((v[i], f"{ruta}[{i}]"))
        elif isinstance(v, dict):
            if any(not isinstance(c, str) for c in v):
                raise NoCanonico(f"{ruta}: clave no textual")
            for c in sorted(v, reverse=True):
                pila.append((v[c], f"{ruta}.{c}"))
                pila.append((c, f"{ruta}.<clave>"))
        else:
            raise NoCanonico(f"{ruta}: tipo {type(v).__name__} fuera del dominio")


def canonico(obj):
    """Bytes canónicos: json.dumps con claves ordenadas, sin escapar lo no ASCII y sin espacios, en UTF-8."""
    comprobar_dominio(obj)
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":"), allow_nan=False).encode()


def sha(datos):
    return hashlib.sha256(datos.encode() if isinstance(datos, str) else datos).hexdigest()


def hash_objeto(obj, excluidos=("id",)):
    return sha(canonico({c: v for c, v in obj.items() if c not in excluidos}))


def con_id(obj, excluidos=("id",)):
    sin = {c: v for c, v in obj.items() if c != "id"}
    return {**sin, "id": hash_objeto(sin, excluidos)}


def iguales(a, b):
    """Igualdad del contrato: la de los bytes canónicos (`false` ≠ `0`)."""
    return canonico(a) == canonico(b)


def es_hash(x):
    return isinstance(x, str) and len(x) == 64 and all(c in "0123456789abcdef" for c in x)


def _explorar(texto):
    """Sin convertir nada y sin recursión: profundidad de anidamiento y cifras de cada número."""
    prof, i, n, cadena = 0, 0, len(texto), False
    while i < n:
        c = texto[i]
        if cadena:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                cadena = False
        elif c == '"':
            cadena = True
        elif c in "[{":
            prof += 1
            if prof > PROFUNDIDAD_MAX:
                raise NoCanonico(f"anidamiento de más de {PROFUNDIDAD_MAX} niveles")
        elif c in "]}":
            prof -= 1
        elif c == "-" or c.isascii() and c.isdigit():
            j = i + 1 if c == "-" else i
            inicio = j
            while j < n and texto[j].isascii() and texto[j].isdigit():
                j += 1
            if j - inicio > CIFRAS_MAX:
                raise NoCanonico("entero fuera de rango")
            i = j
            continue
        i += 1


def decodificar(datos):
    """Entrada textual normativa (§2.1): bytes → valor JSON en el dominio canónico, o NoCanonico. Texto de Python
    (str) es un error de uso: TypeError."""
    if not isinstance(datos, (bytes, bytearray)):
        raise TypeError("la entrada normativa son bytes")
    try:
        texto = bytes(datos).decode("utf-8", errors="strict")
    except UnicodeDecodeError as e:
        raise NoCanonico(f"UTF-8 inválido: {e}") from None
    _explorar(texto)

    def objeto(pares):
        out = {}
        for c, v in pares:
            if c in out:
                raise NoCanonico(f"clave duplicada {c!r}")
            out[c] = v
        return out

    def no_entero(x):
        raise NoCanonico(f"número no entero o no finito: {x}")

    try:
        valor = json.loads(texto, object_pairs_hook=objeto, parse_float=no_entero, parse_constant=no_entero)
    except json.JSONDecodeError as e:
        raise NoCanonico(f"JSON inválido: {e}") from None
    comprobar_dominio(valor)
    return valor


# --- 2. Objetos del contrato (§2.2–§3) ------------------------------------------------------------------

ESQUEMA = "efch-evidencia/2.5"
SEMANTICA = f"efch-{core.LANGUAGE_VERSION}"
SEMANTICAS = (SEMANTICA,)

TIPOS_RANURA = ("computacion", "propiedad", "candidata", "candidata-lang")
CANDIDATAS = ("candidata", "candidata-lang")
PAPELES = {
    "WD": {"objeto": ("computacion",) + CANDIDATAS},
    "EQ": {"nueva": ("computacion",), "anterior": ("computacion",)},
    "PROP": {"propiedad": ("propiedad",)},
    "REAL": {"candidata": CANDIDATAS, "computacion": ("computacion",)},
    "REFUT": {"candidata": CANDIDATAS, "computacion": ("computacion",)},
    "INV": {"objeto": ("computacion",)},
    "CBMC": {"candidata": CANDIDATAS, "computacion": ("computacion",)},
    "TRADUCCION-C": {"objeto": ("computacion",) + CANDIDATAS},
    "RENDIMIENTO": {"objeto": ("computacion",) + CANDIDATAS},
}
CLASES = tuple(PAPELES)
# EQ relaciona dos instantáneas: su cierre es el de `nueva`; `anterior` es histórica y no tiene que estar vigente.
PAPELES_CIERRE = {c: ("nueva",) if c == "EQ" else tuple(sorted(p)) for c, p in PAPELES.items()}
PRINCIPAL = {"WD": "objeto", "EQ": "nueva", "PROP": "propiedad", "REAL": "candidata", "REFUT": "candidata",
             "INV": "objeto", "CBMC": "candidata", "TRADUCCION-C": "objeto", "RENDIMIENTO": "objeto"}
TRANSFERIBLES = ("PROP", "REAL", "REFUT")

LOBS = "L-OBS"
CONTEXTO_FIJO = {"WD": {}, "EQ": {"direccion": "d->a"}, "PROP": {"supuestos": [LOBS]}, "REAL": {}, "INV": {},
                 "CBMC": {}, "TRADUCCION-C": {}, "RENDIMIENTO": {}}          # REFUT: exactamente {"testigo": {…}}

# Base de confianza por clase (§3.3, D-2). Qué identifica cada componente lo fija el productor de la instantánea
# (resultados/p1/bases.md).
_NUCLEO = ("efch-core", "efch-smt", "efch-interp", "z3", "ejecutor", "reglas")
BASE_POR_CLASE = {
    "WD": _NUCLEO, "EQ": _NUCLEO, "PROP": _NUCLEO, "REAL": _NUCLEO, "INV": _NUCLEO,
    "REFUT": ("efch-core", "efch-interp", "ejecutor", "reglas"),
    "CBMC": ("efch-core", "efch-c", "cbmc", "ejecutor", "reglas"),
    "TRADUCCION-C": ("efch-core", "efch-c", "gcc", "abi", "ejecutor", "reglas"),
    "RENDIMIENTO": ("efch-c", "gcc", "abi", "cpu", "workload", "ejecutor", "reglas"),
}
EXTRA_LANG = ("traductor",)                  # algún sujeto es candidata-lang
EXTRA_REAL_LANG = ("efch-c", "cbmc")         # REAL de candidata-lang: lang.verify recurre a CBMC (D-20)
COMPONENTES = tuple(sorted({x for v in BASE_POR_CLASE.values() for x in v} | set(EXTRA_LANG) | set(EXTRA_REAL_LANG)))

ESTADOS_CERTIFICADO = ("probado", "refutado")
ESTADOS_POR_CLASE = {c: ESTADOS_CERTIFICADO for c in CLASES}
ESTADOS_POR_CLASE.update({"REAL": ("probado",), "REFUT": ("probado",), "RENDIMIENTO": ("probado",)})
ESTADOS_REGISTRO = ("probado", "refutado", "desconocido", "no comprobado", "fuera de alcance",
                    "evidencia experimental")
VIA_REGLA = {"directa": ("directa",), "conservada": ("conservacion",), "cache": ("conservacion",),
             "transferida": ("R-PROP", "R-REAL", "R-REFUT")}
VIAS_REGISTRO = ("directa", "conservada-operativa")

CAMPOS = {
    "ranura": ("esquema", "tipo", "ambito", "nombre", "id"),
    "revision": ("esquema", "semantica", "ranura", "contenido", "forma_canonica", "fuente", "forma_fuente", "firma",
                 "dependencias", "id"),
    "instantanea": ("esquema", "semantica", "revisiones", "base", "id"),
    "afirmacion": ("esquema", "semantica", "clase", "sujetos", "contexto", "id"),
    "certificado": ("esquema", "semantica", "afirmacion", "estado", "via", "regla", "instantanea", "base", "cierre",
                    "objeto_verificado", "premisas", "procedencia", "id"),
    "registro": ("esquema", "semantica", "afirmacion", "resultado", "via", "instantanea", "origen", "mediciones",
                 "id"),
}
_C = {"esquema": "texto", "semantica": "texto", "id": "hash"}
TIPOS_CAMPO = {
    "ranura": {"esquema": "texto", "id": "hash", "tipo": "texto", "ambito": "ambito", "nombre": "texto"},
    "revision": {**_C, "ranura": "hash", "contenido": "hash", "forma_canonica": "texto", "fuente": "texto",
                 "forma_fuente": "hash", "firma": "texto", "dependencias": "objeto"},
    "instantanea": {**_C, "revisiones": "objeto", "base": "objeto"},
    "afirmacion": {**_C, "clase": "texto", "sujetos": "objeto", "contexto": "objeto"},
    "certificado": {**_C, "afirmacion": "hash", "estado": "texto", "via": "texto", "regla": "texto",
                    "instantanea": "hash", "base": "objeto", "cierre": "objeto", "objeto_verificado": "hash?",
                    "premisas": "objeto", "procedencia": "hash?"},
    "registro": {**_C, "afirmacion": "hash", "resultado": "texto", "via": "texto", "instantanea": "hash",
                 "origen": "hash?", "mediciones": "objeto"},
}
EXCLUIDOS = {"registro": ("id", "mediciones")}      # fuera del hash, pero se validan (§2.1)
TABLAS = {"afirmaciones": "afirmacion", "certificados": "certificado", "instantaneas": "instantanea",
          "ranuras": "ranura", "registros": "registro", "revisiones": "revision"}
TABLA_DE = {v: c for c, v in TABLAS.items()}


class Rechazo(Exception):
    """Rechazo con código normativo (§7), la ruta que llevó a él y un detalle legible."""

    def __init__(self, codigo, ruta="", detalle=""):
        super().__init__(f"{codigo} en {ruta}: {detalle}" if detalle else f"{codigo} en {ruta}")
        self.codigo, self.ruta, self.detalle = codigo, ruta, detalle

    def a_dict(self):
        return {"codigo": self.codigo, "ruta": self.ruta, "detalle": self.detalle}


def ranura(tipo, nombre, ambito=""):
    return con_id({"esquema": ESQUEMA, "tipo": tipo, "ambito": ambito, "nombre": nombre})


def ranura_computacion(nombre):
    return ranura("computacion", nombre)


def ranura_propiedad(nombre):
    return ranura("propiedad", nombre)


def ranura_candidata(nombre, computacion, tipo="candidata"):
    return ranura(tipo, nombre, ranura_computacion(computacion)["id"])


def revision(ranura_, forma_canonica, fuente, firma, dependencias, semantica=SEMANTICA):
    return con_id({"esquema": ESQUEMA, "semantica": semantica, "ranura": ranura_["id"],
                   "contenido": sha(forma_canonica), "forma_canonica": forma_canonica, "fuente": fuente,
                   "forma_fuente": sha(fuente), "firma": firma, "dependencias": dict(dependencias)})


def instantanea(revisiones, base, semantica=SEMANTICA):
    """`revisiones`: revisiones (objetos); se guarda {ranura: id de revisión}. Una ranura con dos revisiones es un
    error de quien la construye."""
    m = {}
    for r in revisiones:
        if m.setdefault(r["ranura"], r["id"]) != r["id"]:
            raise ValueError("una instantánea con dos revisiones de la misma ranura")
    return con_id({"esquema": ESQUEMA, "semantica": semantica, "revisiones": m, "base": dict(base)})


def afirmacion(clase, contexto=None, semantica=SEMANTICA, **sujetos):
    """`sujetos`: {papel: revisión (objeto) o id de revisión}. Sin `contexto`, el fijo de la clase (§3.2)."""
    ctx = CONTEXTO_FIJO.get(clase, {}) if contexto is None else contexto
    return con_id({"esquema": ESQUEMA, "semantica": semantica, "clase": clase,
                   "sujetos": {p: r if isinstance(r, str) else r["id"] for p, r in sujetos.items()},
                   "contexto": ctx})


def certificado(af, estado, via, regla, inst, base, cierre, objeto_verificado=None, premisas=None,
                procedencia=None):
    """`premisas`: {nombre: certificado o id}; `procedencia`: certificado o id."""
    ident = lambda x: x if isinstance(x, str) or x is None else x["id"]  # noqa: E731
    return con_id({"esquema": ESQUEMA, "semantica": af["semantica"], "afirmacion": af["id"], "estado": estado,
                   "via": via, "regla": regla, "instantanea": ident(inst), "base": dict(base),
                   "cierre": dict(cierre), "objeto_verificado": objeto_verificado,
                   "premisas": {p: ident(c) for p, c in (premisas or {}).items()},
                   "procedencia": ident(procedencia)})


def registro(af, resultado, via, inst, origen=None, mediciones=None):
    """Registro histórico (§3.4, D-3): nunca es premisa ni procedencia. Las mediciones quedan fuera del hash."""
    return con_id({"esquema": ESQUEMA, "semantica": af["semantica"], "afirmacion": af["id"],
                   "resultado": resultado, "via": via,
                   "instantanea": inst if isinstance(inst, str) else inst["id"],
                   "origen": origen if isinstance(origen, str) or origen is None else origen["id"],
                   "mediciones": dict(mediciones or {})}, EXCLUIDOS["registro"])


def paquete(ranuras=(), revisiones=(), instantaneas=(), afirmaciones=(), certificados=(), registros=()):
    """Paquete de intercambio (§2.3): exactamente las seis tablas, indexadas por id, y el esquema."""
    tabla = lambda xs: {x["id"]: x for x in sorted(xs, key=lambda x: x["id"])}  # noqa: E731
    return {"esquema": ESQUEMA, "ranuras": tabla(ranuras), "revisiones": tabla(revisiones),
            "instantaneas": tabla(instantaneas), "afirmaciones": tabla(afirmaciones),
            "certificados": tabla(certificados), "registros": tabla(registros)}


# --- validación de forma (§4.1) -----------------------------------------------------------------------------

def _tipo_ok(x, t):
    if t == "texto":
        return isinstance(x, str)
    if t == "hash":
        return es_hash(x)
    if t == "hash?":
        return x is None or es_hash(x)
    if t == "ambito":
        return x == "" or es_hash(x)
    return isinstance(x, dict)


def _pasos_1_a_8(tipo, obj, ruta):
    if not isinstance(obj, dict):
        raise Rechazo("tipo_invalido", ruta, "no es un objeto")
    if obj.get("esquema") != ESQUEMA:
        raise Rechazo("esquema_desconocido", ruta, repr(obj.get("esquema"))[:80])
    esperados = set(CAMPOS[tipo])
    if esperados - set(obj):
        raise Rechazo("campo_ausente", ruta, ", ".join(sorted(esperados - set(obj))))
    if set(obj) - esperados:
        raise Rechazo("campo_desconocido", ruta, ", ".join(sorted(map(str, set(obj) - esperados)))[:200])
    tipos = TIPOS_CAMPO[tipo]
    for campo in sorted(tipos):
        if not _tipo_ok(obj[campo], tipos[campo]):
            raise Rechazo("tipo_invalido", ruta, f"{campo}: se esperaba {tipos[campo]}")
    if "semantica" in esperados and obj["semantica"] not in SEMANTICAS:
        raise Rechazo("semantica_desconocida", ruta, repr(obj["semantica"])[:80])
    try:
        canonico(obj)
        h = hash_objeto(obj, EXCLUIDOS.get(tipo, ("id",)))
    except NoCanonico as e:
        raise Rechazo("no_canonico", ruta, str(e)) from None
    if obj["id"] != h:
        raise Rechazo("hash_invalido", ruta, f"id {obj['id'][:12]}…, calculado {h[:12]}…")


def _mapa_hashes(m, ruta, campo):
    for c in sorted(m):
        if not es_hash(c) or not es_hash(m[c]):
            raise Rechazo("tipo_invalido", ruta, f"{campo}: claves y valores tienen que ser hashes")


def _base(b, ruta):
    for c in sorted(b):
        if c not in COMPONENTES:
            raise Rechazo("componente_desconocido", ruta, c)
        if not isinstance(b[c], str):
            raise Rechazo("tipo_invalido", ruta, f"base.{c} no es texto")


def validar_ranura(r, ruta="ranura"):
    _pasos_1_a_8("ranura", r, ruta)
    if r["tipo"] not in TIPOS_RANURA:
        raise Rechazo("tipo_invalido", ruta, f"tipo de ranura {r['tipo']!r}")
    if r["nombre"] == "":
        raise Rechazo("tipo_invalido", ruta, "nombre vacío")
    if (r["tipo"] in CANDIDATAS) != es_hash(r["ambito"]):
        raise Rechazo("tipo_invalido", ruta, "el ámbito es la computación de una candidata y vacío en lo demás")


def validar_revision(v, ruta="revision"):
    _pasos_1_a_8("revision", v, ruta)
    if v["contenido"] != sha(v["forma_canonica"]):
        raise Rechazo("contenido_invalido", ruta, "contenido ≠ sha256(forma_canonica)")
    if v["forma_fuente"] != sha(v["fuente"]):
        raise Rechazo("fuente_invalida", ruta, "forma_fuente ≠ sha256(fuente)")
    _mapa_hashes(v["dependencias"], ruta, "dependencias")
    if v["ranura"] in v["dependencias"]:
        raise Rechazo("tipo_invalido", ruta, "una revisión no depende de su propia ranura")


def validar_instantanea(s, ruta="instantanea"):
    _pasos_1_a_8("instantanea", s, ruta)
    _mapa_hashes(s["revisiones"], ruta, "revisiones")
    _base(s["base"], ruta)


def valor_entrada(x):
    """Valor de un testigo (§3.2): booleano, entero no negativo (bv) o lista de bytes."""
    if isinstance(x, bool):
        return True
    if isinstance(x, int):
        return x >= 0
    return isinstance(x, list) and all(isinstance(b, int) and not isinstance(b, bool) and 0 <= b < 256 for b in x)


def validar_afirmacion(a, ruta="afirmacion"):
    _pasos_1_a_8("afirmacion", a, ruta)
    if a["clase"] not in CLASES:
        raise Rechazo("clase_desconocida", ruta, repr(a["clase"])[:80])
    if set(a["sujetos"]) != set(PAPELES[a["clase"]]):
        raise Rechazo("papel_invalido", ruta, f"papeles {sorted(a['sujetos'])}")
    for p in sorted(a["sujetos"]):
        if not es_hash(a["sujetos"][p]):
            raise Rechazo("tipo_invalido", ruta, f"sujetos.{p} no es un hash")
    ctx = a["contexto"]
    if a["clase"] == "REFUT":
        if set(ctx) != {"testigo"} or not isinstance(ctx["testigo"], dict):
            raise Rechazo("contexto_no_fijo", ruta, "REFUT exige exactamente {testigo: {…}}")
        for c in sorted(ctx["testigo"]):
            if not valor_entrada(ctx["testigo"][c]):
                raise Rechazo("tipo_invalido", ruta, f"testigo.{c}")
    elif not iguales(ctx, CONTEXTO_FIJO[a["clase"]]):
        raise Rechazo("contexto_no_fijo", ruta, f"{a['clase']}: {json.dumps(ctx, ensure_ascii=False)[:120]}")


def validar_certificado(c, ruta="certificado"):
    _pasos_1_a_8("certificado", c, ruta)
    if c["estado"] not in ESTADOS_CERTIFICADO:
        raise Rechazo("estado_no_reutilizable", ruta, repr(c["estado"])[:80])
    if c["regla"] not in VIA_REGLA.get(c["via"], ()):
        raise Rechazo("via_regla_incompatible", ruta, f"{c['via']!r}/{c['regla']!r}"[:120])
    _base(c["base"], ruta)
    _mapa_hashes(c["cierre"], ruta, "cierre")
    for p in sorted(c["premisas"]):
        if not es_hash(c["premisas"][p]):
            raise Rechazo("tipo_invalido", ruta, f"premisas.{p} no es un hash")
    if c["regla"] == "directa":
        if c["objeto_verificado"] is None:
            raise Rechazo("tipo_invalido", ruta, "una hoja directa declara su objeto verificado")
        if c["premisas"] or c["procedencia"] is not None:
            raise Rechazo("premisa_sobrante", ruta, "una hoja directa no tiene premisas ni procedencia")
        return
    if c["objeto_verificado"] is not None:
        raise Rechazo("objeto_verificado_distinto", ruta, "solo una hoja directa declara objeto verificado")
    if c["procedencia"] is None:
        raise Rechazo("tipo_invalido", ruta, "una derivación declara su procedencia")
    if c["regla"] == "conservacion":
        if c["premisas"]:
            raise Rechazo("premisa_sobrante", ruta, "la conservación solo tiene procedencia")
    elif c["procedencia"] != c["premisas"].get("origen"):
        raise Rechazo("procedencia_invalida", ruta, "la procedencia de una transferencia es su premisa origen")


def validar_registro(r, ruta="registro"):
    _pasos_1_a_8("registro", r, ruta)
    if r["resultado"] not in ESTADOS_REGISTRO:
        raise Rechazo("tipo_invalido", ruta, f"resultado {r['resultado']!r}"[:80])
    if r["via"] not in VIAS_REGISTRO:
        raise Rechazo("tipo_invalido", ruta, f"vía {r['via']!r}"[:80])
    if (r["via"] == "directa") != (r["origen"] is None):
        raise Rechazo("procedencia_invalida", ruta, "solo un registro conservado declara origen")
    for c in sorted(r["mediciones"]):
        x = r["mediciones"][c]
        if not (x is None or isinstance(x, (str, int))):          # bool es int
            raise Rechazo("tipo_invalido", ruta, f"mediciones.{c}: solo texto, entero, booleano o null")


VALIDAR = {"ranura": validar_ranura, "revision": validar_revision, "instantanea": validar_instantanea,
           "afirmacion": validar_afirmacion, "certificado": validar_certificado, "registro": validar_registro}


def validar_contenedor(p, ruta="paquete"):
    """Contenedor del paquete (§4.1): objeto, esquema, tablas ausentes, claves de más y, por tabla en orden, que sea
    un objeto con índices hash."""
    if not isinstance(p, dict):
        raise Rechazo("tipo_invalido", ruta, "no es un objeto")
    if p.get("esquema") != ESQUEMA:
        raise Rechazo("esquema_desconocido", ruta, repr(p.get("esquema"))[:80])
    esperados = {"esquema", *TABLAS}
    if esperados - set(p):
        raise Rechazo("campo_ausente", ruta, ", ".join(sorted(esperados - set(p))))
    if set(p) - esperados:
        raise Rechazo("campo_desconocido", ruta, ", ".join(sorted(map(str, set(p) - esperados)))[:200])
    for t in sorted(TABLAS):
        if not isinstance(p[t], dict):
            raise Rechazo("tipo_invalido", ruta, f"{t} no es un objeto")
        for i in sorted(p[t]):
            if not es_hash(i):
                raise Rechazo("tipo_invalido", ruta, f"{t}: índice que no es un hash")


def prevalidar(p, ruta="paquete"):
    """Contenedor y prevalidación global (§4.1): cada fila de cada tabla, en orden de tabla y de id, por la forma de
    su objeto; después, índice = id. Un objeto mal formado rechaza el paquete entero."""
    validar_contenedor(p, ruta)
    for t in sorted(TABLAS):
        for i in sorted(p[t]):
            x = p[t][i]
            VALIDAR[TABLAS[t]](x, f"{ruta}<{t}/{i[:12]}>")
            if x["id"] != i:
                raise Rechazo("hash_invalido", ruta, f"{t}: índice {i[:12]} ≠ id {x['id'][:12]}")


# --- 3. Formas de EFCH 0.1 (§2.2, procedimiento único) ---------------------------------------------------

def llamadas(sx):
    """Nombres de las listas `(call SÍMBOLO …)` de un árbol de efch.sexpr, a cualquier profundidad (como árbol,
    nunca como texto)."""
    out, pila = set(), [sx]
    while pila:
        x = pila.pop()
        if isinstance(x, sexpr.SList):
            if len(x.items) >= 2 and x.head() == "call" and isinstance(x.items[1], sexpr.Sym):
                out.add(x.items[1].name)
            pila.extend(x.items)
    return out


def ligaduras(prop):
    return "(property (" + " ".join(f"({n} {core.type_str(t)})" for n, t in prop.variables) + "))"


def forma_canonica_propiedad(prop):
    return f"(efch {core.LANGUAGE_VERSION} {ligaduras(prop)} {core.canonical(prop.body, prop.variables)})"


def contenido_propiedad(prop):
    """Lo que recibe el verificador de una propiedad: sha256 de su forma canónica (§2.2)."""
    return sha(forma_canonica_propiedad(prop))


class RanuraRepetida(ValueError):
    """Dos objetos de una misma elaboración ocupan la misma ranura con revisiones distintas (§2.2, v2.7)."""


class Formas:
    """Revisiones (§2.2) de los objetos de una definición elaborada por `efch.core`. Las dependencias son el cierre
    transitivo {ranura: revisión} de las llamadas de la fuente, resueltas en la definición.

    Identidad (v2.7, §2.2): `ranuras` y `revisiones` se indexan por el **id de la ranura** (tipo, ámbito y nombre),
    nunca por el nombre. Dos candidatas homónimas de computaciones distintas son dos ranuras (K1). Una ranura con
    otra revisión en la misma elaboración (propiedades homónimas, o candidatas homónimas de la misma computación) se
    rechaza con `RanuraRepetida` (K2); con la misma revisión es un único objeto."""

    def __init__(self, defn, semantica=SEMANTICA):
        self.defn, self.semantica = defn, semantica
        self.ranuras = {}            # id de ranura -> ranura
        self.revisiones = {}         # id de ranura -> revisión
        self._en_curso = set()

    def _ranura(self, tipo, nombre, ambito=""):
        r = ranura(tipo, nombre, ambito)
        return self.ranuras.setdefault(r["id"], r)

    def _fijar(self, v, que):
        previa = self.revisiones.setdefault(v["ranura"], v)
        if previa["id"] != v["id"]:
            r = self.ranuras[v["ranura"]]
            raise RanuraRepetida(f"{que}: la ranura {r['tipo']} {r['nombre']!r} ya tiene otra revisión")
        return previa

    def ranura_computacion(self, nombre):
        return self._ranura("computacion", nombre)

    def _dependencias(self, sx, de):
        deps = {}
        for n in sorted(llamadas(sx)):
            if n not in self.defn.computations:
                raise ValueError(f"{de} llama a {n}, que no está en la definición")
            r = self.computacion(n)
            deps[r["ranura"]] = r["id"]
            deps.update(r["dependencias"])
        return deps

    def computacion(self, nombre):
        clave = self.ranura_computacion(nombre)["id"]
        if clave not in self.revisiones:
            if nombre in self._en_curso:
                raise ValueError(f"llamadas cíclicas en {nombre}")
            self._en_curso.add(nombre)
            try:
                comp = self.defn.computations[nombre]
                self._fijar(revision(self.ranura_computacion(nombre), comp.canonical(), sexpr.dumps(comp.source),
                                     comp.signature(), self._dependencias(comp.source, nombre), self.semantica),
                            f"computación {nombre}")
            finally:
                self._en_curso.discard(nombre)
        return self.revisiones[clave]

    def propiedad(self, prop):
        r = self._ranura("propiedad", prop.name)
        return self._fijar(revision(r, forma_canonica_propiedad(prop), sexpr.dumps(prop.source), ligaduras(prop),
                                    self._dependencias(prop.source, prop.name), self.semantica),
                           f"propiedad {prop.name}")

    def candidata(self, cand, tipo="candidata"):
        """Candidata del núcleo o, con `tipo="candidata-lang"`, la que produce el traductor de EFCH Lang."""
        comp = self.defn.computations[cand.implements]
        r = self._ranura(tipo, cand.name, self.ranura_computacion(comp.name)["id"])
        [sx] = sexpr.parse(cand.source_text)
        return self._fijar(revision(r, cand.canonical(comp), cand.source_text, comp.signature(),
                                    self._dependencias(sx, cand.name), self.semantica),
                           f"candidata {cand.name} de {comp.name}")

    def todas(self, candidatas=(), candidatas_lang=()):
        for n in sorted(self.defn.computations):
            self.computacion(n)
        for p in self.defn.properties:
            self.propiedad(p)
        for c in candidatas:
            self.candidata(c)
        for c in candidatas_lang:
            self.candidata(c, "candidata-lang")
        return self


def cierre_de(revisiones):
    """Unión de {ranura: id} de las revisiones dadas y de sus dependencias; None si una ranura aparece con dos
    revisiones (cierre incoherente, §5.1)."""
    out = {}
    for v in revisiones:
        for r, i in [(v["ranura"], v["id"]), *sorted(v["dependencias"].items())]:
            if out.setdefault(r, i) != i:
                return None
    return dict(sorted(out.items()))


def obligacion(af, revisiones):
    """Clave de la obligación: la afirmación a nivel de ranura (clase, ranura por papel y contexto), sin revisiones.
    Relaciona la evidencia de una ranura entre versiones; nunca la identifica. `revisiones`: {id: revisión}."""
    return sha(canonico({"clase": af["clase"], "contexto": af["contexto"],
                         "sujetos": {p: revisiones[i]["ranura"] for p, i in af["sujetos"].items()}}))
