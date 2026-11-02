# EFCH

**EFCH** es un sistema de computación sintética verificable (**SCSV**), primer prototipo
del paradigma **Property-Oriented Computing (POC)** (nombre provisional). La visión y el
programa de investigación están en el [Manifiesto v0.8](EFCH_Manifiesto_v0.8.md).

En POC, la fuente de verdad de un programa no es código escrito para personas, sino una
**definición**: semántica precisa, propiedades, dominio, carga de trabajo, objetivos y
presupuesto. Las implementaciones son **candidatas**: cualquiera puede proponerlas (una
persona, una búsqueda o un LLM), pero solo se aceptan si un verificador formal
independiente **demuestra** que equivalen a la semántica. Después se materializan en C
y se miden.

```text
definición (.efch) ──► núcleo tipado ──► identidad semántica (SHA-256)
                           │
     candidatas ──────────►├─► SMT (Z3): bien definida + equivalente ──► probado | refutado | desconocido
  (persona, LLM)           │
                           └─► C (gcc -O2) ──► pruebas diferenciales ──► medición intercalada
                                                                               │
                                                  selección + evidencia.json ◄─┘
```

## Investigación propuesta: Live Engineering

**[Decisión provisional]** La [RFC de EFCH Live Engineering](docs/rfc/efch-live-engineering.md)
recomienda **reformular** el alcance y separar supervisión humana (H1) de persistencia de
evidencia (H2). Toca G0/G3/G5; ninguna queda superada por esta revisión documental.
La RFC conserva la propuesta original, contrasta tecnologías existentes y define criterios
para un futuro P0 y estudios separados. No autoriza implementación, no valida hipótesis ni
asigna un nuevo número de experimento; EXP-007 sigue dedicado a DNS en EFCH Lang.
El [contrato semántico mínimo propuesto](docs/rfc/efch-live-contrato-semantico-0.1.md)
concreta identidad, reconciliación y sincronización asimétrica; su especificación no autoriza P0.
El [Contract Conformance Pack 0.1](contracts/live/0.1/README.md) añade esquemas, vocabulario,
permisos, corpus sintético y un validador separado del motor. Sus chequeos de trazas no
certifican autenticación, atomicidad ni corrección semántica. El pack y sus pruebas requieren
la dependencia opcional `jsonschema==4.19.2` (presente en el entorno de elaboración; no se
instalaron ni descargaron dependencias). El núcleo EFCH sigue sin depender de ella.

## Inicio rápido

[Guía de inicio de EFCH Lang 0.1 (experimental)](docs/inicio-rapido.md): instalación reproducible con pip 25.3 y Z3 5.1.0.0, y primer proyecto.
Requisitos: Python 3.10+, `gcc` y Z3. Si `import z3` falla, ejecuta `scripts/vendor_z3.sh`
para descargar el wheel oficial con su hash comprobado. La síntesis guiada por LLM usa,
además, el CLI `claude`. EXP-003 necesita también CBMC 6.11.0 (`scripts/vendor_cbmc.sh`) y
bubblewrap (`bwrap`, paquete del sistema, probado con la versión 0.11.1) para aislar las
sesiones de agente.
EXP-005 compara con Rust 1.93, Go 1.26, Dafny 4.11.0 y Kani 0.68.0
(`scripts/vendor_comparadores.sh`).
EXP-011 usa además cvc5 1.4.2 (binario estático oficial, licencia BSD) como buscador SyGuS de
comparación (`scripts/vendor_cvc5.sh`, SHA-256 comprobado).
EXP-018 (escenario T3c, cambio real de solucionador) usa una segunda versión de Z3, la 5.3.1.0: es el wheel oficial
de PyPI, fijado por SHA-256 en `scripts/vendor_z3_exp018.sh`. EFCH sigue usando la 5.1.0.0 fuera del experimento.

```bash
python3 -m efch check  ejemplos/varint.efch                                # demuestra las obligaciones de la definición
python3 -m efch eval   ejemplos/varint.efch varint-decode b:ac02ff         # → (300, 2)
python3 -m efch verify ejemplos/popcount.efch ejemplos/popcount.candidatas.efch
python3 -m efch build  ejemplos/popcount.efch popcount64 --candidata ejemplos/popcount.candidatas.efch -o popcount.c
python3 -m efch synth  ejemplos/popcount.efch popcount64 --sin-llm --candidata ejemplos/popcount.candidatas.efch
python3 -m efch synth  ejemplos/varint.efch varint-decode                   # con LLM, dentro del presupuesto declarado
python3 -m efch store register ejemplos/evolucion/varint-r1.efch varint-decode   # registro semántico (EXP-002)
python3 -m efch store evolve   ejemplos/evolucion/varint-r3.efch varint-decode   # ¿qué cambia y qué sigue siendo válido?
python3 -m unittest discover -s tests -v
```

Una definición mínima:

```lisp
(efch 0.1
  (computation popcount64
    (input x (bv 64))
    (output (bv 8))
    (semantics (reduce add i 0 64 (trunc 8 (and (lshr x i) 1))))
    (workload (seeds 20261020 1 2) (count 10000) (input x (bits 64)))
    (objective (minimize time))
    (budget (llm-calls 4) (llm-usd 1.5) (smt-seconds 30))))
```

La referencia completa del lenguaje está en [docs/lenguaje-efch-0.1.md](docs/lenguaje-efch-0.1.md).

### EFCH Lang (prototipo 0.1)

La misma computación también puede escribirse con sintaxis convencional. EFCH Lang se traduce al
núcleo, así que no tiene una semántica aparte ([referencia](docs/lenguaje-efch-lang-0.1.md),
[EXP-004](docs/experimentos/EXP-004.md)):

```bash
python3 -m efch lang build  ejemplos/lang/varint.efl -o varint.c              # ruta ordinaria, sin LLM
python3 -m efch lang verify ejemplos/lang/varint.efl ejemplos/varint.efch     # equivalencia con la especificación
```

## Qué garantiza y qué no

| Afirmación | Tipo de evidencia |
|---|---|
| La semántica y cada candidata aceptada están **bien definidas** (no hay lecturas fuera de rango) | **Probado** con Z3, para todo el dominio declarado |
| La candidata aceptada es **observablemente equivalente** a la semántica | **Probado** con Z3, para todo el dominio declarado |
| Las propiedades declaradas (`property`) se cumplen | **Probado**, **refutado** (con contraejemplo) o **desconocido** (tiempo agotado), según el caso |
| El C generado se comporta como el núcleo | **Experimental**: unas 5000 pruebas diferenciales por candidata, más una prueba aleatoria entre intérprete, Z3 y C en `tests/` |
| La candidata seleccionada es la más rápida | **Experimental**: medición intercalada con 3 semillas en una máquina concreta |

Toda prueba depende de estos supuestos, que se registran en la evidencia: la semántica del
núcleo EFCH 0.1 ([efch/interp.py](efch/interp.py) y [efch/smt.py](efch/smt.py)), el dominio
declarado de las entradas y la corrección de Z3. Cada contraejemplo de Z3 se vuelve a
ejecutar con el intérprete antes de declarar algo refutado. Si ambos discrepan, el
resultado es *desconocido*, no *refutado*.

## Resultados (20/10/2026)

Entorno: VM x86_64 (Intel Haswell), gcc 15.2.0 `-O2`, Z3 5.1.0, LLM `claude-opus-5-5`. Las evidencias
completas están en [resultados/](resultados/).

**Definiciones ([`efch check`](ejemplos/)).** La semántica de las tres computaciones está probada
como bien definida. En Varint, `ida-y-vuelta` y `decodificacion-canonica` quedan **probadas** en
menos de 0,1 s. En popcount, `cota` queda probada y `complemento` como **desconocido**
(tiempo agotado, lo esperado).

**Síntesis guiada por LLM**, con 2 linajes × 2 rondas, 4 llamadas por computación y 0,74 USD en total:

| Computación | Candidatas del LLM | `-O2`: demostrada / C a mano | `-O3 -march=native`: demostrada / C a mano |
|---|---|---|---|
| `popcount64` | 3 probadas, 1 desconocida | 3,7 / 4,7–5,3 ns | 1,8 / 1,8 ns (**empate**) |
| `varint-decode` | 3 probadas, 1 no aplicable | 14,9–15,8 / 18,3–19,3 ns | 12,6–14,7 / 12,6–14,6 ns (**empate**) |

- **[Resultado]** Ninguna candidata sin demostrar llegó a seleccionarse. La desconocida de
  popcount (sumas por desplazamientos sucesivos) quedó fuera porque Z3 no la decidió en 30 s;
  la no aplicable de `varint-decode` tenía mal contados los paréntesis. Esto apoya la H2 en
  dos dominios acotados.
- **[Resultado, negativo]** La ventaja frente al C escrito a mano **desaparece con un
  compilador fuerte** (`-O3 -march=native`). En popcount, gcc reconoce el patrón SWAR y
  emite POPCNT para las dos versiones; en Varint, `-O3` desenrolla el bucle de la línea
  base. **No hay evidencia a favor de la H3** en estos dominios.
- **[Resultado]** Lo que sí se observa es que EFCH puede aceptar código de un generador no
  fiable solo con una demostración de equivalencia, sin revisarlo a mano.

La ficha completa, con método, revisión crítica y decisión, está en
[docs/experimentos/EXP-001.md](docs/experimentos/EXP-001.md).

## Línea actual: evolución semántica (D1 + D2)

La [R0](docs/estado-del-arte/R0.md) concluyó que EFCH v0.1, como herramienta de síntesis
verificada, no aporta nada nuevo frente a Cryptol/SAW, Rosette, Souper ni los trabajos que
combinan LLM y verificador. **[Decisión]** La dirección reformuló la línea de investigación
hacia la **identidad por definición** (D1) y la **evolución semántica** (D2, hipótesis H4).

El registro semántico ([efch/store.py](efch/store.py), `efch store`) guarda revisiones de
definiciones, realizaciones y evidencia con dirección por contenido. Ante una nueva revisión:
- demuestra si **conserva el comportamiento** o lo **cambia**, en cuyo caso da un testigo;
- **transfiere por composición** las realizaciones cuando la revisión es equivalente a la
  vigente o a una anterior del historial;
- vuelve a verificar las demás;
- **rechaza** la revisión si rompe una propiedad declarada.

**[Resultado] [EXP-002](docs/experimentos/EXP-002.md):** 4 de 4 revisiones de Varint clasificadas
como se había previsto. La transferencia tardó 0,008–0,018 s, frente a 1 s de reverificación
directa de 5 realizaciones. La revisión con un error sutil quedó rechazada con contraejemplo.
Solo hay autorrevisión, un dominio y ninguna comparación práctica con regression verification.

## Arquitectura

| Pieza | Papel (manifiesto §8.1) |
|---|---|
| [efch/sexpr.py](efch/sexpr.py), [efch/core.py](efch/core.py) | Frontend y núcleo semántico: lector, expansión de formas acotadas, tipado, forma canónica, identidad |
| [efch/interp.py](efch/interp.py) | Semántica operacional de referencia |
| [efch/smt.py](efch/smt.py) | Verificador: traducción a vectores de bits, obligaciones, contraejemplos confirmados |
| [efch/pipeline.py](efch/pipeline.py), [efch/llm.py](efch/llm.py) | Sintetizador (LLM como heurística de propuesta), selección y registro de evidencia |
| [efch/backend_c.py](efch/backend_c.py), [efch/native.py](efch/native.py) | Backend en C, pruebas diferenciales y arnés de medición |
| [efch/workload.py](efch/workload.py) | Cargas de trabajo declaradas en la definición |
| [efch/store.py](efch/store.py) | Registro semántico: revisiones, realizaciones, evidencia y evolución con transferencia por composición |
| [efch/__main__.py](efch/__main__.py) | CLI |

**Formatos (§12), con nombres provisionales:** definición y candidatas `.efch`,
representación canónica `.efir` (texto canónico con su identidad) y evidencia
`evidencia.json`. Los nombres definitivos siguen pendientes.

## Estado frente a las puertas de calidad (manifiesto v0.7, §25)

Las puertas son criterios de investigación, no fechas. Ninguna está superada sin reservas.

| Puerta | Estado | Qué falta |
|---|---|---|
| G0 — Evidencia reproducible | **Parcial** | Cada experimento tiene script, evidencia, ficha e incidentes en la bitácora. Faltan revisión adversarial independiente y replicación en otra máquina |
| G1 — Núcleo coherente | Superada con límites (núcleo 0.1 y 0.2a) | Intérprete = Z3 = C con pruebas aleatorias, y CBMC como oráculo independiente. La traducción a C no está verificada y faltan pruebas adversariales externas |
| G2 — Lenguaje vertical | **Parcial** | 10 programas EFCH Lang (EXP-004 y EXP-005) compilan sin LLM y se demuestran equivalentes a su especificación. Son decodificadores de ≤ 30 líneas: falta un programa no trivial y documentar los límites de memoria y seguridad (§27.3) |
| G3 — Ingeniería comparativa | No iniciada | El experimento de H1 con modificaciones sucesivas (§27.2) |
| G4 — Investigación estructural | **No superada** | EXP-001/002 sin ventaja frente a gcc; [R0](docs/estado-del-arte/R0.md): nada nuevo en EFCH v0.1 |
| G5 — Interoperabilidad | No iniciada | Contratos y evidencia consumibles por herramientas externas |

Los procedimientos para agentes y personas están en [AGENTS.md](AGENTS.md) y
[RESEARCH_PROTOCOL.md](RESEARCH_PROTOCOL.md).

## Limitaciones conocidas

- **Dominio pequeño:** no hay bucles no acotados, recursión, memoria mutable ni efectos.
  Las entradas `bytes` tienen como máximo 64 bytes.
- **La traducción a C no está verificada.** Solo se contrasta con pruebas.
- **Algunas propiedades son difíciles para SMT.** Por ejemplo, la igualdad entre dos
  árboles de sumadores de 64 bits (`popcount.efch`, propiedad `complemento`) queda como *desconocido*.
- **La generación por LLM no es determinista.** Las candidatas se guardan y se pueden
  volver a verificar con `efch verify`.
- **El objetivo `minimize time` se mide en una sola máquina.** El tamaño de código se
  informa, pero todavía no forma parte de la optimización.
- El [Experimento 0](experimento0/) es el antecedente: allí la especificación era Python
  y la verificación, por pruebas.
