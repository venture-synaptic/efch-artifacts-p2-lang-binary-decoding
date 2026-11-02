# Núcleo EFCH 0.1: referencia

Estado: **[Decisión provisional]**. Es el primer subconjunto mínimo de la fase A
(manifiesto v0.4, §13): funciones puras y totales sobre vectores de bits, bytes
acotados y opciones. No hay efectos, estado, bucles no acotados ni recursión. La
notación es de expresiones S; es la capa de autoría y, tras la expansión, también
la representación canónica.

## Archivos

Un archivo contiene una única forma `(efch 0.1 ...)`.

- **Definición** (`.efch`): `computation`, `property` y, opcionalmente, `baseline-c`.
- **Candidata** (`.efch`): una o varias `(candidate nombre (implements computación) (body expr))`.
- **Representación canónica** (`.efir`): texto canónico elaborado; su SHA-256 es la identidad semántica.
- **Evidencia** (`evidencia.json`): obligaciones, estados, supuestos, herramientas y mediciones.

Las extensiones son provisionales; la §12 del manifiesto deja pendientes los nombres definitivos.

## Tipos

| Tipo | Valores |
|---|---|
| `(bv N)` | enteros sin signo de N bits, 1 ≤ N ≤ 128; en las entradas y salidas, N ≤ 64 |
| `bool` | `true`, `false` |
| `(bytes M)` | cadenas de 0 a M bytes, M ≤ 64 |
| `(option T...)` | `none` o `(some v...)` con campos escalares (`bv` o `bool`) |

Un valor `(bytes m)` se acepta donde se espera `(bytes M)` si m ≤ M.

## Computación

```
(computation nombre
  (doc "texto")                     ; opcional
  (input x (bv 64)) ...             ; entradas, en orden
  (output TIPO)
  (semantics EXPR)                  ; definición del comportamiento
  (workload ...)                    ; carga de medición (opcional)
  (objective (minimize time))       ; v0.1: solo tiempo; el tamaño de código se informa
  (budget (llm-calls 4) (llm-usd 1.5) (llm-seconds 1800) (smt-seconds 120)))
```

`(property nombre (forall ((x T) ...) EXPR-bool))` declara una propiedad que debe
demostrarse para todos los valores; puede llamar a computaciones con `call`.

**[Decisión provisional] (26/10/2026, diseño de identidad v2.1, paso 1).**
- Las dependencias de cada computación, propiedad y candidata son las que registra el elaborador al resolver cada
  `call` (también las de los argumentos de otra llamada); nunca se buscan en el texto. Un `call` dentro de `(doc ...)`
  no es una dependencia.
- El presupuesto `smt-seconds` de una propiedad, si no se fija con `--smt-seconds`, es el máximo de las computaciones
  de su **cierre** de dependencias. Antes eran las que la propiedad mencionaba directamente, buscadas con una expresión
  regular que no veía nombres como `f-` (D7). Puede aumentar (computaciones del cierre con más presupuesto) o pasar
  del valor por defecto al declarado (nombres que la expresión no veía). Con un presupuesto fijo, los veredictos no
  cambian (resultados/identidad-v2/diferencial/).
- La identidad de una propiedad es el sha256 de `(efch 0.1 (property ((x T) ...)) CUERPO-CANÓNICO)`: incluye las
  ligaduras con sus tipos (∀b:(bytes 0) y ∀b:(bytes 1) son propiedades distintas). Las identidades de computaciones y
  candidatas no cambian (`resultados/identidad-v2/identidades-*.json`).

## Expresiones

Los literales enteros (`7`, `#x7f`, `#b101`) toman el ancho del contexto; si no lo hay,
se escribe `(bv N valor)`. Todas las operaciones aritméticas son módulo 2^N.
No hay tipo «con signo»: un `(bv N)` es un patrón de bits, y las operaciones marcadas como
0.2a lo interpretan en complemento a dos. Son la primera parte del núcleo 0.2
([borrador](nucleo-semantico-0.2.md), §3.1); no cambian la identidad de los programas que no las usan.

| Forma | Significado |
|---|---|
| `(add a b ...)` `(sub a b)` `(mul a b ...)` | aritmética módulo 2^N |
| `(udiv a b)` `(urem a b)` | división sin signo; `udiv x 0 = 2^N-1`, `urem x 0 = x` (SMT-LIB) |
| `(and a b ...)` `(or ...)` `(xor ...)` `(not a)` `(neg a)` | bit a bit; `not` sobre `bool` es negación lógica |
| `(shl a k)` `(lshr a k)` | desplazamientos lógicos; si k ≥ N, el resultado es 0 |
| `(zext N a)` `(trunc N a)` | extensión con ceros / truncado a N bits |
| `(sdiv a b)` `(srem a b)` `(ashr a k)` | con signo, en complemento a dos (0.2a): división truncada hacia cero; `sdiv x 0` = -1 si x ≥ 0 y 1 si x < 0; `srem x 0 = x`; el resto lleva el signo del dividendo; `sdiv` del mínimo entre -1 da el mínimo; `ashr` con k ≥ N replica el bit de signo (SMT-LIB) |
| `(slt a b)` `(sle ...)` `(sgt ...)` `(sge ...)` | comparaciones con signo (0.2a), devuelven `bool` |
| `(sext N a)` | extensión de signo a N bits (0.2a) |
| `(eq a b)` `(ne a b)` `(ult ...)` `(ule ...)` `(ugt ...)` `(uge ...)` | comparaciones sin signo, devuelven `bool` |
| `(all p ...)` `(any p ...)` | conjunción / disyunción con cortocircuito |
| `(ite c a b)` | condicional; solo se evalúa la rama elegida |
| `(let ((x e) (y e2)) cuerpo)` | ligaduras secuenciales y estrictas |
| `(len b)` | longitud de bytes, `(bv 16)` |
| `(byte b i)` | byte i, `(bv 8)`; **indefinido** si i ≥ `(len b)` |
| `(mkbytes n e0 e1 ...)` | bytes de longitud n con esos elementos (los que falten valen 0); indefinido si n supera el máximo; los elementos ≥ n no se evalúan |
| `(some a ...)` `none` | construcción de option |
| `(match e ((some x y) cuerpo) (none cuerpo))` | eliminación de option |
| `(call comp args...)` | la semántica de otra computación definida antes |

### Formas acotadas

Se expanden antes de elaborar; las cotas deben ser constantes (se admiten `add`, `sub`,
`mul`, `min` y `max` entre constantes, y la variable de una forma exterior).

| Forma | Expansión |
|---|---|
| `(first i LO HI cond entonces si-no)` | `entonces[i]` para el primer i en [LO, HI) con `cond[i]`; si no hay, `si-no` |
| `(reduce OP i LO HI e)` | `OP` (add, mul, and, or, xor, all, any) sobre `e[i:=LO] … e[i:=HI-1]` |
| `(each i LO HI e)` | dentro de una lista, se sustituye por `e[i:=LO] … e[i:=HI-1]` |
| `(fold i LO HI (acc INIT) PASO)` | (núcleo 0.2, EXP-009) `acc := PASO[i := LO]`, …, `acc := PASO[i := HI-1]` desde `acc = INIT`; devuelve el último `acc`. `acc` es escalar (`bv` o `bool`); como mucho 256 pasos |

**Pliegues (núcleo 0.2, EXP-009).** La semántica de `fold` es exactamente la cadena de `let` de sus
pasos, y el intérprete, Z3 y el C la respetan; en C, si ningún paso depende de `i`, es un bucle que
sale en cuanto el acumulador deja de cambiar. Además, la verificación intenta dos vías modulares
antes de expandir, y vuelve a la expansión si alguna subprueba no sale `probado` (nunca concluyen
`refutado`):
- **Buena definición:** `INIT` bien definido, cada paso distinto bien definido **para todo**
  acumulador de su tipo, y el resto con el pliegue sustituido por una variable libre.
- **Congruencia:** los pliegues de la semántica y de la candidata se emparejan en orden; si los
  `INIT` coinciden donde el de la semántica está definido y, para todo acumulador, cada paso de la
  candidata coincide con el de la semántica donde este está definido, los dos pliegues valen lo
  mismo (inducción sobre los pasos) y se sustituyen por la misma variable libre.

Solo se intentan con pliegues cuyas variables libres son entradas de la computación, sin estar
ligadas por un `let` o `match` que los rodee.

**Propiedades (EXP-013 y EXP-014).**
- En una `property`, cada pliegue cerrado se sustituye por una variable libre. Si tiene un
  `(invariant INV)` cuyas dos obligaciones quedan `probado`, la variable queda restringida por `INV`.
  Las obligaciones son: el valor inicial lo cumple, y cada paso lo conserva para todo acumulador.
- **Congruencia condicional (EXP-014).** Es un plan de prueba que proporciona el arnés, no la sintaxis:
  `smt.check_property(prop, t, [(i, j, R)])`.
  - `R` es una expresión booleana sobre las variables de la propiedad, sin pliegues.
  - Si `R` está bien definida, `R ⇒ INIT_i = INIT_j` y, para cada posición, `R ⇒ ∀s. PASO_i(s) = PASO_j(s)`,
    entonces se añade `R ⇒ f_i = f_j`.
  - Sirve para propiedades que comparan dos ejecuciones.
- Ninguna de estas vías concluye `refutado`: si no prueban, se vuelve a la expansión.

## Buena definición

Una expresión está bien definida si nunca lee un byte fuera de su longitud ni
construye bytes por encima de su máximo, teniendo en cuenta la pereza de `ite`, `all`,
`any`, `match` y `mkbytes`. Toda semántica y toda candidata deben demostrarse bien definidas.

## Equivalencia observable

Una candidata implementa una computación si, para toda entrada del dominio declarado,
su resultado es observablemente igual al de la semántica: los escalares son iguales;
en los bytes, longitud y contenido hasta la longitud; en las opciones, la etiqueta y,
si es `some`, los campos.
