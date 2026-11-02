# EFCH Lang 0.1: referencia

Estado: **[Decisión provisional]**. Primera interfaz de programación de EFCH (manifiesto v0.5,
§22). La sintaxis es de la familia de Rust y Go. **No tiene semántica propia:** cada programa se
traduce (`efch/lang.py`) a una expresión del [núcleo EFCH 0.1](lenguaje-efch-0.1.md), y el
significado del programa es el de esa expresión. Así, las dos interfaces (EFCH Lang y el lenguaje
de investigación, hoy la forma de expresiones S) comparten un único núcleo semántico (§22.1).

Alcance de 0.1: funciones puras y totales sobre enteros sin signo, booleanos, bytes acotados y
opciones. Es el dominio de los decodificadores de formatos binarios. No hay efectos, memoria
dinámica, recursión ni bucles de longitud arbitraria.

## Ejemplo

```
fn varint_decode(buf: bytes[11]) -> option(u64, u8) implements varint-decode {
    var result: u64 = 0
    for i in 0..min(buf.len, 10) {
        let b = buf[i]
        result |= u64(b & 0x7f) << (7 * i)
        if b < 0x80 {
            if (i > 0 && b == 0) || (i == 9 && b > 1) { return none }
            return some(result, i + 1)
        }
    }
    return none
}
```

## Órdenes

```bash
python3 -m efch lang core   PROG.efl                  # traducción al núcleo (para inspeccionar)
python3 -m efch lang build  PROG.efl -o prog.c        # ruta ordinaria: sin LLM ni búsqueda
python3 -m efch lang verify PROG.efl ESPEC.efch       # ruta de investigación: equivalencia formal
```

- **Ruta ordinaria (`build`):** traducción, elaboración en el núcleo, demostración de buena
  definición (ningún índice fuera de rango) y C. Si un acceso puede salirse del rango, la
  compilación falla con un contraejemplo. Esa comprobación usa SMT con tiempo límite (decisión
  provisional 3 de la §11 del [núcleo 0.2](nucleo-semantico-0.2.md)).
- **Ruta de investigación (`verify`):** cada función marcada con `implements C` debe tener la
  misma interfaz que la computación `C` de la especificación. Se demuestra la equivalencia con
  Z3. Si Z3 no termina y hay bucles con cota dinámica, se parte la prueba en casos según esa cota
  (los 256 valores del byte del que depende, o cada valor de la cota). Si sigue sin terminar, se
  usa CBMC sobre el C de las dos (supuestos en `efch/cbmc.py`).

## Tipos

| EFCH Lang | Núcleo |
|---|---|
| `u1` … `u64` | `(bv N)` |
| `bool` | `bool` |
| `bytes[M]` | `(bytes M)` |
| `option(T, ...)` | `(option T ...)` |

## Declaraciones e instrucciones

| Forma | Significado |
|---|---|
| `fn f(x: T, ...) -> R [implements C] { ... }` | función; puede llamar a funciones definidas antes (se expanden en línea) |
| `let x [: T] = e` | ligadura inmutable |
| `var x [: T] = e` | variable mutable |
| `x = e`, `x += e`, `-=`, `*=`, `/=`, `%=`, `&=`, `\|=`, `^=`, `<<=`, `>>=` | asignación |
| `if c { ... } [else if ... ] [else { ... }]` | condicional |
| `for i in A..B { ... }`, `for i in A..=B { ... }` | bucle acotado; ver abajo |
| `return e` | fin de la función; también vale una expresión final suelta |

Los nombres no pueden sombrearse: declarar un nombre ya visible es un error. El `;` es opcional.

**Bucles.** `A` debe ser constante. `B` puede ser dinámico si su cota superior se deduce sin
SMT: una constante, `.len`, `x & c`, `x % c`, `min(...)`, sumas, productos y desplazamientos a la
izquierda de cotas conocidas (`1 << (b >> 6)` vale como mucho 8), o una variable inmutable ligada
a una de ellas. Se admiten como mucho 64 vueltas. `B` se evalúa una vez, antes
del bucle. La variable de bucle es una constante en cada vuelta (el bucle se desenrolla), así que
toma el ancho que pida el contexto. No hay `break` en 0.1: se expresa con `return` o con la cota.

## Expresiones

Precedencia, de menor a mayor: `||`, `&&`, comparaciones (`== != < <= > >=`), `|`, `^`, `&`,
`<< >>`, `+ -`, `* / %`, unarios (`! ~ -`), sufijos (`[i]`, `.len`, `as T`). **A diferencia de C,
las operaciones de bits van antes que las comparaciones:** `a ^ b == 0` es `(a ^ b) == 0`.

| Forma | Núcleo |
|---|---|
| `+ - * / %` | `add sub mul udiv urem`: aritmética módulo 2^N; `x / 0 = 2^N-1`, `x % 0 = x` |
| `& \| ^ ~ << >>` | `and or xor not shl lshr`; desplazar N o más bits da 0 |
| `== != < <= > >=` | comparaciones sin signo |
| `&& \|\| !` | `all any not`, con cortocircuito |
| `if c { a } else if d { b } else { e }` | `ite` anidados |
| `b[i]` | `byte`; el índice es como mucho `u16` |
| `b.len` | `len`, `u16` |
| `e as uN`, `uN(e)` | `zext` o `trunc`; de `bool` da 0 o 1 |
| `min(a, b)`, `max(a, b)` | `ite` con `ult` |
| `fold k in A..B from INIT with s { e }` | `(fold k A B (s INIT) e)` (núcleo 0.2, EXP-009): `A` y `B` constantes, de 1 a 64 pasos; `s` es el acumulador (entero `uN` o `bool`) y `e` su valor siguiente, que puede llamar a funciones con bucles y `return` |
| `some(a, ...)`, `none` | `some`, `none` |

**Anchos.** Los literales toman el ancho del contexto. En una operación entre anchos distintos, el
más estrecho se extiende con ceros (sin pérdida). Una conversión con pérdida exige `as`.
`255 + 1` entre literales es 256; sobre `u8` es 0.

## Traducción

Es una ejecución simbólica en estilo de continuaciones. Cada asignación crea una ligadura nueva.
Un `if` con `return` bifurca la continuación, y un bucle con cota dinámica salta al final en
cuanto falla su guarda.

Un `if` sin `return` se **predica** (EXP-017). Sus dos ramas se traducen una sola vez, una detrás
de otra, cada una bajo su guarda: `c`, `not c` o, si está anidado, la conjunción con la guarda
exterior, ligada a un nombre. Dentro de una rama:
- una asignación `x = e` pasa a ser `x' = ite(guarda, e, x)`;
- una ligadura que puede quedar indefinida (contiene `byte`, `mkbytes` o `call`) pasa a ser
  `ite(guarda, e, neutro)`, donde neutro es 0, `false`, bytes vacíos o `some` de neutros;
- la condición de un `if` anidado se protege igual.

Como `ite` es perezoso, una lectura solo se evalúa bajo su guarda.

**[Decisión provisional]** Una rama que se ejecuta evalúa todas sus ligaduras, aunque no se usen,
igual que en el nivel superior. Así, `if c { let x = b[0] }` exige `b.len > 0` cuando `c` es
cierto. Antes de EXP-017, una rama que no asignaba variables exteriores se descartaba entera, con
sus lecturas incluidas. Lo detectó Codex Astra; ningún ejemplo depende de ello. El tamaño del núcleo es lineal con el anidamiento. Antes, cada rama se traducía una vez
por variable asignada.

Tamaño del núcleo, en nodos: varint da 392 (la especificación tiene 916) y trama 291 (292; antes
de EXP-017 eran 445). `corpus-g2/dns/prog-v1-sentencias.efl` da unos 224 nodos por byte del búfer
(14 361 con 64 bytes). Antes de EXP-017 no se podía traducir: con 4 bytes la expresión S tenía
15,7 millones de nodos y con 6 se agotaban 3 GB.
**Limitación conocida:** un `if` en el que las dos ramas pueden seguir y alguna puede terminar
duplica el resto de la función.

El traductor y los recorridos del núcleo son recursivos, y la profundidad crece con la longitud
del programa desenrollado. La CLI corre en un hilo con 512 MB de pila y un límite de recursión de
200 000 (`efch.__main__.main_con_pila`). Quien use `efch.lang` como biblioteca tiene que hacer lo
mismo con programas largos.

## Límites de seguridad y memoria (manifiesto v0.7, §12 y §27.3)

Lo que EFCH Lang 0.1 garantiza y lo que no:

| Aspecto | En 0.1 | Base de la afirmación |
|---|---|---|
| Modelo de memoria | **No hay**: sin montículo, referencias, punteros, alias ni estado mutable compartido. Los valores son inmutables; `var` es reasignación de nombres, que se traduce a ligaduras nuevas | Diseño del traductor: no hay ninguna construcción que cree memoria |
| Memoria máxima | Acotada por los tipos: `bytes[M]` con M ≤ 64 y escalares de ≤ 64 bits. El C generado no reserva memoria | Generación de C de `backend_c` |
| Lecturas fuera de rango | Imposibles en un programa compilado: la ruta ordinaria exige `probado` para la buena definición (cada `b[i]` con `i < b.len`) y, si no, rechaza con un contraejemplo | Z3 sobre el núcleo (probado) |
| Terminación | Total: sin recursión y con bucles desenrollados de ≤ 64 vueltas | Traductor |
| Aritmética | Módulo 2^N, división entre 0 y desplazamientos ≥ N definidos en el núcleo; el C generado protege `/`, `%`, `<<` y `>>` | Núcleo y `backend_c`; intérprete = Z3 = C como **evidencia experimental** (pruebas aleatorias y diferenciales) |
| Comportamiento indefinido de C | No se ha **demostrado** que el C generado esté libre de él. CBMC se usa con `--bounds-check --pointer-check`, sin `--undefined-shift-check` ni `--signed-overflow-check` | Pendiente |
| Corrección del traductor | **No verificada.** Se demuestra la equivalencia del **resultado** de cada traducción con su especificación, no la del traductor en general | `efch lang verify` |
| Efectos, E/S, concurrencia | **Fuera de alcance** en 0.1 | — |

Consecuencia: 0.1 vale para funciones puras y acotadas, como los decodificadores de formatos
binarios. Las preguntas de la §12 del manifiesto (propiedad y préstamo, regiones, conteo de
referencias, recolección) siguen abiertas, porque 0.1 las evita en lugar de responderlas.

## Cambios durante EXP-005

Dos extensiones generales, hechas al escribir el corpus de EXP-005 y contadas en su ficha: la
cota de `a << b` usa la cota de `b` aunque no sea constante, y la expresión `if` admite
`else if`. Ninguna cambia el núcleo.

## Pendiente (0.2)

Tipos con signo, tuplas y registros, `match` sobre `option`, `break`, arreglos, bucles sin cota
con prueba de terminación, efectos.
