# Primer proyecto: limitar un nivel

Ejemplo nuevo de función pura: `limitar_nivel(x)` devuelve el menor de `x` y
100. Su dominio son los 256 valores de `u8` (0 a 255). No acepta enteros
arbitrarios, números negativos ni medidas con unidades.

- `nivel.efch`: especificación en el núcleo y propiedad `cota` (resultado ≤ 100).
- `nivel.efl`: implementación en EFCH Lang con `implements limitar-nivel`.
- `main.c`: cinco llamadas desde C; incluye `nivel.c`, que se genera después
  de verificar. No hay que compilar `nivel.c` por separado.

Desde la raíz del checkout, sigue la [guía paso a paso](../../docs/inicio-rapido.md).
Con el entorno ya activado:

```bash
set -euo pipefail
ulimit -v 8000000
cd ejemplos/proyecto-inicial
timeout -k 5s 30 efch check nivel.efch --smt-segundos 5
timeout -k 5s 30 efch lang verify nivel.efl nivel.efch --smt-segundos 5
timeout -k 5s 30 efch lang build nivel.efl --smt-segundos 5 -o nivel.c
gcc -std=c11 -O2 -Wall -Wextra main.c -o nivel
timeout -k 5s 5 ./nivel
```

Salida esperada del ejecutable:

```text
0 -> 0
42 -> 42
100 -> 100
101 -> 100
255 -> 100
```

Los dos veredictos de `check` y las dos obligaciones y el veredicto final de
`verify` deben ser `probado`. Si alguna orden falla, detente antes de compilar.
Las cinco salidas del binario son evidencia experimental; no demuestran el
backend C. No se presenta este prototipo como listo para producción.
