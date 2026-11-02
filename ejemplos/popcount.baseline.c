/*
 * Línea base convencional para popcount.efch: la función integrada del
 * compilador. Con -O2 y sin -mpopcnt, gcc la implementa sin la instrucción
 * POPCNT del procesador.
 */

#include <stdint.h>

uint64_t baseline_popcount64(uint64_t x)
{
    return (uint64_t)__builtin_popcountll(x);
}
