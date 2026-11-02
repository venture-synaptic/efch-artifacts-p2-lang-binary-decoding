/*
 * Línea base convencional para varint.efch, escrita a mano con la ABI de
 * EFCH (ver efch/backend_c.py). Igual que experimento0/nativo/varint.c.
 */

#include <stddef.h>
#include <stdint.h>

size_t baseline_varint_encode(uint64_t x, uint8_t *out)
{
    size_t n = 0;
    while (x >= 0x80) {
        out[n++] = (uint8_t)(x | 0x80);
        x >>= 7;
    }
    out[n++] = (uint8_t)x;
    return n;
}

int baseline_varint_decode(const uint8_t *buf, size_t len, uint64_t *value, uint64_t *consumed)
{
    uint64_t result = 0;
    size_t limit = len < 10 ? len : 10;
    for (size_t i = 0; i < limit; i++) {
        uint8_t b = buf[i];
        result |= (uint64_t)(b & 0x7F) << (7 * i);
        if (b < 0x80) {
            if ((i > 0 && b == 0) || (i == 9 && b > 1))
                return 0;
            *value = result;
            *consumed = i + 1;
            return 1;
        }
    }
    return 0;
}
