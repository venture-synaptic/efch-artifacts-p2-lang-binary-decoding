/* Entero de HPACK con prefijo de N bits (RFC 7541, §5.1), escrito a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

int baseline_hpack_int_decode(uint64_t n, const uint8_t *buf, size_t len, uint64_t *value, uint64_t *consumed)
{
    if (n < 1 || n > 8 || len == 0)
        return 0;
    uint64_t mask = ((uint64_t)1 << n) - 1;
    uint64_t v = buf[0] & mask;
    if (v < mask) {
        *value = v;
        *consumed = 1;
        return 1;
    }
    for (size_t i = 1; i < len && i < 6; i++) {
        v += (uint64_t)(buf[i] & 0x7f) << (7 * (i - 1));
        if (!(buf[i] & 0x80)) {
            if (v > 0xffffffffu)
                return 0;
            *value = v;
            *consumed = i + 1;
            return 1;
        }
    }
    return 0;
}
