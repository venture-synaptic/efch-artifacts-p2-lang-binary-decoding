/* Entero de longitud variable de QUIC (RFC 9000, §16), escrito a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

int baseline_quic_varint_decode(const uint8_t *buf, size_t len, uint64_t *value, uint64_t *consumed)
{
    if (len == 0)
        return 0;
    size_t n = (size_t)1 << (buf[0] >> 6);
    if (len < n)
        return 0;
    uint64_t v = buf[0] & 0x3f;
    for (size_t i = 1; i < n; i++)
        v = (v << 8) | buf[i];
    *value = v;
    *consumed = n;
    return 1;
}
