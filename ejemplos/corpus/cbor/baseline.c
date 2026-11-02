/* Cabecera de un elemento CBOR (RFC 8949, §3), escrita a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

int baseline_cbor_head_decode(const uint8_t *buf, size_t len, uint64_t *major, uint64_t *arg, uint64_t *consumed)
{
    if (len == 0)
        return 0;
    uint8_t info = buf[0] & 0x1f;
    *major = buf[0] >> 5;
    if (info < 24) {
        *arg = info;
        *consumed = 1;
        return 1;
    }
    if (info > 27)
        return 0;
    size_t extra = (size_t)1 << (info - 24);
    if (len < extra + 1)
        return 0;
    uint64_t v = 0;
    for (size_t i = 1; i <= extra; i++)
        v = (v << 8) | buf[i];
    if (*major == 7 && info == 24 && v < 32)
        return 0;
    *arg = v;
    *consumed = extra + 1;
    return 1;
}
