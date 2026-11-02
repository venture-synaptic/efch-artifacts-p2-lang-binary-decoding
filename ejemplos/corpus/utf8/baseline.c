/* Primer punto de código UTF-8 (RFC 3629), escrito a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

int baseline_utf8_decode(const uint8_t *buf, size_t len, uint64_t *cp_out, uint64_t *consumed)
{
    if (len == 0)
        return 0;
    uint8_t b0 = buf[0];
    size_t n;
    uint32_t cp, min;
    if (b0 < 0x80) {
        *cp_out = b0;
        *consumed = 1;
        return 1;
    } else if (b0 < 0xc0) {
        return 0;
    } else if (b0 < 0xe0) {
        n = 2; cp = b0 & 0x1f; min = 0x80;
    } else if (b0 < 0xf0) {
        n = 3; cp = b0 & 0x0f; min = 0x800;
    } else if (b0 < 0xf8) {
        n = 4; cp = b0 & 0x07; min = 0x10000;
    } else {
        return 0;
    }
    if (len < n)
        return 0;
    for (size_t i = 1; i < n; i++) {
        if ((buf[i] & 0xc0) != 0x80)
            return 0;
        cp = (cp << 6) | (buf[i] & 0x3f);
    }
    if (cp < min || (cp >= 0xd800 && cp <= 0xdfff) || cp > 0x10ffff)
        return 0;
    *cp_out = cp;
    *consumed = n;
    return 1;
}
