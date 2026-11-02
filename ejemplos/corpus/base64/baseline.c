/* Bloque base64 de 4 caracteres (RFC 4648, §4), escrito a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

static int sextet(uint8_t c)
{
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1;
}

int baseline_base64_block_decode(const uint8_t *s, size_t len, uint64_t *value, uint64_t *count)
{
    if (len != 4)
        return 0;
    int a = sextet(s[0]), b = sextet(s[1]);
    if (a < 0 || b < 0)
        return 0;
    uint32_t w = (uint32_t)a << 18 | (uint32_t)b << 12;
    if (s[2] == '=' && s[3] == '=') {
        if (w & 0xffff)
            return 0;
        *value = w >> 16;
        *count = 1;
        return 1;
    }
    int c = sextet(s[2]);
    if (c < 0)
        return 0;
    w |= (uint32_t)c << 6;
    if (s[3] == '=') {
        if (w & 0xff)
            return 0;
        *value = w >> 8;
        *count = 2;
        return 1;
    }
    int d = sextet(s[3]);
    if (d < 0)
        return 0;
    *value = w | (uint32_t)d;
    *count = 3;
    return 1;
}
