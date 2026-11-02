/* CompactSize de Bitcoin en forma canónica, escrito a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

int baseline_compactsize_decode(const uint8_t *buf, size_t len, uint64_t *value, uint64_t *consumed)
{
    if (len == 0)
        return 0;
    size_t n;
    uint64_t min;
    switch (buf[0]) {
    case 0xfd: n = 2; min = 0xfd; break;
    case 0xfe: n = 4; min = 0x10000; break;
    case 0xff: n = 8; min = 0x100000000; break;
    default:
        *value = buf[0];
        *consumed = 1;
        return 1;
    }
    if (len < n + 1)
        return 0;
    uint64_t v = 0;
    for (size_t i = 0; i < n; i++)
        v |= (uint64_t)buf[i + 1] << (8 * i);
    if (v < min)
        return 0;
    *value = v;
    *consumed = n + 1;
    return 1;
}
