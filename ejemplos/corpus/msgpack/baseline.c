/* Entero de MessagePack, escrito a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

int baseline_msgpack_int_decode(const uint8_t *buf, size_t len, uint64_t *value, uint64_t *is_signed, uint64_t *consumed)
{
    if (len == 0)
        return 0;
    uint8_t tag = buf[0];
    if (tag < 0x80 || tag >= 0xe0) {
        *value = (uint64_t)(int64_t)(tag < 0x80 ? tag : (int8_t)tag);
        *is_signed = tag >= 0xe0;
        *consumed = 1;
        return 1;
    }
    if (tag < 0xcc || tag > 0xd3)
        return 0;
    int sg = tag >= 0xd0;
    size_t n = (size_t)1 << (tag & 3);
    if (len < n + 1)
        return 0;
    uint64_t u = 0;
    for (size_t i = 1; i <= n; i++)
        u = (u << 8) | buf[i];
    if (sg && n < 8 && (buf[1] & 0x80))
        u |= ~(uint64_t)0 << (8 * n);
    *value = u;
    *is_signed = sg;
    *consumed = n + 1;
    return 1;
}
