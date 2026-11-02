/* Línea base convencional para trama.efch, escrita a mano (= tarea-trama-k7/correcta-base.c de EXP-003). */
#include <stddef.h>
#include <stdint.h>
int baseline_trama_decode(const uint8_t *buf, size_t len, uint64_t *value, uint64_t *kind, uint64_t *consumed)
{
    if (len < 2)
        return 0;
    unsigned h = buf[0], ver = h >> 6, k = (h >> 3) & 7, n = h & 7;
    if (ver != 1)
        return 0;
    if (k == 6) return 0;
    if (len < (size_t)n + 2)
        return 0;
    unsigned sum = h;
    uint8_t mask = (k == 7) ? 0x5A : 0x00;
    uint64_t v = 0;
    for (unsigned i = 1; i <= n; i++) {
        sum += buf[i];
        v |= (uint64_t)(uint8_t)(buf[i] ^ mask) << (8 * (i - 1));
    }
    if (buf[n + 1] != sum % 251)
        return 0;
    if (n > 0 && (uint8_t)(buf[n] ^ mask) == 0)
        return 0;
    if (k == 0 && v >= 1000)
        return 0;
    *value = v;
    *kind = k;
    *consumed = n + 2;
    return 1;
}
