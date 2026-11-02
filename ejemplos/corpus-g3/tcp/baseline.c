/* Opciones de la cabecera TCP (RFC 9293 §3.1 y §3.2; RFC 7323 §2.2-2.3; RFC 2018 §2), escrito a mano. EXP-010. */
#include <stddef.h>
#include <stdint.h>

int baseline_tcp_options(const uint8_t *b, size_t len, uint64_t *hl_out, uint64_t *mss_out, uint64_t *ws_out, uint64_t *sack_out)
{
    if (len < 20)
        return 0;
    unsigned doff = b[12] >> 4;
    size_t hl = 4 * doff;
    if (doff < 5 || hl > len)
        return 0;
    unsigned mss = 0xffff, ws = 0xff;
    int has_mss = 0, has_ws = 0, sack = 0;
    size_t p = 20;
    while (p < hl) {
        unsigned kind = b[p];
        if (kind == 0)
            break;
        if (kind == 1) {
            p++;
            continue;
        }
        if (p + 1 >= hl)
            return 0;
        unsigned n = b[p + 1];
        if (n < 2 || p + n > hl)
            return 0;
        if (kind == 2) {
            if (n != 4 || has_mss)
                return 0;
            has_mss = 1;
            mss = b[p + 2] << 8 | b[p + 3];
        } else if (kind == 3) {
            if (n != 3 || has_ws)
                return 0;
            has_ws = 1;
            ws = b[p + 2] > 14 ? 14 : b[p + 2];
        } else if (kind == 4) {
            if (n != 2 || sack)
                return 0;
            sack = 1;
        }
        p += n;
    }
    *hl_out = hl;
    *mss_out = mss;
    *ws_out = ws;
    *sack_out = sack;
    return 1;
}
