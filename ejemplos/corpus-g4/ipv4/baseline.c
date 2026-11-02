/* Cabecera IPv4 con opciones; interpretación directa de EXP-015. */
#include <stddef.h>
#include <stdint.h>

int baseline_ipv4_header(const uint8_t *b, size_t len, uint64_t *hl_out,
                         uint64_t *nopts_out, uint64_t *srcroute_out,
                         uint64_t *ra_out)
{
    if (len < 20 || (b[0] >> 4) != 4)
        return 0;

    unsigned ihl = b[0] & 15;
    size_t hl = 4 * ihl;
    if (ihl < 5 || hl > len)
        return 0;

    size_t total_len = ((size_t)b[2] << 8) | b[3];
    if (total_len < hl)
        return 0;

    uint32_t sum = 0;
    for (size_t i = 0; i < hl; i += 2)
        sum += ((uint32_t)b[i] << 8) | b[i + 1];
    while (sum >> 16)
        sum = (sum & 0xffffu) + (sum >> 16);
    if (sum != 0xffffu)
        return 0;

    uint64_t nopts = 0;
    uint64_t srcroute = 0;
    uint64_t ra = 0xffff;
    int has_ra = 0;
    size_t p = 20;
    while (p < hl) {
        unsigned type = b[p];
        if (type == 0)
            break;
        if (type == 1) {
            p++;
            continue;
        }
        if (p + 1 >= hl)
            return 0;
        unsigned opt_len = b[p + 1];
        if (opt_len < 2 || p + opt_len > hl)
            return 0;

        if (type == 131 || type == 137) {
            if (srcroute || opt_len < 3)
                return 0;
            srcroute = 1;
        } else if (type == 148) {
            if (has_ra || opt_len != 4)
                return 0;
            has_ra = 1;
            ra = ((uint64_t)b[p + 2] << 8) | b[p + 3];
        }
        nopts++;
        p += opt_len;
    }

    *hl_out = hl;
    *nopts_out = nopts;
    *srcroute_out = srcroute;
    *ra_out = ra;
    return 1;
}
