/* Validación de cabecera IPv4 (RFC 791, RFC 1071), escrita a mano. EXP-005. */
#include <stddef.h>
#include <stdint.h>

int baseline_ipv4_header_check(const uint8_t *h, size_t len, uint64_t *ihl_out, uint64_t *total_out)
{
    if (len < 20)
        return 0;
    unsigned version = h[0] >> 4, ihl = h[0] & 0x0f;
    size_t hl = (size_t)ihl * 4;
    unsigned total = (unsigned)h[2] << 8 | h[3];
    if (version != 4 || ihl < 5 || len < hl || total < hl)
        return 0;
    uint32_t sum = 0;
    for (size_t i = 0; i < hl; i += 2)
        sum += (uint32_t)h[i] << 8 | h[i + 1];
    while (sum > 0xffff)
        sum = (sum & 0xffff) + (sum >> 16);
    if (sum != 0xffff)
        return 0;
    *ihl_out = ihl;
    *total_out = total;
    return 1;
}
