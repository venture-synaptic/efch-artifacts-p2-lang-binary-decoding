/* Nombre de host (RFC 1123 §2.1, RFC 952) en formato de cable DNS (RFC 1035), escrito a mano. EXP-007. */
#include <stddef.h>
#include <stdint.h>

static int ldh(uint8_t c)
{
    return (uint8_t)((c | 0x20) - 'a') < 26 || (uint8_t)(c - '0') < 10 || c == '-';
}

int baseline_dns_hostname_wire(const uint8_t *b, size_t len, uint64_t *used, uint64_t *labels_out, uint64_t *ptr_out)
{
    size_t pos = 0;
    unsigned labels = 0;
    while (pos < len) {
        unsigned n = b[pos];
        if (n == 0) {
            *used = pos + 1;
            *labels_out = labels;
            *ptr_out = 0xffff;
            return 1;
        }
        if ((n & 0xc0) == 0xc0) {
            if (pos + 1 >= len)
                return 0;
            *used = pos + 2;
            *labels_out = labels;
            *ptr_out = (n & 0x3f) << 8 | b[pos + 1];
            return 1;
        }
        if (n & 0xc0 || pos + n >= len || b[pos + 1] == '-' || b[pos + n] == '-')
            return 0;
        for (size_t i = pos + 1; i <= pos + n; i++)
            if (!ldh(b[i]))
                return 0;
        labels++;
        pos += 1 + n;
    }
    return 0;
}
