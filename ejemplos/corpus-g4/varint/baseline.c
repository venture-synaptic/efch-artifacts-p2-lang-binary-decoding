/* Varint sin signo de Protocol Buffers; semántica de Go Uvarint, EXP-015. */
#include <stddef.h>
#include <stdint.h>

int baseline_varint_u64(const uint8_t *b, size_t len, uint64_t *value_out,
                        uint64_t *n_out)
{
    uint64_t value = 0;
    size_t limit = len < 10 ? len : 10;
    for (size_t k = 0; k < limit; k++) {
        unsigned byte = b[k];
        if (k == 9 && byte > 1)
            return 0;
        value |= (uint64_t)(byte & 0x7f) << (7 * k);
        if (byte < 0x80) {
            *value_out = value;
            *n_out = k + 1;
            return 1;
        }
    }
    return 0;
}
