#include <stdio.h>
#include "nivel.c"

int main(void) {
    const uint8_t entradas[] = {0, 42, 100, 101, 255};
    for (unsigned i = 0; i < sizeof entradas / sizeof entradas[0]; ++i) {
        printf("%u -> %u\n", (unsigned)entradas[i],
               (unsigned)efch_limitar_nivel(entradas[i]));
    }
    return 0;
}
