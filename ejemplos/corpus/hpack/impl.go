// Entero de HPACK con prefijo de N bits (RFC 7541, §5.1), valor ≤ 2^32-1 y ≤ 6 bytes. EXP-005.
package corpus

func HpackIntDecode(n uint8, buf []byte) (uint32, uint8, bool) {
	if n < 1 || n > 8 || len(buf) == 0 {
		return 0, 0, false
	}
	mask := uint64(1)<<n - 1
	v := uint64(buf[0]) & mask
	if v < mask {
		return uint32(v), 1, true
	}
	for i := 1; i < len(buf) && i < 6; i++ {
		b := buf[i]
		v += uint64(b&0x7f) << (7 * (i - 1))
		if b&0x80 == 0 {
			if v > 0xffffffff {
				return 0, 0, false
			}
			return uint32(v), uint8(i + 1), true
		}
	}
	return 0, 0, false
}
