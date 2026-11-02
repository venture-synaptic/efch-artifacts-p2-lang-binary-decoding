// Entero de longitud variable de QUIC (RFC 9000, §16). EXP-005.
package corpus

func QuicVarintDecode(buf []byte) (uint64, uint8, bool) {
	if len(buf) == 0 {
		return 0, 0, false
	}
	n := 1 << (buf[0] >> 6)
	if len(buf) < n {
		return 0, 0, false
	}
	v := uint64(buf[0] & 0x3f)
	for _, b := range buf[1:n] {
		v = v<<8 | uint64(b)
	}
	return v, uint8(n), true
}
