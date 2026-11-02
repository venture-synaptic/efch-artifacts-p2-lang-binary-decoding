// Cabecera de un elemento CBOR (RFC 8949, §3); información adicional 28..31 es error. EXP-005.
package corpus

func CborHeadDecode(buf []byte) (uint8, uint64, uint8, bool) {
	if len(buf) == 0 {
		return 0, 0, 0, false
	}
	major, info := buf[0]>>5, buf[0]&0x1f
	if info < 24 {
		return major, uint64(info), 1, true
	}
	if info > 27 {
		return 0, 0, 0, false
	}
	extra := 1 << (info - 24)
	if len(buf) < extra+1 {
		return 0, 0, 0, false
	}
	var arg uint64
	for _, b := range buf[1 : extra+1] {
		arg = arg<<8 | uint64(b)
	}
	if major == 7 && info == 24 && arg < 32 {
		return 0, 0, 0, false
	}
	return major, arg, uint8(extra + 1), true
}
