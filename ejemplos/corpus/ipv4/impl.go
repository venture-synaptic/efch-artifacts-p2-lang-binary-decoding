// Validación de cabecera IPv4 (RFC 791, §3.1) con suma de comprobación (RFC 1071). EXP-005.
package corpus

func Ipv4HeaderCheck(h []byte) (uint8, uint16, bool) {
	if len(h) < 20 {
		return 0, 0, false
	}
	version, ihl := h[0]>>4, h[0]&0x0f
	hl := int(ihl) * 4
	total := uint16(h[2])<<8 | uint16(h[3])
	if version != 4 || ihl < 5 || len(h) < hl || int(total) < hl {
		return 0, 0, false
	}
	var sum uint32
	for i := 0; i < hl; i += 2 {
		sum += uint32(h[i])<<8 | uint32(h[i+1])
	}
	for sum > 0xffff {
		sum = sum&0xffff + sum>>16
	}
	return ihl, total, sum == 0xffff
}
