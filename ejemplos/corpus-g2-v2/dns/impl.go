// Nombre de host (RFC 1123 §2.1, RFC 952) en formato de cable DNS (RFC 1035 §3.1 y §4.1.4). EXP-007.
package corpus

// DnsHostnameWire devuelve los bytes consumidos, las etiquetas y el puntero (0xFFFF si el nombre
// termina en el octeto 0).
func DnsHostnameWire(b []byte) (uint8, uint8, uint16, bool) {
	pos, labels := 0, uint8(0)
	for pos < len(b) {
		n := int(b[pos])
		switch {
		case n == 0:
			return uint8(pos + 1), labels, 0xffff, true
		case n&0xc0 == 0xc0:
			if pos+1 >= len(b) {
				return 0, 0, 0, false
			}
			return uint8(pos + 2), labels, uint16(n&0x3f)<<8 | uint16(b[pos+1]), true
		case n&0xc0 != 0:
			return 0, 0, 0, false
		}
		if pos+1+n > len(b) || !validLabel(b[pos+1:pos+1+n]) {
			return 0, 0, 0, false
		}
		labels++
		pos += 1 + n
	}
	return 0, 0, 0, false
}

func validLabel(label []byte) bool {
	if label[0] == '-' || label[len(label)-1] == '-' {
		return false
	}
	for _, c := range label {
		if !('a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || '0' <= c && c <= '9' || c == '-') {
			return false
		}
	}
	return true
}
