// Bloque base64 de 4 caracteres (RFC 4648, §4); bits de relleno no nulos rechazados. EXP-005.
package corpus

func sextet(c byte) (uint32, bool) {
	switch {
	case c >= 'A' && c <= 'Z':
		return uint32(c - 'A'), true
	case c >= 'a' && c <= 'z':
		return uint32(c-'a') + 26, true
	case c >= '0' && c <= '9':
		return uint32(c-'0') + 52, true
	case c == '+':
		return 62, true
	case c == '/':
		return 63, true
	}
	return 0, false
}

func Base64BlockDecode(s []byte) (uint32, uint8, bool) {
	if len(s) != 4 {
		return 0, 0, false
	}
	a, ok1 := sextet(s[0])
	b, ok2 := sextet(s[1])
	if !ok1 || !ok2 {
		return 0, 0, false
	}
	w := a<<18 | b<<12
	if s[2] == '=' && s[3] == '=' {
		return w >> 16, 1, w&0xffff == 0
	}
	c, ok := sextet(s[2])
	if !ok {
		return 0, 0, false
	}
	w |= c << 6
	if s[3] == '=' {
		return w >> 8, 2, w&0xff == 0
	}
	d, ok := sextet(s[3])
	if !ok {
		return 0, 0, false
	}
	return w | d, 3, true
}
