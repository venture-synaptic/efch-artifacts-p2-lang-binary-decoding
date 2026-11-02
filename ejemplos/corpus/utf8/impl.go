// Primer punto de código UTF-8 (RFC 3629, §3 y §4). EXP-005.
package corpus

func Utf8Decode(buf []byte) (uint32, uint8, bool) {
	if len(buf) == 0 {
		return 0, 0, false
	}
	b0 := buf[0]
	var n int
	var min, cp uint32
	switch {
	case b0 < 0x80:
		return uint32(b0), 1, true
	case b0 >= 0xc0 && b0 < 0xe0:
		n, min, cp = 2, 0x80, uint32(b0&0x1f)
	case b0 >= 0xe0 && b0 < 0xf0:
		n, min, cp = 3, 0x800, uint32(b0&0x0f)
	case b0 >= 0xf0 && b0 < 0xf8:
		n, min, cp = 4, 0x10000, uint32(b0&0x07)
	default:
		return 0, 0, false
	}
	if len(buf) < n {
		return 0, 0, false
	}
	for _, b := range buf[1:n] {
		if b&0xc0 != 0x80 {
			return 0, 0, false
		}
		cp = cp<<6 | uint32(b&0x3f)
	}
	if cp < min || (cp >= 0xd800 && cp <= 0xdfff) || cp > 0x10ffff {
		return 0, 0, false
	}
	return cp, uint8(n), true
}
