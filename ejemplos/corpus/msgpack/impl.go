// Entero de MessagePack: fixint positivo y negativo, uint8..64 e int8..64. EXP-005.
package corpus

func MsgpackIntDecode(buf []byte) (uint64, bool, uint8, bool) {
	if len(buf) == 0 {
		return 0, false, 0, false
	}
	tag := buf[0]
	switch {
	case tag < 0x80:
		return uint64(tag), false, 1, true
	case tag >= 0xe0:
		return uint64(int64(int8(tag))), true, 1, true
	case tag < 0xcc || tag > 0xd3:
		return 0, false, 0, false
	}
	signed := tag >= 0xd0
	n := 1 << (tag & 3)
	if len(buf) < n+1 {
		return 0, false, 0, false
	}
	var u uint64
	for _, b := range buf[1 : n+1] {
		u = u<<8 | uint64(b)
	}
	if signed {
		sh := uint(64 - 8*n)
		u = uint64(int64(u<<sh) >> sh)
	}
	return u, signed, uint8(n + 1), true
}
