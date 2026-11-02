// CompactSize de Bitcoin, solo en forma canónica. EXP-005.
package corpus

func CompactsizeDecode(buf []byte) (uint64, uint8, bool) {
	if len(buf) == 0 {
		return 0, 0, false
	}
	var n int
	var min uint64
	switch buf[0] {
	case 0xfd:
		n, min = 2, 0xfd
	case 0xfe:
		n, min = 4, 0x10000
	case 0xff:
		n, min = 8, 0x100000000
	default:
		return uint64(buf[0]), 1, true
	}
	if len(buf) < n+1 {
		return 0, 0, false
	}
	var v uint64
	for i := n; i >= 1; i-- {
		v = v<<8 | uint64(buf[i])
	}
	return v, uint8(n + 1), v >= min
}
