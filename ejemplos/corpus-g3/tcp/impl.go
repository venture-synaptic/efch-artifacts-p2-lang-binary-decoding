// Opciones de la cabecera TCP (RFC 9293 §3.1 y §3.2; RFC 7323 §2.2–2.3; RFC 2018 §2). EXP-010.
package corpus

// TcpOptions devuelve la longitud de la cabecera, el MSS (0xFFFF si no aparece), la escala de
// ventana (0xFF si no aparece) y si SACK está permitido.
func TcpOptions(b []byte) (uint8, uint16, uint8, bool, bool) {
	if len(b) < 20 {
		return 0, 0, 0, false, false
	}
	doff := int(b[12] >> 4)
	hl := 4 * doff
	if doff < 5 || hl > len(b) {
		return 0, 0, 0, false, false
	}
	mss, ws, sack := uint16(0xffff), uint8(0xff), false
	seenMss, seenWs := false, false
	for p := 20; p < hl; {
		kind := b[p]
		if kind == 0 {
			break
		}
		if kind == 1 {
			p++
			continue
		}
		if p+1 >= hl {
			return 0, 0, 0, false, false
		}
		n := int(b[p+1])
		if n < 2 || p+n > hl {
			return 0, 0, 0, false, false
		}
		switch kind {
		case 2:
			if n != 4 || seenMss {
				return 0, 0, 0, false, false
			}
			seenMss = true
			mss = uint16(b[p+2])<<8 | uint16(b[p+3])
		case 3:
			if n != 3 || seenWs {
				return 0, 0, 0, false, false
			}
			seenWs = true
			ws = min(b[p+2], 14)
		case 4:
			if n != 2 || sack {
				return 0, 0, 0, false, false
			}
			sack = true
		}
		p += n
	}
	return uint8(hl), mss, ws, sack, true
}
