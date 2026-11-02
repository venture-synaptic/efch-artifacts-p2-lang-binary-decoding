// Opciones de la cabecera TCP (RFC 9293 §3.1 y §3.2; RFC 7323 §2.2–2.3; RFC 2018 §2). EXP-010: la referencia de Kani traduce la especificación con el estado empaquetado.

/// Devuelve (longitud de la cabecera, MSS, escala de ventana, SACK permitido) o `None`.
/// El MSS es 0xFFFF y la escala 0xFF si la opción no aparece.
pub fn parse(b: &[u8]) -> Option<(u8, u16, u8, bool)> {
    if b.len() < 20 {
        return None;
    }
    let doff = b[12] >> 4;
    let hl = usize::from(doff) * 4;
    if doff < 5 || hl > b.len() {
        return None;
    }
    let (mut mss, mut ws, mut sack) = (None, None, false);
    let mut p = 20;
    while p < hl {
        match b[p] {
            0 => break,
            1 => p += 1,
            kind => {
                let len = usize::from(*b[..hl].get(p + 1)?);
                if len < 2 || p + len > hl {
                    return None;
                }
                match (kind, len) {
                    (2, 4) if mss.is_none() => mss = Some(u16::from_be_bytes([b[p + 2], b[p + 3]])),
                    (3, 3) if ws.is_none() => ws = Some(b[p + 2].min(14)),
                    (4, 2) if !sack => sack = true,
                    (2..=4, _) => return None,
                    _ => {}
                }
                p += len;
            }
        }
    }
    Some((hl as u8, mss.unwrap_or(0xffff), ws.unwrap_or(0xff), sack))
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación (EXP-010). Estado en 64 bits: posición (bits 0–7),
    // fin (8), error (9), MSS (16–31) y visto (32), escala (40–47) y vista (48), SACK permitido (49).
    fn tcp_hl(b: &[u8]) -> u16 {
        if (b.len() as u16) < 20 {
            0
        } else {
            4 * ((b[12] >> 4) as u16)
        }
    }

    fn tcp_step(b: &[u8], s: u64) -> u64 {
        let hl = tcp_hl(b);
        let p = (s & 0xff) as u16;
        let err = s | 0x200;
        if (s & 0x300) != 0 || p >= hl || hl > b.len() as u16 {
            return s;
        }
        let k = b[p as usize];
        if k == 0 {
            s | 0x100
        } else if k == 1 {
            s + 1
        } else if p + 1 >= hl {
            err
        } else {
            let l = b[(p + 1) as usize];
            if l < 2 || p + l as u16 > hl {
                err
            } else {
                let base = (s & 0xffff_ffff_ffff_ff00) | (p + l as u16) as u64;
                if k == 2 {
                    if l != 4 || (s & 0x1_0000_0000) != 0 {
                        err
                    } else {
                        base | (b[(p + 2) as usize] as u64) << 24 | (b[(p + 3) as usize] as u64) << 16 | 0x1_0000_0000
                    }
                } else if k == 3 {
                    if l != 3 || (s & 0x1_0000_0000_0000) != 0 {
                        err
                    } else {
                        let w = b[(p + 2) as usize];
                        base | ((if w > 14 { 14 } else { w }) as u64) << 40 | 0x1_0000_0000_0000
                    }
                } else if k == 4 {
                    if l != 2 || (s & 0x2_0000_0000_0000) != 0 {
                        err
                    } else {
                        base | 0x2_0000_0000_0000
                    }
                } else {
                    base
                }
            }
        }
    }

    fn reference(b: &[u8]) -> Option<(u8, u16, u8, bool)> {
        if (b.len() as u16) < 20 {
            return None;
        }
        let doff = b[12] >> 4;
        let hl = tcp_hl(b);
        if doff < 5 || hl > b.len() as u16 {
            return None;
        }
        let mut s = 20u64;
        for _ in 0..40 {
            s = tcp_step(b, s);
        }
        if (s & 0x200) != 0 {
            return None;
        }
        Some((
            hl as u8,
            if (s & 0x1_0000_0000) == 0 { 0xffff } else { (s >> 16) as u16 },
            if (s & 0x1_0000_0000_0000) == 0 { 0xff } else { (s >> 40) as u8 },
            (s & 0x2_0000_0000_0000) != 0,
        ))
    }

    #[kani::proof]
    #[kani::unwind(41)]
    fn equivalence() {
        let arr: [u8; 60] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(parse(&arr[..len]), reference(&arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_tcp_options(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
    o2: *mut u64,
    o3: *mut u64,
) -> i32 {
    match parse(core::slice::from_raw_parts(buf, len)) {
        Some((h, m, w, s)) => {
            *o0 = h as u64;
            *o1 = m as u64;
            *o2 = w as u64;
            *o3 = s as u64;
            1
        }
        None => 0,
    }
}
