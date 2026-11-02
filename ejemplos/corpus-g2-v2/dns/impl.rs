// Nombre de host (RFC 1123 §2.1, RFC 952) en formato de cable DNS (RFC 1035 §3.1 y §4.1.4). EXP-008: la referencia de Kani traduce la especificación con índices absolutos.

/// Devuelve (bytes consumidos, etiquetas, puntero) o `None`; el puntero es 0xFFFF si el nombre
/// termina en el octeto 0.
pub fn parse(b: &[u8]) -> Option<(u8, u8, u16)> {
    let mut pos = 0usize;
    let mut labels = 0u8;
    loop {
        let len = *b.get(pos)?;
        match len & 0xc0 {
            0x00 if len == 0 => return Some((pos as u8 + 1, labels, 0xffff)),
            0x00 => {
                let label = b.get(pos + 1..pos + 1 + usize::from(len))?;
                if !valid_label(label) {
                    return None;
                }
                labels += 1;
                pos += 1 + usize::from(len);
            }
            0xc0 => {
                let low = *b.get(pos + 1)?;
                let ptr = u16::from(len & 0x3f) << 8 | u16::from(low);
                return Some((pos as u8 + 2, labels, ptr));
            }
            _ => return None,
        }
    }
}

fn valid_label(label: &[u8]) -> bool {
    label.first() != Some(&b'-')
        && label.last() != Some(&b'-')
        && label.iter().all(|c| c.is_ascii_alphanumeric() || *c == b'-')
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación (EXP-008).
    fn ldh(c: u8) -> bool {
        ((c | 0x20) >= 0x61 && (c | 0x20) <= 0x7a) || (c >= 0x30 && c <= 0x39) || c == 0x2d
    }

    fn label_ok(b: &[u8], p: u16) -> bool {
        let n = b.len() as u16;
        if !(p < n) {
            return false;
        }
        let l = b[p as usize] as u16;
        if !(l >= 1 && l <= 63 && p + l < n) {
            return false;
        }
        if b[(p + 1) as usize] == 0x2d || b[(p + l) as usize] == 0x2d {
            return false;
        }
        for j in 1..64u16 {
            if !(j <= p || j > p + l || ldh(b[j as usize])) {
                return false;
            }
        }
        true
    }

    fn step(b: &[u8], s: u16) -> u16 {
        let p = s & 0xff;
        if label_ok(b, p) {
            ((s >> 8) + 1) << 8 | (p + 1 + b[p as usize] as u16)
        } else {
            s
        }
    }

    fn reference(b: &[u8]) -> Option<(u8, u8, u16)> {
        let mut s = 0u16;
        for _ in 0..32 {
            s = step(b, s);
        }
        let p = s & 0xff;
        let n = (s >> 8) as u8;
        if p >= b.len() as u16 {
            return None;
        }
        let l = b[p as usize];
        if l == 0 {
            Some(((p + 1) as u8, n, 0xffff))
        } else if l & 0xc0 == 0xc0 && p + 1 < b.len() as u16 {
            Some(((p + 2) as u8, n, ((l & 0x3f) as u16) << 8 | b[(p + 1) as usize] as u16))
        } else {
            None
        }
    }

    #[kani::proof]
    #[kani::unwind(65)]
    fn equivalence() {
        let arr: [u8; 64] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(parse(&arr[..len]), reference(&arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_dns_hostname_wire(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
    o2: *mut u64,
) -> i32 {
    match parse(core::slice::from_raw_parts(buf, len)) {
        Some((c, l, p)) => {
            *o0 = c as u64;
            *o1 = l as u64;
            *o2 = p as u64;
            1
        }
        None => 0,
    }
}
