// Primer punto de código UTF-8 (RFC 3629, §3 y §4). EXP-005.

pub fn decode(buf: &[u8]) -> Option<(u32, u8)> {
    let b0 = *buf.first()?;
    let (len, min, init) = match b0 {
        0x00..=0x7f => return Some((u32::from(b0), 1)),
        0xc0..=0xdf => (2, 0x80, b0 & 0x1f),
        0xe0..=0xef => (3, 0x800, b0 & 0x0f),
        0xf0..=0xf7 => (4, 0x1_0000, b0 & 0x07),
        _ => return None,
    };
    let tail = buf.get(1..len)?;
    let mut cp = u32::from(init);
    for &b in tail {
        if b & 0xc0 != 0x80 {
            return None;
        }
        cp = (cp << 6) | u32::from(b & 0x3f);
    }
    if cp < min || (0xd800..=0xdfff).contains(&cp) || cp > 0x10ffff {
        return None;
    }
    Some((cp, len as u8))
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn reference(buf: &[u8]) -> Option<(u32, u8)> {
        if buf.is_empty() {
            return None;
        }
        let b0 = buf[0];
        let n: u8 = if b0 < 0x80 {
            1
        } else if b0 < 0xc0 {
            0
        } else if b0 < 0xe0 {
            2
        } else if b0 < 0xf0 {
            3
        } else if b0 < 0xf8 {
            4
        } else {
            0
        };
        if n == 0 || buf.len() < n as usize {
            return None;
        }
        for j in 1..4u8 {
            if j < n && buf[j as usize] & 0xc0 != 0x80 {
                return None;
            }
        }
        let mut cp = 0u32;
        for j in 0..4u8 {
            if j < n {
                let mask = if j == 0 {
                    0xffu8 >> (if n == 1 { 1 } else { n + 1 })
                } else {
                    0x3f
                };
                cp |= ((buf[j as usize] & mask) as u32) << (6 * (n - 1 - j));
            }
        }
        let min = match n {
            1 => 0,
            2 => 0x80,
            3 => 0x800,
            _ => 0x10000,
        };
        if cp < min || (cp >= 0xd800 && cp <= 0xdfff) || cp > 0x10ffff {
            return None;
        }
        Some((cp, n))
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn equivalence() {
        let arr: [u8; 4] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(decode(&arr[..len]), reference(&arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_utf8_decode(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
) -> i32 {
    match decode(core::slice::from_raw_parts(buf, len)) {
        Some((c, n)) => {
            *o0 = c as u64;
            *o1 = n as u64;
            1
        }
        None => 0,
    }
}
