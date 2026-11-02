// Cabecera de un elemento CBOR (RFC 8949, §3); información adicional 28..31 es error. EXP-005.

pub fn decode(buf: &[u8]) -> Option<(u8, u64, u8)> {
    let ib = *buf.first()?;
    let (major, info) = (ib >> 5, ib & 0x1f);
    let extra = match info {
        0..=23 => return Some((major, u64::from(info), 1)),
        24..=27 => 1usize << (info - 24),
        _ => return None,
    };
    let arg = buf
        .get(1..=extra)?
        .iter()
        .fold(0u64, |acc, &b| (acc << 8) | u64::from(b));
    if major == 7 && info == 24 && arg < 32 {
        return None;
    }
    Some((major, arg, extra as u8 + 1))
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn reference(buf: &[u8]) -> Option<(u8, u64, u8)> {
        if buf.is_empty() {
            return None;
        }
        let mt = buf[0] >> 5;
        let ai = buf[0] & 0x1f;
        if ai < 24 {
            return Some((mt, ai as u64, 1));
        }
        if ai > 27 {
            return None;
        }
        let k = 1u8 << (ai - 24);
        if buf.len() < k as usize + 1 {
            return None;
        }
        let mut v = 0u64;
        for j in 1..9u8 {
            if j <= k {
                v |= (buf[j as usize] as u64) << (8 * (k - j));
            }
        }
        if mt == 7 && ai == 24 && v < 32 {
            return None;
        }
        Some((mt, v, k + 1))
    }

    #[kani::proof]
    #[kani::unwind(10)]
    fn equivalence() {
        let arr: [u8; 9] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(decode(&arr[..len]), reference(&arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_cbor_head_decode(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
    o2: *mut u64,
) -> i32 {
    match decode(core::slice::from_raw_parts(buf, len)) {
        Some((m, a, n)) => {
            *o0 = m as u64;
            *o1 = a;
            *o2 = n as u64;
            1
        }
        None => 0,
    }
}
