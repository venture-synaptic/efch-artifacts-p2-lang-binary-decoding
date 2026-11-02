// Entero de longitud variable de QUIC (RFC 9000, §16). EXP-005.

pub fn decode(buf: &[u8]) -> Option<(u64, u8)> {
    let first = *buf.first()?;
    let len = 1usize << (first >> 6);
    let bytes = buf.get(..len)?;
    let mut v = u64::from(first & 0x3f);
    for &b in &bytes[1..] {
        v = (v << 8) | u64::from(b);
    }
    Some((v, len as u8))
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn reference(buf: &[u8]) -> Option<(u64, u8)> {
        if buf.is_empty() {
            return None;
        }
        let n = 1u8 << (buf[0] >> 6);
        if buf.len() < n as usize {
            return None;
        }
        let mut v = 0u64;
        for j in 0..8u8 {
            if j < n {
                let b = if j == 0 {
                    buf[0] & 0x3f
                } else {
                    buf[j as usize]
                };
                v |= u64::from(b) << (8 * (n - 1 - j));
            }
        }
        Some((v, n))
    }

    #[kani::proof]
    #[kani::unwind(9)]
    fn equivalence() {
        let arr: [u8; 8] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(decode(&arr[..len]), reference(&arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_quic_varint_decode(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
) -> i32 {
    match decode(core::slice::from_raw_parts(buf, len)) {
        Some((v, n)) => {
            *o0 = v;
            *o1 = n as u64;
            1
        }
        None => 0,
    }
}
