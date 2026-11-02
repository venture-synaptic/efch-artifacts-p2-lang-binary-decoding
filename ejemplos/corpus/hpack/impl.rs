// Entero de HPACK con prefijo de N bits (RFC 7541, §5.1), valor ≤ 2^32-1 y ≤ 6 bytes. EXP-005.

pub fn decode(n: u8, buf: &[u8]) -> Option<(u32, u8)> {
    if !(1..=8).contains(&n) {
        return None;
    }
    let mask = ((1u16 << n) - 1) as u8;
    let mut value = u64::from(*buf.first()? & mask);
    if value < u64::from(mask) {
        return Some((value as u32, 1));
    }
    for (i, &b) in buf.iter().enumerate().take(6).skip(1) {
        value += u64::from(b & 0x7f) << (7 * (i - 1));
        if b & 0x80 == 0 {
            return u32::try_from(value).ok().map(|v| (v, i as u8 + 1));
        }
    }
    None
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn reference(n: u8, buf: &[u8]) -> Option<(u32, u8)> {
        if n == 0 || n > 8 || buf.is_empty() {
            return None;
        }
        let mask = ((1u16 << n) - 1) as u8;
        let p = buf[0] & mask;
        if p < mask {
            return Some((p as u32, 1));
        }
        for t in 1..6usize {
            if t < buf.len() && buf[t] < 0x80 {
                let mut v = mask as u64;
                for j in 1..=t {
                    v += ((buf[j] & 0x7f) as u64) << (7 * (j - 1));
                }
                return if v > 0xffff_ffff {
                    None
                } else {
                    Some((v as u32, t as u8 + 1))
                };
            }
        }
        None
    }

    #[kani::proof]
    #[kani::unwind(7)]
    fn equivalence() {
        let n: u8 = kani::any();
        let arr: [u8; 6] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(decode(n, &arr[..len]), reference(n, &arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_hpack_int_decode(
    n: u64,
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
) -> i32 {
    match decode(n as u8, core::slice::from_raw_parts(buf, len)) {
        Some((v, k)) => {
            *o0 = v as u64;
            *o1 = k as u64;
            1
        }
        None => 0,
    }
}
