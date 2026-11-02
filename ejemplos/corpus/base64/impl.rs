// Bloque base64 de 4 caracteres (RFC 4648, §4); bits de relleno no nulos rechazados. EXP-005.

fn sextet(c: u8) -> Option<u32> {
    match c {
        b'A'..=b'Z' => Some(u32::from(c - b'A')),
        b'a'..=b'z' => Some(u32::from(c - b'a' + 26)),
        b'0'..=b'9' => Some(u32::from(c - b'0' + 52)),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

pub fn decode(s: &[u8]) -> Option<(u32, u8)> {
    let &[a, b, c, d] = s else { return None };
    let w = sextet(a)? << 18 | sextet(b)? << 12;
    match (c, d) {
        (b'=', b'=') => (w & 0xffff == 0).then_some((w >> 16, 1)),
        (_, b'=') => {
            let w = w | sextet(c)? << 6;
            (w & 0xff == 0).then_some((w >> 8, 2))
        }
        _ => Some((w | sextet(c)? << 6 | sextet(d)?, 3)),
    }
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn val(c: u8) -> u8 {
        if c >= 0x41 && c <= 0x5a {
            c - 0x41
        } else if c >= 0x61 && c <= 0x7a {
            c - 71
        } else if c >= 0x30 && c <= 0x39 {
            c + 4
        } else if c == 0x2b {
            62
        } else if c == 0x2f {
            63
        } else {
            64
        }
    }

    fn reference(s: &[u8]) -> Option<(u32, u8)> {
        if s.len() != 4 {
            return None;
        }
        let (v0, v1, v2, v3) = (val(s[0]), val(s[1]), val(s[2]), val(s[3]));
        let (p2, p3) = (s[2] == 0x3d, s[3] == 0x3d);
        if v0 == 64 || v1 == 64 || (p2 && !p3) || (!p2 && v2 == 64) || (!p3 && v3 == 64) {
            return None;
        }
        let w = (v0 as u32) << 18
            | (v1 as u32) << 12
            | (if p2 { 0 } else { v2 as u32 }) << 6
            | (if p3 { 0 } else { v3 as u32 });
        if p2 {
            if w & 0xffff != 0 {
                None
            } else {
                Some((w >> 16, 1))
            }
        } else if p3 {
            if w & 0xff != 0 {
                None
            } else {
                Some((w >> 8, 2))
            }
        } else {
            Some((w, 3))
        }
    }

    #[kani::proof]
    fn equivalence() {
        let arr: [u8; 4] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(decode(&arr[..len]), reference(&arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_base64_block_decode(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
) -> i32 {
    match decode(core::slice::from_raw_parts(buf, len)) {
        Some((w, n)) => {
            *o0 = w as u64;
            *o1 = n as u64;
            1
        }
        None => 0,
    }
}
