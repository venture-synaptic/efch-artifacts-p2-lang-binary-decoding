// Validación de cabecera IPv4 (RFC 791, §3.1) con suma de comprobación (RFC 1071). EXP-005.

pub fn check(h: &[u8]) -> Option<(u8, u16)> {
    if h.len() < 20 {
        return None;
    }
    let (version, ihl) = (h[0] >> 4, h[0] & 0x0f);
    let header_len = usize::from(ihl) * 4;
    let total = u16::from_be_bytes([h[2], h[3]]);
    if version != 4 || ihl < 5 || h.len() < header_len || usize::from(total) < header_len {
        return None;
    }
    let mut sum: u32 = h[..header_len]
        .chunks_exact(2)
        .map(|w| u32::from(u16::from_be_bytes([w[0], w[1]])))
        .sum();
    while sum > 0xffff {
        sum = (sum & 0xffff) + (sum >> 16);
    }
    (sum == 0xffff).then_some((ihl, total))
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn reference(h: &[u8]) -> Option<(u8, u16)> {
        if h.len() < 20 {
            return None;
        }
        let ver = h[0] >> 4;
        let ihl = h[0] & 0x0f;
        let hl = (ihl as u16) << 2;
        let tot = (h[2] as u16) << 8 | h[3] as u16;
        if ver != 4 || ihl < 5 || (h.len() as u16) < hl || tot < hl {
            return None;
        }
        let mut s = 0u32;
        for j in 0..30u16 {
            if j < (ihl as u16) << 1 {
                s += (h[2 * j as usize] as u32) << 8 | h[2 * j as usize + 1] as u32;
            }
        }
        let f1 = (s & 0xffff) + (s >> 16);
        let f2 = (f1 & 0xffff) + (f1 >> 16);
        if f2 == 0xffff {
            Some((ihl, tot))
        } else {
            None
        }
    }

    #[kani::proof]
    #[kani::unwind(31)]
    fn equivalence() {
        let arr: [u8; 60] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= arr.len());
        assert_eq!(check(&arr[..len]), reference(&arr[..len]));
    }
}

// --- ABI de EFCH para la medición (no cuenta como esfuerzo) ---
#[no_mangle]
pub unsafe extern "C" fn rust_ipv4_header_check(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
) -> i32 {
    match check(core::slice::from_raw_parts(buf, len)) {
        Some((i, t)) => {
            *o0 = i as u64;
            *o1 = t as u64;
            1
        }
        None => 0,
    }
}
