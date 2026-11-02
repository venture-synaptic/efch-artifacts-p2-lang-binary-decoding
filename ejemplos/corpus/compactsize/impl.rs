// CompactSize de Bitcoin, solo en forma canónica. EXP-005.

pub fn decode(buf: &[u8]) -> Option<(u64, u8)> {
    let (&tag, rest) = buf.split_first()?;
    let (len, min) = match tag {
        0..=0xfc => return Some((u64::from(tag), 1)),
        0xfd => (2, 0xfd),
        0xfe => (4, 0x1_0000),
        0xff => (8, 0x1_0000_0000),
    };
    let mut le = [0u8; 8];
    le[..len].copy_from_slice(rest.get(..len)?);
    let v = u64::from_le_bytes(le);
    (v >= min).then_some((v, len as u8 + 1))
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn reference(buf: &[u8]) -> Option<(u64, u8)> {
        if buf.is_empty() {
            return None;
        }
        let b0 = buf[0];
        if b0 < 0xfd {
            return Some((b0 as u64, 1));
        }
        let k: u8 = if b0 == 0xfd {
            2
        } else if b0 == 0xfe {
            4
        } else {
            8
        };
        if buf.len() < k as usize + 1 {
            return None;
        }
        let mut v = 0u64;
        for j in 1..9u8 {
            if j <= k {
                v |= (buf[j as usize] as u64) << (8 * (j - 1));
            }
        }
        let min = if k == 2 {
            0xfd
        } else if k == 4 {
            0x10000
        } else {
            0x1_0000_0000
        };
        if v < min {
            None
        } else {
            Some((v, k + 1))
        }
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
pub unsafe extern "C" fn rust_compactsize_decode(
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
