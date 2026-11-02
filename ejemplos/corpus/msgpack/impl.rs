// Entero de MessagePack: fixint positivo y negativo, uint8..64 e int8..64. EXP-005.

pub fn decode(buf: &[u8]) -> Option<(u64, bool, u8)> {
    let (&tag, rest) = buf.split_first()?;
    let (len, signed) = match tag {
        0x00..=0x7f => return Some((u64::from(tag), false, 1)),
        0xe0..=0xff => return Some((i64::from(tag as i8) as u64, true, 1)),
        0xcc..=0xcf => (1usize << (tag - 0xcc), false),
        0xd0..=0xd3 => (1usize << (tag - 0xd0), true),
        _ => return None,
    };
    let bytes = rest.get(..len)?;
    let fill = if signed && bytes[0] & 0x80 != 0 {
        0xff
    } else {
        0
    };
    let mut be = [fill; 8];
    be[8 - len..].copy_from_slice(bytes);
    Some((u64::from_be_bytes(be), signed, len as u8 + 1))
}

#[cfg(kani)]
mod verification {
    use super::*;

    // Traducción directa de la especificación.
    fn reference(buf: &[u8]) -> Option<(u64, bool, u8)> {
        if buf.is_empty() {
            return None;
        }
        let b0 = buf[0];
        if b0 < 0x80 {
            return Some((b0 as u64, false, 1));
        }
        if b0 >= 0xe0 {
            return Some((b0 as i8 as i64 as u64, true, 1));
        }
        if b0 < 0xcc || b0 > 0xd3 {
            return None;
        }
        let sg = b0 >= 0xd0;
        let k = 1u8 << (b0 & 3);
        if buf.len() < k as usize + 1 {
            return None;
        }
        let mut u = 0u64;
        for j in 1..9u8 {
            if j <= k {
                u |= (buf[j as usize] as u64) << (8 * (k - j));
            }
        }
        let sh = 8 * (8 - k) as u32;
        let v = if sg {
            (((u << sh) as i64) >> sh) as u64
        } else {
            u
        };
        Some((v, sg, k + 1))
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
pub unsafe extern "C" fn rust_msgpack_int_decode(
    buf: *const u8,
    len: usize,
    o0: *mut u64,
    o1: *mut u64,
    o2: *mut u64,
) -> i32 {
    match decode(core::slice::from_raw_parts(buf, len)) {
        Some((v, s, n)) => {
            *o0 = v;
            *o1 = s as u64;
            *o2 = n as u64;
            1
        }
        None => 0,
    }
}
