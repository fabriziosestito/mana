//! Arbitrary-precision integer magnitudes. A magnitude is a little-endian
//! vector of `u64` limbs. It is always normalized: it has no
//! most-significant zero limbs, and the empty slice is zero. The sign lives
//! in the term header, not here.
//!
//! The kernel is hand-rolled by a measured choice, not by dogma. The term
//! layout stores raw limbs, so a crate pays a limb-to-bignum conversion on
//! every operation. The in-tree A/B
//! (`cargo test --release -p mana-rt ab_ -- --ignored --nocapture`) shows
//! num-bigint 2-9x slower on the dominant 1-2 limb shapes (timestamps,
//! request ids). num-bigint is ahead only about 1.3x on decimal formatting.
//! The u128 property tests below and Conf.Big (BEAM as the oracle) gate
//! correctness.
//!
//! Before you change this decision, run the A/B again.

/// Removes the most-significant zero limbs.
pub fn normalize(mut v: Vec<u64>) -> Vec<u64> {
    while v.last() == Some(&0) {
        v.pop();
    }
    v
}

pub fn mag_is_zero(a: &[u64]) -> bool {
    a.is_empty()
}

pub fn mag_cmp(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    std::cmp::Ordering::Equal
}

pub fn mag_add(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut out = Vec::with_capacity(long.len() + 1);
    let mut carry = 0u128;
    for i in 0..long.len() {
        let s = long[i] as u128 + *short.get(i).unwrap_or(&0) as u128 + carry;
        out.push(s as u64);
        carry = s >> 64;
    }
    if carry != 0 {
        out.push(carry as u64);
    }
    out
}

/// Computes a - b. The caller must pass a >= b.
pub fn mag_sub(a: &[u64], b: &[u64]) -> Vec<u64> {
    debug_assert!(mag_cmp(a, b) != std::cmp::Ordering::Less);
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0i128;
    for i in 0..a.len() {
        let d = a[i] as i128 - *b.get(i).unwrap_or(&0) as i128 - borrow;
        if d < 0 {
            out.push((d + (1i128 << 64)) as u64);
            borrow = 1;
        } else {
            out.push(d as u64);
            borrow = 0;
        }
    }
    normalize(out)
}

pub fn mag_mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = out[i + j] as u128 + x as u128 * y as u128 + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        let mut k = i + b.len();
        while carry != 0 {
            let t = out[k] as u128 + carry;
            out[k] = t as u64;
            carry = t >> 64;
            k += 1;
        }
    }
    normalize(out)
}

/// Divides by a single limb and returns (quotient, remainder). `d` must not be zero.
pub fn mag_divrem_limb(a: &[u64], d: u64) -> (Vec<u64>, u64) {
    debug_assert!(d != 0);
    let mut q = vec![0u64; a.len()];
    let mut rem = 0u128;
    for i in (0..a.len()).rev() {
        let cur = (rem << 64) | a[i] as u128;
        q[i] = (cur / d as u128) as u64;
        rem = cur % d as u128;
    }
    (normalize(q), rem as u64)
}

/// Returns the number of significant bits.
pub fn mag_bits(a: &[u64]) -> u64 {
    match a.last() {
        None => 0,
        Some(&top) => (a.len() as u64 - 1) * 64 + (64 - top.leading_zeros() as u64),
    }
}

pub fn mag_shl(a: &[u64], n: u64) -> Vec<u64> {
    if a.is_empty() {
        return Vec::new();
    }
    let limbs = (n / 64) as usize;
    let bits = n % 64;
    let mut out = vec![0u64; limbs];
    if bits == 0 {
        out.extend_from_slice(a);
    } else {
        let mut carry = 0u64;
        for &x in a {
            out.push((x << bits) | carry);
            carry = x >> (64 - bits);
        }
        if carry != 0 {
            out.push(carry);
        }
    }
    normalize(out)
}

pub fn mag_shr(a: &[u64], n: u64) -> Vec<u64> {
    let limbs = (n / 64) as usize;
    if limbs >= a.len() {
        return Vec::new();
    }
    let bits = n % 64;
    let src = &a[limbs..];
    if bits == 0 {
        return normalize(src.to_vec());
    }
    let mut out = Vec::with_capacity(src.len());
    for i in 0..src.len() {
        let hi = if i + 1 < src.len() {
            src[i + 1] << (64 - bits)
        } else {
            0
        };
        out.push((src[i] >> bits) | hi);
    }
    normalize(out)
}

/// Long division. Returns (quotient, remainder). `b` must not be zero.
/// The algorithm is Knuth D: shift-normalized schoolbook division with
/// two-limb trial quotients and at most two correction steps.
pub fn mag_divrem(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    debug_assert!(!b.is_empty());
    if mag_cmp(a, b) == std::cmp::Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    if b.len() == 1 {
        let (q, r) = mag_divrem_limb(a, b[0]);
        return (q, if r == 0 { Vec::new() } else { vec![r] });
    }
    // Knuth D needs the top bit of the divisor set. Shift both operands by the same amount.
    let shift = b.last().unwrap().leading_zeros() as u64;
    let u = mag_shl(a, shift);
    let v = mag_shl(b, shift);
    let n = v.len();
    let m = u.len() - n;
    let mut u = {
        let mut t = u;
        t.push(0); // Room for the virtual high limb.
        t
    };
    let mut q = vec![0u64; m + 1];
    let vtop = v[n - 1] as u128;
    let vsec = v[n - 2] as u128;
    for j in (0..=m).rev() {
        // The trial quotient comes from the top two dividend limbs and the top divisor limb.
        let num = ((u[j + n] as u128) << 64) | u[j + n - 1] as u128;
        let mut qhat = num / vtop;
        let mut rhat = num % vtop;
        while qhat >> 64 != 0 || qhat * vsec > ((rhat << 64) | u[j + n - 2] as u128) {
            qhat -= 1;
            rhat += vtop;
            if rhat >> 64 != 0 {
                break;
            }
        }
        // u[j..j+n] -= qhat * v
        let mut borrow = 0i128;
        let mut carry = 0u128;
        for i in 0..n {
            let p = qhat * v[i] as u128 + carry;
            carry = p >> 64;
            let d = u[j + i] as i128 - (p as u64) as i128 - borrow;
            if d < 0 {
                u[j + i] = (d + (1i128 << 64)) as u64;
                borrow = 1;
            } else {
                u[j + i] = d as u64;
                borrow = 0;
            }
        }
        let d = u[j + n] as i128 - carry as i128 - borrow;
        if d < 0 {
            // qhat was one too large. Add v back.
            u[j + n] = (d + (1i128 << 64)) as u64;
            qhat -= 1;
            let mut carry = 0u128;
            for i in 0..n {
                let s = u[j + i] as u128 + v[i] as u128 + carry;
                u[j + i] = s as u64;
                carry = s >> 64;
            }
            u[j + n] = u[j + n].wrapping_add(carry as u64);
        } else {
            u[j + n] = d as u64;
        }
        q[j] = qhat as u64;
    }
    u.truncate(n);
    (normalize(q), mag_shr(&normalize(u), shift))
}

/// Converts decimal digits (no sign) to a magnitude. Returns None on a non-digit.
pub fn mag_from_decimal(digits: &[u8]) -> Option<Vec<u64>> {
    let mut out: Vec<u64> = Vec::new();
    // Each step consumes up to 19 digits (10^19 < 2^64): out = out*10^k + chunk.
    let mut i = 0;
    while i < digits.len() {
        let k = std::cmp::min(19, digits.len() - i);
        let mut chunk = 0u64;
        for &d in &digits[i..i + k] {
            if !d.is_ascii_digit() {
                return None;
            }
            chunk = chunk * 10 + (d - b'0') as u64;
        }
        let mul = 10u64.pow(k as u32 - 1) * 10; // 10^k. k<=19, so the value fits in u64 (10^19 fits).
        out = mag_add(&mag_mul(&out, &[mul]), &[chunk]);
        i += k;
    }
    Some(normalize(out))
}

/// Converts a magnitude to decimal digits (no sign).
pub fn mag_to_decimal(a: &[u64]) -> String {
    if a.is_empty() {
        return "0".to_string();
    }
    let mut cur = a.to_vec();
    let mut chunks: Vec<u64> = Vec::new();
    while !cur.is_empty() {
        let (q, r) = mag_divrem_limb(&cur, 10_000_000_000_000_000_000);
        chunks.push(r);
        cur = q;
    }
    let mut s = chunks.pop().unwrap().to_string();
    while let Some(c) = chunks.pop() {
        s.push_str(&format!("{:019}", c));
    }
    s
}

/// Converts a magnitude to f64. The result rounds to nearest through the top 128 bits.
pub fn mag_to_f64(a: &[u64]) -> f64 {
    match a.len() {
        0 => 0.0,
        1 => a[0] as f64,
        2 => a[1] as f64 * 1.8446744073709552e19 + a[0] as f64,
        n => {
            let hi = a[n - 1] as f64 * 1.8446744073709552e19 + a[n - 2] as f64;
            hi * 2f64.powi(64 * (n as i32 - 2))
        }
    }
}

/// Converts the exact integer part of a non-negative finite f64 to a magnitude.
pub fn f64_to_mag(v: f64) -> Vec<u64> {
    debug_assert!(v.is_finite() && v >= 0.0);
    if v < 1.0 {
        return Vec::new();
    }
    let bits = v.to_bits();
    let exp = ((bits >> 52) & 0x7ff) as i64 - 1023;
    let mantissa = (bits & ((1u64 << 52) - 1)) | (1u64 << 52); // Adds the implicit leading bit.
                                                               // value = mantissa * 2^(exp-52)
    let shift = exp - 52;
    if shift >= 0 {
        mag_shl(&[mantissa], shift as u64)
    } else {
        mag_shr(&[mantissa], (-shift) as u64)
    }
}

/// Returns the magnitude as little-endian bytes (the ETF SMALL_BIG/LARGE_BIG payload).
pub fn mag_to_bytes_le(a: &[u64]) -> Vec<u8> {
    let mut out = Vec::with_capacity(a.len() * 8);
    for &l in a {
        out.extend_from_slice(&l.to_le_bytes());
    }
    while out.last() == Some(&0) {
        out.pop();
    }
    out
}

pub fn mag_from_bytes_le(bytes: &[u8]) -> Vec<u64> {
    let mut out = Vec::with_capacity(bytes.len().div_ceil(8));
    for chunk in bytes.chunks(8) {
        let mut b = [0u8; 8];
        b[..chunk.len()].copy_from_slice(chunk);
        out.push(u64::from_le_bytes(b));
    }
    normalize(out)
}

#[cfg(test)]
mod ab_bench {
    //! A/B benchmark: the hand-rolled kernel against num-bigint on our workload shapes.
    //! num-bigint pays the term-boundary conversion (&[u64] limbs to BigUint and
    //! back) because the heap layout stores raw limbs. That conversion is the real
    //! cost that the runtime will see. Run with:
    //!   cargo test --release -p mana-rt ab_ -- --ignored --nocapture
    use super::*;
    use num_bigint::BigUint;
    use std::time::Instant;

    fn to_big(a: &[u64]) -> BigUint {
        let mut bytes = Vec::with_capacity(a.len() * 8);
        for &l in a {
            bytes.extend_from_slice(&l.to_le_bytes());
        }
        BigUint::from_bytes_le(&bytes)
    }

    fn from_big(b: &BigUint) -> Vec<u64> {
        b.to_u64_digits()
    }

    fn time(label: &str, iters: u32, mut f: impl FnMut() -> u64) {
        // Warmup loop. Its time is not measured.
        let mut sink = 0u64;
        for _ in 0..iters / 10 {
            sink = sink.wrapping_add(f());
        }
        let t = Instant::now();
        for _ in 0..iters {
            sink = sink.wrapping_add(f());
        }
        let ns = t.elapsed().as_nanos() as f64 / iters as f64;
        println!("{:<38} {:>9.1} ns/op (sink {})", label, ns, sink & 1);
    }

    #[test]
    #[ignore]
    fn ab_kernel_vs_num_bigint() {
        let one = vec![0x1234_5678_9abc_def0u64]; // 1 limb (timestamps)
        let two = vec![u64::MAX, 0x1f]; // 2 limbs (for example, ns since epoch)
        let four =
            mag_from_decimal(b"123456789012345678901234567890123456789012345678901234567890")
                .unwrap();
        let f200 = {
            // factorial(200), the Conf.Big stress shape (~1245 bits)
            let mut m = vec![1u64];
            for i in 2..=200u64 {
                m = mag_mul(&m, &[i]);
            }
            m
        };

        println!("--- 1-2 limb (dominant runtime case) ---");
        time("hand add 2-limb", 2_000_000, || mag_add(&two, &one)[0]);
        time("crate add 2-limb (+conv)", 2_000_000, || {
            from_big(&(to_big(&two) + to_big(&one)))[0]
        });
        time("hand mul 2x1", 1_000_000, || mag_mul(&two, &one)[0]);
        time("crate mul 2x1 (+conv)", 1_000_000, || {
            from_big(&(to_big(&two) * to_big(&one)))[0]
        });
        time("hand divrem 2/1", 1_000_000, || {
            mag_divrem(&two, &one).1.first().copied().unwrap_or(0)
        });
        time("crate divrem 2/1 (+conv)", 1_000_000, || {
            from_big(&(to_big(&two) % to_big(&one)))
                .first()
                .copied()
                .unwrap_or(0)
        });
        time("hand to_decimal 2-limb", 200_000, || {
            mag_to_decimal(&two).len() as u64
        });
        time("crate to_decimal 2-limb (+conv)", 200_000, || {
            to_big(&two).to_string().len() as u64
        });

        println!("--- 4 limb ---");
        time("hand mul 4x4", 500_000, || mag_mul(&four, &four)[0]);
        time("crate mul 4x4 (+conv)", 500_000, || {
            from_big(&(to_big(&four) * to_big(&four)))[0]
        });
        time("hand divrem 4/2", 500_000, || mag_divrem(&four, &two).0[0]);
        time("crate divrem 4/2 (+conv)", 500_000, || {
            from_big(&(to_big(&four) / to_big(&two)))[0]
        });

        println!("--- factorial(200) scale (~20 limbs) ---");
        time("hand fact200 mul-chain", 5_000, || {
            let mut m = vec![1u64];
            for i in 2..=200u64 {
                m = mag_mul(&m, &[i]);
            }
            m[0]
        });
        time("crate fact200 mul-chain (+conv)", 5_000, || {
            // One conversion per step. The runtime term boundary pays the same cost.
            let mut m = vec![1u64];
            for i in 2..=200u64 {
                m = from_big(&(to_big(&m) * BigUint::from(i)));
            }
            m[0]
        });
        time("hand to_decimal f200 (375 digits)", 20_000, || {
            mag_to_decimal(&f200).len() as u64
        });
        time("crate to_decimal f200 (+conv)", 20_000, || {
            to_big(&f200).to_string().len() as u64
        });
        time("hand divrem f200/4", 100_000, || {
            mag_divrem(&f200, &four).1.first().copied().unwrap_or(0)
        });
        time("crate divrem f200/4 (+conv)", 100_000, || {
            from_big(&(to_big(&f200) % to_big(&four)))
                .first()
                .copied()
                .unwrap_or(0)
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    fn from_u128(v: u128) -> Vec<u64> {
        normalize(vec![v as u64, (v >> 64) as u64])
    }

    fn to_u128(a: &[u64]) -> u128 {
        match a.len() {
            0 => 0,
            1 => a[0] as u128,
            2 => a[0] as u128 | ((a[1] as u128) << 64),
            _ => panic!("too big for u128"),
        }
    }

    #[test]
    fn add_sub_mul_divrem_vs_u128() {
        let vals: Vec<u128> = vec![
            0,
            1,
            2,
            9,
            10,
            255,
            1 << 60,
            (1 << 61) - 1,
            u64::MAX as u128,
            u64::MAX as u128 + 1,
            12345678901234567890,
            (1u128 << 100) + 12345,
            u128::MAX >> 1,
        ];
        for &x in &vals {
            for &y in &vals {
                let (a, b) = (from_u128(x), from_u128(y));
                if let Some(s) = x.checked_add(y) {
                    assert_eq!(to_u128(&mag_add(&a, &b)), s, "add {} {}", x, y);
                }
                if x >= y {
                    assert_eq!(to_u128(&mag_sub(&a, &b)), x - y, "sub {} {}", x, y);
                }
                if let Some(m) = x.checked_mul(y) {
                    assert_eq!(to_u128(&mag_mul(&a, &b)), m, "mul {} {}", x, y);
                }
                if y != 0 {
                    let (q, r) = mag_divrem(&a, &b);
                    assert_eq!(to_u128(&q), x / y, "div {} {}", x, y);
                    assert_eq!(to_u128(&r), x % y, "rem {} {}", x, y);
                }
                assert_eq!(mag_cmp(&a, &b), x.cmp(&y));
            }
        }
    }

    #[test]
    fn decimal_roundtrip() {
        for s in [
            "0",
            "1",
            "10",
            "9223372036854775807",
            "18446744073709551616",
            "340282366920938463463374607431768211456",
            "999999999999999999999999999999999999999999999999",
            "123456789012345678901234567890123456789012345678901234567890",
        ] {
            let m = mag_from_decimal(s.as_bytes()).unwrap();
            assert_eq!(mag_to_decimal(&m), s, "roundtrip {}", s);
        }
        assert!(mag_from_decimal(b"12x4").is_none());
    }

    #[test]
    fn big_multiply_divide_identity() {
        // Multiply (10^40 + 7) by (10^30 + 3). Then divide back.
        let a = mag_from_decimal(b"10000000000000000000000000000000000000007").unwrap();
        let b = mag_from_decimal(b"1000000000000000000000000000003").unwrap();
        let p = mag_mul(&a, &b);
        assert_eq!(
            mag_to_decimal(&p),
            "10000000000000000000000000000030000000007000000000000000000000000000021"
        );
        let (q, r) = mag_divrem(&p, &b);
        assert_eq!(mag_cmp(&q, &a), Ordering::Equal);
        assert!(mag_is_zero(&r));
        let p1 = mag_add(&p, &[5]);
        let (q1, r1) = mag_divrem(&p1, &b);
        assert_eq!(mag_cmp(&q1, &a), Ordering::Equal);
        assert_eq!(to_u128(&r1), 5);
    }

    #[test]
    fn shifts() {
        let one = vec![1u64];
        assert_eq!(mag_bits(&mag_shl(&one, 127)), 128);
        assert_eq!(
            mag_cmp(&mag_shr(&mag_shl(&one, 127), 127), &one),
            Ordering::Equal
        );
        let v = mag_from_decimal(b"123456789123456789123456789").unwrap();
        assert_eq!(mag_cmp(&mag_shr(&mag_shl(&v, 67), 67), &v), Ordering::Equal);
    }

    #[test]
    fn f64_bridge() {
        assert_eq!(f64_to_mag(0.0), Vec::<u64>::new());
        assert_eq!(f64_to_mag(1.0), vec![1]);
        assert_eq!(f64_to_mag(2f64.powi(80)), mag_shl(&[1], 80));
        assert_eq!(mag_to_f64(&mag_shl(&[1], 80)), 2f64.powi(80));
        assert_eq!(mag_to_f64(&[123456]), 123456.0);
    }

    #[test]
    fn bytes_roundtrip() {
        for s in [
            "1",
            "255",
            "256",
            "18446744073709551616",
            "123456789012345678901234567890",
        ] {
            let m = mag_from_decimal(s.as_bytes()).unwrap();
            assert_eq!(
                mag_cmp(&mag_from_bytes_le(&mag_to_bytes_le(&m)), &m),
                Ordering::Equal
            );
        }
    }

    #[test]
    fn knuth_d_correction_paths() {
        // The operands force qhat corrections: their top limbs are close.
        let a = mag_from_decimal(b"340282366920938463463374607431768211455000000001").unwrap();
        let b = mag_from_decimal(b"18446744073709551615999999999").unwrap();
        let (q, r) = mag_divrem(&a, &b);
        // Check by reconstruction: q*b + r must equal a.
        let back = mag_add(&mag_mul(&q, &b), &r);
        assert_eq!(mag_cmp(&back, &a), Ordering::Equal);
        assert_eq!(mag_cmp(&r, &b), Ordering::Less);
    }
}
