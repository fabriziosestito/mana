use super::*;

// ---------------------------------------------------------------------------
// External Term Format (term_to_binary/binary_to_term) — the data subset:
// smalls, atoms, nil, lists (byte lists as STRING_EXT like BEAM), tuples,
// maps, floats, binaries. Pids/refs/funs are badarg (TODO(etf)); this
// encoder is also the wire format planned for mana_dist.

pub(crate) fn etf_encode(t: u64, out: &mut Vec<u8>) -> Result<(), ()> {
    match t & TAG_MASK {
        TAG_SMALL => {
            let v = t as i64 >> 3;
            if (0..=255).contains(&v) {
                out.push(97);
                out.push(v as u8);
            } else if (i32::MIN as i64..=i32::MAX as i64).contains(&v) {
                out.push(98);
                out.extend_from_slice(&(v as i32).to_be_bytes());
            } else {
                // SMALL_BIG_EXT for the 61-bit smalls beyond i32
                let (sign, mag) = if v < 0 { (1u8, (-(v as i128)) as u64) } else { (0, v as u64) };
                let bytes = mag.to_le_bytes();
                let n = bytes.iter().rposition(|&b| b != 0).map_or(1, |i| i + 1);
                out.push(110);
                out.push(n as u8);
                out.push(sign);
                out.extend_from_slice(&bytes[..n]);
            }
        }
        TAG_ATOM => {
            let b = atom_bytes(t);
            if b.len() <= 255 {
                out.push(119); // SMALL_ATOM_UTF8_EXT
                out.push(b.len() as u8);
            } else {
                out.push(118);
                out.extend_from_slice(&(b.len() as u16).to_be_bytes());
            }
            out.extend_from_slice(b);
        }
        _ if t == NIL => out.push(106),
        TAG_CONS => {
            // proper byte lists ≤ 65535 encode as STRING_EXT (BEAM parity)
            let mut bytes: Vec<u8> = Vec::new();
            let mut cur = t;
            let mut is_string = true;
            let mut len = 0usize;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let h = unsafe { *p };
                len += 1;
                if is_string && h & TAG_MASK == TAG_SMALL && (0..=255).contains(&(h as i64 >> 3)) {
                    bytes.push((h as i64 >> 3) as u8);
                } else {
                    is_string = false;
                }
                cur = unsafe { *p.add(1) };
            }
            if is_string && cur == NIL && len <= 65535 {
                out.push(107);
                out.extend_from_slice(&(len as u16).to_be_bytes());
                out.extend_from_slice(&bytes);
                return Ok(());
            }
            out.push(108); // LIST_EXT
            out.extend_from_slice(&(len as u32).to_be_bytes());
            let mut cur = t;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                etf_encode(unsafe { *p }, out)?;
                cur = unsafe { *p.add(1) };
            }
            etf_encode(cur, out)?; // tail (NIL for proper lists)
        }
        TAG_BOXED if t != 0 => unsafe {
            let p = t as *const u64;
            match *p & 0xff {
                KIND_TUPLE => {
                    let n = (*p >> 8) as usize;
                    if n <= 255 {
                        out.push(104);
                        out.push(n as u8);
                    } else {
                        out.push(105);
                        out.extend_from_slice(&(n as u32).to_be_bytes());
                    }
                    for i in 1..=n {
                        etf_encode(*p.add(i), out)?;
                    }
                }
                KIND_MAP => {
                    let n = (*p >> 8) as usize;
                    out.push(116);
                    out.extend_from_slice(&(n as u32).to_be_bytes());
                    for i in 0..n {
                        etf_encode(*p.add(1 + i), out)?;
                        etf_encode(*p.add(1 + n + i), out)?;
                    }
                }
                KIND_FLOAT => {
                    out.push(70);
                    let bits = *p.add(1);
                    out.extend_from_slice(&bits.to_be_bytes());
                }
                KIND_BIGNUM => {
                    let (neg, mag) = bignum_parts(t).unwrap();
                    let bytes = bigint::mag_to_bytes_le(mag);
                    if bytes.len() <= 255 {
                        out.push(110); // SMALL_BIG_EXT
                        out.push(bytes.len() as u8);
                    } else {
                        out.push(111); // LARGE_BIG_EXT
                        out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
                    }
                    out.push(neg as u8);
                    out.extend_from_slice(&bytes);
                }
                KIND_BIN | KIND_SUBBIN => {
                    let bytes = bin_bytes(t);
                    out.push(109);
                    out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
                    out.extend_from_slice(bytes);
                }
                _ => return Err(()),
            }
        },
        _ => return Err(()), // pids/refs — TODO(etf)
    }
    Ok(())
}

pub(crate) struct EtfDec<'a> {
    pub(crate) buf: &'a [u8],
    pub(crate) pos: usize,
}

impl<'a> EtfDec<'a> {
    pub(crate) fn take(&mut self, n: usize) -> Result<&'a [u8], ()> {
        if self.pos + n > self.buf.len() {
            return Err(());
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }
    pub(crate) fn u8(&mut self) -> Result<u8, ()> {
        Ok(self.take(1)?[0])
    }
    pub(crate) fn u16(&mut self) -> Result<u16, ()> {
        Ok(u16::from_be_bytes(self.take(2)?.try_into().unwrap()))
    }
    pub(crate) fn u32(&mut self) -> Result<u32, ()> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().unwrap()))
    }
}

/// Decode one term. `safe` refuses atoms not already interned. All heap
/// results are built with the partial term rooted via a caller frame —
/// here we allocate bottom-up and root intermediates in Rust Vecs of
/// ETERNAL-safe? No: we allocate in the nursery; every recursive result
/// is immediately stored into its parent allocation, and parents are
/// allocated AFTER children — children must be rooted across the parent
/// alloc. We use a per-call stack frame for the child list.
pub(crate) fn etf_decode(ctx: &mut ProcCtx, d: &mut EtfDec, safe: bool) -> Result<u64, ()> {
    let tag = d.u8()?;
    match tag {
        97 => Ok(((d.u8()? as i64) << 3) as u64 | TAG_SMALL),
        98 => {
            let v = i32::from_be_bytes(d.take(4)?.try_into().unwrap()) as i64;
            Ok(((v << 3) as u64) | TAG_SMALL)
        }
        110 | 111 => {
            let n = if tag == 110 {
                d.u8()? as usize
            } else {
                u32::from_be_bytes(d.take(4)?.try_into().unwrap()) as usize
            };
            let sign = d.u8()?;
            let mag_bytes = d.take(n)?.to_vec();
            let mag = bigint::mag_from_bytes_le(&mag_bytes);
            Ok(make_int_mag(ctx, sign == 1 && !mag.is_empty(), &mag))
        }
        118 | 119 | 100 | 115 => {
            let n = if tag == 119 || tag == 115 {
                d.u8()? as usize
            } else {
                d.u16()? as usize
            };
            let name = d.take(n)?;
            if safe && !atom_exists(name) {
                return Err(());
            }
            Ok(atom_intern(name))
        }
        106 => Ok(NIL),
        107 => {
            let n = d.u16()? as usize;
            let bytes = d.take(n)?.to_vec();
            Ok(bytes_to_byte_list(ctx, &bytes))
        }
        108 => {
            let n = d.u32()? as usize;
            // per-call root frame: [prev, len, children...] in a Vec whose
            // capacity is fixed up front (the buffer must never move)
            let saved = ctx.roots_head;
            let mut fr: Vec<u64> = Vec::with_capacity(3 + n);
            fr.push(saved);
            fr.push(0);
            ctx.roots_head = fr.as_ptr() as u64;
            for _ in 0..n {
                let item = match etf_decode(ctx, d, safe) {
                    Ok(v) => v,
                    Err(()) => {
                        ctx.roots_head = saved;
                        return Err(());
                    }
                };
                fr.push(item);
                fr[1] += 1;
            }
            let tail = match etf_decode(ctx, d, safe) {
                Ok(v) => v,
                Err(()) => {
                    ctx.roots_head = saved;
                    return Err(());
                }
            };
            fr.push(tail);
            fr[1] += 1;
            let mut list = fr[2 + n];
            for i in (0..n).rev() {
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[2 + i];
                    *cell.add(1) = list;
                }
                list = cell as u64 | TAG_CONS;
                fr[2 + n] = list; // keep the partial list rooted
            }
            ctx.roots_head = saved;
            Ok(list)
        }
        104 | 105 => {
            let n = if tag == 104 { d.u8()? as usize } else { d.u32()? as usize };
            let saved = ctx.roots_head;
            let mut fr: Vec<u64> = Vec::with_capacity(2 + n);
            fr.push(saved);
            fr.push(0);
            ctx.roots_head = fr.as_ptr() as u64;
            for _ in 0..n {
                let item = match etf_decode(ctx, d, safe) {
                    Ok(v) => v,
                    Err(()) => {
                        ctx.roots_head = saved;
                        return Err(());
                    }
                };
                fr.push(item);
                fr[1] += 1;
            }
            let t = alloc_nursery(ctx, 1 + n);
            unsafe {
                *t = ((n as u64) << 8) | KIND_TUPLE;
                for i in 0..n {
                    *t.add(1 + i) = fr[2 + i];
                }
            }
            ctx.roots_head = saved;
            Ok(t as u64)
        }
        116 => {
            let n = d.u32()? as usize;
            let saved = ctx.roots_head;
            let mut fr: Vec<u64> = Vec::with_capacity(2 + 2 * n);
            fr.push(saved);
            fr.push(0);
            ctx.roots_head = fr.as_ptr() as u64;
            for _ in 0..(2 * n) {
                let item = match etf_decode(ctx, d, safe) {
                    Ok(v) => v,
                    Err(()) => {
                        ctx.roots_head = saved;
                        return Err(());
                    }
                };
                fr.push(item);
                fr[1] += 1;
            }
            let m = alloc_nursery(ctx, 1 + 2 * n);
            unsafe {
                *m = ((n as u64) << 8) | KIND_MAP;
                for i in 0..n {
                    *m.add(1 + i) = fr[2 + 2 * i];
                    *m.add(1 + n + i) = fr[2 + 2 * i + 1];
                }
            }
            ctx.roots_head = saved;
            Ok(mana_rt_map_norm(m as u64))
        }
        70 => {
            let bits = u64::from_be_bytes(d.take(8)?.try_into().unwrap());
            let f = f64::from_bits(bits);
            let ctxp = ctx as *mut ProcCtx;
            Ok(box_float(unsafe { &mut *ctxp }, f))
        }
        109 => {
            let n = d.u32()? as usize;
            let bytes = d.take(n)?.to_vec();
            Ok(bytes_to_new_bin(ctx, &bytes))
        }
        _ => Err(()),
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_term_to_binary(ctx: *mut ProcCtx, t: u64, _opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = vec![131u8];
    if etf_encode(t, &mut out).is_err() {
        return raise_badarg(ctx);
    }
    bytes_to_new_bin(ctx, &out)
}

#[no_mangle]
pub extern "C" fn mana_rt_binary_to_term(ctx: *mut ProcCtx, bin: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((bp, blen)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let bytes: Vec<u8> = unsafe { std::slice::from_raw_parts(bp, blen) }.to_vec();
    let mut safe = false;
    let mut used = false;
    let mut cur = opts;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let o = unsafe { *p };
        if o & TAG_MASK == TAG_ATOM {
            match atom_bytes(o) {
                b"safe" => safe = true,
                b"used" => used = true,
                _ => {}
            }
        }
        cur = unsafe { *p.add(1) };
    }
    if bytes.first() != Some(&131) {
        return raise_badarg(ctx);
    }
    let mut d = EtfDec { buf: &bytes, pos: 1 };
    let r = etf_decode(ctx, &mut d, safe);
    let Ok(term) = r else {
        return raise_badarg(ctx);
    };
    if used {
        let saved = ctx.roots_head;
        let mut fr = [0u64, 1, term];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        let t = alloc_nursery(ctx, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = fr[2];
            *t.add(2) = ((d.pos as i64) << 3) as u64 | TAG_SMALL;
        }
        ctx.roots_head = saved;
        return t as u64;
    }
    term
}
