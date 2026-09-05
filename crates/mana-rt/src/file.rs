//! Native `file` operations. The OTP modules file.erl and prim_file are never
//! compiled.
//!
//! Every operation is a direct blocking syscall on the scheduler thread, the
//! same as stdout today. Local-disk operations take microseconds. A scheduler
//! that is stuck in a slow syscall (for example NFS) stalls STW for that
//! duration. TODO(io-pool): move the syscalls to a blocking pool.

use super::*;

pub(crate) struct FileEntry {
    pub(crate) file: std::fs::File,
    pub(crate) binary: bool,
}

pub(crate) struct FileTable {
    pub(crate) slots: Vec<Option<FileEntry>>,
    pub(crate) free: Vec<usize>,
}

pub(crate) static FILES: std::sync::Mutex<FileTable> = std::sync::Mutex::new(FileTable {
    slots: Vec::new(),
    free: Vec::new(),
});

/// Builds a raw byte list without utf8 decoding. In list mode, file:read returns bytes.
pub(crate) fn bytes_to_byte_list(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &b in bytes.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// Maps an io::Error to a posix error atom. The names match the BEAM file:posix() type.
pub(crate) fn posix_atom(e: &std::io::Error) -> u64 {
    let name: &[u8] = match e.raw_os_error() {
        Some(libc) => match libc {
            1 => b"eperm",
            2 => b"enoent",
            9 => b"ebadf",
            13 => b"eacces",
            17 => b"eexist",
            18 => b"exdev",
            20 => b"enotdir",
            21 => b"eisdir",
            22 => b"einval",
            28 => b"enospc",
            36 => b"enametoolong",
            // BEAM efile maps ENOTEMPTY to eexist. This is an old compatibility quirk.
            39 => b"eexist",
            _ => b"einval",
        },
        None => match e.kind() {
            std::io::ErrorKind::NotFound => b"enoent",
            std::io::ErrorKind::PermissionDenied => b"eacces",
            std::io::ErrorKind::AlreadyExists => b"eexist",
            _ => b"einval",
        },
    };
    atom_intern(name)
}

/// Extracts a filesystem path from chardata or from an atom.
pub(crate) fn path_of(t: u64) -> Result<std::path::PathBuf, ()> {
    let mut bytes = Vec::new();
    if t & TAG_MASK == TAG_ATOM {
        bytes.extend_from_slice(atom_bytes(t));
    } else {
        chardata_flatten(t, &mut bytes)?;
    }
    let s = String::from_utf8(bytes).map_err(|_| ())?;
    Ok(std::path::PathBuf::from(s))
}

/// Builds {Tag, Value} in the nursery and roots Value across the allocation.
pub(crate) fn pair_term(ctx: &mut ProcCtx, tag: &[u8], v: u64) -> u64 {
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, v];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(tag);
        *p.add(2) = fr[2];
    }
    ctx.roots_head = saved;
    p as u64
}

pub(crate) fn err_tuple(ctx: &mut ProcCtx, e: &std::io::Error) -> u64 {
    let a = posix_atom(e);
    pair_term(ctx, b"error", a)
}

pub(crate) fn file_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"mana_file");
        *p.add(2) = ((idx as u64) << 3) | TAG_SMALL;
    }
    p as u64
}

pub(crate) fn file_resolve(t: u64) -> Option<usize> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    unsafe {
        let p = t as *const u64;
        if *p != (2 << 8) | KIND_TUPLE {
            return None;
        }
        let tag = *p.add(1);
        if tag & TAG_MASK != TAG_ATOM || atom_bytes(tag) != b"mana_file" {
            return None;
        }
        let idx = *p.add(2);
        if idx & TAG_MASK != TAG_SMALL {
            return None;
        }
        Some((idx as i64 >> 3) as usize)
    }
}

/// Converts posix seconds to {{Y,M,D},{H,Mi,S}} in UTC. The 'local' option also
/// returns UTC. This is a documented divergence. The conformance tests use
/// {time, posix}.
pub(crate) fn civil_datetime(ctx: &mut ProcCtx, secs: i64) -> u64 {
    let days = secs.div_euclid(86400);
    let rem = secs.rem_euclid(86400);
    let (h, mi, s) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    // The civil_from_days algorithm of Howard Hinnant.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    let small = |v: i64| ((v << 3) as u64) | TAG_SMALL;
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let dt = alloc_nursery(ctx, 4);
    unsafe {
        *dt = (3 << 8) | KIND_TUPLE;
        *dt.add(1) = small(y);
        *dt.add(2) = small(m);
        *dt.add(3) = small(d);
    }
    fr[2] = dt as u64;
    let tm = alloc_nursery(ctx, 4);
    unsafe {
        *tm = (3 << 8) | KIND_TUPLE;
        *tm.add(1) = small(h);
        *tm.add(2) = small(mi);
        *tm.add(3) = small(s);
    }
    fr[3] = tm as u64;
    let pair = alloc_nursery(ctx, 3);
    unsafe {
        *pair = (2 << 8) | KIND_TUPLE;
        *pair.add(1) = fr[2];
        *pair.add(2) = fr[3];
    }
    ctx.roots_head = saved;
    pair as u64
}

// File op codes. The codegen function compile_file_bif mirrors these values.
pub const F_READ_FILE: u64 = 0;

pub const F_WRITE_FILE: u64 = 1;

pub const F_WRITE_FILE3: u64 = 2;

pub const F_OPEN: u64 = 3;

pub const F_CLOSE: u64 = 4;

pub const F_READ: u64 = 5;

pub const F_WRITE: u64 = 6;

pub const F_POSITION: u64 = 7;

pub const F_DELETE: u64 = 8;

pub const F_RENAME: u64 = 9;

pub const F_MAKE_DIR: u64 = 10;

pub const F_DEL_DIR: u64 = 11;

pub const F_LIST_DIR: u64 = 12;

pub const F_FILE_INFO: u64 = 13;

pub const F_FILE_INFO2: u64 = 14;

pub const F_COPY: u64 = 15;

pub const F_GET_CWD: u64 = 16;

#[no_mangle]
pub extern "C" fn mana_rt_file(ctx: *mut ProcCtx, op: u64, a: u64, b: u64, c: u64) -> u64 {
    use std::io::{Read, Seek, Write};
    let ctx = unsafe { &mut *ctx };
    let ok_atom = || atom_intern(b"ok");
    match op {
        F_READ_FILE => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::read(&path) {
                Ok(bytes) => {
                    let bin = bytes_to_new_bin(ctx, &bytes);
                    pair_term(ctx, b"ok", bin)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_WRITE_FILE | F_WRITE_FILE3 => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            let mut data = Vec::new();
            if iolist_flatten(b, &mut data).is_err() {
                return raise_badarg(ctx);
            }
            let mut append = false;
            if op == F_WRITE_FILE3 {
                let mut cur = c;
                while cur & TAG_MASK == TAG_CONS {
                    let p = (cur & !TAG_MASK) as *const u64;
                    let m = unsafe { *p };
                    if m & TAG_MASK == TAG_ATOM && atom_bytes(m) == b"append" {
                        append = true;
                    }
                    cur = unsafe { *p.add(1) };
                }
            }
            let res = if append {
                std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .and_then(|mut f| f.write_all(&data))
            } else {
                std::fs::write(&path, &data)
            };
            match res {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_OPEN => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            // The modes list holds read | write | append | exclusive | binary.
            // The code accepts and ignores raw, read_ahead, and delayed_write.
            let (mut read, mut write, mut append, mut excl, mut binary) =
                (false, false, false, false, false);
            let mut cur = b;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let m = unsafe { *p };
                if m & TAG_MASK == TAG_ATOM {
                    match atom_bytes(m) {
                        b"read" => read = true,
                        b"write" => write = true,
                        b"append" => append = true,
                        b"exclusive" => excl = true,
                        b"binary" => binary = true,
                        _ => {}
                    }
                }
                cur = unsafe { *p.add(1) };
            }
            if !read && !write && !append {
                read = true;
            }
            let mut o = std::fs::OpenOptions::new();
            o.read(read || (!write && !append));
            if append {
                o.append(true).create(true);
            } else if write {
                o.write(true).create(true);
                if !read {
                    o.truncate(true);
                }
            }
            if excl {
                o.create_new(true);
            }
            match o.open(&path) {
                Ok(file) => {
                    let idx = FILES.lock().unwrap().insert(FileEntry { file, binary });
                    let h = file_handle(ctx, idx);
                    pair_term(ctx, b"ok", h)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_CLOSE => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            let mut tab = FILES.lock().unwrap();
            if idx < tab.slots.len() && tab.slots[idx].take().is_some() {
                tab.free.push(idx);
                ok_atom()
            } else {
                drop(tab);
                pair_term(ctx, b"error", atom_intern(b"ebadf"))
            }
        }
        F_READ => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            if b & TAG_MASK != TAG_SMALL || (b as i64 >> 3) < 0 {
                return raise_badarg(ctx);
            }
            let n = (b as i64 >> 3) as usize;
            let mut buf = vec![0u8; n];
            let mut tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            let mut got = 0usize;
            let res = loop {
                match entry.file.read(&mut buf[got..]) {
                    Ok(0) => break Ok(got),
                    Ok(k) => {
                        got += k;
                        if got == n {
                            break Ok(got);
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                    Err(e) => break Err(e),
                }
            };
            let binary = entry.binary;
            drop(tab);
            match res {
                Ok(0) if n > 0 => atom_intern(b"eof"),
                Ok(got) => {
                    let data = if binary {
                        bytes_to_new_bin(ctx, &buf[..got])
                    } else {
                        bytes_to_byte_list(ctx, &buf[..got])
                    };
                    pair_term(ctx, b"ok", data)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_WRITE => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            let mut data = Vec::new();
            if iolist_flatten(b, &mut data).is_err() {
                return raise_badarg(ctx);
            }
            let mut tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            let res = entry.file.write_all(&data);
            drop(tab);
            match res {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_POSITION => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            // The location is N | bof | cur | eof | {bof, N} | {cur, N} | {eof, N}.
            let seek = |whence: &[u8], n: i64| -> Option<std::io::SeekFrom> {
                match whence {
                    b"bof" => u64::try_from(n).ok().map(std::io::SeekFrom::Start),
                    b"cur" => Some(std::io::SeekFrom::Current(n)),
                    b"eof" => Some(std::io::SeekFrom::End(n)),
                    _ => None,
                }
            };
            let loc = if b & TAG_MASK == TAG_SMALL {
                seek(b"bof", b as i64 >> 3)
            } else if b & TAG_MASK == TAG_ATOM {
                seek(atom_bytes(b), 0)
            } else if b & TAG_MASK == TAG_BOXED && b != 0 {
                unsafe {
                    let p = b as *const u64;
                    if *p == (2 << 8) | KIND_TUPLE
                        && *p.add(1) & TAG_MASK == TAG_ATOM
                        && *p.add(2) & TAG_MASK == TAG_SMALL
                    {
                        seek(atom_bytes(*p.add(1)), *p.add(2) as i64 >> 3)
                    } else {
                        None
                    }
                }
            } else {
                None
            };
            let Some(loc) = loc else { return raise_badarg(ctx) };
            let mut tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            let res = entry.file.seek(loc);
            drop(tab);
            match res {
                Ok(pos) => pair_term(ctx, b"ok", ((pos as i64) << 3) as u64 | TAG_SMALL),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_DELETE => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::remove_file(&path) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_RENAME => {
            let (Ok(from), Ok(to)) = (path_of(a), path_of(b)) else {
                return raise_badarg(ctx);
            };
            match std::fs::rename(&from, &to) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_MAKE_DIR => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::create_dir(&path) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_DEL_DIR => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::remove_dir(&path) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_LIST_DIR => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            let rd = match std::fs::read_dir(&path) {
                Ok(rd) => rd,
                Err(e) => return err_tuple(ctx, &e),
            };
            let mut names: Vec<Vec<u8>> = Vec::new();
            for ent in rd {
                match ent {
                    Ok(ent) => names.push(ent.file_name().as_encoded_bytes().to_vec()),
                    Err(e) => return err_tuple(ctx, &e),
                }
            }
            // Each name becomes a charlist. The loop builds the list back to front
            // and roots the accumulator.
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for name in names.iter().rev() {
                fr[3] = utf8_to_codepoint_list(ctx, name);
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            let list = fr[2];
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", list)
        }
        F_FILE_INFO | F_FILE_INFO2 => {
            use std::os::unix::fs::MetadataExt;
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            // {time, posix} is the only option that the code honors. The universal
            // and local options return UTC calendar tuples. Local as UTC is a
            // documented divergence.
            let mut posix_time = false;
            if op == F_FILE_INFO2 {
                let mut cur = b;
                while cur & TAG_MASK == TAG_CONS {
                    let p = (cur & !TAG_MASK) as *const u64;
                    let o = unsafe { *p };
                    if o & TAG_MASK == TAG_BOXED && o != 0 {
                        unsafe {
                            let t = o as *const u64;
                            if *t == (2 << 8) | KIND_TUPLE
                                && *t.add(1) & TAG_MASK == TAG_ATOM
                                && atom_bytes(*t.add(1)) == b"time"
                                && *t.add(2) & TAG_MASK == TAG_ATOM
                                && atom_bytes(*t.add(2)) == b"posix"
                            {
                                posix_time = true;
                            }
                        }
                    }
                    cur = unsafe { *p.add(1) };
                }
            }
            let md = match std::fs::metadata(&path) {
                Ok(md) => md,
                Err(e) => return err_tuple(ctx, &e),
            };
            let ftype: &[u8] = if md.is_dir() {
                b"directory"
            } else if md.is_file() {
                b"regular"
            } else if md.file_type().is_symlink() {
                b"symlink"
            } else {
                b"other"
            };
            let access: &[u8] = if md.permissions().readonly() {
                b"read"
            } else {
                b"read_write"
            };
            let small = |v: i64| ((v << 3) as u64) | TAG_SMALL;
            let mut time_term = |ctx: &mut ProcCtx, secs: i64| -> u64 {
                if posix_time {
                    small(secs)
                } else {
                    civil_datetime(ctx, secs)
                }
            };
            // Root the three time terms across the record allocation.
            let saved = ctx.roots_head;
            let mut fr = [0u64, 3, NIL, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            fr[2] = time_term(ctx, md.atime());
            fr[3] = time_term(ctx, md.mtime());
            fr[4] = time_term(ctx, md.ctime());
            let p = alloc_nursery(ctx, 15);
            unsafe {
                *p = (14 << 8) | KIND_TUPLE;
                *p.add(1) = atom_intern(b"file_info");
                *p.add(2) = small(md.size() as i64);
                *p.add(3) = atom_intern(ftype);
                *p.add(4) = atom_intern(access);
                *p.add(5) = fr[2];
                *p.add(6) = fr[3];
                *p.add(7) = fr[4];
                *p.add(8) = small((md.mode() & 0o7777) as i64);
                *p.add(9) = small(md.nlink() as i64);
                *p.add(10) = small(0); // major_device
                *p.add(11) = small(0); // minor_device
                *p.add(12) = small(md.ino() as i64 & (i64::MAX >> 3));
                *p.add(13) = small(md.uid() as i64);
                *p.add(14) = small(md.gid() as i64);
            }
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", p as u64)
        }
        F_GET_CWD => match std::env::current_dir() {
            Ok(p) => {
                let bytes = p.as_os_str().as_encoded_bytes().to_vec();
                let l = bytes_to_byte_list(ctx, &bytes);
                pair_term(ctx, b"ok", l)
            }
            Err(e) => err_tuple(ctx, &e),
        },
        F_COPY => {
            let (Ok(from), Ok(to)) = (path_of(a), path_of(b)) else {
                return raise_badarg(ctx);
            };
            match std::fs::copy(&from, &to) {
                Ok(n) => pair_term(ctx, b"ok", ((n as i64) << 3) as u64 | TAG_SMALL),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        _ => raise_badarg(ctx),
    }
}

impl FileTable {
    pub(crate) fn insert(&mut self, e: FileEntry) -> usize {
        match self.free.pop() {
            Some(i) => {
                self.slots[i] = Some(e);
                i
            }
            None => {
                self.slots.push(Some(e));
                self.slots.len() - 1
            }
        }
    }
}
