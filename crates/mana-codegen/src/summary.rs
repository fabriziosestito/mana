//! Per-module analysis summaries. A summary holds everything that
//! `reachable_funs`, the effect fixpoints, and `action_key` consume, WITHOUT
//! the AST. The same collectors and condensers that the analysis runs on a
//! parsed module produce the summary. So a summary can never diverge from
//! the result of a parse.
//!
//! The disk cache keys summaries by (format, tool_hash, source_hash). Any
//! source or compiler change moves the key. So a stale summary is impossible
//! by construction.
//!
//! The serialization is a hand-rolled length-prefixed format (no dependency,
//! fully deterministic). Any decode irregularity counts as a miss.

use crate::{
    collect_atom_arg_pairs, collect_atoms, collect_dyn_names, collect_edges, cond_may_gc,
    cond_may_raise, Edge,
};
use mana_syntax::{FunName, Module};
use std::collections::{BTreeSet, HashSet};
use std::path::PathBuf;

/// If the summary contents or the encoding change, bump this value. It is
/// part of the key.
pub const SUMMARY_FORMAT: u32 = 2;

const MAGIC: u32 = 0x4d41_4e53; // "MANS"

pub struct ModuleSummary {
    pub name: String,
    pub exports: Vec<FunName>,
    pub funs: Vec<FunSummary>,
}

pub struct FunSummary {
    pub name: FunName,
    // reachable_funs inputs
    pub atoms: Vec<String>,               // collect_atoms (sorted)
    pub arg_pairs: Vec<(String, String)>, // collect_atom_arg_pairs (in order)
    pub dyn_pairs: Vec<(String, usize)>,  // collect_dyn_names pairs (sorted)
    pub dyn_any_names: Vec<String>,       // MFA-tuple names, any arity (sorted)
    pub fun_dyn: bool,
    pub tuple_heads: Vec<String>, // collect_dyn_names heads (sorted)
    pub edges: Vec<Edge>,         // collect_edges (in order)
    // effect condensations (cond_may_gc, cond_may_raise)
    pub gc_base: bool,
    pub gc_deps: Vec<(String, FunName)>,
    pub raise_base: bool,
    pub raise_deps: Vec<(String, FunName)>,
}

/// Condense a parsed module. This runs the exact walkers of the analysis,
/// once per function instead of once per fixpoint iteration.
pub fn summarize(m: &Module) -> ModuleSummary {
    let funs = m
        .definitions
        .iter()
        .map(|(fname, fun)| {
            let mut atoms = BTreeSet::new();
            collect_atoms(&fun.body, &mut atoms);
            let mut arg_pairs = Vec::new();
            collect_atom_arg_pairs(&fun.body, &mut arg_pairs);
            let mut pairs: HashSet<(String, usize)> = HashSet::new();
            let mut fun_dyn = false;
            let mut heads: HashSet<String> = HashSet::new();
            let mut any_names: HashSet<String> = HashSet::new();
            collect_dyn_names(
                &fun.body,
                &mut pairs,
                &mut fun_dyn,
                &mut heads,
                &mut any_names,
            );
            let mut edges = Vec::new();
            let mut letrec = HashSet::new();
            collect_edges(&fun.body, &mut edges, &mut letrec);
            let mut gc_base = false;
            let mut gc_deps = BTreeSet::new();
            let mut letrec = HashSet::new();
            cond_may_gc(&fun.body, &m.name, &mut letrec, &mut gc_base, &mut gc_deps);
            let mut raise_base = false;
            let mut raise_deps = BTreeSet::new();
            let mut letrec = HashSet::new();
            cond_may_raise(
                &fun.body,
                &m.name,
                &mut letrec,
                &mut raise_base,
                &mut raise_deps,
            );
            let mut dyn_pairs: Vec<(String, usize)> = pairs.into_iter().collect();
            dyn_pairs.sort();
            let mut dyn_any_names: Vec<String> = any_names.into_iter().collect();
            dyn_any_names.sort();
            let mut tuple_heads: Vec<String> = heads.into_iter().collect();
            tuple_heads.sort();
            FunSummary {
                name: fname.clone(),
                atoms: atoms.into_iter().collect(),
                arg_pairs,
                dyn_pairs,
                dyn_any_names,
                fun_dyn,
                tuple_heads,
                edges,
                gc_base,
                gc_deps: gc_deps.into_iter().collect(),
                raise_base,
                raise_deps: raise_deps.into_iter().collect(),
            }
        })
        .collect();
    ModuleSummary {
        name: m.name.clone(),
        exports: m.exports.clone(),
        funs,
    }
}

// Disk cache

impl crate::ObjCache {
    fn summary_path(&self, source_hash: &[u8; 32]) -> PathBuf {
        let mut h = blake3::Hasher::new();
        h.update(b"mana-summary-v1\0");
        h.update(&SUMMARY_FORMAT.to_le_bytes());
        h.update(&self.tool_hash);
        h.update(source_hash);
        let hex = h.finalize().to_hex();
        self.root
            .join("summary")
            .join(&hex.as_str()[..2])
            .join(format!("{}.sum", hex))
    }

    pub fn get_summary(&self, source_hash: &[u8; 32]) -> Option<ModuleSummary> {
        let bytes = std::fs::read(self.summary_path(source_hash)).ok()?;
        decode(&bytes)
    }

    /// Idempotent publish, like the object cache: write a tmp file, then an
    /// atomic rename.
    pub fn put_summary(&self, source_hash: &[u8; 32], s: &ModuleSummary) {
        let dst = self.summary_path(source_hash);
        let Some(parent) = dst.parent() else { return };
        if std::fs::create_dir_all(parent).is_err() {
            return;
        }
        let tmp = dst.with_extension(format!("sum.tmp-{}", std::process::id()));
        if std::fs::write(&tmp, encode(s)).is_ok() {
            let _ = std::fs::rename(&tmp, &dst);
        }
    }

    /// Age-trim the summary bucket with the policy of the object cache.
    pub(crate) fn trim_summaries(&self, cutoff: std::time::SystemTime) {
        if let Ok(buckets) = std::fs::read_dir(self.root.join("summary")) {
            for bucket in buckets.flatten() {
                if !bucket.path().is_dir() {
                    continue;
                }
                if let Ok(entries) = std::fs::read_dir(bucket.path()) {
                    for e in entries.flatten() {
                        if let Ok(meta) = e.metadata() {
                            if meta.modified().map(|m| m < cutoff).unwrap_or(false) {
                                let _ = std::fs::remove_file(e.path());
                            }
                        }
                    }
                }
            }
        }
    }
}

// Encoding

fn encode(s: &ModuleSummary) -> Vec<u8> {
    let mut b = Vec::with_capacity(4096);
    w32(&mut b, MAGIC);
    w32(&mut b, SUMMARY_FORMAT);
    wstr(&mut b, &s.name);
    w32(&mut b, s.exports.len() as u32);
    for f in &s.exports {
        wfun(&mut b, f);
    }
    w32(&mut b, s.funs.len() as u32);
    for f in &s.funs {
        wfun(&mut b, &f.name);
        wvec_str(&mut b, &f.atoms);
        w32(&mut b, f.arg_pairs.len() as u32);
        for (a, c) in &f.arg_pairs {
            wstr(&mut b, a);
            wstr(&mut b, c);
        }
        w32(&mut b, f.dyn_pairs.len() as u32);
        for (n, a) in &f.dyn_pairs {
            wstr(&mut b, n);
            w32(&mut b, *a as u32);
        }
        wvec_str(&mut b, &f.dyn_any_names);
        b.push(f.fun_dyn as u8);
        wvec_str(&mut b, &f.tuple_heads);
        w32(&mut b, f.edges.len() as u32);
        for e in &f.edges {
            match e {
                Edge::Local(f) => {
                    b.push(0);
                    wfun(&mut b, f);
                }
                Edge::Remote(m, f) => {
                    b.push(1);
                    wstr(&mut b, m);
                    wfun(&mut b, f);
                }
                Edge::RemoteAnyArity(m, f) => {
                    b.push(2);
                    wstr(&mut b, m);
                    wstr(&mut b, f);
                }
            }
        }
        b.push(f.gc_base as u8);
        wdeps(&mut b, &f.gc_deps);
        b.push(f.raise_base as u8);
        wdeps(&mut b, &f.raise_deps);
    }
    b
}

fn decode(b: &[u8]) -> Option<ModuleSummary> {
    let mut p = 0usize;
    if r32(b, &mut p)? != MAGIC || r32(b, &mut p)? != SUMMARY_FORMAT {
        return None;
    }
    let name = rstr(b, &mut p)?;
    let n = r32(b, &mut p)? as usize;
    let mut exports = Vec::with_capacity(n);
    for _ in 0..n {
        exports.push(rfun(b, &mut p)?);
    }
    let n = r32(b, &mut p)? as usize;
    let mut funs = Vec::with_capacity(n);
    for _ in 0..n {
        let fname = rfun(b, &mut p)?;
        let atoms = rvec_str(b, &mut p)?;
        let n = r32(b, &mut p)? as usize;
        let mut arg_pairs = Vec::with_capacity(n);
        for _ in 0..n {
            arg_pairs.push((rstr(b, &mut p)?, rstr(b, &mut p)?));
        }
        let n = r32(b, &mut p)? as usize;
        let mut dyn_pairs = Vec::with_capacity(n);
        for _ in 0..n {
            dyn_pairs.push((rstr(b, &mut p)?, r32(b, &mut p)? as usize));
        }
        let dyn_any_names = rvec_str(b, &mut p)?;
        let fun_dyn = rbool(b, &mut p)?;
        let tuple_heads = rvec_str(b, &mut p)?;
        let n = r32(b, &mut p)? as usize;
        let mut edges = Vec::with_capacity(n);
        for _ in 0..n {
            let tag = rbyte(b, &mut p)?;
            edges.push(match tag {
                0 => Edge::Local(rfun(b, &mut p)?),
                1 => Edge::Remote(rstr(b, &mut p)?, rfun(b, &mut p)?),
                2 => Edge::RemoteAnyArity(rstr(b, &mut p)?, rstr(b, &mut p)?),
                _ => return None,
            });
        }
        let gc_base = rbool(b, &mut p)?;
        let gc_deps = rdeps(b, &mut p)?;
        let raise_base = rbool(b, &mut p)?;
        let raise_deps = rdeps(b, &mut p)?;
        funs.push(FunSummary {
            name: fname,
            atoms,
            arg_pairs,
            dyn_pairs,
            dyn_any_names,
            fun_dyn,
            tuple_heads,
            edges,
            gc_base,
            gc_deps,
            raise_base,
            raise_deps,
        });
    }
    if p != b.len() {
        return None;
    }
    Some(ModuleSummary {
        name,
        exports,
        funs,
    })
}

fn w32(b: &mut Vec<u8>, v: u32) {
    b.extend_from_slice(&v.to_le_bytes());
}

fn wstr(b: &mut Vec<u8>, s: &str) {
    w32(b, s.len() as u32);
    b.extend_from_slice(s.as_bytes());
}

fn wfun(b: &mut Vec<u8>, f: &FunName) {
    wstr(b, &f.name);
    w32(b, f.arity as u32);
}

fn wvec_str(b: &mut Vec<u8>, v: &[String]) {
    w32(b, v.len() as u32);
    for s in v {
        wstr(b, s);
    }
}

fn wdeps(b: &mut Vec<u8>, v: &[(String, FunName)]) {
    w32(b, v.len() as u32);
    for (m, f) in v {
        wstr(b, m);
        wfun(b, f);
    }
}

fn rbyte(b: &[u8], p: &mut usize) -> Option<u8> {
    let v = *b.get(*p)?;
    *p += 1;
    Some(v)
}

fn rbool(b: &[u8], p: &mut usize) -> Option<bool> {
    match rbyte(b, p)? {
        0 => Some(false),
        1 => Some(true),
        _ => None,
    }
}

fn r32(b: &[u8], p: &mut usize) -> Option<u32> {
    let s = b.get(*p..*p + 4)?;
    *p += 4;
    Some(u32::from_le_bytes(s.try_into().ok()?))
}

fn rstr(b: &[u8], p: &mut usize) -> Option<String> {
    let n = r32(b, p)? as usize;
    let s = b.get(*p..*p + n)?;
    *p += n;
    String::from_utf8(s.to_vec()).ok()
}

fn rfun(b: &[u8], p: &mut usize) -> Option<FunName> {
    Some(FunName {
        name: rstr(b, p)?,
        arity: r32(b, p)? as usize,
    })
}

fn rvec_str(b: &[u8], p: &mut usize) -> Option<Vec<String>> {
    let n = r32(b, p)? as usize;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rstr(b, p)?);
    }
    Some(v)
}

fn rdeps(b: &[u8], p: &mut usize) -> Option<Vec<(String, FunName)>> {
    let n = r32(b, p)? as usize;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push((rstr(b, p)?, rfun(b, p)?));
    }
    Some(v)
}
