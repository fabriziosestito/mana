//! AST for the Core Erlang subset emitted by `erlc +to_core`.
//! Annotations (`-| [...]`) are parsed and discarded.

#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub name: String,
    pub exports: Vec<FunName>,
    pub definitions: Vec<(FunName, Fun)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunName {
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Fun {
    pub params: Vec<String>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Atom(String),
    Nil,
}

/// One segment of a bitstring: `#<value>(size, unit, type, flags)`.
/// The spec args (size/unit/type/flags) are kept as raw expressions; only
/// the syntax is supported for now — codegen rejects binaries.
#[derive(Debug, Clone, PartialEq)]
pub struct BinSegment<V> {
    pub value: V,
    pub spec: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(String),
    Lit(Literal),
    Tuple(Vec<Expr>),
    Cons(Box<Expr>, Box<Expr>),
    /// `<e1, ..., en>` multi-value expression (only valid in certain positions)
    Values(Vec<Expr>),
    Fun(Box<Fun>),
    /// `let <v1, ..., vn> = arg in body`
    Let {
        vars: Vec<String>,
        arg: Box<Expr>,
        body: Box<Expr>,
    },
    LetRec {
        defs: Vec<(FunName, Fun)>,
        body: Box<Expr>,
    },
    /// `apply f (args)` — f is a local fname or a variable holding a fun
    Apply {
        target: ApplyTarget,
        args: Vec<Expr>,
    },
    /// `call m:f (args)` — m, f restricted to atom literals for now
    Call {
        module: String,
        name: String,
        args: Vec<Expr>,
    },
    PrimOp {
        name: String,
        args: Vec<Expr>,
    },
    Case {
        arg: Box<Expr>,
        clauses: Vec<Clause>,
    },
    /// `#{ seg, ... }#` bitstring construction
    Binary(Vec<BinSegment<Box<Expr>>>),
    /// `do e1 e2` — sequence
    Do(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ApplyTarget {
    LocalFun(FunName),
    Var(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause {
    pub patterns: Vec<Pattern>,
    pub guard: Expr,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Var(String),
    Lit(Literal),
    Tuple(Vec<Pattern>),
    Cons(Box<Pattern>, Box<Pattern>),
    /// `V = pat` alias
    Alias(String, Box<Pattern>),
    /// `#{ seg, ... }#` bitstring pattern
    Binary(Vec<BinSegment<Box<Pattern>>>),
}
