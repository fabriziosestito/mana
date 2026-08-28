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
    /// > i64: decimal digits; valid only as a bitstring segment constant
    Big(String),
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
    /// A function used as a value: bare `'f'/1` (local) or `fun 'm':'f'/1`.
    FunRef {
        module: Option<String>,
        fun: FunName,
    },
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
    /// `call M:F(args)` where the module and/or function position is a
    /// computed expression (erlc emits these for dynamic `m.f(...)` calls);
    /// compiles as erlang:apply/3.
    CallDyn {
        module: Box<Expr>,
        name: Box<Expr>,
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
    /// `~{ k => v, ... }~` or `~{ k := v | M }~` map construction/update.
    /// `=>` inserts-or-replaces; `:=` requires the key to exist (badkey).
    /// erlc rewrites `maps:put/3` calls into `=>` updates, so the
    /// distinction is load-bearing, not a syntax nicety.
    Map {
        pairs: Vec<(Expr, MapAssoc, Expr)>,
        update: Option<Box<Expr>>,
    },
    /// `try Arg of <vars> -> Body catch <evars> -> Handler`
    Try {
        arg: Box<Expr>,
        vars: Vec<String>,
        body: Box<Expr>,
        evars: Vec<String>,
        handler: Box<Expr>,
    },
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapAssoc {
    /// `=>` — insert or replace
    Assoc,
    /// `:=` — exact: key must already exist
    Exact,
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
    /// `~{ k := p, ... }~` map pattern (keys are expressions)
    Map(Vec<(Expr, Pattern)>),
}
