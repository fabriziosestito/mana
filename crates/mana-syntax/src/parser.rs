//! Recursive-descent parser for the Core Erlang subset that `erlc +to_core` emits.

use crate::ast::*;
use crate::lexer::{tokenize, Tok};

pub struct Parser {
    toks: Vec<(Tok, usize)>,
    pos: usize,
}

type PResult<T> = Result<T, String>;

pub fn parse_module(src: &str) -> PResult<Module> {
    let toks = tokenize(src)?;
    let mut p = Parser { toks, pos: 0 };
    p.parse_module()
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos.min(self.toks.len() - 1)].0
    }

    /// Lookahead: true if the next `( ... )` wraps a whole map pair, that is,
    /// if it holds a top-level `:=` or `=>` before it closes. This separates
    /// `( k := v -| ann )` from an annotation-wrapped key `( k -| ann ) := v`.
    fn pair_wrap_ahead(&self) -> bool {
        if *self.peek() != Tok::LParen {
            return false;
        }
        let mut depth = 0usize;
        for (t, _) in &self.toks[self.pos..] {
            match t {
                Tok::LParen | Tok::LBrace | Tok::LBracket | Tok::MapOpen | Tok::BinOpen => {
                    depth += 1
                }
                Tok::RParen | Tok::RBrace | Tok::RBracket | Tok::MapClose | Tok::BinClose => {
                    if depth <= 1 {
                        return false; // The wrapper closed without a pair assoc.
                    }
                    depth -= 1;
                }
                Tok::Assoc | Tok::ExactAssoc if depth == 1 => return true,
                Tok::Eof => return false,
                _ => {}
            }
        }
        false
    }

    fn line(&self) -> usize {
        self.toks[self.pos.min(self.toks.len() - 1)].1
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos.min(self.toks.len() - 1)].0.clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn expect(&mut self, t: Tok) -> PResult<()> {
        let got = self.bump();
        if got == t {
            Ok(())
        } else {
            Err(format!(
                "line {}: expected {}, found {}",
                self.line(),
                t,
                got
            ))
        }
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }

    fn err<T>(&self, msg: &str) -> PResult<T> {
        Err(format!("line {}: {}", self.line(), msg))
    }

    // Module

    fn parse_module(&mut self) -> PResult<Module> {
        self.expect(Tok::Module)?;
        let name = self.parse_atom()?;
        self.expect(Tok::LBracket)?;
        let mut exports = Vec::new();
        if !self.eat(&Tok::RBracket) {
            loop {
                exports.push(self.parse_fname()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::RBracket)?;
        }
        self.expect(Tok::Attributes)?;
        self.expect(Tok::LBracket)?;
        let mut behaviours: Vec<String> = Vec::new();
        if !self.eat(&Tok::RBracket) {
            loop {
                // Each attribute is 'key' = const. The parser keeps only the
                // behaviour keys and discards the rest.
                let key = self.parse_atom()?;
                self.expect(Tok::Eq)?;
                let value = self.parse_expr()?;
                if key == "behaviour" || key == "behavior" {
                    fn atoms(e: &Expr, out: &mut Vec<String>) {
                        match e {
                            Expr::Lit(Literal::Atom(a)) => out.push(a.clone()),
                            Expr::Cons(h, t) => {
                                atoms(h, out);
                                atoms(t, out);
                            }
                            _ => {}
                        }
                    }
                    atoms(&value, &mut behaviours);
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::RBracket)?;
        }
        let mut definitions = Vec::new();
        while *self.peek() != Tok::End {
            definitions.push(self.parse_def()?);
        }
        self.expect(Tok::End)?;
        Ok(Module {
            name,
            exports,
            behaviours,
            definitions,
        })
    }

    fn parse_def(&mut self) -> PResult<(FunName, Fun)> {
        let fname = self.parse_fname()?;
        self.expect(Tok::Eq)?;
        let expr = self.parse_expr()?;
        match expr {
            Expr::Fun(f) => Ok((fname, *f)),
            _ => self.err("expected fun on right-hand side of definition"),
        }
    }

    fn parse_atom(&mut self) -> PResult<String> {
        match self.bump() {
            Tok::Atom(s) => Ok(s),
            other => Err(format!("line {}: expected atom, found {}", self.line(), other)),
        }
    }

    fn parse_fname(&mut self) -> PResult<FunName> {
        // An fname can have an annotation wrapper: ( 'f'/1 -| [...] )
        if self.eat(&Tok::LParen) {
            let f = self.parse_fname()?;
            self.skip_annotation()?;
            self.expect(Tok::RParen)?;
            return Ok(f);
        }
        let name = self.parse_atom()?;
        self.expect(Tok::Slash)?;
        match self.bump() {
            Tok::Int(n) if n >= 0 => Ok(FunName {
                name,
                arity: n as usize,
            }),
            other => Err(format!(
                "line {}: expected arity, found {}",
                self.line(),
                other
            )),
        }
    }

    /// If a `-| [...]` annotation is present, consumes it. The content is
    /// arbitrary constant terms. The parser reads them structurally and
    /// discards them.
    fn skip_annotation(&mut self) -> PResult<()> {
        if self.eat(&Tok::AnnoBar) {
            self.parse_expr()?;
        }
        Ok(())
    }

    // Expressions

    fn parse_expr(&mut self) -> PResult<Expr> {
        match self.peek().clone() {
            Tok::LParen => {
                self.bump();
                if self.is_fname_ahead() {
                    // An annotated fname used as a value: ( 'f'/1 -| [...] )
                    let f = self.parse_fname_no_paren()?;
                    self.skip_annotation()?;
                    self.expect(Tok::RParen)?;
                    return Ok(Expr::FunRef {
                        module: None,
                        fun: f,
                    });
                }
                let e = self.parse_expr()?;
                self.skip_annotation()?;
                self.expect(Tok::RParen)?;
                Ok(e)
            }
            Tok::Int(n) => {
                self.bump();
                Ok(Expr::Lit(Literal::Int(n)))
            }
            Tok::BigInt(d) => {
                self.bump();
                Ok(Expr::Lit(Literal::Big(d)))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(Expr::Lit(Literal::Float(f)))
            }
            Tok::Char(c) => {
                self.bump();
                Ok(Expr::Lit(Literal::Int(c)))
            }
            Tok::Atom(_) => {
                if self.is_fname_ahead() {
                    // A bare fname used as a value: let <F> = 'tr'/1 in ...
                    let f = self.parse_fname_no_paren()?;
                    return Ok(Expr::FunRef {
                        module: None,
                        fun: f,
                    });
                }
                let a = self.parse_atom()?;
                Ok(Expr::Lit(Literal::Atom(a)))
            }
            Tok::Str(s) => {
                self.bump();
                // A string literal is sugar for a char list.
                let mut e = Expr::Lit(Literal::Nil);
                for c in s.chars().rev() {
                    e = Expr::Cons(
                        Box::new(Expr::Lit(Literal::Int(c as i64))),
                        Box::new(e),
                    );
                }
                Ok(e)
            }
            Tok::Var(v) => {
                self.bump();
                Ok(Expr::Var(v))
            }
            Tok::LBrace => {
                self.bump();
                let items = self.parse_comma_exprs(Tok::RBrace)?;
                Ok(Expr::Tuple(items))
            }
            Tok::LBracket => self.parse_list(),
            Tok::BinOpen => {
                let segs = self.parse_binary(|p| Ok(Box::new(p.parse_expr()?)))?;
                Ok(Expr::Binary(segs))
            }
            Tok::MapOpen => {
                self.bump();
                let mut pairs = Vec::new();
                let mut update = None;
                if !self.eat(&Tok::MapClose) {
                    loop {
                        // A pair can have an annotation wrapper: `( k := v -| [...] )`
                        let wrapped = self.pair_wrap_ahead();
                        if wrapped {
                            self.expect(Tok::LParen)?;
                        }
                        let key = self.parse_expr()?;
                        let assoc = if self.eat(&Tok::Assoc) {
                            MapAssoc::Assoc
                        } else {
                            self.expect(Tok::ExactAssoc)?;
                            MapAssoc::Exact
                        };
                        let val = self.parse_expr()?;
                        if wrapped {
                            self.skip_annotation()?;
                            self.expect(Tok::RParen)?;
                        }
                        pairs.push((key, assoc, val));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    if self.eat(&Tok::Bar) {
                        update = Some(Box::new(self.parse_expr()?));
                    }
                    self.expect(Tok::MapClose)?;
                }
                Ok(Expr::Map { pairs, update })
            }
            Tok::Lt => {
                self.bump();
                let items = self.parse_comma_exprs(Tok::Gt)?;
                Ok(Expr::Values(items))
            }
            Tok::Fun => {
                self.bump();
                // `fun 'm':'f'/a` or `fun 'f'/a` is a fun reference.
                if matches!(self.peek(), Tok::Atom(_)) {
                    let first = self.parse_atom()?;
                    if self.eat(&Tok::Colon) {
                        let name = self.parse_atom()?;
                        self.expect(Tok::Slash)?;
                        let arity = self.parse_arity()?;
                        return Ok(Expr::FunRef {
                            module: Some(first),
                            fun: FunName { name, arity },
                        });
                    }
                    self.expect(Tok::Slash)?;
                    let arity = self.parse_arity()?;
                    return Ok(Expr::FunRef {
                        module: None,
                        fun: FunName { name: first, arity },
                    });
                }
                self.expect(Tok::LParen)?;
                let mut params = Vec::new();
                if !self.eat(&Tok::RParen) {
                    loop {
                        // A parameter can have an annotation wrapper:
                        // `fun (( _0 -| ['compiler_generated'] )) -> ...`
                        let wrapped = self.eat(&Tok::LParen);
                        let v = match self.bump() {
                            Tok::Var(v) => v,
                            other => {
                                return Err(format!(
                                    "line {}: expected parameter, found {}",
                                    self.line(),
                                    other
                                ))
                            }
                        };
                        if wrapped {
                            self.skip_annotation()?;
                            self.expect(Tok::RParen)?;
                        }
                        params.push(v);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(Tok::RParen)?;
                }
                self.expect(Tok::Arrow)?;
                let body = self.parse_expr()?;
                Ok(Expr::Fun(Box::new(Fun { params, body })))
            }
            Tok::Let => {
                self.bump();
                let vars = self.parse_var_list()?;
                self.expect(Tok::Eq)?;
                let arg = self.parse_expr()?;
                self.expect(Tok::In)?;
                let body = self.parse_expr()?;
                Ok(Expr::Let {
                    vars,
                    arg: Box::new(arg),
                    body: Box::new(body),
                })
            }
            Tok::Letrec => {
                self.bump();
                let mut defs = Vec::new();
                while *self.peek() != Tok::In {
                    defs.push(self.parse_def()?);
                }
                self.expect(Tok::In)?;
                let body = self.parse_expr()?;
                Ok(Expr::LetRec {
                    defs,
                    body: Box::new(body),
                })
            }
            Tok::Apply => {
                self.bump();
                let target = self.parse_apply_target()?;
                let args = self.parse_call_args()?;
                Ok(Expr::Apply { target, args })
            }
            Tok::Call => {
                self.bump();
                let module = self.parse_call_pos()?;
                self.expect(Tok::Colon)?;
                let name = self.parse_call_pos()?;
                let args = self.parse_call_args()?;
                match (module, name) {
                    (Expr::Lit(Literal::Atom(module)), Expr::Lit(Literal::Atom(name))) => {
                        Ok(Expr::Call { module, name, args })
                    }
                    (module, name) => Ok(Expr::CallDyn {
                        module: Box::new(module),
                        name: Box::new(name),
                        args,
                    }),
                }
            }
            Tok::Catch => {
                // Old-style `catch E`. On success, the result is the value.
                // For throw, the result is the thrown value. For exit, it is
                // {'EXIT', Reason}. For error, it is {'EXIT', {Reason, []}}.
                // TODO(stacktraces): the handler omits the stacktrace. erlc
                // usually lowers catch to try itself. unicode.erl keeps it.
                self.bump();
                let arg = self.parse_expr()?;
                let exit_a = || Expr::Lit(Literal::Atom("EXIT".into()));
                let handler = Expr::Case {
                    arg: Box::new(Expr::Var("_CatchClass".into())),
                    clauses: vec![
                        Clause {
                            patterns: vec![Pattern::Lit(Literal::Atom("throw".into()))],
                            guard: Expr::Lit(Literal::Atom("true".into())),
                            body: Expr::Var("_CatchReason".into()),
                        },
                        Clause {
                            patterns: vec![Pattern::Lit(Literal::Atom("exit".into()))],
                            guard: Expr::Lit(Literal::Atom("true".into())),
                            body: Expr::Tuple(vec![
                                exit_a(),
                                Expr::Var("_CatchReason".into()),
                            ]),
                        },
                        Clause {
                            patterns: vec![Pattern::Var("_CatchOther".into())],
                            guard: Expr::Lit(Literal::Atom("true".into())),
                            body: Expr::Tuple(vec![
                                exit_a(),
                                Expr::Tuple(vec![
                                    Expr::Var("_CatchReason".into()),
                                    Expr::Lit(Literal::Nil),
                                ]),
                            ]),
                        },
                    ],
                };
                Ok(Expr::Try {
                    arg: Box::new(arg),
                    vars: vec!["_CatchVal".into()],
                    body: Box::new(Expr::Var("_CatchVal".into())),
                    evars: vec![
                        "_CatchClass".into(),
                        "_CatchReason".into(),
                        "_CatchStk".into(),
                    ],
                    handler: Box::new(handler),
                })
            }
            Tok::Primop => {
                self.bump();
                let name = self.parse_atom_expr()?;
                let args = self.parse_call_args()?;
                Ok(Expr::PrimOp { name, args })
            }
            Tok::Case => {
                self.bump();
                let arg = self.parse_expr()?;
                self.expect(Tok::Of)?;
                let mut clauses = Vec::new();
                while *self.peek() != Tok::End {
                    clauses.push(self.parse_clause()?);
                }
                self.expect(Tok::End)?;
                Ok(Expr::Case {
                    arg: Box::new(arg),
                    clauses,
                })
            }
            Tok::Try => {
                self.bump();
                let arg = self.parse_expr()?;
                self.expect(Tok::Of)?;
                let vars = self.parse_var_list()?;
                self.expect(Tok::Arrow)?;
                let body = self.parse_expr()?;
                self.expect(Tok::Catch)?;
                let evars = self.parse_var_list()?;
                self.expect(Tok::Arrow)?;
                let handler = self.parse_expr()?;
                Ok(Expr::Try {
                    arg: Box::new(arg),
                    vars,
                    body: Box::new(body),
                    evars,
                    handler: Box::new(handler),
                })
            }
            Tok::Do => {
                self.bump();
                let first = self.parse_expr()?;
                let then = self.parse_expr()?;
                Ok(Expr::Do(Box::new(first), Box::new(then)))
            }
            other => Err(format!(
                "line {}: unsupported or unexpected token in expression: {}",
                self.line(),
                other
            )),
        }
    }

    /// True if the next tokens are `'atom' / int` (an fname). This check
    /// disambiguates inside parentheses.
    fn is_fname_ahead(&self) -> bool {
        matches!(self.toks.get(self.pos).map(|t| &t.0), Some(Tok::Atom(_)))
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.0), Some(Tok::Slash))
    }

    fn parse_fname_no_paren(&mut self) -> PResult<FunName> {
        let name = self.parse_atom()?;
        self.expect(Tok::Slash)?;
        let arity = self.parse_arity()?;
        Ok(FunName { name, arity })
    }

    fn parse_arity(&mut self) -> PResult<usize> {
        match self.bump() {
            Tok::Int(n) if n >= 0 => Ok(n as usize),
            other => Err(format!(
                "line {}: expected arity, found {}",
                self.line(),
                other
            )),
        }
    }

    fn parse_apply_target(&mut self) -> PResult<ApplyTarget> {
        if self.eat(&Tok::LParen) {
            let t = self.parse_apply_target()?;
            self.skip_annotation()?;
            self.expect(Tok::RParen)?;
            return Ok(t);
        }
        if self.is_fname_ahead() {
            return Ok(ApplyTarget::LocalFun(self.parse_fname_no_paren()?));
        }
        match self.bump() {
            Tok::Var(v) => Ok(ApplyTarget::Var(v)),
            other => Err(format!(
                "line {}: expected apply target, found {}",
                self.line(),
                other
            )),
        }
    }

    /// The module or function position of `call`. Usually it is an atom, but
    /// erlc emits arbitrary expressions for dynamic dispatch. The parser
    /// strips annotations.
    fn parse_call_pos(&mut self) -> PResult<Expr> {
        let e = self.parse_expr()?;
        Ok(e)
    }

    /// An atom with optional annotation and parentheses.
    fn parse_atom_expr(&mut self) -> PResult<String> {
        if self.eat(&Tok::LParen) {
            let a = self.parse_atom_expr()?;
            self.skip_annotation()?;
            self.expect(Tok::RParen)?;
            return Ok(a);
        }
        self.parse_atom()
    }

    fn parse_call_args(&mut self) -> PResult<Vec<Expr>> {
        self.expect(Tok::LParen)?;
        self.parse_comma_exprs(Tok::RParen)
    }

    fn parse_comma_exprs(&mut self, close: Tok) -> PResult<Vec<Expr>> {
        let mut items = Vec::new();
        if self.eat(&close) {
            return Ok(items);
        }
        loop {
            items.push(self.parse_expr()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(close)?;
        Ok(items)
    }

    fn parse_list(&mut self) -> PResult<Expr> {
        self.expect(Tok::LBracket)?;
        if self.eat(&Tok::RBracket) {
            return Ok(Expr::Lit(Literal::Nil));
        }
        let mut heads = vec![self.parse_expr()?];
        while self.eat(&Tok::Comma) {
            heads.push(self.parse_expr()?);
        }
        let tail = if self.eat(&Tok::Bar) {
            self.parse_expr()?
        } else {
            Expr::Lit(Literal::Nil)
        };
        self.expect(Tok::RBracket)?;
        let mut e = tail;
        for h in heads.into_iter().rev() {
            e = Expr::Cons(Box::new(h), Box::new(e));
        }
        Ok(e)
    }

    /// `#{ #<v>(spec...), ... }#`. The caller supplies the value parser
    /// (expression or pattern position). Consumes from BinOpen through BinClose.
    fn parse_binary<V>(
        &mut self,
        parse_value: impl Fn(&mut Self) -> PResult<V>,
    ) -> PResult<Vec<BinSegment<V>>> {
        self.expect(Tok::BinOpen)?;
        let mut segs = Vec::new();
        if self.eat(&Tok::BinClose) {
            return Ok(segs);
        }
        loop {
            // A segment can have an annotation wrapper: `( #<v>(spec) -| [...] )`
            let wrapped = self.eat(&Tok::LParen);
            self.expect(Tok::SegOpen)?;
            let value = parse_value(self)?;
            self.expect(Tok::Gt)?;
            self.expect(Tok::LParen)?;
            let spec = self.parse_comma_exprs(Tok::RParen)?;
            if wrapped {
                self.skip_annotation()?;
                self.expect(Tok::RParen)?;
            }
            segs.push(BinSegment { value, spec });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::BinClose)?;
        Ok(segs)
    }

    fn parse_var_list(&mut self) -> PResult<Vec<String>> {
        if self.eat(&Tok::Lt) {
            let mut vars = Vec::new();
            if self.eat(&Tok::Gt) {
                return Ok(vars);
            }
            loop {
                match self.bump() {
                    Tok::Var(v) => vars.push(v),
                    other => {
                        return Err(format!(
                            "line {}: expected variable, found {}",
                            self.line(),
                            other
                        ))
                    }
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::Gt)?;
            Ok(vars)
        } else {
            match self.bump() {
                Tok::Var(v) => Ok(vec![v]),
                other => Err(format!(
                    "line {}: expected variable, found {}",
                    self.line(),
                    other
                )),
            }
        }
    }

    // Clauses and patterns

    fn parse_clause(&mut self) -> PResult<Clause> {
        // A whole clause can have an annotation: ( <ps> when g -> b -| [...] )
        if self.eat(&Tok::LParen) {
            let c = self.parse_clause()?;
            self.skip_annotation()?;
            self.expect(Tok::RParen)?;
            return Ok(c);
        }
        let patterns = if self.eat(&Tok::Lt) {
            let mut ps = Vec::new();
            if !self.eat(&Tok::Gt) {
                loop {
                    ps.push(self.parse_pattern()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::Gt)?;
            }
            ps
        } else {
            vec![self.parse_pattern()?]
        };
        self.expect(Tok::When)?;
        let guard = self.parse_expr()?;
        self.expect(Tok::Arrow)?;
        let body = self.parse_expr()?;
        Ok(Clause {
            patterns,
            guard,
            body,
        })
    }

    fn parse_pattern(&mut self) -> PResult<Pattern> {
        let first = self.parse_pattern_primary()?;
        // An alias `P1 = P2` can follow any pattern. erlc parenthesizes and
        // annotates either side. One side must be a variable.
        if self.eat(&Tok::Eq) {
            let second = self.parse_pattern()?;
            match (first, second) {
                (Pattern::Var(v), p) | (p, Pattern::Var(v)) => {
                    Ok(Pattern::Alias(v, Box::new(p)))
                }
                _ => Err(format!(
                    "line {}: alias pattern without a variable side",
                    self.line()
                )),
            }
        } else {
            Ok(first)
        }
    }

    fn parse_pattern_primary(&mut self) -> PResult<Pattern> {
        match self.peek().clone() {
            Tok::Var(v) => {
                self.bump();
                Ok(Pattern::Var(v))
            }
            // `( pat -| ann )`. parse_pattern handles aliases inside the parentheses.
            Tok::LParen => {
                self.bump();
                let pat = self.parse_pattern()?;
                self.skip_annotation()?;
                self.expect(Tok::RParen)?;
                Ok(pat)
            }
            Tok::Int(n) => {
                self.bump();
                Ok(Pattern::Lit(Literal::Int(n)))
            }
            Tok::BigInt(d) => {
                self.bump();
                Ok(Pattern::Lit(Literal::Big(d)))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(Pattern::Lit(Literal::Float(f)))
            }
            Tok::Char(c) => {
                self.bump();
                Ok(Pattern::Lit(Literal::Int(c)))
            }
            Tok::Atom(_) => {
                let a = self.parse_atom()?;
                Ok(Pattern::Lit(Literal::Atom(a)))
            }
            Tok::LBrace => {
                self.bump();
                let mut items = Vec::new();
                if !self.eat(&Tok::RBrace) {
                    loop {
                        items.push(self.parse_pattern()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(Tok::RBrace)?;
                }
                Ok(Pattern::Tuple(items))
            }
            Tok::LBracket => {
                self.bump();
                if self.eat(&Tok::RBracket) {
                    return Ok(Pattern::Lit(Literal::Nil));
                }
                let mut heads = vec![self.parse_pattern()?];
                while self.eat(&Tok::Comma) {
                    heads.push(self.parse_pattern()?);
                }
                let tail = if self.eat(&Tok::Bar) {
                    self.parse_pattern()?
                } else {
                    Pattern::Lit(Literal::Nil)
                };
                self.expect(Tok::RBracket)?;
                let mut p = tail;
                for h in heads.into_iter().rev() {
                    p = Pattern::Cons(Box::new(h), Box::new(p));
                }
                Ok(p)
            }
            Tok::BinOpen => {
                let segs = self.parse_binary(|p| Ok(Box::new(p.parse_pattern()?)))?;
                Ok(Pattern::Binary(segs))
            }
            Tok::MapOpen => {
                self.bump();
                let mut pairs = Vec::new();
                if !self.eat(&Tok::MapClose) {
                    loop {
                        let wrapped = self.pair_wrap_ahead();
                        if wrapped {
                            self.expect(Tok::LParen)?;
                        }
                        let key = self.parse_expr()?;
                        if !self.eat(&Tok::ExactAssoc) {
                            self.expect(Tok::Assoc)?;
                        }
                        let val = self.parse_pattern()?;
                        if wrapped {
                            self.skip_annotation()?;
                            self.expect(Tok::RParen)?;
                        }
                        pairs.push((key, val));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(Tok::MapClose)?;
                }
                Ok(Pattern::Map(pairs))
            }
            other => Err(format!(
                "line {}: unsupported token in pattern: {}",
                self.line(),
                other
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_minimal_module() {
        let src = r#"
module 'm' ['f'/1]
    attributes []
'f'/1 =
    ( fun (_0) ->
        case _0 of
          <0> when 'true' -> 'zero'
          <N> when 'true' ->
            let <_1> = call 'erlang':'-'(N, 1)
            in apply 'f'/1(_1)
        end
      -| [{'function',{'f',1}}] )
end
"#;
        let m = parse_module(src).expect("parse");
        assert_eq!(m.name, "m");
        assert_eq!(m.definitions.len(), 1);
        assert_eq!(m.definitions[0].0, FunName { name: "f".into(), arity: 1 });
    }

    #[test]
    fn parses_map_literals() {
        let src = r#"
module 'm' ['f'/1]
    attributes []
'f'/1 =
    fun (_0) ->
        case _0 of
          <~{'k' := V}~> when 'true' -> ~{'k' => V, 'x' => 1}~
          <M> when 'true' -> ~{'k' => 2 | M}~
        end
end
"#;
        let m = parse_module(src).expect("parse");
        assert_eq!(m.definitions.len(), 1);
    }

    #[test]
    fn parses_binary_literals() {
        // The shape comes from the __info__/1 that Elixir generates (the exports_md5 clause).
        let src = r#"
module 'm' ['f'/0]
    attributes []
'f'/0 =
    fun () ->
        case 'x' of
          <'exports_md5'> when 'true' ->
              #{#<125>(8,1,'integer',['unsigned'|['big']]),
                #<4>(8,1,'integer',['unsigned'|['big']])}#
          <#{#<V>(8,1,'integer',['unsigned'|['big']])}#> when 'true' -> V
          <_1> when 'true' -> 'nope'
        end
end
"#;
        let m = parse_module(src).expect("parse");
        assert_eq!(m.definitions.len(), 1);
    }
}
