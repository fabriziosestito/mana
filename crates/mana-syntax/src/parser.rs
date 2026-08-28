//! Recursive-descent parser for the Core Erlang subset emitted by `erlc +to_core`.

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

    // ---- module ----

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
        if !self.eat(&Tok::RBracket) {
            loop {
                // 'key' = const  — parsed and discarded
                self.parse_atom()?;
                self.expect(Tok::Eq)?;
                self.parse_expr()?;
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
        // fname may be wrapped in an annotation: ( 'f'/1 -| [...] )
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

    /// Consume a `-| [...]` annotation if present. The content is arbitrary
    /// constant terms; we parse structurally and discard.
    fn skip_annotation(&mut self) -> PResult<()> {
        if self.eat(&Tok::AnnoBar) {
            self.parse_expr()?;
        }
        Ok(())
    }

    // ---- expressions ----

    fn parse_expr(&mut self) -> PResult<Expr> {
        match self.peek().clone() {
            Tok::LParen => {
                self.bump();
                if self.is_fname_ahead() {
                    return self.err("fname is not valid in expression position");
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
            Tok::Float(f) => {
                self.bump();
                Ok(Expr::Lit(Literal::Float(f)))
            }
            Tok::Char(c) => {
                self.bump();
                Ok(Expr::Lit(Literal::Int(c)))
            }
            Tok::Atom(_) => {
                let a = self.parse_atom()?;
                Ok(Expr::Lit(Literal::Atom(a)))
            }
            Tok::Str(s) => {
                self.bump();
                // string literal is sugar for a char list
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
                        let key = self.parse_expr()?;
                        if !self.eat(&Tok::Assoc) {
                            self.expect(Tok::ExactAssoc)?;
                        }
                        let val = self.parse_expr()?;
                        pairs.push((key, val));
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
                self.expect(Tok::LParen)?;
                let mut params = Vec::new();
                if !self.eat(&Tok::RParen) {
                    loop {
                        match self.bump() {
                            Tok::Var(v) => params.push(v),
                            other => {
                                return Err(format!(
                                    "line {}: expected parameter, found {}",
                                    self.line(),
                                    other
                                ))
                            }
                        }
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
                let module = self.parse_atom_expr()?;
                self.expect(Tok::Colon)?;
                let name = self.parse_atom_expr()?;
                let args = self.parse_call_args()?;
                Ok(Expr::Call { module, name, args })
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

    /// True if the next tokens are `'atom' / int` (an fname), used to
    /// disambiguate inside parentheses.
    fn is_fname_ahead(&self) -> bool {
        matches!(self.toks.get(self.pos).map(|t| &t.0), Some(Tok::Atom(_)))
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.0), Some(Tok::Slash))
    }

    fn parse_fname_no_paren(&mut self) -> PResult<FunName> {
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

    /// An atom, possibly annotated/parenthesized (module/function position of `call`).
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

    /// `#{ #<v>(spec...), ... }#` — caller supplies how to parse the value
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
            self.expect(Tok::SegOpen)?;
            let value = parse_value(self)?;
            self.expect(Tok::Gt)?;
            self.expect(Tok::LParen)?;
            let spec = self.parse_comma_exprs(Tok::RParen)?;
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

    // ---- clauses & patterns ----

    fn parse_clause(&mut self) -> PResult<Clause> {
        // a whole clause may be annotated: ( <ps> when g -> b -| [...] )
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
        match self.peek().clone() {
            Tok::LParen => {
                self.bump();
                let p = self.parse_pattern()?;
                self.skip_annotation()?;
                self.expect(Tok::RParen)?;
                Ok(p)
            }
            Tok::Var(v) => {
                self.bump();
                if self.eat(&Tok::Eq) {
                    let p = self.parse_pattern()?;
                    Ok(Pattern::Alias(v, Box::new(p)))
                } else {
                    Ok(Pattern::Var(v))
                }
            }
            Tok::Int(n) => {
                self.bump();
                Ok(Pattern::Lit(Literal::Int(n)))
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
                        let key = self.parse_expr()?;
                        if !self.eat(&Tok::ExactAssoc) {
                            self.expect(Tok::Assoc)?;
                        }
                        let val = self.parse_pattern()?;
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
        // shape taken from Elixir's generated __info__/1 (exports_md5 clause)
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
