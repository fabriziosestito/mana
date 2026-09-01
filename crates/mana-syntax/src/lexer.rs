//! Lexer for Core Erlang text as printed by `erlc +to_core`.

use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    // keywords
    Module,
    Attributes,
    Fun,
    Let,
    Letrec,
    In,
    Case,
    Of,
    When,
    End,
    Call,
    Apply,
    Primop,
    Do,
    Try,
    Catch,
    Receive,
    After,
    // literals & names
    Int(i64),
    /// An integer literal too large for i64 (erlc folds long string
    /// constants into single wide bitstring segments). Decimal digits.
    BigInt(String),
    Float(f64),
    Atom(String),
    Var(String),
    Str(String),
    Char(i64),
    // punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    BinOpen,    // #{
    BinClose,   // }#
    SegOpen,    // #<
    MapOpen,    // ~{
    MapClose,   // }~
    Assoc,      // =>
    ExactAssoc, // :=
    Lt,
    Gt,
    Comma,
    Eq,
    Bar,
    Slash,
    Colon,
    Arrow,   // ->
    AnnoBar, // -|
    Eof,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    pub line: usize,
}

pub type LexResult<T> = Result<T, String>;

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer {
            src: src.as_bytes(),
            pos: 0,
            line: 1,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek();
        if c == Some(b'\n') {
            self.line += 1;
        }
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_ascii_whitespace() => {
                    self.bump();
                }
                Some(b'%') => {
                    while let Some(c) = self.peek() {
                        if c == b'\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                _ => break,
            }
        }
    }

    pub fn next_token(&mut self) -> LexResult<Tok> {
        self.skip_trivia();
        let c = match self.bump() {
            None => return Ok(Tok::Eof),
            Some(c) => c,
        };
        match c {
            b'(' => Ok(Tok::LParen),
            b')' => Ok(Tok::RParen),
            b'{' => Ok(Tok::LBrace),
            // `}` followed by `#`/`~` closes a bitstring/map; a plain
            // tuple-close is always followed by `,`/`)`/... in valid Core
            // Erlang, never `#` or `~`.
            b'}' => match self.peek() {
                Some(b'#') => {
                    self.bump();
                    Ok(Tok::BinClose)
                }
                Some(b'~') => {
                    self.bump();
                    Ok(Tok::MapClose)
                }
                _ => Ok(Tok::RBrace),
            },
            b'~' => match self.bump() {
                Some(b'{') => Ok(Tok::MapOpen),
                other => Err(format!("line {}: unexpected '~{:?}'", self.line, other)),
            },
            b'#' => match self.bump() {
                Some(b'{') => Ok(Tok::BinOpen),
                Some(b'<') => Ok(Tok::SegOpen),
                other => Err(format!("line {}: unexpected '#{:?}'", self.line, other)),
            },
            b'[' => Ok(Tok::LBracket),
            b']' => Ok(Tok::RBracket),
            b'<' => Ok(Tok::Lt),
            b'>' => Ok(Tok::Gt),
            b',' => Ok(Tok::Comma),
            b'=' => {
                if self.peek() == Some(b'>') {
                    self.bump();
                    Ok(Tok::Assoc)
                } else {
                    Ok(Tok::Eq)
                }
            }
            b'|' => Ok(Tok::Bar),
            b'/' => Ok(Tok::Slash),
            b':' => {
                if self.peek() == Some(b'=') {
                    self.bump();
                    Ok(Tok::ExactAssoc)
                } else {
                    Ok(Tok::Colon)
                }
            }
            b'-' => match self.peek() {
                Some(b'>') => {
                    self.bump();
                    Ok(Tok::Arrow)
                }
                Some(b'|') => {
                    self.bump();
                    Ok(Tok::AnnoBar)
                }
                Some(d) if d.is_ascii_digit() => self.lex_number(true),
                other => Err(format!("line {}: unexpected '-{:?}'", self.line, other)),
            },
            b'\'' => self.lex_quoted_atom(),
            b'"' => self.lex_string(),
            b'$' => self.lex_char(),
            d if d.is_ascii_digit() => {
                self.pos -= 1;
                self.lex_number(false)
            }
            a if a.is_ascii_lowercase() => {
                self.pos -= 1;
                let word = self.lex_name();
                Ok(match word.as_str() {
                    "module" => Tok::Module,
                    "attributes" => Tok::Attributes,
                    "fun" => Tok::Fun,
                    "let" => Tok::Let,
                    "letrec" => Tok::Letrec,
                    "in" => Tok::In,
                    "case" => Tok::Case,
                    "of" => Tok::Of,
                    "when" => Tok::When,
                    "end" => Tok::End,
                    "call" => Tok::Call,
                    "apply" => Tok::Apply,
                    "primop" => Tok::Primop,
                    "do" => Tok::Do,
                    "try" => Tok::Try,
                    "catch" => Tok::Catch,
                    "receive" => Tok::Receive,
                    "after" => Tok::After,
                    _ => Tok::Atom(word),
                })
            }
            v if v.is_ascii_uppercase() || v == b'_' => {
                self.pos -= 1;
                Ok(Tok::Var(self.lex_name()))
            }
            other => Err(format!(
                "line {}: unexpected character '{}'",
                self.line, other as char
            )),
        }
    }

    fn lex_name(&mut self) -> String {
        let start = self.pos;
        while let Some(c) = self.peek() {
            // '?' and '!' appear in Elixir-generated variable names
            if c.is_ascii_alphanumeric() || c == b'_' || c == b'@' || c == b'?' || c == b'!' {
                self.bump();
            } else {
                break;
            }
        }
        String::from_utf8_lossy(&self.src[start..self.pos]).into_owned()
    }

    fn lex_number(&mut self, negative: bool) -> LexResult<Tok> {
        let start = self.pos;
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.bump();
        }
        // float: digits '.' digits, optional exponent
        let is_float = self.peek() == Some(b'.')
            && matches!(self.src.get(self.pos + 1), Some(c) if c.is_ascii_digit());
        if is_float {
            self.bump();
            while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                self.bump();
            }
            if matches!(self.peek(), Some(b'e' | b'E')) {
                self.bump();
                if matches!(self.peek(), Some(b'+' | b'-')) {
                    self.bump();
                }
                while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                    self.bump();
                }
            }
            let text = String::from_utf8_lossy(&self.src[start..self.pos]);
            let v: f64 = text
                .parse()
                .map_err(|e| format!("line {}: bad float '{}': {}", self.line, text, e))?;
            return Ok(Tok::Float(if negative { -v } else { v }));
        }
        let text = String::from_utf8_lossy(&self.src[start..self.pos]);
        // smalls are 61-bit tagged (-2^60 ..= 2^60-1): anything outside is
        // a big literal even when it fits i64 — the old i64 cutoff let
        // literals in [2^60, 2^63) wrap silently at codegen
        const SMALL_MAX: i64 = (1 << 60) - 1;
        const SMALL_MIN: i64 = -(1 << 60);
        match text.parse::<i64>() {
            Ok(v) => {
                let v = if negative { -v } else { v };
                if (SMALL_MIN..=SMALL_MAX).contains(&v) {
                    Ok(Tok::Int(v))
                } else {
                    Ok(Tok::BigInt(if negative {
                        format!("-{}", text)
                    } else {
                        text.into_owned()
                    }))
                }
            }
            Err(_) => Ok(Tok::BigInt(if negative {
                format!("-{}", text)
            } else {
                text.into_owned()
            })),
        }
    }

    fn lex_quoted_atom(&mut self) -> LexResult<Tok> {
        let mut s = String::new();
        loop {
            match self.bump() {
                None => return Err(format!("line {}: unterminated atom", self.line)),
                Some(b'\'') => break,
                Some(b'\\') => s.push(self.lex_escape()?),
                Some(c) => s.push(c as char),
            }
        }
        Ok(Tok::Atom(s))
    }

    fn lex_string(&mut self) -> LexResult<Tok> {
        let mut s = String::new();
        loop {
            match self.bump() {
                None => return Err(format!("line {}: unterminated string", self.line)),
                Some(b'"') => break,
                Some(b'\\') => s.push(self.lex_escape()?),
                Some(c) => s.push(c as char),
            }
        }
        Ok(Tok::Str(s))
    }

    fn lex_char(&mut self) -> LexResult<Tok> {
        match self.bump() {
            None => Err(format!("line {}: unterminated char", self.line)),
            Some(b'\\') => Ok(Tok::Char(self.lex_escape()? as i64)),
            Some(c) => Ok(Tok::Char(c as i64)),
        }
    }

    fn lex_escape(&mut self) -> LexResult<char> {
        let c = self
            .bump()
            .ok_or_else(|| format!("line {}: unterminated escape", self.line))?;
        Ok(match c {
            b'n' => '\n',
            b'r' => '\r',
            b't' => '\t',
            b'b' => '\u{8}',
            b'f' => '\u{c}',
            b'v' => '\u{b}',
            b'e' => '\u{1b}',
            b's' => ' ',
            b'd' => '\u{7f}',
            b'0' => '\0',
            other => other as char,
        })
    }
}

/// Tokenize the whole input up front.
pub fn tokenize(src: &str) -> LexResult<Vec<(Tok, usize)>> {
    let mut lx = Lexer::new(src);
    let mut out = Vec::new();
    loop {
        let line = lx.line;
        let t = lx.next_token()?;
        let done = t == Tok::Eof;
        out.push((t, line));
        if done {
            return Ok(out);
        }
    }
}
