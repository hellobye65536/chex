use std::{cell::Cell, fmt::Display, mem};

use crate::{
    diagnostics::{Diagnostic, Severity},
    Context, Span,
};

pub mod ast;
pub mod iota;

#[derive(Debug, Clone, Copy)]
pub struct ParseError;

#[derive(Debug, Clone)]
pub struct StrLex<'str> {
    pos: usize,
    str: &'str str,
}

impl<'str> StrLex<'str> {
    pub fn new(str: &'str str) -> Self {
        Self { pos: 0, str }
    }

    pub fn peek(&self) -> Option<char> {
        self.str[self.pos..].chars().next()
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<char> {
        let mut iter = self.str[self.pos..].chars();
        let plen = iter.as_str().len();
        let ret = iter.next();
        self.pos += plen - iter.as_str().len();
        ret
    }

    pub fn skip_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        let mut iter = self.str[self.pos..].char_indices();
        if let Some((i, _)) = iter.find(|&(_, c)| !pred(c)) {
            self.pos += i;
        } else {
            self.pos = self.str.len();
        }
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn str(&self) -> &'str str {
        self.str
    }

    pub fn make_result<Token>(
        &self,
        start: usize,
        token: Result<Token, ParseError>,
    ) -> LexResult<Token> {
        LexResult::new(start..self.pos, token)
    }

    pub fn make_token<Token>(&self, start: usize, token: Token) -> LexResult<Token> {
        LexResult::new_token(start..self.pos, token)
    }

    pub fn make_error<Token>(&self, start: usize) -> LexResult<Token> {
        LexResult::new_error(start..self.pos)
    }
}

#[derive(Debug, Clone)]
pub struct LexResult<T> {
    span: Span,
    token: Result<T, ParseError>,
}

impl<T> LexResult<T> {
    pub fn new(span: impl Into<Span>, token: Result<T, ParseError>) -> Self {
        Self {
            span: span.into(),
            token,
        }
    }

    pub fn new_token(span: impl Into<Span>, token: T) -> Self {
        Self::new(span, Ok(token))
    }

    pub fn new_error(span: impl Into<Span>) -> Self {
        Self::new(span, Err(ParseError))
    }
}

#[derive(Debug)]
pub struct Lexer<'lex, 'str, Token> {
    strlex: &'lex mut StrLex<'str>,
    span: Span,
    peek: Option<Result<Token, ParseError>>,
    fuel: Cell<u32>,
}

pub type ParseResult<T> = Option<Result<T, ParseError>>;

const REFUEL: u32 = 256;

impl<'lex, 'str, Token> Lexer<'lex, 'str, Token> {
    pub fn new(strlex: &'lex mut StrLex<'str>) -> Self {
        let pos = strlex.pos();
        Self {
            strlex,
            span: (pos..pos).into(),
            peek: None,
            fuel: Cell::new(REFUEL),
        }
    }

    pub fn peek<F>(&mut self, lex_fn: F) -> ParseResult<&Token>
    where
        F: FnOnce(&mut StrLex<'str>) -> Option<LexResult<Token>>,
    {
        self.fuel
            .set(self.fuel.get().checked_sub(1).expect("ran out of fuel"));

        self.peek = self.peek.take().or_else(|| {
            if let Some(res) = lex_fn(self.strlex) {
                self.span = res.span;
                Some(res.token)
            } else {
                let pos = self.strlex.pos();
                self.span = (pos..pos).into();
                None
            }
        });
        self.peek
            .as_ref()
            .map(|v| v.as_ref().map_err(|_| ParseError))
    }

    pub fn take(&mut self) -> ParseResult<Token> {
        self.fuel.set(REFUEL);
        self.peek.take()
    }

    pub fn span(&self) -> Span {
        self.span
    }

    // pub fn skip_while<F, P>(&mut self, lex: F, mut pred: P)
    // where
    //     F: FnOnce(&mut StrLex<'str>) -> Option<LexResult<Token>>,
    //     P: FnMut(&Token) -> bool,
    // {
    // }

    pub fn inner(&self) -> &StrLex<'str> {
        self.strlex
    }
    pub fn inner_mut(&mut self) -> &mut StrLex<'str> {
        debug_assert!(self.peek.is_none());
        self.strlex
    }

    pub fn transform<Token2>(&mut self) -> Lexer<'_, 'str, Token2> {
        Lexer::new(self.inner_mut())
    }
}

pub trait GroupingToken: Sized {
    fn right_matching(&self) -> Option<Self>;
    fn left_matching(&self) -> Option<Self>;
    fn matching(&self) -> Option<Self>;
}

pub trait SubLexer<'lex, 'str: 'lex, T> {
    fn inner(&self) -> &Lexer<'lex, 'str, T>;
    fn inner_mut(&mut self) -> &mut Lexer<'lex, 'str, T>;

    fn peek_closing(&mut self) -> ParseResult<&T>;
}

pub trait SubLexerExt<'lex, 'str, T> {
    fn peek(&mut self) -> ParseResult<&T>;
    fn take(&mut self) -> ParseResult<T>;
    fn pos(&self) -> usize;
    fn span(&self) -> Span;
    fn make_diagnostic(&mut self, expected: impl Display + Into<String>) -> Diagnostic;
}

impl<'lex, 'str: 'lex, T, L> SubLexerExt<'lex, 'str, T> for L
where
    T: GroupingToken + Display,
    L: SubLexer<'lex, 'str, T>,
{
    fn peek(&mut self) -> ParseResult<&T> {
        self.peek_closing()
            .filter(|v| !v.is_ok_and(|v| v.left_matching().is_some()))
    }

    fn take(&mut self) -> ParseResult<T> {
        self.inner_mut().take()
    }

    fn pos(&self) -> usize {
        self.inner().inner().pos()
    }

    fn span(&self) -> Span {
        self.inner().span()
    }

    fn make_diagnostic(&mut self, expected: impl Display + Into<String>) -> Diagnostic {
        let message = match self.inner().peek.as_ref() {
            Some(Ok(t)) => format!("{}, got {}", expected, t),
            Some(Err(_)) => format!("{}, got invalid token", expected),
            None => format!("{}, got eof", expected),
        };

        Diagnostic::new(Severity::Error, message, self.span())
            .with_primary_tag(Some(expected.into()))
    }
}

#[must_use]
fn munch_group<'lex, 'str: 'lex, T, L>(ctx: &mut Context, lex: &mut L) -> Option<()>
where
    T: GroupingToken + Display,
    L: SubLexer<'lex, 'str, T>,
{
    lex.peek()?;
    if let Ok(tok) = lex.take()? {
        if let Some(matching) = tok.right_matching() {
            return expect_closing(ctx, lex, &matching).map(|_| ());
        }
    }

    Some(())
}

#[must_use]
fn munch_groups_until<'lex, 'str: 'lex, T, L>(
    ctx: &mut Context,
    lex: &mut L,
    mut pred: impl FnMut(&T) -> bool,
) -> Option<()>
where
    T: GroupingToken + Display,
    L: SubLexer<'lex, 'str, T>,
{
    while lex.peek()?.is_ok_and(|tok| !pred(tok)) {
        munch_group(ctx, lex)?;
    }

    Some(())
}

#[must_use]
fn expect_closing<'lex, 'str: 'lex, T, L>(
    ctx: &mut Context,
    lex: &mut L,
    right: &T,
) -> ParseResult<Span>
where
    T: GroupingToken + Display,
    L: SubLexer<'lex, 'str, T>,
{
    expect_closing_ext(ctx, lex, right, false)
}

#[must_use]
fn expect_closing_ext<'lex, 'str: 'lex, T, L>(
    ctx: &mut Context,
    lex: &mut L,
    right: &T,
    skip_only: bool,
) -> ParseResult<Span>
where
    T: GroupingToken + Display,
    L: SubLexer<'lex, 'str, T>,
{
    debug_assert!(right.left_matching().is_some());

    if let Ok(tok) = lex.peek_closing()? {
        if mem::discriminant(tok) == mem::discriminant(right) {
            lex.take();
            return Some(Ok(lex.span()));
        } else if tok.left_matching().is_some() {
            ctx.emit_diagnostic(lex.make_diagnostic(format!("expected {}", right)));
            return None;
        }
    }

    if !skip_only {
        ctx.emit_diagnostic(lex.make_diagnostic(format!("expected {}", right)));
    }

    loop {
        let Ok(tok) = lex.peek_closing()? else {
            lex.take();
            continue;
        };

        if mem::discriminant(tok) == mem::discriminant(right) {
            lex.take();
            return Some(Err(ParseError));
        } else if tok.left_matching().is_some() {
            ctx.emit_diagnostic(lex.make_diagnostic(format!("missing closing {}", right)));
            return None;
        } else if let Some(matching) = tok.right_matching() {
            lex.take();
            expect_closing_ext(ctx, lex, &matching, true)?;
        } else {
            lex.take();
        }
    }
}
