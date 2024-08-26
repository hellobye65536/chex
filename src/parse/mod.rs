use std::{cell::Cell, fmt::Display, mem};

use crate::core::{Context, Diagnostic, FileId, FileSpan, Severity, Span};

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
pub struct Lexer<'p, 'str, Token> {
    strlex: &'p mut StrLex<'str>,
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
                self.fuel.set(REFUEL);
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
        self.peek.take()
    }

    pub fn pos(&self) -> usize {
        if self.peek.is_some() {
            self.span.start()
        } else {
            self.strlex.pos()
        }
    }

    pub fn span(&self) -> Span {
        self.span
    }

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

pub trait LexFn<'str> {
    type Token;
    fn lex(&mut self, strlex: &mut StrLex<'str>) -> Option<LexResult<Self::Token>>;
}

impl<'str, T: LexFn<'str>> LexFn<'str> for &mut T {
    type Token = T::Token;

    fn lex(&mut self, strlex: &mut StrLex<'str>) -> Option<LexResult<Self::Token>> {
        <T as LexFn<'str>>::lex(self, strlex)
    }
}

#[derive(Debug)]
pub struct ParseContext<'p, 'str, T, F> {
    pub ctx: &'p mut Context,
    pub file: FileId,
    pub lex_state: Lexer<'p, 'str, T>,
    pub lex_fn: F,
}

impl<'p, 'str, T> ParseContext<'p, 'str, T, ()> {
    pub fn new(ctx: &'p mut Context, file: FileId, strlex: &'p mut StrLex<'str>) -> Self {
        Self {
            ctx,
            file,
            lex_state: Lexer::new(strlex),
            lex_fn: (),
        }
    }
}

impl<'p, 'str, T, F> ParseContext<'p, 'str, T, F> {
    pub fn change_token<NT>(&mut self) -> ParseContext<'_, 'str, NT, ()> {
        assert!(self.lex_state.peek.is_none());
        ParseContext {
            ctx: self.ctx,
            file: self.file,
            lex_state: Lexer::new(self.lex_state.inner_mut()),
            lex_fn: (),
        }
    }

    pub fn with_lex_fn<NF>(self, lex_fn: NF) -> ParseContext<'p, 'str, T, NF> {
        ParseContext {
            ctx: self.ctx,
            file: self.file,
            lex_state: self.lex_state,
            lex_fn,
        }
    }

    pub fn emit_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.ctx.emit_diagnostic(diagnostic)
    }

    pub fn peek_fn<'s, NF>(&'s mut self, lex_fn: &mut NF) -> ParseResult<&'s T>
    where
        NF: LexFn<'str, Token = T>,
    {
        self.lex_state.peek(|strlex| lex_fn.lex(strlex))
    }

    pub fn take(&mut self) -> ParseResult<T> {
        self.lex_state.take()
    }

    pub fn pos(&self) -> usize {
        self.lex_state.pos()
    }

    pub fn file(&self) -> FileId {
        self.file
    }

    pub fn span(&self) -> Span {
        self.lex_state.span()
    }

    pub fn file_span(&self) -> FileSpan {
        (self.file(), self.span()).into()
    }
}

impl<'p, 'str, T, F> ParseContext<'p, 'str, T, F>
where
    F: LexFn<'str, Token = T>,
    T: GroupingToken,
{
    pub fn peek(&mut self) -> ParseResult<&T> {
        self.peek_closing()
            .filter(|v| !v.is_ok_and(|v| v.left_matching().is_some()))
    }

    pub fn peek_closing(&mut self) -> ParseResult<&T> {
        self.lex_state.peek(|strlex| self.lex_fn.lex(strlex))
    }
}

impl<'p, 'str, T, F> ParseContext<'p, 'str, T, F>
where
    F: LexFn<'str, Token = T>,
    T: GroupingToken + Display,
{
    pub fn parse_diagnostic(&mut self, expected: impl Display + Into<String>) {
        let message = match self.lex_state.peek.as_ref() {
            Some(Ok(t)) => format!("{}, got {}", expected, t),
            Some(Err(_)) => format!("{}, got invalid token", expected),
            None => format!("{}, got eof", expected),
        };

        self.emit_diagnostic(
            Diagnostic::new(Severity::Error, message, (self.file, self.span()))
                .with_primary_tag(Some(expected.into())),
        )
    }
}

#[must_use]
fn munch_group<'str, T, F>(ctx: &mut ParseContext<'_, 'str, T, F>) -> Option<()>
where
    F: LexFn<'str, Token = T>,
    T: GroupingToken + Display,
{
    ctx.peek()?;
    if let Ok(tok) = ctx.take()? {
        if let Some(matching) = tok.right_matching() {
            return expect_closing(ctx, &matching).map(|_| ());
        }
    }

    Some(())
}

#[must_use]
fn munch_groups_until<'str, T, F>(
    ctx: &mut ParseContext<'_, 'str, T, F>,
    mut pred: impl FnMut(&T) -> bool,
) -> Option<()>
where
    F: LexFn<'str, Token = T>,
    T: GroupingToken + Display,
{
    while ctx.peek()?.is_ok_and(|tok| !pred(tok)) {
        munch_group(ctx)?;
    }

    Some(())
}

#[must_use]
fn expect_closing<'str, T, F>(
    ctx: &mut ParseContext<'_, 'str, T, F>,
    right: &T,
) -> ParseResult<Span>
where
    F: LexFn<'str, Token = T>,
    T: GroupingToken + Display,
{
    expect_closing_ext(ctx, right, false)
}

#[must_use]
fn expect_closing_ext<'str, T, F>(
    ctx: &mut ParseContext<'_, 'str, T, F>,
    right: &T,
    skip_only: bool,
) -> ParseResult<Span>
where
    F: LexFn<'str, Token = T>,
    T: GroupingToken + Display,
{
    debug_assert!(right.left_matching().is_some());

    if let Ok(tok) = ctx.peek_closing()? {
        if mem::discriminant(tok) == mem::discriminant(right) {
            ctx.take();
            return Some(Ok(ctx.span()));
        } else if tok.left_matching().is_some() {
            ctx.parse_diagnostic(format!("expected {}", right));
            return None;
        }
    }

    if !skip_only {
        ctx.parse_diagnostic(format!("expected {}", right));
    }

    loop {
        let Ok(tok) = ctx.peek_closing()? else {
            ctx.take();
            continue;
        };

        if mem::discriminant(tok) == mem::discriminant(right) {
            ctx.take();
            return Some(Err(ParseError));
        } else if tok.left_matching().is_some() {
            ctx.parse_diagnostic(format!("missing closing {}", right));
            return None;
        } else if let Some(matching) = tok.right_matching() {
            ctx.take();
            expect_closing_ext(ctx, &matching, true)?;
        } else {
            ctx.take();
        }
    }
}
