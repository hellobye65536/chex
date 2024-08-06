use crate::Span;

pub mod ast;
pub mod iota;

#[derive(Debug)]
pub struct Lexer<'lex, 'str, Token> {
    strlex: &'lex mut StrLex<'str>,
    span: Span,
    peek: Option<Result<Token, ParseError>>,
}

pub type ParseResult<T> = Option<Result<T, ParseError>>;

impl<'lex, 'str, Token> Lexer<'lex, 'str, Token> {
    pub fn new(strlex: &'lex mut StrLex<'str>) -> Self {
        let pos = strlex.pos();
        Self {
            strlex,
            span: (pos..pos).into(),
            peek: None,
        }
    }

    pub fn peek<F>(&mut self, lex_fn: F) -> ParseResult<&Token>
    where
        F: FnOnce(&mut StrLex<'str>) -> Option<LexResult<Token>>,
    {
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

    pub fn inner(&mut self) -> &mut StrLex<'str> {
        debug_assert!(self.peek.is_none());
        self.strlex
    }

    pub fn transform<Token2>(&mut self) -> Lexer<'_, 'str, Token2> {
        Lexer::new(self.inner())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ParseError;

#[derive(Debug, Clone)]
pub struct LexResult<Token> {
    span: Span,
    token: Result<Token, ParseError>,
}

impl<Token> LexResult<Token> {
    pub fn new(span: impl Into<Span>, token: Result<Token, ParseError>) -> Self {
        Self {
            span: span.into(),
            token,
        }
    }

    pub fn new_token(span: impl Into<Span>, token: Token) -> Self {
        Self::new(span, Ok(token))
    }

    pub fn new_error(span: impl Into<Span>) -> Self {
        Self::new(span, Err(ParseError))
    }
}

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
