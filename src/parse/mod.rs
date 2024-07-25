use crate::Span;

pub mod iota;
pub mod ir;

#[derive(Debug)]
pub struct Lexer<'lex, 'str, Token> {
    strlex: &'lex mut StrLex<'str>,
    peek: Option<LexResult<Token>>,
}

impl<'lex, 'str, Token> Lexer<'lex, 'str, Token> {
    pub fn new(strlex: &'lex mut StrLex<'str>) -> Self {
        Self { strlex, peek: None }
    }

    pub fn span(&self) -> Span {
        self.peek.as_ref().unwrap().span
    }

    pub fn peek<F>(&mut self, lex_fn: F) -> Option<Result<&Token, ParseError>>
    where
        F: FnOnce(&mut StrLex<'str>) -> Option<LexResult<Token>>,
    {
        self.peek = self.peek.take().or_else(|| lex_fn(self.strlex));
        self.peek
            .as_ref()
            .map(|res| res.token.as_ref().map_err(|v| *v))
    }

    pub fn next<F>(&mut self, lex_fn: F) -> Option<Result<Token, ParseError>>
    where
        F: FnOnce(&mut StrLex<'str>) -> Option<LexResult<Token>>,
    {
        self.peek
            .take()
            .or_else(|| lex_fn(self.strlex))
            .map(|v| v.token)
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
        debug_assert!(self.peek.is_none());
        Lexer {
            strlex: self.strlex,
            peek: None,
        }
    }

    // pub fn with_transformed<T, F, R>(&mut self, f: F) -> R
    // where
    //     T: TryFrom<Token, Error = LexError>,
    //     Token: TryFrom<T, Error = LexError>,
    //     F: FnOnce(&mut Lexer<'_, 'str, T>) -> R,
    // {
    //     let mut sublex = Lexer {
    //         lex: self.lex,
    //         peek: self
    //             .peek
    //             .take()
    //             .map(|res| LexResult::new(res.span, res.token.and_then(T::try_from))),
    //     };

    //     let ret = f(&mut sublex);

    //     self.peek = sublex
    //         .peek
    //         .map(|res| LexResult::new(res.span, res.token.and_then(Token::try_from)));

    //     ret
    // }
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

    pub fn new_token<T>(span: T, token: Token) -> Self
    where
        Span: From<T>,
    {
        Self::new(span, Ok(token))
    }

    pub fn new_error<T>(span: T) -> Self
    where
        Span: From<T>,
    {
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
