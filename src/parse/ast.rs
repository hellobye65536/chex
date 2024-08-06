use std::{fmt::Display, mem};

use crate::{
    diagnostics::{Diagnostic, Severity, Tag}, Context, Span
};

use super::{LexResult, ParseError, ParseResult, StrLex};

#[derive(Debug, Clone)]
pub enum Token<'a> {
    Symbol(&'a str),
    Num(f64),
    Operator(&'a str),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LCurly,
    RCurly,
    Semi,
    Comma,
    KwDef,
    KwLet,
    KwBlock,
    KwReturn,
    KwIota,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operator {
    Comma,
    Not,
    And,
    Or,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
}

// Operator::Not => "`!`",
// Operator::And => "`&&`",
// Operator::Or => "`||`",
// Operator::Eq => "`==`",
// Operator::Ne => "`!=`",
// Operator::Lt => "`<`",
// Operator::Gt => "`>`",
// Operator::Le => "`<=`",
// Operator::Ge => "`>=`",
// Operator::Add => "`+`",
// Operator::Sub => "`-`",
// Operator::Mul => "`*`",
// Operator::Div => "`/`",

impl<'a> Token<'a> {
    pub fn display_type(&self) -> &'static str {
        match self {
            Token::Symbol(_) => "symbol",
            Token::Num(_) => "number",
            Token::Operator(_) => "operator",
            Token::LParen => "`(`",
            Token::RParen => "`)`",
            Token::LBracket => "`[`",
            Token::RBracket => "`]`",
            Token::LCurly => "`{`",
            Token::RCurly => "`}`",
            Token::Semi => "`;`",
            Token::Comma => "`,`",
            Token::KwDef => "`def`",
            Token::KwLet => "`let`",
            Token::KwBlock => "`block`",
            Token::KwReturn => "`return`",
            Token::KwIota => "`iota`",
        }
    }

    pub fn right_matching(&self) -> Option<Token<'static>> {
        Some(match self {
            Token::LParen => Token::RParen,
            Token::LBracket => Token::RBracket,
            Token::LCurly => Token::RCurly,
            _ => return None,
        })
    }

    pub fn left_matching(&self) -> Option<Token<'static>> {
        Some(match self {
            Token::RParen => Token::LParen,
            Token::RBracket => Token::LBracket,
            Token::RCurly => Token::LCurly,
            _ => return None,
        })
    }

    pub fn matching(&self) -> Option<Token<'static>> {
        Some(match self {
            Token::LParen => Token::RParen,
            Token::RParen => Token::LParen,
            Token::LBracket => Token::RBracket,
            Token::RBracket => Token::LBracket,
            Token::LCurly => Token::RCurly,
            Token::RCurly => Token::LCurly,
            _ => return None,
        })
    }
}

fn is_symbol_start(c: char) -> bool {
    matches!(c, '_' | 'a'..='z' | 'A'..='Z')
}

fn is_symbol_continue(c: char) -> bool {
    matches!(c, '_' | 'a'..='z' | 'A'..='Z' | '0'..='9')
}

fn is_operator(c: char) -> bool {
    [
        '!', '%', '^', '&', '*', '-', '+', '=', '|', ':', '<', '>', '.', '/', '?',
    ]
    .contains(&c)
}

fn is_token_sep(c: char) -> bool {
    c.is_ascii_whitespace()
        || ['(', ')', '[', ']', '{', '}', ';', ','].contains(&c)
        || is_operator(c)
}

fn lex_default<'str>(strlex: &mut StrLex<'str>) -> Option<LexResult<Token<'str>>> {
    strlex.skip_while(|c| c.is_ascii_whitespace() && c != '\n');
    let start = strlex.pos();

    Some(match strlex.next()? {
        '(' => strlex.make_token(start, Token::LParen),
        ')' => strlex.make_token(start, Token::RParen),
        '[' => strlex.make_token(start, Token::LBracket),
        ']' => strlex.make_token(start, Token::RBracket),
        '{' => strlex.make_token(start, Token::LCurly),
        '}' => strlex.make_token(start, Token::RCurly),
        ';' => strlex.make_token(start, Token::Semi),
        ',' => strlex.make_token(start, Token::Comma),
        c if is_operator(c) => {
            strlex.skip_while(is_operator);
            strlex.make_token(start, Token::Operator(&strlex.str()[start..strlex.pos()]))
        }
        c if is_symbol_start(c) => {
            strlex.skip_while(is_symbol_continue);
            strlex.make_token(start, Token::Symbol(&strlex.str()[start..strlex.pos()]))
        }
        _ => {
            strlex.skip_while(|c| !is_token_sep(c));
            strlex.make_error(start)
        }
    })
}

#[derive(Debug)]
struct Lexer<'lex, 'str>(super::Lexer<'lex, 'str, Token<'str>>);

impl<'lex, 'str> Lexer<'lex, 'str> {
    #[must_use]
    pub fn peek(&mut self) -> Option<Result<&Token<'str>, ParseError>> {
        self.0
            .peek(lex_default)
            .filter(|v| !v.is_ok_and(|v| v.left_matching().is_some()))
    }

    #[must_use]
    pub fn peek_closing(&mut self) -> Option<Result<&Token<'str>, ParseError>> {
        self.0.peek(lex_default)
    }

    pub fn take(&mut self) -> ParseResult<Token> {
        self.0.take()
    }

    pub fn span(&self) -> Span {
        self.0.span()
    }

    pub fn make_diagnostic(&mut self, expected: impl Display + Clone) -> Diagnostic {
        let peek = &self.0.peek.as_ref();
        let peek_str = peek.map_or("eof", |peek| {
            peek.as_ref().map_or("invalid token", Token::display_type)
        });

        Diagnostic::new(
            Severity::Error,
            format_args!("{}, got {}", expected.clone(), peek_str),
            self.span(),
        )
        .tag(Tag::new(Severity::Error, expected, self.span()))
    }
}

#[must_use]
fn munch_group(ctx: &mut Context, lex: &mut Lexer) -> Option<()> {
    lex.peek()?;
    if let Ok(tok) = lex.take()? {
        if let Some(matching) = tok.right_matching() {
            return expect_closing(ctx, lex, &matching).map(|_| ());
        }
    }

    Some(())
}

#[must_use]
fn expect_closing(ctx: &mut Context, lex: &mut Lexer, right: &Token) -> ParseResult<()> {
    debug_assert!(right.left_matching().is_some());

    let mut err = false;

    loop {
        if let Ok(tok) = lex.peek_closing()? {
            if mem::discriminant(tok) == mem::discriminant(right) {
                lex.take();
                if err {
                    ctx.emit_diagnostic(
                        lex.make_diagnostic(format_args!("expected {}", right.display_type())),
                    );
                    return Some(Err(ParseError));
                }
                return Some(Ok(()));
            } else if let Some(matching) = tok.left_matching() {
                ctx.emit_diagnostic(
                    lex.make_diagnostic(format_args!("expected {}", right.display_type())),
                );
                return None;
            } else if let Some(matching) = tok.right_matching() {
                lex.take();
                expect_closing(ctx, lex, &matching)?;
            } else {
                lex.take();
            }
        } else {
            lex.take();
        }
        err = true;
    }
}
