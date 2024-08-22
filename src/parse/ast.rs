use std::{
    fmt::{self, Display},
    mem,
    ops::{self, Not},
};

use itertools::Itertools;
use tap::TapFallible;

use crate::{
    ast::parse::{
        Block, Call, CallArity, Def, Expr, ExprKind, File, Ident, Item, ItemKind, LetStmt, OpElem,
        Stmt, StmtKind,
    },
    core::{Context, Diagnostic, Severity, Span, Tag},
    Symbol,
};

use super::{
    expect_closing, expect_closing_ext, munch_group, munch_groups_until, GroupingToken, LexResult,
    ParseError, ParseResult, StrLex, SubLexer, SubLexerExt,
};

#[derive(Debug, Clone)]
pub enum Token<'a> {
    Symbol(&'a str),
    Operator(&'a str),
    Num(f64),
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
    KwInclude,
}

// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// pub enum Operator {
//     Comma,
//     Not,
//     And,
//     Or,
//     Eq,
//     Ne,
//     Lt,
//     Gt,
//     Le,
//     Ge,
//     Add,
//     Sub,
//     Mul,
//     Div,
// }

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

impl Token<'_> {
    pub fn is_semi_symbolic(&self) -> bool {
        matches!(
            self,
            Token::Symbol(_)
                | Token::Num(_)
                | Token::KwDef
                | Token::KwLet
                | Token::KwBlock
                | Token::KwReturn
                | Token::KwIota
                | Token::KwInclude
        )
    }

    pub fn is_expr_begin(&self) -> bool {
        matches!(
            self,
            Token::Symbol(_)
                | Token::Num(_)
                | Token::Operator(_)
                | Token::LParen
                | Token::LBracket
                | Token::LCurly
                | Token::KwBlock
                | Token::KwIota
        )
    }
}

impl GroupingToken for Token<'_> {
    fn right_matching(&self) -> Option<Token<'static>> {
        Some(match self {
            Token::LParen => Token::RParen,
            Token::LBracket => Token::RBracket,
            Token::LCurly => Token::RCurly,
            _ => return None,
        })
    }

    fn left_matching(&self) -> Option<Token<'static>> {
        Some(match self {
            Token::RParen => Token::LParen,
            Token::RBracket => Token::LBracket,
            Token::RCurly => Token::LCurly,
            _ => return None,
        })
    }

    fn matching(&self) -> Option<Token<'static>> {
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

impl Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Token::Symbol(s) => return write!(f, "symbol `{}`", s),
            Token::Operator(s) => return write!(f, "operator `{}`", s),
            Token::Num(_) => "number",
            Token::LParen => "`(`",
            Token::RParen => "`)`",
            Token::LBracket => "`[`",
            Token::RBracket => "`]`",
            Token::LCurly => "`{`",
            Token::RCurly => "`}`",
            Token::Semi => "`;`",
            Token::Comma => "`,`",
            Token::KwDef => "keyword `def`",
            Token::KwLet => "keyword `let`",
            Token::KwBlock => "keyword `block`",
            Token::KwReturn => "keyword `return`",
            Token::KwIota => "keyword `iota`",
            Token::KwInclude => "keyword `include`",
        })
    }
}

fn is_symbol_start(c: char) -> bool {
    matches!(c, '#' | '_' | 'a'..='z' | 'A'..='Z')
}

fn is_symbol_continue(c: char) -> bool {
    matches!(c, '#' | '_' | 'a'..='z' | 'A'..='Z' | '0'..='9')
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
    strlex.skip_while(|c| c.is_ascii_whitespace());
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
        c if is_symbol_start(c) => {
            strlex.skip_while(is_symbol_continue);
            let token = match &strlex.str()[start..strlex.pos()] {
                "def" => Token::KwDef,
                "let" => Token::KwLet,
                "block" => Token::KwBlock,
                "return" => Token::KwReturn,
                "iota" => Token::KwIota,
                "include" => Token::KwInclude,
                symbol => Token::Symbol(symbol),
            };

            strlex.make_token(start, token)
        }
        c if is_operator(c) => {
            strlex.skip_while(is_operator);
            let operator = &strlex.str()[start..strlex.pos()];
            strlex.make_token(start, Token::Operator(operator))
        }
        '0'..='9' => 'num: {
            strlex.skip_while(|c| c.is_ascii_digit());
            if let Some('.') = strlex.peek() {
                strlex.next();
                strlex.skip_while(|c| c.is_ascii_digit());
            }

            if let Some('e' | 'E') = strlex.peek() {
                strlex.next();
                if let Some('-' | '+') = strlex.peek() {
                    strlex.next();
                }

                if !strlex.peek().is_some_and(|c| c.is_ascii_digit()) {
                    break 'num strlex.make_error(start);
                }

                strlex.skip_while(|c| c.is_ascii_digit());
            }

            let num = &strlex.str()[start..strlex.pos()];
            strlex.make_result(start, num.parse().map(Token::Num).map_err(|_| ParseError))
        }
        _ => {
            strlex.skip_while(|c| !is_token_sep(c));
            strlex.make_error(start)
        }
    })
}

#[derive(Debug)]
struct Lexer<'lex, 'str>(super::Lexer<'lex, 'str, Token<'str>>);

impl<'lex, 'str> SubLexer<'lex, 'str, Token<'str>> for Lexer<'lex, 'str> {
    fn inner(&self) -> &super::Lexer<'lex, 'str, Token<'str>> {
        &self.0
    }

    fn inner_mut(&mut self) -> &mut super::Lexer<'lex, 'str, Token<'str>> {
        &mut self.0
    }

    fn peek_closing(&mut self) -> ParseResult<&Token<'str>> {
        self.0.peek(lex_default)
    }
}

#[must_use]
fn expect_semi(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Span> {
    expect_semi_ext(ctx, lex, false, |_| false)
}

#[must_use]
fn expect_semi_ext(
    ctx: &mut Context,
    lex: &mut Lexer,
    skip_only: bool,
    mut early_return: impl FnMut(&Token) -> bool,
) -> ParseResult<Span> {
    if let Ok(Token::Semi) = lex.peek()? {
        lex.take();
        return Some(Ok(lex.span()));
    }

    if !skip_only {
        ctx.emit_diagnostic(lex.make_diagnostic("expected `;`"));
    }

    loop {
        let Ok(tok) = lex.peek()? else {
            lex.take();
            continue;
        };

        if early_return(tok) {
            return Some(Err(ParseError));
        }

        if let Some(matching) = tok.left_matching() {
            return None;
        } else if let Some(matching) = tok.right_matching() {
            lex.take();
            expect_closing_ext(ctx, lex, &matching, true)?;
        } else {
            lex.take();
        }
    }
}

pub fn parse(ctx: &mut Context, strlex: &mut StrLex) -> Result<File, ParseError> {
    let mut lex = &mut Lexer(super::Lexer::new(strlex));

    let mut items = Ok(Vec::new());

    loop {
        while lex.peek().is_some() {
            let Some(item) = parse_item(ctx, lex) else {
                items = Err(ParseError);
                break;
            };

            items = items.and_then(|mut items| {
                items.push(item?);
                Ok(items)
            });
        }

        let Some(closing) = lex.peek_closing() else {
            break;
        };
        let closing = closing.expect("should not be Err");

        items = Err(ParseError);

        ctx.emit_diagnostic(
            Diagnostic::new(
                Severity::Error,
                format!("unmatched {}", closing),
                lex.span(),
            )
            .with_primary_tag(None),
        );
        lex.take();
    }

    Ok(File { items: items? })
}

fn parse_item(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Item> {
    match lex.peek()? {
        Ok(Token::KwDef) => Some(parse_def(ctx, lex)?.map(|(def, span)| Item {
            kind: ItemKind::Def(def),
            span,
        })),
        _ => {
            ctx.emit_diagnostic(lex.make_diagnostic("expected item"));
            expect_semi_ext(ctx, lex, true, |tok| matches!(tok, Token::KwDef));
            Some(Err(ParseError))
        }
    }
}

fn parse_def(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<(Def, Span)> {
    let span_def = lex.span();
    lex.take();

    let ident = parse_idents(ctx, lex)?.and_then(|mut idents| {
        if idents.len() != 1 {
            ctx.emit_diagnostic(
                Diagnostic::new(
                    Severity::Error,
                    "expected exactly one identifier".to_owned(),
                    idents
                        .iter()
                        .map(|ident| ident.span)
                        .reduce(std::ops::Add::add)
                        .unwrap(),
                )
                .with_primary_tag(None),
            );
            Err(ParseError)
        } else {
            Ok(idents.into_iter().next().unwrap())
        }
    });

    if let Some(Ok(Token::Operator("="))) = lex.peek() {
        lex.take();
    } else {
        ctx.emit_diagnostic(lex.make_diagnostic("expected `=`"));
        expect_semi_ext(ctx, lex, true, |tok| {
            matches!(tok, Token::KwDef | Token::KwInclude)
        })?;
        return Some(Err(ParseError));
    }

    let expr = parse_expr(ctx, lex)?;
    let semi = expect_semi(ctx, lex)?;

    Some((|| {
        Ok((
            Def {
                ident: ident?,
                expr: expr?,
            },
            span_def + semi?,
        ))
    })())
}

fn parse_idents(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Vec<Ident>> {
    let mut idents = Ok(Vec::new());

    loop {
        let ident = match lex.peek() {
            Some(Ok(&Token::Symbol(symbol))) => {
                lex.take();
                Ok(Ident {
                    symbol: symbol.into(),
                    span: lex.span(),
                })
            }
            Some(Ok(tok)) => {
                if matches!(tok, Token::Comma) {
                    ctx.emit_diagnostic(lex.make_diagnostic("expected symbol"));
                    Err(ParseError)
                } else if tok.is_semi_symbolic() {
                    ctx.emit_diagnostic(lex.make_diagnostic("expected symbol"));
                    lex.take();
                    Err(ParseError)
                } else {
                    break;
                }
            }
            _ => break,
        };

        idents = idents.and_then(|mut idents| {
            idents.push(ident?);
            Ok(idents)
        });

        match lex.peek() {
            Some(Ok(Token::Comma)) => {
                lex.take();
            }
            Some(Ok(tok)) if tok.is_semi_symbolic() => {
                ctx.emit_diagnostic(lex.make_diagnostic("expected `,`"));
            }
            _ => break,
        }
    }

    if idents.as_ref().is_ok_and(Vec::is_empty) {
        ctx.emit_diagnostic(lex.make_diagnostic("expected symbol"));
        lex.peek().map(|_| Err(ParseError))
    } else {
        Some(idents)
    }
}

use parse_expr_comma as parse_expr;

fn parse_expr_comma(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Expr> {
    let mut clusters = Ok(Vec::new());

    let span = lex.span();

    loop {
        let elem = match lex.peek() {
            Some(Ok(tok)) if tok.is_expr_begin() => parse_expr_op(ctx, lex)?,
            Some(Ok(Token::Comma)) => {
                ctx.emit_diagnostic(lex.make_diagnostic("expected expression"));
                Err(ParseError)
            }
            _ => break,
        };

        clusters = clusters.and_then(|mut clusters| {
            clusters.push(elem?);
            Ok(clusters)
        });

        match lex.peek() {
            Some(Ok(Token::Comma)) => {
                lex.take();
            }
            Some(Ok(tok)) if tok.is_expr_begin() => {
                ctx.emit_diagnostic(lex.make_diagnostic("expected `,`"));
                clusters = Err(ParseError);
            }
            _ => break,
        }
    }

    Some(clusters.map(|clusters| Expr {
        kind: clusters.into_iter().exactly_one().map_or_else(
            |clusters| ExprKind::Comma(clusters.collect()),
            |cluster| cluster.kind,
        ),
        span,
    }))
}

fn parse_expr_op(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Expr> {
    let mut cluster = Ok(Vec::new());

    let mut span = lex.span();
    let mut prev_expr = false;

    loop {
        let elem = match lex.peek() {
            Some(Ok(&Token::Operator(op))) => {
                prev_expr = false;
                let span_op = lex.span();
                span += span_op;
                lex.take();
                Ok(OpElem::Op(Ident {
                    symbol: op.into(),
                    span: span_op,
                }))
            }
            Some(Ok(Token::LParen)) if prev_expr => parse_call(ctx, lex)?.map(OpElem::Call),
            Some(Ok(tok)) if tok.is_expr_begin() => {
                if let Ok(t) = parse_expr_term(ctx, lex)? {
                    span += t.span;
                    Ok(OpElem::Term(t))
                } else {
                    Err(ParseError)
                }
            }
            _ => break,
        };
        prev_expr = true;

        cluster = cluster.and_then(|mut cluster| {
            cluster.push(elem?);
            Ok(cluster)
        });
    }

    match cluster {
        Ok(cluster) => {
            if cluster.is_empty() || cluster.iter().all(|elem| matches!(elem, OpElem::Op(_))) {
                ctx.emit_diagnostic(lex.make_diagnostic("expected expression"));
                lex.peek().map(|_| Err(ParseError))
            } else {
                Some(Ok(Expr {
                    kind: ExprKind::OpCluster(cluster),
                    span,
                }))
            }
        }
        Err(ParseError) => Some(Err(ParseError)),
    }
}

fn parse_call(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Call> {
    let span = lex.span();
    lex.take();

    let (arity, expr_after) = if let Some(Ok(Token::Operator("->"))) = lex.peek() {
        let span_arrow = lex.span();
        lex.take();
        let arity = match lex.peek() {
            Some(Ok(&Token::Num(arity))) => {
                lex.take();
                Ok(Some(CallArity {
                    arity: arity as u32,
                    span: span_arrow + lex.span(),
                }))
            }
            _ => {
                ctx.emit_diagnostic(lex.make_diagnostic("expected number"));
                munch_groups_until(ctx, lex, |tok| matches!(tok, Token::Comma));
                Err(ParseError)
            }
        };

        if let Some(Ok(Token::Comma)) = lex.peek() {
            lex.take();
            (arity, true)
        } else {
            (arity, false)
        }
    } else {
        (Ok(None), true)
    };

    let arg = if lex.peek().is_none() || !expr_after {
        Some(Ok(null_expr(ctx, lex)))
    } else {
        parse_expr(ctx, lex)
    };

    expect_closing(ctx, lex, &Token::RParen)
        .zip(arg)
        .map(|(closing, arg)| {
            Ok(Call {
                arity: arity?,
                arg: Box::new(arg?),
                span: span + closing?,
            })
        })
}

fn null_expr(ctx: &mut Context, lex: &mut Lexer) -> Expr {
    Expr {
        kind: ExprKind::Comma(Vec::new()),
        span: (lex.pos()..lex.pos()).into(),
    }
}

fn parse_expr_term(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Expr> {
    match lex.peek() {
        Some(Ok(&Token::Symbol(symbol))) => {
            lex.take();
            Some(Ok(Expr {
                kind: ExprKind::Var(Ident {
                    symbol: symbol.into(),
                    span: lex.span(),
                }),
                span: lex.span(),
            }))
        }
        Some(Ok(&Token::Num(n))) => {
            lex.take();
            Some(Ok(Expr {
                kind: ExprKind::Num(n),
                span: lex.span(),
            }))
        }
        Some(Ok(Token::LParen)) => {
            lex.take();
            let expr = parse_expr(ctx, lex);
            expect_closing(ctx, lex, &Token::RParen)
                .zip(expr)
                .map(|(closing, iota)| closing.and(iota))
        }
        // Some(Ok(Token::LBracket)) => // list expr,
        Some(Ok(Token::LCurly | Token::KwBlock)) => parse_block(ctx, lex).map(|block| {
            block.map(|block| {
                let span = block.span;
                Expr {
                    kind: ExprKind::Block(Box::new(block)),
                    span,
                }
            })
        }),
        Some(Ok(Token::KwIota)) => {
            lex.take();
            match lex.peek() {
                Some(Ok(Token::LParen)) => {
                    let span = lex.span();
                    lex.take();
                    crate::parse::iota::parse(
                        ctx,
                        lex.inner_mut().inner_mut(),
                        &crate::parse::iota::Token::RParen,
                    )
                    .map(|iota| {
                        iota.map(|iota| Expr {
                            kind: ExprKind::Iota(iota),
                            span: (span.start..lex.pos()).into(),
                        })
                    })
                }
                tok => {
                    let ret = tok.map(|_| Err(ParseError));
                    ctx.emit_diagnostic(lex.make_diagnostic("expected `(`"));
                    ret
                }
            }
        }
        tok => {
            ctx.emit_diagnostic(lex.make_diagnostic("expected expression"));
            munch_groups_until(ctx, lex, |tok| matches!(tok, Token::Semi | Token::Comma))?;
            Some(Err(ParseError))
        }
    }
}

fn parse_block(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Block> {
    lex.peek();
    let span = lex.span();

    let args = match lex.peek() {
        Some(Ok(Token::KwBlock)) => {
            lex.take();
            match lex.peek() {
                Some(Ok(Token::LCurly)) => Ok(Vec::new()),
                Some(Ok(Token::LParen)) => {
                    lex.take();
                    let idents = parse_idents(ctx, lex);
                    expect_closing(ctx, lex, &Token::RParen)
                        .map(|closing| closing.and(idents.unwrap_or(Err(ParseError))))?
                }
                tok => {
                    let ret = tok.map(|_| Err(ParseError));
                    ctx.emit_diagnostic(lex.make_diagnostic("expected `(` or `{`"));
                    return ret;
                }
            }
        }
        _ => Ok(Vec::new()),
    };

    match lex.peek() {
        Some(Ok(Token::LCurly)) => {
            lex.take();
        }
        tok => {
            let ret = tok.map(|_| Err(ParseError));
            ctx.emit_diagnostic(lex.make_diagnostic("expected `{`"));
            return ret;
        }
    }

    let inner = parse_stmts(ctx, lex);

    expect_closing(ctx, lex, &Token::RCurly)
        .zip(inner)
        .map(|(closing, inner)| {
            let (stmts, ret) = inner?;

            Ok(Block {
                args: args?,
                stmts,
                ret,
                span: span + closing?,
            })
        })
}

fn parse_stmts(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<(Vec<Stmt>, Expr)> {
    let mut stmts = Ok(Vec::new());

    let ret_expr = loop {
        let stmt = match lex.peek() {
            Some(Ok(Token::KwReturn)) => {
                lex.take();
                let expr = parse_expr(ctx, lex)?;
                let semi = expect_semi(ctx, lex)?;

                if lex.peek().is_some() {
                    ctx.emit_diagnostic(
                        lex.make_diagnostic("expected return statement as last statement"),
                    );
                    break Err(ParseError);
                } else {
                    break semi.and(expr);
                }
            }
            Some(Ok(Token::KwLet)) => {
                let span_let = lex.span();
                lex.take();
                let idents = parse_idents(ctx, lex)?;

                if let Some(Ok(Token::Operator("="))) = lex.peek() {
                    lex.take();

                    let expr = parse_expr(ctx, lex)?;
                    let span_semi = expect_semi(ctx, lex)?;

                    (|| {
                        Ok(Stmt {
                            kind: StmtKind::Let(LetStmt {
                                bindings: idents?,
                                arg: Box::new(expr?),
                            }),
                            span: span_let + span_semi?,
                        })
                    })()
                } else {
                    ctx.emit_diagnostic(lex.make_diagnostic("expected `=`"));
                    expect_semi_ext(ctx, lex, true, |tok| {
                        matches!(tok, Token::KwLet | Token::KwDef | Token::KwInclude)
                    })?;
                    Err(ParseError)
                }
            }
            Some(Ok(Token::KwDef)) => parse_def(ctx, lex)?.map(|(def, span)| Stmt {
                kind: StmtKind::Def(def),
                span,
            }),
            None => {
                break Ok(null_expr(ctx, lex));
            }
            _ => {
                let expr = parse_expr(ctx, lex)?;
                let semi = expect_semi(ctx, lex)?;

                (|| {
                    let expr = expr?;
                    let span = expr.span;
                    Ok(Stmt {
                        kind: StmtKind::Expr(expr),
                        span: span + semi?,
                    })
                })()
            }
        };

        stmts = stmts.and_then(|mut stmts| {
            stmts.push(stmt?);
            Ok(stmts)
        })
    };

    Some(stmts.and_then(|stmts| Ok((stmts, ret_expr?))))
}

#[cfg(test)]
mod tests {
    use crate::{
        core::Context,
        parse::{Lexer, StrLex, SubLexer, SubLexerExt},
    };

    #[test]
    #[ignore]
    fn test_parse() {
        let mut ctx = Context::new();

        let str = "
            def abcd = block (arg1, arg2, ) {
                (1 + 2) (-> 2);
                (1 + 2) (-> 2, 1 + 2);
                (1 + 2) (1,);
                return arg1;
            };
        ";

        let mut strlex = StrLex::new(str);

        // let mut lex = super::Lexer(Lexer::new(&mut strlex));

        // while lex.peek_closing().is_some() {
        //     dbg!(lex.take());
        // }

        let parse = super::parse(&mut ctx, &mut strlex);

        dbg!(ctx);
        dbg!(parse);
    }

    #[test]
    #[ignore]
    fn _test_parse_idents() {
        let mut ctx = Context::new();

        let str = "abc, def, g_1";
        let mut strlex = StrLex::new(str);
        let mut lex = super::Lexer(Lexer::new(&mut strlex));

        // loop {
        //     if lex.peek().is_none() {
        //         break;
        //     }
        //     dbg!(lex.peek());
        //     lex.take();
        // }

        let parse = super::parse_idents(&mut ctx, &mut lex);

        dbg!(ctx);
        dbg!(parse);
    }
}
