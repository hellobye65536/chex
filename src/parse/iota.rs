use std::{borrow::Cow, fmt::Display, mem, sync::OnceLock};

use bitvec::vec::BitVec;
use fst::raw::Fst;
use itertools::Itertools;

use crate::{
    diagnostics::{Diagnostic, Severity, Tag},
    iota::{bytes_as_angles, Angle, ComplexPattern, Direction, Iota, Pattern, SimplePattern},
    parse::{LexResult, ParseError, StrLex},
    pattern, Context, Span,
};

#[derive(Debug, Clone)]
pub enum Token<'a> {
    Symbol(&'a str),
    Num(f64),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LCurly,
    RCurly,
    Colon,
    Sep,
}

impl<'a> Token<'a> {
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

pub fn token_as_str<E>(token: Result<&Token, E>) -> &'static str {
    match token {
        Ok(Token::Symbol(_)) => "symbol",
        Ok(Token::Num(_)) => "number",
        Ok(Token::LParen) => "`(`",
        Ok(Token::RParen) => "`)`",
        Ok(Token::LBracket) => "`[`",
        Ok(Token::RBracket) => "`]`",
        Ok(Token::LCurly) => "`{`",
        Ok(Token::RCurly) => "`}`",
        Ok(Token::Colon) => "`:`",
        Ok(Token::Sep) => "`,`",
        Err(_) => "invalid token",
    }
}

fn is_token_sep(c: char) -> bool {
    c.is_ascii_whitespace() || ['(', ')', '[', ']', '{', '}', ':', ','].contains(&c)
}

fn munch_error_token<T>(lex: &mut StrLex<'_>, start: usize) -> Option<LexResult<T>> {
    lex.skip_while(|c| !is_token_sep(c));
    Some(lex.make_error(start))
}

fn lex_default<'str>(
    strlex: &mut StrLex<'str>,
    symbol_only: bool,
) -> Option<LexResult<Token<'str>>> {
    strlex.skip_while(|c| c.is_ascii_whitespace() && c != '\n');
    let start = strlex.pos();

    Some(match strlex.next()? {
        '(' => strlex.make_token(start, Token::LParen),
        ')' => strlex.make_token(start, Token::RParen),
        '[' => strlex.make_token(start, Token::LBracket),
        ']' => strlex.make_token(start, Token::RBracket),
        '{' => strlex.make_token(start, Token::LCurly),
        '}' => strlex.make_token(start, Token::RCurly),
        ':' => strlex.make_token(start, Token::Colon),
        c @ (',' | '\n') => {
            let mut seen_comma = c == ',';
            let mut start = start;
            let mut end = strlex.pos();
            loop {
                match strlex.peek() {
                    Some('\n') => {
                        strlex.next();
                    }
                    Some(',') if !seen_comma => {
                        seen_comma = true;
                        start = strlex.pos();
                        strlex.next();
                        end = strlex.pos();
                    }
                    Some(c) if c.is_ascii_whitespace() => {
                        strlex.next();
                    }
                    _ => break,
                }
            }

            LexResult::new_token(start..end, Token::Sep)
        }
        c @ ('0'..='9' | '.' | '-' | '+' | 'a'..='z' | 'A'..='Z') => {
            let numeric = match c {
                '0'..='9' | '.' => true,
                '-' | '+' => matches!(strlex.peek(), Some('0'..='9' | '.')),
                'a'..='z' | 'A'..='Z' => false,
                _ => unreachable!(),
            };

            if !symbol_only && numeric {
                strlex.skip_while(|c| !is_token_sep(c));

                match strlex.str()[start..strlex.pos()].parse() {
                    Ok(v) => strlex.make_token(start, Token::Num(v)),
                    Err(e) => strlex.make_error(start),
                }
            } else {
                strlex.skip_while(|c| !is_token_sep(c));

                strlex.make_token(start, Token::Symbol(&strlex.str()[start..strlex.pos()]))
            }
        }
        _ => return munch_error_token(strlex, start),
    })
}

fn parse_direction(str: &str) -> Result<Direction, ParseError> {
    macro_rules! match_dir {
        ($($s:expr => $t:ident),* $(,)?) => {
            $(if str.eq_ignore_ascii_case($s) {
                Ok(Direction::$t)
            } else)* {
                Err(ParseError)
            }
        };
    }

    match_dir!(
        "north_east" => NorthEast,
        "east" => East,
        "south_east" => SouthEast,
        "south_west" => SouthWest,
        "west" => West,
        "north_west" => NorthWest,
    )
}

fn pattern_parse_table() -> &'static Fst<&'static [u8]> {
    static TABLE: OnceLock<Fst<&'static [u8]>> = OnceLock::new();
    static TABLE_BYTES: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/pattern_parse_table"));
    TABLE.get_or_init(|| Fst::new(TABLE_BYTES).unwrap())
}

#[derive(Debug)]
struct Lexer<'lex, 'str>(super::Lexer<'lex, 'str, Token<'str>>);

type ParseResult<T> = Option<Result<T, ParseError>>;

impl<'lex, 'str> Lexer<'lex, 'str> {
    pub fn peek(&mut self) -> Option<Result<&Token<'str>, ParseError>> {
        self.0.peek(|strlex| lex_default(strlex, false))
    }

    pub fn next(&mut self) -> Option<Result<Token<'str>, ParseError>> {
        self.0.next(|strlex| lex_default(strlex, false))
    }

    pub fn peek_symbol(&mut self) -> Option<Result<&Token<'str>, ParseError>> {
        self.0.peek(|strlex| lex_default(strlex, true))
    }

    pub fn next_symbol(&mut self) -> Option<Result<Token<'str>, ParseError>> {
        self.0.next(|strlex| lex_default(strlex, true))
    }

    pub fn span(&self) -> Span {
        self.0.span()
    }

    pub fn make_syntax_diagnostic(&self, expected: impl Display + Clone) -> Diagnostic {
        let peek = &self.0.peek.as_ref().unwrap().token;

        Diagnostic::new(
            Severity::Error,
            format_args!("{}, got {}", expected.clone(), token_as_str(peek.as_ref())),
            self.span(),
        )
        .tag(Tag::new(Severity::Error, expected, self.span()))
    }
}

fn expect(ctx: &mut Context, lex: &mut Lexer, expect: &Token) -> ParseResult<()> {
    if let Ok(tok) = lex.peek()? {
        if mem::discriminant(expect) == mem::discriminant(tok) {
            lex.next();
            return Some(Ok(()));
        }
    }

    ctx.emit_diagnostic(
        lex.make_syntax_diagnostic(format_args!("expected {}", token_as_str::<()>(Ok(expect)))),
    );

    Some(Err(ParseError))
}

fn munch_group(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<()> {
    if let Ok(tok) = lex.next()? {
        if let Some(matching) = tok.right_matching() {
            return munch_rest_of_group(ctx, lex, matching);
        } else if let Some(matching) = tok.left_matching() {
            ctx.emit_diagnostic(
                Diagnostic::new(Severity::Error, "unmatched delimiters", lex.span()).tag(Tag::new(
                    Severity::Error,
                    "unmatched delimiters",
                    lex.span(),
                )),
            );
            return Some(Err(ParseError));
        }
    }

    Some(Ok(()))
}

fn munch_rest_of_group(ctx: &mut Context, lex: &mut Lexer, right: Token) -> ParseResult<()> {
    debug_assert!(right.left_matching().is_some());
    loop {
        match lex.peek()? {
            Ok(tok) => {
                if mem::discriminant(tok) == mem::discriminant(&right) {
                    lex.next();
                    return Some(Ok(()));
                } else if let Some(matching) = tok.left_matching() {
                    ctx.emit_diagnostic(lex.make_syntax_diagnostic(format_args!(
                        "expected {} as closing",
                        token_as_str::<()>(Ok(&right)),
                    )));
                    return Some(Err(ParseError));
                } else if let Some(matching) = tok.right_matching() {
                    lex.next();
                    munch_rest_of_group(ctx, lex, matching)?;
                } else {
                    lex.next();
                }
            }
            Err(ParseError) => {
                lex.next();
            }
        }
    }
}

pub fn parse(ctx: &mut Context, strlex: &mut StrLex) -> ParseResult<Iota> {
    let mut lex = Lexer(super::Lexer::new(strlex));

    let iota = parse_iota(ctx, &mut lex)?;

    if let Ok(Token::RParen) = lex.peek()? {
        lex.next();
        Some(iota)
    } else {
        ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected `)` as end of iota expression"));

        munch_rest_of_group(ctx, &mut lex, Token::RParen)?;
        Some(Err(ParseError))
    }
}

fn parse_iota(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    match lex.peek()? {
        Ok(&Token::Symbol(_)) => parse_pattern(ctx, lex),
        Ok(&Token::Num(n)) => {
            lex.next();
            Some(Ok(Iota::Num(n)))
        }
        Ok(Token::LParen) => {
            lex.next();
            parse_vec(ctx, lex)
        }
        Ok(left @ (Token::LCurly | Token::LBracket)) => {
            let right = left.right_matching().unwrap();
            lex.next();
            parse_list(ctx, lex, right)
        }
        _ => {
            ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected iota expression"));

            munch_group(ctx, lex)?;
            Some(Err(ParseError))
        }
    }
}

fn parse_list(ctx: &mut Context, lex: &mut Lexer, right: Token) -> ParseResult<Iota> {
    let mut iotas = Ok(Vec::new());

    loop {
        if let Ok(maybe_right) = lex.peek()? {
            if mem::discriminant(&right) == mem::discriminant(maybe_right) {
                lex.next();
                break;
            }
        }

        let iota = parse_iota(ctx, lex)?;

        iotas = iotas.and_then(|mut iotas| {
            iotas.push(iota?);
            Ok(iotas)
        });

        match lex.peek()? {
            Ok(maybe_right) if mem::discriminant(&right) == mem::discriminant(maybe_right) => {
                lex.next();
                break;
            }
            Ok(Token::Sep) => {
                lex.next();
            }
            _ => {
                ctx.emit_diagnostic(lex.make_syntax_diagnostic(format_args!(
                    "expected `,` or {}",
                    token_as_str::<()>(Ok(&right)),
                )));
                munch_group(ctx, lex)?;
            }
        }
    }

    Some(iotas.map(Iota::List))
}

fn parse_vec(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    fn parse_num(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<f64> {
        Some(match lex.peek()? {
            Ok(&Token::Num(v)) => {
                lex.next();
                Ok(v)
            }
            Ok(Token::Sep) => Err(ParseError),
            _ => {
                ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected number"));

                munch_group(ctx, lex)?;
                Err(ParseError)
            }
        })
    }

    let x = parse_num(ctx, lex)?;
    let sep0 = expect(ctx, lex, &Token::Sep)?;
    let y = parse_num(ctx, lex)?;
    let sep1 = expect(ctx, lex, &Token::Sep)?;
    let z = parse_num(ctx, lex)?;

    if let Ok(Token::Sep) = lex.peek()? {
        lex.next();
    }

    if let Ok(Token::RParen) = lex.peek()? {
        lex.next();
    } else {
        ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected `)` as end of vector expression"));

        munch_rest_of_group(ctx, lex, Token::RParen)?;
        return Some(Err(ParseError));
    }

    Some((|| {
        sep0?;
        sep1?;

        Ok(Iota::Vec(x?, y?, z?))
    })())
}

#[derive(Debug, Clone)]
struct FstState<'fst> {
    node: Option<fst::raw::Node<'fst>>,
    out: fst::raw::Output,
}

impl<'fst> FstState<'fst> {
    pub fn new(fst: &'fst Fst<impl AsRef<[u8]>>) -> Self {
        Self {
            node: Some(fst.root()),
            out: fst::raw::Output::zero(),
        }
    }

    pub fn step(&mut self, fst: &'fst Fst<impl AsRef<[u8]>>, b: u8) {
        if let Some(node) = self.node.take() {
            if let Some(i) = node.find_input(b) {
                let transition = node.transition(i);
                self.out = self.out.cat(transition.out);
                self.node = Some(fst.node(transition.addr));
            }
        }
    }

    pub fn steps(&mut self, fst: &'fst Fst<impl AsRef<[u8]>>, bs: impl IntoIterator<Item = u8>) {
        bs.into_iter().for_each(|b| self.step(fst, b))
    }

    pub fn node(&self) -> Option<fst::raw::Node<'fst>> {
        self.node
    }

    pub fn value(&self) -> Option<u64> {
        let node = self.node.as_ref()?;
        node.is_final().then_some(())?;
        Some(self.out.cat(node.final_output()).value())
    }
}

fn parse_pattern(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    let Some(Ok(Token::Symbol(pat))) = lex.peek() else {
        panic!("bad lex state in parse_pattern");
    };

    let fst = pattern_parse_table();
    let mut fst_state = FstState::new(fst);

    update_fst_state(fst, &mut fst_state, pat);
    let mut span = lex.span();
    lex.next();

    while let Some(Ok(Token::Symbol(pat))) = lex.0.peek(|strlex| lex_default(strlex, true)) {
        update_fst_state(fst, &mut fst_state, pat);
        span += lex.span();
        lex.next();
    }

    match fst_state.value().map(u64::wrapping_neg) {
        Some(1) => return parse_hexpattern(ctx, lex),
        Some(2) => return parse_numerical_reflection(ctx, lex),
        Some(3) => return parse_bookkeepers_gambit(ctx, lex),
        Some(4) => return Some(Ok(Iota::Null)),
        _ => {}
    }

    loop {
        match lex.peek() {
            Some(Ok(Token::Colon)) => update_fst_state(fst, &mut fst_state, ":"),
            Some(Ok(Token::Symbol(pat))) => update_fst_state(fst, &mut fst_state, pat),
            _ => break,
        }
        span += lex.span();
        lex.next();
    }

    if let Some(val) = fst_state.value() {
        let pat = val.try_into().expect("parse table has invalid pattern id");
        Some(Ok(Iota::Pattern(Pattern::Simple(pat))))
    } else {
        ctx.emit_diagnostic(
            Diagnostic::new(Severity::Error, "expected valid pattern", span).tag(Tag::new(
                Severity::Error,
                "expected valid pattern",
                span,
            )),
        );
        Some(Err(ParseError))
    }
}

fn update_fst_state<'fst>(
    fst: &'fst Fst<impl AsRef<[u8]>>,
    fst_state: &mut FstState<'fst>,
    pat: &str,
) {
    for b in pat.bytes() {
        fst_state.step(fst, b.to_ascii_lowercase());
    }
}

fn parse_hexpattern(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    if expect(ctx, lex, &Token::LParen)?.is_err() {
        return Some(Err(ParseError));
    }

    let direction = match lex.0.peek(|strlex| lex_default(strlex, true))? {
        Ok(Token::Symbol(dir)) => {
            let direction = parse_direction(dir).inspect_err(|_| {
                ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected valid direction"))
            });
            lex.next();
            direction
        }
        tok => {
            let is_closing = tok.is_ok_and(|tok| tok.left_matching().is_some());
            let mismatched_closing = !matches!(tok, Ok(Token::RParen));

            ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected direction and angles"));
            if is_closing {
                if mismatched_closing {
                    ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected `)` as closing"));
                } else {
                    lex.next();
                }
                return Some(Err(ParseError));
            }
            munch_group(ctx, lex)?;
            Err(ParseError)
        }
    };

    let angles = match lex.0.peek(|strlex| lex_default(strlex, true))? {
        Ok(Token::Symbol(angles)) => {
            let angles = bytes_as_angles(angles.as_bytes())
                .ok_or(ParseError)
                .inspect_err(|_| {
                    ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected pattern angles"))
                });
            lex.next();
            angles
        }
        Ok(Token::RParen) => {
            ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected pattern angles"));
            lex.next();
            return Some(Err(ParseError));
        }
        tok => {
            let is_closing = tok.is_ok_and(|tok| tok.left_matching().is_some());
            let mismatched_closing = !matches!(tok, Ok(Token::RParen));

            ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected pattern angles"));
            if is_closing {
                if mismatched_closing {
                    ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected `)` as closing"));
                } else {
                    lex.next();
                }
                return Some(Err(ParseError));
            }
            munch_group(ctx, lex)?;
            Err(ParseError)
        }
    };

    match lex.peek()? {
        Ok(Token::RParen) => {
            lex.next();
        }
        tok => {
            let is_closing = tok.is_ok_and(|tok| tok.left_matching().is_some());
            ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected `)` as closing"));
            if !is_closing {
                munch_rest_of_group(ctx, lex, Token::RParen);
            }
            return Some(Err(ParseError));
        }
    }

    Some((|| {
        Ok(Iota::Pattern(Pattern::Complex(ComplexPattern::Other {
            dir: direction?,
            angles: Cow::Owned(angles?.to_owned()),
        })))
    })())
}

fn parse_numerical_reflection(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    if expect(ctx, lex, &Token::Colon)?.is_err() {
        return Some(Err(ParseError));
    }

    Some(match lex.peek()? {
        Ok(&Token::Num(n)) => {
            lex.next();
            Ok(Iota::Pattern(pattern!(NumericalReflection: n)))
        }
        tok => {
            let do_skip = matches!(tok, Ok(Token::Symbol(_)) | Err(ParseError));
            ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected number"));
            if do_skip {
                lex.next();
            }
            Err(ParseError)
        }
    })
}

fn parse_bookkeepers_gambit(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    if expect(ctx, lex, &Token::Colon)?.is_err() {
        return Some(Err(ParseError));
    }

    Some(match lex.0.peek(|strlex| lex_default(strlex, true))? {
        Ok(Token::Symbol(n)) => n
            .bytes()
            .map(|c| match c {
                b'-' => Ok(true),
                b'v' => Ok(false),
                _ => Err(ParseError),
            })
            .collect::<Result<BitVec, ParseError>>()
            .map(|keep| {
                Iota::Pattern(Pattern::Complex(ComplexPattern::BookkeepersGambit {
                    keep: Cow::Owned(keep),
                }))
            })
            .inspect_err(|_| {
                ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected bookkeepers spec"))
            }),
        tok => {
            let do_skip = tok.is_err();
            ctx.emit_diagnostic(lex.make_syntax_diagnostic("expected bookkeepers spec"));
            lex.next();
            Err(ParseError)
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        parse::{LexResult, StrLex},
        Context,
    };

    use super::{lex_default, parse_iota, pattern_parse_table, Lexer, Token};

    #[test]
    #[ignore]
    fn print_table() {
        println!("{:#?}", fst::Map::new(pattern_parse_table().as_inner()));
    }

    #[test]
    #[ignore]
    fn test_lex_default() {
        let str = "pattern's pattern : a  , pattern ,\n pattern , 0.123 1e5 _err()";
        let mut lex = StrLex::new(str);

        while let Some(tok) = lex_default(&mut lex, false) {
            println!("{:?}", tok);
        }

        // let LexResult { span, token } = lex_default(&mut lex).unwrap();
        // assert_eq!(span, (0..17).into());
        // assert!(matches!(token, Ok(Token::PatternPart("pattern's pattern"))));
    }

    #[test]
    #[ignore]
    fn test_parse() {
        let mut ctx = Context::new();

        let str = " [Explosion , 1.2, (1, 2, 3,), hexpattern (north_east qqq), numerical reflection: 5] )";
        let mut strlex = StrLex::new(str);

        let parse = super::parse(&mut ctx, &mut strlex);

        dbg!(ctx);
        dbg!(parse);
    }
}
