use std::{borrow::Cow, fmt::Display, mem, str::FromStr, sync::OnceLock};

use bitvec::vec::BitVec;
use fst::raw::Fst;
use itertools::Itertools;
use tap::TapOptional;

use crate::{
    diagnostics::{Diagnostic, Severity, Tag},
    iota::{bytes_as_angles, Angle, ComplexPattern, Direction, Iota, Pattern, SimplePattern},
    parse::{LexResult, ParseError, ParseResult, StrLex},
    pattern, Context, Span,
};

#[derive(Debug, Clone)]
pub enum Token<'a> {
    Symbol(&'a str),
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
    pub fn display_type(&self) -> &'static str {
        match self {
            Token::Symbol(_) => "symbol",
            Token::LParen => "`(`",
            Token::RParen => "`)`",
            Token::LBracket => "`[`",
            Token::RBracket => "`]`",
            Token::LCurly => "`{`",
            Token::RCurly => "`}`",
            Token::Colon => "`:`",
            Token::Sep => "`,`",
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

fn is_token_sep(c: char) -> bool {
    c.is_ascii_whitespace() || ['(', ')', '[', ']', '{', '}', ';', ':', ','].contains(&c)
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
            strlex.skip_while(|c| !is_token_sep(c));
            strlex.make_token(start, Token::Symbol(&strlex.str()[start..strlex.pos()]))
        }
        _ => {
            strlex.skip_while(|c| !is_token_sep(c));
            strlex.make_error(start)
        }
    })
}

fn is_symbol_numeric(str: &str) -> Option<f64> {
    f64::from_str(str).ok()
}

fn parse_direction(str: &str) -> Option<Direction> {
    macro_rules! match_dir {
        ($($str:expr => $dir:ident),* $(,)?) => {
            $(if str.eq_ignore_ascii_case($str) {
                Some(Direction::$dir)
            } else)* {
                None
            }
        };
    }

    match_dir! {
        "north_east" => NorthEast,
        "east" => East,
        "south_east" => SouthEast,
        "south_west" => SouthWest,
        "west" => West,
        "north_west" => NorthWest,
    }
}

fn pattern_parse_table() -> &'static Fst<&'static [u8]> {
    static TABLE: OnceLock<Fst<&'static [u8]>> = OnceLock::new();
    static TABLE_BYTES: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/pattern_parse_table"));
    TABLE.get_or_init(|| Fst::new(TABLE_BYTES).unwrap())
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

pub fn parse(ctx: &mut Context, strlex: &mut StrLex, closing: &Token) -> ParseResult<Iota> {
    let mut lex = Lexer(super::Lexer::new(strlex));

    let iota = parse_iota(ctx, &mut lex);

    expect_closing(ctx, &mut lex, closing).map(|v| v.and_then(|_| iota.unwrap_or(Err(ParseError))))
}

fn parse_iota(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    match lex.peek() {
        Some(Ok(&Token::Symbol(pat))) => {
            lex.take();
            if let Some(n) = is_symbol_numeric(pat) {
                Some(Ok(Iota::Num(n)))
            } else {
                parse_pattern(ctx, lex, pat)
            }
        }
        Some(Ok(Token::LParen)) => {
            lex.take();
            parse_vec(ctx, lex)
        }
        Some(Ok(left @ (Token::LCurly | Token::LBracket))) => {
            let right = left.right_matching().unwrap();
            lex.take();
            parse_list(ctx, lex, &right)
        }
        tok => {
            let ret = tok.map(|_| Err(ParseError));

            ctx.emit_diagnostic(lex.make_diagnostic("expected iota expression"));

            while !matches!(lex.peek(), Some(Ok(Token::Sep))) {
                munch_group(ctx, lex)?;
            }

            ret
        }
    }
}

fn parse_list(ctx: &mut Context, lex: &mut Lexer, closing: &Token) -> ParseResult<Iota> {
    let mut iotas = Ok(Vec::new());

    loop {
        if lex.peek().is_none() {
            break;
        }

        let Some(iota) = parse_iota(ctx, lex) else {
            return expect_closing(ctx, lex, closing).map(|_| Err(ParseError));
        };

        iotas = iotas.and_then(|mut iotas| {
            iotas.push(iota?);
            Ok(iotas)
        });

        match lex.peek() {
            Some(Ok(Token::Sep)) => {
                lex.take();
            }
            Some(_) => {
                ctx.emit_diagnostic(
                    lex.make_diagnostic(format_args!("expected `,` or {}", closing.display_type())),
                );
                while !matches!(lex.peek(), Some(Ok(Token::Sep))) {
                    munch_group(ctx, lex)?;
                }
            }
            None => break,
        }
    }

    expect_closing(ctx, lex, closing).map(|closing| closing.and(iotas.map(Iota::List)))
}

fn parse_vec(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    fn parse_num(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<f64> {
        if let Ok(Token::Symbol(str)) = lex.peek()? {
            if let Some(n) = is_symbol_numeric(str) {
                lex.take();
                return Some(Ok(n));
            }
        }

        ctx.emit_diagnostic(lex.make_diagnostic("expected number"));

        while !matches!(lex.peek(), Some(Ok(Token::Sep))) {
            munch_group(ctx, lex)?;
        }
        Some(Err(ParseError))
    }

    fn expect_sep(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<()> {
        Some(if let Ok(Token::Sep) = lex.peek()? {
            lex.take();
            Ok(())
        } else {
            ctx.emit_diagnostic(lex.make_diagnostic("expected `,`"));

            while !matches!(lex.peek(), Some(Ok(Token::Sep))) {
                munch_group(ctx, lex)?;
            }
            Err(ParseError)
        })
    }

    let iota = (|| {
        let x = parse_num(ctx, lex)?;
        let sep0 = expect_sep(ctx, lex)?;
        let y = parse_num(ctx, lex)?;
        let sep1 = expect_sep(ctx, lex)?;
        let z = parse_num(ctx, lex)?;

        if let Some(Ok(Token::Sep)) = lex.peek() {
            lex.take();
        }

        Some((|| {
            sep0?;
            sep1?;

            Ok::<_, ParseError>(Iota::Vec(x?, y?, z?))
        })())
    })();

    if iota.is_none() {
        ctx.emit_diagnostic(lex.make_diagnostic("expected rest of vector expression"));
    }

    expect_closing(ctx, lex, &Token::RParen)
        .zip(iota)
        .map(|(closing, iota)| closing.and(iota))
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

fn parse_pattern(ctx: &mut Context, lex: &mut Lexer, pat: &str) -> ParseResult<Iota> {
    let fst = pattern_parse_table();
    let mut fst_state = FstState::new(fst);

    update_fst_state(fst, &mut fst_state, pat);
    let mut span = lex.span();
    lex.take();

    while let Some(Ok(Token::Symbol(pat))) = lex.peek() {
        update_fst_state(fst, &mut fst_state, pat);
        span += lex.span();
        lex.take();
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
        lex.take();
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
    if !matches!(lex.peek(), Some(Ok(Token::LParen))) {
        ctx.emit_diagnostic(lex.make_diagnostic("expected `(`"));
        return Some(Err(ParseError));
    }
    lex.take();

    let iota = (|| {
        let direction = match lex.peek()? {
            Ok(&Token::Symbol(dir)) => {
                lex.take();
                parse_direction(dir)
                    .tap_none(|| {
                        ctx.emit_diagnostic(lex.make_diagnostic("expected valid direction"))
                    })
                    .ok_or(ParseError)
            }
            _ => {
                ctx.emit_diagnostic(lex.make_diagnostic("expected direction and angles"));
                munch_group(ctx, lex)?;
                Err(ParseError)
            }
        };

        let angles = match lex.peek()? {
            Ok(&Token::Symbol(angles)) => {
                lex.take();
                bytes_as_angles(angles.as_bytes())
                    .tap_none(|| ctx.emit_diagnostic(lex.make_diagnostic("expected angles")))
                    .ok_or(ParseError)
            }
            _ => {
                ctx.emit_diagnostic(lex.make_diagnostic("expected angles"));
                munch_group(ctx, lex)?;
                Err(ParseError)
            }
        };

        Some((|| {
            Ok(Iota::Pattern(pattern!(HexPattern(
                direction?,
                Cow::Owned(angles?.to_owned())
            ))))
        })())
    })();

    if iota.is_none() {
        ctx.emit_diagnostic(lex.make_diagnostic("expected rest of hexpattern expression"));
    }

    expect_closing(ctx, lex, &Token::RParen)
        .zip(iota)
        .map(|(closing, iota)| closing.and(iota))
}

fn parse_numerical_reflection(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    if !matches!(lex.peek(), Some(Ok(Token::Colon))) {
        ctx.emit_diagnostic(lex.make_diagnostic("expected `:`"));
        return Some(Err(ParseError));
    }
    lex.take();

    let tok = lex.peek();

    if let Some(Ok(&Token::Symbol(str))) = tok {
        if let Some(n) = is_symbol_numeric(str) {
            lex.take();
            return Some(Ok(Iota::Pattern(pattern!(NumericalReflection: n))));
        }
    }

    let ret = tok.map(|_| Err(ParseError));
    let do_skip = matches!(tok, Some(Ok(Token::Symbol(_)) | Err(ParseError)));
    ctx.emit_diagnostic(lex.make_diagnostic("expected number"));
    if do_skip {
        lex.take();
    }
    ret
}

fn parse_bookkeepers_gambit(ctx: &mut Context, lex: &mut Lexer) -> ParseResult<Iota> {
    if !matches!(lex.peek(), Some(Ok(Token::Colon))) {
        ctx.emit_diagnostic(lex.make_diagnostic("expected `:`"));
        return Some(Err(ParseError));
    }
    lex.take();

    let tok = lex.peek();

    if let Some(Ok(&Token::Symbol(n))) = tok {
        let keep = n
            .bytes()
            .map(|c| match c {
                b'-' => Ok(true),
                b'v' => Ok(false),
                _ => Err(ParseError),
            })
            .collect::<Result<BitVec, ParseError>>();

        if let Ok(keep) = keep {
            lex.take();

            return Some(Ok(Iota::Pattern(
                pattern!(BookkeepersGambit: Cow::Owned(keep)),
            )));
        }
    }

    let ret = tok.map(|_| Err(ParseError));
    let do_skip = matches!(tok, Some(Ok(Token::Symbol(_)) | Err(ParseError)));
    ctx.emit_diagnostic(lex.make_diagnostic("expected bookkeepers spec"));
    if do_skip {
        lex.take();
    }
    ret
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

        while let Some(tok) = lex_default(&mut lex) {
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

        let str = " [Explosion, -1.2e5, (1, 2, 3,), hexpattern (north_east qqq), null, bookkeeper's gambit: vvv, numerical reflection: 5] )";
        let mut strlex = StrLex::new(str);

        let parse = super::parse(&mut ctx, &mut strlex, &Token::RParen);

        dbg!(ctx);
        dbg!(parse);
    }
}
