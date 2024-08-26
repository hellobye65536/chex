use std::{
    borrow::Cow,
    fmt::{self},
    mem,
    str::FromStr,
    sync::OnceLock,
};

use bitvec::vec::BitVec;
use fst::raw::Fst;
use itertools::Itertools;
use tap::TapOptional;

use crate::{
    core::{Context, Diagnostic, Severity, Span, Tag},
    iota::{bytes_as_angles, Angle, ComplexPattern, Direction, Iota, Pattern, SimplePattern},
    parse::{LexResult, ParseError, ParseResult, StrLex},
    pattern,
};

use super::{expect_closing, munch_group, munch_groups_until, GroupingToken, LexFn};

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

impl<'a> GroupingToken for Token<'a> {
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

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Token::Symbol(s) => return write!(f, "symbol `{}`", s),
            Token::LParen => "`(`",
            Token::RParen => "`)`",
            Token::LBracket => "`[`",
            Token::RBracket => "`]`",
            Token::LCurly => "`{`",
            Token::RCurly => "`}`",
            Token::Colon => "`:`",
            Token::Sep => "`,`",
        })
    }
}

fn is_token_sep(c: char) -> bool {
    c.is_ascii_whitespace() || ['(', ')', '[', ']', '{', '}', ';', ':', ','].contains(&c)
}

struct Lex;
impl<'str> LexFn<'str> for Lex {
    type Token = Token<'str>;

    fn lex(&mut self, strlex: &mut StrLex<'str>) -> Option<LexResult<Self::Token>> {
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

type ParseContext<'p, 'str> = super::ParseContext<'p, 'str, Token<'str>, Lex>;

pub fn parse<'str, T, F>(
    ctx: &mut super::ParseContext<'_, 'str, T, F>,
    closing: &Token<'str>,
) -> ParseResult<Iota> {
    let mut ctx: ParseContext<'_, 'str> = ctx.change_token().with_lex_fn(Lex);
    let ctx = &mut ctx;

    let iota = parse_iota(ctx);

    expect_closing(ctx, closing).map(|closing| closing.and(iota.unwrap_or(Err(ParseError))))
}

fn parse_iota(ctx: &mut ParseContext) -> ParseResult<Iota> {
    match ctx.peek() {
        Some(Ok(&Token::Symbol(pat))) => {
            ctx.take();
            if let Some(n) = is_symbol_numeric(pat) {
                Some(Ok(Iota::Num(n)))
            } else {
                parse_symbol(ctx, pat)
            }
        }
        Some(Ok(Token::LParen)) => {
            ctx.take();
            parse_vec(ctx)
        }
        Some(Ok(left @ (Token::LCurly | Token::LBracket))) => {
            let right = left.right_matching().unwrap();
            ctx.take();
            parse_list(ctx, &right)
        }
        tok => {
            ctx.parse_diagnostic("expected iota expression");
            munch_groups_until(ctx, |tok| matches!(tok, Token::Sep));
            Some(Err(ParseError))
        }
    }
}

fn parse_list<'str>(ctx: &mut ParseContext<'_, 'str>, closing: &Token<'str>) -> ParseResult<Iota> {
    let mut iotas = Ok(Vec::new());

    loop {
        if ctx.peek().is_none() {
            break;
        }

        let Some(iota) = parse_iota(ctx) else {
            return expect_closing(ctx, closing).map(|_| Err(ParseError));
        };

        iotas = iotas.and_then(|mut iotas| {
            iotas.push(iota?);
            Ok(iotas)
        });

        match ctx.peek() {
            Some(Ok(Token::Sep)) => {
                ctx.take();
            }
            Some(_) => {
                ctx.parse_diagnostic(format!("expected `,` or {}", closing));
                // munch_groups_until(ctx, |tok| matches!(tok, Token::Sep))?;
            }
            None => break,
        }
    }

    expect_closing(ctx, closing).map(|closing| closing.and(iotas.map(Iota::List)))
}

fn parse_vec(ctx: &mut ParseContext) -> ParseResult<Iota> {
    fn parse_num(ctx: &mut ParseContext) -> ParseResult<f64> {
        if let Ok(Token::Symbol(str)) = ctx.peek()? {
            if let Some(n) = is_symbol_numeric(str) {
                ctx.take();
                return Some(Ok(n));
            }
        }

        ctx.parse_diagnostic("expected number");

        munch_groups_until(ctx, |tok| matches!(tok, Token::Sep));
        Some(Err(ParseError))
    }

    fn expect_sep(ctx: &mut ParseContext) -> ParseResult<()> {
        Some(if let Ok(Token::Sep) = ctx.peek()? {
            ctx.take();
            Ok(())
        } else {
            ctx.parse_diagnostic("expected `,`");

            munch_groups_until(ctx, |tok| matches!(tok, Token::Sep));
            Err(ParseError)
        })
    }

    let iota = (|| {
        let x = parse_num(ctx)?;
        let sep0 = expect_sep(ctx)?;
        let y = parse_num(ctx)?;
        let sep1 = expect_sep(ctx)?;
        let z = parse_num(ctx)?;

        if let Some(Ok(Token::Sep)) = ctx.peek() {
            ctx.take();
        }

        Some((|| {
            sep0?;
            sep1?;

            Ok::<_, ParseError>(Iota::Vec(x?, y?, z?))
        })())
    })();

    if iota.is_none() {
        ctx.parse_diagnostic("expected rest of vector expression");
    }

    expect_closing(ctx, &Token::RParen).map(|closing| closing.and(iota.unwrap_or(Err(ParseError))))
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

fn parse_symbol(ctx: &mut ParseContext, pat: &str) -> ParseResult<Iota> {
    let fst = pattern_parse_table();
    let mut fst_state = FstState::new(fst);

    update_fst_state(fst, &mut fst_state, pat);
    let mut span = ctx.span();
    ctx.take();

    while let Some(Ok(Token::Symbol(pat))) = ctx.peek() {
        update_fst_state(fst, &mut fst_state, pat);
        span += ctx.span();
        ctx.take();
    }

    match fst_state.value().map(u64::wrapping_neg) {
        Some(1) => return parse_hexpattern(ctx),
        Some(2) => return parse_numerical_reflection(ctx),
        Some(3) => return parse_bookkeepers_gambit(ctx),
        Some(4) => return Some(Ok(Iota::Null)),
        _ => {}
    }

    loop {
        match ctx.peek() {
            Some(Ok(Token::Colon)) => update_fst_state(fst, &mut fst_state, ":"),
            Some(Ok(Token::Symbol(pat))) => update_fst_state(fst, &mut fst_state, pat),
            _ => break,
        }
        span += ctx.span();
        ctx.take();
    }

    if let Some(val) = fst_state.value() {
        let pat = val.try_into().expect("parse table has invalid pattern id");
        Some(Ok(Iota::Pattern(Pattern::Simple(pat))))
    } else {
        ctx.emit_diagnostic(
            Diagnostic::new(
                Severity::Error,
                "expected valid pattern".to_owned(),
                (ctx.file(), span),
            )
            .with_primary_tag(None),
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

fn parse_hexpattern(ctx: &mut ParseContext) -> ParseResult<Iota> {
    if !matches!(ctx.peek(), Some(Ok(Token::LParen))) {
        ctx.parse_diagnostic("expected `(`");
        return Some(Err(ParseError));
    }
    ctx.take();

    let iota = (|| {
        let direction = match ctx.peek()? {
            Ok(&Token::Symbol(dir)) => {
                ctx.take();
                parse_direction(dir)
                    .tap_none(|| ctx.parse_diagnostic("expected valid direction"))
                    .ok_or(ParseError)
            }
            _ => {
                ctx.parse_diagnostic("expected direction and angles");
                munch_group(ctx)?;
                Err(ParseError)
            }
        };

        let angles = match ctx.peek()? {
            Ok(&Token::Symbol(angles)) => {
                ctx.take();
                bytes_as_angles(angles.as_bytes())
                    .tap_none(|| ctx.parse_diagnostic("expected angles"))
                    .ok_or(ParseError)
            }
            _ => {
                ctx.parse_diagnostic("expected angles");
                munch_group(ctx)?;
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
        ctx.parse_diagnostic("expected rest of hexpattern expression");
    }

    expect_closing(ctx, &Token::RParen).map(|closing| closing.and(iota.unwrap_or(Err(ParseError))))
}

fn parse_numerical_reflection(ctx: &mut ParseContext) -> ParseResult<Iota> {
    if !matches!(ctx.peek(), Some(Ok(Token::Colon))) {
        ctx.parse_diagnostic("expected `:`");
        return Some(Err(ParseError));
    }
    ctx.take();

    let tok = ctx.peek();

    if let Some(Ok(&Token::Symbol(str))) = tok {
        if let Some(n) = is_symbol_numeric(str) {
            ctx.take();
            return Some(Ok(Iota::Pattern(pattern!(NumericalReflection: n))));
        }
    }

    let ret = tok.map(|_| Err(ParseError));
    let do_skip = matches!(tok, Some(Ok(Token::Symbol(_)) | Err(ParseError)));
    ctx.parse_diagnostic("expected number");
    if do_skip {
        ctx.take();
    }
    ret
}

fn parse_bookkeepers_gambit(ctx: &mut ParseContext) -> ParseResult<Iota> {
    if !matches!(ctx.peek(), Some(Ok(Token::Colon))) {
        ctx.parse_diagnostic("expected `:`");
        return Some(Err(ParseError));
    }
    ctx.take();

    let tok = ctx.peek();

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
            ctx.take();

            return Some(Ok(Iota::Pattern(
                pattern!(BookkeepersGambit: Cow::Owned(keep)),
            )));
        }
    }

    let ret = tok.map(|_| Err(ParseError));
    let do_skip = matches!(tok, Some(Ok(Token::Symbol(_)) | Err(ParseError)));
    ctx.parse_diagnostic("expected bookkeepers spec");
    if do_skip {
        ctx.take();
    }
    ret
}

#[cfg(test)]
mod tests {
    use crate::{
        core::{Context, IdGen},
        parse::{LexFn, ParseContext, StrLex},
    };

    use super::{parse_iota, pattern_parse_table, Token};

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

        while let Some(tok) = super::Lex.lex(&mut lex) {
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
        let mut file_id_gen = IdGen::new();
        let mut ctx = ParseContext::<(), _>::new(&mut ctx, file_id_gen.new_var(), &mut strlex);

        let parse = super::parse(&mut ctx, &Token::RParen);

        dbg!(ctx);
        dbg!(parse);
    }
}
