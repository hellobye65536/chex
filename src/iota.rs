use std::borrow::Cow;

use bitvec::{slice::BitSlice, vec::BitVec};

#[macro_export]
macro_rules! pattern {
    (BookkeepersGambit: $keep:expr) => {
        $crate::iota::Pattern::Complex($crate::iota::ComplexPattern::BookkeepersGambit {
            keep: $keep,
        })
    };
    (NumericalReflection: $num:expr) => {
        $crate::iota::Pattern::Complex($crate::iota::ComplexPattern::NumericalReflection($num))
    };
    ($ident:ident) => {
        $crate::iota::Pattern::Simple($crate::iota::SimplePattern::$ident)
    };
}

#[macro_export]
macro_rules! patterns {
    ($($tk:tt)*) => {
        $crate::patterns_munch!([] $($tk)*)
    };
}

#[macro_export]
macro_rules! patterns_munch {
    ([]) => {
        {
            let __patterns_res: [$crate::iota::Pattern; 0] = [];
            __patterns_res
        }
    };
    ([$($acc:expr,)*]) => { [$($acc,)*] };
    ([$($acc:expr,)*] $a:tt $(, $($rest:tt)*)?) => {
        $crate::patterns_munch!(
            [$($acc,)* $crate::pattern!($a),]
            $($($rest)*)?
        )
    };
    ([$($acc:expr,)*] $a:tt $b:tt $(, $($rest:tt)*)?) => {
        $crate::patterns_munch!(
            [$($acc,)* $crate::pattern!($a $b),]
            $($($rest)*)?
        )
    };
    ([$($acc:expr,)*] $a:tt $b:tt $c:tt $(, $($rest:tt)*)?) => {
        $crate::patterns_munch!(
            [$($acc,)* $crate::pattern!($a $b $c),]
            $($($rest)*)?
        )
    };
}

#[derive(Debug, Clone, PartialEq)]
pub enum Iota {
    Null,
    Bool(bool),
    Num(f64),
    Vec(f64, f64, f64),
    List(Vec<Iota>),
    Pattern(Pattern),
}

impl Iota {
    pub fn as_embed_pattern(&self) -> Option<Pattern> {
        Some(match *self {
            Iota::Null => pattern!(NullaryReflection),
            Iota::Bool(b) => {
                if b {
                    pattern!(TrueReflection)
                } else {
                    pattern!(FalseReflection)
                }
            }
            Iota::Num(std::f64::consts::PI) => pattern!(ArcsReflection),
            Iota::Num(std::f64::consts::TAU) => pattern!(CirclesReflection),
            Iota::Num(std::f64::consts::E) => pattern!(EulersReflection),
            Iota::Num(_) => return None,
            Iota::Vec(0.0, 0.0, 0.0) => pattern!(VectorReflectionZero),
            Iota::Vec(1.0, 0.0, 0.0) => pattern!(VectorReflectionPX),
            Iota::Vec(0.0, 1.0, 0.0) => pattern!(VectorReflectionPY),
            Iota::Vec(0.0, 0.0, 1.0) => pattern!(VectorReflectionPZ),
            Iota::Vec(-1.0, 0.0, 0.0) => pattern!(VectorReflectionNX),
            Iota::Vec(0.0, -1.0, 0.0) => pattern!(VectorReflectionNY),
            Iota::Vec(0.0, 0.0, -1.0) => pattern!(VectorReflectionNZ),
            Iota::Vec(..) => return None,
            Iota::List(ref v) if v.is_empty() => pattern!(VacantReflection),
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    NorthEast,
    East,
    SouthEast,
    SouthWest,
    West,
    NorthWest,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Angle {
    Forward = b'w',
    Right = b'e',
    RightBack = b'd',
    Back = b's',
    LeftBack = b'a',
    Left = b'q',
}

impl Angle {
    pub const VALID_BYTES: &'static [u8] = b"wedsaq";
}

pub fn angles_as_str(angles: &[Angle]) -> &str {
    unsafe { &*(angles as *const [Angle] as *const str) }
}

pub fn bytes_as_angles(bs: &[u8]) -> Option<&[Angle]> {
    bs.iter()
        .all(|c| Angle::VALID_BYTES.contains(c))
        .then(|| unsafe { &*(bs as *const [u8] as *const [Angle]) })
}

pub fn bytes_as_angles_mut(bs: &mut [u8]) -> Option<&mut [Angle]> {
    bs.iter()
        .all(|c| Angle::VALID_BYTES.contains(c))
        .then(|| unsafe { &mut *(bs as *mut [u8] as *mut [Angle]) })
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Simple(SimplePattern),
    Complex(ComplexPattern),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ComplexPattern {
    NumericalReflection(f64),
    BookkeepersGambit {
        keep: Cow<'static, BitSlice>,
    },
    Other {
        dir: Direction,
        angles: Cow<'static, [Angle]>,
    },
    Unknown {
        name: String,
    },
}

include!(concat!(env!("OUT_DIR"), "/patterns.rs"));

#[cfg(test)]
mod tests {
    use crate::iota::{Pattern, SimplePattern};

    #[test]
    fn pattern_macro() {
        assert_eq!(pattern!(Blink), Pattern::Simple(SimplePattern::Blink));
        assert_eq!(patterns![Blink], [Pattern::Simple(SimplePattern::Blink)]);
        assert_eq!(
            patterns![Blink, Blink],
            [
                Pattern::Simple(SimplePattern::Blink),
                Pattern::Simple(SimplePattern::Blink)
            ]
        );
    }
}
