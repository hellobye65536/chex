#![allow(unused)]

use std::{
    cmp,
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    ops::{Add, AddAssign, Index, IndexMut, Range, RangeTo},
};

use bitvec::vec::BitVec;
use ustr::Ustr;

use crate::core::Diagnostic;

pub mod ast;
pub mod core;
pub mod iota;
pub mod ir;
pub mod parse;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(Ustr);

impl From<&str> for Symbol {
    fn from(v: &str) -> Self {
        Self(v.into())
    }
}

pub trait UsizeToU8 {
    fn into_u8(self) -> u8;
}

impl UsizeToU8 for usize {
    fn into_u8(self) -> u8 {
        self.try_into().expect("index too big")
    }
}
