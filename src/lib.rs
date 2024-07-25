#![allow(unused)]

use std::{
    cmp,
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    ops::{Add, AddAssign, Index, IndexMut, Range, RangeTo},
};

use bitvec::vec::BitVec;
use diagnostics::Diagnostic;
use ustr::Ustr;

// pub mod ast;
pub mod diagnostics;
pub mod iota;
pub mod ir;
pub mod parse;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(Ustr);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

impl AddAssign for Span {
    fn add_assign(&mut self, rhs: Self) {
        self.start = cmp::min(self.start, rhs.start);
        self.end = cmp::max(self.end, rhs.end);
    }
}

impl Add for Span {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign<usize> for Span {
    fn add_assign(&mut self, rhs: usize) {
        self.start += rhs;
        self.end += rhs;
    }
}

impl Add<usize> for Span {
    type Output = Span;

    fn add(mut self, rhs: usize) -> Self::Output {
        self += rhs;
        self
    }
}

impl From<Range<usize>> for Span {
    fn from(Range { start, end }: Range<usize>) -> Self {
        Self { start, end }
    }
}

impl From<RangeTo<usize>> for Span {
    fn from(RangeTo { end }: RangeTo<usize>) -> Self {
        Self { start: 0, end }
    }
}

impl From<Span> for Range<usize> {
    fn from(v: Span) -> Self {
        v.start..v.end
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WithSpan<T> {
    pub val: T,
    pub span: Span,
}

impl<T> WithSpan<T> {
    pub fn new(val: T, span: Span) -> Self {
        Self { val, span }
    }
}

#[derive(Debug)]
pub struct Context {
    diagnostics: Vec<Diagnostic>,
}

impl Context {
    pub fn new() -> Self {
        Self { diagnostics: Vec::new() }
    }

    pub fn emit_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic)
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Id<Tag>(u32, PhantomData<Tag>);

impl<Tag> Id<Tag> {
    pub fn as_index(&self) -> usize {
        (*self).into()
    }
}

impl<Tag> Debug for Id<Tag> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Id").field(&self.0).field(&self.1).finish()
    }
}

impl<Tag> Clone for Id<Tag> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Tag> Copy for Id<Tag> {}

impl<Tag> Hash for Id<Tag> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<Tag> PartialEq for Id<Tag> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl<Tag> Eq for Id<Tag> {}

impl<Tag> From<Id<Tag>> for usize {
    fn from(v: Id<Tag>) -> Self {
        v.0.try_into().unwrap()
    }
}

#[derive(Debug)]
pub struct IdGen<Tag>(Id<Tag>);

impl<Tag> IdGen<Tag> {
    pub fn new() -> Self {
        IdGen(Id(0, PhantomData))
    }

    pub fn new_var(&mut self) -> Id<Tag> {
        let ret = self.0;
        self.0 .0 += 1;
        ret
    }

    pub fn generated_count(&self) -> usize {
        self.0.into()
    }
}

impl<Tag> Default for IdGen<Tag> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct IdMap<Tag, T>(Vec<Option<T>>, PhantomData<Tag>);

impl<Tag, T> IdMap<Tag, T> {
    pub fn new() -> Self {
        Self(Vec::new(), PhantomData)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let mut ret = Self::new();
        ret.0.resize_with(capacity, || None);
        ret
    }

    pub fn get(&self, id: Id<Tag>) -> Option<&T> {
        self.0.get(id.as_index()).and_then(Option::as_ref)
    }

    pub fn get_mut(&mut self, id: Id<Tag>) -> Option<&mut T> {
        self.0.get_mut(id.as_index()).and_then(Option::as_mut)
    }

    pub fn get_or_insert(&mut self, id: Id<Tag>, default: impl FnOnce() -> T) -> &mut T {
        match self.get_mut(id) {
            // hack because lifetimes
            Some(_) => self.get_mut(id).unwrap(),
            None => {
                self.0.resize_with(id.as_index() + 1, || None);
                self.0[id.as_index()] = Some(default());
                self.0[id.as_index()].as_mut().unwrap()
            }
        }
    }

    pub fn insert(&mut self, id: Id<Tag>, val: T) -> &mut T {
        match self.get_mut(id) {
            // hack because lifetimes
            Some(_) => {
                let r = self.get_mut(id).unwrap();
                *r = val;
                r
            }
            None => {
                self.0.resize_with(id.as_index() + 1, || None);
                self.0[id.as_index()] = Some(val);
                self.0[id.as_index()].as_mut().unwrap()
            }
        }
    }

    pub fn remove(&mut self, id: Id<Tag>) {
        if let Some(r) = self.0.get_mut(id.as_index()) {
            *r = None;
        }
    }
}

impl<Tag, T> Index<Id<Tag>> for IdMap<Tag, T> {
    type Output = T;

    fn index(&self, index: Id<Tag>) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<Tag, T> IndexMut<Id<Tag>> for IdMap<Tag, T> {
    fn index_mut(&mut self, index: Id<Tag>) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

impl<Tag, T: Default> IdMap<Tag, T> {
    pub fn get_or_insert_default(&mut self, id: Id<Tag>) -> &mut T {
        self.get_or_insert(id, Default::default)
    }
}

impl<Tag, T: Debug> Debug for IdMap<Tag, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("IdMap")
            .field(&self.0)
            .field(&self.1)
            .finish()
    }
}

impl<Tag, T: Clone> Clone for IdMap<Tag, T> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<Tag, T> Default for IdMap<Tag, T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct IdSet<Tag>(BitVec, PhantomData<Tag>);

impl<Tag> IdSet<Tag> {
    pub fn new() -> IdSet<Tag> {
        Self::default()
    }

    pub fn contains(&self, id: Id<Tag>) -> bool {
        self.0
            .get(id.as_index())
            .as_deref()
            .copied()
            .unwrap_or_default()
    }

    pub fn insert(&mut self, id: Id<Tag>) {
        if id.as_index() >= self.0.len() {
            self.0.resize(id.as_index() + 1, false);
        }
        self.0.set(id.as_index(), true);
    }

    pub fn remove(&mut self, id: Id<Tag>) {
        if let Some(mut r) = self.0.get_mut(id.as_index()) {
            r.set(false);
        }
    }
}

impl<Tag> Debug for IdSet<Tag> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("IdSet")
            .field(&self.0)
            .field(&self.1)
            .finish()
    }
}

impl<Tag> Clone for IdSet<Tag> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<Tag> Default for IdSet<Tag> {
    fn default() -> Self {
        Self(Default::default(), Default::default())
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
