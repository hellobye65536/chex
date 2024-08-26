use std::{
    cmp,
    ops::{Add, AddAssign, Range, RangeTo},
};

use crate::core::id::Id;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.end
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

pub enum FileTag {}
pub type FileId = Id<FileTag>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileSpan {
    pub file: FileId,
    pub span: Span,
}

impl FileSpan {
    pub fn new(file: FileId, span: Span) -> Self {
        Self { file, span }
    }
}

impl<S: Into<Span>> From<(FileId, S)> for FileSpan {
    fn from((file, span): (FileId, S)) -> Self {
        FileSpan { file, span: span.into() }
    }
}
