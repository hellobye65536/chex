use crate::{
    core::{FileSpan, Id, Span},
    iota::Iota,
    Symbol,
};

#[derive(Debug)]
pub struct Unit {
    pub defs: Vec<Def>,
}

type OFSpan = Option<FileSpan>;

pub enum DefTag {}
pub type DefId = Id<DefTag>;

pub enum LetTag {}
pub type LetId = Id<LetTag>;

#[derive(Debug)]
pub struct Def {
    pub id: DefId,
    pub expr: Expr,
    pub span: OFSpan,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: OFSpan,
}

#[derive(Debug)]
pub enum ExprKind {
    Comma(Vec<Expr>),
    Iota(Iota),
    Block(Box<Block>),
    Num(f64),
    Def(DefId),
    Let(LetId),
    Call(Call),
}

#[derive(Debug)]
pub struct CallArity {
    pub arity: u32,
    pub span: OFSpan,
}

#[derive(Debug)]
pub struct Call {
    pub fun: Box<Expr>,
    pub arity: Option<CallArity>,
    pub arg: Box<Expr>,
    pub span: OFSpan,
}

#[derive(Debug)]
pub struct Block {
    pub args: Vec<(LetId, OFSpan)>,
    pub stmts: Vec<Stmt>,
    pub ret: Expr,
    pub span: OFSpan,
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: OFSpan,
}

#[derive(Debug)]
pub enum StmtKind {
    Let(Let),
    Expr(Expr),
}

#[derive(Debug)]
pub struct Let {
    pub bindings: Vec<(LetId, OFSpan)>,
    pub arg: Box<Expr>,
}
