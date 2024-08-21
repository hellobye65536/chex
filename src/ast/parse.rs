use crate::{iota::Iota, Span, Symbol};

#[derive(Debug)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Debug)]
pub struct File {
    pub items: Vec<Item>,
}

#[derive(Debug)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ItemKind {
    Def(Def),
}

#[derive(Debug)]
pub struct Def {
    pub ident: Ident,
    pub expr: Expr,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExprKind {
    Comma(Vec<Expr>),
    OpCluster(Vec<OpElem>),
    Iota(Iota),
    Block(Box<Block>),
    Num(f64),
    Var(Ident),
}

#[derive(Debug)]
pub struct ExprCallArity {
    pub arity: u32,
    pub span: Span,
}

#[derive(Debug)]
pub enum OpElem {
    Op(Ident),
    Term(Expr),
    Call(Call),
}

#[derive(Debug)]
pub struct Call {
    pub arity: Option<ExprCallArity>,
    pub arg: Box<Expr>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Block {
    pub args: Vec<Ident>,
    pub stmts: Vec<Stmt>,
    pub ret: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StmtKind {
    Let(LetStmt),
    Def(Def),
    Expr(Expr),
    // Include(_),
}

#[derive(Debug)]
pub struct LetStmt {
    pub bindings: Vec<Ident>,
    pub arg: Box<Expr>,
}
