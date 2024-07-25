use crate::{Symbol, WithSpan};

pub type Decl = WithSpan<DeclKind>;
pub type Expr = WithSpan<ExprKind>;
pub type Stmt = WithSpan<StmtKind>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Ident {
    module: Option<WithSpan<Symbol>>,
    ident: WithSpan<Symbol>,
}

impl Ident {
    pub fn new(module: Option<WithSpan<Symbol>>, ident: WithSpan<Symbol>) -> Self {
        Self { module, ident }
    }
}

#[derive(Debug)]
pub enum DeclKind {
    Module { ident: Ident, inner: Vec<Decl> },
    Include(Ident),
    Def { ident: Ident, expr: Box<Expr> },
}

#[derive(Debug)]
pub struct Block {
    pub args: Vec<Ident>,
    pub stmts: Vec<Stmt>,
    pub ret: Box<Expr>,
}

#[derive(Debug)]
pub enum ExprKind {
    Sep(Box<Expr>, Box<Expr>),
    Call {
        fun: Box<Expr>,
        arg: Box<Expr>,
        ret_arity: Option<u32>,
    },
    Binop {
        op: BinOp,
        arg1: Box<Expr>,
        arg2: Box<Expr>,
    },
    Block(Block),
    Var(Ident),
    Num(f64),
    Intrinsic(Intrinsic),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug)]
pub enum StmtKind {
    Let { idents: Vec<Ident>, expr: Box<Expr> },
    Def { ident: Ident, expr: Box<Expr> },
}

#[derive(Debug)]
pub enum Intrinsic {
    Null,
    True,
    False,
    Vec,
    Add,
    Sub,
    Mul,
    Div,
}

mod tagged {
    use crate::Span;

    use super::Intrinsic;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Ident(pub u32);

    #[derive(Debug)]
    pub struct Decl {
        ident: Ident,
        expr: Box<Expr>,
        span: Span,
    }

    #[derive(Debug)]
    pub struct Expr {
        kind: ExprKind,
        arity: u32,
        span: Span,
    }

    #[derive(Debug)]
    pub enum ExprKind {
        Sep(Box<Expr>, Box<Expr>),
        Call {
            fun: Box<Expr>,
            arg: Box<Expr>,
            ret_arity: u32,
        },
        Block {
            args: Vec<Ident>,
            inner: Vec<Stmt>,
            ret: Box<Expr>,
        },
        Var(Ident),
        Num(f64),
        Intrinsic(Intrinsic),
    }

    #[derive(Debug)]
    pub struct Stmt {
        kind: StmtKind,
        span: Span,
    }

    #[derive(Debug)]
    pub enum StmtKind {
        Let { idents: Vec<Ident>, expr: Box<Expr> },
        Def { ident: Ident, expr: Box<Expr> },
    }
}

pub fn lower_ast() {}

fn tag_ast() {}
