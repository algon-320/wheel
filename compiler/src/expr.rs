use crate::ty::{Category, Type};

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub e: Expr,
    pub t: Option<Type>,
    pub c: Option<Category>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    LiteralVoid,
    LiteralBool(bool),
    LiteralU64(u64),

    AddrOf(Box<TypedExpr>),

    Var(String),
    PtrDeref(Box<TypedExpr>),

    Add(Box<TypedExpr>, Box<TypedExpr>),
    Sub(Box<TypedExpr>, Box<TypedExpr>),
    Mul(Box<TypedExpr>, Box<TypedExpr>),
    Div(Box<TypedExpr>, Box<TypedExpr>),

    Eq(Box<TypedExpr>, Box<TypedExpr>),
    Neq(Box<TypedExpr>, Box<TypedExpr>),
    Lt(Box<TypedExpr>, Box<TypedExpr>),
    Gt(Box<TypedExpr>, Box<TypedExpr>),

    LNot(Box<TypedExpr>),
    Leq(Box<TypedExpr>, Box<TypedExpr>),
    Geq(Box<TypedExpr>, Box<TypedExpr>),
    LAnd(Box<TypedExpr>, Box<TypedExpr>),
    LOr(Box<TypedExpr>, Box<TypedExpr>),

    Call {
        func: Box<TypedExpr>,
        args: Vec<TypedExpr>,
    },

    If {
        cond: Box<TypedExpr>,
        then_expr: Box<TypedExpr>,
        else_expr: Box<TypedExpr>,
    },

    Loop {
        body: Box<TypedExpr>,
    },
    Break,

    Let {
        name: String,
        value: Box<TypedExpr>,
        expr: Box<TypedExpr>,
    },

    Assignment {
        location: Box<TypedExpr>,
        value: Box<TypedExpr>,
    },

    Block(Vec<TypedExpr>, bool),
}
