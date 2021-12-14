use crate::ty::Type;

#[derive(Debug, PartialEq)]
pub struct TypedExpr {
    pub e: Expr,
    pub t: Option<Type>,
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    LiteralVoid,
    LiteralBool(bool),
    LiteralU64(u64),
    Var(String),
    AddrOf(Box<TypedLocationExpr>),
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

    Let {
        name: String,
        value: Box<TypedExpr>,
        expr: Box<TypedExpr>,
    },

    Assignment {
        location: Box<TypedLocationExpr>,
        value: Box<TypedExpr>,
    },

    Block(Vec<TypedExpr>, bool),
}

#[derive(Debug, PartialEq)]
pub struct TypedLocationExpr {
    pub e: LocationExpr,
    pub t: Option<Type>,
}

#[derive(Debug, PartialEq)]
pub enum LocationExpr {
    Var(String),
}
