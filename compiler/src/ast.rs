use crate::ty::Type;

#[derive(Debug, PartialEq)]
pub struct Program<T: ExprTag> {
    pub defs: Vec<Def<T>>,
}

#[derive(Debug, PartialEq)]
pub enum Def<T: ExprTag> {
    Func(FuncDef<T>),
    Data(DataDef<T>),
}

#[derive(Debug, PartialEq)]
pub struct FuncDef<T: ExprTag> {
    pub name: String,
    pub params: Vec<Parameter>,
    pub ret_ty: Type,
    pub body: Box<Expr<T>>,
}

#[derive(Debug, PartialEq)]
pub struct DataDef<T: ExprTag> {
    pub name: String,
    pub ty: Type,
    pub initializer: Box<Expr<T>>,
}

#[derive(Debug, PartialEq)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
}

pub trait ExprTag: std::fmt::Debug + Clone + PartialEq {}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr<T: ExprTag> {
    pub e: E<T>,
    pub tag: T,
}

#[derive(Debug, Clone, PartialEq)]
pub enum E<T: ExprTag> {
    LiteralVoid,
    LiteralBool(bool),
    LiteralU64(u64),
    LiteralArray(Vec<Box<Expr<T>>>),

    AddrOf(Box<Expr<T>>),

    Var(String),
    PtrDeref(Box<Expr<T>>),
    ArrayAccess {
        ptr: Box<Expr<T>>,
        idx: Box<Expr<T>>,
    },

    Add(Box<Expr<T>>, Box<Expr<T>>),
    Sub(Box<Expr<T>>, Box<Expr<T>>),
    Mul(Box<Expr<T>>, Box<Expr<T>>),
    Div(Box<Expr<T>>, Box<Expr<T>>),

    Eq(Box<Expr<T>>, Box<Expr<T>>),
    Neq(Box<Expr<T>>, Box<Expr<T>>),
    Lt(Box<Expr<T>>, Box<Expr<T>>),
    Gt(Box<Expr<T>>, Box<Expr<T>>),

    LNot(Box<Expr<T>>),
    Leq(Box<Expr<T>>, Box<Expr<T>>),
    Geq(Box<Expr<T>>, Box<Expr<T>>),
    LAnd(Box<Expr<T>>, Box<Expr<T>>),
    LOr(Box<Expr<T>>, Box<Expr<T>>),

    Call {
        func: Box<Expr<T>>,
        args: Vec<Box<Expr<T>>>,
    },

    If {
        cond: Box<Expr<T>>,
        then_expr: Box<Expr<T>>,
        else_expr: Option<Box<Expr<T>>>,
    },

    Loop {
        body: Box<Expr<T>>,
    },
    While {
        cond: Box<Expr<T>>,
        body: Box<Expr<T>>,
    },
    For {
        init: Box<Expr<T>>,
        cond: Box<Expr<T>>,
        update: Box<Expr<T>>,
        body: Box<Expr<T>>,
    },
    Break,
    Continue,

    Let {
        name: String,
        value: Box<Expr<T>>,
    },

    Assignment {
        location: Box<Expr<T>>,
        value: Box<Expr<T>>,
    },
    AssignAdd {
        location: Box<Expr<T>>,
        value: Box<Expr<T>>,
    },
    AssignSub {
        location: Box<Expr<T>>,
        value: Box<Expr<T>>,
    },
    AssignMul {
        location: Box<Expr<T>>,
        value: Box<Expr<T>>,
    },
    AssignDiv {
        location: Box<Expr<T>>,
        value: Box<Expr<T>>,
    },

    Block(Vec<Box<Expr<T>>>),
}
