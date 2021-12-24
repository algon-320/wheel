use crate::ty::TypeBound;

pub trait ExprBound: std::fmt::Debug + Clone + PartialEq {}

#[derive(Debug, Clone, PartialEq)]
pub struct Program<E: ExprBound, T: TypeBound> {
    pub defs: Vec<Def<E, T>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Def<E: ExprBound, T: TypeBound> {
    Func(FuncDef<E, T>),
    Data(DataDef<E, T>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<T: TypeBound> {
    pub name: String,
    pub ty: T,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef<E: ExprBound, T: TypeBound> {
    pub name: String,
    pub params: Vec<Field<T>>,
    pub ret_ty: T,
    pub body: Box<E>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DataDef<E: ExprBound, T: TypeBound> {
    pub name: String,
    pub ty: T,
    pub initializer: Box<E>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<E: ExprBound> {
    LiteralVoid,
    LiteralBool(bool),
    LiteralU64(u64),
    LiteralArray(Vec<Box<E>>),

    AddrOf(Box<E>),

    Var(String),
    PtrDeref(Box<E>),
    ArrayAccess {
        ptr: Box<E>,
        idx: Box<E>,
    },

    Add(Box<E>, Box<E>),
    Sub(Box<E>, Box<E>),
    Mul(Box<E>, Box<E>),
    Div(Box<E>, Box<E>),

    Eq(Box<E>, Box<E>),
    Neq(Box<E>, Box<E>),
    Lt(Box<E>, Box<E>),
    Gt(Box<E>, Box<E>),

    LNot(Box<E>),
    Leq(Box<E>, Box<E>),
    Geq(Box<E>, Box<E>),
    LAnd(Box<E>, Box<E>),
    LOr(Box<E>, Box<E>),

    Call {
        func: Box<E>,
        args: Vec<Box<E>>,
    },

    If {
        cond: Box<E>,
        then_expr: Box<E>,
        else_expr: Option<Box<E>>,
    },

    Loop {
        body: Box<E>,
    },
    While {
        cond: Box<E>,
        body: Box<E>,
    },
    For {
        init: Box<E>,
        cond: Box<E>,
        update: Box<E>,
        body: Box<E>,
    },
    Break,
    Continue,

    Let {
        name: String,
        value: Box<E>,
    },

    Assignment {
        location: Box<E>,
        value: Box<E>,
    },
    AssignAdd {
        location: Box<E>,
        value: Box<E>,
    },
    AssignSub {
        location: Box<E>,
        value: Box<E>,
    },
    AssignMul {
        location: Box<E>,
        value: Box<E>,
    },
    AssignDiv {
        location: Box<E>,
        value: Box<E>,
    },

    Block(Vec<Box<E>>),
}
