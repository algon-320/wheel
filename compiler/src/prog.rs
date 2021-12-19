use crate::expr::{Expr, ExprTag};
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
