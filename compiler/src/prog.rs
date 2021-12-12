use crate::expr::TypedExpr;
use crate::ty::Type;

#[derive(Debug, PartialEq)]
pub struct Program {
    pub functions: Vec<FuncDef>,
}

#[derive(Debug, PartialEq)]
pub struct FuncDef {
    pub name: String,
    pub params: Vec<Parameter>,
    pub ret_ty: Type,
    pub body: Box<TypedExpr>,
}

#[derive(Debug, PartialEq)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
}
