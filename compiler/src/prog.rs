use crate::expr::TypedExpr;
use crate::ty::Type;

#[derive(Debug, PartialEq)]
pub struct Program {
    pub defs: Vec<Def>,
}

#[derive(Debug, PartialEq)]
pub enum Def {
    Func(FuncDef),
    Data(DataDef),
}

#[derive(Debug, PartialEq)]
pub struct FuncDef {
    pub name: String,
    pub params: Vec<Parameter>,
    pub ret_ty: Type,
    pub body: Box<TypedExpr>,
}

#[derive(Debug, PartialEq)]
pub struct DataDef {
    pub name: String,
    pub ty: Type,
    pub initializer: Box<TypedExpr>,
}

#[derive(Debug, PartialEq)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
}
