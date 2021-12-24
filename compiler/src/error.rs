use crate::ty::ResolvedType;

#[derive(Debug)]
pub enum Error {
    Syntax {
        line: usize,
        column: usize,
        msg: String,
    },
    TypeMismatch {
        expect: Option<ResolvedType>,
        actual: ResolvedType,
    },
    CategoryMismatch,
    UndefinedType {
        name: String,
    },
    UndefinedField {
        struct_name: String,
        field_name: String,
    },
    UndefinedVar {
        name: String,
    },
}
