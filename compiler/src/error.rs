use crate::ty::Type;

#[derive(Debug)]
pub enum Error {
    Syntax {
        line: usize,
        column: usize,
        msg: String,
    },
    TypeMismatch {
        expect: Option<Type>,
        actual: Type,
    },
    CategoryMismatch,
    UndefVar {
        name: String,
    },
}
