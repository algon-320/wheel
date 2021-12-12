use crate::ty::Type;

#[derive(Debug)]
pub enum Error {
    SyntaxError {
        line: usize,
        column: usize,
        msg: String,
    },
    TypeMismach {
        expect: Option<Type>,
        actual: Type,
    },
    UndefVar {
        name: String,
    },
}
