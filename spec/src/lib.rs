use num_derive::FromPrimitive;

#[repr(u8)]
#[derive(Debug, Clone, Copy, FromPrimitive, PartialEq, Eq)]
pub enum Instruction {
    Nop = 0,
    Lit08 = 1,
    Lit16 = 2,
    Lit32 = 3,
    Lit64 = 4,
    Drop08 = 5,
    Drop16 = 6,
    Drop32 = 7,
    Drop64 = 8,
    Add08 = 9,
    Add16 = 10,
    Add32 = 11,
    Add64 = 12,
    Sub08 = 13,
    Sub16 = 14,
    Sub32 = 15,
    Sub64 = 16,
    Mul08 = 17,
    Mul16 = 18,
    Mul32 = 19,
    Mul64 = 20,
    Div08 = 21,
    Div16 = 22,
    Div32 = 23,
    Div64 = 24,
    Eq08 = 25,
    Eq16 = 26,
    Eq32 = 27,
    Eq64 = 28,
    Lt08 = 29,
    Lt16 = 30,
    Lt32 = 31,
    Lt64 = 32,
    Gt08 = 33,
    Gt16 = 34,
    Gt32 = 35,
    Gt64 = 36,
    Load08 = 37,
    Load16 = 38,
    Load32 = 39,
    Load64 = 40,
    Store08 = 41,
    Store16 = 42,
    Store32 = 43,
    Store64 = 44,
    Jump = 45,
    JumpIf = 46,
    GetIp = 47,
    SetBp = 48,
    GetBp = 49,
    GetSp = 50,
    Abort = 51,
}

impl Into<u8> for Instruction {
    fn into(self) -> u8 {
        self as u8
    }
}

impl From<u8> for Instruction {
    fn from(opcode: u8) -> Self {
        use num_traits::FromPrimitive;
        FromPrimitive::from_u8(opcode).expect("invalid opcode")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_ident() {
        use Instruction::*;
        let ops = [
            Nop, Lit08, Lit16, Lit32, Lit64, Drop08, Drop16, Drop32, Drop64, Add08, Add16, Add32,
            Add64, Sub08, Sub16, Sub32, Sub64, Mul08, Mul16, Mul32, Mul64, Div08, Div16, Div32,
            Div64, Eq08, Eq16, Eq32, Eq64, Lt08, Lt16, Lt32, Lt64, Gt08, Gt16, Gt32, Gt64, Load08,
            Load16, Load32, Load64, Store08, Store16, Store32, Store64, Jump, JumpIf, GetIp, SetBp,
            GetBp, GetSp, Abort,
        ];
        for op in ops {
            let code: u8 = op.into();
            let op2 = Instruction::from(code);
            assert_eq!(op, op2);
        }
    }
}
