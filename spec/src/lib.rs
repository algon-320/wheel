use num_derive::FromPrimitive;
use strum::{Display, EnumString};

#[repr(u8)]
#[derive(Debug, Clone, Copy, FromPrimitive, PartialEq, Eq, EnumString, Display)]
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
    And08 = 25,
    And16 = 26,
    And32 = 27,
    And64 = 28,
    Or08 = 29,
    Or16 = 30,
    Or32 = 31,
    Or64 = 32,
    Xor08 = 33,
    Xor16 = 34,
    Xor32 = 35,
    Xor64 = 36,
    Not08 = 37,
    Not16 = 38,
    Not32 = 39,
    Not64 = 40,
    Eq08 = 41,
    Eq16 = 42,
    Eq32 = 43,
    Eq64 = 44,
    Lt08 = 45,
    Lt16 = 46,
    Lt32 = 47,
    Lt64 = 48,
    Gt08 = 49,
    Gt16 = 50,
    Gt32 = 51,
    Gt64 = 52,
    Load08 = 53,
    Load16 = 54,
    Load32 = 55,
    Load64 = 56,
    Store08 = 57,
    Store16 = 58,
    Store32 = 59,
    Store64 = 60,
    Jump = 61,
    JumpIf = 62,
    GetIp = 63,
    SetBp = 64,
    GetBp = 65,
    SetSp = 66,
    GetSp = 67,
    Abort = 68,

    DebugComment = 0xF0,
}

impl From<Instruction> for u8 {
    fn from(i: Instruction) -> u8 {
        i as u8
    }
}

impl From<u8> for Instruction {
    fn from(opcode: u8) -> Self {
        use num_traits::FromPrimitive;
        FromPrimitive::from_u8(opcode).expect("invalid opcode")
    }
}

#[repr(u64)]
pub enum MmioBase {
    BasicSerial = 0x8000_0000_0000_0000,
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
            Div64, And08, And16, And32, And64, Or08, Or16, Or32, Or64, Xor08, Xor16, Xor32, Xor64,
            Not08, Not16, Not32, Not64, Eq08, Eq16, Eq32, Eq64, Lt08, Lt16, Lt32, Lt64, Gt08, Gt16,
            Gt32, Gt64, Load08, Load16, Load32, Load64, Store08, Store16, Store32, Store64, Jump,
            JumpIf, GetIp, SetBp, GetBp, GetSp, Abort,
        ];
        for op in ops {
            let code: u8 = op.into();
            let op2 = Instruction::from(code);
            assert_eq!(op, op2);
        }
    }
}
