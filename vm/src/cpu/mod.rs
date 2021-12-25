use log::{info, trace};

use crate::memory::Memory;
use crate::num::Int;
use spec::Instruction;

pub struct Cpu {
    ip: u64,
    bp: u64,
    sp: u64,
    mem: Memory,
}

impl Cpu {
    pub fn new(mem: Memory) -> Self {
        Self {
            ip: 0,
            bp: mem.size() as u64,
            sp: mem.size() as u64,
            mem,
        }
    }

    pub fn execute(&mut self) -> Result<(), ()> {
        let ip = self.ip;
        let opcode = self.mem.read(ip).unwrap();
        let op = Instruction::from(opcode);
        self.ip += 1;

        self.eval(op)
    }

    pub fn inspect_stack<T: Int>(&mut self) -> T {
        let mut bytes = T::Bytes::default();
        for (i, b) in bytes.as_mut().iter_mut().enumerate() {
            *b = self.mem.read(self.sp + i as u64).expect("memory overflow");
        }
        T::from_le_bytes(bytes)
    }

    fn eval(&mut self, inst: Instruction) -> Result<(), ()> {
        trace!("inst={:?}", inst);
        use Instruction::*;
        match inst {
            Nop => {}
            Lit08 => self.literal::<u8>(),
            Lit16 => self.literal::<u16>(),
            Lit32 => self.literal::<u32>(),
            Lit64 => self.literal::<u64>(),
            Drop08 => self.drop_::<u8>(),
            Drop16 => self.drop_::<u16>(),
            Drop32 => self.drop_::<u32>(),
            Drop64 => self.drop_::<u64>(),
            Add08 => self.add::<u8>(),
            Add16 => self.add::<u16>(),
            Add32 => self.add::<u32>(),
            Add64 => self.add::<u64>(),
            Sub08 => self.sub::<u8>(),
            Sub16 => self.sub::<u16>(),
            Sub32 => self.sub::<u32>(),
            Sub64 => self.sub::<u64>(),
            Mul08 => self.mul::<u8>(),
            Mul16 => self.mul::<u16>(),
            Mul32 => self.mul::<u32>(),
            Mul64 => self.mul::<u64>(),
            Div08 => self.div::<u8>(),
            Div16 => self.div::<u16>(),
            Div32 => self.div::<u32>(),
            Div64 => self.div::<u64>(),
            Eq08 => self.eq::<u8>(),
            Eq16 => self.eq::<u16>(),
            Eq32 => self.eq::<u32>(),
            Eq64 => self.eq::<u64>(),
            Lt08 => self.lt::<u8>(),
            Lt16 => self.lt::<u16>(),
            Lt32 => self.lt::<u32>(),
            Lt64 => self.lt::<u64>(),
            Gt08 => self.gt::<u8>(),
            Gt16 => self.gt::<u16>(),
            Gt32 => self.gt::<u32>(),
            Gt64 => self.gt::<u64>(),
            Load08 => self.load::<u8>(),
            Load16 => self.load::<u16>(),
            Load32 => self.load::<u32>(),
            Load64 => self.load::<u64>(),
            Store08 => self.store::<u8>(),
            Store16 => self.store::<u16>(),
            Store32 => self.store::<u32>(),
            Store64 => self.store::<u64>(),
            Jump => self.jump(),
            JumpIf => self.jump_if(),
            GetIp => self.get_ip(),
            GetBp => self.get_bp(),
            SetBp => self.set_bp(),
            GetSp => self.get_sp(),
            SetSp => self.set_sp(),
            Abort => {
                info!("aborted");
                info!("IP={} ({:016X})", self.ip, self.ip);
                info!("SP={} ({:016X})", self.sp, self.sp);
                info!("BP={} ({:016X})", self.bp, self.bp);
                return Err(());
            }
        }
        trace!("");
        Ok(())
    }

    #[inline]
    fn stack_push<T: Int>(&mut self, val: T) {
        let bytes = val.to_le_bytes();
        for &b in bytes.as_ref().iter().rev() {
            self.sp -= 1;
            self.mem.write(self.sp, b).expect("memory overflow");
        }
        trace!("stack_push: addr={:?} val={:?}", self.sp, val);
    }
    #[inline]
    fn stack_pop<T: Int>(&mut self) -> T {
        let mut bytes = T::Bytes::default();
        for b in bytes.as_mut() {
            *b = self.mem.read(self.sp).expect("memory overflow");
            self.sp += 1;
        }
        T::from_le_bytes(bytes)
    }

    #[inline]
    fn literal<T: Int>(&mut self) {
        let mut bytes = T::Bytes::default();
        let slice = bytes.as_mut();
        for b in slice.iter_mut() {
            *b = self.mem.read(self.ip).unwrap();
            self.ip += 1;
        }
        let val = T::from_le_bytes(bytes);
        trace!("literal={}", &val);
        self.stack_push::<T>(val);
    }

    #[inline]
    fn drop_<T: Int>(&mut self) {
        self.stack_pop::<T>();
    }

    #[inline]
    fn add<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        let val = lhs.wrapping_add(&rhs);
        trace!("add: lhs={}, rhs={}", lhs, rhs);
        self.stack_push::<T>(val);
    }

    #[inline]
    fn mul<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        let val = lhs.wrapping_mul(&rhs);
        trace!("mul: lhs={}, rhs={}", lhs, rhs);
        self.stack_push::<T>(val);
    }

    #[inline]
    fn sub<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        let val = lhs.wrapping_sub(&rhs);
        trace!("sub: lhs={}, rhs={}", lhs, rhs);
        self.stack_push::<T>(val);
    }

    #[inline]
    fn div<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        trace!("div: lhs={}, rhs={}", lhs, rhs);
        self.stack_push::<T>(lhs / rhs);
    }

    #[inline]
    fn eq<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        trace!("eq: lhs={}, rhs={}", lhs, rhs);
        let val = if lhs == rhs { 1 } else { 0 };
        self.stack_push::<u8>(val);
    }

    #[inline]
    fn lt<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        trace!("lt: lhs={}, rhs={}", lhs, rhs);
        let val = if lhs < rhs { 1 } else { 0 };
        self.stack_push::<u8>(val);
    }

    #[inline]
    fn gt<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        trace!("gt: lhs={}, rhs={}", lhs, rhs);
        let val = if lhs > rhs { 1 } else { 0 };
        self.stack_push::<u8>(val);
    }

    #[inline]
    fn load<T: Int>(&mut self) {
        let mut addr = self.stack_pop::<u64>();
        let load_addr = addr;

        let mut bytes = T::Bytes::default();
        let slice = bytes.as_mut();
        for b in slice.iter_mut() {
            *b = self.mem.read(addr).expect("mem overflow");
            addr += 1;
        }

        let val = T::from_le_bytes(bytes);
        trace!("load: addr=0x{:X}, val={}", load_addr, val);
        self.stack_push::<T>(val)
    }

    #[inline]
    fn store<T: Int>(&mut self) {
        let mut addr = self.stack_pop::<u64>();
        let val = self.stack_pop::<T>();
        trace!("store: addr=0x{:X}, val={}", addr, val);

        let bytes = val.to_le_bytes();
        for &b in bytes.as_ref() {
            self.mem.write(addr, b).expect("mem overflow");
            addr += 1;
        }
    }

    #[inline]
    fn jump(&mut self) {
        let addr = self.stack_pop::<u64>();
        trace!("jump: 0x{:X}", addr);
        self.ip = addr;
    }

    #[inline]
    fn jump_if(&mut self) {
        let cond = self.stack_pop::<u8>();
        let addr = self.stack_pop::<u64>();
        trace!("jump_if: cond={}, addr={}", cond, addr);
        if cond != 0 {
            self.ip = addr;
        }
    }

    #[inline]
    fn get_ip(&mut self) {
        trace!("get_ip: ip={}", self.ip);
        self.stack_push::<u64>(self.ip);
    }

    #[inline]
    fn get_bp(&mut self) {
        trace!("get_bp: bp={}", self.bp);
        self.stack_push::<u64>(self.bp);
    }

    #[inline]
    fn set_bp(&mut self) {
        let new_bp = self.stack_pop::<u64>();
        trace!("set_bp: new_bp={}", new_bp);
        self.bp = new_bp;
    }

    #[inline]
    fn get_sp(&mut self) {
        trace!("get_sp: sp={}", self.sp);
        self.stack_push::<u64>(self.sp);
    }

    #[inline]
    fn set_sp(&mut self) {
        let new_sp = self.stack_pop::<u64>();
        trace!("set_sp: sp={}", new_sp);
        self.sp = new_sp;
    }
}

#[cfg(test)]
mod tests;
