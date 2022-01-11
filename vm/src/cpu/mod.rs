use log::{debug, info, trace};
use std::sync::atomic;
use std::sync::Arc;

use crate::device::basic_serial::BasicSerial;
use crate::device::timer::Timer;
use crate::memory::Memory;
use crate::num::Int;
use spec::Instruction;

pub struct Cpu {
    ip: u64,
    bp: u64,
    sp: u64,
    intr_mask: bool,
    irq: Arc<atomic::AtomicU8>,
    ivt: Vec<u64>,

    mem: Memory,
    serial: BasicSerial,
}

impl Cpu {
    pub fn new(mem: Memory, serial: BasicSerial) -> Self {
        let irq = Arc::new(atomic::AtomicU8::new(0));

        Timer::new(irq.clone()); // FIXME

        Self {
            ip: 0,
            bp: mem.size() as u64,
            sp: mem.size() as u64,
            intr_mask: false,
            irq,
            ivt: vec![0; 256],

            mem,
            serial,
        }
    }

    pub fn execute(&mut self) -> Result<(), ()> {
        if self.intr_mask && self.irq.load(atomic::Ordering::Relaxed) != 0 {
            return self.handle_interruption();
        }

        let ip = self.ip;
        let opcode = self.bus_read(ip);
        let op = Instruction::from(opcode);
        self.ip += 1;

        self.eval(op)
    }

    #[inline]
    fn handle_interruption(&mut self) -> Result<(), ()> {
        let irq = self.irq.load(atomic::Ordering::SeqCst);
        self.irq.store(0, atomic::Ordering::SeqCst);

        self.stack_push::<u64>(self.ip);
        self.stack_push::<u64>(self.bp);

        self.bp = self.sp;
        self.ip = self.ivt[irq as usize];
        trace!("interruption {}: jump to {:016X}", irq, self.ip);
        Ok(())
    }

    pub fn inspect_stack<T: Int>(&mut self) -> T {
        let mut bytes = T::Bytes::default();
        for (i, b) in bytes.as_mut().iter_mut().enumerate() {
            *b = self.bus_read(self.sp + i as u64);
        }
        T::from_le_bytes(bytes)
    }

    #[inline]
    fn bus_write(&mut self, addr: u64, data: u8) {
        if addr & 0x8000_0000_0000_0000 == 0 {
            self.mem.write(addr, data).expect("mem write");
        } else {
            use spec::MmioBase;
            const CPU_IVT_BASE: u64 = MmioBase::CpuIvt as u64;
            const CPU_IVT_END: u64 = CPU_IVT_BASE + 0x10000;
            const SERIAL_BASE: u64 = MmioBase::BasicSerial as u64;
            const SERIAL_END: u64 = SERIAL_BASE + 2;
            if CPU_IVT_BASE <= addr && addr < CPU_IVT_END {
                let irq = (addr & 0xFFFF) >> 8;
                let sh = (addr & 0xFF) * 8;
                self.ivt[irq as usize] &= !(0xFF << sh);
                self.ivt[irq as usize] |= (data as u64) << sh;
            } else if SERIAL_BASE <= addr && addr < SERIAL_END {
                self.serial.write(addr, data).expect("serial write");
            }
        }
    }

    #[inline]
    fn bus_read(&mut self, addr: u64) -> u8 {
        if addr & 0x8000_0000_0000_0000 == 0 {
            self.mem.read(addr).expect("mem read")
        } else {
            use spec::MmioBase;
            const CPU_IVT_BASE: u64 = MmioBase::CpuIvt as u64;
            const CPU_IVT_END: u64 = CPU_IVT_BASE + 0x10000;
            const SERIAL_BASE: u64 = MmioBase::BasicSerial as u64;
            const SERIAL_END: u64 = SERIAL_BASE + 2;
            if CPU_IVT_BASE <= addr && addr < CPU_IVT_END {
                let irq = (addr & 0xFFFF) >> 8;
                let sh = (addr & 0xFF) * 8;
                let v = self.ivt[irq as usize];
                ((v >> sh) & 0xFF) as u8
            } else if SERIAL_BASE <= addr && addr < SERIAL_END {
                self.serial.read(addr).expect("serial read")
            } else {
                panic!("invalid MMIO address");
            }
        }
    }

    fn set_intr_mask(&mut self, enable: bool) {
        if enable {
            trace!("interruption enabled");
        } else {
            trace!("interruption disabled");
        }
        self.intr_mask = enable;
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
            And08 => self.bit_and::<u8>(),
            And16 => self.bit_and::<u16>(),
            And32 => self.bit_and::<u32>(),
            And64 => self.bit_and::<u64>(),
            Or08 => self.bit_or::<u8>(),
            Or16 => self.bit_or::<u16>(),
            Or32 => self.bit_or::<u32>(),
            Or64 => self.bit_or::<u64>(),
            Xor08 => self.bit_xor::<u8>(),
            Xor16 => self.bit_xor::<u16>(),
            Xor32 => self.bit_xor::<u32>(),
            Xor64 => self.bit_xor::<u64>(),
            Not08 => self.bit_not::<u8>(),
            Not16 => self.bit_not::<u16>(),
            Not32 => self.bit_not::<u32>(),
            Not64 => self.bit_not::<u64>(),
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
            DisableIntr => self.set_intr_mask(false),
            EnableIntr => self.set_intr_mask(true),
            Abort => {
                info!("aborted");
                info!("IP={} ({:016X})", self.ip, self.ip);
                info!("SP={} ({:016X})", self.sp, self.sp);
                info!("BP={} ({:016X})", self.bp, self.bp);
                return Err(());
            }

            DebugComment => self.debug_comment(),
        }
        trace!("");
        Ok(())
    }

    #[inline]
    fn stack_push<T: Int>(&mut self, val: T) {
        let bytes = val.to_le_bytes();
        for &b in bytes.as_ref().iter().rev() {
            self.sp -= 1;
            self.bus_write(self.sp, b);
        }
        trace!("stack_push: addr={:?} val={:?}", self.sp, val);
    }
    #[inline]
    fn stack_pop<T: Int>(&mut self) -> T {
        let mut bytes = T::Bytes::default();
        for b in bytes.as_mut() {
            *b = self.bus_read(self.sp);
            self.sp += 1;
        }
        T::from_le_bytes(bytes)
    }

    #[inline]
    fn literal<T: Int>(&mut self) {
        let mut bytes = T::Bytes::default();
        let slice = bytes.as_mut();
        for b in slice.iter_mut() {
            *b = self.bus_read(self.ip);
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
    fn bit_and<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        trace!("and: lhs={}, rhs={}", lhs, rhs);
        self.stack_push::<T>(lhs & rhs);
    }

    #[inline]
    fn bit_or<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        trace!("or: lhs={}, rhs={}", lhs, rhs);
        self.stack_push::<T>(lhs | rhs);
    }

    #[inline]
    fn bit_xor<T: Int>(&mut self) {
        let rhs = self.stack_pop::<T>();
        let lhs = self.stack_pop::<T>();
        trace!("xor: lhs={}, rhs={}", lhs, rhs);
        self.stack_push::<T>(lhs ^ rhs);
    }

    #[inline]
    fn bit_not<T: Int>(&mut self) {
        let val = self.stack_pop::<T>();
        trace!("not: val={}", val);
        self.stack_push::<T>(!val);
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
            *b = self.bus_read(addr);
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
            self.bus_write(addr, b);
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
        if (cond & 1) == 1 {
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

    #[inline]
    fn debug_comment(&mut self) {
        let len = self.bus_read(self.ip);
        self.ip += 1;

        let mut bytes = vec![0; len as usize];
        for b in bytes.iter_mut() {
            *b = self.bus_read(self.ip);
            self.ip += 1;
        }
        let s = String::from_utf8(bytes).expect("invalid UTF-8");
        debug!("comment: {}", s);
    }
}

#[cfg(test)]
mod tests;
