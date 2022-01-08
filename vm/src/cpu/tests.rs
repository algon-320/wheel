use super::*;
use crate::device::basic_serial::BasicSerial;
use crate::memory::Memory;
use crate::num::Int;
use spec::Instruction as I;

enum TextElem {
    Ins(I),
    Data(Vec<u8>),
}
impl From<I> for TextElem {
    fn from(inst: I) -> Self {
        Self::Ins(inst)
    }
}
impl From<u8> for TextElem {
    fn from(x: u8) -> Self {
        Self::Data(x.to_le_bytes().into())
    }
}
impl From<u16> for TextElem {
    fn from(x: u16) -> Self {
        Self::Data(x.to_le_bytes().into())
    }
}
impl From<u32> for TextElem {
    fn from(x: u32) -> Self {
        Self::Data(x.to_le_bytes().into())
    }
}
impl From<u64> for TextElem {
    fn from(x: u64) -> Self {
        Self::Data(x.to_le_bytes().into())
    }
}

fn write_bytes(mem: &mut Memory, offset: u64, bytes: &[u8]) {
    let mut addr = offset;
    for &b in bytes {
        mem.write(addr, b).unwrap();
        addr += 1;
    }
}

fn write_text(mem: &mut Memory, offset: u64, text: &[TextElem]) {
    let mut bytes = Vec::new();
    for elem in text {
        match elem {
            TextElem::Ins(op) => {
                bytes.push((*op).into());
            }
            TextElem::Data(data) => {
                bytes.extend_from_slice(data);
            }
        }
    }
    write_bytes(mem, offset, &bytes);
}

fn read_int<T: Int>(mem: &Memory, addr: u64) -> T {
    let mut bytes = T::Bytes::default();
    for (i, b) in bytes.as_mut().iter_mut().enumerate() {
        *b = mem.read(addr + i as u64).unwrap();
    }
    T::from_le_bytes(bytes)
}

fn new_cpu(mem: Memory) -> Cpu {
    let serial = BasicSerial::new();
    Cpu::new(mem, serial)
}

#[test]
fn stack() {
    let mut cpu = new_cpu(Memory::new(0x1000));

    let old_sp = cpu.sp;
    cpu.stack_push::<u8>(1);
    assert_eq!(cpu.sp, old_sp - 1);
    cpu.stack_push::<u16>(2);
    assert_eq!(cpu.sp, old_sp - 1 - 2);
    cpu.stack_push::<u32>(3);
    assert_eq!(cpu.sp, old_sp - 1 - 2 - 4);
    cpu.stack_push::<u64>(4);
    assert_eq!(cpu.sp, old_sp - 1 - 2 - 4 - 8);

    assert_eq!(cpu.stack_pop::<u64>(), 4);
    assert_eq!(cpu.stack_pop::<u32>(), 3);
    assert_eq!(cpu.stack_pop::<u16>(), 2);
    assert_eq!(cpu.stack_pop::<u8>(), 1);
    assert_eq!(cpu.sp, old_sp);
}

#[test]
fn lit08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lit08.into(), (123 as u8).into()]);
    let mut cpu = new_cpu(mem);
    for _ in 0..2 {
        cpu.execute().unwrap();
    }
    assert_eq!(cpu.stack_pop::<u8>(), 123);
}

#[test]
fn lit16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lit16.into(), (123 as u16).into()]);
    let mut cpu = new_cpu(mem);
    for _ in 0..2 {
        cpu.execute().unwrap();
    }
    assert_eq!(cpu.stack_pop::<u16>(), 123);
}

#[test]
fn lit32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lit32.into(), (123 as u32).into()]);
    let mut cpu = new_cpu(mem);
    for _ in 0..2 {
        cpu.execute().unwrap();
    }
    assert_eq!(cpu.stack_pop::<u32>(), 123);
}

#[test]
fn lit64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lit64.into(), (123 as u64).into()]);
    let mut cpu = new_cpu(mem);
    for _ in 0..2 {
        cpu.execute().unwrap();
    }
    assert_eq!(cpu.stack_pop::<u64>(), 123);
}

#[test]
fn drop08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Drop08.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u8>(12);
    cpu.stack_push::<u8>(23);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 12);
}

#[test]
fn drop16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Drop16.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u16>(123);
    cpu.stack_push::<u16>(456);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 123);
}

#[test]
fn drop32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Drop32.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u32>(123);
    cpu.stack_push::<u32>(456);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 123);
}

#[test]
fn drop64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Drop64.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(123);
    cpu.stack_push::<u64>(456);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 123);
}

#[test]
fn add08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Add08.into(), I::Add08.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u8>(11);
    cpu.stack_push::<u8>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 33);

    cpu.stack_push::<u8>(0xFF);
    cpu.stack_push::<u8>(0x01);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn add16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Add16.into(), I::Add16.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u16>(11);
    cpu.stack_push::<u16>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 33);

    cpu.stack_push::<u16>(0xFFFF);
    cpu.stack_push::<u16>(0x0001);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 0);
}

#[test]
fn add32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Add32.into(), I::Add32.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u32>(11);
    cpu.stack_push::<u32>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 33);

    cpu.stack_push::<u32>(0xFFFFFFFF);
    cpu.stack_push::<u32>(0x00000001);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 0);
}

#[test]
fn add64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Add64.into(), I::Add64.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u64>(11);
    cpu.stack_push::<u64>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 33);

    cpu.stack_push::<u64>(0xFFFFFFFFFFFFFFFF);
    cpu.stack_push::<u64>(0x0000000000000001);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 0);
}

#[test]
fn sub08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Sub08.into(), I::Sub08.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u8>(123);
    cpu.stack_push::<u8>(23);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 100);

    cpu.stack_push::<u8>(0);
    cpu.stack_push::<u8>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0xFF);
}

#[test]
fn sub16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Sub16.into(), I::Sub16.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u16>(123);
    cpu.stack_push::<u16>(23);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 100);

    cpu.stack_push::<u16>(0);
    cpu.stack_push::<u16>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 0xFFFF);
}

#[test]
fn sub32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Sub32.into(), I::Sub32.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u32>(123);
    cpu.stack_push::<u32>(23);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 100);

    cpu.stack_push::<u32>(0);
    cpu.stack_push::<u32>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 0xFFFFFFFF);
}

#[test]
fn sub64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Sub64.into(), I::Sub64.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u64>(123);
    cpu.stack_push::<u64>(23);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 100);

    cpu.stack_push::<u64>(0);
    cpu.stack_push::<u64>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 0xFFFFFFFFFFFFFFFF);
}

#[test]
fn mul08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Mul08.into(), I::Mul08.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u8>(11);
    cpu.stack_push::<u8>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 242);

    cpu.stack_push::<u8>(0xFF);
    cpu.stack_push::<u8>(16);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0xF0);
}

#[test]
fn mul16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Mul16.into(), I::Mul16.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u16>(11);
    cpu.stack_push::<u16>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 242);

    cpu.stack_push::<u16>(0xFFFF);
    cpu.stack_push::<u16>(16);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 0xFFF0);
}

#[test]
fn mul32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Mul32.into(), I::Mul32.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u32>(11);
    cpu.stack_push::<u32>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 242);

    cpu.stack_push::<u32>(0xFFFFFFFF);
    cpu.stack_push::<u32>(16);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 0xFFFFFFF0);
}

#[test]
fn mul64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Mul64.into(), I::Mul64.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u64>(11);
    cpu.stack_push::<u64>(22);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 242);

    cpu.stack_push::<u64>(0xFFFFFFFFFFFFFFFF);
    cpu.stack_push::<u64>(16);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 0xFFFFFFFFFFFFFFF0);
}

#[test]
fn div08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Div08.into(), I::Div08.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u8>(10);
    cpu.stack_push::<u8>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 5);

    cpu.stack_push::<u8>(10);
    cpu.stack_push::<u8>(3);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 3);
}

#[test]
fn div16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Div16.into(), I::Div16.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u16>(10);
    cpu.stack_push::<u16>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 5);

    cpu.stack_push::<u16>(10);
    cpu.stack_push::<u16>(3);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 3);
}

#[test]
fn div32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Div32.into(), I::Div32.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u32>(10);
    cpu.stack_push::<u32>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 5);

    cpu.stack_push::<u32>(10);
    cpu.stack_push::<u32>(3);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 3);
}

#[test]
fn div64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Div64.into(), I::Div64.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u64>(10);
    cpu.stack_push::<u64>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 5);

    cpu.stack_push::<u64>(10);
    cpu.stack_push::<u64>(3);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 3);
}

#[test]
fn eq08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Eq08.into(), I::Eq08.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u8>(123);
    cpu.stack_push::<u8>(123);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    cpu.stack_push::<u8>(123);
    cpu.stack_push::<u8>(122);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn eq16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Eq16.into(), I::Eq16.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u16>(123);
    cpu.stack_push::<u16>(123);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    cpu.stack_push::<u16>(123);
    cpu.stack_push::<u16>(122);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn eq32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Eq32.into(), I::Eq32.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u32>(123);
    cpu.stack_push::<u32>(123);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    cpu.stack_push::<u32>(123);
    cpu.stack_push::<u32>(122);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn eq64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Eq64.into(), I::Eq64.into()]);
    let mut cpu = new_cpu(mem);

    cpu.stack_push::<u64>(123);
    cpu.stack_push::<u64>(123);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    cpu.stack_push::<u64>(123);
    cpu.stack_push::<u64>(122);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn lt08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lt08.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u8>(1);
    cpu.stack_push::<u8>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u8>(2);
    cpu.stack_push::<u8>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u8>(2);
    cpu.stack_push::<u8>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn lt16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lt16.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u16>(1);
    cpu.stack_push::<u16>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u16>(2);
    cpu.stack_push::<u16>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u16>(2);
    cpu.stack_push::<u16>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn lt32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lt32.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u32>(1);
    cpu.stack_push::<u32>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u32>(2);
    cpu.stack_push::<u32>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u32>(2);
    cpu.stack_push::<u32>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn lt64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Lt64.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(1);
    cpu.stack_push::<u64>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(2);
    cpu.stack_push::<u64>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(2);
    cpu.stack_push::<u64>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);
}

#[test]
fn gt08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Gt08.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u8>(1);
    cpu.stack_push::<u8>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u8>(2);
    cpu.stack_push::<u8>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u8>(2);
    cpu.stack_push::<u8>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);
}

#[test]
fn gt16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Gt16.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u16>(1);
    cpu.stack_push::<u16>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u16>(2);
    cpu.stack_push::<u16>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u16>(2);
    cpu.stack_push::<u16>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);
}

#[test]
fn gt32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Gt32.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u32>(1);
    cpu.stack_push::<u32>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u32>(2);
    cpu.stack_push::<u32>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u32>(2);
    cpu.stack_push::<u32>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);
}

#[test]
fn gt64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Gt64.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(1);
    cpu.stack_push::<u64>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(2);
    cpu.stack_push::<u64>(2);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 0);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(2);
    cpu.stack_push::<u64>(1);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 1);
}

#[test]
fn load08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Load08.into()]);
    mem.write(0x100, 123).unwrap();
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u8>(), 123);
}

#[test]
fn load16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Load16.into()]);
    write_bytes(&mut mem, 0x100, &123u16.to_le_bytes());
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u16>(), 123);
}

#[test]
fn load32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Load32.into()]);
    write_bytes(&mut mem, 0x100, &123u32.to_le_bytes());
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u32>(), 123);
}

#[test]
fn load64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Load64.into()]);
    write_bytes(&mut mem, 0x100, &123u64.to_le_bytes());
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), 123);
}

#[test]
fn store08() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Store08.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u8>(123);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(read_int::<u8>(&cpu.mem, 0x100), 123);
}

#[test]
fn store16() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Store16.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u16>(123);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(read_int::<u16>(&cpu.mem, 0x100), 123);
}

#[test]
fn store32() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Store32.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u32>(123);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(read_int::<u32>(&cpu.mem, 0x100), 123);
}

#[test]
fn store64() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Store64.into()]);
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(123);
    cpu.stack_push::<u64>(0x100);
    cpu.execute().unwrap();
    assert_eq!(read_int::<u64>(&cpu.mem, 0x100), 123);
}

#[test]
fn jump() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0x000, &[I::Jump.into()]);
    write_text(
        &mut mem,
        0x100,
        &[
            I::Lit08.into(),
            11u8.into(),
            I::Lit08.into(),
            22u8.into(),
            I::Add08.into(),
        ],
    );
    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u64>(0x100);
    assert_eq!(cpu.ip, 0x000);
    cpu.execute().unwrap(); // Jump
    assert_eq!(cpu.ip, 0x100);
    cpu.execute().unwrap(); // Lit08
    cpu.execute().unwrap(); // Lit08
    cpu.execute().unwrap(); // Add08
    assert_eq!(cpu.stack_pop::<u8>(), 33);
}

#[test]
fn jump_if() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0x000, &[I::JumpIf.into(), I::Mul08.into()]);
    write_text(&mut mem, 0x100, &[I::Add08.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u8>(3);
    cpu.stack_push::<u8>(5);
    cpu.stack_push::<u64>(0x100);
    cpu.stack_push::<u8>(1);
    assert_eq!(cpu.ip, 0x000);
    cpu.execute().unwrap(); // JumpIf
    assert_eq!(cpu.ip, 0x100);
    cpu.execute().unwrap(); // Add08
    assert_eq!(cpu.stack_pop::<u8>(), 8);

    let mut cpu = new_cpu(mem);
    cpu.stack_push::<u8>(3);
    cpu.stack_push::<u8>(5);
    cpu.stack_push::<u64>(0x100);
    cpu.stack_push::<u8>(0);
    assert_eq!(cpu.ip, 0x000);
    cpu.execute().unwrap(); // JumpIf
    assert_eq!(cpu.ip, 0x001);
    cpu.execute().unwrap(); // Mul08
    assert_eq!(cpu.stack_pop::<u8>(), 15);
}

#[test]
fn get_ip() {
    let mut mem = Memory::new(0x1000);
    write_text(
        &mut mem,
        0,
        &[I::Nop.into(), I::Nop.into(), I::Nop.into(), I::GetIp.into()],
    );
    let mut cpu = new_cpu(mem);
    cpu.execute().unwrap();
    cpu.execute().unwrap();
    cpu.execute().unwrap();
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), cpu.ip);
    assert_eq!(cpu.ip, 0x0004);
}

#[test]
fn get_bp() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::GetBp.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), cpu.bp);

    let mut cpu = new_cpu(mem);
    cpu.bp = 0x500;
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), cpu.bp);
    assert_eq!(cpu.bp, 0x500);
}

#[test]
fn set_bp() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::SetBp.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(0x500);
    cpu.execute().unwrap();
    assert_eq!(cpu.bp, 0x500);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(0x123);
    cpu.execute().unwrap();
    assert_eq!(cpu.bp, 0x123);
}

#[test]
fn get_sp() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::GetSp.into()]);

    let mut cpu = new_cpu(mem.clone());
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), cpu.bp);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u8>(0);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), cpu.bp - 1);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u16>(0);
    cpu.execute().unwrap();
    assert_eq!(cpu.stack_pop::<u64>(), cpu.bp - 2);
}

#[test]
fn set_sp() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::SetSp.into()]);

    mem.write(0x500, 0xAA).unwrap();
    mem.write(0x123, 0xBB).unwrap();

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(0x500);
    cpu.execute().unwrap();
    assert_eq!(cpu.sp, 0x500);
    assert_eq!(cpu.stack_pop::<u8>(), 0xAA);
    assert_eq!(cpu.sp, 0x500 + 1);

    let mut cpu = new_cpu(mem.clone());
    cpu.stack_push::<u64>(0x123);
    cpu.execute().unwrap();
    assert_eq!(cpu.sp, 0x123);
    assert_eq!(cpu.stack_pop::<u8>(), 0xBB);
    assert_eq!(cpu.sp, 0x123 + 1);
}

#[test]
fn abort() {
    let mut mem = Memory::new(0x1000);
    write_text(&mut mem, 0, &[I::Abort.into()]);
    let mut cpu = new_cpu(mem);
    assert!(cpu.execute().is_err());
}

#[test]
fn debug_comment() {
    let mut mem = Memory::new(0x1000);
    let s = "hello,world!".to_owned();
    write_text(
        &mut mem,
        0,
        &[
            I::DebugComment.into(),
            TextElem::Data(vec![s.len() as u8]),
            TextElem::Data(s.as_bytes().to_vec()),
        ],
    );
    let mut cpu = new_cpu(mem);
    cpu.execute().unwrap();
    assert_eq!(cpu.ip, 2 + s.len() as u64);
}
