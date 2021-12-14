mod cpu;
mod memory;
mod num;

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidAddress,
}

use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct CliOpt {
    /// path to the binary file to be executed
    #[structopt(name = "bin", parse(from_os_str))]
    bin: PathBuf,

    /// memory size in bytes
    #[structopt(short = "m", long = "mem", default_value = "4096")]
    memory_size: usize,

    #[structopt(long = "debug")]
    debug: bool,
}

use cpu::Cpu;
use memory::Memory;

fn main() {
    env_logger::init();

    let opt = CliOpt::from_args();
    let bin = std::fs::read(&opt.bin).unwrap();

    log::info!("memory size: {}", opt.memory_size);
    let mut mem = Memory::new(opt.memory_size);
    for (i, &byte) in bin.iter().enumerate() {
        mem.write(i as u64, byte).unwrap();
    }

    let mut cpu = Cpu::new(mem);
    while cpu.execute().is_ok() {
        if opt.debug {
            debug_repl(&mut cpu);
        }
    }

    // FIXME: not necessarily the return value is 64-bit
    println!("{}", cpu.inspect_stack::<u64>());
}

fn debug_repl(cpu: &mut Cpu) {
    use std::io::{stdin, stdout, Write};
    loop {
        print!("> ");
        stdout().flush().unwrap();

        let mut cmd = String::new();
        stdin().read_line(&mut cmd).unwrap();

        match cmd.as_str().trim() {
            "p08" => {
                let val = cpu.inspect_stack::<u8>();
                println!("{} (0x{:02X})", val, val);
            }
            "p16" => {
                let val = cpu.inspect_stack::<u16>();
                println!("{} (0x{:04X})", val, val);
            }
            "p32" => {
                let val = cpu.inspect_stack::<u32>();
                println!("{} (0x{:08X})", val, val);
            }
            "p64" => {
                let val = cpu.inspect_stack::<u64>();
                println!("{} (0x{:016X})", val, val);
            }
            _ => break,
        }
    }
}
