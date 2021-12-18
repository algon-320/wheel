use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct CliOpt {
    #[structopt(parse(from_os_str))]
    bin: PathBuf,

    #[structopt(short = "o", default_value = "-", parse(from_os_str))]
    output: PathBuf,
}

fn main() {
    env_logger::init();

    let opt = CliOpt::from_args();
    println!("bin: {:?}", opt.bin);
    println!("output: {:?}", opt.output);

    let bin = std::fs::read(opt.bin).expect("read");
    let asm = disas(&bin);

    if opt.output.to_str() == Some("-") {
        println!("{}", asm);
    } else {
        std::fs::write(opt.output, asm).expect("write");
    }
}

pub fn disas(bin: &[u8]) -> String {
    use spec::Instruction as I;

    let mut buf = String::new();

    let mut iter = bin.iter().copied().enumerate();
    while let Some((addr, b)) = iter.next() {
        // FIXME: Ignore static data
        if b == 0xbb {
            continue;
        }

        let op = I::from(b);
        match op {
            I::Lit08 => {
                let mut data = (0_u8).to_le_bytes();
                for b in data.iter_mut() {
                    *b = iter.next().unwrap().1;
                }
                let data = u8::from_le_bytes(data);
                buf.push_str(&format!(
                    "0x{:016X}: \t{:?}\t{} (0x{:02X})\n",
                    addr, op, data, data
                ));
            }

            I::Lit16 => {
                let mut data = (0_u16).to_le_bytes();
                for b in data.iter_mut() {
                    *b = iter.next().unwrap().1;
                }
                let data = u16::from_le_bytes(data);
                buf.push_str(&format!(
                    "0x{:016X}: \t{:?}\t{} (0x{:04X})\n",
                    addr, op, data, data
                ));
            }

            I::Lit32 => {
                let mut data = (0_u32).to_le_bytes();
                for b in data.iter_mut() {
                    *b = iter.next().unwrap().1;
                }
                let data = u32::from_le_bytes(data);
                buf.push_str(&format!(
                    "0x{:016X}: \t{:?}\t{} (0x{:08X})\n",
                    addr, op, data, data
                ));
            }

            I::Lit64 => {
                let mut data = (0_u64).to_le_bytes();
                for b in data.iter_mut() {
                    *b = iter.next().unwrap().1;
                }
                let data = u64::from_le_bytes(data);
                buf.push_str(&format!(
                    "0x{:016X}: \t{:?}\t{} (0x{:016X})\n",
                    addr, op, data, data
                ));
            }

            _ => {
                buf.push_str(&format!("0x{:016X}: \t{:?}\n", addr, op));
            }
        }
    }

    buf
}
