mod compiler;
mod error;
mod expr;
mod parser;
mod prog;
mod ty;

use crate::error::Error;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct CliOpt {
    #[structopt(parse(from_os_str))]
    source: PathBuf,

    #[structopt(short = "o", default_value = "out.bin", parse(from_os_str))]
    output: PathBuf,
}

fn main() {
    env_logger::init();

    let opt = CliOpt::from_args();
    println!("source: {:?}", opt.source);
    println!("output: {:?}", opt.output);

    let source = std::fs::read_to_string(opt.source).expect("read_to_string");
    match compile(&source) {
        Ok(text) => {
            std::fs::write(opt.output, text).expect("write");
        }
        Err(err) => {
            eprintln!("[error] {:?}", err);
            std::process::exit(1);
        }
    }
}

pub fn compile(source: &str) -> Result<Vec<u8>, Error> {
    let mut program = parser::parse_program(&source)?;
    ty::type_tree(&mut program)?;
    Ok(compiler::compile(program))
}
