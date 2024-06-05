use compiler::Compiler;
use identity_hasher::IdentityHasher;
use reader::Reader;
use std::collections::HashMap;
use std::env;
use std::error::Error;
use std::fs::File;
use std::io::Read;
use vm::{Constant, OpCode, Vm};

fn main() -> Result<(), Box<dyn Error>> {
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();
    let mut opcodes = Vec::new();
    let mut constants = HashMap::with_hasher(IdentityHasher::new());

    native_functions::load_module(&mut vm);

    for arg in env::args().skip(1) {
        let file = File::open(arg)?;
        compile_file(file, &mut compiler, &mut opcodes, &mut constants)?;
    }

    vm.load_constants(constants.into_values());
    vm.eval(opcodes.as_slice())?;

    Ok(())
}

fn compile_file(
    mut file: File,
    compiler: &mut Compiler,
    opcodes: &mut Vec<OpCode>,
    constants: &mut HashMap<u64, Constant, IdentityHasher>,
) -> Result<(), Box<dyn Error>> {
    let mut buff = String::new();
    file.read_to_string(&mut buff)?;

    let reader = Reader::new(buff.as_str());

    for read in reader {
        let value = read?;
        compiler.compile(&value, opcodes, constants)?;
    }

    Ok(())
}
