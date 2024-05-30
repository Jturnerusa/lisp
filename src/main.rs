use compiler::Compiler;
use identity_hasher::IdentityHasher;
use reader::Reader;
use std::collections::HashMap;
use std::env;
use std::error::Error;
use std::fs::File;
use std::io::Read;
use vm::Vm;

fn main() -> Result<(), Box<dyn Error>> {
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();

    for arg in env::args().skip(1) {
        let file = File::open(arg)?;
        eval_file(file, &mut vm, &mut compiler)?;
    }

    Ok(())
}

fn eval_file(mut file: File, vm: &mut Vm, compiler: &mut Compiler) -> Result<(), Box<dyn Error>> {
    let mut buff = String::new();
    file.read_to_string(&mut buff)?;

    let reader = Reader::new(buff.as_str());
    let mut opcodes = Vec::new();
    let mut constants = HashMap::with_hasher(IdentityHasher::new());

    for read in reader {
        opcodes.clear();
        constants.clear();

        let value = read?;

        compiler.compile(&value, &mut opcodes, &mut constants)?;

        vm.load_constants(constants.values().cloned());
        vm.eval(opcodes.as_slice())?;
    }

    Ok(())
}
