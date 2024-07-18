use std::{
    env,
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};

use compiler::{ast, bytecode, il};
use reader::{Reader, Sexpr};
use vm::{OpCode, OpCodeTable, Vm};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut il_compiler = il::Compiler::new();
    let mut ast_compiler = ast::Compiler::new();
    let mut vm: Vm<&Sexpr<'_>> = Vm::new();

    for arg in env::args().skip(1) {
        let path = PathBuf::from(arg);

        disasm_file(path.as_path(), &mut il_compiler, &mut ast_compiler, &mut vm)?;
    }

    Ok(())
}

fn disasm_file<'a>(
    path: &Path,
    il_compiler: &mut il::Compiler,
    ast_compiler: &mut ast::Compiler,
    vm: &mut Vm<&'a Sexpr<'a>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut file = File::open(path)?;
    let mut buff = String::new();

    file.read_to_string(&mut buff)?;

    let context = Box::leak(Box::new(reader::Context::new(
        buff.as_str(),
        path.to_str().unwrap(),
    )));
    let reader = Reader::new(context);
    let mut opcode_table = OpCodeTable::new();

    for expr in reader {
        let sexpr: &'static _ = Box::leak(Box::new(expr?));

        let ast: &'static _ = Box::leak(Box::new(ast_compiler.compile(sexpr)?));
        let il: &'static _ = Box::leak(Box::new(il_compiler.compile(ast, vm, ast_compiler)?));

        bytecode::compile(il, &mut opcode_table)?;
    }

    println!("disassembling {}\n", path.to_str().unwrap());

    disasm(&opcode_table, 0);

    Ok(())
}

fn disasm(opcode_table: &OpCodeTable<&Sexpr>, depth: usize) {
    let indent = "  ".repeat(depth);

    for opcode in opcode_table.opcodes() {
        println!("{indent}{opcode:?}");

        if let OpCode::Lambda { body, .. } = opcode {
            disasm(body, depth + 1)
        }
    }
}
