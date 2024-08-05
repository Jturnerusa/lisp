use std::{
    env,
    path::{PathBuf},
};

use compiler::{ast, il};
use reader::{Sexpr};
use vm::{OpCode, OpCodeTable, Vm};

static BOOTSTRAP_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/bootstrap/bootstrap.lisp"
));

static NATIVE_DECL_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/native/decl/native.lisp"
));

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut il_compiler = il::Compiler::new();
    let mut ast_compiler = ast::Compiler::new();
    let mut vm: Vm<&Sexpr<'_>> = Vm::new();
    let mut opcode_table = OpCodeTable::new();

    lisp::compile_source(
        BOOTSTRAP_SOURCE,
        "bootstrap.lisp",
        &mut il_compiler,
        &mut ast_compiler,
        &mut vm,
        &mut opcode_table,
    )?;

    lisp::compile_source(
        NATIVE_DECL_SOURCE,
        "native.lisp",
        &mut il_compiler,
        &mut ast_compiler,
        &mut vm,
        &mut opcode_table,
    )?;

    for arg in env::args().skip(1) {
        let path = PathBuf::from(arg);

        let mut opcode_table = OpCodeTable::new();

        lisp::compile_file(
            path.as_path(),
            &mut il_compiler,
            &mut ast_compiler,
            &mut vm,
            &mut opcode_table,
        )?;

        disasm(&opcode_table, 0);
    }

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
