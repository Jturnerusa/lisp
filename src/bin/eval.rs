#![feature(let_chains)]

use std::{env, path::PathBuf};
use vm::{OpCodeTable, Vm};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut il_compiler = compiler::il::Compiler::new();
    let mut ast_compiler = compiler::ast::Compiler::new();
    let mut vm = Vm::new();
    let mut opcode_table = OpCodeTable::new();

    native_functions::load_module(&mut vm);

    lisp::compile_file(
        PathBuf::from("lib/bootstrap/bootstrap.lisp").as_path(),
        &mut il_compiler,
        &mut ast_compiler,
        &mut vm,
        &mut opcode_table,
    )?;

    lisp::compile_file(
        PathBuf::from("lib/native/decl/native.lisp").as_path(),
        &mut il_compiler,
        &mut ast_compiler,
        &mut vm,
        &mut opcode_table,
    )?;

    for arg in env::args().skip(1).take_while(|s| s != "--") {
        let path = PathBuf::from(arg);

        lisp::compile_file(
            path.as_path(),
            &mut il_compiler,
            &mut ast_compiler,
            &mut vm,
            &mut opcode_table,
        )?;
    }

    match vm.eval(&opcode_table) {
        Ok(_) => Ok(()),
        Err((error, sexpr)) => Err(format!("{sexpr:?}:\n{error}").into()),
    }
}
