#![feature(let_chains)]

use reader::Sexpr;
use std::{env, ops::Range, path::PathBuf};
use vm::{OpCodeTable, Vm};

static BOOTSTRAP_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/bootstrap/bootstrap.lisp"
));

static NATIVE_DECL_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/native/decl/native.lisp"
));

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut il_compiler = compiler::il::Compiler::new();
    let mut ast_compiler = compiler::ast::Compiler::new();
    let mut vm = Vm::new();
    let mut opcode_table = OpCodeTable::new();

    native_functions::load_module(&mut vm);

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
