#![feature(let_chains)]

use std::{env, path::PathBuf};
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
    let mut tree_compiler = compiler::tree::Compiler::new();
    let mut ast_compiler = compiler::ast::Compiler::new();
    let mut type_checker = compiler::types::Checker::new();
    let mut vm = Vm::new();
    let mut opcode_table = OpCodeTable::new();

    native_functions::load_module(&mut vm);

    lisp::compile_source(
        NATIVE_DECL_SOURCE,
        "native.lisp",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut type_checker,
        true,
        &mut vm,
        &mut opcode_table,
    )?;

    lisp::compile_source(
        BOOTSTRAP_SOURCE,
        "bootstrap.lisp",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut type_checker,
        false,
        &mut vm,
        &mut opcode_table,
    )?;

    for arg in env::args().skip(1).take_while(|s| s != "--") {
        let path = PathBuf::from(arg);

        lisp::compile_file(
            path.as_path(),
            &mut tree_compiler,
            &mut ast_compiler,
            &mut type_checker,
            true,
            &mut vm,
            &mut opcode_table,
        )?;
    }

    Ok(())
}
