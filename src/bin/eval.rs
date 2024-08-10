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
    let mut tree_compiler = compiler::tree::Compiler::new();
    let mut ast_compiler = compiler::ast::Compiler::new();
    let mut vm = Vm::new();
    let mut opcode_table = OpCodeTable::new();

    native_functions::load_module(&mut vm);

    lisp::compile_source(
        NATIVE_DECL_SOURCE,
        "native.lisp",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut vm,
        &mut opcode_table,
    )?;

    lisp::compile_source(
        BOOTSTRAP_SOURCE,
        "bootstrap.lisp",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut vm,
        &mut opcode_table,
    )?;

    for arg in env::args().skip(1).take_while(|s| s != "--") {
        let path = PathBuf::from(arg);

        lisp::compile_file(
            path.as_path(),
            &mut tree_compiler,
            &mut ast_compiler,
            &mut vm,
            &mut opcode_table,
        )?;
    }

    match vm.eval(&opcode_table) {
        Ok(_) => Ok(()),
        Err((error, sexpr)) => {
            let span = get_span(sexpr);
            let line = get_line_number(sexpr);
            let source = get_source(sexpr, span);
            let display = sexpr.context().display();
            eprintln!("{display}:{line}: {error}\n{source}");
            Err(Box::new(error))
        }
    }
}

fn get_span(sexpr: &Sexpr) -> Range<usize> {
    match sexpr {
        Sexpr::List { list, .. } => list.first().unwrap().span().start - 1..sexpr.span().end,
        _ => sexpr.span(),
    }
}

fn get_line_number(sexpr: &Sexpr) -> usize {
    sexpr
        .context()
        .source()
        .bytes()
        .take(sexpr.span().start)
        .filter(|b| *b == b'\n')
        .count()
}

fn get_source<'sexpr>(sexpr: &'sexpr Sexpr, span: Range<usize>) -> &'sexpr str {
    &sexpr.context().source()[span]
}
