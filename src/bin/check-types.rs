#![feature(let_chains)]

use compiler::tree::Il;
use std::{env, error::Error, path::PathBuf};
use vm::{OpCodeTable, Vm};

static BOOTSTRAP_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/bootstrap/bootstrap.lisp"
));

static NATIVE_DECL_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/native/decl/native.lisp"
));

fn main() {
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
        &mut check_defs as _,
        &mut vm,
        &mut opcode_table,
    )
    .unwrap();

    lisp::compile_source(
        BOOTSTRAP_SOURCE,
        "bootstrap.lisp",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut type_checker,
        &mut check_defs as _,
        &mut vm,
        &mut opcode_table,
    )
    .unwrap();

    let check_type_function = if env::args().skip(1).any(|arg| arg == "--machine-readable") {
        &report_errors as _
    } else {
        &die_on_error as _
    };

    for arg in env::args().skip(1).filter(|s| !s.starts_with("--")) {
        let path = PathBuf::from(arg);

        match lisp::compile_file(
            path.as_path(),
            &mut tree_compiler,
            &mut ast_compiler,
            &mut type_checker,
            check_type_function,
            &mut vm,
            &mut opcode_table,
        ) {
            Ok(()) => continue,
            Err(e) => {
                eprintln!("{e}");
                return;
            }
        }
    }
}

fn check_defs(il: &Il, type_checker: &mut compiler::types::Checker) -> Result<(), Box<dyn Error>> {
    if let Il::Def(def) = il {
        let _ = type_checker.check_def(def);
    }
    Ok(())
}

fn die_on_error(
    il: &Il,
    type_checker: &mut compiler::types::Checker,
) -> Result<(), Box<dyn Error>> {
    match il {
        Il::Def(def) => match type_checker.check_def(def) {
            Ok(_) => Ok(()),
            Err(e) => Err(Box::new(e)),
        },
        Il::Lambda(lambda) => match type_checker.check_lambda(lambda) {
            Ok(_) => Ok(()),
            Err(e) => Err(Box::new(e)),
        },
        _ => Ok(()),
    }
}

fn report_errors(
    il: &Il,
    type_checker: &mut compiler::types::Checker,
) -> Result<(), Box<dyn Error>> {
    match il {
        Il::Def(def) => match type_checker.check_def(def) {
            Ok(_) => Ok(()),
            Err(e) => {
                report_error(&e);
                Ok(())
            }
        },
        Il::Lambda(lambda) => match type_checker.check_lambda(lambda) {
            Ok(_) => Ok(()),
            Err(e) => {
                report_error(&e);
                Ok(())
            }
        },
        _ => Ok(()),
    }
}

fn report_error(error: &compiler::types::Error) {
    match error {
        compiler::types::Error::Expected {
            expected,
            received,
            sexpr,
        } => {
            eprintln!(
                "{}:{}:3 expected: {}, recieved: {}",
                sexpr.context().display(),
                sexpr.line_number(),
                expected,
                received
            );
        }
        compiler::types::Error::Unexpected { sexpr } => {
            eprintln!(
                "{}:{}:3 unexpected type",
                sexpr.context().display(),
                sexpr.line_number(),
            );
        }
        compiler::types::Error::Invalid { sexpr } => {
            eprintln!(
                "{}:{}:3 invalid type",
                sexpr.context().display(),
                sexpr.line_number(),
            );
        }
        compiler::types::Error::Arity { sexpr } => {
            eprintln!(
                "{}:{}:3 incorrect arity",
                sexpr.context().display(),
                sexpr.line_number()
            );
        }
        compiler::types::Error::Narrow { sexpr } => {
            eprintln!(
                "{}:{}:3 can't narrow non-union types",
                sexpr.context().display(),
                sexpr.line_number()
            )
        }
        compiler::types::Error::None { sexpr } => {
            eprintln!(
                "{}:{}:0 unable to resolve type",
                sexpr.context().display(),
                sexpr.line_number()
            )
        }
        compiler::types::Error::Alias { sexpr } => {
            eprintln!(
                "{}:{}:3 unknown type alias",
                sexpr.context().display(),
                sexpr.line_number()
            )
        }
        compiler::types::Error::Global { sexpr } => {
            eprintln!(
                "{}:{}:3 unknown global variable",
                sexpr.context().display(),
                sexpr.line_number()
            )
        }
    }
}
