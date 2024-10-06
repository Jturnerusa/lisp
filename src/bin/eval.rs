use lisp::{compile_file, compile_source, display_error, hash_path};
use std::{collections::HashMap, env, fs, path::PathBuf};
use vm::{OpCodeTable, Vm};

static BOOTSTRAP_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/bootstrap/bootstrap.lisp");

static BOOTSTRAP_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/bootstrap/bootstrap.lisp"
));

static NATIVE_DECL_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/lib/native/decl/native.lisp"
));

fn main() {
    let mut ast_compiler = compiler::ast::Compiler::new();
    let mut tree_compiler = compiler::tree::Compiler::new();
    let mut vm = Vm::new();
    let mut opcode_table = OpCodeTable::new();
    let mut constants = Vec::new();
    let mut files = HashMap::new();

    native_functions::load_module(&mut vm);

    let bootstrap_path = fs::canonicalize(BOOTSTRAP_PATH).unwrap();
    let bootstrap_file_id = hash_path(bootstrap_path.as_path());

    files.insert(bootstrap_file_id, bootstrap_path);

    compile_source(
        NATIVE_DECL_SOURCE,
        0,
        &mut files,
        &mut ast_compiler,
        &mut tree_compiler,
        &mut |_| Ok(()),
        &mut vm,
        &mut opcode_table,
        &mut constants,
    )
    .unwrap();

    match compile_source(
        BOOTSTRAP_SOURCE,
        bootstrap_file_id,
        &mut files,
        &mut ast_compiler,
        &mut tree_compiler,
        &mut |_| Ok(()),
        &mut vm,
        &mut opcode_table,
        &mut constants,
    ) {
        Ok(_) => (),
        Err(lisp::Error::Std(error)) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
        Err(lisp::Error::Spanned(error)) => {
            display_error(&*error, &files, &mut std::io::stderr()).unwrap();
            std::process::exit(1);
        }
    }

    for arg in env::args().skip(1).take_while(|arg| !arg.starts_with("--")) {
        let path = PathBuf::from(arg);

        match compile_file(
            path.as_path(),
            &mut files,
            &mut ast_compiler,
            &mut tree_compiler,
            &mut |_| Ok(()),
            &mut vm,
            &mut opcode_table,
            &mut constants,
        ) {
            Ok(_) => (),
            Err(lisp::Error::Std(error)) => {
                eprintln!("{error}");
                std::process::exit(1);
            }
            Err(lisp::Error::Spanned(error)) => {
                display_error(&*error, &files, &mut std::io::stderr()).unwrap();
                std::process::exit(1)
            }
        }
    }

    for constant in constants {
        vm.load_constant(constant);
    }

    match vm.eval(&opcode_table) {
        Ok(_) => (),
        Err(error) => {
            display_error(&error, &files, &mut std::io::stderr()).unwrap();
            std::process::exit(1);
        }
    }
}
