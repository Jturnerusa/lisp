use core::fmt;
use error::FileSpan;
use lisp::{compile_file, compile_source, display_error, hash_path};
use std::{
    collections::HashMap,
    env, fs,
    hash::{Hash, Hasher},
    path::PathBuf,
};
use vm::{Constant, OpCode, OpCodeTable, Vm};

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

    match compile_source(
        BOOTSTRAP_SOURCE,
        bootstrap_file_id,
        &mut files,
        &mut ast_compiler,
        &mut tree_compiler,
        &mut |_| Ok(()),
        &mut vm,
        &mut OpCodeTable::new(),
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

    compile_source(
        NATIVE_DECL_SOURCE,
        0,
        &mut files,
        &mut ast_compiler,
        &mut tree_compiler,
        &mut |_| Ok(()),
        &mut vm,
        &mut OpCodeTable::new(),
        &mut constants,
    )
    .unwrap();

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

    let constants_table = constants
        .iter()
        .map(|constant| {
            let hash = hash(&constant);
            (hash, constant.clone())
        })
        .collect::<HashMap<u64, Constant<FileSpan>>>();

    disasm(&opcode_table, &constants_table, 0);
}

fn disasm<D: fmt::Debug>(
    opcode_table: &OpCodeTable<D>,
    constants_table: &HashMap<u64, Constant<D>>,
    depth: usize,
) {
    let indent = " ".repeat(depth);

    for opcode in opcode_table.opcodes() {
        if let OpCode::Lambda(_, body) = opcode {
            println!("{indent}{opcode:?}");
            disasm(
                constants_table[body].as_opcodetable().unwrap(),
                constants_table,
                depth + 1,
            );
        } else {
            println!("{indent}{opcode:?}");
        }
    }
}

fn hash<T: Hash>(hash: T) -> u64 {
    let mut hasher = std::hash::DefaultHasher::new();
    hash.hash(&mut hasher);
    hasher.finish()
}
