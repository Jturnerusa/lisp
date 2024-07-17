use compiler::{ast, bytecode, il};
use reader::{Reader, Sexpr};
use std::{
    env,
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};
use vm::{OpCodeTable, Vm};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut il_compiler = compiler::il::Compiler::new();
    let mut ast_compiler = compiler::ast::Compiler::new();
    let mut vm = Vm::new();
    let mut opcode_table = OpCodeTable::new();

    native_functions::load_module(&mut vm);

    for arg in env::args().skip(1) {
        let path = PathBuf::from(arg);

        compile_file(
            path.as_path(),
            &mut il_compiler,
            &mut ast_compiler,
            &mut vm,
            &mut opcode_table,
        )?;
    }

    match vm.eval(&opcode_table) {
        Ok(_) => Ok(()),
        Err((error, sexpr)) => Err(format!("{sexpr:?}: {error}").into()),
    }
}

fn compile_file<'a>(
    path: &Path,
    il_compiler: &mut il::Compiler,
    ast_compiler: &mut ast::Compiler,
    vm: &mut Vm<&'a Sexpr<'_>>,
    opcode_table: &mut OpCodeTable<&'a Sexpr<'_>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut source = String::new();
    let mut file = File::open(path)?;

    file.read_to_string(&mut source)?;

    let context = Box::leak(Box::new(reader::Context::new(
        source.as_str(),
        path.to_str().unwrap(),
    )));

    let reader = Reader::new(context);

    for expr in reader {
        let sexpr: &'static _ = Box::leak(Box::new(expr?));
        let ast: &'static _ = Box::leak(Box::new(ast_compiler.compile(sexpr)?));
        let il: &'static _ = Box::leak(Box::new(il_compiler.compile(ast, vm, ast_compiler)?));
        bytecode::compile(il, opcode_table)?;
    }

    Ok(())
}
