use compiler::{
    ast::{self, Ast},
    bytecode, tree,
};
use reader::{Reader, Sexpr};
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::{env, error::Error};
use vm::{OpCodeTable, Vm};

pub fn compile_file(
    path: &Path,
    tree_compiler: &mut tree::Compiler,
    ast_compiler: &mut ast::Compiler,
    type_checker: &mut compiler::types::Checker,
    check_types: bool,
    vm: &mut Vm<&'static Sexpr<'static>>,
    opcode_table: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut source = String::new();
    let mut file = match File::open(path) {
        Ok(f) => f,
        Err(e) => return Err(format!("failed to open {}: {e}", path.to_str().unwrap()).into()),
    };

    file.read_to_string(&mut source)?;

    compile_source(
        source.as_str(),
        path.to_str().unwrap(),
        tree_compiler,
        ast_compiler,
        type_checker,
        check_types,
        vm,
        opcode_table,
    )
}

pub fn compile_source(
    source: &str,
    context: &str,
    tree_compiler: &mut tree::Compiler,
    ast_compiler: &mut ast::Compiler,
    type_checker: &mut compiler::types::Checker,
    check_types: bool,
    vm: &mut Vm<&'static Sexpr<'static>>,
    opcode_table: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Box<dyn Error>> {
    let context = Box::leak(Box::new(reader::Context::new(source, context)));

    let reader = Reader::new(context);

    for expr in reader {
        let sexpr: &'static _ = Box::leak(Box::new(expr?));
        let ast = ast_compiler.compile(sexpr)?;

        let il = tree_compiler.compile(&ast, vm, ast_compiler, &find_module as _)?;

        if let Ast::Decl(decl) = &ast {
            type_checker.decl(decl)?
        }

        match &il {
            tree::Il::Lambda(lambda) => match type_checker.check_lambda(lambda) {
                Err(e) if check_types => return Err(Box::new(e)),
                _ => (),
            },
            tree::Il::Def(def) => match type_checker.check_def(def) {
                Err(e) if check_types => return Err(Box::new(e)),
                _ => (),
            },
            _ => (),
        }

        bytecode::compile(&il, opcode_table)?;
    }

    Ok(())
}

pub fn find_module(name: &Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>> {
    match env::var("CARPET_LISP_PATH") {
        Ok(paths) => {
            for path in paths.split(':') {
                for entry in match fs::read_dir(path) {
                    Ok(r) => r,
                    Err(e) => {
                        return Some(Err(format!("failed to read directory {path}: {e}").into()))
                    }
                } {
                    let entry = match entry {
                        Ok(entry) => entry,
                        Err(e) => {
                            return Some(Err(format!("failed to read dir entry: {e}").into()))
                        }
                    };

                    dbg!(&entry.file_name());

                    if entry.path().as_path().file_stem()? == name {
                        return Some(Ok(entry.path()));
                    }
                }
            }
            None
        }
        Err(e) => Some(Err(format!("failed to read CARPET_LISP_PATH: {e}").into())),
    }
}
