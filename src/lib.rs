use compiler::{
    ast::{self, Ast},
    bytecode,
    tree::{self, Il},
};
use reader::{Reader, Sexpr};
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::{env, error::Error};
use vm::{OpCodeTable, Vm};

type CheckTypes = dyn Fn(&Il, &mut compiler::types::Checker) -> Result<(), Box<dyn Error>>;

pub fn compile_file(
    path: &Path,
    tree_compiler: &mut tree::Compiler,
    ast_compiler: &mut ast::Compiler,
    type_checker: &mut compiler::types::Checker,
    check_types: &CheckTypes,
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

#[allow(clippy::too_many_arguments)]
pub fn compile_source(
    source: &str,
    context: &str,
    tree_compiler: &mut tree::Compiler,
    ast_compiler: &mut ast::Compiler,
    type_checker: &mut compiler::types::Checker,
    check_types: &CheckTypes,
    vm: &mut Vm<&'static Sexpr<'static>>,
    opcode_table: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Box<dyn Error>> {
    let context = Box::leak(Box::new(reader::Context::new(source, context)));

    let reader = Reader::new(context);

    for expr in reader {
        let sexpr: &'static _ = Box::leak(Box::new(expr?));
        let ast = ast_compiler.compile(sexpr)?;

        if let Ast::EvalWhenCompile(eval_when_compile) = &ast {
            let mut opcode_table = OpCodeTable::new();

            for expr in &eval_when_compile.exprs {
                let tree = tree_compiler.compile(expr, vm, ast_compiler)?;

                check_types(&tree, type_checker)?;

                bytecode::compile(&tree, &mut opcode_table)?;
            }

            match vm.eval(&opcode_table) {
                Ok(()) => (),
                Err((error, sexpr)) => return Err(format!("{error}\n{sexpr}").into()),
            }

            continue;
        } else if let Ast::Require(require) = &ast {
            let path = PathBuf::from(require.module.as_str());

            let module = match find_module(path.as_path()) {
                Some(Ok(m)) => m,
                Some(Err(e)) => return Err(e),
                None => {
                    return Err(format!("failed to find module {}", require.module.as_str()).into())
                }
            };

            compile_file(
                module.as_path(),
                tree_compiler,
                ast_compiler,
                type_checker,
                check_types,
                vm,
                opcode_table,
            )?;

            continue;
        } else if let Ast::Decl(decl) = &ast {
            type_checker.decl(decl).unwrap()
        }

        let tree = tree_compiler.compile(&ast, vm, ast_compiler)?;

        check_types(&tree, type_checker)?;

        bytecode::compile(&tree, opcode_table)?;
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
