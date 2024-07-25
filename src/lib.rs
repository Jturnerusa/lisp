use compiler::{
    ast::{self, Ast},
    bytecode, il,
};
use reader::{Reader, Sexpr};
use std::env;
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use vm::{OpCodeTable, Vm};

pub fn compile_file(
    path: &Path,
    il_compiler: &mut il::Compiler,
    ast_compiler: &mut ast::Compiler,
    vm: &mut Vm<&'static Sexpr<'static>>,
    opcode_table: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Box<dyn std::error::Error>> {
    il_compiler.set_current_module(None);

    let mut source = String::new();
    let mut file = match File::open(path) {
        Ok(f) => f,
        Err(e) => return Err(format!("failed to open {}: {e}", path.to_str().unwrap()).into()),
    };

    file.read_to_string(&mut source)?;

    let context = Box::leak(Box::new(reader::Context::new(
        source.as_str(),
        path.to_str().unwrap(),
    )));

    let reader = Reader::new(context);

    for expr in reader {
        let sexpr: &'static _ = Box::leak(Box::new(expr?));
        let ast = ast_compiler.compile(sexpr)?;

        if let Ast::Require(ast::Require { module, .. }) = ast {
            match find_module(module.as_str()) {
                Some(Ok(m)) => {
                    compile_file(m.as_path(), il_compiler, ast_compiler, vm, opcode_table)?;
                    continue;
                }
                Some(Err(e)) => return Err(e),
                None => return Err(format!("failed to find module: {module}").into()),
            }
        }

        let il = il_compiler.compile(&ast, vm, ast_compiler)?;
        bytecode::compile(&il, opcode_table)?;
    }

    Ok(())
}

pub fn find_module(name: &str) -> Option<Result<PathBuf, Box<dyn std::error::Error>>> {
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

                    if entry.path().as_path().file_stem()?.to_str().unwrap() == name {
                        return Some(Ok(entry.path()));
                    }
                }
            }
            None
        }
        Err(e) => Some(Err(format!("failed to read CARPET_LISP_PATH: {e}").into())),
    }
}
