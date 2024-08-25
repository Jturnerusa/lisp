use compiler::ast::Ast;
use core::fmt;
use error::FileSpan;
use reader::Reader;
use std::collections::HashMap;
use std::env;
use std::fs::{self, File};
use std::hash::{Hash, Hasher};
use std::io::Read;
use std::path::{Path, PathBuf};
use vm::{OpCodeTable, Vm};

#[derive(Debug)]
pub enum Error {
    Std(Box<dyn std::error::Error>),
    Spanned(Box<dyn error::Error>),
}

pub fn compile_file(
    path: &Path,
    files: &mut HashMap<u64, PathBuf>,
    ast_compiler: &mut compiler::ast::Compiler,
    tree_compiler: &mut compiler::tree::Compiler,
    vm: &mut Vm<FileSpan>,
    opcode_table: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    let absolute = fs::canonicalize(path).map_err(|e| Error::Std(Box::new(e)))?;
    let file_id = hash_path(absolute.as_path());
    let mut buff = String::new();
    let mut file = File::open(path).map_err(|e| Error::Std(Box::new(e)))?;

    files.insert(file_id, absolute);

    file.read_to_string(&mut buff)
        .map_err(|e| Error::Std(Box::new(e)))?;

    compile_source(
        buff.as_str(),
        file_id,
        files,
        ast_compiler,
        tree_compiler,
        vm,
        opcode_table,
    )
}

pub fn compile_source(
    source: &str,
    file_id: u64,
    files: &mut HashMap<u64, PathBuf>,
    ast_compiler: &mut compiler::ast::Compiler,
    tree_compiler: &mut compiler::tree::Compiler,
    vm: &mut Vm<FileSpan>,
    opcode_table: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    let reader = Reader::new(source, file_id);

    for expr in reader {
        let sexpr = expr.map_err(|e| Error::Spanned(Box::new(e)))?;

        let ast = ast_compiler
            .compile(&sexpr)
            .map_err(|e| Error::Spanned(Box::new(e)))?;

        if let Ast::EvalWhenCompile(eval_when_compile) = &ast {
            let mut opcode_table = OpCodeTable::new();

            for expr in &eval_when_compile.exprs {
                let tree = tree_compiler.compile(expr, vm, ast_compiler)?;

                compiler::bytecode::compile(&tree, &mut opcode_table)
                    .map_err(|e| Error::Spanned(Box::new(e)))?;
            }

            vm.eval(&opcode_table)
                .map_err(|e| Error::Spanned(Box::new(e)))?;

            continue;
        } else if let Ast::Require(require) = &ast {
            let path = PathBuf::from(require.module.clone());
            let module = match find_module(path.as_path()) {
                Some(Ok(module)) => module,
                Some(Err(e)) => return Err(Error::Std(e)),
                None => {
                    return Err(Error::Std(
                        format!("failed to load module {}", path.to_str().unwrap()).into(),
                    ))
                }
            };

            compile_file(
                module.as_path(),
                files,
                ast_compiler,
                tree_compiler,
                vm,
                opcode_table,
            )?;

            continue;
        }

        let tree = tree_compiler.compile(&ast, vm, ast_compiler)?;

        compiler::bytecode::compile(&tree, opcode_table)
            .map_err(|e| Error::Spanned(Box::new(e)))?;
    }

    Ok(())
}

pub fn display_error(
    error: &dyn error::Error,
    files: &HashMap<u64, PathBuf>,
    mut writer: impl std::io::Write,
) -> Result<(), Box<dyn std::error::Error>> {
    error.message(&mut writer);

    if let Some(span) = error.span() {
        let mut buff = String::new();
        let path = files[&span.id].as_path();
        let mut file = File::open(path)?;

        file.read_to_string(&mut buff)?;

        let line_number = buff
            .bytes()
            .filter(|byte| *byte == b'\n')
            .take(span.start)
            .count();
        let slice = &buff[span.start..span.stop];

        write!(
            writer,
            "\n{}:{}\n{}\n",
            path.to_str().unwrap(),
            line_number,
            slice
        )
        .unwrap();
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

pub fn hash_path(path: &Path) -> u64 {
    let mut hasher = std::hash::DefaultHasher::new();
    path.hash(&mut hasher);
    hasher.finish()
}

impl From<Box<dyn error::Error>> for Error {
    fn from(value: Box<dyn error::Error>) -> Self {
        Self::Spanned(value)
    }
}

impl From<Box<dyn std::error::Error>> for Error {
    fn from(value: Box<dyn std::error::Error>) -> Self {
        Self::Std(value)
    }
}
