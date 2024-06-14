use compiler::Compiler;
use identity_hasher::IdentityHasher;
use reader::ReaderWithLines;
use std::env;
use std::error::Error;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::{collections::HashMap, path::Path};
use vm::{Arity, Constant, OpCode, Vm};

fn main() -> Result<(), Box<dyn Error>> {
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();
    let mut opcodes = Vec::new();
    let mut constants = HashMap::with_hasher(IdentityHasher::new());

    native_functions::load_module(&mut vm);

    for arg in env::args().skip(1).filter(|arg| !arg.starts_with("--")) {
        eval_file(
            PathBuf::from(arg).as_path(),
            &mut compiler,
            &mut opcodes,
            &mut constants,
            &mut vm,
        )?;
    }

    Ok(())
}

fn eval_file(
    path: &Path,
    compiler: &mut Compiler,
    opcodes: &mut Vec<OpCode>,
    constants: &mut HashMap<u64, Constant, IdentityHasher>,
    vm: &mut Vm,
) -> Result<(), Box<dyn Error>> {
    let mut file = File::open(path)?;

    let mut buff = String::new();

    file.read_to_string(&mut buff)?;

    let reader = ReaderWithLines::new(buff.as_str());

    for (read, line) in reader {
        let value = read?;
        opcodes.clear();
        constants.clear();

        compiler.compile(&value, opcodes, constants)?;

        vm.load_constants(constants.values().cloned());

        match vm.eval(opcodes.as_slice()) {
            Ok(_) => continue,
            Err(e) => return Err(format!("{}:{}: {e}", path.to_str().unwrap(), line).into()),
        }
    }

    Ok(())
}

#[allow(dead_code)]
fn indent(depth: usize) -> String {
    " ".repeat(depth * 2)
}

#[allow(dead_code)]
fn disasm(opcodes: &[OpCode], constants: &HashMap<u64, Constant, IdentityHasher>, depth: usize) {
    for (i, opcode) in opcodes.iter().enumerate() {
        match opcode {
            OpCode::DefGlobal(global) => println!(
                "{}{i}: defglobal({})",
                indent(depth),
                constants.get(global).unwrap().as_symbol().unwrap()
            ),
            OpCode::GetGlobal(global) => println! {
                "{}{i}: getglobal({})",
                indent(depth),
                constants.get(global).unwrap().as_symbol().unwrap()
            },
            OpCode::GetLocal(local) => println! {
                "{}{i}: getlocal({local})",
                indent(depth)
            },
            OpCode::SetLocal(local) => println! {
                "{}{i}: setlocal({local})",
                indent(depth)
            },
            OpCode::GetUpValue(u) => println!("{}{i}: getupvalue({u})", indent(depth)),
            OpCode::SetUpValue(u) => println!("{}{i}: setupvalue({u})", indent(depth)),
            OpCode::CreateUpValue(u) => println!("{}{i}: createupvalue({u:?})", indent(depth)),
            OpCode::Add => println!("{}{i}: add", indent(depth)),
            OpCode::Sub => println!("{}{i}: sub", indent(depth)),
            OpCode::Mul => println!("{}{i}: mul", indent(depth)),
            OpCode::Div => println!("{}{i}: div", indent(depth)),
            OpCode::Car => println!("{}{i}: car", indent(depth)),
            OpCode::Cdr => println!("{}{i}: cdr", indent(depth)),
            OpCode::Cons => println!("{}{i}: cons", indent(depth)),
            OpCode::PushSymbol(symbol) => println!(
                "{}{i}: pushsymbol({})",
                indent(depth),
                constants.get(symbol).unwrap().as_symbol().unwrap()
            ),
            OpCode::PushString(string) => println!(
                "{}{i}: pushstring({})",
                indent(depth),
                constants.get(string).unwrap().as_string().unwrap()
            ),
            OpCode::PushInt(int) => println!("{}{i}: pushint({int})", indent(depth)),
            OpCode::PushChar(c) => println!("{}{i}: pushchar({c})", indent(depth)),
            OpCode::PushTrue => println!("{}{i}: pushtrue", indent(depth)),
            OpCode::PushNil => println!("{}{i}: pushnil", indent(depth)),
            OpCode::Call(args) => println!("{}{i}: call({args})", indent(depth)),
            OpCode::Return => println!("{}{i}: ret", indent(depth)),
            OpCode::Eq => println!("{}{i}: eq", indent(depth)),
            OpCode::Lt => println!("{}{i}: lt", indent(depth)),
            OpCode::Gt => println!("{}{i}: gt", indent(depth)),
            OpCode::List(args) => println!("{}{i}, list({args})", indent(depth)),
            OpCode::Branch(offset) => println!("{}{i}: branch({offset})", indent(depth)),
            OpCode::Jmp(offset) => println!("{}{i}: jmp({offset})", indent(depth)),
            OpCode::Lambda { arity, body } => {
                println!(
                    "{}{i}: lambda(arity: {})",
                    indent(depth),
                    match arity {
                        Arity::Nullary => 0,
                        Arity::Nary(n) => *n,
                        _ => todo!(),
                    }
                );
                let lambda_opcodes = constants.get(body).unwrap().as_opcodes().unwrap();
                disasm(lambda_opcodes, constants, depth + 1);
            }
            OpCode::IsType(ty) => println!("{}{i}: is-type({ty})", indent(depth)),
            OpCode::Assert => println!("{}{i}: assert", indent(depth)),
            _ => (),
        }
    }
}
