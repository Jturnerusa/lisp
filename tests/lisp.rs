use std::convert::TryFrom;

use compiler::Compiler;
use reader::Reader;
use value::Value;
use vm::Vm;

fn eval(input: &str) -> Result<Value, Box<dyn std::error::Error>> {
    let reader = Reader::new(input);
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();
    let mut opcodes = Vec::new();

    for read in reader {
        let read = read.unwrap();
        let ast = compiler::Ast::parse(&read).unwrap();
        opcodes.clear();
        compiler.compile(&ast, &mut opcodes).unwrap();
        vm.eval(opcodes.as_slice()).unwrap();
    }

    let ret = vm.stack().first().unwrap().borrow().clone();

    Ok(Value::try_from(&ret).unwrap())
}

#[test]
fn test_add() {
    let input = "(+ 1 1)";
    assert!(matches!(eval(input).unwrap(), Value::Int(2)));
}

#[test]
fn test_nested_add() {
    let input = "(+ (+ 1 1) 1)";
    assert!(matches!(eval(input).unwrap(), Value::Int(3)));
}
