use std::cell::RefCell;
use std::ops::Deref;
use std::rc::Rc;

use compiler::Compiler;
use reader::Reader;
use vm::Vm;

fn eval(input: &str) -> Result<Rc<RefCell<vm::Object>>, Box<dyn std::error::Error>> {
    let reader = Reader::new(input);
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();
    let mut opcodes = Vec::new();
    let mut ret = None;

    for read in reader {
        let read = read.unwrap();
        let ast = compiler::Ast::parse(&read).unwrap();
        opcodes.clear();
        compiler.compile(&ast, &mut opcodes).unwrap();
        ret = Some(vm.eval(opcodes.as_slice())?);
    }

    Ok(ret.unwrap())
}

#[test]
fn test_add() {
    let input = "(+ 1 1)";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(2)
    ))
}

#[test]
fn test_nested_add() {
    let input = "(+ (+ 1 1) 1)";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(3)
    ))
}
