use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

use compiler::Compiler;
use identity_hasher::IdentityHasher;
use reader::Reader;
use vm::Vm;

fn eval(input: &str) -> Result<Rc<RefCell<vm::Object>>, Box<dyn std::error::Error>> {
    let reader = Reader::new(input);
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();
    let mut opcodes = Vec::new();
    let mut constants = HashMap::with_hasher(IdentityHasher::new());
    let mut ret = None;

    for read in reader {
        let value = read?;

        opcodes.clear();
        constants.clear();

        compiler.compile(&value, &mut opcodes, &mut constants)?;

        vm.load_constants(constants.values().cloned());
        ret = vm.eval(opcodes.as_slice()).unwrap();
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

#[test]
fn test_def_global() {
    let input = "(def x 1) x";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(1)
    ));
}

#[test]
fn test_set_global() {
    let input = "(def x 1) (set x 2) x";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(2)
    ));
}

#[test]
fn test_lambda_expr() {
    let input = "((lambda () (+ 1 1)))";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(2)
    ));
}

#[test]
fn test_local_vars() {
    let input = "((lambda (a) (+ a 1)) 1)";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(2)
    ));
}

#[test]
fn test_branch() {
    let input = "(if t 1 2)";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(1)
    ));
}

#[test]
fn test_defmacro() {
    let input = "(defmacro ++ (a)
                   (list '+ a 1))
                 (++ 1)";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(2)
    ));
}

#[test]
fn test_car() {
    let input = "(car (list 1 2 3))";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(1)
    ));
}

#[test]
fn test_cdr() {
    let input = "(car (cdr (list 1 2 3)))";
    assert!(matches!(
        eval(input).unwrap().borrow().deref(),
        vm::Object::Int(2)
    ));
}

#[test]
fn test_get_upvalue() {
    let input = "
(def x (lambda (a)
        ((lambda () a))))
(x 1)
";
    assert!(matches!(
        dbg!(eval(input).unwrap().borrow().deref()),
        vm::Object::Int(1)
    ));
}
