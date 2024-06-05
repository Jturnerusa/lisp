use std::collections::HashMap;

use compiler::Compiler;
use identity_hasher::IdentityHasher;
use reader::Reader;
use vm::Vm;

static BOOTSTRAP_SOURCE: &str = include_str!("../lib/lisp/bootstrap.lisp");

fn eval(input: &str) -> Result<Option<vm::Object>, Box<dyn std::error::Error>> {
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();
    let mut opcodes = Vec::new();
    let mut constants = HashMap::with_hasher(IdentityHasher::new());
    let mut ret = None;

    native_functions::load_module(&mut vm);

    for read in Reader::new(BOOTSTRAP_SOURCE) {
        let value = read?;

        opcodes.clear();
        constants.clear();

        compiler.compile(&value, &mut opcodes, &mut constants)?;

        vm.load_constants(constants.values().cloned());
        ret = vm.eval(opcodes.as_slice())?;
    }

    for read in Reader::new(input) {
        let value = read?;

        opcodes.clear();
        constants.clear();

        compiler.compile(&value, &mut opcodes, &mut constants)?;

        vm.load_constants(constants.values().cloned());
        ret = vm.eval(opcodes.as_slice())?;
    }

    Ok(ret.map(|value| value.into_object()))
}

#[test]
fn test_add() {
    let input = "(+ 1 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)))
}

#[test]
fn test_nested_add() {
    let input = "(+ (+ 1 1) 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(3)))
}

#[test]
fn test_def_global() {
    let input = "(def x 1) x";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
}

#[test]
fn test_set_global() {
    let input = "(def x 1) (set x 2) x";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
}

#[test]
fn test_lambda_expr() {
    let input = "((lambda () (+ 1 1)))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
}

#[test]
fn test_local_vars() {
    let input = "((lambda (a) (+ a 1)) 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
}

#[test]
fn test_branch() {
    let input = "(if t 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
}

#[test]
fn test_defmacro() {
    let input = "(defmacro ++ (a)
                   (list '+ a 1))
                 (++ 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
}

#[test]
fn test_car() {
    let input = "(car (list 1 2 3))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
}

#[test]
fn test_cdr() {
    let input = "(car (cdr (list 1 2 3)))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
}

#[test]
fn test_get_upvalue() {
    let input = "
(def x (lambda (a)
        ((lambda () a))))
(x 1)
";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
}

#[test]
fn test_is_type() {
    let input = "(int? 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
}

#[test]
fn test_multiexpr_lambda() {
    let input = "
((lambda (x)
   (set x 1)
   (+ x 1))
 0)
";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
}

#[test]
fn test_cons() {
    let input = "(car (cons 1 2))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
}

#[test]
fn test_assert() {
    let input = "(assert (int? nil))";
    assert!(eval(input).is_err());
}

#[test]
fn test_lt() {
    let input = "(< 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
}

#[test]
fn test_gt() {
    let input = "(> 2 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
}

#[test]
fn test_eq() {
    let input = "(= 1 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
}

#[test]
fn test_not_lt() {
    let input = "(< 1 0)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Nil));
}

#[test]
fn test_not_gt() {
    let input = "(> 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Nil));
}

#[test]
fn test_not_eq() {
    let input = "(= 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Nil));
}

#[test]
fn test_fact() {
    let input = include_str!("lisp/fact.lisp");
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Int(3628800)
    ));
}

#[test]
fn test_let() {
    let input = include_str!("lisp/let.lisp");
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(3)));
}

#[test]
fn test_eq_list() {
    let input = "(= (list 1 2 3) (list 1 2 3))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
}

#[test]
fn test_map() {
    let input = include_str!("lisp/map.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
}

#[test]
fn test_fold() {
    let input = include_str!("lisp/fold.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
}

#[test]
fn test_filter() {
    let input = include_str!("lisp/filter.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
}

#[test]
fn test_upvalues() {
    let input = include_str!("lisp/upvalues.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
}

#[test]
fn test_string_split() {
    let input = include_str!("lisp/string-split.lisp");
    assert!(dbg!(eval(input)).is_ok());
}

#[test]
fn test_length() {
    let input = include_str!("lisp/length.lisp");
    assert!(dbg!(eval(input).is_ok()));
}

#[test]
fn test_nth() {
    let input = include_str!("lisp/nth.lisp");
    assert!(dbg!(eval(input).is_ok()));
}
