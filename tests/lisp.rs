use lisp::prologue::{self, arithmetic};
use lisp::{self, Interpreter, Object, Reader};
use std::rc::Rc;

fn eval(expr: &str) -> Rc<Object> {
    let mut interpreter = Interpreter::new();

    for (binding, fun) in [
        (
            "+",
            Box::new(arithmetic::add) as Box<lisp::object::NativeFunction>,
        ),
        (
            "-",
            Box::new(arithmetic::sub) as Box<lisp::object::NativeFunction>,
        ),
        (
            "*",
            Box::new(arithmetic::mul) as Box<lisp::object::NativeFunction>,
        ),
        (
            "/",
            Box::new(arithmetic::div) as Box<lisp::object::NativeFunction>,
        ),
        (
            "expt",
            Box::new(arithmetic::expt) as Box<lisp::object::NativeFunction>,
        ),
        (
            "<",
            Box::new(arithmetic::less_than) as Box<lisp::object::NativeFunction>,
        ),
        (
            ">",
            Box::new(arithmetic::greater_than) as Box<lisp::object::NativeFunction>,
        ),
        (
            "=",
            Box::new(prologue::equal) as Box<lisp::object::NativeFunction>,
        ),
    ] {
        let _ = interpreter.load_native_function(binding, fun);
    }

    let reader = Reader::new(expr);
    let mut obj = None;
    for read in reader {
        obj = Some(
            interpreter
                .eval(Rc::new(Object::from(read.unwrap())))
                .unwrap(),
        );
    }
    obj.unwrap()
}

#[test]
fn test_lambda() {
    assert!(matches!(
        *eval("(lambda (a b c) (+ a b c))"),
        Object::Function(..)
    ))
}

#[test]
fn test_self_evaluatiing() {
    assert!(matches!(*eval("1"), Object::Int(1)));
}

#[test]
fn test_def() {
    assert!(matches!(*eval("(def x 1) x"), Object::Int(1)));
}

#[test]
fn test_set() {
    assert!(matches!(*eval("(def x 1) (set x 2) x"), Object::Int(2)));
}

#[test]
fn test_lisp_level_function() {
    let s = r#"
(def f (lambda (a b c) (+ a b c)))
(f 1 1 1)
"#;
    assert!(matches!(*eval(s), Object::Int(3)));
}

#[test]
fn test_lambda_empty_param_list() {
    eval("(lambda () nil)");
}

#[test]
fn test_add() {
    assert!(matches!(*eval("(+ 1 1)"), Object::Int(2)));
}

#[test]
fn test_sub() {
    assert!(matches!(*eval("(- 2 1)"), Object::Int(1)));
}

#[test]
fn test_mul() {
    assert!(matches!(*eval("(* 2 2)"), Object::Int(4)));
}

#[test]
fn test_div() {
    assert!(matches!(*eval("(/ 4 2)"), Object::Int(2)));
}

#[test]
fn test_lt() {
    assert!(matches!(*eval("(< 1 2)"), Object::True));
}

#[test]
fn test_gt() {
    assert!(matches!(*eval("(> 2 1)"), Object::True));
}

#[test]
fn test_branch() {
    assert!(matches!(*eval("(if (> 2 1) 1 2)"), Object::Int(1)));
}

#[test]
fn test_equal() {
    assert!(matches!(*eval("(= 1 1)"), Object::True));
    assert!(matches!(*eval("(= 1 2)"), Object::Nil));
}
