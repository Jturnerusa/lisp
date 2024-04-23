use std::cell::RefCell;
use std::rc::Rc;

use lisp::prologue::{self, arithmetic};
use lisp::{self, Error, Interpreter, Object, Reader};

static BOOTSTRAP: &str = include_str!("lisp/lib/bootstrap.lisp");

fn eval(expr: &str) -> Result<Object, Error> {
    let mut interpreter = Interpreter::new();

    for (binding, fun) in [
        (
            "+",
            Rc::new(arithmetic::add) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "-",
            Rc::new(arithmetic::sub) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "*",
            Rc::new(arithmetic::mul) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "/",
            Rc::new(arithmetic::div) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "expt",
            Rc::new(arithmetic::expt) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "<",
            Rc::new(arithmetic::less_than) as Rc<lisp::object::NativeFunction>,
        ),
        (
            ">",
            Rc::new(arithmetic::greater_than) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "%",
            Rc::new(arithmetic::modulo) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "=",
            Rc::new(prologue::equal) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "cons",
            Rc::new(prologue::cons) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "car",
            Rc::new(prologue::car) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "cdr",
            Rc::new(prologue::cdr) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "list",
            Rc::new(prologue::list) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "nil?",
            Rc::new(prologue::is_nil) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "push-back",
            Rc::new(prologue::push_back) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "print",
            Rc::new(prologue::io::print) as Rc<lisp::object::NativeFunction>,
        ),
    ] {
        let _ = interpreter.load_native_function(binding, fun);
    }

    let reader = Reader::new(BOOTSTRAP);
    for read in reader.map(|r| r.unwrap()) {
        let object = Object::from(read);
        interpreter.eval(Rc::new(RefCell::new(object)))?;
    }

    let reader = Reader::new(expr);
    let mut obj = None;
    for read in reader {
        obj = Some(
            interpreter
                .eval(Rc::new(RefCell::new(Object::from(read.unwrap()))))
                .unwrap(),
        );
    }
    Ok(Rc::unwrap_or_clone(obj.unwrap()).into_inner())
}

#[test]
fn test_lambda() {
    assert!(matches!(
        eval("(lambda (a b c) (+ a b c))").unwrap(),
        Object::Function(..)
    ))
}

#[test]
fn test_self_evaluatiing() {
    assert!(matches!(eval("1").unwrap(), Object::Int(1)));
}

#[test]
fn test_def() {
    assert!(matches!(eval("(def x 1) x").unwrap(), Object::Int(1)));
}

#[test]
fn test_set() {
    assert!(matches!(
        eval("(def x 1) (set x 2) x").unwrap(),
        Object::Int(2)
    ));
}

#[test]
fn test_lisp_level_function() {
    let s = r#"
(def f (lambda (a b c) (+ a b c)))
(f 1 1 1)
"#;
    assert!(matches!(eval(s).unwrap(), Object::Int(3)));
}

#[test]
fn test_lambda_empty_param_list() {
    eval("(lambda () nil)").unwrap();
}

#[test]
fn test_add() {
    assert!(matches!(eval("(+ 1 1)").unwrap(), Object::Int(2)));
}

#[test]
fn test_sub() {
    assert!(matches!(eval("(- 2 1)").unwrap(), Object::Int(1)));
}

#[test]
fn test_mul() {
    assert!(matches!(eval("(* 2 2)").unwrap(), Object::Int(4)));
}

#[test]
fn test_div() {
    assert!(matches!(eval("(/ 4 2)").unwrap(), Object::Int(2)));
}

#[test]
fn test_lt() {
    assert!(matches!(eval("(< 1 2)").unwrap(), Object::True));
}

#[test]
fn test_gt() {
    assert!(matches!(eval("(> 2 1)").unwrap(), Object::True));
}

#[test]
fn test_branch() {
    assert!(matches!(eval("(if (> 2 1) 1 2)").unwrap(), Object::Int(1)));
}

#[test]
fn test_equal() {
    assert!(matches!(eval("(= 1 1)").unwrap(), Object::True));
    assert!(matches!(eval("(= 1 2)").unwrap(), Object::Nil));
}

#[test]
fn test_while() {
    let source = r#"
(def x 1)
(loop (< x 10)
  (set x (+ x 1)))
x
"#;
    assert!(matches!(eval(source).unwrap(), Object::Int(10)));
}

#[test]
fn test_mod() {
    assert!(matches!(eval("(% 256 255)").unwrap(), Object::Int(1)))
}

#[test]
fn test_cons() {
    assert!(matches!(
        &eval("(cons 1 2)").unwrap(),
        Object::Cons(car, cdr) if matches!(*car.borrow(), Object::Int(1)) && matches!(*cdr.borrow(), Object::Int(2))
    ));
}

#[test]
fn test_car() {
    assert!(matches!(eval("(car (cons 1 2))").unwrap(), Object::Int(1)));
}

#[test]
fn test_cdr() {
    assert!(matches!(eval("(cdr (cons 1 2))").unwrap(), Object::Int(2)));
}

#[test]
fn test_list() {
    assert_eq!(
        eval("(list 1 2 3 (+ 2 2) (cons 1 (cons 2 ())) 4)")
            .unwrap()
            .iter()
            .unwrap()
            .count(),
        6
    );
}

#[test]
fn test_quote() {
    assert!(matches!(
        &eval("(quote a)").unwrap(),
        Object::Symbol(symbol) if symbol == "a"
    ));
}

#[test]
fn test_defmacro() {
    assert!(matches!(
        &eval("(defmacro macro (a b c) nil)").unwrap(),
        Object::Nil
    ))
}

#[test]
fn test_macro() {
    let source = r#"
(defmacro defun (name parameters body)
  (list (quote def) name
    (list (quote lambda) parameters body)))

(defun add (a b) (+ a b))

(add 1 1)
"#;
    assert!(matches!(eval(source).unwrap(), Object::Int(2)));
}

#[test]
fn test_quote_shorthand() {
    let source = r#"
(defmacro defun (name parameters body)
  (list 'def name
    (list 'lambda parameters body)))

(defun add (a b) (+ a b))

(add 1 1)
"#;
    assert!(matches!(eval(source).unwrap(), Object::Int(2)));
}

#[test]
fn test_is_nil() {
    assert!(matches!(eval("(nil? nil)").unwrap(), Object::True))
}

#[test]
fn test_progn() {
    assert!(matches!(
        eval(
            "(progn (+ 1 1)
                    (+ 2 2)
                    (+ 3 3))"
        )
        .unwrap(),
        Object::Int(6)
    ))
}

#[test]
fn test_push_back() {
    assert_eq!(
        eval("(push-back (list 1 2 3) (list 4 5 6))")
            .unwrap()
            .iter_cars()
            .unwrap()
            .count(),
        4
    );

    assert_eq!(
        eval("(push-back (list 1 2 3) 4)")
            .unwrap()
            .iter_cars()
            .unwrap()
            .count(),
        4
    );
}

#[test]
fn test_fac() {
    let source = r#"
(def fac (lambda (n)
           (if (< n 2)
               n
               (* n (fac (- n 1))))))

(fac 10)
"#;
    assert!(matches!(eval(source).unwrap(), Object::Int(3628800)))
}

#[test]
fn test_map() {
    let source = r#"
(map (lambda (x) (* x 2)) (list 2 4 6))
"#;
    assert!(matches!(
        eval(source).unwrap(),
        object if matches!(object.iter_cars()
            .unwrap()
            .map(|car| *(*car).clone().into_inner().as_int().unwrap())
            .collect::<Vec<_>>()
            .as_slice(), &[4, 8, 12])
    ))
}

#[test]
fn test_captures() {
    let source = r#"
(defun test-captures ()
  (let ((acc nil))
    (let ((_ nil))
      (set acc 1))
   acc))

(test-captures)
"#;
    assert!(matches!(eval(source).unwrap(), Object::Int(1)));
}

#[test]
fn test_captures_2() {
    let source = r#"
(defun test-captures ()
  (let ((acc nil))
    ((lambda ()
      (set acc 1)))
   acc))

(test-captures)
"#;
    assert!(matches!(dbg!(eval(source).unwrap()), Object::Int(1)))
}

#[test]
fn test_filter() {
    let source = r#"
(filter (lambda (x) (< x 5)) (list 1 2 3 4 5 6 7 8 9))
"#;
    assert!(matches!(
        eval(source).unwrap(),
        object if object.iter_cars().unwrap().count()== 4
    ));
}
