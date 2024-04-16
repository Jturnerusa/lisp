use lisp::{reader::Reader, Interpreter};

fn eval_str(s: &str) -> lisp::Object {
    let mut interpreter = Interpreter::new();
    let mut reader = Reader::new(s);
    let r = reader.next().unwrap().unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    interpreter.get_object(result).unwrap().clone()
}

#[test]
fn test_add() {
    assert!(matches!(eval_str("(+ 1 1)"), lisp::Object::Int(2)));
}

#[test]
fn test_nested_add() {
    assert!(matches!(
        eval_str("(+ (+ 1 1) (+ 1 1))"),
        lisp::Object::Int(4)
    ));
}

#[test]
fn test_lambda() {
    assert!(matches!(
        eval_str("(lambda (a b c) (+ a b c))"),
        lisp::Object::Function { .. }
    ));
}

#[test]
fn test_eval_lambda() {
    assert!(matches!(
        eval_str("((lambda (a b c) (+ a b c)) 1 2 3)"),
        lisp::Object::Int(6)
    ));
}

#[test]
fn test_cons() {
    let mut interpreter = Interpreter::new();
    let mut reader = Reader::new("(cons 1 2)");
    let r = reader.next().unwrap().unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    let (car, cdr) = match interpreter.get_object(result).unwrap() {
        lisp::Object::Cons(car, cdr) => (car, cdr),
        _ => panic!(),
    };
    assert!(matches!(
        interpreter.get_object(*car).unwrap(),
        lisp::Object::Int(1)
    ));
    assert!(matches!(
        interpreter.get_object(*cdr).unwrap(),
        lisp::Object::Int(2)
    ));
}

#[test]
fn test_car() {
    assert!(matches!(eval_str("(car (cons 1 2))"), lisp::Object::Int(1)));
}

#[test]
fn test_cdr() {
    assert!(matches!(eval_str("(cdr (cons 1 2))"), lisp::Object::Int(2)));
}

#[test]
fn test_equal() {
    assert!(matches!(eval_str("(= 1 1)"), lisp::Object::True));
}

#[test]
fn test_not_equal() {
    assert!(matches!(eval_str("(= 1 2)"), lisp::Object::Nil));
}

#[test]
fn test_equal_cons() {
    assert!(matches!(
        eval_str("(= (cons 1 2) (cons 1 2))"),
        lisp::Object::True
    ));
}

#[test]
fn test_if_then() {
    assert!(matches!(eval_str("(if (= 1 1) 1 2)"), lisp::Object::Int(1)));
}

#[test]
fn test_if_else() {
    assert!(matches!(eval_str("(if (= 1 2) 1 2)"), lisp::Object::Int(2)));
}

#[test]
#[should_panic]
fn test_panic() {
    eval_str(r#"(if (= 1 1) (panic "test") nil)"#);
}
