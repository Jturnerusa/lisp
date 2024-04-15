use lisp::{reader, Interpreter};

#[test]
fn test_add() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(+ 1 1)").unwrap().unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    let obj = interpreter.get_object(result).unwrap();
    assert!(matches!(obj, lisp::Object::Int(2)));
}

#[test]
fn test_nested_add() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(+ (+ 1 1) (+ 1 1))").unwrap().unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    let obj = interpreter.get_object(result).unwrap();
    assert!(matches!(obj, lisp::Object::Int(4)));
}

#[test]
fn test_lambda() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(lambda (a b c) (+ a b c))").unwrap().unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    let obj = interpreter.get_object(result).unwrap();
    assert!(matches!(obj, lisp::Object::Function { .. }));
}

#[test]
fn test_eval_lambda() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("((lambda (a b c) (+ a b c)) 1 2 3)")
        .unwrap()
        .unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    let obj = interpreter.get_object(result).unwrap();
    assert!(matches!(obj, lisp::Object::Int(6)));
}
