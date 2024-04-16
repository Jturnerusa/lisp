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

#[test]
fn test_cons() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(cons 1 2)")
        .unwrap()
        .unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    let (car, cdr) = match interpreter.get_object(result).unwrap() {
        lisp::Object::Cons(car, cdr) => (car, cdr),
        _ => panic!()
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
    let mut interpreter = Interpreter::new();
    let r = reader::read("(car (cons 1 2))")
        .unwrap()
        .unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    assert!(matches!(
        interpreter.get_object(result).unwrap(),
        lisp::Object::Int(1)
    ));
}

#[test]
fn test_cdr() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(cdr (cons 1 2))")
        .unwrap()
        .unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    assert!(matches!(
        interpreter.get_object(result).unwrap(),
        lisp::Object::Int(2)
    ));
}


#[test]
fn test_equal() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(= 1 1)")
        .unwrap()
        .unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    assert!(matches!(
        interpreter.get_object(result).unwrap(),
        lisp::Object::True
    ));
}

#[test]
fn test_not_equal() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(= 1 2)")
        .unwrap()
        .unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    assert!(matches!(
        interpreter.get_object(result).unwrap(),
        lisp::Object::Nil
    ));
}

#[test]
fn test_equal_cons() {
    let mut interpreter = Interpreter::new();
    let r = reader::read("(= (cons 1 2) (cons 1 2))")
        .unwrap()
        .unwrap();
    let expr = interpreter.read(r);
    let result = interpreter.eval(expr).unwrap();
    assert!(matches!(
        interpreter.get_object(result).unwrap(),
        lisp::Object::True
    ));
}
