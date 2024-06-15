use std::collections::HashMap;

use compiler::Compiler;
use identity_hasher::IdentityHasher;
use reader::Reader;
use vm::Vm;

macro_rules! deftest {
    ($name:tt, $input:literal) => {
        #[test]
        fn $name() {
            let input = include_str!($input);
            assert!(eval(input).is_ok());
            gc::collect();
        }
    };
}

static BOOTSTRAP_SOURCE: &str = include_str!("../lib/lisp/bootstrap.lisp");

fn eval(input: &str) -> Result<Option<vm::Object>, Box<dyn std::error::Error>> {
    let mut compiler = Compiler::new();
    let mut vm = Vm::new();
    let mut opcodes = Vec::new();
    let mut constants = HashMap::with_hasher(IdentityHasher::new());

    native_functions::load_module(&mut vm);

    for read in Reader::new(BOOTSTRAP_SOURCE) {
        let value = read?;
        compiler.compile(&value, &mut opcodes, &mut constants)?;
    }

    for read in Reader::new(input) {
        let value = read?;
        compiler.compile(&value, &mut opcodes, &mut constants)?;
    }

    vm.load_constants(constants.values().cloned());
    let ret = vm.eval(opcodes.as_slice())?;

    Ok(ret.map(|value| value.into_object()))
}

#[test]
fn test_add() {
    let input = "(+ 1 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
    gc::collect();
}

#[test]
fn test_nested_add() {
    let input = "(+ (+ 1 1) 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(3)));
    gc::collect();
}

#[test]
fn test_def_global() {
    let input = "(def x 1) x";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
    gc::collect();
}

#[test]
fn test_set_global() {
    let input = "(def x 1) (set! x 2) x";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
    gc::collect();
}

#[test]
fn test_lambda_expr() {
    let input = "((lambda () (+ 1 1)))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
    gc::collect();
}

#[test]
fn test_local_vars() {
    let input = "((lambda (a) (+ a 1)) 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
    gc::collect();
}

#[test]
fn test_branch() {
    let input = "(if t 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
    gc::collect();
}

#[test]
fn test_defmacro() {
    let input = "(defmacro ++ (a)
                   (list '+ a 1))
                 (++ 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
    gc::collect();
}

#[test]
fn test_car() {
    let input = "(car (list 1 2 3))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
    gc::collect();
}

#[test]
fn test_cdr() {
    let input = "(car (cdr (list 1 2 3)))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
    gc::collect();
}

#[test]
fn test_get_upvalue() {
    let input = "
(def x (lambda (a)
        ((lambda () a))))
(x 1)
";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
    gc::collect();
}

#[test]
fn test_is_type() {
    let input = "(int? 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
    gc::collect();
}

#[test]
fn test_multiexpr_lambda() {
    let input = "
((lambda (x)
   (set! x 1)
   (+ x 1))
 0)
";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(2)));
    gc::collect();
}

#[test]
fn test_cons() {
    let input = "(car (cons 1 2))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
    gc::collect();
}

#[test]
fn test_assert() {
    let input = "(assert (int? nil))";
    assert!(eval(input).is_err());
    gc::collect();
}

#[test]
fn test_lt() {
    let input = "(< 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
    gc::collect();
}

#[test]
fn test_gt() {
    let input = "(> 2 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
    gc::collect();
}

#[test]
fn test_eq() {
    let input = "(= 1 1)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
    gc::collect();
}

#[test]
fn test_not_lt() {
    let input = "(< 1 0)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Nil));
    gc::collect();
}

#[test]
fn test_not_gt() {
    let input = "(> 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Nil));
    gc::collect();
}

#[test]
fn test_not_eq() {
    let input = "(= 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Nil));
    gc::collect();
}

#[test]
fn test_fact() {
    let input = include_str!("lisp/fact.lisp");
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Int(3628800)
    ));
    gc::collect();
}

#[test]
fn test_let() {
    let input = include_str!("lisp/let.lisp");
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(3)));
    gc::collect();
}

#[test]
fn test_eq_list() {
    let input = "(= (list 1 2 3) (list 1 2 3))";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::True));
    gc::collect();
}

#[test]
fn test_map() {
    let input = include_str!("lisp/map.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
    gc::collect();
}

#[test]
fn test_fold() {
    let input = include_str!("lisp/fold.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
    gc::collect();
}

#[test]
fn test_filter() {
    let input = include_str!("lisp/filter.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
    gc::collect();
}

#[test]
fn test_upvalues() {
    let input = include_str!("lisp/upvalues.lisp");
    assert!(eval(input).unwrap().unwrap().is_true());
    gc::collect();
}

#[test]
fn test_string_split() {
    let input = include_str!("lisp/string-split.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_length() {
    let input = include_str!("lisp/length.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_nth() {
    let input = include_str!("lisp/nth.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_last() {
    let input = include_str!("lisp/last.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_parallel_let() {
    let input = include_str!("lisp/parallel-let.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_hashmap() {
    let input = include_str!("lisp/hashmap.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_setcdr() {
    let input = include_str!("lisp/setcdr.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_nthcdr() {
    let input = include_str!("lisp/nth-cdr.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

#[test]
fn test_find() {
    let input = include_str!("lisp/find.lisp");
    assert!(eval(input).is_ok());
    gc::collect();
}

deftest!(test_setcar, "lisp/setcar.lisp");

deftest!(test_quasiquote, "lisp/quasiquote.lisp");
