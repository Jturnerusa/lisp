use compiler::{ast, tree, types};
use lisp::compile_source;
use reader::Sexpr;
use vm::{OpCodeTable, Vm};

macro_rules! deftest {
    ($name:tt, $input:literal) => {
        #[test]
        fn $name() {
            let input = include_str!($input);
            eval_with_bootstrap(input).unwrap();
            gc::collect();
        }
    };
}

static BOOTSTRAP_SOURCE: &str = include_str!("../lib/bootstrap/bootstrap.lisp");
static LIST_UTILS_SOURCE: &str = include_str!("../lib/lisp/list.lisp");

fn eval_with_bootstrap(
    input: &str,
) -> Result<Option<vm::Object<FileSpan>>, Box<dyn std::error::Error>> {
    let mut tree_compiler = tree::Compiler::new();
    let mut ast_compiler = ast::Compiler::new();
    let mut type_checker = types::Checker::new();
    let mut opcode_table = OpCodeTable::new();
    let mut vm = Vm::new();
    let ignore_types = &mut |_: &_, _: &mut _| Ok(());

    compile_source(
        BOOTSTRAP_SOURCE,
        "bootstrap.lisp",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut type_checker,
        ignore_types,
        &mut vm,
        &mut opcode_table,
    )?;

    compile_source(
        LIST_UTILS_SOURCE,
        "list.lisp",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut type_checker,
        ignore_types,
        &mut vm,
        &mut opcode_table,
    )?;

    compile_source(
        input,
        "test input",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut type_checker,
        ignore_types,
        &mut vm,
        &mut opcode_table,
    )?;

    match vm.eval(&opcode_table) {
        Ok(_) => Ok(vm.pop().map(|local| local.into_object())),
        Err((e, sexpr)) => {
            eprintln!("error in: {}:\nat: {sexpr}", sexpr.context().display());
            Err(Box::new(e))
        }
    }
}

fn eval(input: &'static str) -> Result<Option<vm::Object<&Sexpr>>, Box<dyn std::error::Error>> {
    let mut tree_compiler = tree::Compiler::new();
    let mut ast_compiler = ast::Compiler::new();
    let mut type_checker = types::Checker::new();
    let mut opcode_table = OpCodeTable::new();
    let mut vm = Vm::new();
    let ignore_types = &mut |_: &_, _: &mut _| Ok(());

    compile_source(
        input,
        "test input",
        &mut tree_compiler,
        &mut ast_compiler,
        &mut type_checker,
        ignore_types,
        &mut vm,
        &mut opcode_table,
    )?;

    match vm.eval(&opcode_table) {
        Ok(_) => Ok(vm.pop().map(|local| local.into_object())),
        Err((e, sexpr)) => {
            eprintln!("error in: {}:\nat: {sexpr}", sexpr.context().display());
            Err(Box::new(e))
        }
    }
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
    let input = "(if true 1 2)";
    assert!(matches!(eval(input).unwrap().unwrap(), vm::Object::Int(1)));
    gc::collect();
}

#[test]
fn test_defmacro() {
    let input = "
(defmacro ++ (a)
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
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(true)
    ));
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
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(true)
    ));
    gc::collect();
}

#[test]
fn test_gt() {
    let input = "(> 2 1)";
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(true)
    ));
    gc::collect();
}

#[test]
fn test_eq() {
    let input = "(= 1 1)";
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(true)
    ));
    gc::collect();
}

#[test]
fn test_not_lt() {
    let input = "(< 1 0)";
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(false)
    ));
    gc::collect();
}

#[test]
fn test_not_gt() {
    let input = "(> 1 2)";
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(false)
    ));
    gc::collect();
}

#[test]
fn test_not_eq() {
    let input = "(= 1 2)";
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(false)
    ));
    gc::collect();
}

#[test]
fn test_fact() {
    let input = include_str!("lisp/fact.lisp");
    assert!(matches!(
        eval_with_bootstrap(input).unwrap().unwrap(),
        vm::Object::Int(3628800)
    ));
    gc::collect();
}

#[test]
fn test_let() {
    let input = include_str!("lisp/let.lisp");
    assert!(matches!(
        eval_with_bootstrap(input).unwrap().unwrap(),
        vm::Object::Int(3)
    ));
    gc::collect();
}

#[test]
fn test_eq_list() {
    let input = "(= (list 1 2 3) (list 1 2 3))";
    assert!(matches!(
        eval(input).unwrap().unwrap(),
        vm::Object::Bool(true)
    ));
    gc::collect();
}

#[test]
fn test_map() {
    let input = include_str!("lisp/map.lisp");
    assert!(eval_with_bootstrap(input)
        .unwrap()
        .unwrap()
        .as_bool()
        .unwrap());
    gc::collect();
}

#[test]
fn test_fold() {
    let input = include_str!("lisp/fold.lisp");
    assert!(eval_with_bootstrap(input)
        .unwrap()
        .unwrap()
        .as_bool()
        .unwrap());
    gc::collect();
}

#[test]
fn test_filter() {
    let input = include_str!("lisp/filter.lisp");
    assert!(eval_with_bootstrap(input)
        .unwrap()
        .unwrap()
        .as_bool()
        .unwrap());
    gc::collect();
}

#[test]
fn test_upvalues() {
    let input = include_str!("lisp/upvalues.lisp");
    assert!(eval(input).unwrap().unwrap().as_bool().unwrap());
    gc::collect();
}

#[test]
fn test_length() {
    let input = include_str!("lisp/length.lisp");
    assert!(eval_with_bootstrap(input).is_ok());
    gc::collect();
}

#[test]
fn test_nth() {
    let input = include_str!("lisp/nth.lisp");
    assert!(eval_with_bootstrap(input).is_ok());
    gc::collect();
}

#[test]
fn test_last() {
    let input = include_str!("lisp/last.lisp");
    assert!(eval_with_bootstrap(input).is_ok());
    gc::collect();
}

#[test]
fn test_parallel_let() {
    let input = include_str!("lisp/parallel-let.lisp");
    assert!(eval_with_bootstrap(input).is_ok());
    gc::collect();
}

#[test]
fn test_nthcdr() {
    let input = include_str!("lisp/nth-cdr.lisp");
    assert!(eval_with_bootstrap(input).is_ok());
    gc::collect();
}

#[test]
fn test_find() {
    let input = include_str!("lisp/find.lisp");
    assert!(eval_with_bootstrap(input).is_ok());
    gc::collect();
}

deftest!(test_hashmap, "lisp/hashmap.lisp");

deftest!(test_quasiquote, "lisp/quasiquote.lisp");

deftest!(test_apply, "lisp/apply.lisp");

deftest!(test_and, "lisp/and.lisp");

deftest!(test_or, "lisp/or.lisp");

deftest!(test_cond, "lisp/cond.lisp");

deftest!(test_named_let, "lisp/named-let.lisp");

deftest!(test_list_take, "lisp/list/take.lisp");

deftest!(test_list_drop, "lisp/list/drop.lisp");

deftest!(test_list_sort, "lisp/list/sort.lisp");

deftest!(test_quote_eq_list, "lisp/quote-eq-list.lisp");

deftest!(test_not, "lisp/not.lisp");
