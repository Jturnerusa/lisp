use std::env;
use std::fs::File;
use std::io::Read;
use std::rc::Rc;

use lisp::{Interpreter, Object, Reader};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut file = File::open(
        env::args()
            .nth(1)
            .ok_or("expected path to file as first argument")?,
    )?;

    let mut source = String::new();
    file.read_to_string(&mut source)?;

    let mut interpreter = Interpreter::new();

    for (binding, fun) in [
        (
            "+",
            Box::new(lisp::prologue::arithmetic::add) as Box<lisp::object::NativeFunction>,
        ),
        (
            "-",
            Box::new(lisp::prologue::arithmetic::sub) as Box<lisp::object::NativeFunction>,
        ),
        (
            "*",
            Box::new(lisp::prologue::arithmetic::mul) as Box<lisp::object::NativeFunction>,
        ),
        (
            "/",
            Box::new(lisp::prologue::arithmetic::div) as Box<lisp::object::NativeFunction>,
        ),
        (
            "expt",
            Box::new(lisp::prologue::arithmetic::expt) as Box<lisp::object::NativeFunction>,
        ),
        (
            "<",
            Box::new(lisp::prologue::arithmetic::less_than) as Box<lisp::object::NativeFunction>,
        ),
        (
            ">",
            Box::new(lisp::prologue::arithmetic::greater_than) as Box<lisp::object::NativeFunction>,
        ),
        (
            "=",
            Box::new(lisp::prologue::equal) as Box<lisp::object::NativeFunction>,
        ),
        (
            "print",
            Box::new(lisp::prologue::io::print) as Box<lisp::object::NativeFunction>,
        ),
        (
            "list",
            Box::new(lisp::prologue::list) as Box<lisp::object::NativeFunction>,
        ),
        (
            "nil?",
            Box::new(lisp::prologue::is_nil) as Box<lisp::object::NativeFunction>,
        ),
        (
            "cons",
            Box::new(lisp::prologue::cons) as Box<lisp::object::NativeFunction>,
        ),
        (
            "car",
            Box::new(lisp::prologue::car) as Box<lisp::object::NativeFunction>,
        ),
        (
            "cdr",
            Box::new(lisp::prologue::cdr) as Box<lisp::object::NativeFunction>,
        ),
        (
            "push-back",
            Box::new(lisp::prologue::push_back) as Box<lisp::object::NativeFunction>,
        ),
    ] {
        let _ = interpreter.load_native_function(binding, fun);
    }

    for read in Reader::new(source.as_str()) {
        let object = match read {
            Ok(r) => Rc::new(Object::from(r)),
            Err(e) => return Err(Box::new(e)),
        };
        interpreter.eval(object)?;
    }

    Ok(())
}
