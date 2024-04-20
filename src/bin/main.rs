use std::env;
use std::fs::File;
use std::io::Read;
use std::rc::Rc;

use lisp::{Interpreter, Object, Reader};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
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

    let mut buff = String::new();

    for arg in std::env::args().skip(1) {
        let mut file = File::open(arg)?;
        buff.clear();
        file.read_to_string(&mut buff)?;
        for read in Reader::new(buff.as_str()) {
            match read {
                Ok(r) => {
                    let object = Object::from(r);
                    interpreter.eval(Rc::new(object))?;
                }
                Err(e) => return Err(e.into()),
            }
        }
    }

    Ok(())
}
