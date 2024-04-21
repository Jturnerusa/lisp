use std::cell::RefCell;
use std::fs::File;
use std::io::Read;
use std::rc::Rc;

use lisp::{Interpreter, Object, Reader};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut interpreter = Interpreter::new();

    for (binding, fun) in [
        (
            "+",
            Rc::new(lisp::prologue::arithmetic::add) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "-",
            Rc::new(lisp::prologue::arithmetic::sub) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "*",
            Rc::new(lisp::prologue::arithmetic::mul) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "/",
            Rc::new(lisp::prologue::arithmetic::div) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "expt",
            Rc::new(lisp::prologue::arithmetic::expt) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "<",
            Rc::new(lisp::prologue::arithmetic::less_than) as Rc<lisp::object::NativeFunction>,
        ),
        (
            ">",
            Rc::new(lisp::prologue::arithmetic::greater_than) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "=",
            Rc::new(lisp::prologue::equal) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "print",
            Rc::new(lisp::prologue::io::print) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "list",
            Rc::new(lisp::prologue::list) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "nil?",
            Rc::new(lisp::prologue::is_nil) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "cons",
            Rc::new(lisp::prologue::cons) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "car",
            Rc::new(lisp::prologue::car) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "cdr",
            Rc::new(lisp::prologue::cdr) as Rc<lisp::object::NativeFunction>,
        ),
        (
            "push-back",
            Rc::new(lisp::prologue::push_back) as Rc<lisp::object::NativeFunction>,
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
                    interpreter.eval(Rc::new(RefCell::new(object)))?;
                }
                Err(e) => return Err(e.into()),
            }
        }
    }

    Ok(())
}
