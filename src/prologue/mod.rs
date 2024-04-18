pub mod arithmetic;
pub mod io;

use std::rc::Rc;

use crate::object::NativeArgs;
use crate::{Error, Object, Type};

pub fn cons(mut args: Box<NativeArgs>) -> Result<Rc<Object>, Error> {
    let car = args.next().ok_or(Error::Parameters)?;
    let cdr = args.next().ok_or(Error::Parameters)?;
    Ok(Rc::new(Object::Cons(Rc::clone(&car), Rc::clone(&cdr))))
}

pub fn car(mut args: Box<NativeArgs>) -> Result<Rc<Object>, Error> {
    let cons = args.next().ok_or(Error::Parameters)?;

    let None = args.next() else {
        return Err(Error::Parameters);
    };

    cons.car()
        .ok_or(Error::Type(Type::Cons, Type::from(&*cons)))
}

pub fn cdr(mut args: Box<NativeArgs>) -> Result<Rc<Object>, Error> {
    let cons = args.next().ok_or(Error::Parameters)?;

    let None = args.next() else {
        return Err(Error::Parameters);
    };

    cons.cdr()
        .ok_or(Error::Type(Type::Cons, Type::from(&*cons)))
}

pub fn equal(mut args: Box<NativeArgs>) -> Result<Rc<Object>, Error> {
    if match args.next() {
        Some(object) => args.all(|o| *o == *object),
        None => return Err(Error::Parameters),
    } {
        Ok(Rc::new(Object::True))
    } else {
        Ok(Rc::new(Object::Nil))
    }
}
