use std::cell::RefCell;
use std::rc::Rc;

use crate::object::NativeArgs;
use crate::{Error, Object, ObjectRef};

pub fn print(mut args: Box<NativeArgs>) -> Result<ObjectRef, Error> {
    if args.len() != 1 {
        return Err(Error::Parameters);
    }

    println!("{}", args.next().unwrap().borrow());

    Ok(Rc::new(RefCell::new(Object::Nil)))
}
