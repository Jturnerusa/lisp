use std::rc::Rc;

use crate::object::NativeArgs;
use crate::{Error, Object};

pub fn print(args: Box<NativeArgs>) -> Result<Rc<Object>, Error> {
    for arg in args {
        println!("{}", arg)
    }
    Ok(Rc::new(Object::Nil))
}
