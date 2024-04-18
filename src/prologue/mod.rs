pub mod arithmetic;
pub mod io;

use std::rc::Rc;

use crate::object::NativeArgs;
use crate::{Error, Object};

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
