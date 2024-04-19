use std::rc::Rc;

use crate::object::NativeArgs;
use crate::{Error, Object};

pub fn print(mut args: Box<NativeArgs>) -> Result<Rc<Object>, Error> {
    if args.len() != 1 {
        return Err(Error::Parameters);
    }

    println!("{}", args.next().unwrap());

    Ok(Rc::new(Object::Nil))
}
