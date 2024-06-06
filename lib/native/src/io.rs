use crate::{check_arity, check_type};
use std::{fs::File, io::Read, rc::Rc};
use vm::{object::Type, Error, Object, Value};

pub fn print(objects: &mut [Value]) -> Result<Object, Error> {
    check_arity!("print", 1, objects);
    objects.first().unwrap().with(|object| println!("{object}"));
    Ok(Object::Nil)
}

pub fn read_file(objects: &mut [Value]) -> Result<Object, Error> {
    check_arity!("read-file", 1, objects);

    let path = check_type!(objects.first().unwrap(), String);
    let mut file = File::open(path).map_err(|e| Error::Other(Box::new(e)))?;
    let mut buff = String::new();

    file.read_to_string(&mut buff)
        .map_err(|e| Error::Other(Box::new(e)))?;

    Ok(Object::String(Rc::new(buff)))
}
