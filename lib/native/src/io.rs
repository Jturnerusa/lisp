use crate::{check_arity, check_type};
use gc::Gc;
use std::{fs::File, io::Read};
use vm::{
    object::{self, Type},
    Error, Local, Object,
};

pub fn print<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("print", 1, objects);
    objects.first().unwrap().with(|object| println!("{object}"));
    Ok(Object::Nil)
}

pub fn argv<D: Clone>(_: &mut [Local<D>]) -> Result<Object<D>, Error> {
    Ok(Object::from_iter(
        std::env::args().map(|s| Object::String(Gc::new(s))),
    ))
}

pub fn read_file<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("read-file", 1, objects);

    let path = check_type!(objects.first().unwrap(), String);
    let mut file = File::open(path).map_err(|e| Error::Other(Box::new(e)))?;
    let mut buff = String::new();

    file.read_to_string(&mut buff)
        .map_err(|e| Error::Other(Box::new(e)))?;

    Ok(Object::String(Gc::new(buff)))
}
