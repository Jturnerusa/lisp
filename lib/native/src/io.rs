use crate::{check_arity, check_type};
use gc::Gc;
use std::{fs::File, io::Read};
use vm::{object::Type, Error, Local, Object};

#[allow(clippy::unit_arg)]
pub fn print<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("print", 1, objects);

    objects.first().unwrap().with(|object| {
        Ok(match object {
            Object::Symbol(symbol) => print!("{symbol}"),
            Object::String(string) => print!("{string}"),
            Object::Char(char) => print!("{char}"),
            Object::Int(int) => print!("{int}"),
            Object::Float(float) => print!("{float}"),
            Object::Bool(true) => print!("true"),
            Object::Bool(false) => print!("false"),
            Object::Nil => print!("nil"),
            _ => return Err(Error::Other("failed to print object".to_string().into())),
        })
    })?;

    Ok(Object::Nil)
}

#[allow(clippy::unit_arg)]
pub fn println<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("print", 1, objects);

    objects.first().unwrap().with(|object| {
        Ok(match object {
            Object::Symbol(symbol) => println!("{symbol}"),
            Object::String(string) => println!("{string}"),
            Object::Char(char) => println!("{char}"),
            Object::Int(int) => println!("{int}"),
            Object::Float(float) => println!("{float}"),
            Object::Bool(true) => println!("true"),
            Object::Bool(false) => println!("false"),
            Object::Nil => println!("nil"),
            _ => return Err(Error::Other("failed to print object".to_string().into())),
        })
    })?;

    Ok(Object::Nil)
}

pub fn dbg<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("print", 1, objects);

    let object = objects.first().unwrap().clone().into_object();

    println!("{object}");

    Ok(object)
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
