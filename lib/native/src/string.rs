use crate::{check_arity, check_type};
use gc::Gc;
use vm::{object::Type, Error, Local, Object};

pub fn split<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-split", 2, objects);

    let string = check_type!(objects[0], String);
    let separator = check_type!(objects[1], String);

    Ok(Object::from_iter(
        string
            .split(separator.as_str())
            .map(|s| Object::String(Gc::new(s.to_string()))),
    ))
}

pub fn split_ascii_whitespace<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-split-whitespace", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(Object::from_iter(
        string
            .split_ascii_whitespace()
            .map(|s| Object::String(Gc::new(s.to_string()))),
    ))
}

pub fn to_list<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string->list", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(Object::from_iter(
        string.chars().map(|char| Object::Char(char)),
    ))
}

pub fn from_list<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("list->string", 1, objects);

    let list = check_type!(objects[0], Cons);

    let string: String = list
        .borrow()
        .iter_cars()
        .map(|object| match object {
            Object::Char(c) => Ok(c),
            object => Err(Error::Type {
                expected: Type::Char,
                recieved: Type::from(&object),
            }),
        })
        .collect::<Result<String, _>>()?;

    Ok(Object::String(Gc::new(string)))
}

pub fn parse<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string->int", 1, objects);

    let string = check_type!(objects[0], String);

    let i: i64 = string.parse().map_err(|e| Error::Other(Box::new(e)))?;

    Ok(Object::Int(i))
}

pub fn lines<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-lines", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(Object::from_iter(
        string
            .lines()
            .map(|s| Object::String(Gc::new(s.to_string()))),
    ))
}

pub fn is_digit<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("is-digit?", 1, objects);

    let c = check_type!(objects[0], Char);

    if c.is_ascii_digit() {
        Ok(Object::Bool(true))
    } else {
        Ok(Object::Bool(false))
    }
}
