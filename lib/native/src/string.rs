use crate::{check_arity, check_type};
use std::rc::Rc;
use vm::{object::Type, Error, Local, Object};

pub fn split<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-split", 2, objects);

    let string = check_type!(objects[0], String);
    let separator = check_type!(objects[1], String);

    Ok(Object::from_iter(
        string
            .split(separator.as_str())
            .map(|s| Object::String(Rc::new(s.to_string()))),
    ))
}

pub fn split_ascii_whitespace<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-split-whitespace", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(Object::from_iter(
        string
            .split_ascii_whitespace()
            .map(|s| Object::String(Rc::new(s.to_string()))),
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

    Ok(Object::String(Rc::new(string)))
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
            .map(|s| Object::String(Rc::new(s.to_string()))),
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

pub fn contains<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-contains?", 2, objects);

    let string = check_type!(objects[0], String);

    let contains = match objects[1].clone().into_object() {
        Object::String(pattern) => string.contains(pattern.as_str()),
        Object::Char(pattern) => string.contains(pattern),
        object => {
            return Err(Error::Type {
                expected: Type::String,
                recieved: Type::from(&object),
            })
        }
    };

    Ok(if contains {
        Object::Bool(true)
    } else {
        Object::Bool(false)
    })
}

pub fn substr<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-substr", 3, objects);

    let string = check_type!(objects[0], String);
    let start = check_type!(objects[1], Int).try_into().unwrap();
    let stop = check_type!(objects[2], Int).try_into().unwrap();

    let substr = string.as_str()[start..stop].to_string();

    Ok(Object::String(Rc::new(substr)))
}

pub fn find<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-find", 2, objects);

    let string = check_type!(&objects[0], String);

    let index = match &objects[1].clone().into_object() {
        Object::String(pattern) => string.find(pattern.as_str()),
        Object::Char(pattern) => string.find(*pattern),
        object => {
            return Err(Error::Type {
                expected: Type::String,
                recieved: Type::from(object),
            })
        }
    };

    Ok(match index {
        Some(index) => Object::Int(index.try_into().unwrap()),
        None => Object::Nil,
    })
}

pub fn starts_with<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-starts-with?", 2, objects);

    let string = check_type!(&objects[0], String);

    let starts_with = match objects[1].clone().into_object() {
        Object::String(prefix) => string.starts_with(prefix.as_str()),
        Object::Char(prefix) => string.starts_with(prefix),
        object => {
            return Err(Error::Type {
                expected: Type::String,
                recieved: Type::from(&object),
            })
        }
    };

    Ok(if starts_with {
        Object::Bool(true)
    } else {
        Object::Bool(false)
    })
}
