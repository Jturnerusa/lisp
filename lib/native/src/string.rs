use crate::{check_arity, check_type};
use vm::{
    object::{Cons, Type},
    Error, Object, Value,
};

pub fn split(objects: &mut [Value]) -> Result<Object, Error> {
    check_arity!("string-split", 2, objects);

    let string = check_type!(objects[0], String);
    let separator = check_type!(objects[1], String);

    Ok(make_list_of_string(
        string.split(separator.as_str()).map(|s| s.to_string()),
    ))
}

pub fn to_list(objects: &mut [Value]) -> Result<Object, Error> {
    check_arity!("string->list", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(make_list_of_string(string.chars().map(|c| c.to_string())))
}

pub fn lines(objects: &mut [Value]) -> Result<Object, Error> {
    check_arity!("string-lines", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(make_list_of_string(string.lines().map(|s| s.to_string())))
}

pub fn is_digit(objects: &mut [Value]) -> Result<Object, Error> {
    check_arity!("is-digit?", 1, objects);

    let string = check_type!(objects[0], String);

    if string.chars().all(|c| c.is_ascii_digit()) {
        Ok(Object::True)
    } else {
        Ok(Object::Nil)
    }
}

fn make_list_of_string(mut strings: impl Iterator<Item = String>) -> Object {
    match strings.next() {
        Some(string) => Object::Cons(Box::new(Cons(
            Object::String(string),
            make_list_of_string(strings),
        ))),
        None => Object::Nil,
    }
}
