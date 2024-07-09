use crate::{check_arity, check_type};
use gc::{Gc, GcCell};
use vm::{
    object::{Cons, Type},
    Error, Local, Object,
};

pub fn split<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-split", 2, objects);

    let string = check_type!(objects[0], String);
    let separator = check_type!(objects[1], String);

    Ok(make_list_of_string(
        string.split(separator.as_str()).map(|s| s.to_string()),
    ))
}

pub fn split_ascii_whitespace<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string-split-whitespace", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(make_list_of_string(
        string.split_ascii_whitespace().map(str::to_string),
    ))
}

pub fn to_list<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("string->list", 1, objects);

    let string = check_type!(objects[0], String);

    Ok(make_list_of_char(string.chars()))
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

    Ok(make_list_of_string(string.lines().map(|s| s.to_string())))
}

pub fn is_digit<D: Clone>(objects: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("is-digit?", 1, objects);

    let c = check_type!(objects[0], Char);

    if c.is_ascii_digit() {
        Ok(Object::True)
    } else {
        Ok(Object::Nil)
    }
}

fn make_list_of_string<D: Clone>(mut strings: impl Iterator<Item = String>) -> Object<D> {
    let Some(first) = strings.next() else {
        return Object::Nil;
    };
    let mut tail = Gc::new(GcCell::new(Cons(
        Object::String(Gc::new(first)),
        Object::Nil,
    )));
    let list = Object::Cons(tail.clone());
    for s in strings {
        let new_tail = Gc::new(GcCell::new(Cons(Object::String(Gc::new(s)), Object::Nil)));
        tail.borrow_mut().1 = Object::Cons(new_tail.clone());
        tail = new_tail;
    }
    list
}

fn make_list_of_char<D: Clone>(mut chars: impl Iterator<Item = char>) -> Object<D> {
    let Some(first) = chars.next() else {
        return Object::Nil;
    };
    let mut tail = Gc::new(GcCell::new(Cons(Object::Char(first), Object::Nil)));
    let list = Object::Cons(tail.clone());
    for c in chars {
        let new_tail = Gc::new(GcCell::new(Cons(Object::Char(c), Object::Nil)));
        tail.borrow_mut().1 = Object::Cons(new_tail.clone());
        tail = new_tail;
    }
    list
}
