use std::{cell::RefCell, ops::Deref, rc::Rc};

use vm::{Cons, Error, Object, Type};

pub fn string_to_list(objects: &[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> {
    if objects.len() > 1 {
        Err(Error::Parameters(
            "string-to-list expected a single parameter".to_string(),
        ))
    } else {
        let string = match objects.first().unwrap().borrow().deref() {
            Object::String(string) => string.clone(),
            object => {
                return Err(Error::Type {
                    expected: Type::String,
                    recieved: Type::from(object),
                })
            }
        };

        let list = make_list_from_chars(string.chars());

        Ok(list)
    }
}

pub fn string_split(objects: &[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> {
    if objects.len() != 2 {
        Err(Error::Parameters(
            "string-spilt expected two parameters".to_string(),
        ))
    } else {
        let separator = match objects[0].borrow().deref() {
            Object::Symbol(string) => string.clone(),
            object => {
                return Err(Error::Type {
                    expected: Type::String,
                    recieved: Type::from(object),
                })
            }
        };

        let string = match objects[0].borrow().deref() {
            Object::Symbol(string) => string.clone(),
            object => {
                return Err(Error::Type {
                    expected: Type::String,
                    recieved: Type::from(object),
                })
            }
        };

        let list = make_list_from_lines(string.split(separator.as_str()));

        Ok(list)
    }
}

fn make_list_from_lines<'a>(mut lines: impl Iterator<Item = &'a str>) -> Rc<RefCell<Object>> {
    match lines.next() {
        Some(line) => Rc::new(RefCell::new(Object::Cons(Cons(
            Rc::new(RefCell::new(Object::Symbol(line.to_string()))),
            make_list_from_lines(lines),
        )))),
        None => Rc::new(RefCell::new(Object::Nil)),
    }
}

fn make_list_from_chars(mut chars: impl Iterator<Item = char>) -> Rc<RefCell<Object>> {
    match chars.next() {
        Some(c) => Rc::new(RefCell::new(Object::Cons(Cons(
            Rc::new(RefCell::new(Object::String(c.to_string()))),
            make_list_from_chars(chars),
        )))),
        None => Rc::new(RefCell::new(Object::Nil)),
    }
}
