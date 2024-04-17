#![allow(dead_code)]

pub mod reader;

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use unwrap_enum::{EnumAs, EnumIs};

pub use reader::Reader;

#[derive(Clone, Debug)]
pub enum Error {
    Type(Type, Type),
    Parameters,
    NotFound(String),
}

#[derive(Clone, Debug)]
pub enum Type {
    Function,
    Cons,
    Symbol,
    String,
    Int,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Object {
    Function(Rc<Object>, Vec<String>, HashMap<String, Rc<Object>>),
    Cons(Rc<Object>, Rc<Object>),
    Symbol(String),
    String(String),
    Int(i64),
}

pub struct Iter(Option<(Rc<Object>, Rc<Object>)>);

impl Object {
    pub fn cons(a: Rc<Object>, b: Rc<Object>) -> Rc<Object> {
        Rc::new(Self::Cons(a, b))
    }

    pub fn car(&self) -> Option<Rc<Object>> {
        match self {
            Self::Cons(car, _) => Some(Rc::clone(car)),
            _ => None,
        }
    }

    pub fn cdr(&self) -> Option<Rc<Object>> {
        match self {
            Self::Cons(car, _) => Some(Rc::clone(car)),
            _ => None,
        }
    }

    pub fn iter(&self) -> Option<Iter> {
        match self {
            Object::Cons(car, cdr) => Some(Iter(Some((Rc::clone(car), Rc::clone(cdr))))),
            _ => None,
        }
    }

    pub fn iter_cars(&self) -> Option<impl Iterator<Item = Rc<Object>>> {
        Some(self.iter()?.map(|(car, _)| car))
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Function => write!(f, "function"),
            Self::Cons => write!(f, "cons"),
            Self::Symbol => write!(f, "symbol"),
            Self::String => write!(f, "string"),
            Self::Int => write!(f, "integer"),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(expected, got) => write!(f, "expected type: {}: got :{}", expected, got),
            Self::Parameters => write!(f, "invalid parameters"),
            Self::NotFound(var) => write!(f, "variable not found: {}", var),
        }
    }
}

impl std::error::Error for Error {}

impl Iterator for Iter {
    type Item = (Rc<Object>, Rc<Object>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((car, cdr)) = &self.0.clone() {
            self.0 = match &**cdr {
                Object::Cons(a, b) => Some((Rc::clone(a), Rc::clone(b))),
                _ => None,
            };
            Some((Rc::clone(car), Rc::clone(cdr)))
        } else {
            None
        }
    }
}

impl From<&Object> for Type {
    fn from(other: &Object) -> Type {
        match other {
            Object::Function(..) => Type::Function,
            Object::Cons(..) => Type::Cons,
            Object::Symbol(_) => Type::Symbol,
            Object::String(_) => Type::String,
            Object::Int(_) => Type::Int,
        }
    }
}
