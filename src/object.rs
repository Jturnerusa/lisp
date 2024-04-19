use std::cmp::PartialEq;
use std::collections::HashMap;
use std::iter::ExactSizeIterator;
use std::rc::Rc;
use unwrap_enum::{EnumAs, EnumIs};

use crate::reader;
use crate::Error;

pub type NativeArgs = dyn ExactSizeIterator<Item = Rc<Object>>;

pub type NativeFunction = dyn Fn(Box<NativeArgs>) -> Result<Rc<Object>, Error>;

#[derive(EnumAs, EnumIs)]
pub enum Object {
    NativeFunction(Box<NativeFunction>),
    Function(Rc<Object>, Vec<String>, HashMap<String, Rc<Object>>),
    Macro(Rc<Object>, Vec<String>),
    Cons(Rc<Object>, Rc<Object>),
    Symbol(String),
    String(String),
    Int(i64),
    True,
    Nil,
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
            Self::Cons(_, cdr) => Some(Rc::clone(cdr)),
            _ => None,
        }
    }

    pub fn iter(&self) -> Option<Iter> {
        match self {
            Object::Cons(car, cdr) => Some(Iter(Some((Rc::clone(car), Rc::clone(cdr))))),
            Object::Nil => Some(Iter(None)),
            _ => None,
        }
    }

    pub fn iter_cars(&self) -> Option<impl Iterator<Item = Rc<Object>>> {
        Some(self.iter()?.map(|(car, _)| car))
    }
}

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

impl From<reader::Value> for Object {
    fn from(other: reader::Value) -> Self {
        match other {
            reader::Value::Cons(car, cdr) => {
                Self::Cons(Rc::new(Object::from(*car)), Rc::new(Object::from(*cdr)))
            }
            reader::Value::Symbol(symbol) => Self::Symbol(symbol),
            reader::Value::String(string) => Self::String(string),
            reader::Value::Int(i) => Self::Int(i),
            reader::Value::Nil => Self::Nil,
        }
    }
}

impl std::fmt::Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NativeFunction(..) => write!(f, "<native function>"),
            Self::Function(body, ..) => write!(f, "<lambda> {}", **body),
            Self::Macro(body, _) => write!(f, "<macro> {}", **body),
            Self::Cons(car, cdr) => write!(f, "({} . {})", car, cdr),
            Self::Symbol(symbol) => write!(f, "'{}", symbol.as_str()),
            Self::String(string) => write!(f, r#""{}""#, string.as_str()),
            Self::Int(i) => write!(f, "{i}"),
            Self::True => write!(f, "t"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

impl std::fmt::Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NativeFunction(..) => write!(f, "Object::NativeFunction"),
            Self::Function(body, parameters, captures) => write!(
                f,
                "Object::Function({:?}, {:?} {:?})",
                *body, parameters, captures
            ),
            Self::Macro(body, parameters) => {
                write!(f, "Object::Macro({:?}, {:?})", body, parameters)
            }
            Self::Cons(car, cdr) => write!(f, "Object::Cons({:?}, {:?})", car, cdr),
            Self::String(string) => write!(f, "Object::String({})", string.as_str()),
            Self::Symbol(symbol) => write!(f, "Object::Symbol({})", symbol.as_str()),
            Self::Int(i) => write!(f, "Object::Int({})", i),
            Self::True => write!(f, "Object::True"),
            Self::Nil => write!(f, "Object::Nil"),
        }
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        use Object::*;
        match (self, other) {
            (NativeFunction(_), _) => false,
            (Function(a, b, c), Function(d, e, f)) => a == d && b == e && c == f,
            (Cons(a, b), Cons(c, d)) => a == c && b == d,
            (Symbol(a), Symbol(b)) => a == b,
            (String(a), String(b)) => a == b,
            (Int(a), Int(b)) => a == b,
            (True, True) => true,
            (Nil, Nil) => true,
            _ => false,
        }
    }
}
