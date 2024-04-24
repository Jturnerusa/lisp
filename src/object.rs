use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::iter::ExactSizeIterator;
use std::rc::Rc;
use unwrap_enum::{EnumAs, EnumIs};

use crate::reader;
use crate::Error;

type ObjectRef = Rc<RefCell<Object>>;

pub type NativeArgs = dyn ExactSizeIterator<Item = ObjectRef>;

pub type NativeFunction = dyn Fn(Box<NativeArgs>) -> Result<ObjectRef, Error>;

#[derive(EnumAs, EnumIs, Clone)]
pub enum Object {
    NativeFunction(Rc<NativeFunction>),
    Function(Function),
    Macro(Macro),
    Cons(ObjectRef, ObjectRef),
    Symbol(String),
    String(String),
    Int(i64),
    True,
    Nil,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub body: ObjectRef,
    pub parameters: Vec<String>,
    pub captures: HashMap<String, ObjectRef>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Macro {
    pub body: ObjectRef,
    pub parameters: Vec<String>,
}

pub struct Iter(Option<(ObjectRef, ObjectRef)>);

impl Object {
    pub fn cons(a: ObjectRef, b: ObjectRef) -> ObjectRef {
        Rc::new(RefCell::new(Self::Cons(a, b)))
    }

    pub fn car(&self) -> Option<ObjectRef> {
        match self {
            Self::Cons(car, _) => Some(Rc::clone(car)),
            _ => None,
        }
    }

    pub fn cdr(&self) -> Option<ObjectRef> {
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

    pub fn iter_cars(&self) -> Option<impl Iterator<Item = ObjectRef>> {
        Some(self.iter()?.map(|(car, _)| car))
    }
}

impl Iterator for Iter {
    type Item = (ObjectRef, ObjectRef);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((car, cdr)) = &self.0.clone() {
            self.0 = match &*cdr.borrow() {
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
            reader::Value::Cons(car, cdr) => Self::Cons(
                Rc::new(RefCell::new(Object::from(*car))),
                Rc::new(RefCell::new(Object::from(*cdr))),
            ),
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
            Self::Function(Function { body, .. }) => write!(f, "<lambda> {}", body.borrow()),
            Self::Macro(Macro { body, .. }) => write!(f, "<macro> {}", body.borrow()),
            Self::Cons(car, cdr) => write!(f, "({} . {})", car.borrow(), cdr.borrow()),
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
            Self::Function(Function {
                body,
                parameters,
                captures,
            }) => write!(
                f,
                "Object::Function({:?}, {:?} {:?})",
                *body, parameters, captures
            ),
            Self::Macro(Macro { body, parameters }) => {
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
            (Function(a), Function(b)) => a == b,
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
