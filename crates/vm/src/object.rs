use crate::{Arity, Error, OpCode};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::{self, Debug, Display};
use std::rc::Rc;
use unwrap_enum::{EnumAs, EnumIs};
use value::Value;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Function,
    Cons,
    String,
    Symbol,
    Int,
    True,
    Nil,
    Predicate,
}

#[derive(Clone, Debug, EnumAs, EnumIs, PartialEq)]
pub enum Object {
    NativeFunction(NativeFunction),
    Function(Rc<RefCell<Lambda>>),
    Cons(Cons),
    String(String),
    Symbol(String),
    Int(i64),
    True,
    Nil,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Lambda {
    pub(crate) arity: Arity,
    pub(crate) opcodes: Rc<[OpCode]>,
    pub(crate) upvalues: Vec<Rc<RefCell<Object>>>,
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct NativeFunction(
    pub(crate) Rc<dyn Fn(&[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error>>,
);

#[derive(Clone, Debug, PartialEq)]
pub struct Cons(pub Rc<RefCell<Object>>, pub Rc<RefCell<Object>>);

impl Lambda {
    pub fn arity(&self) -> Arity {
        self.arity
    }
}

impl NativeFunction {
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> + 'static,
    {
        Self(Rc::new(f))
    }
}

impl PartialEq for NativeFunction {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl PartialOrd for NativeFunction {
    fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
        None
    }
}

impl Debug for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("NativeFunction").finish()
    }
}

impl From<&Object> for Type {
    fn from(value: &Object) -> Self {
        match value {
            Object::Function(_) | Object::NativeFunction(_) => Type::Function,
            Object::Cons(_) => Type::Cons,
            Object::String(_) => Type::String,
            Object::Symbol(_) => Type::Symbol,
            Object::Int(_) => Type::Int,
            Object::True => Type::True,
            Object::Nil => Type::Nil,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Function => write!(f, "function"),
            Self::Cons => write!(f, "cons"),
            Self::Symbol => write!(f, "symbol"),
            Self::String => write!(f, "string"),
            Self::Int => write!(f, "int"),
            Self::True => write!(f, "true"),
            Self::Nil => write!(f, "nil"),
            Self::Predicate => write!(f, "predicate"),
        }
    }
}

impl TryFrom<&Object> for Value {
    type Error = ();
    fn try_from(object: &Object) -> Result<Self, Self::Error> {
        Ok(match object {
            Object::Cons(cons) => Value::Cons(Box::new(value::Cons::try_from(cons)?)),
            Object::String(string) => Value::String(string.clone()),
            Object::Symbol(symbol) => Value::Symbol(symbol.clone()),
            Object::Int(i) => Value::Int(*i),
            Object::True => Value::True,
            Object::Nil => Value::Nil,
            _ => return Err(()),
        })
    }
}

impl TryFrom<&Cons> for value::Cons {
    type Error = ();
    fn try_from(value: &Cons) -> Result<Self, Self::Error> {
        Ok(value::Cons(
            Value::try_from(&*value.0.borrow())?,
            Value::try_from(&*value.1.borrow())?,
        ))
    }
}

impl PartialOrd for Object {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match (self, other) {
            (Object::Symbol(a), Object::Symbol(b)) => a.cmp(b),
            (Object::String(a), Object::String(b)) => a.cmp(b),
            (Object::Int(a), Object::Int(b)) => a.cmp(b),
            (Object::True, Object::True) => Ordering::Equal,
            (Object::Nil, Object::Nil) => Ordering::Equal,
            _ => return None,
        })
    }
}

impl Display for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.arity {
            Arity::Nullary => write!(f, "nullary lambda"),
            Arity::Nary(n) => write!(f, "{n}-ary lambda"),
            Arity::Variadic => write!(f, "variadic lambda"),
        }
    }
}

impl Display for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "native function")
    }
}

impl Display for Cons {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.0.borrow(), self.1.borrow())
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NativeFunction(native_function) => write!(f, "{native_function}",),
            Self::Function(function) => write!(f, "{}", function.borrow()),
            Self::Cons(cons) => write!(f, "{cons}"),
            Self::Symbol(symbol) => write!(f, "'{symbol}"),
            Self::String(string) => write!(f, r#""{string}""#),
            Self::Int(i) => write!(f, "{i}"),
            Self::True => write!(f, "true"),
            Self::Nil => write!(f, "nil"),
        }
    }
}
