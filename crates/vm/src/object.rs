use crate::{Arity, Error, OpCode};
use gc::{Gc, Trace};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Debug, Display};
use std::ops::Deref;
use std::ptr::NonNull;
use std::rc::Rc;
use unwrap_enum::{EnumAs, EnumIs};
use value::Value;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Function,
    Cons,
    Map,
    String,
    Symbol,
    Int,
    Char,
    True,
    Nil,
    Predicate,
}

#[derive(Clone, Debug, EnumAs, EnumIs, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HashMapKey {
    String(Gc<String>),
    Symbol(Gc<String>),
    Int(i64),
    Char(char),
    True,
    Nil,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Object {
    NativeFunction(NativeFunction),
    Function(Gc<RefCell<Lambda>>),
    Cons(Gc<RefCell<Cons>>),
    HashMap(Gc<RefCell<HashMap<HashMapKey, Object>>>),
    String(Gc<String>),
    Symbol(Gc<String>),
    Int(i64),
    Char(char),
    True,
    Nil,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Lambda {
    pub(crate) arity: Arity,
    pub(crate) opcodes: Rc<[OpCode]>,
    pub(crate) upvalues: Vec<Gc<RefCell<Object>>>,
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct NativeFunction(pub(crate) Rc<dyn Fn(&mut [crate::Local]) -> Result<Object, Error>>);

#[derive(Clone, Debug, PartialEq)]
pub struct Cons(pub Object, pub Object);

#[derive(Clone, Debug)]
pub struct IterCons(Option<Cons>);

#[derive(Clone, Debug)]
pub struct IterCars(IterCons);

impl Cons {
    pub fn iter(&self) -> IterCons {
        IterCons(Some(self.clone()))
    }

    pub fn iter_cars(&self) -> IterCars {
        IterCars(self.iter())
    }
}

impl Lambda {
    pub fn arity(&self) -> Arity {
        self.arity
    }
}

impl NativeFunction {
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&mut [crate::Local]) -> Result<Object, Error> + 'static,
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
            Object::HashMap(_) => Type::Map,
            Object::String(_) => Type::String,
            Object::Symbol(_) => Type::Symbol,
            Object::Int(_) => Type::Int,
            Object::Char(_) => Type::Char,
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
            Self::Map => write!(f, "map"),
            Self::Symbol => write!(f, "symbol"),
            Self::String => write!(f, "string"),
            Self::Int => write!(f, "int"),
            Self::Char => write!(f, "char"),
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
            Object::Cons(cons) => Value::Cons(Box::new(value::Cons::try_from(
                cons.deref().borrow().deref(),
            )?)),
            Object::String(string) => Value::String(string.deref().clone()),
            Object::Symbol(symbol) => Value::Symbol(symbol.deref().clone()),
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
            Value::try_from(&value.0)?,
            Value::try_from(&value.1)?,
        ))
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Object::Cons(a), Object::Cons(b)) => a == b,
            (Object::String(a), Object::String(b)) => a == b,
            (Object::Symbol(a), Object::Symbol(b)) => a == b,
            (Object::Int(a), Object::Int(b)) => a == b,
            (Object::True, Object::True) => true,
            (Object::Nil, Object::Nil) => true,
            _ => false,
        }
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
            Arity::Variadic(n) => write!(f, "{n}-ary variadic lambda"),
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
        write!(f, "{} {}", self.0, self.1)
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NativeFunction(native_function) => write!(f, "{native_function}",),
            Self::Function(function) => write!(f, "{}", function.deref().borrow()),
            Self::Cons(cons) => write!(f, "({})", cons.deref().borrow()),
            Self::HashMap(map) => {
                for (key, val) in map.deref().borrow().iter() {
                    writeln!(f, "{key} => {val},")?;
                }
                Ok(())
            }
            Self::Symbol(symbol) => write!(f, "'{symbol}"),
            Self::String(string) => write!(f, r#""{string}""#),
            Self::Int(i) => write!(f, "{i}"),
            Self::Char(c) => write!(f, r#"'{c}'"#),
            Self::True => write!(f, "true"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

impl Display for HashMapKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::String(string) => write!(f, r#""{string}""#),
            Self::Symbol(symbol) => write!(f, "'{symbol}"),
            Self::Char(c) => write!(f, "'{c}'"),
            Self::Int(i) => write!(f, "{i}"),
            Self::True => write!(f, "true"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

impl Iterator for IterCons {
    type Item = Cons;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.0.take();
        self.0 = if let Some(current) = current.clone() {
            current
                .1
                .as_cons()
                .map(|cons| cons.deref().borrow().clone())
        } else {
            None
        };
        current
    }
}

impl Iterator for IterCars {
    type Item = Object;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|cons| cons.0.clone())
    }
}

impl TryFrom<&Object> for HashMapKey {
    type Error = ();
    fn try_from(value: &Object) -> Result<Self, Self::Error> {
        Ok(match value {
            Object::Symbol(symbol) => Self::Symbol(symbol.clone()),
            Object::String(string) => Self::String(string.clone()),
            Object::Char(c) => Self::Char(*c),
            Object::Int(i) => Self::Int(*i),
            Object::True => Self::True,
            Object::Nil => Self::Nil,
            _ => return Err(()),
        })
    }
}

unsafe impl Trace for OpCode {
    unsafe fn trace(&self, _: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>)) {}
}

unsafe impl Trace for HashMapKey {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>)) {
        match self {
            Self::Symbol(symbol) => symbol.trace(tracer),
            Self::String(string) => string.trace(tracer),
            _ => (),
        }
    }
}

unsafe impl Trace for Lambda {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>)) {
        self.upvalues.trace(tracer);
    }
}

unsafe impl Trace for Cons {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>)) {
        self.0.trace(tracer);
        self.1.trace(tracer);
    }
}

unsafe impl Trace for Object {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>)) {
        match self {
            Object::Function(function) => function.trace(tracer),
            Object::Cons(cons) => cons.trace(tracer),
            Object::Symbol(symbol) => symbol.trace(tracer),
            Object::String(string) => string.trace(tracer),
            _ => (),
        }
    }
}
