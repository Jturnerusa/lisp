use std::fmt;

use crate::Object;

#[derive(Clone, Debug)]
pub enum Error {
    Type(Type, Type),
    Parameters,
    NotFound(String),
    NotFunction(String),
    Lambda(String),
}

#[derive(Clone, Debug)]
pub enum Type {
    Function,
    Macro,
    Cons,
    Symbol,
    String,
    Int,
    True,
    Nil,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Function => write!(f, "function"),
            Self::Macro => write!(f, "macro"),
            Self::Cons => write!(f, "cons"),
            Self::Symbol => write!(f, "symbol"),
            Self::String => write!(f, "string"),
            Self::Int => write!(f, "integer"),
            Self::True => write!(f, "true"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(expected, got) => write!(f, "expected type: {}: got :{}", expected, got),
            Self::Parameters => write!(f, "invalid parameters"),
            Self::NotFound(var) => write!(f, "variable not found: {}", var),
            Self::NotFunction(var) => write!(f, "variable is not function: {}", var),
            Self::Lambda(var) => write!(f, "lambda expression is malformed: {}", var),
        }
    }
}

impl std::error::Error for Error {}

impl From<&Object> for Type {
    fn from(other: &Object) -> Type {
        match other {
            Object::NativeFunction(..) | Object::Function(..) => Type::Function,
            Object::Macro(..) => Type::Macro,
            Object::Cons(..) => Type::Cons,
            Object::Symbol(_) => Type::Symbol,
            Object::String(_) => Type::String,
            Object::Int(_) => Type::Int,
            Object::True => Type::True,
            Object::Nil => Type::Nil,
        }
    }
}
