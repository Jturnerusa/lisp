#![allow(dead_code)]

pub mod compiler;
pub mod reader;
pub mod vm;

use unwrap_enum::{EnumAs, EnumIs};

// A unified lisp value representation.
#[derive(Clone, PartialEq, Eq, Debug, EnumAs, EnumIs)]
pub enum Value {
    Cons(Box<Cons>),
    Symbol(String),
    String(String),
    Int(i64),
    Nil,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Cons(Value, Value);
