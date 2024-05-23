#![allow(dead_code)]

use unwrap_enum::{EnumAs, EnumIs};

#[derive(Clone, PartialEq, Eq, Debug, EnumAs, EnumIs)]
pub enum Value {
    List(Vec<Value>),
    Symbol(String),
    String(String),
    Int(i64),
    True,
    Nil,
}
