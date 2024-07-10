#![allow(dead_code)]
#![feature(let_chains, impl_trait_in_assoc_type)]

use std::collections::HashSet;

mod ast;
mod environment;

#[derive(Clone, Debug)]
pub(crate) enum Type {
    List(Box<Type>),
    Cons,
    Function,
    Symbol,
    String,
    Char,
    Int,
    Bool,
    Nil,
    Union(HashSet<Type>),
}
mod il;
