#![allow(dead_code)]

pub mod ast;
mod environment;

use std::{collections::HashMap, ops::Deref};

use thiserror::Error;

use value::Value;
use vm::{OpCode, Vm};

pub use ast::Ast;
use environment::{Environment, Variable};

#[derive(Debug, Error)]
pub enum Error {
    #[error("vm error: {0}")]
    Vm(#[from] vm::Error),
}

pub struct Compiler {
    environment: Environment,
    macros: HashMap<String, ast::Macro>,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
            macros: HashMap::new(),
        }
    }
}
