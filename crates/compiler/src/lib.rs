#![allow(dead_code)]
#![feature(let_chains)]

mod environment;

use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

use environment::Environment;
use identity_hasher::IdentityHasher;
use thiserror::Error;
use value::{Cons, Value};
use vm::{Constant, OpCode, Vm};
use xxhash::Xxh3;

type ConstantTable = HashMap<u64, Constant, IdentityHasher>;

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("compiler error: {0}")]
    Compiler(String),
    #[error("vm error {0}")]
    Vm(#[from] vm::Error),
}

pub struct Compiler {
    environment: Environment,
    vm: Vm,
    macros: HashMap<String, u64>,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
            vm: Vm::new(),
            macros: HashMap::new(),
        }
    }

    pub fn compile(
        &mut self,
        value: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 3
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| symbol == "+")
        {
            let lhs = cons.iter_cars().nth(1).unwrap();
            let rhs = cons.iter_cars().nth(2).unwrap();
            self.compile_binary_op(lhs, rhs, OpCode::Add, opcodes, constants)
        } else {
            match value {
                Value::Int(i) => {
                    opcodes.push(OpCode::PushInt(*i));
                    Ok(())
                }
                _ => todo!(),
            }
        }
    }

    fn compile_binary_op(
        &mut self,
        lhs: &Value,
        rhs: &Value,
        op: OpCode,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        self.compile(lhs, opcodes, constants)?;
        self.compile(rhs, opcodes, constants)?;
        opcodes.push(op);
        Ok(())
    }
}

fn hash_constant(constant: &Constant) -> u64 {
    let mut hasher = Xxh3::new(0).unwrap();
    constant.hash(&mut hasher);
    hasher.finish()
}
