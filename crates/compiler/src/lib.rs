#![allow(dead_code)]
#![feature(let_chains)]

mod environment;

use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

use environment::{Environment, Variable};
use identity_hasher::IdentityHasher;
use thiserror::Error;
use value::{Cons, Value};
use vm::{Arity, Constant, OpCode, Vm};
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
        // lambda
        if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 3
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|s| s == "lambda")
            && let Value::Cons(_) | Value::Nil = cons.iter_cars().nth(1).unwrap()
        {
            let body = cons.iter_cars().nth(2).unwrap();
            let parameters = match cons.iter_cars().nth(1).unwrap() {
                Value::Cons(cons) => cons
                    .iter_cars()
                    .map(|car| car.as_symbol().cloned())
                    .collect::<Option<Vec<String>>>()
                    .ok_or_else(|| Error::Compiler("".to_string()))?,
                Value::Nil => Vec::new(),
                _ => unreachable!(),
            };
            self.compile_lambda(parameters.into_iter(), body, opcodes, constants)
        }
        // def
        else if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 3
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| symbol == "def")
            && let Value::Symbol(name) = cons.iter_cars().nth(1).unwrap()
        {
            let expr = cons.iter_cars().nth(2).unwrap();
            self.compile_def(name.as_str(), expr, opcodes, constants)
        }
        //set
        else if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 3
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| symbol == "set")
            && let Value::Symbol(name) = cons.iter_cars().nth(1).unwrap()
        {
            let expr = cons.iter_cars().nth(2).unwrap();
            self.compile_set(name, expr, opcodes, constants)
        }
        // add
        else if let Value::Cons(cons) = value
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
        }
        // fncall
        else if let Value::Cons(cons) = value {
            self.compile_fncall(cons, opcodes, constants)
        }
        // atoms
        else if let Value::Int(i) = value {
            opcodes.push(OpCode::PushInt(*i));
            Ok(())
        } else if let Value::Symbol(symbol) = value {
            self.compile_symbol(symbol.as_str(), opcodes, constants)
        } else {
            todo!()
        }
    }

    fn compile_def(
        &mut self,
        name: &str,
        expr: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        let constant = vm::Constant::Symbol(name.to_string());
        let hash = hash_constant(&constant);
        constants.insert(hash, constant);
        self.compile(expr, opcodes, constants)?;
        opcodes.push(OpCode::DefGlobal(hash));
        Ok(())
    }

    fn compile_set(
        &mut self,
        name: &str,
        expr: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        self.compile(expr, opcodes, constants)?;
        opcodes.push(
            if self.environment.is_global_scope() || self.environment.get(name).is_none() {
                let constant = vm::Constant::Symbol(name.to_string());
                let hash = hash_constant(&constant);
                constants.insert(hash, constant);
                OpCode::SetGlobal(hash)
            } else {
                todo!()
            },
        );
        Ok(())
    }

    fn compile_lambda(
        &mut self,
        parameters: impl Iterator<Item = String> + Clone,
        body: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        self.environment.push_scope(parameters.clone());

        let mut lambda_opcodes = Vec::new();
        self.compile(body, &mut lambda_opcodes, constants)?;
        lambda_opcodes.push(OpCode::Return);

        let opcodes_constant = Constant::Opcodes(lambda_opcodes.into());
        let opcodes_hash = hash_constant(&opcodes_constant);
        constants.insert(opcodes_hash, opcodes_constant);

        let arity = match parameters.count() {
            0 => Arity::Nullary,
            n => Arity::Nary(n),
        };

        opcodes.push(OpCode::Lambda {
            arity,
            body: opcodes_hash,
        });

        for upvalue in self.environment.upvalues() {
            opcodes.push(OpCode::CreateUpValue(upvalue));
        }

        self.environment.pop_scope();

        Ok(())
    }

    fn compile_fncall(
        &mut self,
        exprs: &Cons,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        for expr in exprs.iter_cars() {
            self.compile(expr, opcodes, constants)?
        }

        opcodes.push(OpCode::Call(exprs.iter_cars().count() - 1));

        Ok(())
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

    fn compile_symbol(
        &mut self,
        symbol: &str,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        opcodes.push(
            if self.environment.is_global_scope() || self.environment.get(symbol).is_none() {
                let constant = vm::Constant::Symbol(symbol.to_string());
                let hash = hash_constant(&constant);
                constants.insert(hash, constant);
                OpCode::GetGlobal(hash)
            } else {
                match self.environment.get(symbol).unwrap() {
                    Variable::Local(i) => OpCode::GetLocal(i),
                    _ => todo!(),
                }
            },
        );
        Ok(())
    }
}

fn hash_constant(constant: &Constant) -> u64 {
    let mut hasher = Xxh3::new(0).unwrap();
    constant.hash(&mut hasher);
    hasher.finish()
}
