#![allow(dead_code)]
#![feature(let_chains)]

mod environment;

use std::{
    cell::RefCell,
    collections::HashMap,
    hash::{Hash, Hasher},
    iter,
    ops::Deref,
    rc::Rc,
};

use environment::{Environment, Variable};
use identity_hasher::IdentityHasher;
use thiserror::Error;
use value::Value;
use vm::{Arity, OpCode, Vm};
use xxhash::Xxh3;

type ConstantsTable = HashMap<u64, vm::Constant, IdentityHasher>;

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("compiler error: {0}")]
    Compiler(String),
    #[error("vm error: {0}")]
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
        constants: &mut ConstantsTable,
    ) -> Result<(), Error> {
        match dbg!(value) {
            Value::List(list) => match list.as_slice() {
                [Value::Symbol(symbol), _] if symbol == "eval-when-compile" => todo!(),
                [Value::Symbol(symbol), Value::Symbol(name), Value::List(parameters), body]
                    if symbol == "defmacro" =>
                {
                    self.compile_defmacro(
                        name.as_str(),
                        parameters
                            .iter()
                            .map(Value::as_symbol)
                            .collect::<Option<Vec<_>>>()
                            .ok_or_else(|| {
                                Error::Compiler("non-symbol parameter in defmacro expr".to_string())
                            })?
                            .into_iter()
                            .cloned(),
                        body,
                    )
                }
                [Value::Symbol(symbol), exprs @ ..] if self.macros.contains_key(symbol) => {
                    self.eval_macro(symbol.as_str(), exprs, opcodes, constants)
                }
                [Value::Symbol(symbol), expr] if symbol == "quote" => {
                    self.quote(expr, opcodes, constants)
                }
                [Value::Symbol(symbol), exprs @ ..] if symbol == "vec" => {
                    self.compile_make_vec(exprs, opcodes, constants)
                }
                [Value::Symbol(symbol), a, b] if symbol == "+" => {
                    self.compile_binary_op(a, b, || OpCode::Add, opcodes, constants)
                }
                _ => todo!(),
            },
            Value::Symbol(symbol) => self.compile_symbol(symbol, opcodes, constants),
            Value::Int(i) => {
                opcodes.push(OpCode::PushInt(*i));
                Ok(())
            }
            _ => todo!(),
        }
    }

    fn eval_when_compile(&mut self, expr: &Value) -> Result<(), Error> {
        if !self.environment.is_global_scope() {
            return Err(Error::Compiler(
                "eval-when-compile expected to be at global scope".to_string(),
            ));
        }

        let mut opcodes = Vec::new();
        let mut constants = HashMap::with_hasher(IdentityHasher::new());

        self.compile(expr, &mut opcodes, &mut constants)?;

        self.vm.load_constants(constants.values().cloned());
        self.vm.eval(opcodes.as_slice())?;

        Ok(())
    }

    fn compile_defmacro(
        &mut self,
        name: &str,
        parameters: impl Iterator<Item = String> + Clone,
        body: &Value,
    ) -> Result<(), Error> {
        if !self.environment.is_global_scope() {
            return Err(Error::Compiler(
                "defmacro expected to be at global scope".to_string(),
            ));
        }

        self.environment.push_scope(
            parameters
                .clone()
                .chain(std::iter::once("&rest".to_string())),
        );

        let mut opcodes = Vec::new();
        let mut constants = HashMap::with_hasher(IdentityHasher::new());

        self.compile(body, &mut opcodes, &mut constants)?;
        opcodes.push(OpCode::Return);

        let opcodes_constant = vm::Constant::Opcodes(opcodes.into());
        let opcodes_constant_hash = hash_constant(&opcodes_constant);

        let arity = match parameters.count() {
            0 => Arity::Nullary,
            i => Arity::Nary(i + 1),
        };

        let lambda_name_constant = vm::Constant::Symbol(name.to_string());
        let lambda_name_constant_hash = hash_constant(&lambda_name_constant);

        self.vm.load_constants(constants.values().cloned());
        self.vm.load_constants(iter::once(opcodes_constant));
        self.vm.load_constants(iter::once(lambda_name_constant));
        self.vm.lambda(arity, opcodes_constant_hash)?;
        self.vm.def_global(lambda_name_constant_hash)?;

        self.macros
            .insert(name.to_string(), lambda_name_constant_hash);

        Ok(())
    }

    fn eval_macro(
        &mut self,
        name: &str,
        exprs: &[Value],
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantsTable,
    ) -> Result<(), Error> {
        self.vm.get_global(*self.macros.get(name).unwrap())?;

        let arity = self
            .vm
            .stack()
            .last()
            .unwrap()
            .deref()
            .borrow()
            .as_function()
            .cloned()
            .unwrap()
            .deref()
            .borrow()
            .arity();

        for expr in exprs {
            self.vm.push(Rc::new(RefCell::new(match expr {
                Value::Symbol(symbol) => vm::Object::Symbol(symbol.clone()),
                Value::Int(i) => vm::Object::Int(*i),
                _ => todo!(),
            })))
        }

        let rest = match arity {
            Arity::Nary(n) if exprs.len() == n - 1 => 0,
            Arity::Nary(n) if exprs.len() >= n - 1 => exprs.len() - n - 1,
            _ => {
                return Err(Error::Compiler(
                    "wrong number of parameters to macro".to_string(),
                ))
            }
        };

        self.vm.make_vec(rest)?;

        self.vm.call(match arity {
            Arity::Nary(n) => n,
            _ => unreachable!(),
        })?;

        let ret = self.vm.eval(&[])?.unwrap();

        let val = Value::try_from(ret.borrow().deref()).unwrap();

        self.compile(&val, opcodes, constants)?;

        Ok(())
    }

    fn compile_make_vec(
        &mut self,
        exprs: &[Value],
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantsTable,
    ) -> Result<(), Error> {
        for expr in exprs {
            self.compile(expr, opcodes, constants)?;
        }
        opcodes.push(OpCode::Vec(exprs.len()));
        Ok(())
    }

    fn compile_binary_op(
        &mut self,
        a: &Value,
        b: &Value,
        op: impl Fn() -> OpCode,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantsTable,
    ) -> Result<(), Error> {
        self.compile(a, opcodes, constants)?;
        self.compile(b, opcodes, constants)?;
        opcodes.push(op());
        Ok(())
    }

    fn compile_symbol(
        &mut self,
        symbol: &str,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantsTable,
    ) -> Result<(), Error> {
        opcodes.push(
            if self.environment.is_global_scope() || self.environment.get(symbol).is_none() {
                let constant = vm::Constant::Symbol(symbol.to_string());
                let hash = hash_constant(&constant);
                constants.insert(hash, constant);
                OpCode::PushSymbol(hash)
            } else {
                match self.environment.get(symbol).unwrap() {
                    Variable::Local(i) => OpCode::GetLocal(i),
                    Variable::Upvalue(i) => OpCode::GetUpValue(i),
                }
            },
        );

        Ok(())
    }

    fn quote(
        &mut self,
        expr: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantsTable,
    ) -> Result<(), Error> {
        match expr {
            Value::Symbol(symbol) => self.quote_symbol(symbol, opcodes, constants)?,
            _ => todo!(),
        }

        Ok(())
    }

    fn quote_symbol(
        &mut self,
        symbol: &str,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantsTable,
    ) -> Result<(), Error> {
        let constant = vm::Constant::Symbol(symbol.to_string());
        let hash = hash_constant(&constant);
        constants.insert(hash, constant);
        opcodes.push(OpCode::PushSymbol(hash));
        Ok(())
    }
}

fn hash_constant(constant: &vm::Constant) -> u64 {
    let mut hasher = Xxh3::new(0).unwrap();
    constant.hash(&mut hasher);
    hasher.finish()
}
