#![allow(dead_code)]
#![feature(let_chains)]

mod environment;

use std::{
    cell::RefCell,
    collections::HashMap,
    hash::{Hash, Hasher},
    ops::Deref,
    rc::Rc,
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
        // defmacro
        if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 4
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| symbol == "defmacro")
            && let Value::Symbol(name) = cons.iter_cars().nth(1).unwrap()
            && let Value::Cons(_) | Value::Nil = cons.iter_cars().nth(2).unwrap()
        {
            let parameters = match cons.iter_cars().nth(2).unwrap() {
                Value::Cons(cons) => cons
                    .iter_cars()
                    .map(|car| car.as_symbol().cloned())
                    .collect::<Option<Vec<String>>>()
                    .ok_or_else(|| Error::Compiler("".to_string()))?,
                Value::Nil => Vec::new(),
                _ => unreachable!(),
            };
            let body = cons.iter_cars().nth(3).unwrap();
            self.compile_defmacro(name.as_str(), parameters.into_iter(), body)
        }
        // lambda
        else if let Value::Cons(cons) = value
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
        // if
        else if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 4
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| symbol == "if")
        {
            let predicate = cons.iter_cars().nth(1).unwrap();
            let then = cons.iter_cars().nth(2).unwrap();
            let els = cons.iter_cars().nth(3).unwrap();
            self.compile_branch(predicate, then, els, opcodes, constants)
        }
        // quote
        else if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 2
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| symbol == "quote")
        {
            self.quote(cons.iter_cars().nth(1).unwrap(), opcodes, constants)
        }
        //list
        else if let Value::Cons(cons) = value
            && cons.iter_cars().count() > 0
            && let Value::Cons(exprs) = &cons.deref().1
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| symbol == "list")
        {
            self.compile_list(exprs, opcodes, constants)
        }
        // add
        else if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 3
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| matches!(symbol.as_str(), "+" | "-" | "*" | "/" | "cons"))
        {
            let lhs = cons.iter_cars().nth(1).unwrap();
            let rhs = cons.iter_cars().nth(2).unwrap();
            self.compile_binary_op(
                lhs,
                rhs,
                match cons
                    .iter_cars()
                    .nth(0)
                    .unwrap()
                    .as_symbol()
                    .unwrap()
                    .as_str()
                {
                    "+" => OpCode::Add,
                    "-" => OpCode::Sub,
                    "*" => OpCode::Mul,
                    "/" => OpCode::Div,
                    "cons" => OpCode::Cons,
                    _ => unreachable!(),
                },
                opcodes,
                constants,
            )
        }
        // unary ops
        else if let Value::Cons(cons) = value
            && cons.iter_cars().count() == 2
            && cons
                .iter_cars()
                .nth(0)
                .unwrap()
                .as_symbol()
                .is_some_and(|symbol| {
                    matches!(
                        symbol.as_str(),
                        "car"
                            | "cdr"
                            | "cons?"
                            | "lambda?"
                            | "symbol?"
                            | "string?"
                            | "int?"
                            | "true?"
                            | "nil?"
                    )
                })
        {
            let expr = cons.iter_cars().nth(1).unwrap();
            self.compile_unary_op(
                expr,
                match cons
                    .iter_cars()
                    .nth(0)
                    .unwrap()
                    .as_symbol()
                    .unwrap()
                    .as_str()
                {
                    "car" => OpCode::Car,
                    "cdr" => OpCode::Cdr,
                    "cons?" => OpCode::IsType(vm::Type::Cons),
                    "lambda?" => OpCode::IsType(vm::Type::Function),
                    "symbol?" => OpCode::IsType(vm::Type::Symbol),
                    "string?" => OpCode::IsType(vm::Type::String),
                    "int?" => OpCode::IsType(vm::Type::Int),
                    "true?" => OpCode::IsType(vm::Type::True),
                    "nil?" => OpCode::IsType(vm::Type::Nil),
                    _ => unreachable!(),
                },
                opcodes,
                constants,
            )
        }
        // eval macro
        else if let Value::Cons(cons) = value
            && let Value::Cons(exprs) = &cons.deref().1
            && cons.iter_cars().count() > 0
            && let Value::Symbol(name) = cons.iter_cars().nth(0).unwrap()
            && self.macros.contains_key(name)
        {
            self.eval_macro(name, exprs, opcodes, constants)
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
        } else if let Value::True = value {
            opcodes.push(OpCode::PushTrue);
            Ok(())
        } else {
            todo!()
        }
    }

    fn compile_defmacro(
        &mut self,
        name: &str,
        parameters: impl Iterator<Item = String> + Clone,
        body: &Value,
    ) -> Result<(), Error> {
        if !self.environment.is_global_scope() {
            return Err(Error::Compiler(
                "defmacro must exist at the global scope".to_string(),
            ));
        }

        self.environment.push_scope(
            parameters
                .clone()
                .chain(std::iter::once("&rest".to_string())),
        );

        let mut defmacro_opcodes = Vec::new();
        let mut defmacro_constants = ConstantTable::with_hasher(IdentityHasher::new());
        self.compile(body, &mut defmacro_opcodes, &mut defmacro_constants)?;
        defmacro_opcodes.push(OpCode::Return);
        self.environment.pop_scope();

        let defmacro_name_constant = Constant::Symbol(name.to_string());
        let defmacro_name_hash = hash_constant(&defmacro_name_constant);
        let defmacro_opcodes_constant = Constant::Opcodes(defmacro_opcodes.into());
        let defmacro_opcodes_hash = hash_constant(&defmacro_opcodes_constant);

        self.vm.load_constants(defmacro_constants.into_values());
        self.vm
            .load_constants(std::iter::once(defmacro_name_constant));
        self.vm
            .load_constants(std::iter::once(defmacro_opcodes_constant));

        let arity = Arity::Nary(parameters.count());

        self.vm.lambda(arity, defmacro_opcodes_hash)?;
        self.vm.def_global(defmacro_name_hash)?;
        self.macros.insert(name.to_string(), defmacro_name_hash);

        Ok(())
    }

    fn eval_macro(
        &mut self,
        name: &str,
        exprs: &Cons,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        let defmacro_name_hash = self.macros.get(name).unwrap();

        self.vm.get_global(*defmacro_name_hash)?;

        let arity = self
            .vm
            .stack()
            .last()
            .unwrap()
            .borrow()
            .as_function()
            .unwrap()
            .borrow()
            .arity();

        let rest = match (arity, exprs.iter_cars().count()) {
            (Arity::Nary(n), count) if count > n => count - n,
            (Arity::Nary(n), count) if count == n => 0,
            _ => {
                return Err(Error::Compiler(format!(
                    "invalid number of parameters to macro {name}"
                )))
            }
        };

        for expr in exprs.iter_cars() {
            push_value(&mut self.vm, expr);
        }

        self.vm.list(rest)?;

        self.vm.call(match arity {
            Arity::Nary(n) => n + 1,
            _ => unreachable!(),
        })?;

        let ret = self.vm.eval([].as_slice())?.unwrap();

        let val = Value::try_from(ret.borrow().deref()).unwrap();

        self.compile(&val, opcodes, constants)?;

        Ok(())
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

    fn compile_branch(
        &mut self,
        predicate: &Value,
        then: &Value,
        els: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        let mut then_opcodes = Vec::new();
        let mut els_opcodes = Vec::new();

        self.compile(predicate, opcodes, constants)?;
        self.compile(then, &mut then_opcodes, constants)?;
        self.compile(els, &mut els_opcodes, constants)?;

        opcodes.push(OpCode::Branch(then_opcodes.len() + 1));
        then_opcodes.push(OpCode::Jmp(els_opcodes.len().try_into().unwrap()));

        opcodes.extend(then_opcodes);
        opcodes.extend(els_opcodes);

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
        if !self.environment.is_global_scope() {
            self.environment.insert(symbol);
        }
        opcodes.push(match self.environment.get(symbol) {
            Some(Variable::Local(i)) => OpCode::GetLocal(i),
            Some(Variable::Upvalue(i)) => OpCode::GetUpValue(i),
            None => {
                let constant = Constant::Symbol(symbol.to_string());
                let hash = hash_constant(&constant);
                constants.insert(hash, constant);
                OpCode::GetGlobal(hash)
            }
        });
        Ok(())
    }

    fn compile_unary_op(
        &mut self,
        expr: &Value,
        op: OpCode,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        self.compile(expr, opcodes, constants)?;
        opcodes.push(op);
        Ok(())
    }

    fn compile_list(
        &mut self,
        exprs: &Cons,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        for expr in exprs.iter_cars() {
            self.compile(expr, opcodes, constants)?;
        }

        opcodes.push(OpCode::List(exprs.iter_cars().count()));

        Ok(())
    }

    fn quote(
        &mut self,
        value: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        match value {
            Value::Cons(cons) => self.quote_list(cons, opcodes, constants)?,
            Value::Symbol(symbol) => self.quote_symbol(symbol, opcodes, constants)?,
            Value::String(string) => self.quote_string(string, opcodes, constants)?,
            Value::Int(i) => opcodes.push(OpCode::PushInt(*i)),
            Value::True => opcodes.push(OpCode::PushTrue),
            Value::Nil => opcodes.push(OpCode::PushNil),
        }
        Ok(())
    }

    fn quote_list(
        &mut self,
        list: &Cons,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        for element in list.iter_cars() {
            self.quote(element, opcodes, constants)?
        }

        opcodes.push(OpCode::List(list.iter_cars().count()));

        todo!()
    }

    fn quote_symbol(
        &mut self,
        symbol: &str,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        let constant = Constant::Symbol(symbol.to_string());
        let hash = hash_constant(&constant);

        constants.insert(hash, constant);

        opcodes.push(OpCode::PushSymbol(hash));

        Ok(())
    }

    fn quote_string(
        &mut self,
        string: &str,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        let constant = Constant::String(string.to_string());
        let hash = hash_constant(&constant);

        constants.insert(hash, constant);

        opcodes.push(OpCode::PushString(hash));

        Ok(())
    }
}

fn hash_constant(constant: &Constant) -> u64 {
    let mut hasher = Xxh3::new(0).unwrap();
    constant.hash(&mut hasher);
    hasher.finish()
}

fn push_list(vm: &mut Vm, list: &Cons) {
    for e in list.iter_cars() {
        push_value(vm, e);
    }
    vm.list(list.iter_cars().count()).unwrap();
}

fn push_value(vm: &mut Vm, value: &Value) {
    match value {
        Value::Cons(cons) => push_list(vm, cons),
        Value::Symbol(symbol) => vm.push(Rc::new(RefCell::new(vm::Object::Symbol(
            symbol.to_string(),
        )))),
        Value::String(string) => vm.push(Rc::new(RefCell::new(vm::Object::String(
            string.to_string(),
        )))),
        Value::Int(i) => vm.push(Rc::new(RefCell::new(vm::Object::Int(*i)))),
        Value::True => vm.push(Rc::new(RefCell::new(vm::Object::True))),
        Value::Nil => vm.push(Rc::new(RefCell::new(vm::Object::Nil))),
    }
}
