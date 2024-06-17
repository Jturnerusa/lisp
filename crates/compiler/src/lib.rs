#![allow(dead_code)]
#![feature(let_chains, box_patterns)]

mod environment;

use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

use gc::Gc;

use environment::{Environment, Variable};
use identity_hasher::IdentityHasher;
use thiserror::Error;
use twox_hash::Xxh3Hash64;
use value::{Cons, Value};
use vm::object::Type;
use vm::{Arity, Constant, OpCode, Vm};

type ConstantTable = HashMap<u64, Constant, IdentityHasher>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("compiler error: {0}")]
    Compiler(String),
    #[error("invalid form: {0}")]
    Form(String, Form, Value),
    #[error("vm error {0}")]
    Vm(#[from] vm::Error),
}

#[derive(Clone, Debug)]
enum Parameters {
    WithoutRest(Vec<String>),
    WithRest(Vec<String>, String),
}

#[derive(Clone, Copy, Debug)]
pub enum Form {
    EvalWhenCompile,
    DefMacro,
    Lambda,
    Quote,
    If,
    Def,
    Set,
    List,
    Apply,
    Binary,
    Unary,
    MapInsert,
}

pub struct Compiler {
    environment: Environment,
    vm: Vm,
    macros: HashMap<String, u64>,
}

#[allow(clippy::new_without_default)]
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
        match value {
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "eval-when-compile" => {
                if value.as_cons().unwrap().iter_cars().count() < 2 {
                    Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::EvalWhenCompile,
                        value.clone(),
                    ))
                } else {
                    self.eval_when_compile(
                        value.as_cons().unwrap().iter().nth(1).unwrap(),
                        opcodes,
                        constants,
                    )
                }
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "defmacro" => {
                if value.as_cons().unwrap().iter_cars().count() < 4 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::DefMacro,
                        value.clone(),
                    ));
                };
                let defmacro_name = value
                    .as_cons()
                    .unwrap()
                    .iter_cars()
                    .nth(1)
                    .unwrap()
                    .as_symbol()
                    .ok_or(Error::Form(
                        "non-symbol expression in defmacro name position".to_string(),
                        Form::DefMacro,
                        value.clone(),
                    ))?;
                let parameters =
                    parse_parameters(value.as_cons().unwrap().iter_cars().nth(2).unwrap())?;
                let body = value.as_cons().unwrap().iter_cars().nth(3).unwrap();
                self.compile_defmacro(defmacro_name, &parameters, body)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "lambda" => {
                if value.as_cons().unwrap().iter_cars().count() < 3 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::Lambda,
                        value.clone(),
                    ));
                }
                let parameters =
                    parse_parameters(value.as_cons().unwrap().iter_cars().nth(1).unwrap())?;
                let exprs = value.as_cons().unwrap().iter().nth(2).unwrap();
                self.compile_lambda(&parameters, exprs, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "def" => {
                if value.as_cons().unwrap().iter_cars().count() != 3 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::Def,
                        value.clone(),
                    ));
                }
                let name = value
                    .as_cons()
                    .unwrap()
                    .iter_cars()
                    .nth(1)
                    .unwrap()
                    .as_symbol()
                    .ok_or(Error::Form(
                        "non-symbol expression as def name".to_string(),
                        Form::Def,
                        value.clone(),
                    ))?;
                let expr = value.as_cons().unwrap().iter_cars().nth(2).unwrap();
                self.compile_def(name, expr, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "set!" => {
                if value.as_cons().unwrap().iter_cars().count() != 3 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::Set,
                        value.clone(),
                    ));
                }
                let name = value
                    .as_cons()
                    .unwrap()
                    .iter_cars()
                    .nth(1)
                    .unwrap()
                    .as_symbol()
                    .ok_or(Error::Form(
                        "non-symbol expression as def name".to_string(),
                        Form::Set,
                        value.clone(),
                    ))?;
                let expr = value.as_cons().unwrap().iter_cars().nth(2).unwrap();
                self.compile_set(name, expr, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "if" => {
                if value.as_cons().unwrap().iter_cars().count() != 4 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::If,
                        value.clone(),
                    ));
                }
                let predicate = value.as_cons().unwrap().iter_cars().nth(1).unwrap();
                let then = value.as_cons().unwrap().iter_cars().nth(2).unwrap();
                let r#else = value.as_cons().unwrap().iter_cars().nth(3).unwrap();
                self.compile_branch(predicate, then, r#else, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), Value::Cons(list)))
                if symbol == "quote" =>
            {
                self.quote_list(list, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), atom)) if symbol == "quote" => {
                self.quote(atom, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "list" => {
                if value.as_cons().unwrap().iter_cars().count() < 2 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::List,
                        value.clone(),
                    ));
                }
                let exprs = value.as_cons().unwrap().iter().nth(1).unwrap();
                self.compile_list(exprs, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "apply" => {
                if value.as_cons().unwrap().iter_cars().count() != 3 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::Apply,
                        value.clone(),
                    ));
                }
                let exprs = value.as_cons().unwrap().iter().nth(1).unwrap();
                self.compile_apply(exprs, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _))
                if matches!(
                    symbol.as_str(),
                    "+" | "-"
                        | "*"
                        | "/"
                        | "cons"
                        | "="
                        | "<"
                        | ">"
                        | "map-retrieve"
                        | "setcar!"
                        | "setcdr!"
                ) =>
            {
                if value.as_cons().unwrap().iter_cars().count() != 3 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::Binary,
                        value.clone(),
                    ));
                }
                let lhs = value.as_cons().unwrap().iter_cars().nth(1).unwrap();
                let rhs = value.as_cons().unwrap().iter_cars().nth(2).unwrap();
                let op = match symbol.as_str() {
                    "+" => OpCode::Add,
                    "-" => OpCode::Sub,
                    "*" => OpCode::Mul,
                    "/" => OpCode::Div,
                    "cons" => OpCode::Cons,
                    "=" => OpCode::Eq,
                    "<" => OpCode::Lt,
                    ">" => OpCode::Gt,
                    "map-retrieve" => OpCode::MapRetrieve,
                    "setcar!" => OpCode::SetCar,
                    "setcdr!" => OpCode::SetCdr,
                    _ => unreachable!(),
                };
                self.compile_binary_op(lhs, rhs, op, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _))
                if matches!(
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
                        | "assert"
                ) =>
            {
                if value.as_cons().unwrap().iter_cars().count() != 2 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::Unary,
                        value.clone(),
                    ));
                }
                let expr = value.as_cons().unwrap().iter_cars().nth(1).unwrap();
                let op = match symbol.as_str() {
                    "car" => OpCode::Car,
                    "cdr" => OpCode::Cdr,
                    "cons?" => OpCode::IsType(Type::Cons),
                    "lambda?" => OpCode::IsType(Type::Function),
                    "symbol?" => OpCode::IsType(Type::Symbol),
                    "string?" => OpCode::IsType(Type::String),
                    "int?" => OpCode::IsType(Type::Int),
                    "true?" => OpCode::IsType(Type::True),
                    "nil?" => OpCode::IsType(Type::Nil),
                    "assert" => OpCode::Assert,
                    _ => unreachable!(),
                };
                self.compile_unary_op(expr, op, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), Value::Cons(exprs)))
                if self.macros.contains_key(symbol) =>
            {
                self.eval_macro(symbol, exprs, opcodes, constants)
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "map-create" => {
                opcodes.push(OpCode::MapCreate);
                Ok(())
            }
            Value::Cons(box Cons(Value::Symbol(symbol), _)) if symbol == "map-insert!" => {
                if value.as_cons().unwrap().iter_cars().count() != 4 {
                    return Err(Error::Form(
                        "invalid number of expressions".to_string(),
                        Form::MapInsert,
                        value.clone(),
                    ));
                }
                let map = value.as_cons().unwrap().iter_cars().nth(1).unwrap();
                let key = value.as_cons().unwrap().iter_cars().nth(2).unwrap();
                let val = value.as_cons().unwrap().iter_cars().nth(3).unwrap();
                self.compile_map_insert(map, key, val, opcodes, constants)
            }
            Value::Cons(cons) => self.compile_fncall(cons, opcodes, constants),
            Value::Symbol(symbol) => self.compile_symbol(symbol, opcodes, constants),
            Value::String(string) => self.compile_string(string, opcodes, constants),
            Value::Int(i) => {
                opcodes.push(OpCode::PushInt(*i));
                Ok(())
            }
            Value::True => {
                opcodes.push(OpCode::PushTrue);
                Ok(())
            }
            Value::Nil => {
                opcodes.push(OpCode::PushNil);
                Ok(())
            }
        }
    }

    fn eval_when_compile(
        &mut self,
        exprs: &Cons,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        if !self.environment.is_global_scope() {
            return Err(Error::Compiler(
                "eval-when-compile must exist at the global scope".to_string(),
            ));
        }

        let mut eval_when_compile_opcodes = Vec::new();
        let mut eval_when_compile_constants = HashMap::with_hasher(IdentityHasher::new());

        for expr in exprs.iter_cars() {
            eval_when_compile_opcodes.clear();
            eval_when_compile_constants.clear();

            self.compile(
                expr,
                &mut eval_when_compile_opcodes,
                &mut eval_when_compile_constants,
            )?;

            self.vm
                .load_constants(eval_when_compile_constants.values().cloned());
            self.vm.eval(eval_when_compile_opcodes.as_slice())?;

            opcodes.extend(&eval_when_compile_opcodes);
            constants.extend(
                eval_when_compile_constants
                    .iter()
                    .map(|(hash, constant)| (*hash, constant.clone())),
            );
        }

        Ok(())
    }

    fn compile_defmacro(
        &mut self,
        name: &str,
        parameters: &Parameters,
        body: &Value,
    ) -> Result<(), Error> {
        if !self.environment.is_global_scope() {
            return Err(Error::Compiler(
                "defmacro must exist at the global scope".to_string(),
            ));
        }

        self.environment.push_scope(parameters.clone().into_iter());

        let mut defmacro_opcodes = Vec::new();
        let mut defmacro_constants = ConstantTable::with_hasher(IdentityHasher::new());
        self.compile(body, &mut defmacro_opcodes, &mut defmacro_constants)?;
        defmacro_opcodes.push(OpCode::Return);
        self.environment.pop_scope();

        let defmacro_name_constant = Constant::Symbol(Gc::new(name.to_string()));
        let defmacro_name_hash = hash_constant(&defmacro_name_constant);
        let defmacro_opcodes_constant = Constant::Opcodes(defmacro_opcodes.into());
        let defmacro_opcodes_hash = hash_constant(&defmacro_opcodes_constant);

        self.vm.load_constants(defmacro_constants.into_values());
        self.vm
            .load_constants(std::iter::once(defmacro_name_constant));
        self.vm
            .load_constants(std::iter::once(defmacro_opcodes_constant));

        let arity = match &parameters {
            Parameters::WithoutRest(params) if params.is_empty() => Arity::Nullary,
            Parameters::WithoutRest(params) => Arity::Nary(params.len()),
            Parameters::WithRest(params, _) => Arity::Variadic(params.len()),
        };

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

        for expr in exprs.iter_cars() {
            push_value(&mut self.vm, expr);
        }

        self.vm.call(exprs.iter_cars().count())?;

        let ret = self.vm.eval([].as_slice())?.unwrap();

        let val = Value::try_from(&ret.into_object()).unwrap();

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
        let constant = vm::Constant::Symbol(Gc::new(name.to_string()));
        let hash = hash_constant(&constant);
        constants.insert(hash, constant);
        self.compile(expr, opcodes, constants)?;
        opcodes.push(OpCode::DefGlobal(hash));
        Ok(())
    }

    fn compile_set(
        &mut self,
        symbol: &str,
        expr: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        self.compile(expr, opcodes, constants)?;

        opcodes.push(match self.environment.resolve(symbol) {
            Variable::Local(i) => OpCode::SetLocal(i),
            Variable::Upvalue(i) => OpCode::SetUpValue(i),
            Variable::Global => {
                let constant = Constant::Symbol(Gc::new(symbol.to_string()));
                let hash = hash_constant(&constant);
                constants.insert(hash, constant);
                OpCode::SetGlobal(hash)
            }
        });

        Ok(())
    }

    fn compile_lambda(
        &mut self,
        parameters: &Parameters,
        exprs: &Cons,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        self.environment.push_scope(parameters.clone().into_iter());

        let mut lambda_opcodes = Vec::new();

        for expr in exprs.iter_cars() {
            self.compile(expr, &mut lambda_opcodes, constants)?;
        }
        lambda_opcodes.push(OpCode::Return);

        let opcodes_constant = Constant::Opcodes(lambda_opcodes.into());
        let opcodes_hash = hash_constant(&opcodes_constant);
        constants.insert(opcodes_hash, opcodes_constant);

        let arity = match parameters {
            Parameters::WithoutRest(parameters) if parameters.is_empty() => Arity::Nullary,
            Parameters::WithoutRest(parameters) => Arity::Nary(parameters.len()),
            Parameters::WithRest(parameters, _) => Arity::Variadic(parameters.len()),
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

    fn compile_apply(
        &mut self,
        exprs: &Cons,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        for expr in exprs.iter_cars() {
            self.compile(expr, opcodes, constants)?;
        }

        opcodes.push(OpCode::Apply);

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
        opcodes.push(match self.environment.resolve(symbol) {
            Variable::Local(i) => OpCode::GetLocal(i),
            Variable::Upvalue(i) => OpCode::GetUpValue(i),
            Variable::Global => {
                let constant = Constant::Symbol(Gc::new(symbol.to_string()));
                let hash = hash_constant(&constant);
                constants.insert(hash, constant);
                OpCode::GetGlobal(hash)
            }
        });
        Ok(())
    }

    fn compile_string(
        &mut self,
        string: &str,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        let constant = Constant::String(Gc::new(string.to_string()));
        let hash = hash_constant(&constant);
        constants.insert(hash, constant);
        opcodes.push(OpCode::PushString(hash));
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
        let constant = Constant::Symbol(Gc::new(symbol.to_string()));
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
        let constant = Constant::String(Gc::new(string.to_string()));
        let hash = hash_constant(&constant);

        constants.insert(hash, constant);

        opcodes.push(OpCode::PushString(hash));

        Ok(())
    }

    fn compile_map_insert(
        &mut self,
        map: &Value,
        key: &Value,
        val: &Value,
        opcodes: &mut Vec<OpCode>,
        constants: &mut ConstantTable,
    ) -> Result<(), Error> {
        self.compile(map, opcodes, constants)?;
        self.compile(key, opcodes, constants)?;
        self.compile(val, opcodes, constants)?;
        opcodes.push(OpCode::MapInsert);
        Ok(())
    }
}

impl IntoIterator for Parameters {
    type Item = String;
    type IntoIter = Box<dyn Iterator<Item = String>>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Parameters::WithRest(params, rest) => {
                Box::new(params.into_iter().chain(std::iter::once(rest)))
            }
            Parameters::WithoutRest(params) => Box::new(params.into_iter()),
        }
    }
}

fn hash_constant(constant: &Constant) -> u64 {
    let mut hasher = Xxh3Hash64::with_seed(0);
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
        Value::Symbol(symbol) => vm.push(vm::Object::Symbol(Gc::new(symbol.to_string()))),
        Value::String(string) => vm.push(vm::Object::String(Gc::new(string.to_string()))),
        Value::Int(i) => vm.push(vm::Object::Int(*i)),
        Value::True => vm.push(vm::Object::True),
        Value::Nil => vm.push(vm::Object::Nil),
    }
}

fn parse_parameters(value: &Value) -> Result<Parameters, Error> {
    let mut list = match value {
        Value::Cons(parameters) => parameters
            .iter_cars()
            .map(|car| car.as_symbol().cloned())
            .collect::<Option<Vec<_>>>()
            .ok_or(Error::Form(
                "non-symbol expression in parameter list".to_string(),
                Form::Lambda,
                value.clone(),
            ))?,
        Value::Nil => Vec::new(),
        _ => {
            return Err(Error::Form(
                "non-list expression as parameter list".to_string(),
                Form::Lambda,
                value.clone(),
            ))
        }
    }
    .into_iter();

    let parameters: Vec<String> = list.by_ref().take_while(|param| param != "&rest").collect();

    let rest = list.next();

    if !parameters
        .iter()
        .all(|param| parameters.iter().filter(|x| param == *x).count() == 1)
    {
        return Err(Error::Form(
            "duplicate parameter in parameter list".to_string(),
            Form::Lambda,
            value.clone(),
        ));
    }

    Ok(match rest {
        Some(rest) => Parameters::WithRest(parameters, rest),
        None => Parameters::WithoutRest(parameters),
    })
}
