#![allow(dead_code)]

pub mod object;

use crate::object::{Cons, Lambda, NativeFunction, Type};
use identity_hasher::IdentityHasher;
use std::cell::RefCell;
use std::cmp::{Ordering, PartialOrd};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;
use thiserror::Error;
use unwrap_enum::{EnumAs, EnumIs};
use xxhash::Xxh3;

pub use crate::object::Object;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arity {
    Nullary,
    Nary(usize),
    Variadic,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("type error: expected {expected}: received: {recieved}")]
    Type { expected: Type, recieved: Type },
    #[error("variable not found: {0}")]
    NotFound(String),
    #[error("invalid parameters: {0}")]
    Parameters(String),
    #[error("assertion failed: {0}")]
    Assert(String),
    #[error("cannot compare this combination of types: {0} {1}")]
    Cmp(Type, Type),
    #[error("other error: {0}")]
    Other(#[from] Box<dyn std::error::Error>),
}

#[derive(Clone, Debug, EnumAs, EnumIs, PartialEq, Eq, Hash)]
pub enum Constant {
    String(String),
    Symbol(String),
    Opcodes(Rc<[OpCode]>),
}

#[derive(Clone, Copy, Debug, EnumAs, EnumIs, PartialEq, Eq, Hash)]
pub enum OpCode {
    DefGlobal(u64),
    SetGlobal(u64),
    GetGlobal(u64),
    SetLocal(usize),
    GetLocal(usize),
    SetUpValue(usize),
    GetUpValue(usize),
    Call(usize),
    Tail(usize),
    Return,
    Lambda { arity: Arity, body: u64 },
    CreateUpValue(UpValue),
    PushSymbol(u64),
    PushInt(i64),
    PushChar(char),
    PushString(u64),
    PushTrue,
    PushNil,
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Car,
    Cdr,
    Cons,
    List(usize),
    Jmp(isize),
    Branch(usize),
    IsType(Type),
    Assert,
    Lt,
    Gt,
    Eq,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UpValue {
    Local(usize),
    UpValue(usize),
}

#[derive(Clone, Debug)]
struct Frame {
    function: Option<Lambda>,
    pc: usize,
    bp: usize,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Value {
    Value(Object),
    UpValue(Rc<RefCell<Object>>),
}

pub struct Vm {
    globals: HashMap<String, Object>,
    constants: HashMap<u64, Constant, IdentityHasher>,
    stack: Vec<Value>,
    frames: Vec<Frame>,
    current_function: Option<Lambda>,
    pc: usize,
    bp: usize,
}

#[allow(clippy::new_without_default)]
impl Vm {
    pub fn new() -> Self {
        Self {
            globals: HashMap::new(),
            constants: HashMap::with_hasher(IdentityHasher::new()),
            stack: Vec::new(),
            frames: Vec::new(),
            current_function: None,
            pc: 0,
            bp: 0,
        }
    }

    pub fn load_constants(&mut self, constants: impl Iterator<Item = Constant>) {
        for constant in constants {
            let mut hasher = Xxh3::new(0).unwrap();
            constant.hash(&mut hasher);
            let hash = hasher.finish();
            self.constants.insert(hash, constant);
        }
    }

    pub fn load_native_function<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&mut [Value]) -> Result<Object, Error> + 'static,
    {
        let native_function = NativeFunction::new(f);
        self.globals
            .insert(name.to_string(), Object::NativeFunction(native_function));
    }

    pub fn eval(&mut self, opcodes: &[OpCode]) -> Result<Option<Value>, Error> {
        loop {
            let opcode = if let Some(function) = &self.current_function {
                function.opcodes[self.pc]
            } else if self.pc < opcodes.len() {
                opcodes[self.pc]
            } else {
                let ret = self.stack.pop();
                self.stack.clear();
                self.pc = 0;
                self.bp = 0;
                return Ok(ret);
            };

            self.pc += 1;

            match opcode {
                OpCode::DefGlobal(global) => self.def_global(global)?,
                OpCode::SetGlobal(global) => self.set_global(global)?,
                OpCode::GetGlobal(global) => self.get_global(global)?,
                OpCode::SetLocal(local) => self.set_local(local)?,
                OpCode::GetLocal(local) => self.get_local(local)?,
                OpCode::SetUpValue(upvalue) => self.set_upvalue(upvalue)?,
                OpCode::GetUpValue(upvalue) => self.get_upvalue(upvalue)?,
                OpCode::Call(args) => self.call(args)?,
                OpCode::Return => self.ret()?,
                OpCode::Lambda { arity, body } => self.lambda(arity, body)?,
                OpCode::CreateUpValue(upvalue) => self.create_upvalue(upvalue)?,
                OpCode::PushSymbol(symbol) => {
                    let symbol_value = self
                        .constants
                        .get(&symbol)
                        .unwrap()
                        .as_symbol()
                        .cloned()
                        .unwrap();
                    self.stack
                        .push(Value::Value(Object::Symbol(symbol_value.clone())));
                }
                OpCode::PushString(string) => {
                    let string_value = self
                        .constants
                        .get(&string)
                        .unwrap()
                        .as_string()
                        .cloned()
                        .unwrap();
                    self.stack
                        .push(Value::Value(Object::String(string_value.clone())));
                }
                OpCode::PushInt(i) => self.stack.push(Value::Value(Object::Int(i))),
                OpCode::PushChar(c) => self.stack.push(Value::Value(Object::Char(c))),
                OpCode::PushTrue => self.stack.push(Value::Value(Object::True)),
                OpCode::PushNil => self.stack.push(Value::Value(Object::Nil)),
                OpCode::Pop => {
                    self.stack.pop().unwrap();
                }
                OpCode::Add => self.add()?,
                OpCode::Sub => self.sub()?,
                OpCode::Mul => self.mul()?,
                OpCode::Div => self.div()?,
                OpCode::Cons => self.cons()?,
                OpCode::Car => self.car()?,
                OpCode::Cdr => self.cdr()?,
                OpCode::List(args) => self.list(args)?,
                OpCode::Branch(offset) => self.branch(offset)?,
                OpCode::Jmp(offset) => {
                    self.pc += offset as usize;
                }
                OpCode::IsType(ty) => self.is_type(ty)?,
                OpCode::Assert => self.assert()?,
                OpCode::Eq => self.eq()?,
                OpCode::Lt => self.lt()?,
                OpCode::Gt => self.gt()?,
                _ => todo!(),
            }
        }
    }

    pub fn peek(&self, i: usize) -> Option<&Value> {
        self.stack.get(self.stack.len() - i - 1)
    }

    pub fn push(&mut self, object: Object) {
        self.stack.push(Value::Value(object));
    }

    pub fn pop(&mut self) -> Option<Value> {
        self.stack.pop()
    }

    pub fn def_global(&mut self, constant: u64) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        self.globals.insert(
            self.constants
                .get(&constant)
                .unwrap()
                .as_symbol()
                .cloned()
                .unwrap(),
            val.into_object(),
        );
        self.stack.push(Value::Value(Object::Nil));
        Ok(())
    }

    pub fn set_global(&mut self, constant: u64) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        if let Some(var) = self
            .globals
            .get_mut(self.constants.get(&constant).unwrap().as_symbol().unwrap())
        {
            *var = val.clone().into_object();
            self.stack.push(val);
            Ok(())
        } else {
            Err(Error::NotFound(
                self.constants
                    .get(&constant)
                    .unwrap()
                    .as_symbol()
                    .cloned()
                    .unwrap(),
            ))
        }
    }

    pub fn get_global(&mut self, constant: u64) -> Result<(), Error> {
        if let Some(var) = self
            .globals
            .get(self.constants.get(&constant).unwrap().as_symbol().unwrap())
        {
            self.stack.push(Value::Value(var.clone()))
        } else {
            return Err(Error::NotFound(
                self.constants
                    .get(&constant)
                    .unwrap()
                    .as_symbol()
                    .cloned()
                    .unwrap(),
            ));
        }
        Ok(())
    }

    pub fn set_local(&mut self, local: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let i = self.bp + local;
        match &mut self.stack[i] {
            Value::Value(_) => self.stack[i] = val.clone(),
            Value::UpValue(inner) => {
                *inner.borrow_mut() = val.clone().into_object();
            }
        }
        self.stack.push(val);
        Ok(())
    }

    pub fn get_local(&mut self, local: usize) -> Result<(), Error> {
        let i = self.bp + local;
        let local = self.stack[i].clone();
        self.stack.push(local);
        Ok(())
    }

    pub fn set_upvalue(&mut self, upvalue: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        *self.current_function.as_mut().unwrap().upvalues[upvalue].borrow_mut() = val.into_object();

        Ok(())
    }

    pub fn get_upvalue(&mut self, upvalue: usize) -> Result<(), Error> {
        let val = self.current_function.as_ref().unwrap().upvalues[upvalue].clone();

        self.stack.push(Value::UpValue(val));

        Ok(())
    }

    pub fn create_upvalue(&mut self, upvalue: UpValue) -> Result<(), Error> {
        let val = match upvalue {
            UpValue::Local(i) => {
                let val = self.stack[self.bp + i].clone().into_object();
                let rc = Rc::new(RefCell::new(val));
                self.stack[self.bp + i] = Value::UpValue(rc.clone());
                rc
            }
            UpValue::UpValue(i) => self.current_function.as_ref().unwrap().upvalues[i].clone(),
        };

        let function = match self.stack.last_mut().unwrap() {
            Value::Value(Object::Function(function)) => function,
            value => {
                return Err(Error::Type {
                    expected: Type::Function,
                    recieved: Type::from(&value.clone().into_object()),
                })
            }
        };

        function.upvalues.push(val);

        Ok(())
    }

    pub fn call(&mut self, args: usize) -> Result<(), Error> {
        match self.stack[self.stack.len() - args - 1]
            .clone()
            .into_object()
        {
            Object::Function(function) => {
                match &function.arity {
                    Arity::Nullary if args != 0 => todo!(),
                    Arity::Nary(_) if args == 0 => todo!(),
                    _ => (),
                }

                self.frames.push(Frame {
                    function: self.current_function.clone(),
                    bp: self.bp,
                    pc: self.pc,
                });

                self.current_function = Some(function);
                self.bp = self.stack.len() - args;
                self.pc = 0;

                Ok(())
            }
            Object::NativeFunction(function) => {
                let len = self.stack.len();
                let parameters = &mut self.stack[len - args..];
                let ret = function.0(parameters);

                self.stack.truncate(self.stack.len() - args - 1);

                match ret {
                    Ok(val) => {
                        self.stack.push(Value::Value(val));
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            }
            object => Err(Error::Type {
                expected: Type::Function,
                recieved: Type::from(&object),
            }),
        }
    }

    fn tail(&mut self) -> Result<(), Error> {
        todo!()
    }

    pub fn ret(&mut self) -> Result<(), Error> {
        let ret = self.stack.pop().unwrap();
        self.stack.truncate(self.bp - 1);
        self.stack.push(ret);
        let frame = self.frames.pop().unwrap();
        self.pc = frame.pc;
        self.bp = frame.bp;
        self.current_function = frame.function;
        Ok(())
    }

    pub fn lambda(&mut self, arity: Arity, opcodes: u64) -> Result<(), Error> {
        let function = Lambda {
            arity,
            opcodes: self
                .constants
                .get(&opcodes)
                .unwrap()
                .as_opcodes()
                .cloned()
                .unwrap(),
            upvalues: Vec::new(),
        };

        let object = Object::Function(function);

        self.stack.push(Value::Value(object));

        Ok(())
    }

    fn binary_integer_op(&mut self, f: impl Fn(i64, i64) -> i64) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        let a = match lhs.into_object() {
            Object::Int(i) => i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(&object),
                })
            }
        };

        let b = match rhs.into_object() {
            Object::Int(i) => i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(&object),
                })
            }
        };

        let result = Object::Int(f(a, b));

        self.stack.push(Value::Value(result));

        Ok(())
    }

    pub fn add(&mut self) -> Result<(), Error> {
        self.binary_integer_op(|a, b| a + b)
    }

    pub fn sub(&mut self) -> Result<(), Error> {
        self.binary_integer_op(|a, b| a - b)
    }

    pub fn mul(&mut self) -> Result<(), Error> {
        self.binary_integer_op(|a, b| a * b)
    }

    pub fn div(&mut self) -> Result<(), Error> {
        self.binary_integer_op(|a, b| a / b)
    }

    pub fn car(&mut self) -> Result<(), Error> {
        let car = match self.stack.pop().unwrap().into_object() {
            Object::Cons(cons) => cons.0,
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recieved: Type::from(&object),
                })
            }
        };

        self.stack.push(Value::Value(car));

        Ok(())
    }

    pub fn cdr(&mut self) -> Result<(), Error> {
        let cdr = match self.stack.pop().unwrap().into_object() {
            Object::Cons(cons) => cons.1,
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recieved: Type::from(&object),
                })
            }
        };

        self.stack.push(Value::Value(cdr));

        Ok(())
    }

    pub fn cons(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        let cons = Object::Cons(Box::new(Cons(lhs.into_object(), rhs.into_object())));

        self.stack.push(Value::Value(cons));

        Ok(())
    }

    pub fn list(&mut self, args: usize) -> Result<(), Error> {
        let list = make_list(&self.stack[self.stack.len() - args..]);
        self.stack.truncate(self.stack.len() - args);
        self.stack.push(list);
        Ok(())
    }

    pub fn branch(&mut self, i: usize) -> Result<(), Error> {
        let p = self.stack.pop().unwrap();

        match p.into_object() {
            Object::True => (),
            Object::Nil => {
                self.pc += i;
            }
            object => {
                return Err(Error::Type {
                    expected: Type::Predicate,
                    recieved: Type::from(&object),
                });
            }
        }

        Ok(())
    }

    pub fn is_type(&mut self, ty: Type) -> Result<(), Error> {
        self.stack.push(
            if Type::from(&self.stack.last().unwrap().clone().into_object()) == ty {
                Value::Value(Object::True)
            } else {
                Value::Value(Object::Nil)
            },
        );
        Ok(())
    }

    pub fn assert(&mut self) -> Result<(), Error> {
        match self.stack.pop().unwrap().into_object() {
            Object::True => Ok(()),
            _ => Err(Error::Assert("assertion failed".to_string())),
        }
    }

    pub fn eq(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(if lhs.into_object() == rhs.into_object() {
            Value::Value(Object::True)
        } else {
            Value::Value(Object::Nil)
        });

        Ok(())
    }

    pub fn lt(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(
            match lhs
                .clone()
                .into_object()
                .partial_cmp(&rhs.clone().into_object())
            {
                Some(Ordering::Less) => Value::Value(Object::True),
                Some(_) => Value::Value(Object::Nil),
                None => {
                    return Err(Error::Cmp(
                        Type::from(&lhs.into_object()),
                        Type::from(&rhs.into_object()),
                    ))
                }
            },
        );

        Ok(())
    }

    pub fn gt(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(
            match lhs
                .clone()
                .into_object()
                .partial_cmp(&rhs.clone().into_object())
            {
                Some(Ordering::Greater) => Value::Value(Object::True),
                Some(_) => Value::Value(Object::Nil),
                None => {
                    return Err(Error::Cmp(
                        Type::from(&lhs.into_object()),
                        Type::from(&rhs.into_object()),
                    ))
                }
            },
        );

        Ok(())
    }
}

fn make_list(objects: &[Value]) -> Value {
    if !objects.is_empty() {
        Value::Value(Object::Cons(Box::new(Cons(
            objects[0].clone().into_object(),
            make_list(&objects[1..]).into_object(),
        ))))
    } else {
        Value::Value(Object::Nil)
    }
}

impl Value {
    pub fn into_object(self) -> Object {
        match self {
            Self::Value(object) => object,
            Self::UpValue(object) => object.borrow().clone(),
        }
    }

    pub fn with<T, F>(&self, f: F) -> T
    where
        F: Fn(&Object) -> T,
    {
        match self {
            Self::Value(object) => f(object),
            Self::UpValue(object) => {
                let borrow_guard = object.borrow();
                f(borrow_guard.deref())
            }
        }
    }

    pub fn with_mut<T, F>(&mut self, mut f: F) -> T
    where
        F: FnMut(&mut Object) -> T,
    {
        match self {
            Self::Value(object) => f(object),
            Self::UpValue(object) => {
                let mut borrow_guard = object.borrow_mut();
                f(borrow_guard.deref_mut())
            }
        }
    }
}
