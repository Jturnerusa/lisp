#![allow(dead_code)]

use core::fmt;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::ops::{DerefMut, Range};
use std::rc::Rc;
use std::{cell::RefCell, ops::Deref};

use thiserror::Error;

use xxhash::Xxh3;

use identity_hasher::IdentityHasher;

use unwrap_enum::{EnumAs, EnumIs};

use value::Value;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arity {
    Nullary,
    Nary(usize),
    Variadic,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Function,
    Vec,
    String,
    Symbol,
    Int,
    True,
    Nil,
    Predicate,
}

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("type error: expected {expected}: received: {recieved}")]
    Type { expected: Type, recieved: Type },
    #[error("variable not found: {0}")]
    NotFound(String),
    #[error("invalid parameters: {0}")]
    Parameters(String),
}

#[derive(Clone, EnumAs, EnumIs, PartialEq, Eq, Hash)]
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
    PushString(u64),
    PushTrue,
    PushNil,
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Vec(usize),
    VecNth,
    VecPush,
    VecPop,
    VecInsert,
    VecSlice,
    Jmp(isize),
    Branch(usize),
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Object {
    Function(Rc<RefCell<Lambda>>),
    Vec(Vec<Rc<RefCell<Object>>>),
    String(String),
    Symbol(String),
    Int(i64),
    True,
    Nil,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UpValue {
    pub frame: usize,
    pub index: usize,
}

#[derive(Clone, Debug)]
pub struct Lambda {
    arity: Arity,
    opcodes: Rc<[OpCode]>,
    upvalues: Vec<Rc<RefCell<Object>>>,
}

struct Frame {
    function: Option<Rc<RefCell<Lambda>>>,
    pc: usize,
    bp: usize,
}

pub struct Vm {
    globals: HashMap<String, Rc<RefCell<Object>>>,
    constants: HashMap<u64, Constant, IdentityHasher>,
    stack: Vec<Rc<RefCell<Object>>>,
    frames: Vec<Frame>,
    current_function: Option<Rc<RefCell<Lambda>>>,
    pc: usize,
    bp: usize,
}

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

    pub fn load_constant(&mut self, constant: Constant) {
        let mut hasher = Xxh3::new(0).unwrap();
        constant.hash(&mut hasher);
        let hash = hasher.finish();
        self.constants.insert(hash, constant);
    }

    pub fn eval(&mut self, opcodes: &[OpCode]) -> Result<Option<Rc<RefCell<Object>>>, Error> {
        loop {
            let opcode = if let Some(function) = &self.current_function {
                function.borrow().opcodes[self.pc]
            } else if self.pc < opcodes.len() {
                opcodes[self.pc]
            } else {
                let ret = self.stack.pop();
                self.stack.clear();
                self.pc = 0;
                return Ok(ret);
            };

            match opcode {
                OpCode::DefGlobal(global) => self.def_global(global)?,
                OpCode::SetGlobal(global) => self.set_global(global)?,
                OpCode::GetGlobal(global) => self.get_global(global)?,
                OpCode::SetLocal(local) => self.set_local(local)?,
                OpCode::GetLocal(local) => self.get_local(local)?,
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
                        .push(Rc::new(RefCell::new(Object::Symbol(symbol_value))));
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
                        .push(Rc::new(RefCell::new(Object::String(string_value))));
                }
                OpCode::PushInt(i) => self.stack.push(Rc::new(RefCell::new(Object::Int(i)))),
                OpCode::Pop => {
                    self.stack.pop().unwrap();
                }
                OpCode::Add => self.add()?,
                OpCode::Sub => self.sub()?,
                OpCode::Mul => self.mul()?,
                OpCode::Div => self.div()?,
                OpCode::Vec(args) => self.make_vec(args)?,
                OpCode::VecPush => self.vec_push()?,
                OpCode::VecPop => self.vec_pop()?,
                OpCode::VecNth => self.vec_nth()?,
                OpCode::VecInsert => self.vec_insert()?,
                OpCode::VecSlice => self.vec_insert()?,
                OpCode::Branch(offset) => self.branch(offset)?,
                OpCode::Jmp(offset) => {
                    self.pc += offset as usize;
                }
                _ => todo!(),
            }
        }
    }

    pub fn push(&mut self, object: Rc<RefCell<Object>>) {
        self.stack.push(object);
    }

    pub fn pop(&mut self) -> Option<Rc<RefCell<Object>>> {
        self.stack.pop()
    }

    pub fn stack(&self) -> &[Rc<RefCell<Object>>] {
        self.stack.as_slice()
    }

    pub fn def_global(&mut self, constant: u64) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        self.globals.insert(
            self.constants
                .get(&constant)
                .unwrap()
                .as_string()
                .cloned()
                .unwrap(),
            val,
        );
        self.stack.push(Rc::new(RefCell::new(Object::Nil)));
        Ok(())
    }

    pub fn set_global(&mut self, constant: u64) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        if let Some(var) = self
            .globals
            .get_mut(self.constants.get(&constant).unwrap().as_string().unwrap())
        {
            *var = Rc::clone(&val);
            self.stack.push(val);
            Ok(())
        } else {
            Err(Error::NotFound(
                self.constants
                    .get(&constant)
                    .unwrap()
                    .as_string()
                    .cloned()
                    .unwrap(),
            ))
        }
    }

    pub fn get_global(&mut self, constant: u64) -> Result<(), Error> {
        if let Some(var) = self
            .globals
            .get(self.constants.get(&constant).unwrap().as_string().unwrap())
        {
            self.stack.push(Rc::clone(var))
        } else {
            return Err(Error::NotFound(
                self.constants
                    .get(&constant)
                    .unwrap()
                    .as_string()
                    .cloned()
                    .unwrap(),
            ));
        }
        Ok(())
    }

    pub fn set_local(&mut self, local: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let i = self.bp + local;
        *self.stack[i].borrow_mut() = (*val).clone().into_inner();
        self.stack.push(val);
        Ok(())
    }

    pub fn get_local(&mut self, local: usize) -> Result<(), Error> {
        let i = self.bp + local;
        let local = self.stack[i].clone();
        self.stack.push(local);
        Ok(())
    }

    pub fn create_upvalue(&mut self, upvalue: UpValue) -> Result<(), Error> {
        let upvalue_index = self.frames[upvalue.frame].bp + upvalue.index;

        let val = self.stack[upvalue_index].clone();

        if let Object::Function(function) = self.stack.last().unwrap().borrow().deref() {
            function.borrow_mut().upvalues.push(val);
        } else {
            panic!();
        }

        Ok(())
    }

    pub fn call(&mut self, args: usize) -> Result<(), Error> {
        let f = match self.stack[self.stack.len() - args - 1].borrow().deref() {
            Object::Function(function) => Rc::clone(function),
            _ => todo!(),
        };

        match &f.borrow().arity {
            Arity::Nullary if args != 0 => todo!(),
            Arity::Nary(_) if args == 0 => todo!(),
            _ => (),
        }

        self.frames.push(Frame {
            function: self.current_function.clone(),
            bp: self.bp,
            pc: self.pc,
        });

        self.current_function = Some(f);
        self.bp = self.stack.len() - args;
        self.pc = 0;

        Ok(())
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
        let function = Rc::new(RefCell::new(Lambda {
            arity,
            opcodes: self
                .constants
                .get(&opcodes)
                .unwrap()
                .as_opcodes()
                .cloned()
                .unwrap(),
            upvalues: Vec::new(),
        }));

        let object = Rc::new(RefCell::new(Object::Function(function)));

        self.stack.push(object);

        Ok(())
    }

    fn binary_integer_op(&mut self, f: impl Fn(i64, i64) -> i64) -> Result<(), Error> {
        let a = self.stack.pop().unwrap();
        let b = self.stack.pop().unwrap();

        let Object::Int(a) = *(*a).borrow() else {
            return Err(Error::Type {
                expected: Type::Int,
                recieved: Type::from(&*(*a).borrow()),
            });
        };

        let Object::Int(b) = *(*b).borrow() else {
            return Err(Error::Type {
                expected: Type::Int,
                recieved: Type::from(&*(*b).borrow()),
            });
        };

        let result = Rc::new(RefCell::new(Object::Int(f(a, b))));

        self.stack.push(result);

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

    pub fn make_vec(&mut self, args: usize) -> Result<(), Error> {
        let vec = self.stack[self.stack.len() - args..].to_vec();
        self.stack.truncate(self.stack.len() - args);
        self.stack.push(Rc::new(RefCell::new(Object::Vec(vec))));
        Ok(())
    }

    pub fn vec_pop(&mut self) -> Result<(), Error> {
        let val = match self.stack.last_mut().unwrap().borrow_mut().deref_mut() {
            Object::Vec(vec) => vec.pop().unwrap(),
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&*object),
                })
            }
        };

        self.stack.push(val);

        Ok(())
    }

    pub fn vec_push(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        match self.stack.last_mut().unwrap().borrow_mut().deref_mut() {
            Object::Vec(vec) => vec.push(val),
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&*object),
                })
            }
        }

        Ok(())
    }

    pub fn vec_nth(&mut self) -> Result<(), Error> {
        let index: usize = match self.stack.pop().unwrap().borrow().deref() {
            Object::Int(i) => *i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(object),
                })
            }
        }
        .try_into()
        .unwrap();

        let element = match self.stack.last().unwrap().deref().borrow().deref() {
            Object::Vec(vec) => Rc::clone(&vec[index]),
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(object),
                })
            }
        };

        self.stack.push(element);

        Ok(())
    }

    pub fn vec_insert(&mut self) -> Result<(), Error> {
        let index = match self.stack.pop().unwrap().borrow().deref() {
            Object::Int(i) => *i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(object),
                })
            }
        }
        .try_into()
        .unwrap();

        let val = self.stack.pop().unwrap();

        match self.stack.last_mut().unwrap().borrow_mut().deref_mut() {
            Object::Vec(vec) => vec.insert(index, val),
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&*object),
                })
            }
        }

        Ok(())
    }

    pub fn vec_slice(&mut self) -> Result<(), Error> {
        let start: usize = match self.stack.pop().unwrap().deref().borrow().deref() {
            Object::Int(i) => *i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(object),
                })
            }
        }
        .try_into()
        .unwrap();

        let stop: usize = match self.stack.pop().unwrap().deref().borrow().deref() {
            Object::Int(i) => *i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(object),
                })
            }
        }
        .try_into()
        .unwrap();

        let slice = match self.stack.last().unwrap().deref().borrow().deref() {
            Object::Vec(vec) => Rc::new(RefCell::new(Object::Vec(vec[start..stop].to_vec()))),
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(object),
                })
            }
        };

        self.stack.push(slice);

        Ok(())
    }

    pub fn branch(&mut self, i: usize) -> Result<(), Error> {
        let p = self.stack.pop().unwrap();

        match p.deref().borrow().deref() {
            Object::True => (),
            Object::Nil => {
                self.pc += i;
            }
            object => {
                return Err(Error::Type {
                    expected: Type::Predicate,
                    recieved: Type::from(object),
                });
            }
        }

        Ok(())
    }
}

impl From<&Object> for Type {
    fn from(value: &Object) -> Self {
        match value {
            Object::Function(_) => Type::Function,
            Object::Vec(_) => Type::Vec,
            Object::String(_) => Type::String,
            Object::Symbol(_) => Type::Symbol,
            Object::Int(_) => Type::Int,
            Object::True => Type::True,
            Object::Nil => Type::Nil,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Function => write!(f, "function"),
            Self::Vec => write!(f, "vec"),
            Self::Symbol => write!(f, "symbol"),
            Self::String => write!(f, "string"),
            Self::Int => write!(f, "int"),
            Self::True => write!(f, "true"),
            Self::Nil => write!(f, "nil"),
            Self::Predicate => write!(f, "predicate"),
        }
    }
}

impl TryFrom<&Object> for Value {
    type Error = ();
    fn try_from(object: &Object) -> Result<Self, Self::Error> {
        Ok(match object {
            Object::Function(_) => return Err(()),
            Object::Vec(vec) => Value::List(
                vec.iter()
                    .cloned()
                    .map(|object| Value::try_from(object.borrow().deref()))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|_| ())?,
            ),
            Object::String(string) => Value::String(string.clone()),
            Object::Symbol(symbol) => Value::Symbol(symbol.clone()),
            Object::Int(i) => Value::Int(*i),
            Object::True => Value::True,
            Object::Nil => Value::Nil,
        })
    }
}
