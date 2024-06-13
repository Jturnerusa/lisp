#![allow(dead_code)]

pub mod object;

use crate::object::{Cons, Lambda, NativeFunction, Type};
use gc::Gc;
use identity_hasher::IdentityHasher;
use object::HashMapKey;
use std::cell::RefCell;
use std::cmp::{Ordering, PartialOrd};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use thiserror::Error;
use twox_hash::Xxh3Hash64;
use unwrap_enum::{EnumAs, EnumIs};

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
    #[error("cannot make hashmap key from type: {0}")]
    HashKey(Type),
    #[error("other error: {0}")]
    Other(#[from] Box<dyn std::error::Error>),
}

#[derive(Clone, Debug, EnumAs, EnumIs, PartialEq, Eq, Hash)]
pub enum Constant {
    String(Gc<String>),
    Symbol(Gc<String>),
    Opcodes(Gc<[OpCode]>),
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
    MapCreate,
    MapInsert,
    MapRetrieve,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UpValue {
    Local(usize),
    UpValue(usize),
}

#[derive(Clone, Debug)]
struct Frame {
    function: Option<Gc<RefCell<Lambda>>>,
    pc: usize,
    bp: usize,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Local {
    Value(Object),
    UpValue(Gc<RefCell<Object>>),
}

pub struct Vm {
    globals: HashMap<String, Object>,
    constants: HashMap<u64, Constant, IdentityHasher>,
    stack: Vec<Local>,
    frames: Vec<Frame>,
    current_function: Option<Gc<RefCell<Lambda>>>,
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
            let mut hasher = Xxh3Hash64::with_seed(0);
            constant.hash(&mut hasher);
            let hash = hasher.finish();
            self.constants.insert(hash, constant);
        }
    }

    pub fn load_native_function<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&mut [Local]) -> Result<Object, Error> + 'static,
    {
        let native_function = NativeFunction::new(f);
        self.globals
            .insert(name.to_string(), Object::NativeFunction(native_function));
    }

    pub fn eval(&mut self, opcodes: &[OpCode]) -> Result<Option<Local>, Error> {
        loop {
            let opcode = if let Some(function) = &self.current_function {
                function.borrow().opcodes[self.pc]
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
                        .push(Local::Value(Object::Symbol(symbol_value.clone())));
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
                        .push(Local::Value(Object::String(string_value.clone())));
                }
                OpCode::PushInt(i) => self.stack.push(Local::Value(Object::Int(i))),
                OpCode::PushChar(c) => self.stack.push(Local::Value(Object::Char(c))),
                OpCode::PushTrue => self.stack.push(Local::Value(Object::True)),
                OpCode::PushNil => self.stack.push(Local::Value(Object::Nil)),
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
                OpCode::MapCreate => self.map_create()?,
                OpCode::MapInsert => self.map_insert()?,
                OpCode::MapRetrieve => self.map_retrieve()?,
                _ => todo!(),
            }
        }
    }

    pub fn peek(&self, i: usize) -> Option<&Local> {
        self.stack.get(self.stack.len() - i - 1)
    }

    pub fn push(&mut self, object: Object) {
        self.stack.push(Local::Value(object));
    }

    pub fn pop(&mut self) -> Option<Local> {
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
                .unwrap()
                .deref()
                .clone(),
            val.into_object(),
        );
        self.stack.push(Local::Value(Object::Nil));
        Ok(())
    }

    pub fn set_global(&mut self, constant: u64) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        if let Some(var) = self.globals.get_mut(
            self.constants
                .get(&constant)
                .unwrap()
                .as_symbol()
                .unwrap()
                .deref(),
        ) {
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
                    .unwrap()
                    .deref()
                    .clone(),
            ))
        }
    }

    pub fn get_global(&mut self, constant: u64) -> Result<(), Error> {
        if let Some(var) = self.globals.get(
            self.constants
                .get(&constant)
                .unwrap()
                .as_symbol()
                .unwrap()
                .deref(),
        ) {
            self.stack.push(Local::Value(var.clone()))
        } else {
            return Err(Error::NotFound(
                self.constants
                    .get(&constant)
                    .unwrap()
                    .as_symbol()
                    .cloned()
                    .unwrap()
                    .deref()
                    .clone(),
            ));
        }
        Ok(())
    }

    pub fn set_local(&mut self, local: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let i = self.bp + local;
        match &mut self.stack[i] {
            Local::Value(_) => self.stack[i] = val.clone(),
            Local::UpValue(inner) => {
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

        *self
            .current_function
            .as_mut()
            .unwrap()
            .borrow_mut()
            .upvalues[upvalue]
            .borrow_mut() = val.into_object();

        Ok(())
    }

    pub fn get_upvalue(&mut self, upvalue: usize) -> Result<(), Error> {
        let val = self
            .current_function
            .as_ref()
            .unwrap()
            .borrow_mut()
            .upvalues[upvalue]
            .clone();

        self.stack.push(Local::UpValue(val));

        Ok(())
    }

    pub fn create_upvalue(&mut self, upvalue: UpValue) -> Result<(), Error> {
        let val = match upvalue {
            UpValue::Local(i) => {
                let val = self.stack[self.bp + i].clone().into_object();
                let gc = Gc::new(RefCell::new(val));
                self.stack[self.bp + i] = Local::UpValue(gc.clone());
                gc
            }
            UpValue::UpValue(i) => {
                self.current_function.as_ref().unwrap().borrow().upvalues[i].clone()
            }
        };

        let function = match self.stack.last_mut().unwrap() {
            Local::Value(Object::Function(function)) => function,
            value => {
                return Err(Error::Type {
                    expected: Type::Function,
                    recieved: Type::from(&value.clone().into_object()),
                })
            }
        };

        function.borrow_mut().upvalues.push(val);

        Ok(())
    }

    pub fn call(&mut self, args: usize) -> Result<(), Error> {
        match self.stack[self.stack.len() - args - 1]
            .clone()
            .into_object()
        {
            Object::Function(function) => {
                match &function.borrow().arity {
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
                        self.stack.push(Local::Value(val));
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

        let object = Object::Function(Gc::new(RefCell::new(function)));

        self.stack.push(Local::Value(object));

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

        self.stack.push(Local::Value(result));

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
            Object::Cons(cons) => cons.borrow().0.clone(),
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recieved: Type::from(&object),
                })
            }
        };

        self.stack.push(Local::Value(car));

        Ok(())
    }

    pub fn cdr(&mut self) -> Result<(), Error> {
        let cdr = match self.stack.pop().unwrap().into_object() {
            Object::Cons(cons) => cons.borrow().1.clone(),
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recieved: Type::from(&object),
                })
            }
        };

        self.stack.push(Local::Value(cdr));

        Ok(())
    }

    pub fn cons(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        let cons = Object::Cons(Gc::new(RefCell::new(Cons(
            lhs.into_object(),
            rhs.into_object(),
        ))));

        self.stack.push(Local::Value(cons));

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
                Local::Value(Object::True)
            } else {
                Local::Value(Object::Nil)
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
            Local::Value(Object::True)
        } else {
            Local::Value(Object::Nil)
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
                Some(Ordering::Less) => Local::Value(Object::True),
                Some(_) => Local::Value(Object::Nil),
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
                Some(Ordering::Greater) => Local::Value(Object::True),
                Some(_) => Local::Value(Object::Nil),
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

    pub fn map_create(&mut self) -> Result<(), Error> {
        let map = Object::HashMap(Gc::new(RefCell::new(HashMap::new())));
        self.stack.push(Local::Value(map));
        Ok(())
    }

    pub fn map_insert(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();
        let mut map = self.stack.pop().unwrap();

        let key = match lhs.with(|object| HashMapKey::try_from(object)) {
            Ok(key) => key,
            Err(_) => return Err(Error::HashKey(rhs.with(|object| Type::from(object)))),
        };

        map.with_mut(|object| match object {
            Object::HashMap(hm) => {
                hm.borrow_mut().insert(key, rhs.into_object());
                Ok(())
            }
            object => Err(Error::Type {
                expected: Type::Map,
                recieved: Type::from(&*object),
            }),
        })?;

        Ok(())
    }

    fn map_retrieve(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let map = self.stack.pop().unwrap();

        let key = match val.with(|object| HashMapKey::try_from(object)) {
            Ok(key) => key,
            Err(_) => return Err(Error::HashKey(val.with(|object| Type::from(object)))),
        };

        let ret = map.with(|object| match object {
            Object::HashMap(hm) => Ok(hm.borrow().get(&key).cloned()),
            object => Err(Error::Type {
                expected: Type::Map,
                recieved: Type::from(object),
            }),
        })?;

        self.stack.push(Local::Value(match ret {
            Some(obj) => obj,
            None => Object::Nil,
        }));

        Ok(())
    }
}

fn make_list(objects: &[Local]) -> Local {
    if !objects.is_empty() {
        Local::Value(Object::Cons(Gc::new(RefCell::new(Cons(
            objects[0].clone().into_object(),
            make_list(&objects[1..]).into_object(),
        )))))
    } else {
        Local::Value(Object::Nil)
    }
}

impl Local {
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

    pub fn with_mut<T, F>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Object) -> T,
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
