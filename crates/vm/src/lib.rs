#![allow(dead_code)]

pub mod object;

use crate::object::{Cons, Lambda, NativeFunction, Type};
use core::fmt;
use error::FileSpan;
use identity_hasher::{IdentityHasher, IdentityMap};
use object::{HashMapKey, Struct};
use std::cell::RefCell;
use std::cmp::{Ordering, PartialOrd};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;
use thiserror::Error;
use unwrap_enum::{EnumAs, EnumIs};

pub use crate::object::Object;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Hash)]
pub enum Arity {
    Nullary,
    Nary(usize),
    Variadic(usize),
}

#[derive(Debug)]
pub struct ErrorWithDebug<D> {
    pub error: Error,
    pub debug: D,
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
    #[error("cannot do arithmetic on this combination of types: {0} {1}")]
    Arithmetic(Type, Type),
    #[error("cannot make hashmap key from type: {0}")]
    HashKey(Type),
    #[error("expected a list for apply")]
    Apply,
    #[error("expected box")]
    Box,
    #[error("other error: {0}")]
    Other(#[from] Box<dyn std::error::Error>),
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, EnumAs, EnumIs)]
pub enum OpCode {
    DefGlobal(u64),
    SetGlobal(u64),
    GetGlobal(u64),
    SetLocal(usize),
    GetLocal(usize),
    SetUpValue(usize),
    GetUpValue(usize),
    SetBox,
    Box,
    UnBox,
    Call(usize),
    Tail(usize),
    Apply,
    Return,
    Lambda(Arity, u64),
    CreateUpValue(UpValue),
    PushSymbol(u64),
    PushInt(i64),
    PushFloat(f64),
    PushChar(char),
    PushString(u64),
    PushBool(bool),
    PushNil,
    Pop,
    Dup,
    Peek(usize),
    Swap,
    Add,
    Sub,
    Mul,
    Div,
    Car,
    Cdr,
    Cons,
    SetCar,
    SetCdr,
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
    MapItems,
    MakeStruct(usize),
    GetField(usize),
    SetField(usize),
    VecCreate,
    VecPush,
    VecPop,
    VecRef,
    VecSet,
    VecLen,
}

#[derive(Clone, PartialEq, PartialOrd, Hash)]
pub struct OpCodeTable<D> {
    opcodes: Vec<OpCode>,
    debug: Vec<D>,
}

#[derive(Clone, PartialEq, Hash, EnumAs, EnumIs)]
pub enum Constant<D> {
    OpCodeTable(Rc<OpCodeTable<D>>),
    Symbol(Rc<String>),
    String(Rc<String>),
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum UpValue {
    Local(usize),
    UpValue(usize),
}

#[derive(Clone, Debug)]
struct Frame<D: 'static> {
    function: Option<Rc<RefCell<Lambda<D>>>>,
    pc: usize,
    bp: usize,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Local<D: 'static> {
    Value(Object<D>),
    UpValue(Rc<RefCell<Object<D>>>),
}

pub struct Vm<D: 'static> {
    globals: HashMap<Rc<String>, Object<D>>,
    constants: IdentityMap<u64, Constant<D>>,
    stack: Vec<Local<D>>,
    frames: Vec<Frame<D>>,
    current_function: Option<Rc<RefCell<Lambda<D>>>>,
    pc: usize,
    bp: usize,
}

#[allow(clippy::new_without_default)]
impl<D: Clone + PartialEq + PartialOrd + Hash + Debug> Vm<D> {
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

    pub fn load_constant(&mut self, constant: Constant<D>) {
        let mut hasher = std::hash::DefaultHasher::new();
        constant.hash(&mut hasher);
        let hash = hasher.finish();
        self.constants.insert(hash, constant);
    }

    pub fn load_native_function<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&mut [Local<D>]) -> Result<Object<D>, Error> + 'static,
    {
        let native_function = NativeFunction::new(f);
        self.globals.insert(
            Rc::new(name.to_string()),
            Object::NativeFunction(native_function),
        );
    }

    pub fn eval(&mut self, opcode_table: &OpCodeTable<D>) -> Result<(), ErrorWithDebug<D>> {
        loop {
            let opcode = if let Some(function) = &self.current_function {
                function.borrow().opcodes.opcodes[self.pc]
            } else if self.pc < opcode_table.opcodes.len() {
                opcode_table.opcodes[self.pc]
            } else {
                self.pc = 0;
                return Ok(());
            };

            self.pc += 1;

            match self.dispatch(opcode) {
                Ok(_) => continue,
                Err(error) => {
                    let debug = if let Some(function) = &self.current_function {
                        function.borrow().opcodes.debug[self.pc - 1].clone()
                    } else {
                        opcode_table.debug[self.pc - 1].clone()
                    };
                    return Err(ErrorWithDebug { error, debug });
                }
            }
        }
    }

    fn dispatch(&mut self, opcode: OpCode) -> Result<(), Error> {
        match opcode {
            OpCode::DefGlobal(global) => self.def_global(global)?,
            OpCode::SetGlobal(global) => self.set_global(global)?,
            OpCode::GetGlobal(global) => self.get_global(global)?,
            OpCode::SetLocal(local) => self.set_local(local)?,
            OpCode::GetLocal(local) => self.get_local(local)?,
            OpCode::SetUpValue(upvalue) => self.set_upvalue(upvalue)?,
            OpCode::GetUpValue(upvalue) => self.get_upvalue(upvalue)?,
            OpCode::Box => self.r#box()?,
            OpCode::UnBox => self.unbox()?,
            OpCode::SetBox => self.set_box()?,
            OpCode::Call(args) => self.call(args)?,
            OpCode::Tail(args) => self.tail(args)?,
            OpCode::Return => self.ret()?,
            OpCode::Apply => self.apply()?,
            OpCode::Lambda(arity, opcode_table) => self.lambda(arity, opcode_table)?,
            OpCode::CreateUpValue(upvalue) => self.create_upvalue(upvalue)?,
            OpCode::PushSymbol(symbol) => {
                self.stack.push(Local::Value(Object::Symbol(
                    self.constants[&symbol].as_symbol().unwrap().clone(),
                )));
            }
            OpCode::PushString(string) => {
                self.stack.push(Local::Value(Object::String(
                    self.constants[&string].as_string().unwrap().clone(),
                )));
            }
            OpCode::PushInt(i) => self.stack.push(Local::Value(Object::Int(i))),
            OpCode::PushFloat(f) => self.stack.push(Local::Value(Object::Float(f))),
            OpCode::PushChar(c) => self.stack.push(Local::Value(Object::Char(c))),
            OpCode::PushBool(b) => self.stack.push(Local::Value(Object::Bool(b))),
            OpCode::PushNil => self.stack.push(Local::Value(Object::Nil)),
            OpCode::Pop => {
                self.stack.pop().unwrap();
            }
            OpCode::Dup => self.dup()?,
            OpCode::Peek(i) => self.peek(i)?,
            OpCode::Swap => self.swap()?,
            OpCode::Add => self.add()?,
            OpCode::Sub => self.sub()?,
            OpCode::Mul => self.mul()?,
            OpCode::Div => self.div()?,
            OpCode::Cons => self.cons()?,
            OpCode::Car => self.car()?,
            OpCode::Cdr => self.cdr()?,
            OpCode::SetCar => self.set_car()?,
            OpCode::SetCdr => self.set_cdr()?,
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
            OpCode::MapItems => self.map_items()?,
            OpCode::MakeStruct(args) => self.make_struct(args)?,
            OpCode::SetField(field) => self.set_field(field)?,
            OpCode::GetField(field) => self.get_field(field)?,
            OpCode::VecCreate => self.vec_create()?,
            OpCode::VecPop => self.vec_pop()?,
            OpCode::VecPush => self.vec_push()?,
            OpCode::VecRef => self.vec_ref()?,
            OpCode::VecSet => self.vec_set()?,
            OpCode::VecLen => self.vec_len()?,
        }

        Ok(())
    }

    pub fn peek(&mut self, i: usize) -> Result<(), Error> {
        let val = self.stack.get(self.stack.len() - i - 1).unwrap().clone();

        self.stack.push(val);

        Ok(())
    }

    pub fn swap(&mut self) -> Result<(), Error> {
        let a = self.stack.pop().unwrap();
        let b = self.stack.pop().unwrap();

        self.stack.push(a);
        self.stack.push(b);

        Ok(())
    }

    pub fn push(&mut self, object: Object<D>) {
        self.stack.push(Local::Value(object));
    }

    pub fn pop(&mut self) -> Option<Local<D>> {
        self.stack.pop()
    }

    pub fn dup(&mut self) -> Result<(), Error> {
        let val = self.stack.last().unwrap().clone();

        self.stack.push(val);

        Ok(())
    }

    pub fn def_global(&mut self, global: u64) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        self.globals.insert(
            self.constants[&global].as_symbol().unwrap().clone(),
            val.into_object(),
        );
        self.stack.push(Local::Value(Object::Nil));
        Ok(())
    }

    pub fn set_global(&mut self, global: u64) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        if let Some(var) = self
            .globals
            .get_mut(self.constants[&global].as_symbol().unwrap())
        {
            *var = val.clone().into_object();
            self.stack.push(val);
            Ok(())
        } else {
            Err(Error::NotFound(global.to_string()))
        }
    }

    pub fn get_global(&mut self, global: u64) -> Result<(), Error> {
        if let Some(var) = self
            .globals
            .get(self.constants[&global].as_symbol().unwrap())
        {
            self.stack.push(Local::Value(var.clone()))
        } else {
            return Err(Error::NotFound(global.to_string()));
        }
        Ok(())
    }

    pub fn set_local(&mut self, local: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let i = self.bp + local;
        match &mut self.stack[i] {
            Local::Value(Object::Box(object)) => *object.borrow_mut() = val.clone().into_object(),
            Local::Value(inner) => {
                *inner = val.clone().into_object();
            }
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
                let val = self.stack[self.bp + i].clone();
                let gc = match val {
                    Local::Value(inner) => Rc::new(RefCell::new(inner)),
                    Local::UpValue(inner) => inner,
                };
                self.stack[self.bp + i] = Local::UpValue(gc.clone());
                gc
            }
            UpValue::UpValue(i) => {
                self.current_function.as_ref().unwrap().borrow().upvalues[i].clone()
            }
        };

        self.stack
            .last_mut()
            .unwrap()
            .with_mut(|object| match object {
                Object::Function(function) => {
                    function.borrow_mut().upvalues.push(val);
                    Ok(())
                }
                object => Err(Error::Type {
                    expected: Type::Function,
                    recieved: Type::from(&*object),
                }),
            })?;

        Ok(())
    }

    pub fn unbox(&mut self) -> Result<(), Error> {
        let r#box = self.stack.pop().unwrap().into_object();
        let val = match r#box {
            Object::Box(inner) => inner.borrow().clone(),
            _ => return Err(Error::Box),
        };

        self.stack.push(Local::Value(val));

        Ok(())
    }

    pub fn set_box(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let r#box = self.stack.pop().unwrap().into_object();

        match r#box {
            Object::Box(inner) => *inner.borrow_mut() = val.clone().into_object(),
            _ => return Err(Error::Box),
        };

        self.stack.push(val);

        Ok(())
    }

    pub fn r#box(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap().into_object();
        self.stack
            .push(Local::Value(Object::Box(Rc::new(RefCell::new(val)))));
        Ok(())
    }

    pub fn call(&mut self, args: usize) -> Result<(), Error> {
        self.stack[self.stack.len() - args - 1]
            .clone()
            .with(|object| match object {
                Object::Function(function) => {
                    self.check_arity(args, function.clone())?;

                    self.frames.push(Frame {
                        function: self.current_function.clone(),
                        bp: self.bp,
                        pc: self.pc,
                    });

                    self.current_function = Some(function.clone());
                    self.pc = 0;
                    self.bp = if let Arity::Variadic(n) = function.borrow().arity() {
                        let rest = if args > n { args - n } else { 0 };
                        self.list(rest)?;
                        self.stack.len() - (n + 1)
                    } else {
                        self.stack.len() - args
                    };

                    Ok(())
                }
                Object::NativeFunction(function) => self.native_call(args, function.clone()),
                object => Err(Error::Type {
                    expected: Type::Function,
                    recieved: Type::from(object),
                }),
            })
    }

    fn tail(&mut self, args: usize) -> Result<(), Error> {
        match self.stack[self.stack.len() - args - 1]
            .clone()
            .into_object()
        {
            Object::Function(function) => {
                self.check_arity(args, function.clone())?;

                self.stack.drain(self.bp..self.stack.len() - args);

                self.current_function = Some(function.clone());

                self.pc = 0;

                if let Arity::Variadic(n) = function.borrow().arity {
                    self.list(args - n)?;
                }

                Ok(())
            }
            Object::NativeFunction(native_function) => self.native_call(args, native_function),
            object => Err(Error::Type {
                expected: Type::Function,
                recieved: Type::from(&object),
            }),
        }
    }

    fn check_arity(&mut self, args: usize, function: Rc<RefCell<Lambda<D>>>) -> Result<(), Error> {
        match function.borrow().arity {
            Arity::Nullary if args != 0 => Err(Error::Parameters(format!(
                "expected 0 parameters, received {args}"
            ))),
            Arity::Nary(n) if args != n => Err(Error::Parameters(format!(
                "expected {n} parameters, received {args}"
            ))),
            Arity::Variadic(n) if args < n => Err(Error::Parameters(format!(
                "expected at least {n} parameters, received {args}"
            ))),
            _ => Ok(()),
        }
    }

    fn native_call(&mut self, args: usize, function: NativeFunction<D>) -> Result<(), Error> {
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

    pub fn apply(&mut self) -> Result<(), Error> {
        let args = match self.stack.pop().unwrap().into_object() {
            Object::Cons(cons) => {
                for arg in cons.borrow().iter_cars() {
                    self.stack.push(Local::Value(arg.clone()));
                }
                cons.borrow().iter_cars().count()
            }
            Object::Nil => {
                self.stack.push(Local::Value(Object::Nil));
                1
            }
            _ => return Err(Error::Apply),
        };

        self.call(args)?;

        Ok(())
    }

    pub fn lambda(&mut self, arity: Arity, opcodes: u64) -> Result<(), Error> {
        let opcodes = self.constants[&opcodes].as_opcodetable().unwrap().clone();

        let function = Lambda {
            arity,
            opcodes,
            upvalues: Vec::new(),
        };

        let object = Object::Function(Rc::new(RefCell::new(function)));

        self.stack.push(Local::Value(object));

        Ok(())
    }

    pub fn add(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        match (lhs.into_object(), rhs.into_object()) {
            (Object::Int(a), Object::Int(b)) => {
                self.stack.push(Local::Value(Object::Int(a + b)));
                Ok(())
            }
            (Object::Float(a), Object::Float(b)) => {
                self.stack.push(Local::Value(Object::Float(a + b)));
                Ok(())
            }
            (a, b) => Err(Error::Arithmetic(Type::from(&a), Type::from(&b))),
        }
    }

    pub fn sub(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        match (lhs.into_object(), rhs.into_object()) {
            (Object::Int(a), Object::Int(b)) => {
                self.stack.push(Local::Value(Object::Int(a - b)));
                Ok(())
            }
            (Object::Float(a), Object::Float(b)) => {
                self.stack.push(Local::Value(Object::Float(a - b)));
                Ok(())
            }
            (a, b) => Err(Error::Arithmetic(Type::from(&a), Type::from(&b))),
        }
    }

    pub fn mul(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        match (lhs.into_object(), rhs.into_object()) {
            (Object::Int(a), Object::Int(b)) => {
                self.stack.push(Local::Value(Object::Int(a * b)));
                Ok(())
            }
            (Object::Float(a), Object::Float(b)) => {
                self.stack.push(Local::Value(Object::Float(a * b)));
                Ok(())
            }
            (a, b) => Err(Error::Arithmetic(Type::from(&a), Type::from(&b))),
        }
    }

    pub fn div(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        match (lhs.into_object(), rhs.into_object()) {
            (Object::Int(a), Object::Int(b)) => {
                self.stack.push(Local::Value(Object::Int(a / b)));
                Ok(())
            }
            (Object::Float(a), Object::Float(b)) => {
                self.stack.push(Local::Value(Object::Float(a / b)));
                Ok(())
            }
            (a, b) => Err(Error::Arithmetic(Type::from(&a), Type::from(&b))),
        }
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

        let cons = Object::Cons(Rc::new(RefCell::new(Cons(
            lhs.into_object(),
            rhs.into_object(),
        ))));

        self.stack.push(Local::Value(cons));

        Ok(())
    }

    pub fn set_car(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let mut cons = self.stack.pop().unwrap();

        cons.with_mut(|object| match object {
            Object::Cons(cons) => {
                cons.borrow_mut().0 = val.into_object();
                Ok(())
            }
            object => Err(Error::Type {
                expected: Type::Cons,
                recieved: Type::from(&*object),
            }),
        })?;

        self.stack.push(cons);

        Ok(())
    }

    pub fn set_cdr(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let mut cons = self.stack.pop().unwrap();

        cons.with_mut(|object| match object {
            Object::Cons(cons) => {
                cons.borrow_mut().1 = val.into_object();
                Ok(())
            }
            object => Err(Error::Type {
                expected: Type::Cons,
                recieved: Type::from(&*object),
            }),
        })?;

        self.stack.push(cons);

        Ok(())
    }

    pub fn list(&mut self, args: usize) -> Result<(), Error> {
        let list = Object::from_iter(
            self.stack[self.stack.len() - args..]
                .iter()
                .map(|local| local.clone().into_object()),
        );
        self.stack.truncate(self.stack.len() - args);
        self.stack.push(Local::Value(list));
        Ok(())
    }

    pub fn branch(&mut self, i: usize) -> Result<(), Error> {
        let p = self.stack.pop().unwrap();

        p.with(|object| match object {
            Object::Bool(true) => Ok(()),
            Object::Bool(false) => {
                self.pc += i;
                Ok(())
            }
            object => Err(Error::Type {
                expected: Type::Bool,
                recieved: Type::from(object),
            }),
        })?;

        Ok(())
    }

    pub fn is_type(&mut self, ty: Type) -> Result<(), Error> {
        let object = self.stack.pop().unwrap().into_object();

        self.stack.push(if Type::from(&object) == ty {
            Local::Value(Object::Bool(true))
        } else {
            Local::Value(Object::Bool(false))
        });
        Ok(())
    }

    pub fn assert(&mut self) -> Result<(), Error> {
        match self.stack.pop().unwrap().into_object() {
            Object::Bool(true) => Ok(()),
            _ => Err(Error::Assert("assertion failed".to_string())),
        }
    }

    pub fn eq(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(if lhs == rhs {
            Local::Value(Object::Bool(true))
        } else {
            Local::Value(Object::Bool(false))
        });

        Ok(())
    }

    pub fn lt(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(match lhs.partial_cmp(&rhs) {
            Some(Ordering::Less) => Local::Value(Object::Bool(true)),
            Some(_) => Local::Value(Object::Bool(false)),
            None => {
                return Err(Error::Cmp(
                    Type::from(&lhs.into_object()),
                    Type::from(&rhs.into_object()),
                ))
            }
        });

        Ok(())
    }

    pub fn gt(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(match lhs.partial_cmp(&rhs) {
            Some(Ordering::Greater) => Local::Value(Object::Bool(true)),
            Some(_) => Local::Value(Object::Bool(false)),
            None => {
                return Err(Error::Cmp(
                    Type::from(&lhs.into_object()),
                    Type::from(&rhs.into_object()),
                ))
            }
        });

        Ok(())
    }

    pub fn map_create(&mut self) -> Result<(), Error> {
        let map = Object::HashMap(Rc::new(RefCell::new(HashMap::new())));
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

    fn map_items(&mut self) -> Result<(), Error> {
        let map = match self.stack.pop().unwrap().into_object() {
            Object::HashMap(map) => map,
            object => {
                return Err(Error::Type {
                    expected: Type::Map,
                    recieved: Type::from(&object),
                })
            }
        };

        let list = Object::from_iter(map.borrow().iter().map(|(key, value)| {
            Object::Cons(Rc::new(RefCell::new(Cons(
                Object::from(key),
                Object::Cons(Rc::new(RefCell::new(Cons(value.clone(), Object::Nil)))),
            ))))
        }));

        self.stack.push(Local::Value(list));

        Ok(())
    }

    fn make_struct(&mut self, args: usize) -> Result<(), Error> {
        let fields = self
            .stack
            .drain(self.stack.len() - args..self.stack.len())
            .map(Local::into_object)
            .collect::<Vec<_>>();

        let r#struct = Struct { fields };

        self.stack
            .push(Local::Value(Object::Struct(Rc::new(RefCell::new(
                r#struct,
            )))));

        Ok(())
    }

    fn set_field(&mut self, field: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap().into_object();
        let object = self.stack.pop().unwrap().into_object();

        match object {
            Object::Struct(r#struct) => {
                r#struct.borrow_mut().fields[field] = val.clone();
            }
            object => {
                return Err(Error::Type {
                    expected: Type::Struct,
                    recieved: Type::from(&object),
                })
            }
        }

        Ok(())
    }

    fn get_field(&mut self, field: usize) -> Result<(), Error> {
        let object = self.stack.pop().unwrap().into_object();

        let val = match object {
            Object::Struct(r#struct) => r#struct.borrow().fields[field].clone(),
            object => {
                return Err(Error::Type {
                    expected: Type::Struct,
                    recieved: Type::from(&object),
                })
            }
        };

        self.stack.push(Local::Value(val));

        Ok(())
    }

    fn vec_create(&mut self) -> Result<(), Error> {
        self.stack
            .push(Local::Value(Object::Vec(Rc::new(RefCell::new(Vec::new())))));

        Ok(())
    }

    fn vec_push(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap().into_object();

        let vec = match self.stack.pop().unwrap().into_object() {
            Object::Vec(vec) => vec,
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&object),
                })
            }
        };

        vec.borrow_mut().push(val);

        Ok(())
    }

    fn vec_pop(&mut self) -> Result<(), Error> {
        let vec = match self.stack.pop().unwrap().into_object() {
            Object::Vec(vec) => vec,
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&object),
                })
            }
        };

        let val = vec.borrow_mut().pop().unwrap();

        self.stack.push(Local::Value(val));

        Ok(())
    }

    fn vec_ref(&mut self) -> Result<(), Error> {
        let index = match self.stack.pop().unwrap().into_object() {
            Object::Int(int) => int,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(&object),
                })
            }
        };

        let vec = match self.stack.pop().unwrap().into_object() {
            Object::Vec(vec) => vec,
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&object),
                })
            }
        };

        let val: Object<D> = vec.borrow()[usize::try_from(index).unwrap()].clone();

        self.stack.push(Local::Value(val));

        Ok(())
    }

    fn vec_set(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap().into_object();

        let index = match self.stack.pop().unwrap().into_object() {
            Object::Int(int) => int,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(&object),
                })
            }
        };

        let vec = match self.stack.pop().unwrap().into_object() {
            Object::Vec(vec) => vec,
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&object),
                })
            }
        };

        vec.borrow_mut()[usize::try_from(index).unwrap()] = val.clone();

        self.stack.push(Local::Value(val));

        Ok(())
    }

    fn vec_len(&mut self) -> Result<(), Error> {
        let vec = match self.stack.pop().unwrap().into_object() {
            Object::Vec(vec) => vec,
            object => {
                return Err(Error::Type {
                    expected: Type::Vec,
                    recieved: Type::from(&object),
                })
            }
        };

        self.stack.push(Local::Value(Object::Int(
            vec.borrow().len().try_into().unwrap(),
        )));

        Ok(())
    }
}

impl<D: Clone> Local<D> {
    pub fn into_object(self) -> Object<D> {
        match self {
            Self::Value(object) => object,
            Self::UpValue(object) => object.borrow().clone(),
        }
    }

    pub fn with<T, F>(&self, f: F) -> T
    where
        F: FnOnce(&Object<D>) -> T,
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
        F: FnOnce(&mut Object<D>) -> T,
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

#[allow(clippy::new_without_default)]
impl<T> OpCodeTable<T> {
    pub fn new() -> Self {
        Self {
            opcodes: Vec::new(),
            debug: Vec::new(),
        }
    }

    pub fn push(&mut self, opcode: OpCode, debug: T) {
        self.opcodes.push(opcode);
        self.debug.push(debug);
    }

    pub fn opcodes(&self) -> &[OpCode] {
        self.opcodes.as_slice()
    }

    pub fn debug(&self) -> &[T] {
        self.debug.as_slice()
    }

    pub fn len(&self) -> usize {
        self.opcodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.opcodes.len() == 0
    }

    pub fn append(&mut self, other: OpCodeTable<T>) {
        for (opcode, debug) in other.opcodes.into_iter().zip(other.debug.into_iter()) {
            self.opcodes.push(opcode);
            self.debug.push(debug);
        }
    }
}

impl<D> fmt::Debug for OpCodeTable<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "OpCodeTable")
    }
}

impl<D> fmt::Display for ErrorWithDebug<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error)
    }
}

impl error::Error for ErrorWithDebug<FileSpan> {
    fn span(&self) -> Option<error::FileSpan> {
        Some(self.debug)
    }

    fn message(&self, writer: &mut dyn std::io::Write) {
        write!(writer, "{}", self.error).unwrap();
    }
}

impl Hash for OpCode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::DefGlobal(global) => global.hash(state),
            Self::SetGlobal(global) => global.hash(state),
            Self::GetGlobal(global) => global.hash(state),
            Self::SetLocal(local) => local.hash(state),
            Self::GetLocal(local) => local.hash(state),
            Self::SetUpValue(upvalue) => upvalue.hash(state),
            Self::GetUpValue(upvalue) => upvalue.hash(state),
            Self::Call(args) => args.hash(state),
            Self::Tail(args) => args.hash(state),
            Self::Lambda(arity, opcodes) => {
                arity.hash(state);
                opcodes.hash(state);
            }
            Self::CreateUpValue(upvalue) => upvalue.hash(state),
            Self::PushSymbol(symbol) => symbol.hash(state),
            Self::PushString(string) => string.hash(state),
            Self::PushChar(char) => char.hash(state),
            Self::PushInt(int) => int.hash(state),
            Self::PushFloat(float) => float.to_bits().hash(state),
            Self::PushBool(bool) => bool.hash(state),
            Self::Peek(n) => n.hash(state),
            Self::List(length) => length.hash(state),
            Self::Jmp(n) => n.hash(state),
            Self::Branch(n) => n.hash(state),
            Self::IsType(r#type) => r#type.hash(state),
            Self::GetField(field) => field.hash(state),
            Self::SetField(field) => field.hash(state),
            _ => (),
        }
    }
}

impl<D: PartialEq> PartialEq for Local<D> {
    fn eq(&self, other: &Self) -> bool {
        let a = match self {
            Local::Value(object) => object,
            Local::UpValue(upvalue) => &upvalue.borrow(),
        };

        let b = match other {
            Local::Value(object) => object,
            Local::UpValue(upvalue) => &upvalue.borrow(),
        };

        a == b
    }
}

impl<D: PartialOrd> PartialOrd for Local<D> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let a = match self {
            Local::Value(object) => object,
            Local::UpValue(upvalue) => &upvalue.borrow(),
        };

        let b = match other {
            Local::Value(object) => object,
            Local::UpValue(upvalue) => &upvalue.borrow(),
        };

        a.partial_cmp(b)
    }
}
