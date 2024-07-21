#![allow(dead_code)]

pub mod object;

use crate::object::{Cons, Lambda, NativeFunction, Type};
use gc::{Gc, GcCell, Trace};
use object::{HashMapKey, Module};
use std::cmp::{Ordering, PartialOrd};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use thiserror::Error;
use unwrap_enum::{EnumAs, EnumIs};

pub use crate::object::Object;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arity {
    Nullary,
    Nary(usize),
    Variadic(usize),
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
    #[error("expected a list for apply")]
    Apply,
    #[error("other error: {0}")]
    Other(#[from] Box<dyn std::error::Error>),
}

#[derive(Clone, Debug, EnumAs, EnumIs, PartialEq, Eq, Hash)]
pub enum OpCode<D> {
    DefGlobal(Gc<String>),
    SetGlobal(Gc<String>),
    GetGlobal(Gc<String>),
    SetLocal(usize),
    GetLocal(usize),
    SetUpValue(usize),
    GetUpValue(usize),
    DefModuleVar(Gc<String>),
    SetModuleVar(Gc<String>),
    GetModuleVar(Gc<String>),
    Call(usize),
    Tail(usize),
    Apply,
    Return,
    Lambda {
        arity: Arity,
        body: Gc<OpCodeTable<D>>,
    },
    CreateUpValue(UpValue),
    CreateModule(Gc<String>),
    PushSymbol(Gc<String>),
    PushInt(i64),
    PushChar(char),
    PushString(Gc<String>),
    PushBool(bool),
    PushNil,
    Pop,
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
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OpCodeTable<D> {
    opcodes: Vec<OpCode<D>>,
    debug: Vec<D>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UpValue {
    Local(usize),
    UpValue(usize),
}

#[derive(Clone, Debug)]
struct Frame<D: 'static> {
    function: Option<Gc<GcCell<Lambda<D>>>>,
    pc: usize,
    bp: usize,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Local<D: 'static> {
    Value(Object<D>),
    UpValue(Gc<GcCell<Object<D>>>),
}

pub struct Vm<D: 'static> {
    globals: HashMap<String, Object<D>>,
    stack: Vec<Local<D>>,
    frames: Vec<Frame<D>>,
    current_function: Option<Gc<GcCell<Lambda<D>>>>,
    pc: usize,
    bp: usize,
}

#[allow(clippy::new_without_default)]
impl<D: Clone + PartialEq + PartialOrd + Hash + Debug> Vm<D> {
    pub fn new() -> Self {
        Self {
            globals: HashMap::new(),
            stack: Vec::new(),
            frames: Vec::new(),
            current_function: None,
            pc: 0,
            bp: 0,
        }
    }

    pub fn load_native_function<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&mut [Local<D>]) -> Result<Object<D>, Error> + 'static,
    {
        let native_function = NativeFunction::new(f);
        self.globals
            .insert(name.to_string(), Object::NativeFunction(native_function));
    }

    pub fn eval(&mut self, opcode_table: &OpCodeTable<D>) -> Result<(), (Error, D)> {
        loop {
            let opcode = if let Some(function) = &self.current_function {
                function.borrow().opcodes.opcodes[self.pc].clone()
            } else if self.pc < opcode_table.opcodes.len() {
                opcode_table.opcodes[self.pc].clone()
            } else {
                self.pc = 0;
                return Ok(());
            };

            self.pc += 1;

            match self.dispatch(opcode) {
                Ok(_) => continue,
                Err(e) => {
                    let debug = if let Some(function) = &self.current_function {
                        function.borrow().opcodes.debug[self.pc - 1].clone()
                    } else {
                        opcode_table.debug[self.pc - 1].clone()
                    };
                    return Err((e, debug));
                }
            }
        }
    }

    fn dispatch(&mut self, opcode: OpCode<D>) -> Result<(), Error> {
        match opcode {
            OpCode::DefGlobal(global) => self.def_global(global.as_str())?,
            OpCode::SetGlobal(global) => self.set_global(global.as_str())?,
            OpCode::GetGlobal(global) => self.get_global(global.as_str())?,
            OpCode::SetLocal(local) => self.set_local(local)?,
            OpCode::GetLocal(local) => self.get_local(local)?,
            OpCode::SetUpValue(upvalue) => self.set_upvalue(upvalue)?,
            OpCode::GetUpValue(upvalue) => self.get_upvalue(upvalue)?,
            OpCode::DefModuleVar(module_var) => self.def_module_var(module_var.as_str())?,
            OpCode::SetModuleVar(module_var) => self.set_module_var(module_var.as_str())?,
            OpCode::GetModuleVar(module_var) => self.get_module_var(module_var.as_str())?,
            OpCode::Call(args) => self.call(args)?,
            OpCode::Tail(args) => self.tail(args)?,
            OpCode::Return => self.ret()?,
            OpCode::Apply => self.apply()?,
            OpCode::Lambda { arity, body } => self.lambda(arity, body)?,
            OpCode::CreateUpValue(upvalue) => self.create_upvalue(upvalue)?,
            OpCode::CreateModule(module_name) => {
                self.stack
                    .push(Local::Value(Object::Module(Gc::new(GcCell::new(Module {
                        name: module_name.to_string(),
                        globals: HashMap::new(),
                    })))));
            }
            OpCode::PushSymbol(symbol) => {
                self.stack
                    .push(Local::Value(Object::Symbol(symbol.clone())));
            }
            OpCode::PushString(string) => {
                self.stack
                    .push(Local::Value(Object::String(string.clone())));
            }
            OpCode::PushInt(i) => self.stack.push(Local::Value(Object::Int(i))),
            OpCode::PushChar(c) => self.stack.push(Local::Value(Object::Char(c))),
            OpCode::PushBool(b) => self.stack.push(Local::Value(Object::Bool(b))),
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
        }

        Ok(())
    }

    pub fn peek(&self, i: usize) -> Option<&Local<D>> {
        self.stack.get(self.stack.len() - i - 1)
    }

    pub fn push(&mut self, object: Object<D>) {
        self.stack.push(Local::Value(object));
    }

    pub fn pop(&mut self) -> Option<Local<D>> {
        self.stack.pop()
    }

    pub fn def_global(&mut self, global: &str) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        self.globals.insert(global.to_string(), val.into_object());
        self.stack.push(Local::Value(Object::Nil));
        Ok(())
    }

    pub fn set_global(&mut self, global: &str) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        if let Some(var) = self.globals.get_mut(global) {
            *var = val.clone().into_object();
            self.stack.push(val);
            Ok(())
        } else {
            Err(Error::NotFound(global.to_string()))
        }
    }

    pub fn get_global(&mut self, global: &str) -> Result<(), Error> {
        if let Some(var) = self.globals.get(global) {
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
                let gc = Gc::new(GcCell::new(val));
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

    pub fn def_module_var(&mut self, var: &str) -> Result<(), Error> {
        let module = self.stack.pop().unwrap().into_object();
        let val = self.stack.pop().unwrap().into_object();

        match module {
            Object::Module(m) => {
                m.borrow_mut().globals.insert(var.to_string(), val);
                Ok(())
            }
            object => Err(Error::Type {
                expected: Type::Module,
                recieved: Type::from(&object),
            }),
        }
    }

    pub fn set_module_var(&mut self, var: &str) -> Result<(), Error> {
        let module = self.stack.pop().unwrap().into_object();
        let val = self.stack.pop().unwrap().into_object();

        match module {
            Object::Module(m) => {
                if let Some(var) = m.borrow_mut().globals.get_mut(var) {
                    *var = val;
                } else {
                    return Err(Error::NotFound(var.to_string()));
                }

                Ok(())
            }
            object => Err(Error::Type {
                expected: Type::Module,
                recieved: Type::from(&object),
            }),
        }
    }

    pub fn get_module_var(&mut self, var: &str) -> Result<(), Error> {
        let module = self.stack.pop().unwrap().into_object();

        match module {
            Object::Module(m) => {
                self.stack.push(Local::Value(
                    m.borrow()
                        .globals
                        .get(var)
                        .cloned()
                        .ok_or(Error::NotFound(var.to_string()))?,
                ));

                Ok(())
            }
            object => Err(Error::Type {
                expected: Type::Module,
                recieved: Type::from(&object),
            }),
        }
    }

    pub fn call(&mut self, args: usize) -> Result<(), Error> {
        match self.stack[self.stack.len() - args - 1]
            .clone()
            .into_object()
        {
            Object::Function(function) => {
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
            Object::NativeFunction(function) => self.native_call(args, function),
            object => Err(Error::Type {
                expected: Type::Function,
                recieved: Type::from(&object),
            }),
        }
    }

    fn tail(&mut self, args: usize) -> Result<(), Error> {
        match self.stack[self.stack.len() - args - 1]
            .clone()
            .into_object()
        {
            Object::Function(function) => {
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

    fn check_arity(&mut self, args: usize, function: Gc<GcCell<Lambda<D>>>) -> Result<(), Error> {
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

    pub fn lambda(&mut self, arity: Arity, opcodes: Gc<OpCodeTable<D>>) -> Result<(), Error> {
        let function = Lambda {
            arity,
            opcodes: opcodes.clone(),
            upvalues: Vec::new(),
        };

        let object = Object::Function(Gc::new(GcCell::new(function)));

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

        let cons = Object::Cons(Gc::new(GcCell::new(Cons(
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
        let list = make_list(
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

        match p.into_object() {
            Object::Bool(true) => (),
            Object::Bool(false) => {
                self.pc += i;
            }
            object => {
                return Err(Error::Type {
                    expected: Type::Bool,
                    recieved: Type::from(&object),
                });
            }
        }

        Ok(())
    }

    pub fn is_type(&mut self, ty: Type) -> Result<(), Error> {
        self.stack.push(
            if Type::from(&self.stack.last().unwrap().clone().into_object()) == ty {
                Local::Value(Object::Bool(true))
            } else {
                Local::Value(Object::Bool(false))
            },
        );
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

        self.stack.push(if lhs.into_object() == rhs.into_object() {
            Local::Value(Object::Bool(true))
        } else {
            Local::Value(Object::Bool(false))
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
                Some(Ordering::Less) => Local::Value(Object::Bool(true)),
                Some(_) => Local::Value(Object::Bool(false)),
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
                Some(Ordering::Greater) => Local::Value(Object::Bool(true)),
                Some(_) => Local::Value(Object::Bool(false)),
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
        let map = Object::HashMap(Gc::new(GcCell::new(HashMap::new())));
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

        let list = make_list(map.borrow().iter().map(|(key, value)| {
            Object::Cons(Gc::new(GcCell::new(Cons(
                Object::from(key),
                Object::Cons(Gc::new(GcCell::new(Cons(value.clone(), Object::Nil)))),
            ))))
        }));

        self.stack.push(Local::Value(list));

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
        F: Fn(&Object<D>) -> T,
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

impl<T> OpCodeTable<T> {
    pub fn new() -> Self {
        Self {
            opcodes: Vec::new(),
            debug: Vec::new(),
        }
    }

    pub fn push(&mut self, opcode: OpCode<T>, debug: T) {
        self.opcodes.push(opcode);
        self.debug.push(debug);
    }

    pub fn opcodes(&self) -> &[OpCode<T>] {
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

unsafe impl<D> Trace for OpCodeTable<D> {
    unsafe fn root(&self) {}

    unsafe fn unroot(&self) {}

    unsafe fn trace(&self, _: &mut dyn FnMut(std::ptr::NonNull<gc::Inner<dyn Trace>>) -> bool) {}
}

fn make_list<'a, D: Clone>(mut objects: impl Iterator<Item = Object<D>>) -> Object<D> {
    let Some(first) = objects.next() else {
        return Object::Nil;
    };

    let mut tail = Gc::new(GcCell::new(Cons(first, Object::Nil)));

    let list = Object::Cons(tail.clone());

    for object in objects {
        let new_tail = Gc::new(GcCell::new(Cons(object, Object::Nil)));
        tail.deref().borrow_mut().1 = Object::Cons(new_tail.clone());
        tail = new_tail
    }

    list
}
