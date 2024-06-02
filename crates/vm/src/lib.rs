#![allow(dead_code)]

use core::fmt;
use std::cmp::{Ordering, PartialOrd};
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::{Hash, Hasher};
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Function,
    Cons,
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
    #[error("assertion failed: {0}")]
    Assert(String),
    #[error("cannot compare this combination of types: {0} {1}")]
    Cmp(Type, Type),
    #[error("other error: {0}")]
    Other(#[from] Rc<dyn std::error::Error>),
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

#[derive(Clone, Debug, EnumAs, EnumIs, PartialEq)]
pub enum Object {
    NativeFunction(NativeFunction),
    Function(Rc<RefCell<Lambda>>),
    Cons(Cons),
    String(String),
    Symbol(String),
    Int(i64),
    True,
    Nil,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UpValue {
    Local(usize),
    UpValue(usize),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Lambda {
    arity: Arity,
    opcodes: Rc<[OpCode]>,
    upvalues: Vec<Rc<RefCell<Object>>>,
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct NativeFunction(Rc<dyn Fn(&[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error>>);

#[derive(Clone, Debug, PartialEq)]
pub struct Cons(Rc<RefCell<Object>>, Rc<RefCell<Object>>);

#[derive(Clone, Debug)]
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
        F: Fn(&[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> + 'static,
    {
        let native_function = NativeFunction::new(f);
        self.globals.insert(
            name.to_string(),
            Rc::new(RefCell::new(Object::NativeFunction(native_function))),
        );
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
                OpCode::PushTrue => self.stack.push(Rc::new(RefCell::new(Object::True))),
                OpCode::PushNil => self.stack.push(Rc::new(RefCell::new(Object::Nil))),
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
                .as_symbol()
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
            .get_mut(self.constants.get(&constant).unwrap().as_symbol().unwrap())
        {
            *var = Rc::clone(&val);
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
            self.stack.push(Rc::clone(var))
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

    pub fn set_upvalue(&mut self, upvalue: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();

        *self
            .current_function
            .as_mut()
            .unwrap()
            .borrow_mut()
            .upvalues[upvalue]
            .borrow_mut() = val.borrow().deref().clone();

        Ok(())
    }

    pub fn get_upvalue(&mut self, upvalue: usize) -> Result<(), Error> {
        let val = Rc::clone(&self.current_function.as_ref().unwrap().borrow().upvalues[upvalue]);

        self.stack.push(val);

        Ok(())
    }

    pub fn create_upvalue(&mut self, upvalue: UpValue) -> Result<(), Error> {
        let function = match self.stack.last().unwrap().borrow().deref() {
            Object::Function(function) => Rc::clone(function),
            object => {
                return Err(Error::Type {
                    expected: Type::Function,
                    recieved: Type::from(object),
                })
            }
        };

        let val = match upvalue {
            UpValue::Local(i) => self.stack[self.bp + i].clone(),
            UpValue::UpValue(i) => {
                self.current_function.as_ref().unwrap().borrow().upvalues[i].clone()
            }
        };

        function.borrow_mut().upvalues.push(val);

        Ok(())
    }

    pub fn call(&mut self, args: usize) -> Result<(), Error> {
        match self.stack[self.stack.len() - args - 1]
            .clone()
            .borrow()
            .deref()
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

                self.current_function = Some(Rc::clone(function));
                self.bp = self.stack.len() - args;
                self.pc = 0;

                Ok(())
            }
            Object::NativeFunction(function) => {
                let parameters = &self.stack[self.stack.len() - args..];
                let ret = function.0(parameters);

                self.stack.truncate(self.stack.len() - args - 1);

                match ret {
                    Ok(val) => {
                        self.stack.push(val);
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            }
            object => Err(Error::Type {
                expected: Type::Function,
                recieved: Type::from(object),
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
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        let a = match lhs.borrow().deref() {
            Object::Int(i) => *i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(object),
                })
            }
        };

        let b = match rhs.borrow().deref() {
            Object::Int(i) => *i,
            object => {
                return Err(Error::Type {
                    expected: Type::Int,
                    recieved: Type::from(object),
                })
            }
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

    pub fn car(&mut self) -> Result<(), Error> {
        let car = match self.stack.pop().unwrap().borrow().deref() {
            Object::Cons(Cons(car, _)) => Rc::clone(car),
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recieved: Type::from(object),
                })
            }
        };

        self.stack.push(car);

        Ok(())
    }

    pub fn cdr(&mut self) -> Result<(), Error> {
        let car = match self.stack.pop().unwrap().borrow().deref() {
            Object::Cons(Cons(_, cdr)) => Rc::clone(cdr),
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recieved: Type::from(object),
                })
            }
        };

        self.stack.push(car);

        Ok(())
    }

    pub fn cons(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        let cons = Object::Cons(Cons(lhs, rhs));

        let object = Rc::new(RefCell::new(cons));

        self.stack.push(object);

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

        match p.borrow().deref() {
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

    pub fn is_type(&mut self, ty: Type) -> Result<(), Error> {
        self.stack.push(
            if Type::from(self.stack.last().unwrap().borrow().deref()) == ty {
                Rc::new(RefCell::new(Object::True))
            } else {
                Rc::new(RefCell::new(Object::Nil))
            },
        );
        Ok(())
    }

    pub fn assert(&mut self) -> Result<(), Error> {
        match self.stack.pop().unwrap().borrow().deref() {
            Object::True => Ok(()),
            _ => Err(Error::Assert("assertion failed".to_string())),
        }
    }

    pub fn eq(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(if lhs == rhs {
            Rc::new(RefCell::new(Object::True))
        } else {
            Rc::new(RefCell::new(Object::Nil))
        });

        Ok(())
    }

    pub fn lt(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(match lhs.partial_cmp(&rhs) {
            Some(Ordering::Less) => Rc::new(RefCell::new(Object::True)),
            Some(_) => Rc::new(RefCell::new(Object::Nil)),
            None => {
                return Err(Error::Cmp(
                    Type::from(lhs.borrow().deref()),
                    Type::from(rhs.borrow().deref()),
                ))
            }
        });

        Ok(())
    }

    pub fn gt(&mut self) -> Result<(), Error> {
        let rhs = self.stack.pop().unwrap();
        let lhs = self.stack.pop().unwrap();

        self.stack.push(match lhs.partial_cmp(&rhs) {
            Some(Ordering::Greater) => Rc::new(RefCell::new(Object::True)),
            Some(_) => Rc::new(RefCell::new(Object::Nil)),
            None => {
                return Err(Error::Cmp(
                    Type::from(lhs.borrow().deref()),
                    Type::from(rhs.borrow().deref()),
                ))
            }
        });

        Ok(())
    }
}

impl Lambda {
    pub fn arity(&self) -> Arity {
        self.arity
    }
}

impl NativeFunction {
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> + 'static,
    {
        Self(Rc::new(f))
    }
}

impl PartialEq for NativeFunction {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl PartialOrd for NativeFunction {
    fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
        None
    }
}

impl Debug for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("NativeFunction").finish()
    }
}

impl From<&Object> for Type {
    fn from(value: &Object) -> Self {
        match value {
            Object::Function(_) | Object::NativeFunction(_) => Type::Function,
            Object::Cons(_) => Type::Cons,
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
            Self::Cons => write!(f, "cons"),
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
            Object::Cons(cons) => Value::Cons(Box::new(value::Cons::try_from(cons)?)),
            Object::String(string) => Value::String(string.clone()),
            Object::Symbol(symbol) => Value::Symbol(symbol.clone()),
            Object::Int(i) => Value::Int(*i),
            Object::True => Value::True,
            Object::Nil => Value::Nil,
            _ => return Err(()),
        })
    }
}

impl TryFrom<&crate::Cons> for value::Cons {
    type Error = ();
    fn try_from(value: &crate::Cons) -> Result<Self, Self::Error> {
        Ok(value::Cons(
            Value::try_from(&*value.0.borrow())?,
            Value::try_from(&*value.1.borrow())?,
        ))
    }
}

impl PartialOrd for Object {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match (self, other) {
            (Object::Symbol(a), Object::Symbol(b)) => a.cmp(b),
            (Object::String(a), Object::String(b)) => a.cmp(b),
            (Object::Int(a), Object::Int(b)) => a.cmp(b),
            (Object::True, Object::True) => Ordering::Equal,
            (Object::Nil, Object::Nil) => Ordering::Equal,
            _ => return None,
        })
    }
}

impl Display for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.arity {
            Arity::Nullary => write!(f, "nullary lambda"),
            Arity::Nary(n) => write!(f, "{n}-ary lambda"),
            Arity::Variadic => write!(f, "variadic lambda"),
        }
    }
}

impl Display for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "native function")
    }
}

impl Display for Cons {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({} {})",
            self.0.borrow().deref(),
            self.1.borrow().deref()
        )
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NativeFunction(native_function) => write!(f, "{native_function}",),
            Self::Function(function) => write!(f, "{}", function.borrow().deref()),
            Self::Cons(cons) => write!(f, "{cons}"),
            Self::Symbol(symbol) => write!(f, "'{symbol}"),
            Self::String(string) => write!(f, r#""{string}""#),
            Self::Int(i) => write!(f, "{i}"),
            Self::True => write!(f, "true"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

fn make_list(objects: &[Rc<RefCell<Object>>]) -> Rc<RefCell<Object>> {
    if !objects.is_empty() {
        Rc::new(RefCell::new(Object::Cons(Cons(
            Rc::clone(&objects[0]),
            make_list(&objects[1..]),
        ))))
    } else {
        Rc::new(RefCell::new(Object::Nil))
    }
}
