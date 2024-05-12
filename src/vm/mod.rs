use std::cell::RefCell;
use std::collections::HashMap;

use cycle_collector::{Cc, CcInner, Context, Trace};
use unwrap_enum::{EnumAs, EnumIs};

use crate::Value;

#[derive(Clone, Debug)]
pub enum Type {
    Function,
    Cons,
    String,
    Symbol,
    Int,
    True,
    Nil,
}

#[derive(Clone, Debug)]
pub enum Error {
    Type { expected: Type, recived: Type },
    NotFound(String),
}

#[derive(Clone, Debug)]
pub enum OpCode {
    DefGlobal(String),
    SetGlobal(String),
    SetLocal(usize),
    GetLocal(usize),
    SetUpValue(usize),
    GetUpValue(usize),
    Call,
    Tail,
    Return,
    Lambda {
        body: Vec<OpCode>,
        upvalues: Vec<UpValue>,
    },
    Push(Value),
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Car,
    Cdr,
    Cons,
    Jmp(isize),
    Branch(isize),
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
enum Object<'ctx: 'static> {
    Function(Cc<'ctx, RefCell<Lambda<'ctx>>>),
    Cons(Cons<'ctx>),
    String(String),
    Symbol(String),
    Int(i64),
    True,
    Nil,
}

#[derive(Clone, Copy, Debug)]
pub struct UpValue {
    pub frame: usize,
    pub index: usize,
}

#[derive(Clone, Debug)]
struct Lambda<'ctx: 'static> {
    opcodes: Vec<OpCode>,
    upvalues: Vec<Cc<'ctx, RefCell<Object<'ctx>>>>,
}

#[derive(Clone, Debug)]
pub struct Cons<'ctx: 'static>(
    Cc<'ctx, RefCell<Object<'ctx>>>,
    Cc<'ctx, RefCell<Object<'ctx>>>,
);

struct Frame<'ctx: 'static> {
    function: Cc<'ctx, RefCell<Lambda<'ctx>>>,
    pc: usize,
    bp: usize,
}

pub struct Vm<'ctx: 'static> {
    cc: &'static Context,
    globals: HashMap<String, Cc<'ctx, RefCell<Object<'ctx>>>>,
    stack: Vec<Cc<'ctx, RefCell<Object<'ctx>>>>,
    frames: Vec<Frame<'ctx>>,
    pc: usize,
    bp: usize,
}

impl<'ctx> Vm<'ctx> {
    pub fn new(ctx: &'static Context) -> Self {
        Self {
            cc: ctx,
            globals: HashMap::new(),
            stack: Vec::new(),
            frames: Vec::new(),
            pc: 0,
            bp: 0,
        }
    }

    fn def_global(&mut self, name: &str) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        self.globals.insert(name.to_string(), val);
        Ok(())
    }

    fn set_global(&mut self, name: &str) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        if let Some(var) = self.globals.get_mut(name) {
            *var = val;
            Ok(())
        } else {
            Err(Error::NotFound(name.to_string()))
        }
    }

    fn set_local(&mut self, local: usize) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let i = self.bp + local;
        *self.stack[i].borrow_mut() = (*val).clone().into_inner();
        Ok(())
    }

    fn get_local(&mut self, local: usize) -> Result<(), Error> {
        let i = self.bp + local;
        let local = self.stack[i].clone();
        self.stack.push(local);
        Ok(())
    }

    fn call(&mut self) -> Result<(), Error> {
        let val = self.stack.pop().unwrap();
        let Object::Function(function) = (*val).clone().into_inner() else {
            return Err(Error::Type {
                expected: Type::Function,
                recived: Type::from(&*(*val).borrow()),
            });
        };

        let frame = Frame {
            function: function.clone(),
            pc: self.pc,
            bp: self.bp,
        };

        self.frames.push(frame);
        self.pc = 0;
        self.bp = self.stack.len();

        Ok(())
    }

    fn tail(&mut self) -> Result<(), Error> {
        self.pc = 0;
        Ok(())
    }

    fn ret(&mut self) -> Result<(), Error> {
        let frame = self.frames.pop().unwrap();
        self.pc = frame.pc;
        self.bp = frame.bp;
        Ok(())
    }

    fn lambda(
        &mut self,
        opcodes: impl Iterator<Item = OpCode>,
        upvalues: impl Iterator<Item = UpValue>,
    ) -> Result<(), Error> {
        let mut values = Vec::new();

        for upvalue in upvalues {
            let i = self.frames[upvalue.frame].bp + upvalue.index;
            values.push(self.stack[i].clone());
        }

        let function = self.cc.create(RefCell::new(Lambda {
            opcodes: opcodes.collect(),
            upvalues: values,
        }));

        let object = self.cc.create(RefCell::new(Object::Function(function)));

        self.stack.push(object);

        Ok(())
    }

    fn binary_integer_op(&mut self, f: impl Fn(i64, i64) -> i64) -> Result<(), Error> {
        let a = self.stack.pop().unwrap();
        let b = self.stack.pop().unwrap();

        let Object::Int(a) = *(*a).borrow() else {
            return Err(Error::Type {
                expected: Type::Int,
                recived: Type::from(&*(*a).borrow()),
            });
        };

        let Object::Int(b) = *(*b).borrow() else {
            return Err(Error::Type {
                expected: Type::Int,
                recived: Type::from(&*(*b).borrow()),
            });
        };

        let result = self.cc.create(RefCell::new(Object::Int(f(a, b))));

        self.stack.push(result);

        Ok(())
    }

    fn car(&mut self) -> Result<(), Error> {
        let car = match &*(*self.stack.last().unwrap()).borrow() {
            Object::Cons(Cons(car, _)) => Cc::clone(car),
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recived: Type::from(object),
                })
            }
        };

        self.stack.push(car);

        Ok(())
    }

    fn cdr(&mut self) -> Result<(), Error> {
        let car = match &*(*self.stack.last().unwrap()).borrow() {
            Object::Cons(Cons(_, cdr)) => Cc::clone(cdr),
            object => {
                return Err(Error::Type {
                    expected: Type::Cons,
                    recived: Type::from(object),
                })
            }
        };

        self.stack.push(car);

        Ok(())
    }

    fn cons(&mut self) -> Result<(), Error> {
        let a = self.stack.pop().unwrap();
        let b = self.stack.pop().unwrap();

        let cons = Object::Cons(Cons(a, b));

        let object = self.cc.create(RefCell::new(cons));

        self.stack.push(object);

        Ok(())
    }

    fn branch(&mut self, i: usize) -> Result<(), Error> {
        let p = self.stack.pop().unwrap();

        if p.borrow().is_true() {
            self.pc += i;
        }

        Ok(())
    }
}

impl<'ctx> From<&Object<'ctx>> for Type {
    fn from(value: &Object) -> Self {
        match value {
            Object::Function(_) => Type::Function,
            Object::Cons(_) => Type::Cons,
            Object::String(_) => Type::String,
            Object::Symbol(_) => Type::Symbol,
            Object::Int(_) => Type::Int,
            Object::True => Type::True,
            Object::Nil => Type::Nil,
        }
    }
}

unsafe impl<'ctx: 'static> Trace for Object<'ctx> {
    unsafe fn refs(&self, ptrs: &mut Vec<std::ptr::NonNull<CcInner<dyn Trace>>>) {
        match self {
            Self::Function(function) => function.refs(ptrs),
            Self::Cons(cons) => cons.refs(ptrs),
            _ => (),
        }
    }
}

unsafe impl<'ctx: 'static> Trace for Cons<'ctx> {
    unsafe fn refs(&self, ptrs: &mut Vec<std::ptr::NonNull<CcInner<dyn Trace>>>) {
        let (car, cdr) = (&self.0, &self.1);
        car.refs(ptrs);
        cdr.refs(ptrs);
    }
}

unsafe impl<'ctx: 'static> Trace for Lambda<'ctx> {
    unsafe fn refs(&self, ptrs: &mut Vec<std::ptr::NonNull<CcInner<dyn Trace>>>) {
        for upvalue in &self.upvalues {
            upvalue.refs(ptrs);
        }
    }
}
