use crate::{Arity, Error, OpCodeTable};
use gc::{Gc, GcCell, Trace};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Write;
use std::fmt::{self, Debug, Display};
use std::ops::Deref;
use std::ptr::NonNull;
use std::rc::Rc;
use unwrap_enum::{EnumAs, EnumIs};

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum Type {
    Struct,
    Function,
    Cons,
    Map,
    String,
    Symbol,
    Int,
    Float,
    Char,
    Bool,
    Nil,
}

#[derive(Clone, Debug, EnumAs, EnumIs, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HashMapKey {
    String(Gc<String>),
    Symbol(Gc<String>),
    Int(i64),
    Char(char),
    Bool(bool),
    Nil,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Object<D: 'static> {
    Box(Gc<GcCell<Object<D>>>),
    Struct(Gc<GcCell<Struct<D>>>),
    NativeFunction(NativeFunction<D>),
    Function(Gc<GcCell<Lambda<D>>>),
    Cons(Gc<GcCell<Cons<D>>>),
    HashMap(Gc<GcCell<HashMap<HashMapKey, Object<D>>>>),
    String(Gc<String>),
    Symbol(Gc<String>),
    Int(i64),
    Float(f64),
    Char(char),
    Bool(bool),
    Nil,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Struct<D: 'static> {
    pub(crate) fields: Vec<Object<D>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Lambda<D: 'static> {
    pub(crate) arity: Arity,
    pub(crate) opcodes: Gc<OpCodeTable<D>>,
    pub(crate) upvalues: Vec<Gc<GcCell<Object<D>>>>,
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct NativeFunction<D: 'static>(
    pub(crate) Rc<dyn Fn(&mut [crate::Local<D>]) -> Result<Object<D>, Error>>,
);

#[derive(Clone, Debug, PartialEq)]
pub struct Cons<D: 'static>(pub Object<D>, pub Object<D>);

#[derive(Clone, Debug)]
pub struct IterCons<D: 'static>(Option<Cons<D>>);

#[derive(Clone, Debug)]
pub struct IterCars<D: 'static>(IterCons<D>);

impl<D: Clone> FromIterator<Object<D>> for Object<D> {
    fn from_iter<T: IntoIterator<Item = Object<D>>>(iter: T) -> Self {
        let mut objects = iter.into_iter();

        let Some(first) = objects.by_ref().next() else {
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
}

impl<D: Clone + 'static> Cons<D> {
    pub fn iter(&self) -> IterCons<D> {
        IterCons(Some(self.clone()))
    }

    pub fn iter_cars(&self) -> IterCars<D> {
        IterCars(self.iter())
    }
}

impl<D> Lambda<D> {
    pub fn arity(&self) -> Arity {
        self.arity
    }
}

impl<D> NativeFunction<D> {
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&mut [crate::Local<D>]) -> Result<Object<D>, Error> + 'static,
    {
        Self(Rc::new(f))
    }
}

impl<D> PartialEq for NativeFunction<D> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<D> PartialOrd for NativeFunction<D> {
    fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
        None
    }
}

impl<D> Debug for NativeFunction<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("NativeFunction").finish()
    }
}

impl<D> From<&Object<D>> for Type {
    fn from(value: &Object<D>) -> Self {
        match value {
            Object::Box(object) => Type::from(&*object.borrow()),
            Object::Struct(_) => Type::Struct,
            Object::Function(_) | Object::NativeFunction(_) => Type::Function,
            Object::Cons(_) => Type::Cons,
            Object::HashMap(_) => Type::Map,
            Object::String(_) => Type::String,
            Object::Symbol(_) => Type::Symbol,
            Object::Int(_) => Type::Int,
            Object::Float(_) => Type::Float,
            Object::Char(_) => Type::Char,
            Object::Bool(_) => Type::Bool,
            Object::Nil => Type::Nil,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Function => write!(f, "function"),
            Self::Struct => write!(f, "struct"),
            Self::Cons => write!(f, "cons"),
            Self::Map => write!(f, "map"),
            Self::Symbol => write!(f, "symbol"),
            Self::String => write!(f, "string"),
            Self::Int => write!(f, "int"),
            Self::Float => write!(f, "float"),
            Self::Char => write!(f, "char"),
            Self::Bool => write!(f, "bool"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

impl<D: PartialEq> PartialEq for Object<D> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Object::Struct(a), Object::Struct(b)) => a == b,
            (Object::Cons(a), Object::Cons(b)) => *a.borrow() == *b.borrow(),
            (Object::String(a), Object::String(b)) => a == b,
            (Object::Symbol(a), Object::Symbol(b)) => a == b,
            (Object::Char(a), Object::Char(b)) => a == b,
            (Object::Int(a), Object::Int(b)) => a == b,
            (Object::Float(a), Object::Float(b)) => a == b,
            (Object::Bool(a), Object::Bool(b)) => a == b,
            (Object::Nil, Object::Nil) => true,
            _ => false,
        }
    }
}

impl<D: PartialOrd> PartialOrd for Object<D> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Object::Symbol(a), Object::Symbol(b)) => a.partial_cmp(b),
            (Object::String(a), Object::String(b)) => a.partial_cmp(b),
            (Object::Int(a), Object::Int(b)) => a.partial_cmp(b),
            (Object::Float(a), Object::Float(b)) => a.partial_cmp(b),
            (Object::Bool(a), Object::Bool(b)) => a.partial_cmp(b),
            (Object::Nil, Object::Nil) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

impl<D> Display for Lambda<D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.arity {
            Arity::Nullary => write!(f, "nullary lambda"),
            Arity::Nary(n) => write!(f, "{n}-ary lambda"),
            Arity::Variadic(n) => write!(f, "{n}-ary variadic lambda"),
        }
    }
}

impl<D> Display for NativeFunction<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "native function")
    }
}

impl<D: Clone> Display for Cons<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        pretty_print(self, 0, f)
    }
}

impl<D: Clone> Display for Object<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Box(object) => write!(f, "box({object})"),
            Self::Struct(r#struct) => {
                write!(f, "struct(")?;
                for (i, field) in r#struct.borrow().fields.iter().enumerate() {
                    write!(f, "{field}")?;
                    if i < r#struct.borrow().fields.len() - 1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
            Self::NativeFunction(native_function) => write!(f, "{native_function}",),
            Self::Function(function) => write!(f, "{}", *function.deref().borrow()),
            Self::Cons(cons) => write!(f, "{}", cons.borrow().deref()),
            Self::HashMap(map) => {
                for (key, val) in map.deref().borrow().iter() {
                    writeln!(f, "{key} => {val},")?;
                }
                Ok(())
            }
            Self::Symbol(symbol) => write!(f, "'{symbol}"),
            Self::String(string) => write!(f, r#""{string}""#),
            Self::Int(i) => write!(f, "{i}"),
            Self::Float(i) => write!(f, "{i}"),
            Self::Char(c) => write!(f, r#"'{c}'"#),
            Self::Bool(true) => write!(f, "true"),
            Self::Bool(false) => write!(f, "false"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

impl Display for HashMapKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::String(string) => write!(f, r#""{string}""#),
            Self::Symbol(symbol) => write!(f, "'{symbol}"),
            Self::Char(c) => write!(f, "'{c}'"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Bool(true) => write!(f, "true"),
            Self::Bool(false) => write!(f, "false"),
            Self::Nil => write!(f, "nil"),
        }
    }
}

impl<D: Clone> Iterator for IterCons<D> {
    type Item = Cons<D>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.0.take();
        self.0 = if let Some(current) = current.clone() {
            current
                .1
                .as_cons()
                .map(|cons| cons.deref().borrow().clone())
        } else {
            None
        };
        current
    }
}

impl<D: Clone> Iterator for IterCars<D> {
    type Item = Object<D>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|cons| cons.0.clone())
    }
}

impl<D> TryFrom<&Object<D>> for HashMapKey {
    type Error = ();
    fn try_from(value: &Object<D>) -> Result<Self, Self::Error> {
        Ok(match value {
            Object::Symbol(symbol) => Self::Symbol(symbol.clone()),
            Object::String(string) => Self::String(string.clone()),
            Object::Char(c) => Self::Char(*c),
            Object::Int(i) => Self::Int(*i),
            Object::Bool(b) => Self::Bool(*b),
            Object::Nil => Self::Nil,
            _ => return Err(()),
        })
    }
}

impl<D> From<&HashMapKey> for Object<D> {
    fn from(value: &HashMapKey) -> Self {
        match value {
            HashMapKey::Symbol(symbol) => Object::Symbol(symbol.clone()),
            HashMapKey::String(string) => Object::String(string.clone()),
            HashMapKey::Char(char) => Object::Char(*char),
            HashMapKey::Int(int) => Object::Int(*int),
            HashMapKey::Bool(bool) => Object::Bool(*bool),
            HashMapKey::Nil => Object::Nil,
        }
    }
}

unsafe impl Trace for HashMapKey {
    unsafe fn root(&self) {
        match self {
            Self::Symbol(symbol) => symbol.root(),
            Self::String(string) => string.root(),
            _ => (),
        }
    }

    unsafe fn unroot(&self) {
        match self {
            Self::Symbol(symbol) => symbol.unroot(),
            Self::String(string) => string.unroot(),
            _ => (),
        }
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>) -> bool) {
        match self {
            Self::Symbol(symbol) => symbol.trace(tracer),
            Self::String(string) => string.trace(tracer),
            _ => (),
        }
    }
}

unsafe impl<D: 'static> Trace for Lambda<D> {
    unsafe fn root(&self) {
        self.upvalues.root();
    }

    unsafe fn unroot(&self) {
        self.upvalues.unroot();
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>) -> bool) {
        self.upvalues.trace(tracer);
    }
}

unsafe impl<D: 'static> Trace for Object<D> {
    unsafe fn root(&self) {
        match self {
            Self::Struct(r#struct) => r#struct.root(),
            Self::Function(function) => function.root(),
            Self::Cons(cons) => cons.root(),
            Self::HashMap(hm) => hm.root(),
            Self::Symbol(symbol) => symbol.root(),
            Self::String(string) => string.root(),
            _ => (),
        }
    }

    unsafe fn unroot(&self) {
        match self {
            Self::Struct(r#struct) => r#struct.unroot(),
            Self::Function(function) => function.unroot(),
            Self::Cons(cons) => cons.unroot(),
            Self::HashMap(hm) => hm.unroot(),
            Self::Symbol(symbol) => symbol.unroot(),
            Self::String(string) => string.unroot(),
            _ => (),
        }
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>) -> bool) {
        match self {
            Self::Struct(r#struct) => r#struct.trace(tracer),
            Self::Function(function) => function.trace(tracer),
            Self::Cons(cons) => cons.trace(tracer),
            Self::HashMap(hm) => hm.trace(tracer),
            Self::Symbol(symbol) => symbol.trace(tracer),
            Self::String(string) => string.trace(tracer),
            _ => (),
        }
    }
}

unsafe impl<D> Trace for Struct<D> {
    unsafe fn root(&self) {
        self.fields.root();
    }

    unsafe fn unroot(&self) {
        self.fields.unroot()
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>) -> bool) {
        self.fields.trace(tracer);
    }
}

unsafe impl<D> Trace for Cons<D> {
    unsafe fn root(&self) {
        self.0.root();
        self.1.root();
    }

    unsafe fn unroot(&self) {
        self.0.unroot();
        self.1.unroot();
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<gc::Inner<dyn Trace>>) -> bool) {
        self.0.trace(tracer);
        self.1.trace(tracer);
    }
}

impl<D: Clone> Object<D> {
    #[allow(clippy::result_unit_err)]
    pub fn print(&self, buffer: &mut String) -> Result<(), ()> {
        match self {
            Self::Box(object) => object.borrow().print(buffer)?,
            Self::Cons(cons) => cons.borrow().print(buffer)?,
            Self::Symbol(symbol) => write!(buffer, "{symbol}").map_err(|_| ())?,
            Self::String(string) => write!(buffer, r#""{string}""#).map_err(|_| ())?,
            Self::Char(char) => write!(buffer, r#"?{char}"#).map_err(|_| ())?,
            Self::Int(int) => write!(buffer, "{int}").map_err(|_| ())?,
            // this needs to be printed with the debug formatter or else "even" floats
            // get printed without a decimal point
            Self::Float(float) => write!(buffer, "{float:?}").map_err(|_| ())?,
            Self::Bool(true) => write!(buffer, "true").map_err(|_| ())?,
            Self::Bool(false) => write!(buffer, "false").map_err(|_| ())?,
            Self::Nil => write!(buffer, "nil").map_err(|_| ())?,
            _ => return Err(()),
        }

        Ok(())
    }
}

impl<D: Clone> Cons<D> {
    #[allow(clippy::result_unit_err)]
    pub fn print(&self, buffer: &mut String) -> Result<(), ()> {
        write!(buffer, "(").map_err(|_| ())?;

        for (i, e) in self.iter_cars().enumerate() {
            e.print(buffer)?;
            if i < self.iter_cars().count() - 1 {
                write!(buffer, " ").map_err(|_| ())?;
            }
        }

        write!(buffer, ")").map_err(|_| ())?;

        Ok(())
    }
}

fn pretty_print<D: Clone>(cons: &Cons<D>, depth: usize, f: &mut fmt::Formatter) -> fmt::Result {
    let indent = " ".repeat(depth);
    if !cons.1.is_nil() && !cons.1.is_cons() {
        write!(f, "{indent}({} . {})", cons.0, cons.1)?;
    } else {
        write!(f, "{indent}(")?;
        for (i, expr) in cons.iter_cars().enumerate() {
            write!(f, "{indent}{expr}")?;
            if i < cons.iter_cars().count() - 1 {
                write!(f, "{indent} ")?;
            }
        }
        write!(f, ")")?;
    }
    Ok(())
}
