#![allow(dead_code)]

pub mod reader;

use std::collections::HashMap;

use slotmap::SlotMap;
use unwrap_enum::{EnumAs, EnumIs};

type ObjectRef = slotmap::Key;

#[derive(Clone, Copy, Debug)]
pub enum Error {
    TypeError,
    InvalidParams,
    NotFound,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Object {
    Function {
        body: ObjectRef,
        captures: HashMap<String, ObjectRef>,
        parameters: Vec<String>,
    },
    Cons(ObjectRef, ObjectRef),
    String(String),
    Symbol(String),
    Int(u64),
    Nil,
}

#[derive(Clone, Copy)]
pub struct Iter<'a> {
    objects: &'a SlotMap<Object>,
    cursor: Option<ObjectRef>,
}

#[derive(Clone, Copy)]
pub struct IterCars<'a>(Iter<'a>);

#[derive(Clone)]
pub struct Interpreter {
    objects: SlotMap<Object>,
    globals: HashMap<String, ObjectRef>,
    locals: Vec<HashMap<String, ObjectRef>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            objects: SlotMap::new(),
            globals: HashMap::new(),
            locals: Vec::new(),
        }
    }

    pub fn get_object(&self, objref: ObjectRef) -> Option<&Object> {
        self.objects.get(objref)
    }

    pub fn read(&mut self, value: reader::Value) -> ObjectRef {
        let object = match value {
            reader::Value::Cons(car, cdr) => Object::Cons(self.read(*car), self.read(*cdr)),
            reader::Value::Symbol(symbol) => Object::Symbol(symbol),
            reader::Value::String(string) => Object::String(string),
            reader::Value::Int(i) => Object::Int(i),
            reader::Value::Nil => Object::Nil,
        };
        self.objects.insert(object)
    }

    pub fn eval(&mut self, objref: ObjectRef) -> Result<ObjectRef, Error> {
        match &self.objects[objref] {
            Object::Cons(car, rest) => {
                // not sure how to make the pattern copy the keys?
                let (car, rest) = (*car, *rest);
                // handle special forms
                #[allow(clippy::single_match)]
                match self.objects[car].as_symbol().map(|s| s.as_str()) {
                    Some("lambda") => return self.lambda(objref),
                    _ => (),
                }
                // regular function calls eval right to left, with the
                // first expr being the function that is called
                let fun = self.eval(car)?;
                &self.objects[fun];
                let args = self
                    .iter_cars(rest)?
                    .collect::<Vec<ObjectRef>>()
                    .into_iter()
                    .map(|i| self.eval(i))
                    .collect::<Result<Vec<_>, Error>>()?;
                self.fncall(fun, args.into_iter())
            }
            Object::Symbol(symbol) if matches!(symbol.as_str(), "+" | "lambda") => Ok(objref),
            Object::Symbol(symbol) => {
                Ok(self.get_variable(symbol.as_str()).ok_or(Error::NotFound)?)
            }
            _ => Ok(objref),
        }
    }

    fn fncall<I: Iterator<Item = ObjectRef> + Clone>(
        &mut self,
        fun: ObjectRef,
        args: I,
    ) -> Result<ObjectRef, Error> {
        // built ins get called first
        #[allow(clippy::single_match)]
        match self.objects[fun].as_symbol().map(|s| s.as_str()) {
            Some("+") => return self.add(args),
            _ => (),
        }
        // get the actual function object from a lambda or a function
        // bound to a symbol
        let (body, captures, parameters) = match &self.objects[fun] {
            Object::Function {
                body,
                captures,
                parameters,
            } => (body, captures, parameters),
            Object::Symbol(symbol) => {
                let var = self.get_variable(symbol.as_str()).ok_or(Error::NotFound)?;
                if let Some((body, captures, parameters)) = self.objects[var].as_function() {
                    (body, captures, parameters)
                } else {
                    return Err(Error::TypeError);
                }
            }
            _ => return Err(Error::TypeError),
        };

        let mut locals = HashMap::new();

        for (key, val) in captures {
            locals.insert(key.clone(), *val);
        }

        for (arg, parameter) in args.zip(parameters.iter()) {
            locals.insert(parameter.clone(), arg);
        }

        self.locals.push(locals);

        let ret = self.eval(*body);

        self.locals.pop();

        ret
    }

    fn lambda(&mut self, cons: ObjectRef) -> Result<ObjectRef, Error> {
        let parameter_list = self.iter_cars(cons)?.nth(1).ok_or(Error::InvalidParams)?;
        let mut parameters: Vec<String> = Vec::new();
        for param_ref in self.iter_cars(parameter_list)? {
            let parameter = match &self.objects[param_ref] {
                Object::Symbol(symbol) => symbol.clone(),
                _ => return Err(Error::TypeError),
            };
            parameters.push(parameter);
        }
        let body = self.iter_cars(cons)?.nth(2).ok_or(Error::InvalidParams)?;
        let lambda = Object::Function {
            body,
            captures: self
                .locals
                .iter()
                .next_back()
                .cloned()
                .unwrap_or_else(HashMap::new),
            parameters,
        };
        Ok(self.objects.insert(lambda))
    }

    fn add<I: Iterator<Item = ObjectRef> + Clone>(&mut self, args: I) -> Result<ObjectRef, Error> {
        let mut acc = 0;
        for arg in args {
            match &self.objects[arg] {
                Object::Int(i) => acc += i,
                _ => return Err(Error::TypeError),
            }
        }
        Ok(self.objects.insert(Object::Int(acc)))
    }

    fn get_variable(&self, name: &str) -> Option<ObjectRef> {
        if let Some(Some(v)) = self
            .locals
            .iter()
            .next_back()
            .map(|locals| locals.get(name))
        {
            Some(*v)
        } else {
            self.globals.get(name).copied()
        }
    }

    fn iter_cons(&self, cons: ObjectRef) -> Result<Iter, Error> {
        if self.objects[cons].is_cons() {
            Ok(Iter {
                objects: &self.objects,
                cursor: Some(cons),
            })
        } else {
            Err(Error::TypeError)
        }
    }

    fn iter_cars(&self, cons: ObjectRef) -> Result<IterCars, Error> {
        Ok(IterCars(self.iter_cons(cons)?))
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = ObjectRef;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(cursor) = self.cursor {
            match self.objects[cursor] {
                Object::Cons(_, cdr) => {
                    if self.objects[cdr].is_cons() {
                        self.cursor = Some(cdr);
                    } else {
                        self.cursor = None;
                    }
                    Some(cursor)
                }
                _ => unreachable!(),
            }
        } else {
            None
        }
    }
}

impl<'a> Iterator for IterCars<'a> {
    type Item = ObjectRef;
    fn next(&mut self) -> Option<Self::Item> {
        match self.0.next() {
            Some(objref) => {
                let (car, _) = self.0.objects[objref].as_cons().unwrap();
                Some(*car)
            }
            None => None,
        }
    }
}
