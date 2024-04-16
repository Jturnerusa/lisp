#![allow(dead_code)]

pub mod reader;

use std::collections::HashMap;

use slotmap::SlotMap;
use unwrap_enum::{EnumAs, EnumIs};

type ObjectRef = slotmap::Key;

const BUILTINS: &[&str] = &[
    "lambda", "car", "cdr", "cons", "print", "if", "nil", "t", "panic", "def", "set", "=", "+",
    "-", "*", "/",
];

#[derive(Clone, Copy, Debug)]
pub enum Error {
    TypeError,
    InvalidParams,
    NotFound,
}

#[derive(Clone, Debug, PartialEq, Eq, EnumAs, EnumIs)]
pub enum Object {
    Function {
        body: ObjectRef,
        captures: HashMap<String, ObjectRef>,
        parameters: Vec<String>,
    },
    Cons(ObjectRef, ObjectRef),
    String(String),
    Symbol(String),
    Int(i64),
    True,
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
                    Some("if") => return self.branch(objref),
                    Some("def") => return self.def(objref),
                    Some("set") => return self.set(objref),
                    _ => (),
                }
                // regular function calls eval right to left, with the
                // first expr being the function that is called
                let fun = self.eval(car)?;
                let args = self
                    .iter_cars(rest)?
                    .collect::<Vec<ObjectRef>>()
                    .into_iter()
                    .map(|i| self.eval(i))
                    .collect::<Result<Vec<_>, Error>>()?;
                self.fncall(fun, args.into_iter())
            }
            Object::Symbol(symbol) if symbol.as_str() == "t" => {
                Ok(self.objects.insert(Object::True))
            }
            Object::Symbol(symbol) if symbol.as_str() == "nil" => {
                Ok(self.objects.insert(Object::Nil))
            }
            Object::Symbol(symbol)
                if BUILTINS.iter().any(|builtin| *builtin == symbol.as_str()) =>
            {
                Ok(objref)
            }
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
            Some("car") => return self.car(args),
            Some("cdr") => return self.cdr(args),
            Some("cons") => return self.cons(args),
            Some("print") => return self.print(args),
            Some("panic") => return self.panic(args),
            Some("=") => return self.equal(args),
            Some("+") => return self.add(args),
            Some("-") => return self.sub(args),
            Some("*") => return self.mul(args),
            Some("/") => return self.div(args),
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

    fn set(&mut self, cons: ObjectRef) -> Result<ObjectRef, Error> {
        if self.iter_cars(cons)?.count() != 3 {
            return Err(Error::InvalidParams);
        }

        let binding_ref = self.iter_cars(cons)?.nth(1).unwrap();
        let binding = match &self.objects[binding_ref] {
            Object::Symbol(symbol) => symbol.clone(),
            _ => return Err(Error::InvalidParams),
        };

        if self.get_variable(binding.as_str()).is_none() {
            Err(Error::NotFound)
        } else {
            self.def(cons)
        }
    }

    fn def(&mut self, cons: ObjectRef) -> Result<ObjectRef, Error> {
        if self.iter_cars(cons)?.count() != 3 {
            return Err(Error::InvalidParams);
        }
        let binding_ref = self.iter_cars(cons)?.nth(1).unwrap();
        let binding = match &self.objects[binding_ref] {
            Object::Symbol(symbol) => symbol.clone(),
            _ => return Err(Error::InvalidParams),
        };
        let expr = self.iter_cars(cons)?.nth(2).unwrap();
        let val = self.eval(expr)?;
        self.globals.insert(binding, val);
        Ok(self.objects.insert(Object::Nil))
    }

    fn branch(&mut self, cons: ObjectRef) -> Result<ObjectRef, Error> {
        if self.iter_cars(cons)?.count() != 4 {
            return Err(Error::InvalidParams);
        }
        let predicate = self.iter_cars(cons)?.nth(1).unwrap();
        let then = self.iter_cars(cons)?.nth(2).unwrap();
        let els = self.iter_cars(cons)?.nth(3).unwrap();
        let result = self.eval(predicate)?;
        if self.objects[result].is_true() {
            self.eval(then)
        } else {
            self.eval(els)
        }
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
        let result = args
            .map(|arg| &self.objects[arg])
            .map(|obj| match obj {
                Object::Int(i) => Ok(*i),
                _ => Err(Error::TypeError),
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .reduce(|acc, e| acc + e)
            .ok_or(Error::InvalidParams)?;
        Ok(self.objects.insert(Object::Int(result)))
    }

    fn sub<I: Iterator<Item = ObjectRef> + Clone>(&mut self, args: I) -> Result<ObjectRef, Error> {
        let result = args
            .map(|arg| &self.objects[arg])
            .map(|obj| match obj {
                Object::Int(i) => Ok(*i),
                _ => Err(Error::TypeError),
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .reduce(|acc, e| acc - e)
            .ok_or(Error::InvalidParams)?;
        Ok(self.objects.insert(Object::Int(result)))
    }

    fn mul<I: Iterator<Item = ObjectRef> + Clone>(&mut self, args: I) -> Result<ObjectRef, Error> {
        let result = args
            .map(|arg| &self.objects[arg])
            .map(|obj| match obj {
                Object::Int(i) => Ok(*i),
                _ => Err(Error::TypeError),
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .reduce(|acc, e| acc * e)
            .ok_or(Error::InvalidParams)?;
        Ok(self.objects.insert(Object::Int(result)))
    }

    fn div<I: Iterator<Item = ObjectRef> + Clone>(&mut self, args: I) -> Result<ObjectRef, Error> {
        let result = args
            .map(|arg| &self.objects[arg])
            .map(|obj| match obj {
                Object::Int(i) => Ok(*i),
                _ => Err(Error::TypeError),
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .reduce(|acc, e| acc / e)
            .ok_or(Error::InvalidParams)?;
        Ok(self.objects.insert(Object::Int(result)))
    }

    fn car<I: Iterator<Item = ObjectRef> + Clone>(
        &mut self,
        mut args: I,
    ) -> Result<ObjectRef, Error> {
        if args.clone().count() != 1 {
            return Err(Error::InvalidParams);
        }
        let cons = args.next().unwrap();
        let cdr = match self.objects[cons] {
            Object::Cons(car, _) => car,
            _ => return Err(Error::TypeError),
        };
        Ok(cdr)
    }

    fn cdr<I: Iterator<Item = ObjectRef> + Clone>(
        &mut self,
        mut args: I,
    ) -> Result<ObjectRef, Error> {
        if args.clone().count() != 1 {
            return Err(Error::InvalidParams);
        }
        let cons = args.next().unwrap();
        let cdr = match self.objects[cons] {
            Object::Cons(_, cdr) => cdr,
            _ => return Err(Error::TypeError),
        };
        Ok(cdr)
    }

    fn cons<I: Iterator<Item = ObjectRef> + Clone>(
        &mut self,
        mut args: I,
    ) -> Result<ObjectRef, Error> {
        if args.clone().count() != 2 {
            return Err(Error::InvalidParams);
        }
        let car = args.next().unwrap();
        let cdr = args.next().unwrap();
        Ok(self.objects.insert(Object::Cons(car, cdr)))
    }

    fn print<I: Iterator<Item = ObjectRef> + Clone>(
        &mut self,
        args: I,
    ) -> Result<ObjectRef, Error> {
        for arg in args {
            let object = &self.objects[arg];
            println!("{:?}", object);
        }
        Ok(self.objects.insert(Object::Nil))
    }

    fn equal<I: Iterator<Item = ObjectRef> + Clone>(
        &mut self,
        mut args: I,
    ) -> Result<ObjectRef, Error> {
        let first = args.next().ok_or(Error::InvalidParams)?;
        for arg in args {
            if match (&self.objects[first], &self.objects[arg]) {
                (Object::Cons(a, b), Object::Cons(c, d)) => {
                    (&self.objects[*a], &self.objects[*b]) != (&self.objects[*c], &self.objects[*d])
                }
                (a, b) => a != b,
            } {
                return Ok(self.objects.insert(Object::Nil));
            }
        }
        Ok(self.objects.insert(Object::True))
    }

    fn panic<I: Iterator<Item = ObjectRef> + Clone>(
        &mut self,
        mut args: I,
    ) -> Result<ObjectRef, Error> {
        if args.clone().count() != 1 {
            return Err(Error::InvalidParams);
        }
        let message = args.next().unwrap();
        let object = &self.objects[message];

        panic!("lisp interpreter panicked {:?}", object);
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
