#![allow(dead_code)]

pub mod error;
pub mod object;
pub mod prologue;
pub mod reader;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub use error::{Error, Type};
pub use object::Object;
pub use reader::Reader;

type ObjectRef = Rc<RefCell<Object>>;

pub struct Interpreter {
    globals: HashMap<String, ObjectRef>,
    locals: Vec<HashMap<String, ObjectRef>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            globals: HashMap::new(),
            locals: Vec::new(),
        }
    }

    pub fn load_native_function(&mut self, name: &str, f: Rc<object::NativeFunction>) -> ObjectRef {
        let object = Rc::new(RefCell::new(Object::NativeFunction(f)));
        self.globals.insert(name.to_string(), Rc::clone(&object));
        object
    }

    pub fn eval(&mut self, object: ObjectRef) -> Result<ObjectRef, Error> {
        match Rc::unwrap_or_clone(Rc::clone(&object)).into_inner() {
            Object::Cons(car, cdr) => {
                let fun = self.eval(Rc::clone(&car))?;
                match Rc::unwrap_or_clone(fun).into_inner() {
                    Object::Symbol(symbol) if symbol == "lambda" => self.lambda(object),
                    Object::Symbol(symbol) if symbol == "def" => self.def(object),
                    Object::Symbol(symbol) if symbol == "set" => self.set(object),
                    Object::Symbol(symbol) if symbol == "if" => self.branch(object),
                    Object::Symbol(symbol) if symbol == "defmacro" => self.defmacro(object),
                    Object::Symbol(symbol) if symbol == "quote" => self.quote(object),
                    Object::NativeFunction(f) => {
                        let args = cdr
                            .borrow()
                            .iter_cars()
                            .ok_or(Error::Parameters)?
                            .map(|expr| self.eval(expr))
                            .collect::<Result<Vec<_>, Error>>()?
                            .into_iter();
                        f(Box::new(args))
                    }
                    Object::Function(f) => {
                        let args = cdr
                            .borrow()
                            .iter_cars()
                            .ok_or(Error::Parameters)?
                            .map(|expr| self.eval(expr))
                            .collect::<Result<Vec<_>, Error>>()?
                            .into_iter();
                        self.fncall(&f, args)
                    }
                    Object::Macro(mac) => {
                        let args = cdr
                            .borrow()
                            .iter_cars()
                            .ok_or(Error::Parameters)?
                            .collect::<Vec<_>>()
                            .into_iter();
                        let expanded = self.expand_macro(&mac, args)?;
                        self.eval(expanded)
                    }
                    object => Err(Error::NotFunction(format!("{}", object))),
                }
            }
            Object::Symbol(symbol)
                if matches!(
                    symbol.as_str(),
                    "lambda" | "def" | "set" | "if" | "defmacro" | "quote"
                ) =>
            {
                Ok(object)
            }
            Object::Symbol(symbol) if symbol == "nil" => Ok(Rc::new(RefCell::new(Object::Nil))),
            Object::Symbol(symbol) if symbol == "t" => Ok(Rc::new(RefCell::new(Object::True))),
            Object::Symbol(symbol) if self.get_variable(symbol.as_str()).is_none() => {
                Err(Error::NotFound(symbol.clone()))
            }
            Object::Symbol(symbol) => Ok(self.get_variable(symbol.as_str()).unwrap()),
            _ => Ok(object),
        }
    }

    fn quote(&self, object: ObjectRef) -> Result<ObjectRef, Error> {
        let expr = object
            .borrow()
            .iter_cars()
            .and_then(|mut iter| iter.nth(1))
            .ok_or(Error::Parameters)?;
        Ok(expr)
    }

    fn expand_macro(
        &mut self,
        mac: &object::Macro,
        mut args: impl Iterator<Item = ObjectRef>,
    ) -> Result<ObjectRef, Error> {
        let mut enviromemt = mac
            .parameters
            .iter()
            .cloned()
            .zip(args.by_ref())
            .collect::<HashMap<_, _>>();
        let rest: Vec<ObjectRef> = args.collect();
        let rest = crate::prologue::list(Box::new(rest.into_iter()))?;
        enviromemt.insert("&rest".to_string(), rest);
        self.locals.push(enviromemt);
        let expanded = self.eval(Rc::clone(&mac.body));
        self.locals.pop().unwrap();
        expanded
    }

    fn defmacro(&mut self, object: ObjectRef) -> Result<ObjectRef, Error> {
        let macro_name = object
            .borrow()
            .iter_cars()
            .and_then(|mut iter| iter.nth(1))
            .and_then(|object| object.borrow().as_symbol().cloned())
            .ok_or(Error::Parameters)?;

        let parameter_list = object
            .borrow()
            .iter_cars()
            .and_then(|mut iter| iter.nth(2))
            .ok_or(Error::Parameters)?;

        let parameters = parameter_list
            .borrow()
            .iter_cars()
            .and_then(|iter| {
                iter.map(|object| object.borrow().as_symbol().cloned())
                    .collect::<Option<Vec<_>>>()
            })
            .ok_or(Error::Parameters)?;

        let body = object
            .borrow()
            .iter_cars()
            .and_then(|mut iter| iter.nth(3))
            .ok_or(Error::Parameters)?;

        let mac = Object::Macro(object::Macro { body, parameters });

        self.globals.insert(macro_name, Rc::new(RefCell::new(mac)));

        Ok(Rc::new(RefCell::new(Object::Nil)))
    }

    fn branch(&mut self, object: ObjectRef) -> Result<ObjectRef, Error> {
        let predicate = object
            .borrow()
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(1)
            .ok_or(Error::Parameters)?;

        let then = object
            .borrow()
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(2)
            .ok_or(Error::Parameters)?;

        let els = object
            .borrow()
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(3)
            .ok_or(Error::Parameters)?;

        if let Object::True = *self.eval(predicate)?.borrow() {
            self.eval(then)
        } else {
            self.eval(els)
        }
    }

    fn fncall(
        &mut self,
        f: &object::Function,
        args: impl Iterator<Item = ObjectRef>,
    ) -> Result<ObjectRef, Error> {
        let environment = f
            .captures
            .iter()
            .map(|(s, obj)| (s.clone(), Rc::clone(obj)))
            .chain(f.parameters.iter().cloned().zip(args))
            .collect::<HashMap<_, _>>();
        self.locals.push(environment);
        let ret = self.eval(Rc::clone(&f.body));
        self.locals.pop();
        ret
    }

    fn lambda(&self, object: ObjectRef) -> Result<ObjectRef, Error> {
        if object
            .borrow()
            .iter_cars()
            .map(|iter| iter.count())
            .filter(|count| *count == 3)
            .is_none()
        {
            return Err(Error::Lambda("expected 3 expressions".to_string()));
        }

        let parameters = object
            .borrow()
            .iter_cars()
            .unwrap()
            .nth(1)
            .unwrap()
            .borrow()
            .iter_cars()
            .ok_or(Error::Lambda(
                "expected list in parameter position".to_string(),
            ))?
            .map(|object| match &*object.borrow() {
                Object::Symbol(symbol) => Ok(symbol.clone()),
                object => Err(Error::Lambda(format!(
                    "expected symbols in parameter list, found {}",
                    Type::from(object)
                ))),
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let body = object.borrow().iter_cars().unwrap().nth(2).unwrap();

        let captures = self
            .locals
            .iter()
            .next_back()
            .cloned()
            .unwrap_or_else(HashMap::new);

        let lambda = Object::Function(object::Function {
            body,
            parameters,
            captures,
        });

        Ok(Rc::new(RefCell::new(lambda)))
    }

    fn set(&mut self, object: ObjectRef) -> Result<ObjectRef, Error> {
        if object
            .borrow()
            .iter_cars()
            .ok_or(Error::Parameters)?
            .count()
            != 3
        {
            return Err(Error::Parameters);
        }

        let variable_name = object
            .borrow()
            .iter_cars()
            .and_then(|mut iter| iter.nth(1))
            .and_then(|object| object.borrow().as_symbol().cloned())
            .ok_or(Error::Parameters)?;

        let expr = object
            .borrow()
            .iter_cars()
            .and_then(|mut iter| iter.nth(2))
            .ok_or(Error::Parameters)?;

        let val = self.eval(expr)?;

        if let Some(var) = self
            .locals
            .iter_mut()
            .next_back()
            .and_then(|env| env.get_mut(variable_name.as_str()))
        {
            *(*var).borrow_mut() = (*val).clone().into_inner();
        } else if let Some(var) = self.globals.get_mut(variable_name.as_str()) {
            *(*var).borrow_mut() = (*val).clone().into_inner();
        } else {
            return Err(Error::NotFound(variable_name));
        }

        Ok(val)
    }

    fn def(&mut self, object: ObjectRef) -> Result<ObjectRef, Error> {
        let variable_name = match &*object
            .borrow()
            .iter_cars()
            .ok_or(Error::Type(Type::Cons, Type::from(&*object.borrow())))?
            .nth(1)
            .ok_or(Error::Parameters)?
            .borrow()
        {
            Object::Symbol(symbol) => symbol.clone(),
            object => return Err(Error::Type(Type::Symbol, Type::from(object))),
        };

        let expr = object
            .borrow()
            .iter_cars()
            .ok_or(Error::Type(Type::Cons, Type::from(&*object.borrow())))?
            .nth(2)
            .ok_or(Error::Parameters)?;

        let variable_value = self.eval(expr)?;

        self.globals.insert(variable_name, variable_value);

        Ok(Rc::new(RefCell::new(Object::Nil)))
    }

    fn get_variable(&self, name: &str) -> Option<ObjectRef> {
        if let Some(Some(var)) = self.locals.iter().next_back().map(|env| env.get(name)) {
            Some(Rc::clone(var))
        } else {
            self.globals.get(name).cloned()
        }
    }
}
