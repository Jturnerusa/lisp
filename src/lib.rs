#![allow(dead_code)]

pub mod error;
pub mod object;
pub mod prologue;
pub mod reader;

use std::collections::HashMap;
use std::rc::Rc;

pub use error::{Error, Type};
pub use object::Object;
pub use reader::Reader;

pub struct Interpreter {
    globals: HashMap<String, Rc<Object>>,
    locals: Vec<HashMap<String, Rc<Object>>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            globals: HashMap::new(),
            locals: Vec::new(),
        }
    }

    pub fn load_native_function(
        &mut self,
        name: &str,
        f: Box<object::NativeFunction>,
    ) -> Rc<Object> {
        let object = Rc::new(Object::NativeFunction(f));
        self.globals.insert(name.to_string(), Rc::clone(&object));
        object
    }

    pub fn eval(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        match &*object {
            Object::Cons(car, cdr) => {
                let fun = self.eval(Rc::clone(car))?;
                match &*fun {
                    Object::Symbol(symbol) if symbol == "lambda" => self.lambda(object),
                    Object::Symbol(symbol) if symbol == "def" => self.def(object),
                    Object::Symbol(symbol) if symbol == "set" => self.set(object),
                    Object::Symbol(symbol) if symbol == "if" => self.branch(object),
                    Object::Symbol(symbol) if symbol == "loop" => self.while_loop(object),
                    Object::Symbol(symbol) if symbol == "defmacro" => self.defmacro(object),
                    Object::Symbol(symbol) if symbol == "quote" => self.quote(object),
                    Object::Symbol(symbol) if symbol == "progn" => self.progn(object),
                    Object::NativeFunction(f) => {
                        let args = cdr
                            .iter_cars()
                            .ok_or(Error::Parameters)?
                            .map(|expr| self.eval(expr))
                            .collect::<Result<Vec<_>, Error>>()?
                            .into_iter();
                        f(Box::new(args))
                    }
                    Object::Function(body, parameters, captures) => {
                        let args = cdr
                            .iter_cars()
                            .ok_or(Error::Parameters)?
                            .map(|expr| self.eval(expr))
                            .collect::<Result<Vec<_>, Error>>()?
                            .into_iter();
                        self.fncall(
                            Rc::clone(body),
                            parameters.iter().cloned(),
                            captures
                                .iter()
                                .map(|(var, val)| (var.clone(), Rc::clone(val))),
                            args,
                        )
                    }
                    Object::Macro(body, parameters) => {
                        let args = cdr
                            .iter_cars()
                            .ok_or(Error::Parameters)?
                            .collect::<Vec<_>>()
                            .into_iter();
                        let expanded =
                            self.expand_macro(Rc::clone(body), parameters.iter().cloned(), args)?;
                        self.eval(expanded)
                    }
                    object => Err(Error::NotFunction(format!("{}", object))),
                }
            }
            Object::Symbol(symbol)
                if matches!(
                    symbol.as_str(),
                    "lambda" | "def" | "set" | "if" | "loop" | "defmacro" | "quote" | "progn"
                ) =>
            {
                Ok(object)
            }
            Object::Symbol(symbol) if symbol == "nil" => Ok(Rc::new(Object::Nil)),
            Object::Symbol(symbol) if symbol == "t" => Ok(Rc::new(Object::True)),
            Object::Symbol(symbol) if self.get_variable(symbol).is_none() => {
                Err(Error::NotFound(symbol.clone()))
            }
            Object::Symbol(symbol) => Ok(self.get_variable(symbol).unwrap()),
            _ => Ok(object),
        }
    }

    fn progn(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        object
            .iter_cars()
            .and_then(|iter| iter.map(|expr| self.eval(expr)).last())
            .ok_or(Error::Parameters)?
    }

    fn quote(&self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        let expr = object
            .iter_cars()
            .and_then(|mut iter| iter.nth(1))
            .ok_or(Error::Parameters)?;
        Ok(expr)
    }

    fn expand_macro(
        &mut self,
        body: Rc<Object>,
        parameters: impl Iterator<Item = String>,
        args: impl Iterator<Item = Rc<Object>>,
    ) -> Result<Rc<Object>, Error> {
        let enviromemt = parameters.zip(args).collect::<HashMap<_, _>>();
        self.locals.push(enviromemt);
        let expanded = self.eval(body);
        self.locals.pop().unwrap();
        expanded
    }

    fn defmacro(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        let macro_name = object
            .iter_cars()
            .and_then(|mut iter| iter.nth(1))
            .and_then(|object| object.as_symbol().cloned())
            .ok_or(Error::Parameters)?;

        let parameter_list = object
            .iter_cars()
            .and_then(|mut iter| iter.nth(2))
            .ok_or(Error::Parameters)?;

        let parameters = parameter_list
            .iter_cars()
            .and_then(|iter| {
                iter.map(|object| object.as_symbol().cloned())
                    .collect::<Option<Vec<_>>>()
            })
            .ok_or(Error::Parameters)?;

        let body = object
            .iter_cars()
            .and_then(|mut iter| iter.nth(3))
            .ok_or(Error::Parameters)?;

        let mac = Object::Macro(body, parameters);

        self.globals.insert(macro_name, Rc::new(mac));

        Ok(Rc::new(Object::Nil))
    }

    fn while_loop(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        let predicate = object
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(1)
            .ok_or(Error::Parameters)?;

        let body = object
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(2)
            .ok_or(Error::Parameters)?;

        while let Object::True = *self.eval(Rc::clone(&predicate))? {
            self.eval(Rc::clone(&body))?;
        }

        Ok(Rc::new(Object::Nil))
    }

    fn branch(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        let predicate = object
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(1)
            .ok_or(Error::Parameters)?;

        let then = object
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(2)
            .ok_or(Error::Parameters)?;

        let els = object
            .iter_cars()
            .ok_or(Error::Parameters)?
            .nth(3)
            .ok_or(Error::Parameters)?;

        if let Object::True = *self.eval(predicate)? {
            self.eval(then)
        } else {
            self.eval(els)
        }
    }

    fn fncall(
        &mut self,
        body: Rc<Object>,
        parameters: impl Iterator<Item = String>,
        captures: impl Iterator<Item = (String, Rc<Object>)>,
        args: impl Iterator<Item = Rc<Object>>,
    ) -> Result<Rc<Object>, Error> {
        let environment = captures
            .chain(parameters.zip(args))
            .collect::<HashMap<_, _>>();
        self.locals.push(environment);
        let ret = self.eval(body);
        self.locals.pop();
        ret
    }

    fn lambda(&self, cons: Rc<Object>) -> Result<Rc<Object>, Error> {
        let parameter_list = cons
            .iter()
            .ok_or(Error::Type(Type::Cons, Type::from(&*cons)))?
            .map(|(car, _)| car)
            .nth(1)
            .ok_or(Error::Parameters)?;

        let body = cons
            .iter()
            .ok_or(Error::Type(Type::Cons, Type::from(&*cons)))?
            .map(|(car, _)| car)
            .nth(2)
            .ok_or(Error::Parameters)?;

        let parameters = if let Object::Nil = &*parameter_list {
            Vec::new()
        } else {
            parameter_list
                .iter_cars()
                .ok_or(Error::Parameters)?
                .map(|param| match &*param {
                    Object::Symbol(symbol) => Ok(symbol.clone()),
                    object => Err(Error::Type(Type::Symbol, Type::from(object))),
                })
                .collect::<Result<Vec<_>, Error>>()?
        };

        let captures = self
            .locals
            .iter()
            .next_back()
            .cloned()
            .unwrap_or_else(HashMap::new);

        Ok(Rc::new(Object::Function(body, parameters, captures)))
    }

    fn set(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        let variable_name = match &*object
            .iter_cars()
            .ok_or(Error::Type(Type::Cons, Type::from(&*object)))?
            .nth(1)
            .ok_or(Error::Parameters)?
        {
            Object::Symbol(symbol) => symbol.clone(),
            object => return Err(Error::Type(Type::Symbol, Type::from(object))),
        };

        if self.get_variable(variable_name.as_str()).is_none() {
            Err(Error::NotFound(variable_name.clone()))
        } else {
            self.def(object)
        }
    }

    fn def(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        let variable_name = match &*object
            .iter_cars()
            .ok_or(Error::Type(Type::Cons, Type::from(&*object)))?
            .nth(1)
            .ok_or(Error::Parameters)?
        {
            Object::Symbol(symbol) => symbol.clone(),
            object => return Err(Error::Type(Type::Symbol, Type::from(object))),
        };

        let expr = object
            .iter_cars()
            .ok_or(Error::Type(Type::Cons, Type::from(&*object)))?
            .nth(2)
            .ok_or(Error::Parameters)?;

        let variable_value = self.eval(expr)?;

        self.globals.insert(variable_name, variable_value);

        Ok(Rc::new(Object::Nil))
    }

    fn get_variable(&self, name: &str) -> Option<Rc<Object>> {
        if let Some(Some(var)) = self.locals.iter().next_back().map(|env| env.get(name)) {
            Some(Rc::clone(var))
        } else {
            self.globals.get(name).cloned()
        }
    }
}
