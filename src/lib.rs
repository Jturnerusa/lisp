#![allow(dead_code)]

pub mod error;
pub mod object;
pub mod reader;

use std::collections::HashMap;
use std::rc::Rc;

pub use error::{Error, Type};
pub use object::Object;
pub use reader::Reader;

const BUILTINS: &[&str] = &["lambda"];

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

    pub fn eval(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        match &*object {
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "lambda") => {
                self.lambda(object)
            }
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "def") => {
                self.def(object)
            }
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "set") => {
                self.set(object)
            }
            Object::Symbol(symbol)
                if !BUILTINS.iter().any(|builtin| *builtin == symbol.as_str()) =>
            {
                self.get_variable(symbol.as_str())
                    .ok_or(Error::NotFound(symbol.clone()))
            }
            _ => Ok(object),
        }
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

        let parameters: Vec<String> = parameter_list
            .iter()
            .ok_or(Error::Parameters)?
            .map(|(car, _)| match &*car {
                Object::Symbol(symbol) => Ok(symbol.clone()),
                _ => Err(Error::Parameters),
            })
            .collect::<Result<Vec<_>, Error>>()?;

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
        std::iter::once(&self.globals)
            .chain(self.locals.iter())
            .next_back()
            .and_then(|env| env.get(name))
            .cloned()
    }
}
