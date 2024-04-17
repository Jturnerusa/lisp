#![allow(dead_code)]

pub mod error;
pub mod object;
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

    pub fn eval(&mut self, object: Rc<Object>) -> Result<Rc<Object>, Error> {
        match &*object {
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "lambda") => {
                self.lambda(object)
            }
            _ => todo!(),
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
}
