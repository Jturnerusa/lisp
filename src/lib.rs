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
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "lambda") => {
                self.lambda(object)
            }
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "def") => {
                self.def(object)
            }
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "set") => {
                self.set(object)
            }
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "if") => {
                self.branch(object)
            }
            Object::Cons(car, _) if matches!(&**car, Object::Symbol(s) if s.as_str() == "loop") => {
                self.while_loop(object)
            }
            Object::Cons(car, cdr) => {
                let f = self.eval(Rc::clone(car))?;
                let args = cdr
                    .iter_cars()
                    .ok_or(Error::Parameters)?
                    .map(|c| self.eval(c))
                    .collect::<Result<Vec<_>, Error>>()?;
                self.fncall(f, args.into_iter())
            }
            Object::Symbol(symbol) => self
                .get_variable(symbol.as_str())
                .ok_or(Error::NotFound(symbol.clone())),
            _ => Ok(object),
        }
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

    fn fncall<I: Iterator<Item = Rc<Object>> + 'static>(
        &mut self,
        f: Rc<Object>,
        args: I,
    ) -> Result<Rc<Object>, Error> {
        if let Some(native_function) = f.as_nativefunction() {
            return native_function(Box::new(args));
        }

        let (body, parameters, captures) = match &*f {
            Object::Function(b, p, c) => (Rc::clone(b), p.clone(), c.clone()),
            Object::Symbol(symbol) => match *self
                .get_variable(symbol.as_str())
                .ok_or(Error::NotFound(symbol.clone()))?
            {
                Object::Function(ref b, ref p, ref c) => (Rc::clone(b), p.clone(), c.clone()),
                ref object => return Err(Error::Type(Type::Function, Type::from(object))),
            },
            object => return Err(Error::Type(Type::Function, Type::from(object))),
        };

        let mut environment = HashMap::new();

        environment.extend(captures);

        for (parameter, arg) in parameters.iter().zip(args) {
            environment.insert(parameter.clone(), arg);
        }

        self.locals.push(environment);

        let ret = self.eval(body);

        self.locals.pop().unwrap();

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
