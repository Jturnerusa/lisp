use std::collections::HashMap;
use std::rc::Rc;
use unwrap_enum::{EnumAs, EnumIs};

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Object {
    Function(Rc<Object>, Vec<String>, HashMap<String, Rc<Object>>),
    Cons(Rc<Object>, Rc<Object>),
    Symbol(String),
    String(String),
    Int(i64),
    True,
    Nil,
}

pub struct Iter(Option<(Rc<Object>, Rc<Object>)>);

impl Object {
    pub fn cons(a: Rc<Object>, b: Rc<Object>) -> Rc<Object> {
        Rc::new(Self::Cons(a, b))
    }

    pub fn car(&self) -> Option<Rc<Object>> {
        match self {
            Self::Cons(car, _) => Some(Rc::clone(car)),
            _ => None,
        }
    }

    pub fn cdr(&self) -> Option<Rc<Object>> {
        match self {
            Self::Cons(car, _) => Some(Rc::clone(car)),
            _ => None,
        }
    }

    pub fn iter(&self) -> Option<Iter> {
        match self {
            Object::Cons(car, cdr) => Some(Iter(Some((Rc::clone(car), Rc::clone(cdr))))),
            _ => None,
        }
    }

    pub fn iter_cars(&self) -> Option<impl Iterator<Item = Rc<Object>>> {
        Some(self.iter()?.map(|(car, _)| car))
    }
}

impl Iterator for Iter {
    type Item = (Rc<Object>, Rc<Object>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((car, cdr)) = &self.0.clone() {
            self.0 = match &**cdr {
                Object::Cons(a, b) => Some((Rc::clone(a), Rc::clone(b))),
                _ => None,
            };
            Some((Rc::clone(car), Rc::clone(cdr)))
        } else {
            None
        }
    }
}
