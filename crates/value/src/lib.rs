#![allow(dead_code)]

use unwrap_enum::{EnumAs, EnumIs};

// A unified lisp value representation.
#[derive(Clone, PartialEq, Eq, Debug, EnumAs, EnumIs)]
pub enum Value {
    Cons(Box<Cons>),
    Symbol(String),
    String(String),
    Int(i64),
    Nil,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Cons(pub Value, pub Value);

pub struct Iter<'a>(Option<&'a Cons>);

pub struct Cars<'a>(Iter<'a>);

impl Cons {
    pub fn iter(&self) -> Iter {
        Iter(Some(self))
    }

    pub fn iter_cars(&self) -> Cars {
        Cars(self.iter())
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Cons;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(current) = self.0 {
            self.0 = match &current.1 {
                Value::Cons(cons) => Some(cons),
                _ => None,
            };
            Some(current)
        } else {
            None
        }
    }
}

impl<'a> Iterator for Cars<'a> {
    type Item = &'a Value;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|cons| &cons.0)
    }
}

impl<'a> IntoIterator for &'a Cons {
    type Item = &'a Cons;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
