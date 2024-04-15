mod parse;

use parse::Parser;
use unwrap_enum::{EnumAs, EnumIs};

#[derive(Clone, PartialEq, Eq, Debug, EnumAs, EnumIs)]
pub enum Value {
    Cons(Box<Value>, Box<Value>),
    Symbol(String),
    String(String),
    Int(u64),
    Nil,
}

#[derive(Clone, Debug)]
pub enum Error {
    UnbalancedParens,
    ParseError(String),
}

pub struct Iter<'a>(Option<&'a Value>);

pub fn read(input: &str) -> Option<Result<Value, Error>> {
    let mut parser = Parser::new(input);
    match parser.next()? {
        Ok(parse::Node::LeftParen) => Some(parse_cons(&mut parser)),
        Ok(parse::Node::RightParen) => Some(Err(Error::UnbalancedParens)),
        Ok(parse::Node::String(string)) => Some(Ok(Value::String(string.to_string()))),
        Ok(parse::Node::Symbol(symbol)) => Some(Ok(Value::Symbol(symbol.to_string()))),
        Ok(parse::Node::Int(i)) => Some(Ok(Value::Int(i.parse().unwrap()))),
        Err(e) => Some(Err(Error::ParseError(e.to_string()))),
    }
}

fn parse_cons<'a>(
    nodes: &mut impl Iterator<Item = <Parser<'a> as Iterator>::Item>,
) -> Result<Value, Error> {
    Ok(match nodes.next() {
        Some(Ok(parse::Node::LeftParen)) => {
            Value::Cons(Box::new(parse_cons(nodes)?), Box::new(parse_cons(nodes)?))
        }
        Some(Ok(parse::Node::RightParen)) => Value::Nil,
        Some(Ok(parse::Node::String(string))) => Value::Cons(
            Box::new(Value::String(string.to_string())),
            Box::new(parse_cons(nodes)?),
        ),
        Some(Ok(parse::Node::Symbol(symbol))) => Value::Cons(
            Box::new(Value::Symbol(symbol.to_string())),
            Box::new(parse_cons(nodes)?),
        ),
        Some(Ok(parse::Node::Int(i))) => Value::Cons(
            Box::new(Value::Int(i.parse().unwrap())),
            Box::new(parse_cons(nodes)?),
        ),
        None => return Err(Error::UnbalancedParens),
        Some(Err(e)) => return Err(Error::ParseError(e.to_string())),
    })
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Value;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(value) = self.0 {
            let (_, cdr) = value.as_cons().unwrap();
            if matches!(**cdr, Value::Cons(..)) {
                self.0 = Some(cdr);
            } else {
                self.0 = None;
            }
            self.0
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! boxed {
        ($e:expr) => {
            Box::new($e)
        };
    }

    #[test]
    fn test_simple() {
        use Value::{Cons, Int, Nil, String, Symbol};
        let expected = Cons(
            boxed!(Symbol("hello".to_string())),
            boxed!(Value::Cons(
                boxed!(String("world".to_string())),
                boxed!(Cons(boxed!(Int(1)), boxed!(Nil))),
            )),
        );
        let value = read(r#"(hello "world" 1)"#).unwrap().unwrap();
        assert_eq!(expected, value);
    }

    #[test]
    fn test_nested() {
        use Value::{Cons, Int, Nil, Symbol};
        let a = Cons(
            boxed!(Symbol("a".to_string())),
            boxed!(Cons(boxed!(Int(1)), boxed!(Nil))),
        );
        let b = Cons(
            boxed!(Symbol("b".to_string())),
            boxed!(Cons(boxed!(Int(2)), boxed!(Nil))),
        );
        let bindings_list = Cons(boxed!(a), boxed!(Cons(boxed!(b), boxed!(Nil))));
        let expected = Cons(
            boxed!(Symbol("let".to_string())),
            boxed!(Cons(boxed!(bindings_list), boxed!(Nil))),
        );
        let value = read(r#"(let ((a 1) (b 2)))"#).unwrap().unwrap();
        assert_eq!(expected, value);
    }
}
