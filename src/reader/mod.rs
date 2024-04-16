mod parse;

use parse::Parser;
use unwrap_enum::{EnumAs, EnumIs};

#[derive(Clone, PartialEq, Eq, Debug, EnumAs, EnumIs)]
pub enum Value {
    Cons(Box<Value>, Box<Value>),
    Symbol(String),
    String(String),
    Int(i64),
    Nil,
}

#[derive(Clone, Debug)]
pub enum Error {
    UnbalancedParens,
    ParseError(String),
}

pub struct Reader<'a> {
    parser: Parser<'a>,
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

impl<'a> Reader<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            parser: Parser::new(input),
        }
    }

    fn read(&mut self) -> Option<Result<Value, Error>> {
        match self.parser.next()? {
            Ok(parse::Node::LeftParen) => Some(parse_cons(&mut self.parser)),
            Ok(parse::Node::RightParen) => Some(Err(Error::UnbalancedParens)),
            Ok(parse::Node::String(string)) => Some(Ok(Value::String(string.to_string()))),
            Ok(parse::Node::Symbol(symbol)) => Some(Ok(Value::Symbol(symbol.to_string()))),
            Ok(parse::Node::Int(i)) => Some(Ok(Value::Int(i.parse().unwrap()))),
            Err(e) => Some(Err(Error::ParseError(e.to_string()))),
        }
    }
}

impl<'a> Iterator for Reader<'a> {
    type Item = Result<Value, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        self.read()
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
        let value = Reader::new(r#"(hello "world" 1)"#).next().unwrap().unwrap();
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
        let value = Reader::new(r#"(let ((a 1) (b 2)))"#)
            .next()
            .unwrap()
            .unwrap();
        assert_eq!(expected, value);
    }

    #[test]
    fn test_multi() {
        let reader = Reader::new("(a b c) (d e f)");
        assert_eq!(reader.count(), 2);
    }
}
