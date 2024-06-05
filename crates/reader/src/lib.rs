mod parse;

use thiserror::Error;

use parse::Parser;

use value::{Cons, Value};

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("unbalanced parens")]
    UnbalancedParens,
    #[error("parser error: {0}")]
    ParseError(String),
}

pub struct Reader<'a> {
    parser: Parser<'a>,
}

impl<'a> Reader<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            parser: Parser::new(input),
        }
    }

    fn read(&mut self) -> Option<Result<Value, Error>> {
        self.read_atom()
    }

    fn read_atom(&mut self) -> Option<Result<Value, Error>> {
        Some(Ok(match self.parser.next()? {
            Ok(parse::Node::LeftParen) => match self.read_cons() {
                Ok(cons) => cons,
                Err(e) => return Some(Err(Error::ParseError(e.to_string()))),
            },
            Ok(parse::Node::RightParen) => return Some(Err(Error::UnbalancedParens)),
            Ok(parse::Node::Quote) => match self.quote() {
                Ok(value) => value,
                Err(e) => return Some(Err(Error::ParseError(e.to_string()))),
            },
            Ok(parse::Node::Symbol("nil")) => Value::Nil,
            Ok(parse::Node::Symbol("t")) => Value::True,
            Ok(parse::Node::Symbol(symbol)) => Value::Symbol(symbol.to_string()),
            Ok(parse::Node::String(string)) => Value::String(string.to_string()),
            Ok(parse::Node::Int(i)) => Value::Int(i.parse().unwrap()),
            Err(e) => return Some(Err(Error::ParseError(e.to_string()))),
        }))
    }

    fn read_cons(&mut self) -> Result<Value, Error> {
        Ok(Value::Cons(Box::new(Cons(
            match self.parser.next() {
                Some(Ok(parse::Node::LeftParen)) => self.read_cons()?,
                Some(Ok(parse::Node::RightParen)) => return Ok(Value::Nil),
                Some(Ok(parse::Node::Quote)) => self.quote()?,
                Some(Ok(parse::Node::Symbol("nil"))) => Value::Nil,
                Some(Ok(parse::Node::Symbol("t"))) => Value::True,
                Some(Ok(parse::Node::Symbol(symbol))) => Value::Symbol(symbol.to_string()),
                Some(Ok(parse::Node::String(string))) => Value::String(string.to_string()),
                Some(Ok(parse::Node::Int(i))) => Value::Int(i.parse().unwrap()),
                Some(Err(e)) => return Err(Error::ParseError(e.to_string())),
                None => return Err(Error::UnbalancedParens),
            },
            self.read_cons()?,
        ))))
    }

    fn quote(&mut self) -> Result<Value, Error> {
        Ok(Value::Cons(Box::new(Cons(
            Value::Symbol("quote".to_string()),
            Value::Cons(Box::new(Cons(
                match self.read_atom() {
                    Some(Ok(value)) => value,
                    Some(Err(e)) => return Err(Error::ParseError(e.to_string())),
                    None => return Err(Error::UnbalancedParens),
                },
                Value::Nil,
            ))),
        ))))
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

    macro_rules! atom {
        ($e:tt) => {
            Value::Symbol(stringify!($e).to_string())
        };
    }

    macro_rules! cons {
        ($e:expr) => {
            Value::Cons(Box::new(value::Cons(
                $e,
                Value::Nil
            )))
        };

        ($e:expr, $($rest:expr),+) => {
            Value::Cons(Box::new(value::Cons(
                $e,
                cons!($($rest),+)
            )))
        };
    }

    #[test]
    fn test_simple() {
        let expected = cons! {atom!(a), atom!(b), atom!(c)};
        let mut reader = Reader::new("(a b c)");
        assert_eq!(expected, reader.next().unwrap().unwrap());
    }

    #[test]
    fn test_nested() {
        let expected = cons!(
            atom!(a),
            atom!(b),
            cons!(atom!(c), atom!(d), cons!(atom!(e), atom!(f)))
        );
        let mut reader = Reader::new("(a b (c d (e f)))");
        assert_eq!(expected, reader.next().unwrap().unwrap());
    }

    #[test]
    fn test_quote_shorthand() {
        let expected = cons!(atom!(a), cons!(atom!(quote), cons!(atom!(b), atom!(c))));
        let mut reader = Reader::new("(a '(b c))");
        assert_eq!(expected, reader.next().unwrap().unwrap());
    }
}
