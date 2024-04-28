mod parse;

use std::fmt;

use parse::Parser;
use unwrap_enum::{EnumAs, EnumIs};

use crate::Value;

#[derive(Clone, Debug)]
pub enum Error {
    UnbalancedParens,
    ParseError(String),
}

pub struct Reader<'a> {
    parser: Parser<'a>,
    depth: u64,
    quoting: bool,
}

impl<'a> Reader<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            parser: Parser::new(input),
            depth: 0,
            quoting: false,
        }
    }

    fn read(&mut self) -> Option<Result<Value, Error>> {
        use parse::Node;
        if self.depth == 0 || self.quoting {
            self.quoting = false;
            Some(Ok(match self.parser.next()? {
                Ok(Node::LeftParen) => {
                    self.depth += 1;
                    match self.read() {
                        Some(Ok(v)) => v,
                        Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                        None => return Some(Err(Error::UnbalancedParens)),
                    }
                }
                Ok(Node::String(string)) => Value::String(string.to_string()),
                Ok(Node::Symbol(symbol)) => Value::Symbol(symbol.to_string()),
                Ok(Node::Int(i)) => Value::Int(i.parse().unwrap()),
                Err(e) => return Some(Err(Error::ParseError(e.to_string()))),
                _ => unreachable!(),
            }))
        } else {
            Some(Ok(match self.parser.next() {
                Some(Ok(Node::LeftParen)) => {
                    self.depth += 1;
                    Value::Cons(Box::new(crate::Cons(
                        match self.read() {
                            Some(Ok(v)) => v,
                            Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                            None => return Some(Err(Error::UnbalancedParens)),
                        },
                        match self.read() {
                            Some(Ok(v)) => v,
                            Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                            None => return Some(Err(Error::UnbalancedParens)),
                        },
                    )))
                }
                Some(Ok(Node::RightParen)) => {
                    self.depth -= 1;
                    self.quoting = false;
                    Value::Nil
                }
                Some(Ok(Node::Quote)) => {
                    self.quoting = true;
                    let quoted = self.read().unwrap().unwrap();
                    let inner = Value::Cons(Box::new(crate::Cons(
                        Value::Symbol("quote".to_string()),
                        Value::Cons(Box::new(crate::Cons(quoted, Value::Nil))),
                    )));
                    Value::Cons(Box::new(crate::Cons(inner, self.read().unwrap().unwrap())))
                }
                Some(Ok(Node::Symbol(symbol))) => Value::Cons(Box::new(crate::Cons(
                    Value::Symbol(symbol.to_string()),
                    match self.read() {
                        Some(Ok(v)) => v,
                        Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                        None => return Some(Err(Error::UnbalancedParens)),
                    },
                ))),
                Some(Ok(Node::String(string))) => Value::Cons(Box::new(crate::Cons(
                    Value::String(string.to_string()),
                    match self.read() {
                        Some(Ok(v)) => v,
                        Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                        None => return Some(Err(Error::UnbalancedParens)),
                    },
                ))),
                Some(Ok(Node::Int(i))) => Value::Cons(Box::new(crate::Cons(
                    Value::Int(i.parse().unwrap()),
                    match self.read() {
                        Some(Ok(v)) => v,
                        Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                        None => return Some(Err(Error::UnbalancedParens)),
                    },
                ))),

                Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                None => return Some(Err(Error::UnbalancedParens)),
            }))
        }
    }
}

impl<'a> Iterator for Reader<'a> {
    type Item = Result<Value, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        self.read()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnbalancedParens => write!(f, "unbalanced parens"),
            Self::ParseError(e) => write!(f, "parser error: {}", e),
        }
    }
}

impl std::error::Error for Error {}

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
            Value::Cons(Box::new(crate::Cons(
                $e,
                Value::Nil
            )))
        };

        ($e:expr, $($rest:expr),+) => {
            Value::Cons(Box::new(crate::Cons(
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
