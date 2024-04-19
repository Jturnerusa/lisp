mod parse;

use std::fmt;

use parse::Parser;
use unwrap_enum::{EnumAs, EnumIs};

use crate::Object;

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
        use Value::Cons;
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
                    Cons(
                        Box::new(match self.read() {
                            Some(Ok(v)) => v,
                            Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                            None => return Some(Err(Error::UnbalancedParens)),
                        }),
                        Box::new(match self.read() {
                            Some(Ok(v)) => v,
                            Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                            None => return Some(Err(Error::UnbalancedParens)),
                        }),
                    )
                }
                Some(Ok(Node::RightParen)) => {
                    self.depth -= 1;
                    self.quoting = false;
                    Value::Nil
                }
                Some(Ok(Node::Quote)) => {
                    self.quoting = true;
                    let quoted = self.read().unwrap().unwrap();
                    Cons(
                        Box::new(Cons(
                            Box::new(Value::Symbol("quote".to_string())),
                            Box::new(Cons(Box::new(quoted), Box::new(Value::Nil))),
                        )),
                        Box::new(self.read().unwrap().unwrap()),
                    )
                }
                Some(Ok(Node::Symbol(symbol))) => Cons(
                    Box::new(Value::Symbol(symbol.to_string())),
                    Box::new(match self.read() {
                        Some(Ok(v)) => v,
                        Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                        None => return Some(Err(Error::UnbalancedParens)),
                    }),
                ),
                Some(Ok(Node::String(string))) => Cons(
                    Box::new(Value::String(string.to_string())),
                    Box::new(match self.read() {
                        Some(Ok(v)) => v,
                        Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                        None => return Some(Err(Error::UnbalancedParens)),
                    }),
                ),
                Some(Ok(Node::Int(i))) => Cons(
                    Box::new(Value::Int(i.parse().unwrap())),
                    Box::new(match self.read() {
                        Some(Ok(v)) => v,
                        Some(Err(e)) => return Some(Err(Error::ParseError(e.to_string()))),
                        None => return Some(Err(Error::UnbalancedParens)),
                    }),
                ),
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

    #[test]
    fn test_expand_quote_shorthand() {
        let mut reader = Reader::new("('a b '(c d e))");
        dbg!(reader.next().unwrap().unwrap());
    }
}
