mod parse;

use thiserror::Error;

use parse::Parser;

use value::Value;

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

    fn parse_value(&mut self) -> Option<Result<Value, Error>> {
        Some(Ok(match self.parser.next()? {
            Ok(parse::Node::LeftParen) => Value::List(match self.parse_list() {
                Ok(list) => list,
                Err(e) => return Some(Err(Error::ParseError(e.to_string()))),
            }),
            Ok(parse::Node::Symbol(symbol)) => Value::Symbol(symbol.to_string()),
            _ => todo!(),
        }))
    }

    fn parse_list(&mut self) -> Result<Vec<Value>, Error> {
        let mut list = Vec::new();
        loop {
            match self.parser.next() {
                Some(Ok(parse::Node::LeftParen)) => list.push(Value::List(self.parse_list()?)),
                Some(Ok(parse::Node::RightParen)) => return Ok(list),
                Some(Ok(parse::Node::Quote)) => list.push(Value::List(vec![
                    Value::Symbol("quote".to_string()),
                    match self.parse_value() {
                        Some(Ok(val)) => val,
                        Some(Err(e)) => return Err(Error::ParseError(e.to_string())),
                        None => return Err(Error::UnbalancedParens),
                    },
                ])),
                Some(Ok(parse::Node::Symbol(symbol))) => {
                    list.push(Value::Symbol(symbol.to_string()))
                }
                Some(Ok(parse::Node::String(string))) => {
                    list.push(Value::String(string.to_string()))
                }
                Some(Ok(parse::Node::Int(i))) => list.push(Value::Int(i.parse().unwrap())),
                Some(Err(e)) => return Err(Error::ParseError(e.to_string())),
                None => return Err(Error::UnbalancedParens),
            }
        }
    }
}

impl<'a> Iterator for Reader<'a> {
    type Item = Result<Value, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        self.parse_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list_simple() {
        let input = "(a b c)";
        let mut reader = Reader::new(input);

        assert!(matches!(
            reader
                .next()
                .unwrap()
                .unwrap()
                .as_list()
                .unwrap()
                .as_slice(),
            [Value::Symbol(_), Value::Symbol(_), Value::Symbol(_)]
        ));
    }

    #[test]
    fn test_list_nested() {
        let input = "(a (b c) d)";
        let mut reader = Reader::new(input);

        let inner_list = match reader
            .next()
            .unwrap()
            .unwrap()
            .as_list()
            .unwrap()
            .as_slice()
        {
            [Value::Symbol(_), Value::List(list), Value::Symbol(_)] => list.clone(),
            _ => panic!(),
        };

        assert!(matches!(
            inner_list.as_slice(),
            [Value::Symbol(_), Value::Symbol(_)]
        ));
    }

    #[test]
    fn test_quote() {
        let input = "(a 'b c)";
        let mut reader = Reader::new(input);

        let inner_list = match reader
            .next()
            .unwrap()
            .unwrap()
            .as_list()
            .unwrap()
            .as_slice()
        {
            [Value::Symbol(_), Value::List(list), Value::Symbol(_)] => list.clone(),
            _ => panic!(),
        };

        assert!(matches!(inner_list.as_slice(),
            [Value::Symbol(quote), Value::Symbol(_)] if quote == "quote"
        ))
    }
}
