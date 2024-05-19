use thiserror::Error;

use unwrap_enum::{EnumAs, EnumIs};

use value::{Cons, Value};

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("invalid lambda expression: {0}")]
    Lambda(String),
    #[error("invalid if expression: {0}")]
    If(String),
    #[error("invalid parameters: {0}")]
    Parameters(String),
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Ast {
    Lambda(Lambda),
    If(If),
    List(Vec<Ast>),
    Add(Box<Ast>, Box<Ast>),
    Sub(Box<Ast>, Box<Ast>),
    Mul(Box<Ast>, Box<Ast>),
    Div(Box<Ast>, Box<Ast>),
    Car(Box<Ast>),
    Cdr(Box<Ast>),
    Cons(Box<Ast>, Box<Ast>),
    Symbol(String),
    String(String),
    Int(i64),
    True,
    Nil,
}

#[derive(Clone, Debug)]
pub struct Lambda {
    pub parameters: Vec<String>,
    pub body: Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct If {
    pub predicate: Box<Ast>,
    pub then: Box<Ast>,
    pub els: Box<Ast>,
}

impl Ast {
    pub fn parse(value: &Value) -> Result<Self, Error> {
        Ok(match value {
            Value::Cons(cons) if cons.0.as_symbol().is_some_and(|s| s == "lambda") => {
                parse_lambda(cons)?
            }
            Value::Cons(cons) if cons.0.as_symbol().is_some_and(|s| s == "if") => parse_if(cons)?,
            Value::Cons(cons)
                if matches!(
                    cons.0.as_symbol().map(|s| s.as_str()),
                    Some("+" | "-" | "*" | "/" | "cons")
                ) =>
            {
                if cons.iter_cars().count() != 3 {
                    return Err(Error::Parameters(format!(
                        "binary operation {} expects 2 parameters",
                        cons.0.as_symbol().unwrap()
                    )));
                } else {
                    let a = Box::new(Ast::parse(cons.iter_cars().nth(1).unwrap())?);
                    let b = Box::new(Ast::parse(cons.iter_cars().nth(2).unwrap())?);
                    match cons.0.as_symbol().unwrap().as_str() {
                        "+" => Ast::Add(a, b),
                        "-" => Ast::Sub(a, b),
                        "*" => Ast::Mul(a, b),
                        "/" => Ast::Div(a, b),
                        "cons" => Ast::Cons(a, b),
                        _ => unreachable!(),
                    }
                }
            }
            Value::Cons(cons)
                if matches!(cons.0.as_symbol().map(|s| s.as_str()), Some("car" | "cdr")) =>
            {
                if cons.iter_cars().count() != 2 {
                    return Err(Error::Parameters(format!(
                        "unary operation {} expects 1 parameter",
                        cons.0.as_symbol().unwrap()
                    )));
                } else {
                    let a = Box::new(Ast::parse(cons.iter_cars().nth(1).unwrap())?);
                    match cons.0.as_symbol().unwrap().as_str() {
                        "car" => Ast::Car(a),
                        "cdr" => Ast::Cdr(a),
                        _ => unreachable!(),
                    }
                }
            }
            Value::Cons(cons) => Ast::List(
                cons.iter_cars()
                    .map(Ast::parse)
                    .collect::<Result<Vec<_>, Error>>()?,
            ),
            Value::Symbol(symbol) => Ast::Symbol(symbol.clone()),
            Value::String(string) => Ast::String(string.clone()),
            Value::Int(i) => Ast::Int(*i),
            Value::True => Ast::True,
            Value::Nil => Ast::Nil,
        })
    }
}

fn parse_lambda(cons: &Cons) -> Result<Ast, Error> {
    if cons.iter_cars().count() != 3 {
        return Err(Error::Lambda("wrong amount of expressions".to_string()));
    }

    let parmeters_list = cons
        .iter_cars()
        .nth(1)
        .and_then(|param| param.as_cons())
        .ok_or(Error::Lambda("invalid parameter list".to_string()))?;

    let parameters = parmeters_list
        .iter_cars()
        .map(|value| match value {
            Value::Symbol(symbol) => Ok(symbol.clone()),
            _ => Err(Error::Lambda("parameter not a symbol".to_string())),
        })
        .collect::<Result<Vec<String>, Error>>()?;

    let body = cons.iter_cars().nth(2).unwrap();

    Ok(Ast::Lambda(Lambda {
        parameters,
        body: Box::new(Ast::parse(body)?),
    }))
}

fn parse_if(cons: &Cons) -> Result<Ast, Error> {
    if cons.iter_cars().count() != 4 {
        return Err(Error::If("wrong amount of expressions".to_string()));
    }

    let predicate = Ast::parse(cons.iter_cars().nth(1).unwrap())?;
    let then = Ast::parse(cons.iter_cars().nth(2).unwrap())?;
    let els = Ast::parse(cons.iter_cars().nth(3).unwrap())?;

    Ok(Ast::If(If {
        predicate: Box::new(predicate),
        then: Box::new(then),
        els: Box::new(els),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> Result<Ast, Error> {
        let mut reader = reader::Reader::new(input);
        let read = reader.next().unwrap().unwrap();
        Ast::parse(&read)
    }

    #[test]
    fn test_parse_lambda() {
        let input = "(lambda (a b c) (+ a b))";
        let ast = parse(input).unwrap();
        let lambda = ast.as_lambda().unwrap();
        dbg!(&lambda);
        assert!(lambda
            .parameters
            .iter()
            .map(String::as_str)
            .eq(["a", "b", "c"].into_iter()));
    }

    #[test]
    fn test_parse_if() {
        let input = "(if (= 1 1) (+ 1 1) (+ 2 2))";
        let ast = parse(input).unwrap();

        assert!(ast.is_if());
    }

    #[test]
    fn test_parse_list() {
        let input = "(a b c)";
        let ast = parse(input).unwrap();
        let list = ast.as_list().unwrap();

        assert!(matches!(
            &list[0], Ast::Symbol(a) if a.as_str() == "a"
        ));
        assert!(matches!(
            &list[1], Ast::Symbol(a) if a.as_str() == "b"
        ));
        assert!(matches!(
            &list[2], Ast::Symbol(a) if a.as_str() == "c"
        ));
    }
}
