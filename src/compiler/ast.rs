use unwrap_enum::{EnumAs, EnumIs};

use crate::{Cons, Value};

#[derive(Clone, Copy, Debug)]
pub enum Error {
    Lambda(&'static str),
    If(&'static str),
    Parameters(&'static str),
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Ast {
    Lambda(Lambda),
    If(If),
    List(Vec<Ast>),
    Add(Vec<Ast>),
    Sub(Vec<Ast>),
    Mul(Vec<Ast>),
    Div(Vec<Ast>),
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

pub fn parse(value: &Value) -> Result<Ast, Error> {
    match value {
        Value::Cons(cons)
            if cons
                .0
                .as_symbol()
                .filter(|sym| sym.as_str() == "lambda")
                .is_some() =>
        {
            parse_lambda(cons)
        }
        Value::Cons(cons)
            if cons
                .0
                .as_symbol()
                .filter(|sym| sym.as_str() == "if")
                .is_some() =>
        {
            parse_if(cons)
        }
        Value::Cons(cons) if matches!(cons.0.as_symbol(), Some(sym) if sym.as_str() == "+") => {
            Ok(Ast::Add(
                cons.iter_cars()
                    .skip(1)
                    .map(parse)
                    .collect::<Result<Vec<_>, Error>>()?,
            ))
        }
        Value::Cons(cons) if matches!(cons.0.as_symbol(), Some(sym) if sym.as_str() == "-") => {
            Ok(Ast::Sub(
                cons.iter_cars()
                    .skip(1)
                    .map(parse)
                    .collect::<Result<Vec<_>, Error>>()?,
            ))
        }
        Value::Cons(cons) if matches!(cons.0.as_symbol(), Some(sym) if sym.as_str() == "*") => {
            Ok(Ast::Mul(
                cons.iter_cars()
                    .skip(1)
                    .map(parse)
                    .collect::<Result<Vec<_>, Error>>()?,
            ))
        }
        Value::Cons(cons) if matches!(cons.0.as_symbol(), Some(sym) if sym.as_str() == "/") => {
            Ok(Ast::Div(
                cons.iter_cars()
                    .skip(1)
                    .map(parse)
                    .collect::<Result<Vec<_>, Error>>()?,
            ))
        }
        Value::Cons(cons) if matches!(cons.0.as_symbol(), Some(sym) if sym.as_str() == "car") => {
            if cons.iter_cars().count() != 2 {
                Err(Error::Parameters("car expects 1 parameter"))
            } else {
                Ok(Ast::Car(Box::new(parse(cons.iter_cars().nth(1).unwrap())?)))
            }
        }
        Value::Cons(cons) if matches!(cons.0.as_symbol(), Some(sym) if sym.as_str() == "cdr") => {
            if cons.iter_cars().count() != 2 {
                Err(Error::Parameters("cdr expects 1 parameter"))
            } else {
                Ok(Ast::Cdr(Box::new(parse(cons.iter_cars().nth(1).unwrap())?)))
            }
        }
        Value::Cons(cons) if matches!(cons.0.as_symbol(), Some(sym) if sym.as_str() == "cons") => {
            if cons.iter_cars().count() != 3 {
                Err(Error::Parameters("cons expects 2 parameters"))
            } else {
                Ok(Ast::Cons(
                    Box::new(parse(cons.iter_cars().nth(1).unwrap())?),
                    Box::new(parse(cons.iter_cars().nth(2).unwrap())?),
                ))
            }
        }
        Value::Cons(cons) => Ok(Ast::List(
            cons.iter_cars()
                .map(parse)
                .collect::<Result<Vec<_>, Error>>()?,
        )),
        Value::Symbol(symbol) if symbol.as_str() == "t" => Ok(Ast::True),
        Value::Symbol(symbol) => Ok(Ast::Symbol(symbol.clone())),
        Value::String(string) => Ok(Ast::String(string.clone())),
        Value::Int(i) => Ok(Ast::Int(*i)),
        Value::Nil => Ok(Ast::Nil),
    }
}

fn parse_lambda(cons: &Cons) -> Result<Ast, Error> {
    if cons.iter_cars().count() != 3 {
        return Err(Error::Lambda("wrong amount of expressions"));
    }

    let parmeters_list = cons
        .iter_cars()
        .nth(1)
        .and_then(|param| param.as_cons())
        .ok_or(Error::Lambda("invalid parameter list"))?;

    let parameters = parmeters_list
        .iter_cars()
        .map(|value| match value {
            Value::Symbol(symbol) => Ok(symbol.clone()),
            _ => Err(Error::Lambda("parameter not a symbol")),
        })
        .collect::<Result<Vec<String>, Error>>()?;

    let body = cons.iter_cars().nth(2).unwrap();

    Ok(Ast::Lambda(Lambda {
        parameters,
        body: Box::new(parse(body)?),
    }))
}

fn parse_if(cons: &Cons) -> Result<Ast, Error> {
    if cons.iter_cars().count() != 4 {
        return Err(Error::If("wrong amount of expressions"));
    }

    let predicate = parse(cons.iter_cars().nth(1).unwrap())?;
    let then = parse(cons.iter_cars().nth(2).unwrap())?;
    let els = parse(cons.iter_cars().nth(3).unwrap())?;

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
        let mut reader = crate::reader::Reader::new(input);
        let read = reader.next().unwrap().unwrap();
        super::parse(&read)
    }

    #[test]
    fn test_parse_lambda() {
        let input = "(lambda (a b c) (+ a b c))";
        let ast = parse(input).unwrap();
        let lambda = ast.as_lambda().unwrap();

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
