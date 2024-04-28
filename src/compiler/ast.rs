use crate::{Cons, Value};

#[derive(Clone, Copy, Debug)]
pub enum Error {
    Lambda(&'static str),
    If(&'static str),
}

pub enum Ast {
    Lambda(Lambda),
    If(If),
    List(Vec<Ast>),
    Symbol(String),
    String(String),
    Int(i64),
}

pub struct Lambda {
    parameters: Vec<String>,
    body: Box<Ast>,
}

pub struct If {
    predicate: Box<Ast>,
    then: Box<Ast>,
    els: Box<Ast>,
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
        Value::Cons(cons) => parse_list(cons),
        Value::Symbol(symbol) => Ok(Ast::Symbol(symbol.clone())),
        Value::String(string) => Ok(Ast::String(string.clone())),
        Value::Int(i) => Ok(Ast::Int(*i)),
        _ => todo!(),
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

fn parse_list(cons: &Cons) -> Result<Ast, Error> {
    Ok(Ast::List(
        cons.iter_cars()
            .map(parse)
            .collect::<Result<Vec<_>, Error>>()?,
    ))
}
