use thiserror::Error;

use unwrap_enum::{EnumAs, EnumIs};

use value::{Cons, Value};

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("invalid lambda expression: {0}")]
    Lambda(String),
    #[error("invalid if expression: {0}")]
    If(String),
    #[error("invalid def expression: {0}")]
    Def(String),
    #[error("invalid set expression: {0}")]
    Set(String),
    #[error("invalid defmacro expression: {0}")]
    DefMacro(String),
    #[error("invalid quote expression: {0}")]
    Quote(String),
    #[error("invalid parameters: {0}")]
    Parameters(String),
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Ast {
    Lambda(Lambda),
    DefMacro(Macro),
    Quote(Box<Ast>),
    If(If),
    FnCall(Vec<Ast>),
    Add(Box<Ast>, Box<Ast>),
    Sub(Box<Ast>, Box<Ast>),
    Mul(Box<Ast>, Box<Ast>),
    Div(Box<Ast>, Box<Ast>),
    Car(Box<Ast>),
    Cdr(Box<Ast>),
    Cons(Box<Ast>, Box<Ast>),
    Def(String, Box<Ast>),
    Set(String, Box<Ast>),
    List(Vec<Ast>),
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

#[derive(Clone, Debug)]
pub struct Macro {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: Box<Ast>,
}

impl Ast {
    pub fn parse(value: &Value) -> Result<Self, Error> {
        Ok(match value {
            Value::Cons(cons) if cons.0.as_symbol().is_some_and(|s| s == "lambda") => {
                parse_lambda(cons)?
            }
            Value::Cons(cons) if cons.0.as_symbol().is_some_and(|s| s == "defmacro") => {
                parse_defmacro(cons)?
            }
            Value::Cons(cons) if cons.0.as_symbol().is_some_and(|s| s == "if") => parse_if(cons)?,
            Value::Cons(cons) if cons.0.as_symbol().is_some_and(|s| s == "quote") => {
                if cons.iter_cars().count() != 2 {
                    return Err(Error::Quote("expected 1 parameter".to_string()));
                } else {
                    Ast::Quote(Box::new(Ast::parse(cons.iter_cars().nth(1).unwrap())?))
                }
            }
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
            Value::Cons(cons)
                if matches!(cons.0.as_symbol().map(|s| s.as_str()), Some("def" | "set")) =>
            {
                if cons.iter_cars().count() != 3 {
                    match cons.0.as_symbol().unwrap().as_str() {
                        "def" => return Err(Error::Def("expected 2 parameters".to_string())),
                        "set" => return Err(Error::Set("expected 2 parameters".to_string())),
                        _ => unreachable!(),
                    }
                } else if !cons.iter_cars().nth(1).unwrap().is_symbol() {
                    match cons.0.as_symbol().unwrap().as_str() {
                        "def" => {
                            return Err(Error::Def(
                                "expected symbol as first parameter".to_string(),
                            ))
                        }
                        "set" => {
                            return Err(Error::Set(
                                "expected symbol as first parameter".to_string(),
                            ))
                        }
                        _ => unreachable!(),
                    }
                } else {
                    let expr = Box::new(Ast::parse(cons.iter_cars().nth(2).unwrap())?);
                    let name = cons
                        .iter_cars()
                        .nth(1)
                        .unwrap()
                        .as_symbol()
                        .cloned()
                        .unwrap();
                    match cons.0.as_symbol().unwrap().as_str() {
                        "def" => Ast::Def(name, expr),
                        "set" => Ast::Set(name, expr),
                        _ => unreachable!(),
                    }
                }
            }
            Value::Cons(cons) if cons.0.as_symbol().is_some_and(|s| s == "list") => Ast::List(
                cons.iter_cars()
                    .skip(1)
                    .map(Ast::parse)
                    .collect::<Result<Vec<_>, Error>>()?,
            ),
            Value::Cons(cons) => Ast::FnCall(
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

    let parameters = match cons.iter_cars().nth(1).unwrap() {
        Value::Cons(cons) => cons
            .iter_cars()
            .map(|car| {
                car.as_symbol()
                    .cloned()
                    .ok_or_else(|| Error::Lambda("non symbol in parameter list".to_string()))
            })
            .collect::<Result<Vec<_>, Error>>()?,
        Value::Nil => Vec::new(),
        _ => todo!(),
    };

    let body = cons.iter_cars().nth(2).unwrap();

    Ok(Ast::Lambda(Lambda {
        parameters,
        body: Box::new(Ast::parse(body)?),
    }))
}

fn parse_defmacro(cons: &Cons) -> Result<Ast, Error> {
    if cons.iter_cars().count() != 4 {
        return Err(Error::DefMacro("expected 3 parameters".to_string()));
    }

    let name = cons
        .iter_cars()
        .nth(1)
        .unwrap()
        .as_symbol()
        .cloned()
        .ok_or_else(|| Error::DefMacro("macro name must be a symbol".to_string()))?;

    let parameters = match cons.iter_cars().nth(2).unwrap() {
        Value::Cons(cons) => cons
            .iter_cars()
            .map(|car| {
                car.as_symbol()
                    .cloned()
                    .ok_or_else(|| Error::Lambda("non symbol in parameter list".to_string()))
            })
            .collect::<Result<Vec<_>, Error>>()?,
        Value::Nil => Vec::new(),
        _ => return Err(Error::DefMacro("invalid parameter list".to_string())),
    };

    Ok(Ast::DefMacro(Macro {
        name,
        parameters,
        body: Box::new(Ast::parse(cons.iter_cars().nth(3).unwrap())?),
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

        assert!(lambda
            .parameters
            .iter()
            .map(String::as_str)
            .eq(["a", "b", "c"].into_iter()));
    }

    #[test]
    fn test_parse_lambda_empty_parameter_list() {
        let input = "(lambda () (+ 1 1))";
        let ast = parse(input).unwrap();
        let lambda = ast.as_lambda().unwrap();

        assert!(lambda.parameters.is_empty())
    }

    #[test]
    fn test_parse_if() {
        let input = "(if (= 1 1) (+ 1 1) (+ 2 2))";
        let ast = parse(input).unwrap();

        assert!(ast.is_if());
    }

    #[test]
    fn test_parse_fncall() {
        let input = "(a b c)";
        let ast = parse(input).unwrap();
        let list = ast.as_fncall().unwrap();

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

    #[test]
    fn test_def() {
        let input = "(def x 1)";
        let ast = parse(input).unwrap();

        assert!(matches!(
            ast,
            Ast::Def(name, _) if name == "x"
        ));
    }

    #[test]
    fn test_set() {
        let input = "(set x 1)";
        let ast = parse(input).unwrap();

        assert!(matches!(
            ast,
            Ast::Set(name, _) if name == "x"
        ));
    }

    #[test]
    fn test_def_err() {
        let input = "(def (+ 1 1) 1)";
        let err = parse(input);

        assert!(matches!(err, Err(Error::Def(_))));
    }

    #[test]
    fn test_set_err() {
        let input = "(set (+ 1 1) 1)";
        let err = parse(input);

        assert!(matches!(err, Err(Error::Set(_))));
    }

    #[test]
    fn test_defmacro() {
        let input = "(defmacro let (&rest)
                       todo)";
        let ast = parse(input).unwrap();

        let defmacro = ast.as_defmacro().unwrap();

        assert_eq!(defmacro.name, "let");
    }

    #[test]
    fn test_quote() {
        let input = "(quote (a b c))";
        let ast = parse(input).unwrap();

        assert!(ast.is_quote());
    }

    #[test]
    fn test_list() {
        let input = "(list a b c)";
        let ast = parse(input).unwrap();

        assert!(ast.is_list());
    }
}
