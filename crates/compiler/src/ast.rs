use core::fmt;

use reader::Sexpr;
use unwrap_enum::{EnumAs, EnumIs};

static BUILT_INS: &[&str] = &[
    "+",
    "-",
    "*",
    "/",
    "cons",
    "car",
    "cdr",
    "list",
    "apply",
    "cons?",
    "function?",
    "symbol?",
    "string?",
    "int?",
    "char?",
    "nil?",
    "apply",
    "lambda",
    "defmacro",
    "def",
    "set!",
    "eval-when-compile",
    "quote",
    "if",
    "=",
    ">",
    "<",
];

#[derive(Clone, Debug, thiserror::Error)]
pub struct Error<'sexpr, 'context> {
    sexpr: &'sexpr Sexpr<'context>,
    message: String,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Ast<'sexpr, 'context> {
    EvalWhenCompile(EvalWhenCompile<'sexpr, 'context>),
    DefMacro(DefMacro<'sexpr, 'context>),
    Lambda(Lambda<'sexpr, 'context>),
    Def(Def<'sexpr, 'context>),
    Set(Set<'sexpr, 'context>),
    If(If<'sexpr, 'context>),
    Apply(Apply<'sexpr, 'context>),
    BinaryArithemticOperation(BinaryArithmeticOperation<'sexpr, 'context>),
    ComparisonOperation(ComparisonOperation<'sexpr, 'context>),
    List(List<'sexpr, 'context>),
    Cons(Cons<'sexpr, 'context>),
    Car(Car<'sexpr, 'context>),
    Cdr(Cdr<'sexpr, 'context>),
    FnCall(FnCall<'sexpr, 'context>),
    Quote(Quote<'sexpr, 'context>),
    Variable(Variable<'sexpr, 'context>),
    Constant(Constant<'sexpr, 'context>),
}

#[derive(Clone, Debug)]
pub struct EvalWhenCompile<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub enum Constant<'sexpr, 'context> {
    String {
        source: &'sexpr Sexpr<'context>,
        string: String,
    },
    Char {
        source: &'sexpr Sexpr<'context>,
        char: char,
    },
    Int {
        source: &'sexpr Sexpr<'context>,
        int: i64,
    },
    Bool {
        source: &'sexpr Sexpr<'context>,
        bool: bool,
    },
    Nil {
        source: &'sexpr Sexpr<'context>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Scalar(String),
    Composite(Vec<Type>),
}

#[derive(Clone, Debug)]
pub struct Variable<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parameter {
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters {
    Normal(Vec<Parameter>),
    Rest(Vec<Parameter>, Parameter),
}

#[derive(Clone, Debug)]
pub struct DefMacro<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub name: String,
    pub parameters: Parameters,
    pub body: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Lambda<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub r#type: Option<Type>,
    pub parameters: Parameters,
    pub body: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Def<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub parameter: Parameter,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Set<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub variable: String,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct If<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub predicate: Box<Ast<'sexpr, 'context>>,
    pub then: Box<Ast<'sexpr, 'context>>,
    pub r#else: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Apply<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub enum BinaryArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct BinaryArithmeticOperation<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub operator: BinaryArithmeticOperator,
    pub lhs: Box<Ast<'sexpr, 'context>>,
    pub rhs: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum ComparisonOperator {
    Lt,
    Gt,
    Eq,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub operator: ComparisonOperator,
    pub lhs: Box<Ast<'sexpr, 'context>>,
    pub rhs: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct List<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Cons<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub lhs: Box<Ast<'sexpr, 'context>>,
    pub rhs: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Car<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Cdr<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct FnCall<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub function: Box<Ast<'sexpr, 'context>>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Quote<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub body: Quoted<'sexpr, 'context>,
}

#[derive(Clone, Debug)]
pub enum Quoted<'sexpr, 'context> {
    List {
        source: &'sexpr Sexpr<'context>,
        list: Vec<Quoted<'sexpr, 'context>>,
    },
    Symbol {
        source: &'sexpr Sexpr<'context>,
        symbol: String,
    },
    String {
        source: &'sexpr Sexpr<'context>,
        string: String,
    },
    Char {
        source: &'sexpr Sexpr<'context>,
        char: char,
    },
    Int {
        source: &'sexpr Sexpr<'context>,
        int: i64,
    },
    Bool {
        source: &'sexpr Sexpr<'context>,
        bool: bool,
    },
    Nil {
        source: &'sexpr Sexpr<'context>,
    },
}

impl<'sexpr, 'context> fmt::Display for Error<'sexpr, 'context> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\n{}", self.message, self.sexpr)
    }
}

impl<'sexpr, 'context> Ast<'sexpr, 'context> {
    pub fn from_sexpr(sexpr: &'sexpr Sexpr<'context>) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(
            if let Sexpr::List { list, .. } = sexpr
                && let Some(Sexpr::Symbol { symbol, .. }) = list.first()
                && BUILT_INS.iter().any(|b| b == symbol)
            {
                match list.as_slice() {
                    [Sexpr::Symbol { symbol, .. }, rest @ ..] if symbol == "eval-when-compile" => {
                        Ast::EvalWhenCompile(EvalWhenCompile::from_sexpr(sexpr, rest)?)
                    }

                    [Sexpr::Symbol { symbol, .. }, name, parameters, rest @ ..]
                        if symbol == "defmacro" =>
                    {
                        Ast::DefMacro(DefMacro::from_sexpr(sexpr, name, parameters, rest)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, parameters, rest @ ..] if symbol == "lambda" => {
                        Ast::Lambda(Lambda::from_sexpr(sexpr, parameters, None, rest)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, parameters, Sexpr::Symbol { symbol: arrow, .. }, r#type, rest @ ..]
                        if symbol == "lambda" && arrow == "->" =>
                    {
                        Ast::Lambda(Lambda::from_sexpr(sexpr, parameters, Some(r#type), rest)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, parameter, body] if symbol == "def" => {
                        Ast::Def(Def::from_sexpr(sexpr, parameter, body)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, parameter, body] if symbol == "set!" => {
                        Ast::Set(Set::from_sexpr(sexpr, parameter, body)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, predicate, then, r#else] if symbol == "if" => {
                        Ast::If(If::from_sexpr(sexpr, predicate, then, r#else)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, rest @ ..] if symbol == "apply" => {
                        todo!()
                    }
                    [operator @ Sexpr::Symbol { symbol, .. }, lhs, rhs]
                        if matches!(symbol.as_str(), "+" | "-" | "*" | "/") =>
                    {
                        Ast::BinaryArithemticOperation(BinaryArithmeticOperation::from_sexpr(
                            sexpr, operator, lhs, rhs,
                        )?)
                    }
                    [operator @ Sexpr::Symbol { symbol, .. }, lhs, rhs]
                        if matches!(symbol.as_str(), "=" | ">" | "<") =>
                    {
                        Ast::ComparisonOperation(ComparisonOperation::from_sexpr(
                            sexpr, operator, lhs, rhs,
                        )?)
                    }
                    [Sexpr::Symbol { symbol, .. }, rest @ ..] if symbol == "list" => {
                        Ast::List(List::from_sexpr(sexpr, rest)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, lhs, rhs] if symbol == "cons" => {
                        Ast::Cons(Cons::from_sexpr(sexpr, lhs, rhs)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, body] if symbol == "car" => {
                        Ast::Car(Car::from_sexpr(sexpr, body)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, body] if symbol == "cdr" => {
                        Ast::Cdr(Cdr::from_sexpr(sexpr, body)?)
                    }
                    [Sexpr::Symbol { symbol, .. }, body] if symbol == "quote" => {
                        Ast::Quote(Quote::from_sexpr(sexpr, body)?)
                    }
                    _ => {
                        return Err(Error {
                            sexpr,
                            message: "invalid expression".to_string(),
                        })
                    }
                }
            } else if let Sexpr::List { list, .. } = sexpr {
                Ast::FnCall(FnCall::from_sexpr(sexpr, list.as_slice())?)
            } else if let Sexpr::Symbol { symbol, .. } = sexpr {
                Ast::Variable(Variable {
                    source: sexpr,
                    name: symbol.clone(),
                })
            } else if let Sexpr::String { string, .. } = sexpr {
                Ast::Constant(Constant::String {
                    source: sexpr,
                    string: string.clone(),
                })
            } else if let Sexpr::Char { char, .. } = sexpr {
                Ast::Constant(Constant::Char {
                    source: sexpr,
                    char: *char,
                })
            } else if let Sexpr::Int { int, .. } = sexpr {
                Ast::Constant(Constant::Int {
                    source: sexpr,
                    int: *int,
                })
            } else if let Sexpr::Bool { bool, .. } = sexpr {
                Ast::Constant(Constant::Bool {
                    source: sexpr,
                    bool: *bool,
                })
            } else if let Sexpr::Nil { .. } = sexpr {
                Ast::Constant(Constant::Nil { source: sexpr })
            } else {
                todo!()
            },
        )
    }

    pub fn source_sexpr(&self) -> &'sexpr Sexpr<'context> {
        match self {
            Self::EvalWhenCompile(EvalWhenCompile { source, .. })
            | Self::DefMacro(DefMacro { source, .. })
            | Self::Lambda(Lambda { source, .. })
            | Self::Def(Def { source, .. })
            | Self::Set(Set { source, .. })
            | Self::If(If { source, .. })
            | Self::Apply(Apply { source, .. })
            | Self::BinaryArithemticOperation(BinaryArithmeticOperation { source, .. })
            | Self::ComparisonOperation(ComparisonOperation { source, .. })
            | Self::List(List { source, .. })
            | Self::Cons(Cons { source, .. })
            | Self::Car(Car { source, .. })
            | Self::Cdr(Cdr { source, .. })
            | Self::FnCall(FnCall { source, .. })
            | Self::Quote(Quote { source, .. })
            | Self::Variable(Variable { source, .. })
            | Self::Constant(Constant::String { source, .. })
            | Self::Constant(Constant::Char { source, .. })
            | Self::Constant(Constant::Int { source, .. })
            | Self::Constant(Constant::Bool { source, .. })
            | Self::Constant(Constant::Nil { source }) => source,
        }
    }
}

impl Type {
    pub fn from_sexpr(sexpr: &Sexpr) -> Result<Self, ()> {
        Ok(match sexpr {
            Sexpr::List { list, .. } => Type::Composite(
                list.iter()
                    .map(Type::from_sexpr)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Sexpr::Symbol { symbol, .. } => Type::Scalar(symbol.clone()),
            _ => return Err(()),
        })
    }
}

impl Parameter {
    pub fn from_sexpr(sexpr: &Sexpr) -> Result<Self, ()> {
        Ok(match sexpr {
            Sexpr::List { list, .. } => {
                if list.len() != 2 {
                    return Err(());
                }
                let name = list[0].as_symbol().ok_or(())?.to_string();
                let r#type = Type::from_sexpr(&list[1])?;
                Parameter {
                    name,
                    r#type: Some(r#type),
                }
            }
            Sexpr::Symbol { symbol, .. } => Parameter {
                name: symbol.clone(),
                r#type: None,
            },
            _ => return Err(()),
        })
    }
}

impl Parameters {
    pub fn len(&self) -> usize {
        match self {
            Parameters::Normal(params) => params.len(),
            Parameters::Rest(params, _) => params.len() + 1,
        }
    }
}

fn parse_parameters<'sexpr, 'context>(
    source: &'sexpr Sexpr<'context>,
    list: &'sexpr [Sexpr<'context>],
) -> Result<Parameters, Error<'sexpr, 'context>> {
    let parameters = list
        .iter()
        .map(Parameter::from_sexpr)
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| Error {
            sexpr: source,
            message: "failed to parse parameter".to_string(),
        })?;

    let with_rest = micro_nom::map(
        micro_nom::separated(
            micro_nom::take_while::<&[Parameter], _>(|parameter: &Parameter| {
                parameter.name != "&rest"
            }),
            micro_nom::take_one_if::<&[Parameter], _>(|parameter: &&Parameter| {
                parameter.name == "&rest"
            }),
            micro_nom::take_one,
        ),
        |(parameters, rest)| Parameters::Rest(parameters.to_vec(), rest.clone()),
    );

    let without_rest = micro_nom::map(
        micro_nom::take_while::<&[Parameter], _>(|_| true),
        |parameters| Parameters::Normal(parameters.to_vec()),
    );

    let p = match micro_nom::branch(with_rest, without_rest)(parameters.as_slice()) {
        Ok((_, p)) => p,
        Err(_) => {
            return Err(Error {
                sexpr: source,
                message: "failed to parse parameters".to_string(),
            })
        }
    };

    Ok(p)
}

impl<'sexpr, 'context> EvalWhenCompile<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        exprs: &'sexpr [Sexpr<'context>],
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(EvalWhenCompile {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl<'sexpr, 'context> DefMacro<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        name: &'sexpr Sexpr<'context>,
        parameters: &'sexpr Sexpr<'context>,
        rest: &'sexpr [Sexpr<'context>],
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(DefMacro {
            source,
            name: name
                .as_symbol()
                .ok_or(Error {
                    sexpr: source,
                    message: "expected symbol as identifer".to_string(),
                })?
                .to_string(),
            parameters: match parameters {
                Sexpr::List { list, .. } => parse_parameters(source, list.as_slice())?,
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        sexpr: source,
                        message: "expected list for parameters".to_string(),
                    })
                }
            },
            body: rest
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error>>()?,
        })
    }
}

impl<'sexpr, 'context> Lambda<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        parameters: &'sexpr Sexpr<'context>,
        r#type: Option<&'sexpr Sexpr<'context>>,
        rest: &'sexpr [Sexpr<'context>],
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Lambda {
            source,
            parameters: match parameters {
                Sexpr::List { list, .. } => parse_parameters(source, list.as_slice())?,
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        sexpr: source,
                        message: "expected list for parameters".to_string(),
                    })
                }
            },
            r#type: match r#type {
                Some(r#type) => Some(Type::from_sexpr(r#type).map_err(|_| Error {
                    sexpr: source,
                    message: "failed to parse type parameter".to_string(),
                })?),
                None => None,
            },
            body: rest
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error>>()?,
        })
    }
}

impl<'sexpr, 'context> Def<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        parameter: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Def {
            source,
            parameter: Parameter::from_sexpr(parameter).map_err(|_| Error {
                sexpr: source,
                message: "failed to parse parameter".to_string(),
            })?,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'sexpr, 'context> Set<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        variable: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            variable: variable
                .as_symbol()
                .ok_or(Error {
                    sexpr: source,
                    message: "expected symbol as indentifiter".to_string(),
                })?
                .to_string(),
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'sexpr, 'context> If<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        predicate: &'sexpr Sexpr<'context>,
        then: &'sexpr Sexpr<'context>,
        r#else: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(If {
            source,
            predicate: Box::new(Ast::from_sexpr(predicate)?),
            then: Box::new(Ast::from_sexpr(then)?),
            r#else: Box::new(Ast::from_sexpr(r#else)?),
        })
    }
}

impl<'sexpr, 'context> Apply<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        exprs: &'sexpr [Sexpr<'context>],
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl<'sexpr, 'context> BinaryArithmeticOperation<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        operator: &'sexpr Sexpr<'context>,
        lhs: &'sexpr Sexpr<'context>,
        rhs: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            operator: match operator {
                Sexpr::Symbol { symbol, .. } if symbol == "+" => BinaryArithmeticOperator::Add,
                Sexpr::Symbol { symbol, .. } if symbol == "-" => BinaryArithmeticOperator::Sub,
                Sexpr::Symbol { symbol, .. } if symbol == "*" => BinaryArithmeticOperator::Mul,
                Sexpr::Symbol { symbol, .. } if symbol == "/" => BinaryArithmeticOperator::Div,
                Sexpr::Symbol { symbol, .. } => {
                    return Err(Error {
                        sexpr: source,
                        message: format!("unknown operator: {symbol}"),
                    })
                }
                _ => {
                    return Err(Error {
                        sexpr: source,
                        message: "expected symbol as operator".to_string(),
                    })
                }
            },
            lhs: Box::new(Ast::from_sexpr(lhs)?),
            rhs: Box::new(Ast::from_sexpr(rhs)?),
        })
    }
}

impl<'sexpr, 'context> ComparisonOperation<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        operator: &'sexpr Sexpr<'context>,
        lhs: &'sexpr Sexpr<'context>,
        rhs: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            operator: match operator {
                Sexpr::Symbol { symbol, .. } if symbol == "=" => ComparisonOperator::Eq,
                Sexpr::Symbol { symbol, .. } if symbol == ">" => ComparisonOperator::Gt,
                Sexpr::Symbol { symbol, .. } if symbol == "<" => ComparisonOperator::Lt,
                Sexpr::Symbol { .. } => {
                    return Err(Error {
                        sexpr: source,
                        message: "invalid comparison operator".to_string(),
                    })
                }
                _ => {
                    return Err(Error {
                        sexpr: source,
                        message: "expected symbol as operator".to_string(),
                    })
                }
            },
            lhs: Box::new(Ast::from_sexpr(lhs)?),
            rhs: Box::new(Ast::from_sexpr(rhs)?),
        })
    }
}

impl<'sexpr, 'context> List<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        list: &'sexpr [Sexpr<'context>],
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(List {
            source,
            exprs: list
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error>>()?,
        })
    }
}

impl<'sexpr, 'context> Cons<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        lhs: &'sexpr Sexpr<'context>,
        rhs: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            lhs: Box::new(Ast::from_sexpr(lhs)?),
            rhs: Box::new(Ast::from_sexpr(rhs)?),
        })
    }
}

impl<'sexpr, 'context> Car<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'sexpr, 'context> Cdr<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'sexpr, 'context> FnCall<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        exprs: &'sexpr [Sexpr<'context>],
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            function: Box::new(exprs.first().map(Ast::from_sexpr).unwrap()?),
            exprs: exprs
                .iter()
                .skip(1)
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error>>()?,
        })
    }
}

impl<'sexpr, 'context> Quote<'sexpr, 'context> {
    pub fn from_sexpr(
        source: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Self, Error<'sexpr, 'context>> {
        Ok(Self {
            source,
            body: match body {
                Sexpr::List { list, .. } => quote_list(source, list.as_slice()),
                Sexpr::Symbol { symbol, .. } => Quoted::Symbol {
                    source,
                    symbol: symbol.clone(),
                },
                Sexpr::String { string, .. } => Quoted::String {
                    source,
                    string: string.clone(),
                },
                Sexpr::Char { char, .. } => Quoted::Char {
                    source,
                    char: *char,
                },
                Sexpr::Int { int, .. } => Quoted::Int { source, int: *int },
                Sexpr::Bool { bool, .. } => Quoted::Bool {
                    source,
                    bool: *bool,
                },
                Sexpr::Nil { .. } => Quoted::Nil { source },
            },
        })
    }
}

fn quote_list<'sexpr, 'context>(
    source: &'sexpr Sexpr<'context>,
    list: &'sexpr [Sexpr<'context>],
) -> Quoted<'sexpr, 'context> {
    Quoted::List {
        source,
        list: list
            .iter()
            .map(|sexpr| match sexpr {
                Sexpr::List { list, .. } => quote_list(source, list.as_slice()),
                Sexpr::Symbol { symbol, .. } => Quoted::Symbol {
                    source,
                    symbol: symbol.clone(),
                },
                Sexpr::String { string, .. } => Quoted::String {
                    source,
                    string: string.clone(),
                },
                Sexpr::Char { char, .. } => Quoted::Char {
                    source,
                    char: *char,
                },
                Sexpr::Int { int, .. } => Quoted::Int { source, int: *int },
                Sexpr::Bool { bool, .. } => Quoted::Bool {
                    source,
                    bool: *bool,
                },
                Sexpr::Nil { .. } => Quoted::Nil { source },
            })
            .collect(),
    }
}
