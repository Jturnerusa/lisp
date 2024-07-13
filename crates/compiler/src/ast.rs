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
];

#[derive(Clone, Debug, thiserror::Error)]
pub struct Error<'a> {
    sexpr: &'a Sexpr<'a>,
    message: String,
}

#[derive(Clone, Debug)]
pub enum Ast<'a> {
    EvalWhenCompile(EvalWhenCompile<'a>),
    DefMacro(DefMacro<'a>),
    Lambda(Lambda<'a>),
    Def(Def<'a>),
    Set(Set<'a>),
    If(If<'a>),
    Apply(Apply<'a>),
    BinaryArithemticOperation(BinaryArithmeticOperation<'a>),
    ComparisonOperation(ComparisonOperation<'a>),
    List(List<'a>),
    Cons(Cons<'a>),
    Car(Car<'a>),
    Cdr(Cdr<'a>),
    FnCall(FnCall<'a>),
    Quote(Quote<'a>),
    Variable(Variable<'a>),
    Constant(Constant<'a>),
}

#[derive(Clone, Debug)]
pub struct EvalWhenCompile<'a> {
    pub source: &'a Sexpr<'a>,
    pub exprs: Vec<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub enum Constant<'a> {
    String {
        source: &'a Sexpr<'a>,
        string: String,
    },
    Char {
        source: &'a Sexpr<'a>,
        char: char,
    },
    Int {
        source: &'a Sexpr<'a>,
        int: i64,
    },
    Bool {
        source: &'a Sexpr<'a>,
        bool: bool,
    },
    Nil {
        source: &'a Sexpr<'a>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Scalar(String),
    Composite(Vec<Type>),
}

#[derive(Clone, Debug)]
pub struct Variable<'a> {
    pub source: &'a Sexpr<'a>,
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
pub struct DefMacro<'a> {
    pub source: &'a Sexpr<'a>,
    pub name: String,
    pub parameters: Parameters,
    pub body: Vec<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Lambda<'a> {
    pub source: &'a Sexpr<'a>,
    pub r#type: Option<Type>,
    pub parameters: Parameters,
    pub body: Vec<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Def<'a> {
    pub source: &'a Sexpr<'a>,
    pub parameter: Parameter,
    pub body: Box<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Set<'a> {
    pub source: &'a Sexpr<'a>,
    pub variable: String,
    pub body: Box<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct If<'a> {
    pub source: &'a Sexpr<'a>,
    pub predicate: Box<Ast<'a>>,
    pub then: Box<Ast<'a>>,
    pub r#else: Box<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Apply<'a> {
    pub source: &'a Sexpr<'a>,
    pub exprs: Vec<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub enum BinaryArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct BinaryArithmeticOperation<'a> {
    pub source: &'a Sexpr<'a>,
    pub operator: BinaryArithmeticOperator,
    pub lhs: Box<Ast<'a>>,
    pub rhs: Box<Ast<'a>>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum ComparisonOperator {
    Lt,
    Gt,
    Eq,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation<'a> {
    pub source: &'a Sexpr<'a>,
    pub operator: ComparisonOperator,
    pub lhs: Box<Ast<'a>>,
    pub rhs: Box<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct List<'a> {
    pub source: &'a Sexpr<'a>,
    pub exprs: Vec<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Cons<'a> {
    pub source: &'a Sexpr<'a>,
    pub lhs: Box<Ast<'a>>,
    pub rhs: Box<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Car<'a> {
    pub source: &'a Sexpr<'a>,
    pub body: Box<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Cdr<'a> {
    pub source: &'a Sexpr<'a>,
    pub body: Box<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct FnCall<'a> {
    pub source: &'a Sexpr<'a>,
    pub exprs: Vec<Ast<'a>>,
}

#[derive(Clone, Debug)]
pub struct Quote<'a> {
    pub source: &'a Sexpr<'a>,
    pub body: Quoted<'a>,
}

#[derive(Clone, Debug)]
pub enum Quoted<'a> {
    List {
        source: &'a Sexpr<'a>,
        list: Vec<Quoted<'a>>,
    },
    Symbol {
        source: &'a Sexpr<'a>,
        symbol: String,
    },
    String {
        source: &'a Sexpr<'a>,
        string: String,
    },
    Char {
        source: &'a Sexpr<'a>,
        char: char,
    },
    Int {
        source: &'a Sexpr<'a>,
        int: i64,
    },
    Bool {
        source: &'a Sexpr<'a>,
        bool: bool,
    },
    Nil {
        source: &'a Sexpr<'a>,
    },
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\n{}", self.message, self.sexpr)
    }
}

impl<'a> Ast<'a> {
    pub fn from_sexpr(sexpr: &'a Sexpr<'a>) -> Result<Self, Error<'a>> {
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

    pub fn source_sexpr(&self) -> &Sexpr {
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

fn parse_parameters<'a>(
    source: &'a Sexpr<'a>,
    list: &'a [Sexpr<'a>],
) -> Result<Parameters, Error<'a>> {
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

impl<'a> EvalWhenCompile<'a> {
    pub fn from_sexpr(source: &'a Sexpr<'a>, exprs: &'a [Sexpr<'a>]) -> Result<Self, Error<'a>> {
        Ok(EvalWhenCompile {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl<'a> DefMacro<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        name: &'a Sexpr<'a>,
        parameters: &'a Sexpr<'a>,
        rest: &'a [Sexpr<'a>],
    ) -> Result<Self, Error<'a>> {
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

impl<'a> Lambda<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        parameters: &'a Sexpr<'a>,
        r#type: Option<&'a Sexpr<'a>>,
        rest: &'a [Sexpr<'a>],
    ) -> Result<Self, Error<'a>> {
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

impl<'a> Def<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        parameter: &'a Sexpr<'a>,
        body: &'a Sexpr<'a>,
    ) -> Result<Self, Error<'a>> {
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

impl<'a> Set<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        variable: &'a Sexpr<'a>,
        body: &'a Sexpr<'a>,
    ) -> Result<Self, Error<'a>> {
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

impl<'a> If<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        predicate: &'a Sexpr<'a>,
        then: &'a Sexpr<'a>,
        r#else: &'a Sexpr<'a>,
    ) -> Result<Self, Error<'a>> {
        Ok(If {
            source,
            predicate: Box::new(Ast::from_sexpr(predicate)?),
            then: Box::new(Ast::from_sexpr(then)?),
            r#else: Box::new(Ast::from_sexpr(r#else)?),
        })
    }
}

impl<'a> Apply<'a> {
    pub fn from_sexpr(source: &'a Sexpr<'a>, exprs: &'a [Sexpr<'a>]) -> Result<Self, Error<'a>> {
        Ok(Self {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl<'a> BinaryArithmeticOperation<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        operator: &'a Sexpr<'a>,
        lhs: &'a Sexpr<'a>,
        rhs: &'a Sexpr<'a>,
    ) -> Result<Self, Error<'a>> {
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

impl<'a> ComparisonOperation<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        operator: &'a Sexpr<'a>,
        lhs: &'a Sexpr<'a>,
        rhs: &'a Sexpr<'a>,
    ) -> Result<Self, Error<'a>> {
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

impl<'a> List<'a> {
    pub fn from_sexpr(source: &'a Sexpr<'a>, list: &'a [Sexpr<'a>]) -> Result<Self, Error<'a>> {
        Ok(List {
            source,
            exprs: list
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error>>()?,
        })
    }
}

impl<'a> Cons<'a> {
    pub fn from_sexpr(
        source: &'a Sexpr<'a>,
        lhs: &'a Sexpr<'a>,
        rhs: &'a Sexpr<'a>,
    ) -> Result<Self, Error<'a>> {
        Ok(Self {
            source,
            lhs: Box::new(Ast::from_sexpr(lhs)?),
            rhs: Box::new(Ast::from_sexpr(rhs)?),
        })
    }
}

impl<'a> Car<'a> {
    pub fn from_sexpr(source: &'a Sexpr<'a>, body: &'a Sexpr<'a>) -> Result<Self, Error<'a>> {
        Ok(Self {
            source,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'a> Cdr<'a> {
    pub fn from_sexpr(source: &'a Sexpr<'a>, body: &'a Sexpr<'a>) -> Result<Self, Error<'a>> {
        Ok(Self {
            source,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'a> FnCall<'a> {
    pub fn from_sexpr(source: &'a Sexpr<'a>, exprs: &'a [Sexpr<'a>]) -> Result<Self, Error<'a>> {
        Ok(Self {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error>>()?,
        })
    }
}

impl<'a> Quote<'a> {
    pub fn from_sexpr(source: &'a Sexpr<'a>, body: &'a Sexpr<'a>) -> Result<Self, Error<'a>> {
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

fn quote_list<'a>(source: &'a Sexpr<'a>, list: &'a [Sexpr<'a>]) -> Quoted<'a> {
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
