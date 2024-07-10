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
    "set",
    "eval-when-compile",
];

#[derive(Clone, Debug)]
pub struct Error<'a, T> {
    source: &'a Sexpr<'a, T>,
    message: String,
}

#[derive(Clone, Debug)]
pub(crate) enum Ast<'a, T> {
    EvalWhenCompile(EvalWhenCompile<'a, T>),
    DefMacro(DefMacro<'a, T>),
    Lambda(Lambda<'a, T>),
    Def(Def<'a, T>),
    Set(Set<'a, T>),
    If(If<'a, T>),
    Apply(Apply<'a, T>),
    BinaryArithemticOperation(BinaryArithmeticOperation<'a, T>),
    ComparisonOperation(ComparisonOperation<'a, T>),
    List(List<'a, T>),
    Cons(Cons<'a, T>),
    Car(Car<'a, T>),
    Cdr(Cdr<'a, T>),
    FnCall(FnCall<'a, T>),
    Quote(Quote<'a, T>),
    Variable(Variable<'a, T>),
    Constant(Constant<'a, T>),
}

#[derive(Clone, Debug)]
pub(crate) struct EvalWhenCompile<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub exprs: Vec<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) enum Constant<'a, T> {
    String {
        source: &'a Sexpr<'a, T>,
        string: String,
    },
    Char {
        source: &'a Sexpr<'a, T>,
        char: char,
    },
    Int {
        source: &'a Sexpr<'a, T>,
        int: i64,
    },
    Bool {
        source: &'a Sexpr<'a, T>,
        bool: bool,
    },
    Nil {
        source: &'a Sexpr<'a, T>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Type {
    Scalar(String),
    Composite(Vec<Type>),
}

#[derive(Clone, Debug)]
pub(crate) struct Variable<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Parameter {
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub(crate) enum Parameters {
    Normal(Vec<Parameter>),
    Rest(Vec<Parameter>, Parameter),
}

#[derive(Clone, Debug)]
pub(crate) struct DefMacro<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub name: String,
    pub parameters: Parameters,
    pub body: Vec<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Lambda<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub r#type: Option<Type>,
    pub parameters: Parameters,
    pub body: Vec<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Def<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub parameter: Parameter,
    pub body: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Set<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub variable: String,
    pub body: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct If<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub predicate: Box<Ast<'a, T>>,
    pub then: Box<Ast<'a, T>>,
    pub r#else: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Apply<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub exprs: Vec<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) enum BinaryArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub(crate) struct BinaryArithmeticOperation<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub operator: BinaryArithmeticOperator,
    pub lhs: Box<Ast<'a, T>>,
    pub rhs: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub(crate) enum ComparisonOperator {
    Lt,
    Gt,
    Eq,
}

#[derive(Clone, Debug)]
pub(crate) struct ComparisonOperation<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub operator: ComparisonOperator,
    pub lhs: Box<Ast<'a, T>>,
    pub rhs: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct List<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub exprs: Vec<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Cons<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub lhs: Box<Ast<'a, T>>,
    pub rhs: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Car<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub body: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Cdr<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub body: Box<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct FnCall<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub exprs: Vec<Ast<'a, T>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Quote<'a, T> {
    pub source: &'a Sexpr<'a, T>,
    pub body: Box<Ast<'a, T>>,
}

impl<'a, T> Ast<'a, T> {
    pub(crate) fn from_sexpr(sexpr: &'a Sexpr<'a, T>) -> Result<Self, Error<'a, T>> {
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
                            source: sexpr,
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

    pub(crate) fn source_sexpr(&self) -> &Sexpr<T> {
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
    pub(crate) fn from_sexpr<T>(sexpr: &Sexpr<'_, T>) -> Result<Self, ()> {
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
    pub(crate) fn from_sexpr<T>(sexpr: &Sexpr<'_, T>) -> Result<Self, ()> {
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
    pub(crate) fn len(&self) -> usize {
        match self {
            Parameters::Normal(params) => params.len(),
            Parameters::Rest(params, _) => params.len() + 1,
        }
    }
}

fn parse_parameters<'a, T>(
    source: &'a Sexpr<'a, T>,
    list: &'a [Sexpr<'a, T>],
) -> Result<Parameters, Error<'a, T>> {
    let parameters = list
        .iter()
        .map(Parameter::from_sexpr)
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| Error {
            source,
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
                source,
                message: "failed to parse parameters".to_string(),
            })
        }
    };

    Ok(p)
}

impl<'a, T> EvalWhenCompile<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        exprs: &'a [Sexpr<'a, T>],
    ) -> Result<Self, Error<'a, T>> {
        Ok(EvalWhenCompile {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl<'a, T> DefMacro<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        name: &'a Sexpr<'a, T>,
        parameters: &'a Sexpr<'a, T>,
        rest: &'a [Sexpr<'a, T>],
    ) -> Result<Self, Error<'a, T>> {
        Ok(DefMacro {
            source,
            name: name
                .as_symbol()
                .ok_or(Error {
                    source,
                    message: "expected symbol as identifer".to_string(),
                })?
                .to_string(),
            parameters: match parameters {
                Sexpr::List { list, .. } => parse_parameters(source, list.as_slice())?,
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        source,
                        message: "expected list for parameters".to_string(),
                    })
                }
            },
            body: rest
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error<_>>>()?,
        })
    }
}

impl<'a, T> Lambda<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        parameters: &'a Sexpr<'a, T>,
        r#type: Option<&'a Sexpr<'a, T>>,
        rest: &'a [Sexpr<'a, T>],
    ) -> Result<Self, Error<'a, T>> {
        Ok(Lambda {
            source,
            parameters: match parameters {
                Sexpr::List { list, .. } => parse_parameters(source, list.as_slice())?,
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        source,
                        message: "expected list for parameters".to_string(),
                    })
                }
            },
            r#type: match r#type {
                Some(r#type) => Some(Type::from_sexpr(r#type).map_err(|_| Error {
                    source,
                    message: "failed to parse type parameter".to_string(),
                })?),
                None => None,
            },
            body: rest
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error<_>>>()?,
        })
    }
}

impl<'a, T> Def<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        parameter: &'a Sexpr<'a, T>,
        body: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Def {
            source,
            parameter: Parameter::from_sexpr(parameter).map_err(|_| Error {
                source,
                message: "failed to parse parameter".to_string(),
            })?,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'a, T> Set<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        variable: &'a Sexpr<'a, T>,
        body: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            variable: variable
                .as_symbol()
                .ok_or(Error {
                    source,
                    message: "expected symbol as indentifiter".to_string(),
                })?
                .to_string(),
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'a, T> If<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        predicate: &'a Sexpr<'a, T>,
        then: &'a Sexpr<'a, T>,
        r#else: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(If {
            source,
            predicate: Box::new(Ast::from_sexpr(predicate)?),
            then: Box::new(Ast::from_sexpr(then)?),
            r#else: Box::new(Ast::from_sexpr(r#else)?),
        })
    }
}

impl<'a, T> Apply<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        exprs: &'a [Sexpr<'a, T>],
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl<'a, T> BinaryArithmeticOperation<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        operator: &'a Sexpr<'a, T>,
        lhs: &'a Sexpr<'a, T>,
        rhs: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            operator: match operator {
                Sexpr::Symbol { symbol, .. } if symbol == "+" => BinaryArithmeticOperator::Add,
                Sexpr::Symbol { symbol, .. } if symbol == "-" => BinaryArithmeticOperator::Sub,
                Sexpr::Symbol { symbol, .. } if symbol == "*" => BinaryArithmeticOperator::Mul,
                Sexpr::Symbol { symbol, .. } if symbol == "/" => BinaryArithmeticOperator::Div,
                Sexpr::Symbol { symbol, .. } => {
                    return Err(Error {
                        source,
                        message: format!("unknown operator: {symbol}"),
                    })
                }
                _ => {
                    return Err(Error {
                        source,
                        message: "expected symbol as operator".to_string(),
                    })
                }
            },
            lhs: Box::new(Ast::from_sexpr(lhs)?),
            rhs: Box::new(Ast::from_sexpr(rhs)?),
        })
    }
}

impl<'a, T> ComparisonOperation<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        operator: &'a Sexpr<'a, T>,
        lhs: &'a Sexpr<'a, T>,
        rhs: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            operator: match operator {
                Sexpr::Symbol { symbol, .. } if symbol == "=" => ComparisonOperator::Eq,
                Sexpr::Symbol { symbol, .. } if symbol == ">" => ComparisonOperator::Gt,
                Sexpr::Symbol { symbol, .. } if symbol == "<" => ComparisonOperator::Lt,
                Sexpr::Symbol { .. } => {
                    return Err(Error {
                        source,
                        message: "invalid comparison operator".to_string(),
                    })
                }
                _ => {
                    return Err(Error {
                        source,
                        message: "expected symbol as operator".to_string(),
                    })
                }
            },
            lhs: Box::new(Ast::from_sexpr(lhs)?),
            rhs: Box::new(Ast::from_sexpr(rhs)?),
        })
    }
}

impl<'a, T> List<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        list: &'a [Sexpr<'a, T>],
    ) -> Result<Self, Error<'a, T>> {
        Ok(List {
            source,
            exprs: list
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error<_>>>()?,
        })
    }
}

impl<'a, T> Cons<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        lhs: &'a Sexpr<'a, T>,
        rhs: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            lhs: Box::new(Ast::from_sexpr(lhs)?),
            rhs: Box::new(Ast::from_sexpr(rhs)?),
        })
    }
}

impl<'a, T> Car<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        body: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'a, T> Cdr<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        body: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}

impl<'a, T> FnCall<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        exprs: &'a [Sexpr<'a, T>],
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            exprs: exprs
                .iter()
                .map(Ast::from_sexpr)
                .collect::<Result<Vec<_>, Error<_>>>()?,
        })
    }
}

impl<'a, T> Quote<'a, T> {
    pub(crate) fn from_sexpr(
        source: &'a Sexpr<'a, T>,
        body: &'a Sexpr<'a, T>,
    ) -> Result<Self, Error<'a, T>> {
        Ok(Self {
            source,
            body: Box::new(Ast::from_sexpr(body)?),
        })
    }
}
