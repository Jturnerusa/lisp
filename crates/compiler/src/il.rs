use std::collections::BTreeSet;
use vm::{Arity, UpValue};

use crate::{
    ast::{self, Ast},
    environment::{self, Environment},
};

#[derive(Clone, Debug)]
pub struct Error<'a> {
    source: &'a Ast<'a>,
    message: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Type {
    List(Box<Type>),
    Cons,
    Function,
    Symbol,
    String,
    Char,
    Int,
    Bool,
    Nil,
    Union(BTreeSet<Type>),
}

#[derive(Clone, Debug)]
pub(crate) enum Il<'a> {
    DefMacro(DefMacro<'a>),
    Lambda(Lambda<'a>),
    VarRef(VarRef<'a>),
}

#[derive(Clone, Debug)]
pub(crate) enum VarRef<'a> {
    Local {
        source: &'a Ast<'a>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    UpValue {
        source: &'a Ast<'a>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    Global {
        source: &'a Ast<'a>,
        name: String,
        r#type: Option<Type>,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct Parameter<'a> {
    pub source: &'a Ast<'a>,
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub(crate) enum Parameters<'a> {
    Nary(Vec<Parameter<'a>>),
    Variadic(Vec<Parameter<'a>>),
}

#[derive(Clone, Debug)]
pub(crate) struct DefMacro<'a> {
    pub source: &'a Ast<'a>,
    pub name: String,
    pub parameters: Parameters<'a>,
    pub body: Vec<Il<'a>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Lambda<'a> {
    pub source: &'a Ast<'a>,
    pub parameters: Parameters<'a>,
    pub r#type: Option<Type>,
    pub arity: Arity,
    pub upvalues: Vec<UpValue>,
    pub body: Vec<Il<'a>>,
}

#[derive(Clone, Debug)]
pub(crate) enum ArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub(crate) struct ArithmeticOperation<'a> {
    pub source: &'a Ast<'a>,
    pub operator: ArithmeticOperator,
    pub lhs: Box<Il<'a>>,
    pub rhs: Box<Il<'a>>,
}

pub(crate) struct Compiler {
    environment: Environment,
}

impl<'a> Il<'a> {
    pub(crate) fn source_ast(&self) -> &Ast<'a> {
        match self {
            Self::DefMacro(DefMacro { source, .. })
            | Self::Lambda(Lambda { source, .. })
            | Self::VarRef(VarRef::Local { source, .. })
            | Self::VarRef(VarRef::UpValue { source, .. })
            | Self::VarRef(VarRef::Global { source, .. }) => source,
        }
    }
}

impl Type {
    pub(crate) fn from_ast(ast: &ast::Type) -> Result<Self, ()> {
        Ok(match ast {
            ast::Type::Composite(composite) => match composite.as_slice() {
                [ast::Type::Scalar(t), types @ ..] if t == "union" => Type::Union(
                    types
                        .iter()
                        .map(Type::from_ast)
                        .collect::<Result<BTreeSet<_>, ()>>()?,
                ),
                _ => return Err(()),
            },
            ast::Type::Scalar(scalar) => match scalar.as_str() {
                "cons" => Type::Cons,
                "function" => Type::Function,
                "symbol" => Type::Symbol,
                "string" => Type::String,
                "char" => Type::Char,
                "int" => Type::Int,
                "bool" => Type::Bool,
                "nil" => Type::Nil,
                _ => return Err(()),
            },
        })
    }
}

impl<'a> Parameter<'a> {
    pub fn from_ast(source: &'a Ast<'a>, parameter: &'a ast::Parameter) -> Result<Self, ()> {
        Ok(Self {
            source,
            name: parameter.name.clone(),
            r#type: match parameter.r#type.as_ref().map(Type::from_ast) {
                Some(Ok(t)) => Some(t),
                Some(Err(_)) => return Err(()),
                None => None,
            },
        })
    }
}

impl<'a> Parameters<'a> {
    pub fn from_ast(source: &'a Ast<'a>, parameters: &'a ast::Parameters) -> Result<Self, ()> {
        Ok(match parameters {
            ast::Parameters::Normal(params) => Parameters::Nary(
                params
                    .iter()
                    .map(|param| Parameter::from_ast(source, param))
                    .collect::<Result<Vec<Parameter>, ()>>()?,
            ),
            ast::Parameters::Rest(params, rest) => Parameters::Variadic(
                params
                    .iter()
                    .chain(std::iter::once(rest))
                    .map(|param| Parameter::from_ast(source, param))
                    .collect::<Result<Vec<Parameter>, _>>()?,
            ),
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = Parameter> + '_ {
        self.into_iter()
    }
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
        }
    }

    pub fn compile<'a>(&mut self, ast: &'a Ast<'a>) -> Result<Il<'a>, Error<'a>> {
        match ast {
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
            _ => todo!(),
        }
    }

    fn compile_variable_reference<'a>(
        &mut self,
        source: &'a Ast<'a>,
        variable: &ast::Variable<'a>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(match self.environment.resolve(variable.name.as_str()) {
            Some(environment::Variable::Local(index, r#type)) => Il::VarRef(VarRef::Local {
                source,
                name: variable.name.clone(),
                index,
                r#type,
            }),
            Some(environment::Variable::Upvalue(index, r#type)) => Il::VarRef(VarRef::UpValue {
                source,
                name: variable.name.clone(),
                index,
                r#type,
            }),
            Some(environment::Variable::Global(r#type)) => Il::VarRef(VarRef::Global {
                source,
                name: variable.name.clone(),
                r#type,
            }),
            None => {
                return Err(Error {
                    source,
                    message: format!("unknown variable referenced: {}", variable.name),
                })
            }
        })
    }

    fn compile_lambda<'a>(
        &mut self,
        source: &'a Ast<'a>,
        lambda: &'a ast::Lambda<'a>,
    ) -> Result<Il<'a>, Error<'a>> {
        let arity = match &lambda.parameters {
            ast::Parameters::Normal(_) if lambda.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(lambda.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(lambda.parameters.len()),
        };

        let parameters = Parameters::from_ast(source, &lambda.parameters).map_err(|_| Error {
            source,
            message: "failed to compile parameters".to_string(),
        })?;

        self.environment
            .push_scope(parameters.iter().map(|param| (param.name, param.r#type)));

        let body = lambda
            .body
            .iter()
            .map(|ast| self.compile(ast))
            .collect::<Result<Vec<Il>, Error>>()?;

        let upvalues = self.environment.upvalues().collect::<Vec<UpValue>>();

        let r#type = match lambda.r#type.as_ref().map(Type::from_ast) {
            Some(Ok(t)) => Some(t),
            Some(Err(_)) => {
                return Err(Error {
                    source,
                    message: "failed to compile type".to_string(),
                })
            }
            None => None,
        };

        self.environment.pop_scope();

        Ok(Il::Lambda(Lambda {
            source,
            parameters,
            r#type,
            arity,
            upvalues,
            body,
        }))
    }
}

impl<'a> IntoIterator for &'a Parameters<'a> {
    type Item = Parameter<'a>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Parameters::Nary(params) | Parameters::Variadic(params) => params.iter().cloned(),
        }
    }
}
