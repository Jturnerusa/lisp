mod checker;
use crate::ast;
pub use checker::Checker;
use core::fmt;
use std::collections::{HashMap, HashSet};

use error::FileSpan;
use unwrap_enum::{EnumAs, EnumIs};

pub type TypeId = usize;

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum MaybeUnknownType {
    Known(Type),
    Unknown,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Error {
    InvalidType(FileSpan),
    Unification {
        message: String,
        span: FileSpan,
        a: MaybeUnknownType,
        b: MaybeUnknownType,
    },
    DefType(FileSpan),
    Failed(FileSpan),
    Annotation(FileSpan),
    Expected {
        span: FileSpan,
        expected: Type,
        received: Type,
    },
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
#[allow(clippy::enum_variant_names)]
pub enum Type {
    DefType {
        name: String,
        parameters: Vec<Type>,
    },
    GenericFunction {
        parameters: Vec<Type>,
        rest: Option<Box<Type>>,
        r#return: Box<Type>,
    },
    Function {
        parameters: Vec<Type>,
        rest: Option<Box<Type>>,
        r#return: Box<Type>,
    },
    List(Box<Type>),
    Cons(Box<Type>, Box<Type>),
    Generic(String),
    Symbol,
    String,
    Char,
    Int,
    Bool,
    Nil,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
#[allow(clippy::enum_variant_names)]
pub enum TypeInfo {
    DefType {
        name: String,
        parameters: Parameters,
    },
    Function {
        parameters: Parameters,
        rest: Rest,
        r#return: TypeId,
    },
    List(TypeId),
    Cons(TypeId, TypeId),
    Generic(String),
    String,
    Symbol,
    Char,
    Int,
    Bool,
    Nil,
    Ref(TypeId),
    Unknown,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Parameters {
    Unknown,
    Known(Vec<TypeId>),
}

#[derive(Clone, Copy, Debug, EnumAs, EnumIs)]
pub enum Rest {
    Unknown,
    Known(TypeId),
    None,
}

#[derive(Clone, Debug)]
struct Types {
    vars: Vec<TypeInfo>,
}

impl From<Option<Type>> for MaybeUnknownType {
    fn from(value: Option<Type>) -> Self {
        match value {
            Some(value) => Self::Known(value),
            None => Self::Unknown,
        }
    }
}

impl error::Error for Error {
    fn span(&self) -> Option<FileSpan> {
        match self {
            Self::InvalidType(span)
            | Self::Unification { span, .. }
            | Self::DefType(span)
            | Self::Failed(span)
            | Self::Annotation(span)
            | Self::Expected { span, .. } => Some(*span),
        }
    }

    fn message(&self, writer: &mut dyn std::io::Write) {
        match self {
            Self::InvalidType(_) => {
                write!(writer, "invalid type annotation").unwrap();
            }
            Self::Unification { a, b, message, .. } => {
                write!(writer, "{message}\n{a:?} | {b:?}").unwrap();
            }
            Self::DefType(_) => {
                write!(writer, "unknown type").unwrap();
            }
            Self::Failed(_) => write!(writer, "failed to completely solve the type(s)").unwrap(),
            Self::Annotation(_) => {
                write!(writer, "top level functions must be fully annotated").unwrap()
            }
            Self::Expected {
                expected, received, ..
            } => write!(
                writer,
                "body resolved to unexpected type: expected: {expected:?}: received: {received:?}"
            )
            .unwrap(),
        }
    }
}

impl Type {
    fn from_ast(ast: &ast::Type) -> Result<Self, ()> {
        Ok(match ast {
            ast::Type::Composite(composite) => match composite.as_slice() {
                [ast::Type::Scalar(function), parameters @ .., ast::Type::Scalar(arrow), r#return]
                    if function == "fn" && arrow == "->" =>
                {
                    match parameters {
                        [parameters @ .., ast::Type::Scalar(rest), variadic] if rest == "&rest" => {
                            Type::Function {
                                parameters: parameters
                                    .iter()
                                    .map(Type::from_ast)
                                    .collect::<Result<_, _>>()?,
                                rest: Some(Box::new(Type::from_ast(variadic)?)),
                                r#return: Box::new(Type::from_ast(r#return)?),
                            }
                        }
                        _ => Type::Function {
                            parameters: parameters
                                .iter()
                                .map(Type::from_ast)
                                .collect::<Result<_, _>>()?,
                            rest: None,
                            r#return: Box::new(Type::from_ast(r#return)?),
                        },
                    }
                }
                [ast::Type::Scalar(list), inner] if list == "list" => {
                    Type::List(Box::new(Type::from_ast(inner)?))
                }
                [ast::Type::Scalar(quote), ast::Type::Scalar(generic)] if quote == "quote" => {
                    Type::Generic(generic.clone())
                }
                [ast::Type::Scalar(deftype), parameters @ ..] => Type::DefType {
                    name: deftype.clone(),
                    parameters: parameters
                        .iter()
                        .map(Type::from_ast)
                        .collect::<Result<Vec<_>, _>>()?,
                },
                _ => return Err(()),
            },
            ast::Type::Scalar(t) if t == "symbol" => Type::Symbol,
            ast::Type::Scalar(t) if t == "string" => Type::String,
            ast::Type::Scalar(t) if t == "char" => Type::Char,
            ast::Type::Scalar(t) if t == "int" => Type::Int,
            ast::Type::Scalar(t) if t == "bool" => Type::Bool,
            ast::Type::Scalar(t) if t == "nil" => Type::Nil,
            ast::Type::Scalar(t) => Type::DefType {
                name: t.clone(),
                parameters: Vec::new(),
            },
            _ => return Err(()),
        })
    }

    pub(crate) fn has_generics(&self) -> bool {
        match self {
            Self::DefType { parameters, .. } => parameters.iter().any(Type::has_generics),
            Self::GenericFunction { .. } => true,
            Self::Function {
                parameters,
                rest,
                r#return,
            } => {
                parameters.iter().any(Type::has_generics)
                    || match rest {
                        Some(t) => t.has_generics(),
                        _ => false,
                    }
                    || r#return.has_generics()
            }
            Self::List(inner) => inner.has_generics(),
            Self::Cons(car, cdr) => car.has_generics() || cdr.has_generics(),
            Self::Generic(_) => true,
            _ => false,
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Type::DefType {
                    name: name_a,
                    parameters: parameters_a,
                },
                Type::DefType {
                    name: name_b,
                    parameters: parameters_b,
                },
            ) => name_a == name_b && parameters_a == parameters_b,
            (
                Type::Function {
                    parameters: parameters_a,
                    rest: rest_a,
                    r#return: return_a,
                },
                Type::Function {
                    parameters: parameters_b,
                    rest: rest_b,
                    r#return: return_b,
                },
            ) => parameters_a == parameters_b && rest_a == rest_b && return_a == return_b,
            (Type::List(a), Type::List(b)) => a == b,
            (Type::Cons(a, b), Type::Cons(c, d)) => a == c && b == d,
            (Type::Generic(a), Type::Generic(b)) => a == b,
            (Type::Symbol, Type::Symbol) => true,
            (Type::String, Type::String) => true,
            (Type::Char, Type::Char) => true,
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Nil, Type::Nil) => true,
            (Type::List(_), Type::Nil) => true,
            (Type::Nil, Type::List(_)) => true,
            _ => false,
        }
    }
}

impl Types {
    pub(crate) fn new() -> Self {
        Self { vars: Vec::new() }
    }

    pub(crate) fn insert(&mut self, type_info: TypeInfo) -> TypeId {
        self.vars.push(type_info);
        self.vars.len() - 1
    }

    pub(crate) fn construct(&self, id: TypeId) -> Option<Type> {
        Some(match self.vars[id].clone() {
            TypeInfo::DefType { name, parameters } => {
                let parameters = match parameters {
                    Parameters::Known(parameters) => parameters
                        .iter()
                        .cloned()
                        .map(|parameter| self.construct(parameter))
                        .collect::<Option<_>>()?,
                    Parameters::Unknown => return None,
                };
                Type::DefType { name, parameters }
            }
            TypeInfo::Function {
                parameters,
                rest,
                r#return,
            } => Type::Function {
                parameters: match parameters {
                    Parameters::Known(parameters) => parameters
                        .iter()
                        .map(|parameter| self.construct(*parameter))
                        .collect::<Option<_>>()?,
                    Parameters::Unknown => return None,
                },
                rest: match rest {
                    Rest::Unknown => return None,
                    Rest::Known(id) => Some(Box::new(self.construct(id)?)),
                    Rest::None => None,
                },
                r#return: Box::new(self.construct(r#return)?),
            },
            TypeInfo::List(inner) => Type::List(Box::new(self.construct(inner)?)),
            TypeInfo::Cons(car, cdr) => Type::Cons(
                Box::new(self.construct(car)?),
                Box::new(self.construct(cdr)?),
            ),
            TypeInfo::Generic(generic) => Type::Generic(generic),
            TypeInfo::Symbol => Type::Symbol,
            TypeInfo::String => Type::String,
            TypeInfo::Char => Type::Char,
            TypeInfo::Int => Type::Int,
            TypeInfo::Bool => Type::Bool,
            TypeInfo::Nil => Type::Nil,
            TypeInfo::Ref(id) => self.construct(id)?,
            _ => return None,
        })
    }

    pub(crate) fn unify(&mut self, a: TypeId, b: TypeId) -> Result<(), ()> {
        match (self.vars[a].clone(), self.vars[b].clone()) {
            _ if a == b => Ok(()),
            (
                TypeInfo::DefType {
                    name: name_a,
                    parameters: parameters_a,
                },
                TypeInfo::DefType {
                    name: name_b,
                    parameters: parameters_b,
                },
            ) if name_a == name_b => {
                match (parameters_a.clone(), parameters_b.clone()) {
                    (Parameters::Unknown, Parameters::Known(parameters)) => {
                        self.vars.insert(
                            a,
                            TypeInfo::DefType {
                                name: name_a.clone(),
                                parameters: Parameters::Known(parameters),
                            },
                        );
                    }
                    (Parameters::Known(parameters), Parameters::Unknown) => {
                        self.vars.insert(
                            b,
                            TypeInfo::DefType {
                                name: name_a.clone(),
                                parameters: Parameters::Known(parameters),
                            },
                        );
                    }
                    (Parameters::Known(parameters_a), Parameters::Known(parameters_b)) => {
                        for (a, b) in parameters_a.iter().zip(parameters_b.iter()) {
                            self.unify(*a, *b)?;
                        }
                    }
                    _ => (),
                }
                Ok(())
            }
            (
                TypeInfo::Function {
                    parameters: parameters_a,
                    rest: rest_a,
                    r#return: return_a,
                },
                TypeInfo::Function {
                    parameters: parameters_b,
                    rest: rest_b,
                    r#return: return_b,
                },
            ) => {
                match (parameters_a.clone(), parameters_b.clone()) {
                    (Parameters::Unknown, Parameters::Known(parameters)) => {
                        let new_parameters: Vec<TypeId> = (0..parameters.len())
                            .map(|_| self.insert(TypeInfo::Unknown))
                            .collect();
                        for (a, b) in new_parameters.iter().zip(parameters.iter()) {
                            self.unify(*a, *b)?;
                        }
                        self.vars[a] = TypeInfo::Function {
                            parameters: Parameters::Known(new_parameters),
                            rest: rest_a,
                            r#return: return_a,
                        };
                    }
                    (Parameters::Known(parameters), Parameters::Unknown) => {
                        let new_parameters: Vec<TypeId> = (0..parameters.len())
                            .map(|_| self.insert(TypeInfo::Unknown))
                            .collect();
                        for (a, b) in new_parameters.iter().zip(parameters.iter()) {
                            self.unify(*a, *b)?;
                        }
                        self.vars[b] = TypeInfo::Function {
                            parameters: Parameters::Known(new_parameters),
                            rest: rest_a,
                            r#return: return_a,
                        };
                    }
                    (Parameters::Known(parameters_a), Parameters::Known(parameters_b))
                        if parameters_a.len() == parameters_b.len() =>
                    {
                        for (a, b) in parameters_a.iter().zip(parameters_b.iter()) {
                            self.unify(*a, *b)?;
                        }
                    }
                    (Parameters::Known(parameters_a), Parameters::Known(parameters_b))
                        if parameters_a.len() != parameters_b.len() =>
                    {
                        return Err(())
                    }
                    _ => (),
                }

                match (rest_a, rest_b) {
                    (Rest::Unknown, Rest::Known(id)) => {
                        let new_rest = self.insert(TypeInfo::Unknown);
                        self.unify(new_rest, id)?;
                        self.vars[a] = TypeInfo::Function {
                            parameters: parameters_a,
                            rest: Rest::Known(new_rest),
                            r#return: return_a,
                        };
                    }
                    (Rest::Known(id), Rest::Unknown) => {
                        let new_rest = self.insert(TypeInfo::Unknown);
                        self.unify(new_rest, id)?;
                        self.vars[b] = TypeInfo::Function {
                            parameters: parameters_b,
                            rest: Rest::Known(new_rest),
                            r#return: return_b,
                        };
                    }
                    (Rest::Known(a), Rest::Known(b)) => {
                        self.unify(a, b)?;
                    }
                    (Rest::None, Rest::None) => (),
                    _ => return Err(()),
                }

                self.unify(return_a, return_b)?;

                Ok(())
            }
            (TypeInfo::List(a), TypeInfo::List(b)) => self.unify(a, b),
            (TypeInfo::Cons(a, b), TypeInfo::Cons(c, d)) => {
                self.unify(a, c).and_then(|()| self.unify(b, d))
            }
            (TypeInfo::Generic(a), TypeInfo::Generic(b)) if a == b => Ok(()),
            (TypeInfo::String, TypeInfo::String) => Ok(()),
            (TypeInfo::Symbol, TypeInfo::Symbol) => Ok(()),
            (TypeInfo::String, TypeInfo::Symbol) => Ok(()),
            (TypeInfo::Char, TypeInfo::Char) => Ok(()),
            (TypeInfo::Int, TypeInfo::Int) => Ok(()),
            (TypeInfo::Bool, TypeInfo::Bool) => Ok(()),
            (TypeInfo::Nil, TypeInfo::Nil) => Ok(()),
            (TypeInfo::Nil, TypeInfo::List(_)) => Ok(()),
            (TypeInfo::List(_), TypeInfo::Nil) => Ok(()),
            (TypeInfo::Ref(a), _) => self.unify(a, b),
            (_, TypeInfo::Ref(b)) => self.unify(a, b),
            (TypeInfo::Unknown, b) if !b.is_unknown() => {
                self.vars[a] = b;
                Ok(())
            }
            (a, TypeInfo::Unknown) if !a.is_unknown() => {
                self.vars[b] = a;
                Ok(())
            }
            (TypeInfo::Unknown, TypeInfo::Unknown) => Ok(()),
            _ => Err(()),
        }
    }

    fn insert_concrete_type(&mut self, r#type: Type) -> TypeId {
        match r#type {
            Type::DefType { name, parameters } => {
                let parameters = parameters
                    .iter()
                    .cloned()
                    .map(|parameter| self.insert_concrete_type(parameter))
                    .collect::<Vec<_>>();
                self.insert(TypeInfo::DefType {
                    name,
                    parameters: Parameters::Known(parameters),
                })
            }
            Type::GenericFunction {
                parameters,
                rest,
                r#return,
            } => {
                let parameters = parameters
                    .iter()
                    .cloned()
                    .map(|parameter| self.insert_concrete_type(parameter))
                    .collect();
                let rest = match rest.map(|rest| self.insert_concrete_type(*rest)) {
                    Some(r#rest) => Rest::Known(r#rest),
                    None => Rest::None,
                };
                let r#return = self.insert_concrete_type(*r#return);
                let function = self.insert(TypeInfo::Function {
                    parameters: Parameters::Known(parameters),
                    rest,
                    r#return,
                });
                self.instantiate(function, &mut HashMap::new())
            }
            Type::Function {
                parameters,
                rest,
                r#return,
            } => {
                let parameters = parameters
                    .iter()
                    .cloned()
                    .map(|parameter| self.insert_concrete_type(parameter))
                    .collect();
                let rest = match rest.map(|rest| self.insert_concrete_type(*rest)) {
                    Some(r#rest) => Rest::Known(r#rest),
                    None => Rest::None,
                };
                let r#return = self.insert_concrete_type(*r#return);
                self.insert(TypeInfo::Function {
                    parameters: Parameters::Known(parameters),
                    rest,
                    r#return,
                })
            }
            Type::List(inner) => {
                let inner = self.insert_concrete_type(*inner);
                self.insert(TypeInfo::List(inner))
            }
            Type::Cons(car, cdr) => {
                let car = self.insert_concrete_type(*car);
                let cdr = self.insert_concrete_type(*cdr);
                self.insert(TypeInfo::Cons(car, cdr))
            }
            Type::Generic(generic) => self.insert(TypeInfo::Generic(generic)),
            Type::Symbol => self.insert(TypeInfo::Symbol),
            Type::String => self.insert(TypeInfo::String),
            Type::Char => self.insert(TypeInfo::Char),
            Type::Int => self.insert(TypeInfo::Int),
            Type::Bool => self.insert(TypeInfo::Bool),
            Type::Nil => self.insert(TypeInfo::Nil),
        }
    }

    pub fn instantiate(&mut self, id: TypeId, subs: &mut HashMap<String, TypeId>) -> TypeId {
        match self.vars[id].clone() {
            TypeInfo::Function {
                parameters,
                rest,
                r#return,
            } => {
                let parameters = match parameters {
                    Parameters::Known(parameters) => Parameters::Known(
                        parameters
                            .iter()
                            .map(|parameter| self.instantiate(*parameter, subs))
                            .collect(),
                    ),
                    parameters => parameters,
                };
                let rest = match rest {
                    Rest::Known(id) => Rest::Known(self.instantiate(id, subs)),
                    rest => rest,
                };
                let r#return = self.instantiate(r#return, subs);
                self.insert(TypeInfo::Function {
                    parameters,
                    rest,
                    r#return,
                })
            }
            TypeInfo::List(inner) => {
                let inner = self.instantiate(inner, subs);
                self.insert(TypeInfo::List(inner))
            }
            TypeInfo::Generic(generic) if subs.contains_key(generic.as_str()) => {
                subs[generic.as_str()]
            }
            TypeInfo::Generic(generic) => {
                let id = self.insert(TypeInfo::Unknown);
                subs.insert(generic.clone(), id);
                id
            }
            TypeInfo::Cons(..) => todo!(),
            TypeInfo::Ref(id) => self.instantiate(id, subs),
            _ => id,
        }
    }

    pub(crate) fn debug_typeid(&self, id: TypeId, seen: &mut HashSet<TypeId>) -> String {
        if seen.contains(&id) {
            return String::new();
        }

        seen.insert(id);

        let result = match self.vars[id].clone() {
            TypeInfo::Function {
                parameters,
                r#return,
                ..
            } => {
                let mut buff = String::new();
                buff += "fn -> ";
                match parameters {
                    Parameters::Known(parameters) => {
                        for parameter in parameters {
                            buff += self.debug_typeid(parameter, seen).as_str();
                            buff += " ";
                        }
                    }
                    Parameters::Unknown => buff += "unknown ",
                }
                buff += self.debug_typeid(r#return, seen).as_str();
                buff
            }
            TypeInfo::List(inner) => format!("List({})", self.debug_typeid(inner, seen)),
            TypeInfo::Generic(generic) => format!("Generic({generic})"),
            TypeInfo::Symbol => "Symbol".to_string(),
            TypeInfo::String => "String".to_string(),
            TypeInfo::Char => "Char".to_string(),
            TypeInfo::Int => "Int".to_string(),
            TypeInfo::Bool => "Bool".to_string(),
            TypeInfo::Nil => "Nil".to_string(),
            TypeInfo::Unknown => "Unknown".to_string(),
            _ => todo!(),
        };

        result
    }
}