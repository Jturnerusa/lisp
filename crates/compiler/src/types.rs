use std::collections::HashMap;

use error::FileSpan;
use unwrap_enum::{EnumAs, EnumIs};
use vm::UpValue;

use crate::{
    ast::{self},
    tree::{self, Il},
};

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

#[derive(Clone, Debug)]
struct Scope {
    locals: Vec<TypeId>,
    upvalues: Vec<UpValue>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
enum Variant {
    Struct(String, Type),
    Enum(String),
}

#[derive(Clone, Debug)]
pub struct Checker {
    types: Types,
    scopes: Vec<Scope>,
    globals: HashMap<String, Type>,
    deftypes: HashMap<String, String>,
    deftype_variants: HashMap<String, (usize, Variant)>,
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
                        let refs = parameters
                            .iter()
                            .map(|p| self.insert(TypeInfo::Ref(*p)))
                            .collect();
                        self.vars.insert(
                            a,
                            TypeInfo::Function {
                                parameters: Parameters::Known(refs),
                                rest: rest_a,
                                r#return: return_a,
                            },
                        );
                    }
                    (Parameters::Known(parameters), Parameters::Unknown) => {
                        let refs = parameters
                            .iter()
                            .map(|p| self.insert(TypeInfo::Ref(*p)))
                            .collect();
                        self.vars.insert(
                            b,
                            TypeInfo::Function {
                                parameters: Parameters::Known(refs),
                                rest: rest_a,
                                r#return: return_a,
                            },
                        );
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
                        let r#ref = self.insert(TypeInfo::Ref(id));
                        self.vars.insert(
                            a,
                            TypeInfo::Function {
                                parameters: parameters_a,
                                rest: Rest::Known(r#ref),
                                r#return: return_a,
                            },
                        );
                    }
                    (Rest::Known(id), Rest::Unknown) => {
                        let r#ref = self.insert(TypeInfo::Ref(id));
                        self.vars.insert(
                            b,
                            TypeInfo::Function {
                                parameters: parameters_b,
                                rest: Rest::Known(r#ref),
                                r#return: return_b,
                            },
                        );
                    }
                    (Rest::Known(a), Rest::Known(b)) => {
                        self.unify(a, b)?;
                    }
                    _ => (),
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
}

impl Checker {
    pub fn new() -> Self {
        Self {
            types: Types::new(),
            scopes: Vec::new(),
            globals: HashMap::new(),
            deftypes: HashMap::new(),
            deftype_variants: HashMap::new(),
        }
    }

    pub fn deftype(&mut self, deftype: &ast::DefType) -> Result<(), Error> {
        Ok(())
    }

    pub fn check_def(&mut self, def: &tree::Def) -> Result<(), Error> {
        match &def.parameter.r#type.as_ref().map(Type::from_ast) {
            Some(Ok(r#type)) if r#type.is_function() => {
                self.globals.insert(
                    def.parameter.name.clone(),
                    match r#type {
                        Type::Function {
                            parameters,
                            rest,
                            r#return,
                        } if r#type.has_generics() => Type::GenericFunction {
                            parameters: parameters.clone(),
                            rest: rest.clone(),
                            r#return: r#return.clone(),
                        },
                        _ => r#type.clone(),
                    },
                );

                let (parameters, r#return) = match r#type {
                    Type::GenericFunction {
                        parameters,
                        r#return,
                        ..
                    } => (parameters, r#return),
                    Type::Function {
                        parameters,
                        r#return,
                        ..
                    } => (parameters, r#return),
                    _ => unreachable!(),
                };

                let Il::Lambda(lambda) = &*def.body else {
                    todo!()
                };

                let id = self.check_lambda(lambda, Some(parameters.clone()))?;

                match self.types.construct(id) {
                    Some(Type::Function { r#return: r, .. }) if *r == **r#return => Ok(()),
                    Some(Type::Function { r#return: r, .. }) => Err(Error::Expected {
                        span: def.span,
                        expected: *r#return.clone(),
                        received: *r,
                    }),
                    None => Err(Error::Failed(def.span)),
                    _ => unreachable!(),
                }
            }
            Some(Ok(r#type)) => {
                self.globals
                    .insert(def.parameter.name.clone(), r#type.clone());

                let id = self.check_tree(&def.body)?;

                match self.types.construct(id) {
                    Some(t) if &t == r#type => Ok(()),
                    Some(_) => todo!(),
                    None => todo!(),
                }
            }
            Some(Err(())) => todo!(),
            None => todo!(),
        }
    }

    fn check_lambda(
        &mut self,
        lambda: &tree::Lambda,
        parameters: Option<Vec<Type>>,
    ) -> Result<TypeId, Error> {
        let parameters: Vec<TypeId> = if let Some(parameters) = parameters {
            parameters
                .iter()
                .map(|parameter| self.types.insert_concrete_type(parameter.clone()))
                .collect()
        } else {
            (0..lambda.parameters.len())
                .map(|_| self.types.insert(TypeInfo::Unknown))
                .collect()
        };

        self.scopes.push(Scope {
            locals: parameters.clone(),
            upvalues: lambda.upvalues.clone(),
        });

        let r#return = match lambda.r#type.as_ref().map(Type::from_ast) {
            Some(Ok(t)) => self.types.insert_concrete_type(t),
            Some(Err(())) => return Err(Error::InvalidType(lambda.span)),
            None => self.types.insert(TypeInfo::Unknown),
        };

        for expr in lambda.body.iter().take(lambda.body.len() - 1) {
            self.check_tree(expr)?;
        }

        let last = self.check_tree(lambda.body.last().unwrap())?;

        self.scopes.pop().unwrap();

        let Ok(()) = self.types.unify(r#return, last) else {
            return Err(Error::Unification {
                message: "failed to unify function return with final expression".to_string(),
                span: lambda.span,
                a: MaybeUnknownType::from(self.types.construct(r#return)),
                b: MaybeUnknownType::from(self.types.construct(last)),
            });
        };

        Ok(self.types.insert(TypeInfo::Function {
            parameters: Parameters::Known(parameters),
            rest: Rest::None,
            r#return,
        }))
    }

    fn check_fncall(&mut self, fncall: &tree::FnCall) -> Result<TypeId, Error> {
        let fncall_function = self.check_tree(&fncall.function)?;

        let parameters = fncall
            .args
            .iter()
            .map(|arg| self.check_tree(arg))
            .collect::<Result<Vec<_>, _>>()?;
        let r#return = self.types.insert(TypeInfo::Unknown);
        let function = self.types.insert(TypeInfo::Function {
            parameters: Parameters::Known(parameters),
            rest: Rest::None,
            r#return,
        });

        let Ok(()) = self.types.unify(function, fncall_function) else {
            return Err(Error::Unification {
                message: "failed to unify fncall".to_string(),
                span: fncall.span,
                a: MaybeUnknownType::from(self.types.construct(function)),
                b: MaybeUnknownType::from(self.types.construct(fncall_function)),
            });
        };

        Ok(r#return)
    }

    fn check_tree(&mut self, tree: &Il) -> Result<TypeId, Error> {
        match tree {
            Il::Lambda(lambda) => self.check_lambda(lambda, None),
            Il::Set(set) => self.check_set(set),
            Il::FnCall(fncall) => self.check_fncall(fncall),
            Il::If(r#if) => self.check_if(r#if),
            Il::ArithmeticOperation(op) => self.check_aritmetic_op(op),
            Il::ComparisonOperation(op) => self.check_comparison_op(op),
            Il::List(list) => self.check_list(list),
            Il::Cons(cons) => self.check_cons(cons),
            Il::Car(car) => self.check_car(car),
            Il::Cdr(cdr) => self.check_cdr(cdr),
            Il::IsType(is_type) => self.check_is_type(is_type),
            Il::MakeType(make_type) => self.check_make_type(make_type),
            Il::IfLet(if_let) => self.check_if_let(if_let),
            Il::VarRef(varref) => Ok(self.check_varref(varref)),
            Il::Constant(constant) => self.check_constant(constant),
            _ => panic!("unexpected tree il node: {tree:?}"),
        }
    }

    fn check_set(&mut self, set: &tree::Set) -> Result<TypeId, Error> {
        let body = self.check_tree(&set.body)?;
        let var = self.check_varref(&set.target);

        let Ok(()) = self.types.unify(body, var) else {
            todo!()
        };

        Ok(var)
    }

    fn check_aritmetic_op(&mut self, op: &tree::ArithmeticOperation) -> Result<TypeId, Error> {
        let lhs = self.check_tree(&op.lhs)?;
        let rhs = self.check_tree(&op.rhs)?;
        let int = self.types.insert_concrete_type(Type::Int);

        let Ok(()) = self.types.unify(lhs, int) else {
            return Err(Error::Unification {
                message: "failed to unify lhs with integer".to_string(),
                span: op.span,
                a: MaybeUnknownType::from(self.types.construct(lhs)),
                b: MaybeUnknownType::from(self.types.construct(rhs)),
            });
        };

        let Ok(()) = self.types.unify(rhs, int) else {
            return Err(Error::Unification {
                message: "failed to unify rhs with integer".to_string(),
                span: op.span,
                a: MaybeUnknownType::from(self.types.construct(lhs)),
                b: MaybeUnknownType::from(self.types.construct(rhs)),
            });
        };

        Ok(int)
    }

    fn check_comparison_op(&mut self, op: &tree::ComparisonOperation) -> Result<TypeId, Error> {
        let lhs = self.check_tree(&op.lhs)?;
        let rhs = self.check_tree(&op.rhs)?;
        let bool = self.types.insert(TypeInfo::Bool);

        let Ok(()) = self.types.unify(lhs, rhs) else {
            todo!()
        };

        Ok(bool)
    }

    fn check_if(&mut self, r#if: &tree::If) -> Result<TypeId, Error> {
        let predicate = self.check_tree(&r#if.predicate)?;
        let then = self.check_tree(&r#if.then)?;
        let r#else = self.check_tree(&r#if.r#else)?;
        let bool = self.types.insert_concrete_type(Type::Bool);

        let Ok(()) = self.types.unify(predicate, bool) else {
            return Err(Error::Unification {
                message: "failed to unify preficate with bool".to_string(),
                span: r#if.span,
                a: MaybeUnknownType::from(self.types.construct(predicate)),
                b: MaybeUnknownType::from(self.types.construct(bool)),
            });
        };

        let Ok(()) = self.types.unify(then, r#else) else {
            return Err(Error::Unification {
                message: "failed to unify then with else".to_string(),
                span: r#if.span,
                a: MaybeUnknownType::from(self.types.construct(then)),
                b: MaybeUnknownType::from(self.types.construct(r#else)),
            });
        };

        Ok(then)
    }

    fn check_apply(&mut self, apply: &tree::Apply) -> Result<TypeId, Error> {
        let apply_function = self.check_tree(&apply.function)?;
        let apply_list = self.check_tree(&apply.list)?;

        let r#return = self.types.insert(TypeInfo::Unknown);
        let rest = self.types.insert(TypeInfo::Unknown);
        let function = self.types.insert(TypeInfo::Function {
            parameters: Parameters::Unknown,
            rest: Rest::Known(rest),
            r#return,
        });
        let list = self.types.insert(TypeInfo::List(r#return));

        let Ok(()) = self.types.unify(apply_function, function) else {
            todo!()
        };

        let Ok(()) = self.types.unify(apply_list, list) else {
            todo!()
        };

        Ok(r#return)
    }

    fn check_list(&mut self, list: &tree::List) -> Result<TypeId, Error> {
        let exprs = list
            .exprs
            .iter()
            .map(|expr| self.check_tree(expr))
            .collect::<Result<Vec<_>, _>>()?;

        let inner = self.types.insert(TypeInfo::Unknown);
        let list = self.types.insert(TypeInfo::List(inner));

        for expr in &exprs {
            let Ok(()) = self.types.unify(inner, *expr) else {
                todo!()
            };
        }

        Ok(list)
    }

    fn check_cons(&mut self, cons: &tree::Cons) -> Result<TypeId, Error> {
        let lhs = self.check_tree(&cons.lhs)?;
        let rhs = self.check_tree(&cons.rhs)?;
        let rhs_inner = self.types.insert(TypeInfo::Unknown);
        let list = self.types.insert(TypeInfo::List(rhs_inner));
        let r#return = self.types.insert(TypeInfo::Unknown);

        let Ok(()) = self.types.unify(list, rhs) else {
            return Err(Error::Unification {
                message: "failed to unify rhs with list".to_string(),
                span: cons.span,
                a: MaybeUnknownType::from(self.types.construct(list)),
                b: MaybeUnknownType::from(self.types.construct(rhs)),
            });
        };

        let Ok(()) = self.types.unify(r#return, lhs) else {
            return Err(Error::Unification {
                message: "failed to unify lhs with unknown".to_string(),
                span: cons.span,
                a: MaybeUnknownType::from(self.types.construct(r#return)),
                b: MaybeUnknownType::from(self.types.construct(lhs)),
            });
        };

        let Ok(()) = self.types.unify(r#return, rhs_inner) else {
            return Err(Error::Unification {
                message: "failed to unify lhs with rhs inner type".to_string(),
                span: cons.span,
                a: MaybeUnknownType::from(self.types.construct(r#return)),
                b: MaybeUnknownType::from(self.types.construct(rhs_inner)),
            });
        };

        Ok(self.types.insert(TypeInfo::List(r#return)))
    }

    fn check_car(&mut self, car: &tree::Car) -> Result<TypeId, Error> {
        let body = self.check_tree(&car.body)?;
        let inner = self.types.insert(TypeInfo::Unknown);
        let list = self.types.insert(TypeInfo::List(inner));

        let Ok(()) = self.types.unify(list, body) else {
            return Err(Error::Unification {
                message: "failed to unify body with list".to_string(),
                span: car.span,
                a: MaybeUnknownType::from(self.types.construct(list)),
                b: MaybeUnknownType::from(self.types.construct(body)),
            });
        };

        Ok(inner)
    }

    fn check_cdr(&mut self, cdr: &tree::Cdr) -> Result<TypeId, Error> {
        let body = self.check_tree(&cdr.body)?;
        let inner = self.types.insert(TypeInfo::Unknown);
        let list = self.types.insert(TypeInfo::List(inner));

        let Ok(()) = self.types.unify(list, body) else {
            return Err(Error::Unification {
                message: "failed to unify body with list".to_string(),
                span: cdr.span,
                a: MaybeUnknownType::from(self.types.construct(list)),
                b: MaybeUnknownType::from(self.types.construct(body)),
            });
        };

        Ok(list)
    }

    fn check_is_type(&mut self, is_type: &tree::IsType) -> Result<TypeId, Error> {
        self.check_tree(&is_type.body)?;

        Ok(self.types.insert(TypeInfo::Bool))
    }

    fn check_make_type(&mut self, make_type: &tree::MakeType) -> Result<TypeId, Error> {
        Ok(match self.deftypes.get(make_type.pattern.as_str()) {
            Some(deftype) => self.types.insert(TypeInfo::DefType {
                name: deftype.to_string(),
                parameters: Parameters::Unknown,
            }),
            None => return Err(Error::DefType(make_type.span)),
        })
    }

    fn check_if_let(&mut self, if_let: &tree::IfLet) -> Result<TypeId, Error> {
        let body = self.check_tree(&if_let.body)?;
        let r#return = self.types.insert(TypeInfo::Unknown);

        let (then, r#else) = if if_let.binding.is_some() {
            let variant_index = self.deftype_variants[if_let.pattern.as_str()].0;
            let variant_type = match self.types.construct(body) {
                Some(Type::DefType { parameters, .. }) => parameters[variant_index].clone(),
                _ => todo!(),
            };

            let binding = self.types.insert_concrete_type(variant_type);
            let scope = Scope {
                locals: vec![binding],
                upvalues: if_let.upvalues.clone(),
            };

            self.scopes.push(scope);
            let then = self.check_tree(&if_let.then)?;
            self.scopes.pop().unwrap();

            let r#else = self.check_tree(&if_let.r#else)?;

            (then, r#else)
        } else {
            let then = self.check_tree(&if_let.then)?;
            let r#else = self.check_tree(&if_let.r#else)?;

            (then, r#else)
        };

        let Ok(()) = self.types.unify(r#return, then) else {
            todo!()
        };

        let Ok(()) = self.types.unify(r#return, r#else) else {
            todo!()
        };

        Ok(r#return)
    }

    fn check_varref(&mut self, varref: &tree::VarRef) -> TypeId {
        match varref {
            tree::VarRef::Local { index, .. } => self.scopes.last().unwrap().locals[*index],
            tree::VarRef::UpValue { index, .. } => {
                let upvalue = self.scopes.last().unwrap().upvalues[*index];
                get_upvalue_type(upvalue, self.scopes.iter().rev().skip(1))
            }
            tree::VarRef::Global { name, .. } => self
                .types
                .insert_concrete_type(self.globals[name.as_str()].clone()),
        }
    }

    fn check_constant(&mut self, constant: &tree::Constant) -> Result<TypeId, Error> {
        Ok(match constant {
            tree::Constant::Symbol { .. } => self.types.insert(TypeInfo::Symbol),
            tree::Constant::String { .. } => self.types.insert(TypeInfo::String),
            tree::Constant::Char { .. } => self.types.insert(TypeInfo::Char),
            tree::Constant::Int { .. } => self.types.insert(TypeInfo::Int),
            tree::Constant::Bool { .. } => self.types.insert(TypeInfo::Bool),
            tree::Constant::Nil { .. } => self.types.insert(TypeInfo::Nil),
        })
    }
}

fn get_upvalue_type<'a>(upvalue: UpValue, mut scopes: impl Iterator<Item = &'a Scope>) -> TypeId {
    let scope = scopes.next().unwrap();
    match upvalue {
        UpValue::UpValue(upvalue) => get_upvalue_type(scope.upvalues[upvalue], scopes),
        UpValue::Local(i) => scope.locals[i],
    }
}
