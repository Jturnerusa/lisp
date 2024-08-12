use core::fmt;
use reader::Sexpr;
use std::collections::{BTreeSet, HashMap};
use vm::UpValue;

use crate::{ast, tree};

#[derive(Clone, Debug, thiserror::Error)]
pub enum Error {
    #[error("expected: {expected}, received: {received}\n{sexpr}")]
    Expected {
        expected: Type,
        received: Type,
        sexpr: &'static Sexpr<'static>,
    },
    #[error("unexpected\n{sexpr}")]
    Unexpected { sexpr: &'static Sexpr<'static> },
    #[error("wrong number of arguments\n{sexpr}")]
    Arity { sexpr: &'static Sexpr<'static> },
    #[error("no type found\n{sexpr}")]
    None { sexpr: &'static Sexpr<'static> },
    #[error("invalid type\n{sexpr}")]
    Invalid { sexpr: &'static Sexpr<'static> },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    List(std::boxed::Box<Type>),
    Cons(std::boxed::Box<Type>, std::boxed::Box<Type>),
    Function {
        parameters: Vec<Type>,
        r#return: std::boxed::Box<Type>,
    },
    Symbol,
    String,
    Char,
    Int,
    Bool,
    Nil,
    Union(BTreeSet<Type>),
    Box(std::boxed::Box<Type>),
    Generic {
        name: String,
    },
}

#[derive(Clone, Debug)]
struct Scope {
    locals: Vec<Option<Type>>,
    upvalues: Vec<UpValue>,
}

#[derive(Clone, Debug)]
struct Environment {
    globals: HashMap<String, Option<Type>>,
    scopes: Vec<Scope>,
}

#[derive(Clone, Debug)]
pub struct Checker {
    environments: Vec<Environment>,
}

impl Type {
    pub fn check(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::List(a), Type::List(b)) if a.check(b) => true,
            (Type::Cons(a, b), Type::Cons(c, d)) if a.check(c) && b.check(d) => true,
            (
                Type::Function {
                    parameters: parameters_a,
                    r#return: return_a,
                },
                Type::Function {
                    parameters: parameters_b,
                    r#return: return_b,
                },
            ) if parameters_a
                .iter()
                .zip(parameters_b.iter())
                .all(|(a, b)| a.check(b))
                && return_a.check(return_b) =>
            {
                true
            }
            (Type::Symbol, Type::Symbol) => true,
            (Type::String, Type::String) => true,
            (Type::Char, Type::Char) => true,
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Nil, Type::Nil) => true,
            (Type::Union(a), Type::Union(b)) if a == b => true,
            (Type::Generic { name: a }, Type::Generic { name: b }) if a == b => true,
            _ => false,
        }
    }

    pub fn from_ast(tree: &ast::Type) -> Result<Self, ()> {
        Ok(match tree {
            ast::Type::Composite(types) => match types.as_slice() {
                [ast::Type::Scalar(t), parameters @ .., ast::Type::Scalar(arrow), r#return]
                    if t == "function" && arrow == "->" =>
                {
                    Type::Function {
                        parameters: parameters
                            .iter()
                            .map(Type::from_ast)
                            .collect::<Result<Vec<_>, _>>()?,
                        r#return: std::boxed::Box::new(Type::from_ast(r#return)?),
                    }
                }
                [ast::Type::Scalar(t), inner] if t == "list" => {
                    Type::List(std::boxed::Box::new(Type::from_ast(inner)?))
                }
                [ast::Type::Scalar(t), rest @ ..] if t == "union" => Type::Union(
                    rest.iter()
                        .map(Type::from_ast)
                        .collect::<Result<BTreeSet<_>, _>>()?,
                ),
                [ast::Type::Scalar(t), ast::Type::Scalar(name)] if t == "generic" => {
                    Type::Generic { name: name.clone() }
                }
                _ => return Err(()),
            },
            ast::Type::Scalar(t) if t == "symbol" => Type::Symbol,
            ast::Type::Scalar(t) if t == "string" => Type::String,
            ast::Type::Scalar(t) if t == "int" => Type::Int,
            ast::Type::Scalar(t) if t == "char" => Type::Char,
            ast::Type::Scalar(t) if t == "bool" => Type::Bool,
            ast::Type::Scalar(t) if t == "nil" => Type::Nil,
            _ => return Err(()),
        })
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::List(inner) => write!(f, "List({inner})"),
            Self::Function {
                parameters,
                r#return: ret,
            } => {
                write!(f, "function(")?;
                for (i, parameter) in parameters.iter().enumerate() {
                    write!(f, "{parameter}")?;
                    if i < parameters.len() - 1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")?;
                write!(f, "-> {ret}")
            }
            Self::Cons(lhs, rhs) => write!(f, "cons({lhs}, {rhs})"),
            Self::Symbol => write!(f, "symbol"),
            Self::String => write!(f, "string"),
            Self::Char => write!(f, "char"),
            Self::Int => write!(f, "int"),
            Self::Bool => write!(f, "bool"),
            Self::Nil => write!(f, "nil"),
            Self::Union(inner) => {
                write!(f, "union(")?;
                for (i, t) in inner.iter().enumerate() {
                    write!(f, "{t}")?;
                    if i < inner.len() - 1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
            _ => todo!(),
        }
    }
}

impl Scope {
    fn new() -> Self {
        Self {
            locals: Vec::new(),
            upvalues: Vec::new(),
        }
    }
}

impl Environment {
    fn new() -> Self {
        Environment {
            globals: HashMap::new(),
            scopes: Vec::new(),
        }
    }
}

impl Checker {
    pub fn new() -> Self {
        Self {
            environments: vec![Environment::new()],
        }
    }

    pub fn decl(&mut self, decl: &ast::Decl) -> Result<(), Error> {
        let t = match decl.parameter.r#type.as_ref().map(Type::from_ast) {
            Some(Ok(t)) => t,
            Some(Err(())) => return Err(Error::Invalid { sexpr: decl.source }),
            None => return Err(Error::None { sexpr: decl.source }),
        };

        self.environments
            .last_mut()
            .unwrap()
            .globals
            .insert(decl.parameter.name.clone(), Some(t));

        Ok(())
    }

    fn check(&mut self, tree: &tree::Il) -> Result<Type, Error> {
        match tree {
            tree::Il::Lambda(lambda) => self.check_lambda(lambda),
            tree::Il::If(r#if) => self.check_if(r#if),
            tree::Il::Apply(apply) => self.check_apply(apply),
            tree::Il::Def(def) => self.check_def(def),
            tree::Il::Set(set) => self.check_set(set),
            tree::Il::FnCall(fncall) => self.check_fncall(fncall),
            tree::Il::ArithmeticOperation(op) => self.check_arithmetic_op(op),
            tree::Il::ComparisonOperation(op) => self.check_comparison_op(op),
            tree::Il::List(list) => self.check_list(list),
            tree::Il::Cons(cons) => self.check_cons(cons),
            tree::Il::Car(car) => self.check_car(car),
            tree::Il::Cdr(cdr) => self.check_cdr(cdr),
            tree::Il::VarRef(varref) => self.check_varref(varref),
            tree::Il::Constant(constant) => self.check_constant(constant),
            _ => todo!("{tree:?}"),
        }
    }

    pub fn check_lambda(&mut self, lambda: &tree::Lambda) -> Result<Type, Error> {
        let mut scope = Scope::new();

        let mut parameters = Vec::new();

        for parameter in &lambda.parameters {
            let t = match parameter.r#type.as_ref().map(Type::from_ast) {
                Some(Ok(t)) => t,
                Some(Err(())) => {
                    return Err(Error::Invalid {
                        sexpr: lambda.source.source_sexpr(),
                    })
                }
                None => {
                    return Err(Error::None {
                        sexpr: lambda.source.source_sexpr(),
                    })
                }
            };

            scope.locals.push(Some(t.clone()));
            parameters.push(t);
        }

        for upvalue in &lambda.upvalues {
            scope.upvalues.push(*upvalue);
        }

        self.environments.last_mut().unwrap().scopes.push(scope);

        let r#return = match lambda.r#type.as_ref().map(Type::from_ast) {
            Some(Ok(t)) => t,
            Some(Err(())) => {
                return Err(Error::Invalid {
                    sexpr: lambda.source.source_sexpr(),
                })
            }
            None => {
                return Err(Error::None {
                    sexpr: lambda.source.source_sexpr(),
                })
            }
        };

        for expr in lambda.body.iter().take(lambda.body.len() - 1) {
            self.check(expr)?;
        }

        let last_expr = self.check(lambda.body.last().unwrap())?;

        self.environments.last_mut().unwrap().scopes.pop();

        if r#return.check(&last_expr) {
            Ok(Type::Function {
                parameters,
                r#return: Box::new(r#return),
            })
        } else {
            Err(Error::Unexpected {
                sexpr: lambda.source.source_sexpr(),
            })
        }
    }

    fn check_if(&mut self, r#if: &tree::If) -> Result<Type, Error> {
        let predicate = self.check(&r#if.predicate)?;
        let then = self.check(&r#if.then)?;
        let r#else = self.check(&r#if.r#else)?;

        let Type::Bool = &predicate else {
            return Err(Error::Expected {
                sexpr: r#if.source.source_sexpr(),
                expected: Type::Bool,
                received: predicate,
            });
        };

        if then.check(&r#else) {
            Ok(then)
        } else {
            Err(Error::Expected {
                sexpr: r#if.source.source_sexpr(),
                expected: then,
                received: r#else,
            })
        }
    }

    fn check_apply(&mut self, apply: &tree::Apply) -> Result<Type, Error> {
        let function = self.check(&apply.function)?;
        let list = self.check(&apply.list)?;

        let Type::Function {
            parameters,
            r#return,
        } = function
        else {
            return Err(Error::Unexpected {
                sexpr: apply.source.source_sexpr(),
            });
        };

        let Type::List(inner) = list else {
            return Err(Error::Unexpected {
                sexpr: apply.source.source_sexpr(),
            });
        };

        for parameter in &parameters {
            if !inner.check(parameter) {
                return Err(Error::Expected {
                    sexpr: apply.source.source_sexpr(),
                    expected: parameter.clone(),
                    received: *inner,
                });
            }
        }

        Ok(*r#return)
    }

    pub fn check_def(&mut self, def: &tree::Def) -> Result<Type, Error> {
        let parameter = match def.parameter.r#type.as_ref().map(Type::from_ast) {
            Some(Ok(t)) => t,
            Some(Err(())) => {
                return Err(Error::Invalid {
                    sexpr: def.source.source_sexpr(),
                })
            }
            None => {
                return Err(Error::None {
                    sexpr: def.source.source_sexpr(),
                })
            }
        };

        self.environments
            .last_mut()
            .unwrap()
            .globals
            .insert(def.parameter.name.clone(), Some(parameter.clone()));

        let body = self.check(&def.body)?;

        if parameter.check(&body) {
            Ok(parameter)
        } else {
            Err(Error::Expected {
                sexpr: def.source.source_sexpr(),
                expected: parameter,
                received: body,
            })
        }
    }

    fn check_set(&mut self, set: &tree::Set) -> Result<Type, Error> {
        let parameter = self.check_varref(&set.target)?;

        let body = self.check(&set.body)?;

        if parameter.check(&body) {
            Ok(parameter)
        } else {
            Err(Error::Expected {
                sexpr: set.source.source_sexpr(),
                expected: parameter,
                received: body,
            })
        }
    }

    fn check_fncall(&mut self, fncall: &tree::FnCall) -> Result<Type, Error> {
        let mut generics: HashMap<String, Type> = HashMap::new();

        let function = self.check(&fncall.function)?;

        let Type::Function {
            parameters,
            r#return,
        } = function
        else {
            return Err(Error::Unexpected {
                sexpr: fncall.source.source_sexpr(),
            });
        };

        let args = fncall
            .args
            .iter()
            .map(|arg| self.check(arg))
            .collect::<Result<Vec<_>, _>>()?;

        if parameters.len() != args.len() {
            return Err(Error::Arity {
                sexpr: fncall.source.source_sexpr(),
            });
        }

        for (a, b) in parameters.iter().zip(args.iter()) {
            match a {
                Type::Generic { name } => match generics.get(name.as_str()) {
                    Some(t) => {
                        if !t.check(b) {
                            return Err(Error::Expected {
                                sexpr: fncall.source.source_sexpr(),
                                expected: t.clone(),
                                received: b.clone(),
                            });
                        }
                    }
                    None => {
                        generics.insert(name.clone(), b.clone());
                    }
                },
                t => {
                    if !t.check(b) {
                        return Err(Error::Expected {
                            sexpr: fncall.source.source_sexpr(),
                            expected: a.clone(),
                            received: b.clone(),
                        });
                    }
                }
            }
        }

        if let Type::Generic { name } = *r#return {
            Ok(generics.get(name.as_str()).cloned().unwrap())
        } else {
            Ok(*r#return)
        }
    }

    fn check_arithmetic_op(&mut self, op: &tree::ArithmeticOperation) -> Result<Type, Error> {
        let lhs = self.check(&op.lhs)?;
        let rhs = self.check(&op.rhs)?;

        Ok(match (lhs, rhs) {
            (Type::Int, Type::Int) => Type::Int,
            _ => {
                return Err(Error::Unexpected {
                    sexpr: op.source.source_sexpr(),
                })
            }
        })
    }

    fn check_comparison_op(&mut self, op: &tree::ComparisonOperation) -> Result<Type, Error> {
        let lhs = self.check(&op.lhs)?;
        let rhs = self.check(&op.rhs)?;

        if lhs.check(&rhs) {
            Ok(Type::Bool)
        } else {
            Err(Error::Expected {
                sexpr: op.source.source_sexpr(),
                expected: lhs,
                received: rhs,
            })
        }
    }

    fn check_list(&mut self, list: &tree::List) -> Result<Type, Error> {
        let exprs = list
            .exprs
            .iter()
            .map(|expr| self.check(expr))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(if exprs.is_empty() {
            Type::Nil
        } else if exprs.iter().all(|a| exprs.iter().all(|b| a == b)) {
            Type::List(std::boxed::Box::new(exprs.first().cloned().unwrap()))
        } else {
            Type::List(std::boxed::Box::new(Type::Union(
                exprs.into_iter().collect(),
            )))
        })
    }

    fn check_cons(&mut self, cons: &tree::Cons) -> Result<Type, Error> {
        let lhs = self.check(&cons.lhs)?;
        let rhs = self.check(&cons.rhs)?;

        Ok(match (lhs, rhs) {
            (a, Type::List(inner)) if inner.check(&a) => Type::List(inner.clone()),
            (a, b) => Type::Cons(std::boxed::Box::new(a), std::boxed::Box::new(b)),
        })
    }

    fn check_car(&mut self, car: &tree::Car) -> Result<Type, Error> {
        self.check(&car.body)
    }

    fn check_cdr(&mut self, cdr: &tree::Cdr) -> Result<Type, Error> {
        self.check(&cdr.body)
    }

    fn check_varref(&self, varref: &tree::VarRef) -> Result<Type, Error> {
        Ok(match varref {
            tree::VarRef::Local { index, .. } => self
                .environments
                .last()
                .unwrap()
                .scopes
                .last()
                .unwrap()
                .locals[*index]
                .clone(),
            tree::VarRef::UpValue { index, .. } => {
                let upvalue = self
                    .environments
                    .last()
                    .unwrap()
                    .scopes
                    .last()
                    .unwrap()
                    .upvalues[*index];
                get_upvalue_type(
                    upvalue,
                    self.environments
                        .last()
                        .unwrap()
                        .scopes
                        .iter()
                        .rev()
                        .skip(1),
                )
            }
            tree::VarRef::Global { name, .. } => self
                .environments
                .last()
                .unwrap()
                .globals
                .get(name)
                .cloned()
                .unwrap(),
        }
        .ok_or(Error::None {
            sexpr: varref.source().source_sexpr(),
        })?)
    }

    fn check_constant(&mut self, constant: &tree::Constant) -> Result<Type, Error> {
        Ok(match constant {
            tree::Constant::Symbol { .. } => Type::Symbol,
            tree::Constant::String { .. } => Type::String,
            tree::Constant::Char { .. } => Type::Char,
            tree::Constant::Int { .. } => Type::Int,
            tree::Constant::Bool { .. } => Type::Bool,
            tree::Constant::Nil { .. } => Type::Nil,
        })
    }
}

fn get_upvalue_type<'scope>(
    upvalue: UpValue,
    mut scopes: impl Iterator<Item = &'scope Scope>,
) -> Option<Type> {
    let scope = scopes.next().unwrap();
    match upvalue {
        UpValue::Local(i) => scope.locals[i].clone(),
        UpValue::UpValue(i) => {
            let next_upvalue = scope.upvalues[i];
            get_upvalue_type(next_upvalue, scopes)
        }
    }
}
