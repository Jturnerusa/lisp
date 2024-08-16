use core::fmt;
use reader::Sexpr;
use std::collections::{BTreeSet, HashMap, HashSet};
use unwrap_enum::{EnumAs, EnumIs};
use vm::UpValue;

use crate::{ast, tree};

#[derive(Clone, Debug, thiserror::Error)]
pub enum Error {
    #[error("type error: expected: {expected}, received: {received}\n{sexpr:?}")]
    Expected {
        expected: Type,
        received: Type,
        sexpr: &'static Sexpr<'static>,
    },
    #[error("type error: unexpected type for context\n{sexpr:?}")]
    Unexpected { sexpr: &'static Sexpr<'static> },
    #[error("type error: wrong number of arguments\n{sexpr:?}")]
    Arity { sexpr: &'static Sexpr<'static> },
    #[error("type error: no type found for expression\n{sexpr:?}")]
    None { sexpr: &'static Sexpr<'static> },
    #[error("type error: invalid type annotation\n{sexpr:?}")]
    Invalid { sexpr: &'static Sexpr<'static> },
    #[error("type error: cant narrow non-union types\n{sexpr:?}")]
    Narrow { sexpr: &'static Sexpr<'static> },
    #[error("type error: unknown type alias: {sexpr:?}")]
    Alias { sexpr: &'static Sexpr<'static> },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, EnumAs, EnumIs)]
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
    TypeVar(usize),
    Alias(String),
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
    vars: Vec<HashMap<usize, Type>>,
    aliases: HashMap<String, Type>,
}

impl Type {
    pub fn check(&self, other: &Self, vars: &mut HashMap<usize, Type>) -> bool {
        match (self, other) {
            (Type::List(a), Type::List(b)) if a.check(b, vars) => true,
            (Type::Cons(a, b), Type::Cons(c, d)) if a.check(c, vars) && b.check(d, vars) => true,
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
                .all(|(a, b)| a.check(b, vars))
                && return_a.check(return_b, vars) =>
            {
                true
            }
            (Type::Symbol, Type::Symbol) => true,
            (Type::String, Type::String) => true,
            (Type::Char, Type::Char) => true,
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Nil, Type::Nil) => true,
            (Type::Union(a), Type::Union(b))
                if a.iter().all(|x| b.iter().any(|y| x.check(y, vars))) =>
            {
                true
            }
            (Type::Union(a), b) if a.iter().any(|x| x.check(b, vars)) => true,
            (a, Type::Union(b)) if b.iter().any(|x| x.check(a, vars)) => true,
            (Type::Generic { name: a }, Type::Generic { name: b }) if a == b => true,
            (Type::TypeVar(t), rhs) => match vars.get(t) {
                Some(t) => t == rhs,
                None => {
                    vars.insert(*t, rhs.clone());
                    true
                }
            },
            (lhs, Type::TypeVar(t)) => match vars.get(t) {
                Some(t) => t == lhs,
                None => {
                    vars.insert(*t, lhs.clone());
                    true
                }
            },
            (Type::Alias(a), Type::Alias(b)) if a == b => true,
            _ => false,
        }
    }

    pub fn expand(
        &self,
        aliases: &HashMap<String, Type>,
        seen: &mut HashSet<String>,
    ) -> Option<Type> {
        Some(match self {
            Self::List(a) => Type::List(Box::new(a.expand(aliases, seen)?)),
            Self::Cons(lhs, rhs) => Type::Cons(
                Box::new(lhs.expand(aliases, seen)?),
                Box::new(rhs.expand(aliases, seen)?),
            ),
            Self::Function {
                parameters,
                r#return,
            } => Type::Function {
                parameters: parameters
                    .iter()
                    .map(|p| p.expand(aliases, seen))
                    .collect::<Option<_>>()?,
                r#return: Box::new(r#return.expand(aliases, seen)?),
            },
            Self::Union(types) => Type::Union(
                types
                    .iter()
                    .map(|p| p.expand(aliases, seen))
                    .collect::<Option<_>>()?,
            ),
            Self::Alias(a) if seen.contains(a) => aliases.get(a).cloned()?,
            Self::Alias(a) => aliases.get(a.as_str()).cloned()?,
            t => t.clone(),
        })
    }

    #[allow(clippy::result_unit_err)]
    pub fn from_ast(tree: &ast::Type) -> Result<Self, ()> {
        Ok(match tree {
            ast::Type::Composite(types) => match types.as_slice() {
                [ast::Type::Scalar(t), parameters @ .., ast::Type::Scalar(arrow), r#return]
                    if t == "fn" && arrow == "->" =>
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
                [ast::Type::Scalar(t), ast::Type::Scalar(name)] if t == "quote" => {
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
            ast::Type::Scalar(t) => Type::Alias(t.clone()),
            _ => return Err(()),
        })
    }

    fn narrow(&self, parameter: &tree::IsTypeParameter) -> Result<Type, ()> {
        let Type::Union(types) = self else {
            return Err(());
        };

        for t in types.iter() {
            match (t, parameter) {
                (Type::List(_) | Type::Cons(_, _), tree::IsTypeParameter::Cons) => {
                    return Ok(t.clone())
                }
                (Type::Function { .. }, tree::IsTypeParameter::Function) => return Ok(t.clone()),
                (Type::Symbol, tree::IsTypeParameter::Symbol) => return Ok(t.clone()),
                (Type::String, tree::IsTypeParameter::String) => return Ok(t.clone()),
                (Type::Char, tree::IsTypeParameter::Char) => return Ok(t.clone()),
                (Type::Int, tree::IsTypeParameter::Int) => return Ok(t.clone()),
                (Type::Bool, tree::IsTypeParameter::Bool) => return Ok(t.clone()),
                (Type::Nil, tree::IsTypeParameter::Nil) => return Ok(t.clone()),
                _ => continue,
            }
        }

        Err(())
    }

    fn is_list_or_nil(&self) -> bool {
        let Type::Union(types) = self else {
            return false;
        };

        types.len() == 2
            && types.iter().filter(|t| t.is_list()).count() == 1
            && types.iter().filter(|t| t.is_nil()).count() == 1
    }

    fn unify(&self, mapping: &mut HashMap<String, usize>) -> Type {
        debug_assert!(!self.is_typevar());

        match self {
            Type::Generic { name } => match mapping.get(name) {
                Some(t) => Type::TypeVar(*t),
                None => {
                    let t = rand::random::<usize>();
                    mapping.insert(name.clone(), t);
                    Type::TypeVar(t)
                }
            },
            Type::List(inner) => Type::List(Box::new(inner.unify(mapping))),
            Type::Cons(lhs, rhs) => {
                Type::Cons(Box::new(lhs.unify(mapping)), Box::new(rhs.unify(mapping)))
            }
            Type::Function {
                parameters,
                r#return,
            } => Type::Function {
                parameters: parameters.iter().map(|p| p.unify(mapping)).collect(),
                r#return: Box::new(r#return.unify(mapping)),
            },
            Type::Union(types) => Type::Union(types.iter().map(|t| t.unify(mapping)).collect()),
            t => t.clone(),
        }
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
            Self::Generic { name } => write!(f, "generic({name})"),
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

#[allow(clippy::new_without_default)]
impl Checker {
    pub fn new() -> Self {
        Self {
            environments: vec![Environment::new()],
            vars: vec![HashMap::new()],
            aliases: HashMap::new(),
        }
    }

    pub fn compare_types(
        &mut self,
        a: &Type,
        b: &Type,
        sexpr: &'static Sexpr<'static>,
    ) -> Result<bool, Error> {
        let a_expanded = a
            .expand(&self.aliases, &mut HashSet::new())
            .ok_or(Error::Alias { sexpr })?;

        let b_expanded = b
            .expand(&self.aliases, &mut HashSet::new())
            .ok_or(Error::Alias { sexpr })?;

        Ok(a_expanded.check(&b_expanded, self.vars.last_mut().unwrap()))
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

    pub fn create_type_alias(&mut self, let_type: &ast::LetType) -> Result<(), Error> {
        self.aliases.insert(
            let_type.name.clone(),
            Type::from_ast(&let_type.r#type).map_err(|_| Error::Invalid {
                sexpr: let_type.source,
            })?,
        );

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
            tree::Il::IsType(_) => Ok(Type::Bool),
            _ => todo!("{tree:?}"),
        }
    }

    pub fn check_lambda(&mut self, lambda: &tree::Lambda) -> Result<Type, Error> {
        self.vars.push(HashMap::new());

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

        for expr in lambda.body.iter().take(lambda.body.len() - 1) {
            self.check(expr)?;
        }

        let last_expr = self.check(lambda.body.last().unwrap())?;

        let r#return = match &lambda.r#type {
            Some(ast::Type::Inferred) => last_expr.clone(),
            Some(r#type) => Type::from_ast(r#type).map_err(|_| Error::Invalid {
                sexpr: lambda.source.source_sexpr(),
            })?,
            None => {
                return Err(Error::None {
                    sexpr: lambda.source.source_sexpr(),
                })
            }
        };

        self.environments.last_mut().unwrap().scopes.pop();

        let ret = self.compare_types(&r#return, &last_expr, lambda.source.source_sexpr())?;

        self.vars.pop().unwrap();

        if ret {
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

    fn infer_lambda(&self, lambda: &tree::Lambda) -> Result<Type, Error> {
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

            parameters.push(t);
        }

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

        Ok(Type::Function {
            parameters,
            r#return: Box::new(r#return),
        })
    }

    fn narrow(&mut self, r#if: &tree::If) -> Result<(), Error> {
        if let tree::Il::IsType(is_type) = &*r#if.predicate
            && let tree::Il::VarRef(varref) = &*is_type.body
        {
            let t = self.check_varref(varref)?;
            let narrowed = t.narrow(&is_type.r#type).map_err(|_| Error::Narrow {
                sexpr: r#if.source.source_sexpr(),
            })?;

            match varref {
                tree::VarRef::Local { index, .. } => {
                    self.environments
                        .last_mut()
                        .unwrap()
                        .scopes
                        .last_mut()
                        .unwrap()
                        .locals[*index] = Some(narrowed)
                }
                _ => todo!(),
            }
        }

        Ok(())
    }

    fn narrow_nested_ifs(&mut self, r#if: &tree::If) -> Result<(), Error> {
        self.narrow(r#if)?;

        if let tree::Il::If(then) = &*r#if.then {
            self.narrow(then)?;
        }

        Ok(())
    }

    fn check_if(&mut self, r#if: &tree::If) -> Result<Type, Error> {
        self.environments
            .push(self.environments.last().cloned().unwrap());

        let predicate = self.check(&r#if.predicate)?;

        if r#if.predicate.is_istype() {
            self.narrow(r#if)?;
        } else if let tree::Il::If(inner_if) = &*r#if.predicate
            && is_and(inner_if)
        {
            self.narrow_nested_ifs(inner_if)?;
        }

        let then = self.check(&r#if.then)?;

        self.environments.pop().unwrap();

        let r#else = self.check(&r#if.r#else)?;

        let Type::Bool = &predicate else {
            return Err(Error::Expected {
                sexpr: r#if.source.source_sexpr(),
                expected: Type::Bool,
                received: predicate,
            });
        };

        Ok(
            if self.compare_types(&then, &r#else, r#if.source.source_sexpr())? {
                then
            } else {
                Type::Union(BTreeSet::from([then, r#else]))
            },
        )
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
            if !self.compare_types(&inner, parameter, apply.source.source_sexpr())? {
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
        let parameter = match (def.parameter.r#type.as_ref(), &*def.body) {
            (Some(ast::Type::Scalar(t)), tree::Il::Lambda(lambda)) if t == "function" => {
                self.infer_lambda(lambda)?
            }
            _ => match def.parameter.r#type.as_ref().map(Type::from_ast) {
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
            },
        };

        self.environments
            .last_mut()
            .unwrap()
            .globals
            .insert(def.parameter.name.clone(), Some(parameter.clone()));

        let body = self.check(&def.body)?;

        if self.compare_types(&parameter, &body, def.source.source_sexpr())? {
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

        if self.compare_types(&parameter, &body, set.source.source_sexpr())? {
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
        let mut mapping = HashMap::new();

        let Type::Function {
            parameters,
            r#return,
        } = self
            .check(&fncall.function)?
            .unify(&mut mapping)
            .expand(&self.aliases, &mut HashSet::new())
            .ok_or(Error::Alias {
                sexpr: fncall.source.source_sexpr(),
            })?
        else {
            todo!()
        };

        let args = fncall
            .args
            .iter()
            .map(|arg| self.check(arg))
            .collect::<Result<Vec<_>, _>>()?;

        for (expected, received) in parameters.iter().zip(args.iter()) {
            if self.compare_types(expected, received, fncall.source.source_sexpr())? {
                continue;
            } else {
                return Err(Error::Expected {
                    sexpr: fncall.source.source_sexpr(),
                    expected: expected.clone(),
                    received: received.clone(),
                });
            }
        }

        Ok(*r#return)
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

        if self.compare_types(&lhs, &rhs, op.source.source_sexpr())? {
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
            (a, Type::List(inner))
                if self.compare_types(&a, &inner, cons.source.source_sexpr())? =>
            {
                Type::List(inner.clone())
            }
            (a, b)
                if b.is_list_or_nil()
                    && b.as_union().unwrap().iter().any(|x| {
                        self.compare_types(
                            x,
                            &Type::List(Box::new(a.clone())),
                            cons.source.source_sexpr(),
                        )
                        .is_ok_and(|b| b)
                    }) =>
            {
                Type::List(Box::new(
                    b.as_union()
                        .unwrap()
                        .iter()
                        .find_map(|t| match t {
                            Type::List(inner) => Some(*inner.clone()),
                            _ => None,
                        })
                        .unwrap(),
                ))
            }
            (a, b) => Type::Cons(std::boxed::Box::new(a), std::boxed::Box::new(b)),
        })
    }

    fn check_car(&mut self, car: &tree::Car) -> Result<Type, Error> {
        match self.check(&car.body)? {
            Type::List(inner) => Ok(*inner),
            _ => Err(Error::Unexpected {
                sexpr: car.source.source_sexpr(),
            }),
        }
    }

    fn check_cdr(&mut self, cdr: &tree::Cdr) -> Result<Type, Error> {
        let t = self.check(&cdr.body)?;

        match t {
            Type::List(_) => Ok(Type::Union(BTreeSet::from([Type::Nil, t]))),
            _ => Err(Error::Unexpected {
                sexpr: cdr.source.source_sexpr(),
            }),
        }
    }

    fn check_varref(&self, varref: &tree::VarRef) -> Result<Type, Error> {
        match varref {
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
        })
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

fn is_and(r#if: &tree::If) -> bool {
    match (&*r#if.then, &*r#if.r#else) {
        (tree::Il::If(inner), tree::Il::Constant(tree::Constant::Bool { bool, .. })) if !*bool => {
            is_and(inner)
        }
        (
            tree::Il::Constant(tree::Constant::Bool { bool: then, .. }),
            tree::Il::Constant(tree::Constant::Bool { bool: r#else, .. }),
        ) if *then && !r#else => true,
        _ => false,
    }
}
