use super::{Error, MaybeUnknownType, Parameters, Rest, Type, TypeId, TypeInfo, Types};
use crate::ast;
use crate::tree::{self, Il};
use std::collections::{HashMap, HashSet};
use std::iter;
use unwrap_enum::{EnumAs, EnumIs};
use vm::UpValue;

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

                let (parameters, rest, r#return) = match r#type {
                    Type::GenericFunction {
                        parameters,
                        rest,
                        r#return,
                        ..
                    } => (parameters, rest, r#return),
                    Type::Function {
                        parameters,
                        rest,
                        r#return,
                        ..
                    } => (parameters, rest, r#return),
                    _ => unreachable!(),
                };

                let Il::Lambda(lambda) = &*def.body else {
                    unreachable!();
                };

                let id = self.check_top_level_lambda(
                    lambda,
                    parameters.clone(),
                    rest.as_ref().map(|rest| *rest.clone()),
                )?;

                match self.types.construct(id) {
                    Some(t) if t == **r#return => Ok(()),
                    Some(_) => todo!(),
                    None => todo!(),
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

    fn check_top_level_lambda(
        &mut self,
        lambda: &tree::Lambda,
        parameters: Vec<Type>,
        rest: Option<Type>,
    ) -> Result<TypeId, Error> {
        let parameters = if let Some(rest) = rest {
            let inner = self.types.insert_concrete_type(rest);
            let rest = self.types.insert(TypeInfo::List(inner));
            parameters[0..parameters.len()]
                .iter()
                .map(|parameter| self.types.insert_concrete_type(parameter.clone()))
                .chain(iter::once(rest))
                .collect::<Vec<_>>()
        } else {
            parameters
                .iter()
                .map(|parameter| self.types.insert_concrete_type(parameter.clone()))
                .collect()
        };

        self.scopes.push(Scope {
            locals: parameters.clone(),
            upvalues: Vec::new(),
        });

        for expr in lambda.body.iter().take(lambda.body.len() - 1) {
            self.check_tree(expr)?;
        }

        let last = self.check_tree(lambda.body.last().unwrap())?;

        self.scopes.pop().unwrap();

        Ok(last)
    }

    fn check_lambda(
        &mut self,
        lambda: &tree::Lambda,
        parameters: Vec<TypeId>,
    ) -> Result<TypeId, Error> {
        let (parameters, rest): (Vec<TypeId>, Rest) = if !parameters.is_empty() {
            match &lambda.parameters {
                tree::Parameters::Nary(_) => (parameters, Rest::None),
                tree::Parameters::Variadic(_) => {
                    let inner = parameters.last().unwrap();
                    let list = self.types.insert(TypeInfo::List(*inner));
                    (
                        parameters[..parameters.len() - 1]
                            .iter()
                            .copied()
                            .chain(iter::once(list))
                            .collect(),
                        Rest::Known(list),
                    )
                }
            }
        } else {
            match &lambda.parameters {
                tree::Parameters::Nary(parameters) => (
                    (0..parameters.len())
                        .map(|_| self.types.insert(TypeInfo::Unknown))
                        .collect(),
                    Rest::None,
                ),
                tree::Parameters::Variadic(parameters) => {
                    let inner = self.types.insert(TypeInfo::Unknown);
                    let list = self.types.insert(TypeInfo::List(inner));
                    (
                        (0..parameters.len() - 1)
                            .map(|_| self.types.insert(TypeInfo::Unknown))
                            .chain(iter::once(list))
                            .collect(),
                        Rest::Known(list),
                    )
                }
            }
        };

        self.scopes.push(Scope {
            locals: parameters.clone(),
            upvalues: lambda.upvalues.clone(),
        });

        let r#return = self.types.insert(TypeInfo::Unknown);

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
            rest,
            r#return,
        }))
    }

    fn check_fncall(&mut self, fncall: &tree::FnCall) -> Result<TypeId, Error> {
        let fncall_parameters = fncall
            .args
            .iter()
            .map(|arg| self.check_tree(arg))
            .collect::<Result<Vec<_>, _>>()?;

        let fncall_function = match &*fncall.function {
            Il::Lambda(lambda) => self.check_lambda(lambda, fncall_parameters.clone())?,
            Il::VarRef(varref) => self.check_varref(varref),
            _ => unreachable!(),
        };

        let r#return = self.types.insert(TypeInfo::Unknown);
        let function = self.types.insert(TypeInfo::Function {
            parameters: Parameters::Known(fncall_parameters),
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
            Il::Lambda(lambda) => self.check_lambda(lambda, Vec::new()),
            Il::Set(set) => self.check_set(set),
            Il::FnCall(fncall) => self.check_fncall(fncall),
            Il::If(r#if) => self.check_if(r#if),
            Il::Apply(apply) => self.check_apply(apply),
            Il::ArithmeticOperation(op) => self.check_aritmetic_op(op),
            Il::ComparisonOperation(op) => self.check_comparison_op(op),
            Il::List(list) => self.check_list(list),
            Il::Cons(cons) => self.check_cons(cons),
            Il::Car(car) => self.check_car(car),
            Il::Cdr(cdr) => self.check_cdr(cdr),
            Il::IsType(is_type) => self.check_is_type(is_type),
            Il::MakeType(make_type) => self.check_make_type(make_type),
            Il::IfLet(if_let) => self.check_if_let(if_let),
            Il::LetRec(letrec) => self.check_letrec(letrec),
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

        let Ok(()) = self.types.unify(apply_function, function) else {
            todo!()
        };

        let rest = self.types.insert(TypeInfo::List(rest));

        let Ok(()) = self.types.unify(apply_list, rest) else {
            return Err(Error::Unification {
                message: "failed to unify apply's list".to_string(),
                span: apply.span,
                a: MaybeUnknownType::from(self.types.construct(apply_list)),
                b: MaybeUnknownType::from(self.types.construct(rest)),
            });
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

    fn check_letrec(&mut self, letrec: &tree::LetRec) -> Result<TypeId, Error> {
        let scope = Scope {
            locals: (0..letrec.bindings.len())
                .map(|_| self.types.insert(TypeInfo::Unknown))
                .collect(),
            upvalues: letrec.upvalues.clone(),
        };

        self.scopes.push(scope);

        for (_, expr) in &letrec.bindings {
            self.check_tree(expr)?;
        }

        let body = self.check_tree(&letrec.body)?;

        self.scopes.pop().unwrap();

        Ok(body)
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
