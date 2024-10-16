use super::{Error, Parameters, Rest, Type, TypeId, TypeInfo, Types, VariantOrStruct};
use crate::ast::{self, VariantPattern};
use crate::tree::{self, Il};
use itertools::Itertools;
use std::collections::HashMap;
use std::iter;
use unwrap_enum::{EnumAs, EnumIs};
use vm::UpValue;

#[derive(Clone, Debug, EnumAs, EnumIs)]
enum PolyType {
    Poly(TypeId),
    Mono(TypeId),
}

#[derive(Clone, Debug)]
struct Scope {
    locals: Vec<TypeId>,
    upvalues: Vec<UpValue>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
enum TypeOrGeneric {
    Type(Type),
    Generic(Type, HashMap<String, usize>),
}

#[derive(Clone, Debug)]
struct VariantType {
    name: String,
    variants: Vec<Variant>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
enum Variant {
    Struct(String, Vec<TypeOrGeneric>),
    Enum(String),
}

#[derive(Clone, Debug)]
struct Struct {
    name: String,
    fields: Vec<TypeOrGeneric>,
}

#[derive(Clone, Debug)]
pub struct Checker {
    types: Types,
    scopes: Vec<Scope>,
    globals: HashMap<String, PolyType>,
    variant_types: HashMap<VariantPattern, VariantType>,
    variants: HashMap<VariantPattern, (usize, Variant)>,
    structs: HashMap<String, Struct>,
    constructors: HashMap<ast::StructConstructor, Struct>,
    accessors: HashMap<ast::StructAccessor, TypeOrGeneric>,
    user_types: HashMap<String, VariantOrStruct>,
}

impl Checker {
    pub fn new() -> Self {
        Self {
            types: Types::new(),
            scopes: Vec::new(),
            globals: HashMap::new(),
            variant_types: HashMap::new(),
            variants: HashMap::new(),
            structs: HashMap::new(),
            constructors: HashMap::new(),
            accessors: HashMap::new(),
            user_types: HashMap::new(),
        }
    }

    pub fn check(&mut self, tree: &tree::Il) -> Result<(), Error> {
        match tree {
            Il::Def(def) => self.check_def(def),
            Il::Lambda(lambda) => self.check_lambda(lambda, Vec::new()).map(|_| ()),
            Il::If(r#if) => self.check_if(r#if).map(|_| ()),
            Il::Apply(apply) => self.check_apply(apply).map(|_| ()),
            Il::Set(set) => self.check_set(set).map(|_| ()),
            Il::FnCall(fncall) => self.check_fncall(fncall).map(|_| ()),
            Il::ArithmeticOperation(op) => self.check_aritmetic_op(op).map(|_| ()),
            Il::FloatOperation(op) => self.check_float_op(op).map(|_| ()),
            Il::ComparisonOperation(op) => self.check_comparison_op(op).map(|_| ()),
            Il::List(list) => self.check_list(list).map(|_| ()),
            Il::Cons(cons) => self.check_cons(cons).map(|_| ()),
            Il::Car(car) => self.check_car(car).map(|_| ()),
            Il::Cdr(cdr) => self.check_cdr(cdr).map(|_| ()),
            Il::Assert(assert) => self.check_assert(assert).map(|_| ()),
            Il::Decl(decl) => self.check_decl(decl),
            Il::DefType(deftype) => self.deftype(deftype),
            Il::MakeType(maketype) => self.check_make_type(maketype).map(|_| ()),
            Il::IfLet(if_let) => self.check_if_let(if_let).map(|_| ()),
            Il::DefStruct(defstruct) => self.check_defstruct(defstruct),
            Il::MakeStruct(make_struct) => self.check_make_struct(make_struct).map(|_| ()),
            Il::GetField(get_field) => self.check_get_field(get_field).map(|_| ()),
            Il::MakeVec(make_vec) => self.check_make_vec(make_vec).map(|_| ()),
            Il::VecPush(vec_push) => self.check_vec_push(vec_push).map(|_| ()),
            Il::VecPop(vec_pop) => self.check_vec_pop(vec_pop).map(|_| ()),
            Il::VecRef(vec_index) => self.check_vec_ref(vec_index).map(|_| ()),
            Il::VecLength(vec_length) => self.check_vec_length(vec_length).map(|_| ()),
            _ => Ok(()),
        }
    }

    fn deftype(&mut self, deftype: &ast::DefType) -> Result<(), Error> {
        self.user_types
            .insert(deftype.name.clone(), VariantOrStruct::Variant);

        let mut generics = HashMap::new();

        let variants = deftype
            .variants
            .iter()
            .map(|variant| {
                Ok(if !variant.types.is_empty() {
                    Variant::Struct(
                        variant.name.clone(),
                        variant
                            .types
                            .iter()
                            .map(|r#type| match Type::from_ast(r#type, &self.user_types) {
                                Ok(t) if t.has_generics() => {
                                    t.map_generics(&mut generics);
                                    Ok(TypeOrGeneric::Generic(t, generics.clone()))
                                }
                                Ok(t) => Ok(TypeOrGeneric::Type(t)),
                                Err(()) => Err(Error::InvalidType(deftype.span)),
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                } else {
                    Variant::Enum(variant.name.clone())
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let variant_type = VariantType {
            name: deftype.name.clone(),
            variants: variants.clone(),
        };

        for (i, variant) in variants.iter().enumerate() {
            let variant_name = match variant {
                Variant::Struct(name, _) | Variant::Enum(name) => name.clone(),
            };
            let pattern = format!("{}-{}", deftype.name, variant_name);

            self.variant_types
                .insert(VariantPattern(pattern.clone()), variant_type.clone());
            self.variants
                .insert(VariantPattern(pattern), (i, variant.clone()));
        }

        Ok(())
    }

    fn check_decl(&mut self, decl: &ast::Decl) -> Result<(), Error> {
        let r#type = match decl
            .parameter
            .r#type
            .as_ref()
            .map(|r#type| Type::from_ast(r#type, &self.user_types))
        {
            Some(Ok(t)) => t,
            Some(Err(())) => return Err(Error::InvalidType(decl.span)),
            None => return Err(Error::Annotation(decl.span)),
        };

        let id = self.types.insert_concrete_type(r#type.clone());

        self.globals.insert(
            decl.parameter.name.clone(),
            if r#type.has_generics() {
                PolyType::Poly(id)
            } else {
                PolyType::Mono(id)
            },
        );

        Ok(())
    }

    fn check_def(&mut self, def: &tree::Def) -> Result<(), Error> {
        match def
            .parameter
            .r#type
            .as_ref()
            .map(|r#type| Type::from_ast(r#type, &self.user_types))
        {
            Some(Ok(t)) if t.is_function() && def.body.is_lambda() => {
                let id = self.types.insert_concrete_type(t.clone());

                self.globals.insert(
                    def.parameter.name.clone(),
                    if t.has_generics() {
                        PolyType::Poly(id)
                    } else {
                        PolyType::Mono(id)
                    },
                );

                let (parameters, rest, _) = t.as_function().unwrap();

                let parameter_ids = parameters
                    .iter()
                    .map(|parameter| self.types.insert_concrete_type(parameter.clone()))
                    .collect::<Vec<_>>();

                let lambda = match &*def.body {
                    tree::Il::Lambda(lambda) => lambda,
                    _ => unreachable!(),
                };

                if lambda.parameters.len()
                    != if rest.is_some() {
                        parameters.len() + 1
                    } else {
                        parameters.len()
                    }
                {
                    return Err(Error::Arity(def.span));
                }

                let ret = self.check_lambda(lambda, parameter_ids)?;

                let Ok(()) = self.types.unify(id, ret) else {
                    return Err(Error::Unification {
                        message: "failed to unify return value with defined type".to_string(),
                        span: def.span,
                        a: self.types.construct_partially_known_type(id),
                        b: self.types.construct_partially_known_type(ret),
                    });
                };

                Ok(())
            }
            Some(Ok(t)) => {
                let id = self.types.insert_concrete_type(t.clone());

                let ret = self.check_tree(&def.body)?;

                let Ok(()) = self.types.unify(id, ret) else {
                    todo!()
                };

                Ok(())
            }
            Some(Err(())) => Err(Error::InvalidType(def.span)),
            None => {
                self.globals.insert(
                    def.parameter.name.clone(),
                    PolyType::Mono(self.types.insert(TypeInfo::Any)),
                );
                Ok(())
            }
        }
    }

    fn check_lambda(
        &mut self,
        lambda: &tree::Lambda,
        parameters: Vec<TypeId>,
    ) -> Result<TypeId, Error> {
        let (parameters, rest): (Vec<TypeId>, Rest) = if !parameters.is_empty() {
            match &lambda.parameters {
                tree::Parameters::Nary(_) => (parameters, Rest::None),
                tree::Parameters::Variadic(n) => {
                    let inner = parameters[n.len()];

                    if !parameters[n.len()..parameters.len()]
                        .iter()
                        .all(|parameter| self.types.unify(inner, *parameter).is_ok())
                    {
                        panic!()
                    }

                    let list = self.types.insert(TypeInfo::List(inner));
                    (parameters[..n.len()].to_vec(), Rest::Known(list))
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
                            .collect(),
                        Rest::Known(list),
                    )
                }
            }
        };

        self.scopes.push(Scope {
            locals: match rest {
                Rest::Known(id) => parameters.iter().copied().chain(iter::once(id)).collect(),
                _ => parameters.clone(),
            },
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
                a: self.types.construct_partially_known_type(r#return),
                b: self.types.construct_partially_known_type(last),
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
            tree => self.check_tree(tree)?,
        };

        let r#return = self.types.insert(TypeInfo::Unknown);
        let function = self.types.insert(TypeInfo::Function {
            parameters: Parameters::Unknown,
            rest: Rest::Unknown,
            r#return,
        });

        let Ok(()) = self.types.unify(function, fncall_function) else {
            return Err(Error::Unification {
                message: "failed to unify fncall".to_string(),
                span: fncall.span,
                a: self.types.construct_partially_known_type(function),
                b: self.types.construct_partially_known_type(fncall_function),
            });
        };

        match self.types.vars[fncall_function].clone() {
            TypeInfo::Function {
                parameters: Parameters::Known(parameters),
                rest: Rest::Known(rest),
                ..
            } => {
                let non_variadic_parameters = fncall_parameters[0..parameters.len()].to_vec();
                let variadic_parameters =
                    fncall_parameters[parameters.len()..fncall_parameters.len()].to_vec();

                for a in &variadic_parameters {
                    for b in &variadic_parameters {
                        let Ok(()) = self.types.unify(*a, *b) else {
                            return Err(Error::Unification {
                                message: "failed to unify variadic parameter".to_string(),
                                span: fncall.span,
                                a: self.types.construct_partially_known_type(*a),
                                b: self.types.construct_partially_known_type(*b),
                            });
                        };
                    }
                }

                let id = self.types.insert(TypeInfo::Function {
                    parameters: Parameters::Known(non_variadic_parameters),
                    rest: Rest::Known(rest),
                    r#return,
                });

                let Ok(()) = self.types.unify(id, fncall_function) else {
                    return Err(Error::Unification {
                        message: "failed to unify fncall".to_string(),
                        span: fncall.span,
                        a: self.types.construct_partially_known_type(id),
                        b: self.types.construct_partially_known_type(fncall_function),
                    });
                };
            }
            TypeInfo::Function { .. } => {
                let id = self.types.insert(TypeInfo::Function {
                    parameters: Parameters::Known(fncall_parameters),
                    rest: Rest::Unknown,
                    r#return,
                });

                let Ok(()) = self.types.unify(id, fncall_function) else {
                    return Err(Error::Unification {
                        message: "failed to unify fncall".to_string(),
                        span: fncall.span,
                        a: self.types.construct_partially_known_type(id),
                        b: self.types.construct_partially_known_type(fncall_function),
                    });
                };
            }
            TypeInfo::Any => (),
            _ => unreachable!(),
        }

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
            Il::FloatOperation(op) => self.check_float_op(op),
            Il::ComparisonOperation(op) => self.check_comparison_op(op),
            Il::List(list) => self.check_list(list),
            Il::Cons(cons) => self.check_cons(cons),
            Il::Car(car) => self.check_car(car),
            Il::Cdr(cdr) => self.check_cdr(cdr),
            Il::IsType(is_type) => self.check_is_type(is_type),
            Il::MakeType(make_type) => self.check_make_type(make_type),
            Il::IfLet(if_let) => self.check_if_let(if_let),
            Il::LetRec(letrec) => self.check_letrec(letrec),
            Il::MakeStruct(make_struct) => self.check_make_struct(make_struct),
            Il::GetField(get_field) => self.check_get_field(get_field),
            Il::Assert(assert) => self.check_assert(assert),
            Il::VarRef(varref) => Ok(self.check_varref(varref)),
            Il::Constant(constant) => self.check_constant(constant),
            Il::MakeVec(make_vec) => self.check_make_vec(make_vec),
            Il::VecPush(vec_push) => self.check_vec_push(vec_push),
            Il::VecPop(vec_pop) => self.check_vec_pop(vec_pop),
            Il::VecRef(vec_index) => self.check_vec_ref(vec_index),
            Il::VecLength(vec_length) => self.check_vec_length(vec_length),
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
                a: self.types.construct_partially_known_type(lhs),
                b: self.types.construct_partially_known_type(rhs),
            });
        };

        let Ok(()) = self.types.unify(rhs, int) else {
            return Err(Error::Unification {
                message: "failed to unify rhs with integer".to_string(),
                span: op.span,
                a: self.types.construct_partially_known_type(lhs),
                b: self.types.construct_partially_known_type(rhs),
            });
        };

        Ok(int)
    }

    fn check_float_op(&mut self, op: &tree::FloatOperation) -> Result<TypeId, Error> {
        let lhs = self.check_tree(&op.lhs)?;
        let rhs = self.check_tree(&op.rhs)?;
        let float = self.types.insert_concrete_type(Type::Float);

        let Ok(()) = self.types.unify(lhs, float) else {
            return Err(Error::Unification {
                message: "failed to unify lhs with float".to_string(),
                span: op.span,
                a: self.types.construct_partially_known_type(lhs),
                b: self.types.construct_partially_known_type(rhs),
            });
        };

        let Ok(()) = self.types.unify(rhs, float) else {
            return Err(Error::Unification {
                message: "failed to unify rhs with float".to_string(),
                span: op.span,
                a: self.types.construct_partially_known_type(lhs),
                b: self.types.construct_partially_known_type(rhs),
            });
        };

        Ok(float)
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
                a: self.types.construct_partially_known_type(predicate),
                b: self.types.construct_partially_known_type(bool),
            });
        };

        let Ok(()) = self.types.unify(then, r#else) else {
            return Err(Error::Unification {
                message: "failed to unify then with else".to_string(),
                span: r#if.span,
                a: self.types.construct_partially_known_type(then),
                b: self.types.construct_partially_known_type(r#else),
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
                a: self.types.construct_partially_known_type(apply_list),
                b: self.types.construct_partially_known_type(rest),
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
        let car = self.types.insert(TypeInfo::Unknown);
        let cdr = self.types.insert(TypeInfo::Unknown);

        self.types.unify(car, lhs).unwrap();
        self.types.unify(cdr, rhs).unwrap();

        let inner = self.types.insert(TypeInfo::Unknown);
        let list = self.types.insert(TypeInfo::List(inner));

        match self
            .types
            .unify(list, rhs)
            .and_then(|_| self.types.unify(inner, lhs))
        {
            Ok(()) => Ok(list),
            Err(()) => Ok(self.types.insert(TypeInfo::Cons(car, cdr))),
        }
    }

    fn check_car(&mut self, car: &tree::Car) -> Result<TypeId, Error> {
        let body = self.check_tree(&car.body)?;
        let inner = self.types.insert(TypeInfo::Unknown);
        let list = self.types.insert(TypeInfo::List(inner));

        let Ok(()) = self.types.unify(list, body) else {
            return Err(Error::Unification {
                message: "failed to unify body with list".to_string(),
                span: car.span,
                a: self.types.construct_partially_known_type(list),
                b: self.types.construct_partially_known_type(body),
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
                a: self.types.construct_partially_known_type(list),
                b: self.types.construct_partially_known_type(body),
            });
        };

        Ok(list)
    }

    fn check_is_type(&mut self, is_type: &tree::IsType) -> Result<TypeId, Error> {
        self.check_tree(&is_type.body)?;

        Ok(self.types.insert(TypeInfo::Bool))
    }

    fn check_make_type(&mut self, make_type: &tree::MakeType) -> Result<TypeId, Error> {
        let variant_type = self.variant_types[&make_type.pattern].clone();
        let (_, variant) = self.variants[&make_type.pattern].clone();

        let parameters = variant_type
            .variants
            .iter()
            .filter_map(|variant| {
                variant
                    .as_struct()
                    .map(|(_, types)| types.iter().filter_map(|r#type| r#type.as_generic()))
            })
            .flatten()
            .unique_by(|(r#type, _)| r#type.as_generic())
            .map(|_| self.types.insert(TypeInfo::Unknown))
            .collect::<Vec<_>>();

        match variant {
            Variant::Struct(_, types) => {
                for (type_or_generic, expr) in types.iter().zip(make_type.exprs.iter()) {
                    match type_or_generic {
                        TypeOrGeneric::Generic(r#type, generics) => {
                            let expr = self.check_tree(expr)?;

                            let id = self.types.insert_concrete_type(r#type.clone());

                            let subs = generics
                                .iter()
                                .map(|(generic, index)| (generic.clone(), parameters[*index]))
                                .collect::<HashMap<_, _>>();

                            let id = self.types.instantiate_with(id, &subs);

                            let Ok(()) = self.types.unify(id, expr) else {
                                return Err(Error::Unification {
                                    message: "failed to unify variant fields".to_string(),
                                    span: make_type.span,
                                    a: self.types.construct_partially_known_type(id),
                                    b: self.types.construct_partially_known_type(expr),
                                });
                            };
                        }
                        _ => continue,
                    }
                }
            }
            _ => (),
        }

        Ok(self.types.insert(TypeInfo::DefType {
            name: variant_type.name.clone(),
            parameters,
        }))
    }

    fn check_if_let(&mut self, if_let: &tree::IfLet) -> Result<TypeId, Error> {
        let body = self.check_tree(&if_let.body)?;

        let (then, r#else) = if !if_let.bindings.is_empty() {
            let variant_type = self.variant_types[&if_let.pattern].clone();
            let (_, variant) = self.variants[&if_let.pattern].clone();

            let parameters = variant_type
                .variants
                .iter()
                .filter_map(|variant| {
                    variant
                        .as_struct()
                        .map(|(_, types)| types.iter().filter_map(|r#type| r#type.as_generic()))
                })
                .flatten()
                .unique_by(|(r#type, _)| r#type.as_generic())
                .map(|_| self.types.insert(TypeInfo::Unknown))
                .collect::<Vec<_>>();

            let id = self.types.insert(TypeInfo::DefType {
                name: variant_type.name.clone(),
                parameters: parameters.clone(),
            });

            self.types.unify(id, body).unwrap();

            let bindings = match variant {
                Variant::Struct(_, types) => types
                    .iter()
                    .map(|type_or_generic| match type_or_generic {
                        TypeOrGeneric::Generic(r#type, generics) => {
                            let r#type = self.types.insert_concrete_type(r#type.clone());
                            let subs = generics
                                .iter()
                                .map(|(generic, index)| (generic.clone(), parameters[*index]))
                                .collect::<HashMap<_, _>>();
                            self.types.instantiate_with(r#type, &subs)
                        }
                        TypeOrGeneric::Type(r#type) => {
                            self.types.insert_concrete_type(r#type.clone())
                        }
                    })
                    .collect(),
                _ => unreachable!(),
            };

            self.scopes.push(Scope {
                locals: bindings,
                upvalues: if_let.upvalues.clone(),
            });

            let then = self.check_tree(&if_let.then)?;

            self.scopes.pop().unwrap();

            let r#else = self.check_tree(&if_let.r#else)?;

            (then, r#else)
        } else {
            let then = self.check_tree(&if_let.then)?;
            let r#else = self.check_tree(&if_let.r#else)?;

            (then, r#else)
        };

        let r#return = self.types.insert(TypeInfo::Unknown);

        self.types.unify(r#return, then).unwrap();

        let Ok(()) = self.types.unify(r#return, r#else) else {
            return Err(Error::Unification {
                message: "failed while unifying if-let then and else".to_string(),
                span: if_let.span,
                a: self.types.construct_partially_known_type(then),
                b: self.types.construct_partially_known_type(r#else),
            });
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

    fn check_assert(&mut self, _: &tree::Assert) -> Result<TypeId, Error> {
        Ok(self.types.insert(TypeInfo::Bool))
    }

    fn check_defstruct(&mut self, defstruct: &ast::DefStruct) -> Result<(), Error> {
        let mut generics = HashMap::new();

        let fields = defstruct
            .fields
            .iter()
            .map(|(_, r#type)| {
                Ok(match Type::from_ast(r#type, &self.user_types) {
                    Ok(t) if t.has_generics() => {
                        t.map_generics(&mut generics);
                        TypeOrGeneric::Generic(t, generics.clone())
                    }
                    Ok(t) => TypeOrGeneric::Type(t),
                    Err(()) => return Err(Error::InvalidType(defstruct.span)),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let r#struct = Struct {
            name: defstruct.name.clone(),
            fields: fields.clone(),
        };

        for ((field_name, _), field) in defstruct.fields.iter().zip(fields.iter()) {
            let accessor = format!("{}-{}", defstruct.name, field_name);
            self.accessors
                .insert(ast::StructAccessor(accessor), field.clone());
        }

        let constructor = format!("make-{}", defstruct.name);
        self.constructors
            .insert(ast::StructConstructor(constructor), r#struct.clone());

        self.structs.insert(r#struct.name.clone(), r#struct.clone());

        self.user_types
            .insert(r#struct.name.clone(), VariantOrStruct::Struct);

        Ok(())
    }

    fn check_make_struct(&mut self, make_struct: &tree::MakeStruct) -> Result<TypeId, Error> {
        let r#struct = self.constructors[&make_struct.constructor].clone();

        let parameters = r#struct
            .fields
            .iter()
            .filter_map(|type_or_generic| type_or_generic.as_generic())
            .map(|_| self.types.insert(TypeInfo::Unknown))
            .collect::<Vec<_>>();

        let exprs = make_struct
            .exprs
            .iter()
            .map(|expr| self.check_tree(expr))
            .collect::<Result<Vec<_>, _>>()?;

        for (field, expr) in r#struct.fields.iter().zip(exprs.iter()) {
            match field {
                TypeOrGeneric::Generic(r#type, generics) => {
                    let id = self.types.insert_concrete_type(r#type.clone());
                    let subs = generics
                        .iter()
                        .map(|(generic, index)| (generic.clone(), parameters[*index]))
                        .collect::<HashMap<_, _>>();
                    let id = self.types.instantiate_with(id, &subs);

                    let Ok(()) = self.types.unify(id, *expr) else {
                        return Err(Error::Unification {
                            message: "failed to unify struct fields with constructor expressions"
                                .to_string(),
                            span: make_struct.span,
                            a: self.types.construct_partially_known_type(id),
                            b: self.types.construct_partially_known_type(*expr),
                        });
                    };
                }
                _ => continue,
            }
        }

        Ok(self.types.insert(TypeInfo::Struct {
            name: r#struct.name.clone(),
            parameters,
        }))
    }

    fn check_get_field(&mut self, get_field: &tree::GetField) -> Result<TypeId, Error> {
        let r#struct = self.structs[&get_field.struct_name].clone();
        let body = self.check_tree(&get_field.body)?;

        match self.accessors[&get_field.accessor].clone() {
            TypeOrGeneric::Generic(r#type, generics) => {
                let parameters = r#struct
                    .fields
                    .iter()
                    .filter_map(|field| field.as_generic())
                    .map(|_| self.types.insert(TypeInfo::Unknown))
                    .collect::<Vec<_>>();

                let id = self.types.insert(TypeInfo::Struct {
                    name: r#struct.name.clone(),
                    parameters: parameters.clone(),
                });

                let Ok(()) = self.types.unify(id, body) else {
                    todo!()
                };

                let id = self.types.insert_concrete_type(r#type);
                let subs = generics
                    .iter()
                    .map(|(generic, index)| (generic.clone(), parameters[*index]))
                    .collect::<HashMap<_, _>>();
                let id = self.types.instantiate_with(id, &subs);

                Ok(id)
            }
            TypeOrGeneric::Type(r#type) => Ok(self.types.insert_concrete_type(r#type)),
        }
    }

    fn check_make_vec(&mut self, make_vec: &tree::MakeVec) -> Result<TypeId, Error> {
        let capacity = self.check_tree(&make_vec.capacity)?;

        let inner = self.types.insert(TypeInfo::Unknown);
        let vec = self.types.insert(TypeInfo::Vec(inner));
        let int = self.types.insert(TypeInfo::Int);

        let Ok(()) = self.types.unify(int, capacity) else {
            return Err(Error::Unification {
                span: make_vec.span,
                message: "failed to unify capacity with int".to_string(),
                a: self.types.construct_partially_known_type(int),
                b: self.types.construct_partially_known_type(capacity),
            });
        };

        Ok(vec)
    }

    fn check_vec_push(&mut self, vec_push: &tree::VecPush) -> Result<TypeId, Error> {
        let vec = self.check_tree(&vec_push.vec)?;
        let expr = self.check_tree(&vec_push.expr)?;

        let inner = self.types.insert(TypeInfo::Unknown);
        let id = self.types.insert(TypeInfo::Vec(inner));

        let Ok(()) = self.types.unify(id, vec) else {
            todo!()
        };

        let Ok(()) = self.types.unify(inner, expr) else {
            todo!()
        };

        let nil = self.types.insert(TypeInfo::Nil);

        Ok(nil)
    }

    fn check_vec_pop(&mut self, vec_pop: &tree::VecPop) -> Result<TypeId, Error> {
        let vec = self.check_tree(&vec_pop.vec)?;

        let inner = self.types.insert(TypeInfo::Unknown);
        let id = self.types.insert(TypeInfo::Vec(inner));

        let Ok(()) = self.types.unify(id, vec) else {
            todo!()
        };

        Ok(inner)
    }

    fn check_vec_ref(&mut self, vec_index: &tree::VecRef) -> Result<TypeId, Error> {
        let vec = self.check_tree(&vec_index.vec)?;

        let inner = self.types.insert(TypeInfo::Unknown);
        let id = self.types.insert(TypeInfo::Vec(inner));

        let Ok(()) = self.types.unify(id, vec) else {
            todo!()
        };

        Ok(inner)
    }

    fn check_vec_set(&mut self, vec_set: &tree::VecSet) -> Result<TypeId, Error> {
        let vec = self.check_tree(&vec_set.vec)?;
        let index = self.check_tree(&vec_set.index)?;
        let expr = self.check_tree(&vec_set.expr)?;

        let inner = self.types.insert(TypeInfo::Unknown);
        let id = self.types.insert(TypeInfo::Vec(inner));
        let int = self.types.insert(TypeInfo::Int);

        let Ok(()) = self.types.unify(id, vec) else {
            todo!()
        };

        let Ok(()) = self.types.unify(inner, expr) else {
            todo!()
        };

        let Ok(()) = self.types.unify(int, index) else {
            todo!()
        };

        Ok(inner)
    }

    fn check_vec_length(&mut self, vec_length: &tree::VecLength) -> Result<TypeId, Error> {
        let vec = self.check_tree(&vec_length.vec)?;

        let inner = self.types.insert(TypeInfo::Unknown);
        let id = self.types.insert(TypeInfo::Vec(inner));

        let Ok(()) = self.types.unify(id, vec) else {
            todo!()
        };

        let int = self.types.insert(TypeInfo::Int);

        Ok(int)
    }

    fn check_varref(&mut self, varref: &tree::VarRef) -> TypeId {
        match varref {
            tree::VarRef::Local { index, .. } => self.scopes.last().unwrap().locals[*index],
            tree::VarRef::UpValue { index, .. } => {
                let upvalue = self.scopes.last().unwrap().upvalues[*index];
                get_upvalue_type(upvalue, self.scopes.iter().rev().skip(1))
            }
            tree::VarRef::Global { name, .. } => match self.globals[name.as_str()].clone() {
                PolyType::Poly(id) => self.types.instantiate(id, &mut HashMap::new()),
                PolyType::Mono(id) => id,
            },
        }
    }

    fn check_constant(&mut self, constant: &tree::Constant) -> Result<TypeId, Error> {
        Ok(match constant {
            tree::Constant::Symbol { .. } => self.types.insert(TypeInfo::Symbol),
            tree::Constant::String { .. } => self.types.insert(TypeInfo::String),
            tree::Constant::Char { .. } => self.types.insert(TypeInfo::Char),
            tree::Constant::Int { .. } => self.types.insert(TypeInfo::Int),
            tree::Constant::Float { .. } => self.types.insert(TypeInfo::Float),
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
