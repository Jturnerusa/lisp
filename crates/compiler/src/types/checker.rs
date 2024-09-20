use super::{
    Error, MaybeUnknownType, Parameters, Rest, Type, TypeId, TypeInfo, Types, VariantOrStruct,
};
use crate::ast;
use crate::tree::{self, Il};
use std::collections::{HashMap, HashSet};
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
enum Variant {
    Struct(String, Type),
    Enum(String),
}

#[derive(Clone, Debug)]
struct Struct {
    name: String,
    fields: Vec<Type>,
}

#[derive(Clone, Debug)]
pub struct Checker {
    types: Types,
    scopes: Vec<Scope>,
    globals: HashMap<String, PolyType>,
    deftypes: HashMap<String, ast::DefType>,
    deftype_variants: HashMap<String, (usize, Variant)>,
    structs: HashMap<String, Struct>,
    constructors: HashMap<ast::StructConstructor, Struct>,
    accessors: HashMap<ast::StructAccessor, Struct>,
    user_types: HashMap<String, VariantOrStruct>,
}

impl Checker {
    pub fn new() -> Self {
        Self {
            types: Types::new(),
            scopes: Vec::new(),
            globals: HashMap::new(),
            deftypes: HashMap::new(),
            deftype_variants: HashMap::new(),
            structs: HashMap::new(),
            constructors: HashMap::new(),
            accessors: HashMap::new(),
            user_types: HashMap::new(),
        }
    }

    pub fn check(&mut self, tree: &tree::Il) -> Result<(), Error> {
        match tree {
            tree::Il::Def(def) => self.check_def(def),
            tree::Il::Lambda(lambda) => self.check_lambda(lambda, Vec::new()).map(|_| ()),
            tree::Il::If(r#if) => self.check_if(r#if).map(|_| ()),
            tree::Il::Apply(apply) => self.check_apply(apply).map(|_| ()),
            tree::Il::Set(set) => self.check_set(set).map(|_| ()),
            tree::Il::FnCall(fncall) => self.check_fncall(fncall).map(|_| ()),
            tree::Il::ArithmeticOperation(op) => self.check_aritmetic_op(op).map(|_| ()),
            tree::Il::ComparisonOperation(op) => self.check_comparison_op(op).map(|_| ()),
            tree::Il::List(list) => self.check_list(list).map(|_| ()),
            tree::Il::Cons(cons) => self.check_cons(cons).map(|_| ()),
            tree::Il::Car(car) => self.check_car(car).map(|_| ()),
            tree::Il::Cdr(cdr) => self.check_cdr(cdr).map(|_| ()),
            tree::Il::Assert(assert) => self.check_assert(assert).map(|_| ()),
            tree::Il::Decl(decl) => self.check_decl(decl),
            tree::Il::DefType(deftype) => self.deftype(deftype),
            tree::Il::MakeType(maketype) => self.check_make_type(maketype).map(|_| ()),
            tree::Il::IfLet(if_let) => self.check_if_let(if_let).map(|_| ()),
            tree::Il::DefStruct(defstruct) => self.check_defstruct(defstruct),
            tree::Il::MakeStruct(make_struct) => self.check_make_struct(make_struct).map(|_| ()),
            tree::Il::GetField(get_field) => self.check_get_field(get_field).map(|_| ()),
            _ => Ok(()),
        }
    }

    fn deftype(&mut self, deftype: &ast::DefType) -> Result<(), Error> {
        for (i, variant) in deftype.variants.iter().enumerate() {
            let constructor = format!("{}-{}", deftype.name, variant.name);
            let v = match variant
                .r#type
                .as_ref()
                .map(|r#type| Type::from_ast(r#type, &self.user_types))
            {
                Some(Ok(t)) => Variant::Struct(variant.name.clone(), t),
                Some(Err(())) => return Err(Error::InvalidType(deftype.span)),
                None => Variant::Enum(variant.name.clone()),
            };

            self.deftypes.insert(constructor.clone(), deftype.clone());
            self.deftype_variants.insert(constructor, (i, v));
        }

        self.user_types
            .insert(deftype.name.clone(), VariantOrStruct::Variant);

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

                let (parameters, _, _) = t.as_function().unwrap();

                let parameter_ids = parameters
                    .iter()
                    .map(|parameter| self.types.insert_concrete_type(parameter.clone()))
                    .collect::<Vec<_>>();

                let lambda = match &*def.body {
                    tree::Il::Lambda(lambda) => lambda,
                    _ => unreachable!(),
                };

                let ret = self.check_lambda(lambda, parameter_ids)?;

                let Ok(()) = self.types.unify(id, ret) else {
                    todo!()
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
            None => Err(Error::Annotation(def.span)),
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
                tree::Parameters::Variadic(_) => {
                    let inner = parameters.last().unwrap();
                    let list = self.types.insert(TypeInfo::List(*inner));
                    (
                        parameters[..parameters.len() - 1].to_vec(),
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
            Il::MakeStruct(make_struct) => self.check_make_struct(make_struct),
            Il::GetField(get_field) => self.check_get_field(get_field),
            Il::Assert(assert) => self.check_assert(assert),
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
        let deftype = self.deftypes[make_type.pattern.as_str()].clone();
        let parameters = deftype
            .variants
            .iter()
            .filter_map(|variant| {
                match variant
                    .r#type
                    .as_ref()
                    .map(|r#type| Type::from_ast(r#type, &self.user_types))
                {
                    Some(Ok(t)) => Some(Ok(self.types.insert_concrete_type(t))),
                    Some(Err(())) => Some(Err(Error::InvalidType(make_type.span))),
                    None => None,
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let id = self.types.insert(TypeInfo::DefType {
            name: deftype.name.clone(),
            parameters,
        });

        Ok(self.types.instantiate(id, &mut HashMap::new()))
    }

    fn check_if_let(&mut self, if_let: &tree::IfLet) -> Result<TypeId, Error> {
        let body = self.check_tree(&if_let.body)?;
        let r#return = self.types.insert(TypeInfo::Unknown);

        let (then, r#else) = if if_let.binding.is_some() {
            let variant_index = self.deftype_variants[if_let.pattern.as_str()].0;
            let variant_type = match self.types.vars[body].clone() {
                TypeInfo::DefType { name, parameters }
                    if self.deftypes[if_let.pattern.as_str()].name == name.as_str() =>
                {
                    parameters[variant_index]
                }
                _ => todo!(),
            };

            let scope = Scope {
                locals: vec![variant_type],
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
            return Err(Error::Unification {
                message: "failed unifying if-let branches".to_string(),
                span: if_let.span,
                a: MaybeUnknownType::from(self.types.construct(r#return)),
                b: MaybeUnknownType::from(self.types.construct(r#else)),
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
        let r#struct = Struct {
            name: defstruct.name.clone(),
            fields: defstruct
                .fields
                .iter()
                .map(|(_, r#type)| {
                    Type::from_ast(r#type, &self.user_types)
                        .map_err(|_| Error::InvalidType(defstruct.span))
                })
                .collect::<Result<Vec<_>, _>>()?,
        };

        self.user_types
            .insert(defstruct.name.clone(), VariantOrStruct::Struct);

        self.structs
            .insert(defstruct.name.clone(), r#struct.clone());

        let constructor = format!("make-{}", defstruct.name);
        self.constructors
            .insert(ast::StructConstructor(constructor), r#struct.clone());

        for (field_name, _) in &defstruct.fields {
            let accessor = format!("{}-{}", defstruct.name, field_name);
            self.accessors
                .insert(ast::StructAccessor(accessor), r#struct.clone());
        }

        Ok(())
    }

    fn check_make_struct(&mut self, make_struct: &tree::MakeStruct) -> Result<TypeId, Error> {
        let r#struct = self.constructors[&make_struct.constructor].clone();

        let parameters = r#struct
            .fields
            .iter()
            .zip(make_struct.exprs.iter())
            .filter(|(field, _)| field.is_generic())
            .map(|(_, expr)| self.check_tree(expr))
            .collect::<Result<Vec<_>, _>>()?;

        let id = self.types.insert(TypeInfo::Struct {
            name: make_struct.struct_name.clone(),
            parameters,
        });

        Ok(id)
    }

    fn check_get_field(&mut self, get_field: &tree::GetField) -> Result<TypeId, Error> {
        let body = self.check_tree(&get_field.body)?;
        let r#struct = self.structs[get_field.struct_name.as_str()].clone();

        let r#type = if r#struct.fields[get_field.index].is_generic() {
            let index = r#struct
                .fields
                .iter()
                .filter(|field| field.is_generic())
                .count();
            let parameters = (0..r#struct.fields.len())
                .map(|_| self.types.insert(TypeInfo::Unknown))
                .collect::<Vec<_>>();
            let id = self.types.insert(TypeInfo::Struct {
                name: get_field.struct_name.clone(),
                parameters: parameters.clone(),
            });

            let Ok(()) = self.types.unify(id, body) else {
                todo!()
            };

            parameters[index]
        } else {
            self.types
                .insert_concrete_type(r#struct.fields[get_field.index].clone())
        };

        Ok(r#type)
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
