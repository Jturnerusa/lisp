use std::collections::BTreeSet;
use vm::{Arity, UpValue};

use crate::{
    ast::{self, Ast, Quoted},
    environment::{self, Environment, Variable},
};

#[derive(Clone, Debug)]
pub struct Error<'a, T> {
    source: &'a Ast<'a, T>,
    message: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
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
pub enum Il<'a, T> {
    EvalWhenCompile(EvalWhenCompile<'a, T>),
    DefMacro(DefMacro<'a, T>),
    Lambda(Lambda<'a, T>),
    If(If<'a, T>),
    Apply(Apply<'a, T>),
    Def(Def<'a, T>),
    Set(Set<'a, T>),
    FnCall(FnCall<'a, T>),
    ArithmeticOperation(ArithmeticOperation<'a, T>),
    ComparisonOperation(ComparisonOperation<'a, T>),
    List(List<'a, T>),
    Cons(Cons<'a, T>),
    Car(Car<'a, T>),
    Cdr(Cdr<'a, T>),
    MapCreate(MapCreate<'a, T>),
    MapInsert(MapInsert<'a, T>),
    MapRetrieve(MapRetrieve<'a, T>),
    VarRef(VarRef<'a, T>),
    Constant(Constant<'a, T>),
}

#[derive(Clone, Debug)]
pub enum Constant<'a, T> {
    Symbol {
        source: &'a Ast<'a, T>,
        symbol: String,
    },
    String {
        source: &'a Ast<'a, T>,
        string: String,
    },
    Char {
        source: &'a Ast<'a, T>,
        char: char,
    },
    Int {
        source: &'a Ast<'a, T>,
        int: i64,
    },
    Bool {
        source: &'a Ast<'a, T>,
        bool: bool,
    },
    Nil {
        source: &'a Ast<'a, T>,
    },
}

#[derive(Clone, Debug)]
pub enum VarRef<'a, T> {
    Local {
        source: &'a Ast<'a, T>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    UpValue {
        source: &'a Ast<'a, T>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    Global {
        source: &'a Ast<'a, T>,
        name: String,
        r#type: Option<Type>,
    },
}

#[derive(Clone, Debug)]
pub struct Parameter<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters<'a, T> {
    Nary(Vec<Parameter<'a, T>>),
    Variadic(Vec<Parameter<'a, T>>),
}

#[derive(Clone, Debug)]
pub struct EvalWhenCompile<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub exprs: Vec<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct DefMacro<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub name: String,
    pub parameters: Parameters<'a, T>,
    pub arity: Arity,
    pub body: Vec<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct Lambda<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub parameters: Parameters<'a, T>,
    pub r#type: Option<Type>,
    pub arity: Arity,
    pub upvalues: Vec<UpValue>,
    pub body: Vec<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct If<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub predicate: Box<Il<'a, T>>,
    pub then: Box<Il<'a, T>>,
    pub r#else: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct FnCall<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub function: Box<Il<'a, T>>,
    pub args: Vec<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct Apply<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub exprs: Vec<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct List<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub exprs: Vec<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct Cons<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub lhs: Box<Il<'a, T>>,
    pub rhs: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct Car<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub body: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct Cdr<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub body: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub enum ArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct ArithmeticOperation<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub operator: ArithmeticOperator,
    pub lhs: Box<Il<'a, T>>,
    pub rhs: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub enum ComparisonOperator {
    Eq,
    Lt,
    Gt,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub operator: ComparisonOperator,
    pub lhs: Box<Il<'a, T>>,
    pub rhs: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct Def<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub parameter: Parameter<'a, T>,
    pub body: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct Set<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub target: VarRef<'a, T>,
    pub body: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct MapCreate<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub map: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct MapInsert<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub map: Box<Il<'a, T>>,
    pub key: Box<Il<'a, T>>,
    pub value: Box<Il<'a, T>>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve<'a, T> {
    pub source: &'a Ast<'a, T>,
    pub map: Box<Il<'a, T>>,
    pub key: Box<Il<'a, T>>,
}

pub struct Compiler {
    environment: Environment,
}

impl<'a, T> Il<'a, T> {
    pub fn source_ast(&self) -> &Ast<'a, T> {
        match self {
            Self::EvalWhenCompile(EvalWhenCompile { source, .. })
            | Self::DefMacro(DefMacro { source, .. })
            | Self::Lambda(Lambda { source, .. })
            | Self::ArithmeticOperation(ArithmeticOperation { source, .. })
            | Self::ComparisonOperation(ComparisonOperation { source, .. })
            | Self::Def(Def { source, .. })
            | Self::Set(Set { source, .. })
            | Self::If(If { source, .. })
            | Self::FnCall(FnCall { source, .. })
            | Self::Apply(Apply { source, .. })
            | Self::List(List { source, .. })
            | Self::Cons(Cons { source, .. })
            | Self::Car(Car { source, .. })
            | Self::Cdr(Cdr { source, .. })
            | Self::MapCreate(MapCreate { source, .. })
            | Self::MapInsert(MapInsert { source, .. })
            | Self::MapRetrieve(MapRetrieve { source, .. })
            | Self::VarRef(VarRef::Local { source, .. })
            | Self::VarRef(VarRef::UpValue { source, .. })
            | Self::VarRef(VarRef::Global { source, .. })
            | Self::Constant(Constant::Symbol { source, .. })
            | Self::Constant(Constant::String { source, .. })
            | Self::Constant(Constant::Char { source, .. })
            | Self::Constant(Constant::Int { source, .. })
            | Self::Constant(Constant::Bool { source, .. })
            | Self::Constant(Constant::Nil { source, .. }) => source,
        }
    }
}

impl Type {
    pub fn from_ast(ast: &ast::Type) -> Result<Self, ()> {
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

impl<'a, T> Parameter<'a, T> {
    pub fn from_ast(source: &'a Ast<'a, T>, parameter: &'a ast::Parameter) -> Result<Self, ()> {
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

impl<'a, T: Clone> Parameters<'a, T> {
    pub fn from_ast(source: &'a Ast<'a, T>, parameters: &'a ast::Parameters) -> Result<Self, ()> {
        Ok(match parameters {
            ast::Parameters::Normal(params) => Parameters::Nary(
                params
                    .iter()
                    .map(|param| Parameter::from_ast(source, param))
                    .collect::<Result<Vec<Parameter<_>>, ()>>()?,
            ),
            ast::Parameters::Rest(params, rest) => Parameters::Variadic(
                params
                    .iter()
                    .chain(std::iter::once(rest))
                    .map(|param| Parameter::from_ast(source, param))
                    .collect::<Result<Vec<Parameter<_>>, _>>()?,
            ),
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = Parameter<T>> + '_ {
        self.into_iter()
    }
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
        }
    }

    pub fn compile<'a, T: Clone>(
        &mut self,
        ast: &'a Ast<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        match ast {
            Ast::EvalWhenCompile(eval_when_compile) => {
                self.compile_eval_when_compile(ast, eval_when_compile)
            }
            Ast::DefMacro(defmacro) => self.compile_defmacro(ast, defmacro),
            Ast::Lambda(lambda) => self.compile_lambda(ast, lambda),
            Ast::Def(def) => self.compile_def(ast, def),
            Ast::Set(set) => self.compile_set(ast, set),
            Ast::If(r#if) => self.compile_if(ast, r#if),
            Ast::FnCall(fncall) => self.compile_fncall(ast, fncall),
            Ast::Apply(apply) => self.compile_apply(ast, apply),
            Ast::BinaryArithemticOperation(op) => self.compile_arithmetic_operation(ast, op),
            Ast::ComparisonOperation(op) => self.compile_comparison_operation(ast, op),
            Ast::List(list) => self.compile_list(ast, list),
            Ast::Cons(cons) => self.compile_cons(ast, cons),
            Ast::Car(car) => self.compile_car(ast, car),
            Ast::Cdr(cdr) => self.compile_cdr(ast, cdr),
            Ast::Constant(constant) => self.compile_constant(ast, constant),
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
            _ => todo!(),
        }
    }

    fn compile_constant<'a, T>(
        &mut self,
        source: &'a Ast<'a, T>,
        constant: &'a ast::Constant<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(match constant {
            ast::Constant::String { string, .. } => Il::Constant(Constant::String {
                source,
                string: string.clone(),
            }),
            ast::Constant::Char { char, .. } => Il::Constant(Constant::Char {
                source,
                char: *char,
            }),
            ast::Constant::Int { int, .. } => Il::Constant(Constant::Int { source, int: *int }),
            ast::Constant::Bool { bool, .. } => Il::Constant(Constant::Bool {
                source,
                bool: *bool,
            }),
            ast::Constant::Nil { .. } => Il::Constant(Constant::Nil { source }),
        })
    }

    fn compile_variable_reference<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        variable: &ast::Variable<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
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

    fn compile_eval_when_compile<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        eval_when_compile: &'a ast::EvalWhenCompile<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        if !self.environment.is_global_scope() {
            return Err(Error {
                source,
                message: "eval-when-compile must exist at global scope".to_string(),
            });
        }

        let exprs = eval_when_compile
            .exprs
            .iter()
            .map(|expr| self.compile(expr))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Il::EvalWhenCompile(EvalWhenCompile { source, exprs }))
    }

    fn compile_defmacro<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        defmacro: &'a ast::DefMacro<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        if !self.environment.is_global_scope() {
            return Err(Error {
                source,
                message: "defmacro must exist at global scope".to_string(),
            });
        }

        let arity = match &defmacro.parameters {
            ast::Parameters::Normal(_) if defmacro.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(defmacro.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(defmacro.parameters.len()),
        };

        let parameters = Parameters::from_ast(source, &defmacro.parameters).map_err(|_| Error {
            source,
            message: "failed to compile parameters".to_string(),
        })?;

        self.environment
            .push_scope(parameters.iter().map(|param| (param.name, param.r#type)));

        let body = defmacro
            .body
            .iter()
            .map(|ast| self.compile(ast))
            .collect::<Result<Vec<Il<_>>, Error<_>>>()?;

        self.environment.pop_scope();

        Ok(Il::DefMacro(DefMacro {
            source,
            name: defmacro.name.clone(),
            parameters,
            arity,
            body,
        }))
    }

    fn compile_lambda<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        lambda: &'a ast::Lambda<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
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
            .collect::<Result<Vec<Il<_>>, Error<_>>>()?;

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

    fn compile_if<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        r#if: &'a ast::If<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::If(If {
            source,
            predicate: Box::new(self.compile(&r#if.predicate)?),
            then: Box::new(self.compile(&r#if.then)?),
            r#else: Box::new(self.compile(&r#if.r#else)?),
        }))
    }

    fn compile_def<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        def: &'a ast::Def<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        self.environment.insert_global(
            def.parameter.name.as_str(),
            match def.parameter.r#type.as_ref().map(Type::from_ast) {
                Some(Ok(t)) => Some(t),
                Some(Err(_)) => {
                    return Err(Error {
                        source,
                        message: "failed to parse type".to_string(),
                    })
                }
                None => None,
            },
        );

        Ok(Il::Def(Def {
            source,
            parameter: Parameter::from_ast(source, &def.parameter).map_err(|_| Error {
                source,
                message: "failed to parse parameter".to_string(),
            })?,
            body: Box::new(self.compile(&def.body)?),
        }))
    }

    fn compile_set<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        set: &'a ast::Set<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::Set(Set {
            source,
            target: match self.environment.resolve(set.variable.as_str()) {
                Some(Variable::Local(index, r#type)) => VarRef::Local {
                    source,
                    name: set.variable.clone(),
                    r#type,
                    index,
                },
                Some(Variable::Upvalue(index, r#type)) => VarRef::UpValue {
                    source,
                    name: set.variable.clone(),
                    r#type,
                    index,
                },
                Some(Variable::Global(r#type)) => VarRef::Global {
                    source,
                    name: set.variable.clone(),
                    r#type,
                },
                None => {
                    return Err(Error {
                        source,
                        message: "unknown variable".to_string(),
                    })
                }
            },
            body: Box::new(self.compile(&set.body)?),
        }))
    }

    fn compile_quote<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        quote: &'a ast::Quote<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(match &quote.body {
            Quoted::List { list, .. } => self.compile_quoted_list(source, list.as_slice())?,
            Quoted::Symbol { symbol, .. } => Il::Constant(Constant::Symbol {
                source,
                symbol: symbol.clone(),
            }),
            Quoted::String { string, .. } => Il::Constant(Constant::String {
                source,
                string: string.clone(),
            }),
            Quoted::Char { char, .. } => Il::Constant(Constant::Char {
                source,
                char: *char,
            }),
            Quoted::Int { int, .. } => Il::Constant(Constant::Int { source, int: *int }),
            Quoted::Bool { bool, .. } => Il::Constant(Constant::Bool {
                source,
                bool: *bool,
            }),
            Quoted::Nil { .. } => Il::Constant(Constant::Nil { source }),
        })
    }

    #[allow(clippy::only_used_in_recursion)]
    fn compile_quoted_list<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        list: &'a [Quoted<'a, T>],
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::List(List {
            source,
            exprs: list
                .iter()
                .map(|quoted| {
                    Ok(match quoted {
                        Quoted::List { list, .. } => {
                            self.compile_quoted_list(source, list.as_slice())?
                        }
                        Quoted::Symbol { symbol, .. } => Il::Constant(Constant::Symbol {
                            source,
                            symbol: symbol.clone(),
                        }),
                        Quoted::String { string, .. } => Il::Constant(Constant::String {
                            source,
                            string: string.clone(),
                        }),
                        Quoted::Char { char, .. } => Il::Constant(Constant::Char {
                            source,
                            char: *char,
                        }),
                        Quoted::Int { int, .. } => {
                            Il::Constant(Constant::Int { source, int: *int })
                        }
                        Quoted::Bool { bool, .. } => Il::Constant(Constant::Bool {
                            source,
                            bool: *bool,
                        }),
                        Quoted::Nil { .. } => Il::Constant(Constant::Nil { source }),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_fncall<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        fncall: &'a ast::FnCall<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::FnCall(FnCall {
            source,
            function: Box::new(self.compile(fncall.exprs.first().unwrap())?),
            args: fncall
                .exprs
                .iter()
                .skip(1)
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_apply<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        apply: &'a ast::Apply<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::Apply(Apply {
            source,
            exprs: apply
                .exprs
                .iter()
                .map(|expr| self.compile(expr))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_arithmetic_operation<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        op: &'a ast::BinaryArithmeticOperation<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::ArithmeticOperation(ArithmeticOperation {
            source,
            operator: match op.operator {
                ast::BinaryArithmeticOperator::Add => ArithmeticOperator::Add,
                ast::BinaryArithmeticOperator::Sub => ArithmeticOperator::Sub,
                ast::BinaryArithmeticOperator::Mul => ArithmeticOperator::Mul,
                ast::BinaryArithmeticOperator::Div => ArithmeticOperator::Div,
            },
            lhs: Box::new(self.compile(&op.lhs)?),
            rhs: Box::new(self.compile(&op.rhs)?),
        }))
    }

    fn compile_comparison_operation<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        op: &'a ast::ComparisonOperation<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::ComparisonOperation(ComparisonOperation {
            source,
            operator: match op.operator {
                ast::ComparisonOperator::Eq => ComparisonOperator::Eq,
                ast::ComparisonOperator::Lt => ComparisonOperator::Lt,
                ast::ComparisonOperator::Gt => ComparisonOperator::Gt,
            },
            lhs: Box::new(self.compile(&op.lhs)?),
            rhs: Box::new(self.compile(&op.rhs)?),
        }))
    }

    fn compile_list<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        list: &'a ast::List<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::List(List {
            source,
            exprs: list
                .exprs
                .iter()
                .map(|expr| self.compile(expr))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_cons<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        cons: &'a ast::Cons<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::Cons(Cons {
            source,
            lhs: Box::new(self.compile(&cons.lhs)?),
            rhs: Box::new(self.compile(&cons.rhs)?),
        }))
    }

    fn compile_car<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        car: &'a ast::Car<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::Car(Car {
            source,
            body: Box::new(self.compile(&car.body)?),
        }))
    }

    fn compile_cdr<'a, T: Clone>(
        &mut self,
        source: &'a Ast<'a, T>,
        cdr: &'a ast::Cdr<'a, T>,
    ) -> Result<Il<'a, T>, Error<'a, T>> {
        Ok(Il::Cdr(Cdr {
            source,
            body: Box::new(self.compile(&cdr.body)?),
        }))
    }
}

impl<'a, T: Clone> IntoIterator for &'a Parameters<'a, T> {
    type Item = Parameter<'a, T>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Parameters::Nary(params) | Parameters::Variadic(params) => params.iter().cloned(),
        }
    }
}
