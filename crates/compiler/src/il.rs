use crate::{
    ast::{self, Ast, Quoted},
    bytecode,
    environment::{self, Environment, Variable},
    il,
};
use reader::{Reader, Sexpr};
use std::{collections::BTreeSet, hash::Hash};
use vm::{Arity, OpCodeTable, UpValue, Vm};

#[derive(Debug, thiserror::Error)]
pub enum Error<'ast, 'sexpr, 'context> {
    #[error("il compiler error: {message}")]
    Il {
        ast: &'ast Ast<'sexpr, 'context>,
        message: String,
    },

    #[error("reader error: {0}")]
    Reader(#[from] reader::Error<'static>),

    #[error("ast error: {0}")]
    Ast(#[from] ast::Error<'static, 'static>),

    #[error("bytecode compiler error: {0}")]
    Bytecode(#[from] bytecode::Error<'static, 'static, 'static, 'static>),

    #[error("vm error: {0}")]
    Vm(#[from] vm::Error),

    #[error("vm error: {sexpr}")]
    VmWithDebug {
        error: vm::Error,
        sexpr: &'sexpr Sexpr<'context>,
    },
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
pub enum Il<'ast, 'sexpr, 'context> {
    Lambda(Lambda<'ast, 'sexpr, 'context>),
    If(If<'ast, 'sexpr, 'context>),
    Apply(Apply<'ast, 'sexpr, 'context>),
    Def(Def<'ast, 'sexpr, 'context>),
    Set(Set<'ast, 'sexpr, 'context>),
    FnCall(FnCall<'ast, 'sexpr, 'context>),
    ArithmeticOperation(ArithmeticOperation<'ast, 'sexpr, 'context>),
    ComparisonOperation(ComparisonOperation<'ast, 'sexpr, 'context>),
    List(List<'ast, 'sexpr, 'context>),
    Cons(Cons<'ast, 'sexpr, 'context>),
    Car(Car<'ast, 'sexpr, 'context>),
    Cdr(Cdr<'ast, 'sexpr, 'context>),
    MapCreate(MapCreate<'ast, 'sexpr, 'context>),
    MapInsert(MapInsert<'ast, 'sexpr, 'context>),
    MapRetrieve(MapRetrieve<'ast, 'sexpr, 'context>),
    IsType(IsType<'ast, 'sexpr, 'context>),
    Assert(Assert<'ast, 'sexpr, 'context>),
    VarRef(VarRef<'ast, 'sexpr, 'context>),
    Constant(Constant<'ast, 'sexpr, 'context>),
}

#[derive(Clone, Debug)]
pub enum Constant<'ast, 'sexpr, 'context> {
    Symbol {
        source: &'ast Ast<'sexpr, 'context>,
        symbol: String,
    },
    String {
        source: &'ast Ast<'sexpr, 'context>,
        string: String,
    },
    Char {
        source: &'ast Ast<'sexpr, 'context>,
        char: char,
    },
    Int {
        source: &'ast Ast<'sexpr, 'context>,
        int: i64,
    },
    Bool {
        source: &'ast Ast<'sexpr, 'context>,
        bool: bool,
    },
    Nil {
        source: &'ast Ast<'sexpr, 'context>,
    },
}

#[derive(Clone, Debug)]
pub enum VarRef<'ast, 'sexpr, 'context> {
    Local {
        source: &'ast Ast<'sexpr, 'context>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    UpValue {
        source: &'ast Ast<'sexpr, 'context>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    Global {
        source: &'ast Ast<'sexpr, 'context>,
        name: String,
        r#type: Option<Type>,
    },
}

#[derive(Clone, Debug)]
pub struct Parameter<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters<'ast, 'sexpr, 'context> {
    Nary(Vec<Parameter<'ast, 'sexpr, 'context>>),
    Variadic(Vec<Parameter<'ast, 'sexpr, 'context>>),
}

#[derive(Clone, Debug)]
pub struct Lambda<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub parameters: Parameters<'ast, 'sexpr, 'context>,
    pub r#type: Option<Type>,
    pub arity: Arity,
    pub upvalues: Vec<UpValue>,
    pub body: Vec<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct If<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub predicate: Box<Il<'ast, 'sexpr, 'context>>,
    pub then: Box<Il<'ast, 'sexpr, 'context>>,
    pub r#else: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct FnCall<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub function: Box<Il<'ast, 'sexpr, 'context>>,
    pub args: Vec<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Apply<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub exprs: Vec<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct List<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub exprs: Vec<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Cons<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub lhs: Box<Il<'ast, 'sexpr, 'context>>,
    pub rhs: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Car<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub body: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Cdr<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub body: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub enum ArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct ArithmeticOperation<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub operator: ArithmeticOperator,
    pub lhs: Box<Il<'ast, 'sexpr, 'context>>,
    pub rhs: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub enum ComparisonOperator {
    Eq,
    Lt,
    Gt,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub operator: ComparisonOperator,
    pub lhs: Box<Il<'ast, 'sexpr, 'context>>,
    pub rhs: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Def<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub parameter: Parameter<'ast, 'sexpr, 'context>,
    pub body: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Set<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub target: VarRef<'ast, 'sexpr, 'context>,
    pub body: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct MapCreate<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub map: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct MapInsert<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub map: Box<Il<'ast, 'sexpr, 'context>>,
    pub key: Box<Il<'ast, 'sexpr, 'context>>,
    pub value: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub map: Box<Il<'ast, 'sexpr, 'context>>,
    pub key: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct IsType<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub r#type: Type,
    pub body: Box<Il<'ast, 'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Assert<'ast, 'sexpr, 'context> {
    pub source: &'ast Ast<'sexpr, 'context>,
    pub body: Box<Il<'ast, 'sexpr, 'context>>,
}

pub struct Compiler {
    environment: Environment,
}

impl<'ast, 'sexpr, 'context> VarRef<'ast, 'sexpr, 'context> {
    pub fn source(&self) -> &'ast Ast<'sexpr, 'context> {
        match self {
            Self::Local { source, .. }
            | Self::UpValue { source, .. }
            | Self::Global { source, .. } => source,
        }
    }
}

impl<'ast, 'sexpr, 'context> Constant<'ast, 'sexpr, 'context> {
    pub fn source(&self) -> &'ast Ast<'sexpr, 'context> {
        match self {
            Self::Symbol { source, .. }
            | Self::String { source, .. }
            | Self::Char { source, .. }
            | Self::Int { source, .. }
            | Self::Bool { source, .. }
            | Self::Nil { source } => source,
        }
    }
}

impl<'ast, 'sexpr, 'context> Il<'ast, 'sexpr, 'context> {
    pub fn source_ast(&self) -> &Ast<'sexpr, 'context> {
        match self {
            Self::Lambda(Lambda { source, .. })
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
            | Self::IsType(IsType { source, .. })
            | Self::Assert(Assert { source, .. })
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

impl<'ast, 'sexpr, 'context> Parameter<'ast, 'sexpr, 'context> {
    pub fn from_ast(
        source: &'ast Ast<'sexpr, 'context>,
        parameter: &'ast ast::Parameter,
    ) -> Result<Self, ()> {
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

impl<'ast, 'sexpr, 'context> Parameters<'ast, 'sexpr, 'context> {
    pub fn from_ast(
        source: &'ast Ast<'sexpr, 'context>,
        parameters: &'ast ast::Parameters,
    ) -> Result<Self, ()> {
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

    pub fn compile<'ast_compiler, 'vm, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        ast: &'ast Ast<'sexpr, 'context>,
        vm: &'vm mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        match ast {
            Ast::EvalWhenCompile(eval_when_compile) => {
                self.eval_when_compile(ast, eval_when_compile, vm, ast_compiler)
            }
            Ast::DefMacro(defmacro) => self.compile_defmacro(ast, defmacro, vm, ast_compiler),
            Ast::Lambda(lambda) => self.compile_lambda(ast, lambda, vm, ast_compiler),
            Ast::Def(def) => self.compile_def(ast, def, vm, ast_compiler),
            Ast::Set(set) => self.compile_set(ast, set, vm, ast_compiler),
            Ast::If(r#if) => self.compile_if(ast, r#if, vm, ast_compiler),
            Ast::MacroCall(macro_call) => self.eval_macro(ast, macro_call, vm, ast_compiler),
            Ast::FnCall(fncall) => self.compile_fncall(ast, fncall, vm, ast_compiler),
            Ast::Quote(quote) => self.compile_quoted(ast, &quote.body),
            Ast::Apply(apply) => self.compile_apply(ast, apply, vm, ast_compiler),
            Ast::BinaryArithemticOperation(op) => {
                self.compile_arithmetic_operation(ast, op, vm, ast_compiler)
            }
            Ast::ComparisonOperation(op) => {
                self.compile_comparison_operation(ast, op, vm, ast_compiler)
            }
            Ast::List(list) => self.compile_list(ast, list, vm, ast_compiler),
            Ast::Cons(cons) => self.compile_cons(ast, cons, vm, ast_compiler),
            Ast::Car(car) => self.compile_car(ast, car, vm, ast_compiler),
            Ast::Cdr(cdr) => self.compile_cdr(ast, cdr, vm, ast_compiler),
            Ast::IsType(is_type) => self.compile_is_type(ast, is_type, vm, ast_compiler),
            Ast::Assert(assert) => self.compile_assert(ast, assert, vm, ast_compiler),
            Ast::Constant(constant) => self.compile_constant(ast, constant),
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
        }
    }

    fn eval_when_compile<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        eval_when_compile: &'ast ast::EvalWhenCompile<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        let mut opcode_table = OpCodeTable::new();

        for expr in &eval_when_compile.exprs {
            let il = Box::leak(Box::new(self.compile(expr, vm, ast_compiler)?));

            bytecode::compile(il, &mut opcode_table)?;
        }

        vm.eval(&opcode_table)
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        Ok(Il::Constant(Constant::Nil { source }))
    }

    fn compile_constant<'ast, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        constant: &'ast ast::Constant<'sexpr, 'context>,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
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

    fn compile_variable_reference<'ast, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        variable: &'ast ast::Variable<'sexpr, 'context>,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
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
                return Err(Error::Il {
                    ast: source,
                    message: format!("unknown variable referenced: {}", variable.name),
                })
            }
        })
    }

    fn compile_defmacro<'ast_compiler, 'vm, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        defmacro: &'ast ast::DefMacro<'sexpr, 'context>,
        vm: &'vm mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        let arity = match &defmacro.parameters {
            ast::Parameters::Normal(_) if defmacro.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(defmacro.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(defmacro.parameters.len() - 1),
        };

        let parameters =
            Parameters::from_ast(source, &defmacro.parameters).map_err(|_| Error::Il {
                ast: source,
                message: "failed to compile parameters".to_string(),
            })?;

        self.environment
            .push_scope(parameters.iter().map(|param| (param.name, param.r#type)));

        let body = defmacro
            .body
            .iter()
            .map(|ast| self.compile(ast, vm, ast_compiler))
            .collect::<Result<Vec<Il>, Error>>()?;

        let lambda = Box::leak(Box::new(Il::Lambda(il::Lambda {
            source,
            parameters,
            r#type: None,
            upvalues: Vec::new(),
            arity,
            body,
        })));

        let mut opcodes = OpCodeTable::new();

        bytecode::compile(lambda, &mut opcodes)?;

        vm.eval(&opcodes)
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        vm.def_global(defmacro.name.as_str())?;

        Ok(Il::Constant(Constant::Nil { source }))
    }

    fn eval_macro<'ast, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        macro_call: &'ast ast::MacroCall<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        let mut opcode_table = OpCodeTable::new();

        for arg in &macro_call.args {
            let il = Box::leak(Box::new(self.compile_quoted(source, arg)?));
            bytecode::compile(Box::leak(Box::new(il)), &mut opcode_table).unwrap();
        }

        vm.get_global(macro_call.r#macro.as_str())?;

        vm.eval(&opcode_table)
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        vm.call(macro_call.args.len())?;

        vm.eval(&OpCodeTable::new())
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        let Some(object) = vm.pop().map(|local| local.into_object()) else {
            return Ok(Il::Constant(Constant::Nil { source }));
        };

        let mut buff = String::new();

        object.print(&mut buff).map_err(|_| Error::Il {
            ast: source,
            message: "failed to print macro result".to_string(),
        })?;

        let context: &'static _ = Box::leak(Box::new(reader::Context::new(
            buff.as_str(),
            "macro-expansion",
        )));
        let mut reader = Reader::new(context);
        let sexpr: &'static _ = Box::leak(Box::new(reader.next().unwrap()?));
        let ast: &'static _ = Box::leak(Box::new(ast_compiler.compile(sexpr)?));

        self.compile(ast, vm, ast_compiler)
    }

    fn compile_lambda<'ast_compiler, 'vm, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        lambda: &'ast ast::Lambda<'sexpr, 'context>,
        vm: &'vm mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        let arity = match &lambda.parameters {
            ast::Parameters::Normal(_) if lambda.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(lambda.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(lambda.parameters.len() - 1),
        };

        let parameters =
            Parameters::from_ast(source, &lambda.parameters).map_err(|_| Error::Il {
                ast: source,
                message: "failed to compile parameters".to_string(),
            })?;

        self.environment
            .push_scope(parameters.iter().map(|param| (param.name, param.r#type)));

        let body = lambda
            .body
            .iter()
            .map(|ast| self.compile(ast, vm, ast_compiler))
            .collect::<Result<Vec<Il>, Error>>()?;

        let upvalues = self.environment.upvalues().collect::<Vec<UpValue>>();

        let r#type = match lambda.r#type.as_ref().map(Type::from_ast) {
            Some(Ok(t)) => Some(t),
            Some(Err(_)) => {
                return Err(Error::Il {
                    ast: source,
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

    fn compile_if<'ast_compiler, 'vm, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        r#if: &'ast ast::If<'sexpr, 'context>,
        vm: &'vm mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::If(If {
            source,
            predicate: Box::new(self.compile(&r#if.predicate, vm, ast_compiler)?),
            then: Box::new(self.compile(&r#if.then, vm, ast_compiler)?),
            r#else: Box::new(self.compile(&r#if.r#else, vm, ast_compiler)?),
        }))
    }

    fn compile_def<'ast_compiler, 'vm, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        def: &'ast ast::Def<'sexpr, 'context>,
        vm: &'vm mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        self.environment.insert_global(
            def.parameter.name.as_str(),
            match def.parameter.r#type.as_ref().map(Type::from_ast) {
                Some(Ok(t)) => Some(t),
                Some(Err(_)) => {
                    return Err(Error::Il {
                        ast: source,
                        message: "failed to parse type".to_string(),
                    })
                }
                None => None,
            },
        );

        Ok(Il::Def(Def {
            source,
            parameter: Parameter::from_ast(source, &def.parameter).map_err(|_| Error::Il {
                ast: source,
                message: "failed to parse parameter".to_string(),
            })?,
            body: Box::new(self.compile(&def.body, vm, ast_compiler)?),
        }))
    }

    fn compile_set<'ast_compiler, 'vm, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        set: &'ast ast::Set<'sexpr, 'context>,
        vm: &'vm mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
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
                    return Err(Error::Il {
                        ast: source,
                        message: "unknown variable".to_string(),
                    })
                }
            },
            body: Box::new(self.compile(&set.body, vm, ast_compiler)?),
        }))
    }

    fn compile_quoted<'ast, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        quoted: &'ast ast::Quoted<'sexpr, 'context>,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(match &quoted {
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
    fn compile_quoted_list<'ast, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        list: &'ast [Quoted<'sexpr, 'context>],
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
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
                .collect::<Result<Vec<_>, Error<'ast, 'sexpr, 'context>>>()?,
        }))
    }

    fn compile_fncall<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        fncall: &'ast ast::FnCall<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::FnCall(FnCall {
            source,
            function: Box::new(self.compile(&fncall.function, vm, ast_compiler)?),
            args: fncall
                .exprs
                .iter()
                .map(|arg| self.compile(arg, vm, ast_compiler))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_apply<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        apply: &'ast ast::Apply<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::Apply(Apply {
            source,
            exprs: apply
                .exprs
                .iter()
                .map(|expr| self.compile(expr, vm, ast_compiler))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_arithmetic_operation<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        op: &'ast ast::BinaryArithmeticOperation<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::ArithmeticOperation(ArithmeticOperation {
            source,
            operator: match op.operator {
                ast::BinaryArithmeticOperator::Add => ArithmeticOperator::Add,
                ast::BinaryArithmeticOperator::Sub => ArithmeticOperator::Sub,
                ast::BinaryArithmeticOperator::Mul => ArithmeticOperator::Mul,
                ast::BinaryArithmeticOperator::Div => ArithmeticOperator::Div,
            },
            lhs: Box::new(self.compile(&op.lhs, vm, ast_compiler)?),
            rhs: Box::new(self.compile(&op.rhs, vm, ast_compiler)?),
        }))
    }

    fn compile_comparison_operation<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        op: &'ast ast::ComparisonOperation<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::ComparisonOperation(ComparisonOperation {
            source,
            operator: match op.operator {
                ast::ComparisonOperator::Eq => ComparisonOperator::Eq,
                ast::ComparisonOperator::Lt => ComparisonOperator::Lt,
                ast::ComparisonOperator::Gt => ComparisonOperator::Gt,
            },
            lhs: Box::new(self.compile(&op.lhs, vm, ast_compiler)?),
            rhs: Box::new(self.compile(&op.rhs, vm, ast_compiler)?),
        }))
    }

    fn compile_list<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        list: &'ast ast::List<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::List(List {
            source,
            exprs: list
                .exprs
                .iter()
                .map(|expr| self.compile(expr, vm, ast_compiler))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_cons<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        cons: &'ast ast::Cons<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::Cons(Cons {
            source,
            lhs: Box::new(self.compile(&cons.lhs, vm, ast_compiler)?),
            rhs: Box::new(self.compile(&cons.rhs, vm, ast_compiler)?),
        }))
    }

    fn compile_car<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        car: &'ast ast::Car<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::Car(Car {
            source,
            body: Box::new(self.compile(&car.body, vm, ast_compiler)?),
        }))
    }

    fn compile_cdr<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        cdr: &'ast ast::Cdr<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::Cdr(Cdr {
            source,
            body: Box::new(self.compile(&cdr.body, vm, ast_compiler)?),
        }))
    }

    fn compile_is_type<'ast_compiler, 'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        is_type: &'ast ast::IsType<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &'ast_compiler mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::IsType(IsType {
            source,
            r#type: match is_type.parameter {
                ast::IsTypeParameter::Function => Type::Function,
                ast::IsTypeParameter::Cons => Type::Cons,
                ast::IsTypeParameter::Symbol => Type::Symbol,
                ast::IsTypeParameter::String => Type::String,
                ast::IsTypeParameter::Char => Type::Char,
                ast::IsTypeParameter::Int => Type::Int,
                ast::IsTypeParameter::Bool => Type::Bool,
                ast::IsTypeParameter::Nil => Type::Nil,
            },
            body: Box::new(self.compile(&is_type.body, vm, ast_compiler)?),
        }))
    }

    fn compile_assert<'ast: 'static, 'sexpr, 'context>(
        &mut self,
        source: &'ast Ast<'sexpr, 'context>,
        assert: &'ast ast::Assert<'sexpr, 'context>,
        vm: &mut Vm<&'sexpr Sexpr<'context>>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Il<'ast, 'sexpr, 'context>, Error<'ast, 'sexpr, 'context>> {
        Ok(Il::Assert(Assert {
            source,
            body: Box::new(self.compile(&assert.body, vm, ast_compiler)?),
        }))
    }
}

impl<'parameters, 'ast, 'sexpr, 'context> IntoIterator
    for &'parameters Parameters<'ast, 'sexpr, 'context>
{
    type Item = Parameter<'ast, 'sexpr, 'context>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Parameters::Nary(params) | Parameters::Variadic(params) => params.iter().cloned(),
        }
    }
}
