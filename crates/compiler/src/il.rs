use std::{
    fs::File,
    io::{self, Read},
    path::{Path, PathBuf},
};

use crate::{
    ast::{self, Ast, Quoted},
    bytecode,
    environment::{self, Environment, Variable},
    il,
};
use reader::{Reader, Sexpr};
use unwrap_enum::{EnumAs, EnumIs};
use vm::{Arity, OpCodeTable, UpValue, Vm};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("il compiler error: {message}")]
    Il { ast: Ast, message: String },

    #[error("reader error: {0}")]
    Reader(#[from] reader::Error<'static>),

    #[error("ast error: {0}")]
    Ast(#[from] ast::Error),

    #[error("bytecode compiler error: {0}")]
    Bytecode(#[from] bytecode::Error),

    #[error("vm error: {0}")]
    Vm(#[from] vm::Error),

    #[error("vm error: {sexpr}")]
    VmWithDebug {
        error: vm::Error,
        sexpr: &'static Sexpr<'static>,
    },

    #[error("io error: {0}")]
    Io(#[from] io::Error),
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Il {
    Lambda(Lambda),
    If(If),
    Apply(Apply),
    Def(Def),
    Set(Set),
    SetBox(SetBox),
    Box(Box),
    UnBox(UnBox),
    FnCall(FnCall),
    ArithmeticOperation(ArithmeticOperation),
    ComparisonOperation(ComparisonOperation),
    List(List),
    Cons(Cons),
    Car(Car),
    Cdr(Cdr),
    MapCreate(MapCreate),
    MapInsert(MapInsert),
    MapRetrieve(MapRetrieve),
    MapItems(MapItems),
    IsType(IsType),
    Assert(Assert),
    VarRef(VarRef),
    Constant(Constant),
}

#[derive(Clone, Debug)]
pub enum Type {
    Scalar(String),
    Composite(Vec<Type>),
}

#[derive(Clone, Debug)]
pub struct Module {
    pub source: Ast,
    pub name: String,
}

#[derive(Clone, Debug)]
pub enum Constant {
    Symbol { source: Ast, symbol: String },
    String { source: Ast, string: String },
    Char { source: Ast, char: char },
    Int { source: Ast, int: i64 },
    Bool { source: Ast, bool: bool },
    Nil { source: Ast },
}

#[derive(Clone, Debug)]
pub enum VarRef {
    Local {
        source: Ast,
        name: String,
        index: usize,
    },
    UpValue {
        source: Ast,
        name: String,
        index: usize,
    },
    Global {
        source: Ast,
        name: String,
    },
}

#[derive(Clone, Debug)]
pub struct Parameter {
    pub source: Ast,
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters {
    Nary(Vec<Parameter>),
    Variadic(Vec<Parameter>),
}

#[derive(Clone, Debug)]
pub struct Lambda {
    pub source: Ast,
    pub parameters: Parameters,
    pub r#type: Option<Type>,
    pub arity: Arity,
    pub upvalues: Vec<UpValue>,
    pub body: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct If {
    pub source: Ast,
    pub predicate: std::boxed::Box<Il>,
    pub then: std::boxed::Box<Il>,
    pub r#else: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct FnCall {
    pub source: Ast,
    pub function: std::boxed::Box<Il>,
    pub args: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct Apply {
    pub source: Ast,
    pub function: std::boxed::Box<Il>,
    pub list: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct List {
    pub source: Ast,
    pub exprs: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct Cons {
    pub source: Ast,
    pub lhs: std::boxed::Box<Il>,
    pub rhs: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Car {
    pub source: Ast,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Cdr {
    pub source: Ast,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub enum ArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct ArithmeticOperation {
    pub source: Ast,
    pub operator: ArithmeticOperator,
    pub lhs: std::boxed::Box<Il>,
    pub rhs: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub enum ComparisonOperator {
    Eq,
    Lt,
    Gt,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation {
    pub source: Ast,
    pub operator: ComparisonOperator,
    pub lhs: std::boxed::Box<Il>,
    pub rhs: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Def {
    pub source: Ast,
    pub parameter: Parameter,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Set {
    pub source: Ast,
    pub target: VarRef,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct SetBox {
    pub source: Ast,
    pub target: std::boxed::Box<Il>,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Box {
    pub source: Ast,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct UnBox {
    pub source: Ast,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapCreate {
    pub source: Ast,
}

#[derive(Clone, Debug)]
pub struct MapInsert {
    pub source: Ast,
    pub map: std::boxed::Box<Il>,
    pub key: std::boxed::Box<Il>,
    pub value: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve {
    pub source: Ast,
    pub map: std::boxed::Box<Il>,
    pub key: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapItems {
    pub source: Ast,
    pub map: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub enum IsTypeParameter {
    Function,
    Cons,
    Symbol,
    String,
    Char,
    Int,
    Bool,
    Nil,
}

#[derive(Clone, Debug)]
pub struct IsType {
    pub source: Ast,
    pub r#type: IsTypeParameter,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Assert {
    pub source: Ast,
    pub body: std::boxed::Box<Il>,
}

pub struct Compiler {
    environment: Environment,
}

impl Type {
    fn from_ast(ast: &ast::Type) -> Self {
        match ast {
            ast::Type::Scalar(scalar) => Self::Scalar(scalar.clone()),
            ast::Type::Composite(composite) => {
                Self::Composite(composite.iter().map(Type::from_ast).collect())
            }
        }
    }
}

impl VarRef {
    pub fn source(&self) -> &Ast {
        match self {
            Self::Local { source, .. }
            | Self::UpValue { source, .. }
            | Self::Global { source, .. } => source,
        }
    }
}

impl Constant {
    pub fn source(&self) -> &Ast {
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

impl Il {
    pub fn source_ast(&self) -> &Ast {
        match self {
            Self::Lambda(Lambda { source, .. })
            | Self::ArithmeticOperation(ArithmeticOperation { source, .. })
            | Self::ComparisonOperation(ComparisonOperation { source, .. })
            | Self::Def(Def { source, .. })
            | Self::Set(Set { source, .. })
            | Self::SetBox(SetBox { source, .. })
            | Self::Box(Box { source, .. })
            | Self::UnBox(UnBox { source, .. })
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
            | Self::MapItems(MapItems { source, .. })
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

impl Parameter {
    pub fn from_ast(source: &Ast, parameter: &ast::Parameter) -> Result<Self, ()> {
        Ok(Self {
            source: source.clone(),
            name: parameter.name.clone(),
            r#type: parameter.r#type.as_ref().map(Type::from_ast),
        })
    }
}

impl Parameters {
    pub fn from_ast(source: &Ast, parameters: &ast::Parameters) -> Result<Self, ()> {
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

    pub fn compile(
        &mut self,
        ast: &Ast,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        match ast {
            Ast::Require(require) => {
                self.compile_require(ast, require, vm, ast_compiler, find_module)
            }
            Ast::EvalWhenCompile(eval_when_compile) => {
                self.eval_when_compile(ast, eval_when_compile, vm, ast_compiler, find_module)
            }
            Ast::DefMacro(defmacro) => {
                self.compile_defmacro(ast, defmacro, vm, ast_compiler, find_module)
            }
            Ast::Lambda(lambda) => self.compile_lambda(ast, lambda, vm, ast_compiler, find_module),
            Ast::Def(def) => self.compile_def(ast, def, vm, ast_compiler, find_module),
            Ast::Decl(decl) => self.compile_decl(ast, decl),
            Ast::Set(set) => self.compile_set(ast, set, vm, ast_compiler, find_module),
            Ast::SetBox(setbox) => self.compile_set_box(ast, setbox, vm, ast_compiler, find_module),
            Ast::Box(r#box) => self.compile_box(ast, r#box, vm, ast_compiler, find_module),
            Ast::UnBox(unbox) => self.compile_unbox(ast, unbox, vm, ast_compiler, find_module),
            Ast::If(r#if) => self.compile_if(ast, r#if, vm, ast_compiler, find_module),
            Ast::MacroCall(macro_call) => {
                self.eval_macro(ast, macro_call, vm, ast_compiler, find_module)
            }
            Ast::FnCall(fncall) => self.compile_fncall(ast, fncall, vm, ast_compiler, find_module),
            Ast::Quote(quote) => self.compile_quoted(ast, &quote.body),
            Ast::Apply(apply) => self.compile_apply(ast, apply, vm, ast_compiler, find_module),
            Ast::BinaryArithemticOperation(op) => {
                self.compile_arithmetic_operation(ast, op, vm, ast_compiler, find_module)
            }
            Ast::ComparisonOperation(op) => {
                self.compile_comparison_operation(ast, op, vm, ast_compiler, find_module)
            }
            Ast::List(list) => self.compile_list(ast, list, vm, ast_compiler, find_module),
            Ast::Cons(cons) => self.compile_cons(ast, cons, vm, ast_compiler, find_module),
            Ast::Car(car) => self.compile_car(ast, car, vm, ast_compiler, find_module),
            Ast::Cdr(cdr) => self.compile_cdr(ast, cdr, vm, ast_compiler, find_module),
            Ast::IsType(is_type) => {
                self.compile_is_type(ast, is_type, vm, ast_compiler, find_module)
            }
            Ast::MapCreate(_) => self.compile_map_create(ast),
            Ast::MapInsert(map_insert) => {
                self.compile_map_insert(ast, map_insert, vm, ast_compiler, find_module)
            }
            Ast::MapRetrieve(map_retrieve) => {
                self.compile_map_retrieve(ast, map_retrieve, vm, ast_compiler, find_module)
            }
            Ast::MapItems(map_items) => {
                self.compile_map_items(ast, map_items, vm, ast_compiler, find_module)
            }
            Ast::Assert(assert) => self.compile_assert(ast, assert, vm, ast_compiler, find_module),
            Ast::GenSym(_) => self.compile_gensym(ast),
            Ast::Constant(constant) => self.compile_constant(ast, constant),
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
        }
    }

    fn compile_require(
        &mut self,
        source: &Ast,
        require: &ast::Require,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let module = PathBuf::from(require.module.as_str());

        let path = match find_module(module.as_path()) {
            Some(Ok(p)) => p,
            Some(Err(e)) => {
                return Err(Error::Il {
                    ast: source.clone(),
                    message: format!("{e}"),
                })
            }
            None => {
                return Err(Error::Il {
                    ast: source.clone(),
                    message: "failed to find module".to_string(),
                })
            }
        };

        let mut file = File::open(path.as_path())?;

        let mut buff = String::new();

        file.read_to_string(&mut buff)?;

        let context: &'static _ = std::boxed::Box::leak(std::boxed::Box::new(
            reader::Context::new(buff.as_str(), path.to_str().unwrap()),
        ));

        let reader = Reader::new(context);

        let mut opcode_table = OpCodeTable::new();

        for expr in reader {
            let sexpr = std::boxed::Box::leak(std::boxed::Box::new(expr?));
            let ast = ast_compiler.compile(sexpr)?;
            let il = self.compile(&ast, vm, ast_compiler, find_module)?;
            bytecode::compile(&il, &mut opcode_table)?;
        }

        vm.eval(&opcode_table)
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        Ok(Il::Constant(Constant::Nil {
            source: source.clone(),
        }))
    }

    fn eval_when_compile(
        &mut self,
        source: &Ast,
        eval_when_compile: &ast::EvalWhenCompile,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let mut opcode_table = OpCodeTable::new();

        for expr in &eval_when_compile.exprs {
            let il = std::boxed::Box::leak(std::boxed::Box::new(self.compile(
                expr,
                vm,
                ast_compiler,
                find_module,
            )?));

            bytecode::compile(il, &mut opcode_table)?;
        }

        vm.eval(&opcode_table)
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        Ok(Il::Constant(Constant::Nil {
            source: source.clone(),
        }))
    }

    fn compile_constant(&mut self, source: &Ast, constant: &ast::Constant) -> Result<Il, Error> {
        Ok(match constant {
            ast::Constant::String { string, .. } => Il::Constant(Constant::String {
                source: source.clone(),
                string: string.clone(),
            }),
            ast::Constant::Char { char, .. } => Il::Constant(Constant::Char {
                source: source.clone(),
                char: *char,
            }),
            ast::Constant::Int { int, .. } => Il::Constant(Constant::Int {
                source: source.clone(),
                int: *int,
            }),
            ast::Constant::Bool { bool, .. } => Il::Constant(Constant::Bool {
                source: source.clone(),
                bool: *bool,
            }),
            ast::Constant::Nil { .. } => Il::Constant(Constant::Nil {
                source: source.clone(),
            }),
        })
    }

    fn compile_variable_reference(
        &mut self,
        source: &Ast,
        variable: &ast::Variable,
    ) -> Result<Il, Error> {
        Ok(match self.environment.resolve(variable.name.as_str()) {
            Some(environment::Variable::Local(index)) => Il::VarRef(VarRef::Local {
                source: source.clone(),
                name: variable.name.clone(),
                index,
            }),
            Some(environment::Variable::Upvalue(index)) => Il::VarRef(VarRef::UpValue {
                source: source.clone(),
                name: variable.name.clone(),
                index,
            }),
            Some(environment::Variable::Global) => Il::VarRef(VarRef::Global {
                source: source.clone(),
                name: variable.name.clone(),
            }),
            None => {
                return Err(Error::Il {
                    ast: source.clone(),
                    message: format!("unknown variable referenced: {}", variable.name.as_str()),
                })
            }
        })
    }

    fn compile_defmacro(
        &mut self,
        source: &Ast,
        defmacro: &ast::DefMacro,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let arity = match &defmacro.parameters {
            ast::Parameters::Normal(_) if defmacro.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(defmacro.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(defmacro.parameters.len() - 1),
        };

        let parameters =
            Parameters::from_ast(source, &defmacro.parameters).map_err(|_| Error::Il {
                ast: source.clone(),
                message: "failed to compile parameters".to_string(),
            })?;

        self.environment
            .push_scope(parameters.iter().map(|param| param.name));

        let body = defmacro
            .body
            .iter()
            .map(|ast| self.compile(ast, vm, ast_compiler, find_module))
            .collect::<Result<Vec<Il>, Error>>()?;

        let lambda = std::boxed::Box::leak(std::boxed::Box::new(Il::Lambda(il::Lambda {
            source: source.clone(),
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

        Ok(Il::Constant(Constant::Nil {
            source: source.clone(),
        }))
    }

    fn eval_macro(
        &mut self,
        source: &Ast,
        macro_call: &ast::MacroCall,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let mut opcode_table = OpCodeTable::new();

        for arg in &macro_call.args {
            let il = std::boxed::Box::leak(std::boxed::Box::new(self.compile_quoted(source, arg)?));
            bytecode::compile(
                std::boxed::Box::leak(std::boxed::Box::new(il)),
                &mut opcode_table,
            )
            .unwrap();
        }

        vm.get_global(macro_call.r#macro.as_str())?;

        vm.eval(&opcode_table)
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        vm.call(macro_call.args.len())?;

        vm.eval(&OpCodeTable::new())
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        let Some(object) = vm.pop().map(|local| local.into_object()) else {
            return Ok(Il::Constant(Constant::Nil {
                source: source.clone(),
            }));
        };

        let mut buff = String::new();

        object.print(&mut buff).map_err(|_| Error::Il {
            ast: source.clone(),
            message: "failed to print macro result".to_string(),
        })?;

        let context: &'static _ = std::boxed::Box::leak(std::boxed::Box::new(
            reader::Context::new(buff.as_str(), "macro-expansion"),
        ));
        let mut reader = Reader::new(context);
        let sexpr: &'static _ =
            std::boxed::Box::leak(std::boxed::Box::new(reader.next().unwrap()?));
        let ast = ast_compiler.compile(sexpr)?;

        self.compile(&ast, vm, ast_compiler, find_module)
    }

    fn compile_lambda(
        &mut self,
        source: &Ast,
        lambda: &ast::Lambda,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let arity = match &lambda.parameters {
            ast::Parameters::Normal(_) if lambda.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(lambda.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(lambda.parameters.len() - 1),
        };

        let parameters =
            Parameters::from_ast(source, &lambda.parameters).map_err(|_| Error::Il {
                ast: source.clone(),
                message: "failed to compile parameters".to_string(),
            })?;

        self.environment
            .push_scope(parameters.iter().map(|param| param.name));

        let body = lambda
            .body
            .iter()
            .map(|ast| self.compile(ast, vm, ast_compiler, find_module))
            .collect::<Result<Vec<Il>, Error>>()?;

        let upvalues = self.environment.upvalues().collect::<Vec<UpValue>>();

        let r#type = match lambda.r#type.as_ref().map(Type::from_ast) {
            Some(t) => Some(t),
            None => None,
        };

        self.environment.pop_scope();

        Ok(Il::Lambda(Lambda {
            source: source.clone(),
            parameters,
            r#type,
            arity,
            upvalues,
            body,
        }))
    }

    fn compile_if(
        &mut self,
        source: &Ast,
        r#if: &ast::If,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::If(If {
            source: source.clone(),
            predicate: std::boxed::Box::new(self.compile(
                &r#if.predicate,
                vm,
                ast_compiler,
                find_module,
            )?),
            then: std::boxed::Box::new(self.compile(&r#if.then, vm, ast_compiler, find_module)?),
            r#else: std::boxed::Box::new(self.compile(
                &r#if.r#else,
                vm,
                ast_compiler,
                find_module,
            )?),
        }))
    }

    fn compile_def(
        &mut self,
        source: &Ast,
        def: &ast::Def,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        self.environment.insert_global(def.parameter.name.as_str());

        let parameter = Parameter::from_ast(source, &def.parameter).map_err(|_| Error::Il {
            ast: source.clone(),
            message: "failed to parse parameter".to_string(),
        })?;

        Ok(Il::Def(Def {
            source: source.clone(),
            parameter,
            body: std::boxed::Box::new(self.compile(&def.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_decl(&mut self, source: &Ast, decl: &ast::Decl) -> Result<Il, Error> {
        self.environment.insert_global(decl.parameter.name.as_str());

        Ok(Il::Constant(Constant::Nil {
            source: source.clone(),
        }))
    }

    fn compile_set(
        &mut self,
        source: &Ast,
        set: &ast::Set,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Set(Set {
            source: source.clone(),
            target: match self.environment.resolve(&set.target.as_str()) {
                Some(Variable::Local(index)) => VarRef::Local {
                    source: source.clone(),
                    name: set.target.clone(),
                    index,
                },
                Some(Variable::Upvalue(index)) => VarRef::UpValue {
                    source: source.clone(),
                    name: set.target.clone(),
                    index,
                },
                Some(Variable::Global) => VarRef::Global {
                    source: source.clone(),
                    name: set.target.clone(),
                },
                None => {
                    return Err(Error::Il {
                        ast: source.clone(),
                        message: "unknown variable".to_string(),
                    })
                }
            },

            body: std::boxed::Box::new(self.compile(&set.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_set_box(
        &mut self,
        source: &Ast,
        setbox: &ast::SetBox,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::SetBox(SetBox {
            source: source.clone(),
            target: std::boxed::Box::new(self.compile(
                &setbox.target,
                vm,
                ast_compiler,
                find_module,
            )?),
            body: std::boxed::Box::new(self.compile(
                &setbox.body,
                vm,
                ast_compiler,
                find_module,
            )?),
        }))
    }

    fn compile_box(
        &mut self,
        source: &Ast,
        r#box: &ast::Box,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Box(Box {
            source: source.clone(),
            body: std::boxed::Box::new(self.compile(&r#box.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_unbox(
        &mut self,
        source: &Ast,
        unbox: &ast::UnBox,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::UnBox(UnBox {
            source: source.clone(),
            body: std::boxed::Box::new(self.compile(&unbox.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_quoted(&mut self, source: &Ast, quoted: &ast::Quoted) -> Result<Il, Error> {
        Ok(match &quoted {
            Quoted::List { list, .. } => self.compile_quoted_list(source, list.as_slice())?,
            Quoted::Symbol { symbol, .. } => Il::Constant(Constant::Symbol {
                source: source.clone(),
                symbol: symbol.clone(),
            }),
            Quoted::String { string, .. } => Il::Constant(Constant::String {
                source: source.clone(),
                string: string.clone(),
            }),
            Quoted::Char { char, .. } => Il::Constant(Constant::Char {
                source: source.clone(),
                char: *char,
            }),
            Quoted::Int { int, .. } => Il::Constant(Constant::Int {
                source: source.clone(),
                int: *int,
            }),
            Quoted::Bool { bool, .. } => Il::Constant(Constant::Bool {
                source: source.clone(),
                bool: *bool,
            }),
            Quoted::Nil { .. } => Il::Constant(Constant::Nil {
                source: source.clone(),
            }),
        })
    }

    #[allow(clippy::only_used_in_recursion)]
    fn compile_quoted_list(&mut self, source: &Ast, list: &[Quoted]) -> Result<Il, Error> {
        Ok(Il::List(List {
            source: source.clone(),
            exprs: list
                .iter()
                .map(|quoted| {
                    Ok(match quoted {
                        Quoted::List { list, .. } => {
                            self.compile_quoted_list(source, list.as_slice())?
                        }
                        Quoted::Symbol { symbol, .. } => Il::Constant(Constant::Symbol {
                            source: source.clone(),
                            symbol: symbol.clone(),
                        }),
                        Quoted::String { string, .. } => Il::Constant(Constant::String {
                            source: source.clone(),
                            string: string.clone(),
                        }),
                        Quoted::Char { char, .. } => Il::Constant(Constant::Char {
                            source: source.clone(),
                            char: *char,
                        }),
                        Quoted::Int { int, .. } => Il::Constant(Constant::Int {
                            source: source.clone(),
                            int: *int,
                        }),
                        Quoted::Bool { bool, .. } => Il::Constant(Constant::Bool {
                            source: source.clone(),
                            bool: *bool,
                        }),
                        Quoted::Nil { .. } => Il::Constant(Constant::Nil {
                            source: source.clone(),
                        }),
                    })
                })
                .collect::<Result<Vec<_>, Error>>()?,
        }))
    }

    fn compile_fncall(
        &mut self,
        source: &Ast,
        fncall: &ast::FnCall,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::FnCall(FnCall {
            source: source.clone(),
            function: std::boxed::Box::new(self.compile(
                &fncall.function,
                vm,
                ast_compiler,
                find_module,
            )?),
            args: fncall
                .exprs
                .iter()
                .map(|arg| self.compile(arg, vm, ast_compiler, find_module))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_apply(
        &mut self,
        source: &Ast,
        apply: &ast::Apply,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Apply(Apply {
            source: source.clone(),
            function: std::boxed::Box::new(self.compile(
                &apply.function,
                vm,
                ast_compiler,
                find_module,
            )?),
            list: std::boxed::Box::new(self.compile(&apply.list, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_arithmetic_operation(
        &mut self,
        source: &Ast,
        op: &ast::BinaryArithmeticOperation,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::ArithmeticOperation(ArithmeticOperation {
            source: source.clone(),
            operator: match op.operator {
                ast::BinaryArithmeticOperator::Add => ArithmeticOperator::Add,
                ast::BinaryArithmeticOperator::Sub => ArithmeticOperator::Sub,
                ast::BinaryArithmeticOperator::Mul => ArithmeticOperator::Mul,
                ast::BinaryArithmeticOperator::Div => ArithmeticOperator::Div,
            },
            lhs: std::boxed::Box::new(self.compile(&op.lhs, vm, ast_compiler, find_module)?),
            rhs: std::boxed::Box::new(self.compile(&op.rhs, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_comparison_operation(
        &mut self,
        source: &Ast,
        op: &ast::ComparisonOperation,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::ComparisonOperation(ComparisonOperation {
            source: source.clone(),
            operator: match op.operator {
                ast::ComparisonOperator::Eq => ComparisonOperator::Eq,
                ast::ComparisonOperator::Lt => ComparisonOperator::Lt,
                ast::ComparisonOperator::Gt => ComparisonOperator::Gt,
            },
            lhs: std::boxed::Box::new(self.compile(&op.lhs, vm, ast_compiler, find_module)?),
            rhs: std::boxed::Box::new(self.compile(&op.rhs, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_list(
        &mut self,
        source: &Ast,
        list: &ast::List,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::List(List {
            source: source.clone(),
            exprs: list
                .exprs
                .iter()
                .map(|expr| self.compile(expr, vm, ast_compiler, find_module))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_cons(
        &mut self,
        source: &Ast,
        cons: &ast::Cons,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Cons(Cons {
            source: source.clone(),
            lhs: std::boxed::Box::new(self.compile(&cons.lhs, vm, ast_compiler, find_module)?),
            rhs: std::boxed::Box::new(self.compile(&cons.rhs, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_car(
        &mut self,
        source: &Ast,
        car: &ast::Car,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Car(Car {
            source: source.clone(),
            body: std::boxed::Box::new(self.compile(&car.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_cdr(
        &mut self,
        source: &Ast,
        cdr: &ast::Cdr,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Cdr(Cdr {
            source: source.clone(),
            body: std::boxed::Box::new(self.compile(&cdr.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_is_type(
        &mut self,
        source: &Ast,
        is_type: &ast::IsType,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::IsType(IsType {
            source: source.clone(),
            r#type: match is_type.parameter {
                ast::IsTypeParameter::Function => IsTypeParameter::Function,
                ast::IsTypeParameter::Cons => IsTypeParameter::Cons,
                ast::IsTypeParameter::Symbol => IsTypeParameter::Symbol,
                ast::IsTypeParameter::String => IsTypeParameter::String,
                ast::IsTypeParameter::Char => IsTypeParameter::Char,
                ast::IsTypeParameter::Int => IsTypeParameter::Int,
                ast::IsTypeParameter::Bool => IsTypeParameter::Bool,
                ast::IsTypeParameter::Nil => IsTypeParameter::Nil,
            },
            body: std::boxed::Box::new(self.compile(
                &is_type.body,
                vm,
                ast_compiler,
                find_module,
            )?),
        }))
    }

    fn compile_assert(
        &mut self,
        source: &Ast,
        assert: &ast::Assert,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Assert(Assert {
            source: source.clone(),
            body: std::boxed::Box::new(self.compile(
                &assert.body,
                vm,
                ast_compiler,
                find_module,
            )?),
        }))
    }

    fn compile_gensym(&mut self, source: &Ast) -> Result<Il, Error> {
        let suffix = rand::random::<u32>();

        let symbol = format!("e{suffix}");

        Ok(Il::Constant(Constant::Symbol {
            source: source.clone(),
            symbol,
        }))
    }

    fn compile_map_create(&mut self, source: &Ast) -> Result<Il, Error> {
        Ok(Il::MapCreate(MapCreate {
            source: source.clone(),
        }))
    }

    fn compile_map_insert(
        &mut self,
        source: &Ast,
        map_insert: &ast::MapInsert,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::MapInsert(MapInsert {
            source: source.clone(),
            map: std::boxed::Box::new(self.compile(
                &map_insert.map,
                vm,
                ast_compiler,
                find_module,
            )?),
            key: std::boxed::Box::new(self.compile(
                &map_insert.key,
                vm,
                ast_compiler,
                find_module,
            )?),
            value: std::boxed::Box::new(self.compile(
                &map_insert.value,
                vm,
                ast_compiler,
                find_module,
            )?),
        }))
    }

    fn compile_map_retrieve(
        &mut self,
        source: &Ast,
        map_retrieve: &ast::MapRetrieve,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::MapRetrieve(MapRetrieve {
            source: source.clone(),
            map: std::boxed::Box::new(self.compile(
                &map_retrieve.map,
                vm,
                ast_compiler,
                find_module,
            )?),
            key: std::boxed::Box::new(self.compile(
                &map_retrieve.key,
                vm,
                ast_compiler,
                find_module,
            )?),
        }))
    }

    fn compile_map_items(
        &mut self,
        source: &Ast,
        map_items: &ast::MapItems,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(
            &Path,
        )
            -> Option<Result<PathBuf, std::boxed::Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::MapItems(MapItems {
            source: source.clone(),
            map: std::boxed::Box::new(self.compile(
                &map_items.map,
                vm,
                ast_compiler,
                find_module,
            )?),
        }))
    }
}

impl<'parameters> IntoIterator for &'parameters Parameters {
    type Item = Parameter;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Parameters::Nary(params) | Parameters::Variadic(params) => params.iter().cloned(),
        }
    }
}
