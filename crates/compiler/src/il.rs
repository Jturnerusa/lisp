use std::{
    borrow::Borrow,
    env,
    fs::{self, File},
    io::{self, Read},
    path::{Path, PathBuf},
};

use crate::{
    ast::{self, Ast, Quoted},
    bytecode,
    environment::{self, Environment, ModuleVar, Variable},
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
    Module(Module),
    Lambda(Lambda),
    If(If),
    Apply(Apply),
    Def(Def),
    Set(Set),
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
    Module {
        source: Ast,
        name: String,
        module: String,
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
    pub predicate: Box<Il>,
    pub then: Box<Il>,
    pub r#else: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct FnCall {
    pub source: Ast,
    pub function: Box<Il>,
    pub args: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct Apply {
    pub source: Ast,
    pub function: Box<Il>,
    pub list: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct List {
    pub source: Ast,
    pub exprs: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct Cons {
    pub source: Ast,
    pub lhs: Box<Il>,
    pub rhs: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Car {
    pub source: Ast,
    pub body: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Cdr {
    pub source: Ast,
    pub body: Box<Il>,
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
    pub lhs: Box<Il>,
    pub rhs: Box<Il>,
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
    pub lhs: Box<Il>,
    pub rhs: Box<Il>,
}

#[derive(Clone, Debug)]
pub enum Def {
    Global {
        source: Ast,
        parameter: Parameter,
        body: Box<Il>,
    },
    Module {
        source: Ast,
        parameter: Parameter,
        module: String,
        body: Box<Il>,
    },
}

#[derive(Clone, Debug)]
pub struct Set {
    pub source: Ast,
    pub target: VarRef,
    pub body: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapCreate {
    pub source: Ast,
}

#[derive(Clone, Debug)]
pub struct MapInsert {
    pub source: Ast,
    pub map: Box<Il>,
    pub key: Box<Il>,
    pub value: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve {
    pub source: Ast,
    pub map: Box<Il>,
    pub key: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapItems {
    pub source: Ast,
    pub map: Box<Il>,
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
    pub body: Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Assert {
    pub source: Ast,
    pub body: Box<Il>,
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
            | Self::Global { source, .. }
            | Self::Module { source, .. } => source,
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
            Self::Module(Module { source, .. })
            | Self::Lambda(Lambda { source, .. })
            | Self::ArithmeticOperation(ArithmeticOperation { source, .. })
            | Self::ComparisonOperation(ComparisonOperation { source, .. })
            | Self::Def(Def::Global { source, .. })
            | Self::Def(Def::Module { source, .. })
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
            | Self::MapItems(MapItems { source, .. })
            | Self::IsType(IsType { source, .. })
            | Self::Assert(Assert { source, .. })
            | Self::VarRef(VarRef::Local { source, .. })
            | Self::VarRef(VarRef::UpValue { source, .. })
            | Self::VarRef(VarRef::Global { source, .. })
            | Self::VarRef(VarRef::Module { source, .. })
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

impl Def {
    pub(crate) fn source(&self) -> &Ast {
        match self {
            Self::Global { source, .. } | Self::Module { source, .. } => source,
        }
    }

    pub(crate) fn body(&self) -> &Il {
        match self {
            Self::Global { body, .. } | Self::Module { body, .. } => &*body,
        }
    }
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
        }
    }

    pub fn set_current_module(&mut self, module: Option<String>) {
        self.environment.set_current_module(module);
    }

    pub fn current_module(&self) -> Option<String> {
        self.environment.current_module()
    }

    pub fn compile(
        &mut self,
        ast: &Ast,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        match ast {
            Ast::Module(module) => self.compile_module(ast, module),
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
            Ast::Export(export) => self.compile_export(ast, export),
            Ast::Constant(constant) => self.compile_constant(ast, constant),
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
        }
    }

    fn compile_module(&mut self, source: &Ast, module: &ast::Module) -> Result<Il, Error> {
        self.environment.create_module(module.name.as_str());
        self.set_current_module(Some(module.name.clone()));

        Ok(Il::Module(Module {
            source: source.clone(),
            name: module.name.clone(),
        }))
    }

    fn compile_require(
        &mut self,
        source: &Ast,
        require: &ast::Require,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let current_module = self.environment.current_module();
        self.set_current_module(None);

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

        let context: &'static _ = Box::leak(Box::new(reader::Context::new(
            buff.as_str(),
            path.to_str().unwrap(),
        )));

        let reader = Reader::new(context);

        let mut opcode_table = OpCodeTable::new();

        for expr in reader {
            let sexpr = Box::leak(Box::new(expr?));
            let ast = ast_compiler.compile(sexpr)?;
            let il = self.compile(&ast, vm, ast_compiler, find_module)?;
            bytecode::compile(&il, &mut opcode_table)?;
        }

        vm.eval(&opcode_table)
            .map_err(|(error, sexpr)| Error::VmWithDebug { error, sexpr })?;

        self.set_current_module(current_module);

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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let mut opcode_table = OpCodeTable::new();

        for expr in &eval_when_compile.exprs {
            let il = Box::leak(Box::new(self.compile(
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
        Ok(match variable {
            ast::Variable::WithoutModule { name, .. } => {
                match self.environment.resolve(name.as_str()) {
                    Some(environment::Variable::Local(index)) => Il::VarRef(VarRef::Local {
                        source: source.clone(),
                        name: name.clone(),
                        index,
                    }),
                    Some(environment::Variable::Upvalue(index)) => Il::VarRef(VarRef::UpValue {
                        source: source.clone(),
                        name: name.clone(),
                        index,
                    }),
                    Some(environment::Variable::Global) => Il::VarRef(VarRef::Global {
                        source: source.clone(),
                        name: name.clone(),
                    }),
                    Some(environment::Variable::Module) => Il::VarRef(VarRef::Module {
                        source: source.clone(),
                        name: name.clone(),
                        module: self
                            .environment
                            .current_module()
                            .map(|s| s.to_string())
                            .unwrap(),
                    }),
                    None => {
                        return Err(Error::Il {
                            ast: source.clone(),
                            message: format!("unknown variable referenced: {}", name),
                        })
                    }
                }
            }
            ast::Variable::WithModule { name, module, .. } => {
                match self
                    .environment
                    .resolve_module_var(module.as_str(), name.as_str())
                {
                    Some(ModuleVar { visible, .. }) if visible => Il::VarRef(VarRef::Module {
                        source: source.clone(),
                        name: name.clone(),
                        module: module.to_string(),
                    }),
                    Some(ModuleVar { .. }) => {
                        return Err(Error::Il {
                            ast: source.clone(),
                            message: "private module variable referenced".to_string(),
                        })
                    }
                    None => {
                        return Err(Error::Il {
                            ast: source.clone(),
                            message: "unknown module variable referenced".to_string(),
                        })
                    }
                }
            }
        })
    }

    fn compile_defmacro(
        &mut self,
        source: &Ast,
        defmacro: &ast::DefMacro,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let current_module = self.environment.current_module();
        self.set_current_module(None);

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

        let lambda = Box::leak(Box::new(Il::Lambda(il::Lambda {
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

        self.set_current_module(current_module);

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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let current_module = self.environment.current_module();
        self.set_current_module(None);

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
            return Ok(Il::Constant(Constant::Nil {
                source: source.clone(),
            }));
        };

        let mut buff = String::new();

        object.print(&mut buff).map_err(|_| Error::Il {
            ast: source.clone(),
            message: "failed to print macro result".to_string(),
        })?;

        let context: &'static _ = Box::leak(Box::new(reader::Context::new(
            buff.as_str(),
            "macro-expansion",
        )));
        let mut reader = Reader::new(context);
        let sexpr: &'static _ = Box::leak(Box::new(reader.next().unwrap()?));
        let ast = ast_compiler.compile(sexpr)?;

        self.set_current_module(current_module);

        self.compile(&ast, vm, ast_compiler, find_module)
    }

    fn compile_lambda(
        &mut self,
        source: &Ast,
        lambda: &ast::Lambda,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::If(If {
            source: source.clone(),
            predicate: Box::new(self.compile(&r#if.predicate, vm, ast_compiler, find_module)?),
            then: Box::new(self.compile(&r#if.then, vm, ast_compiler, find_module)?),
            r#else: Box::new(self.compile(&r#if.r#else, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_def(
        &mut self,
        source: &Ast,
        def: &ast::Def,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        let parameter = Parameter::from_ast(source, &def.parameter).map_err(|_| Error::Il {
            ast: source.clone(),
            message: "failed to parse parameter".to_string(),
        })?;

        let r#type = match def.parameter.r#type.as_ref().map(Type::from_ast) {
            Some(t) => Some(t),
            None => None,
        };

        Ok(
            if let Some(module) = self.environment.current_module().map(|s| s.to_string()) {
                self.environment
                    .insert_module_var(module.as_str(), def.parameter.name.as_str());

                Il::Def(Def::Module {
                    source: source.clone(),
                    parameter,
                    module: self
                        .environment
                        .current_module()
                        .map(|s| s.to_string())
                        .unwrap(),
                    body: Box::new(self.compile(&def.body, vm, ast_compiler, find_module)?),
                })
            } else {
                self.environment.insert_global(def.parameter.name.as_str());

                Il::Def(Def::Global {
                    source: source.clone(),
                    parameter,
                    body: Box::new(self.compile(&def.body, vm, ast_compiler, find_module)?),
                })
            },
        )
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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Set(Set {
            source: source.clone(),
            target: match &set.variable {
                ast::Variable::WithoutModule { name, .. } => {
                    match self.environment.resolve(name.as_str()) {
                        Some(Variable::Local(index)) => VarRef::Local {
                            source: source.clone(),
                            name: name.clone(),
                            index,
                        },
                        Some(Variable::Upvalue(index)) => VarRef::UpValue {
                            source: source.clone(),
                            name: name.clone(),
                            index,
                        },
                        Some(Variable::Global) => VarRef::Global {
                            source: source.clone(),
                            name: name.clone(),
                        },
                        Some(Variable::Module) => VarRef::Module {
                            source: source.clone(),
                            name: name.clone(),
                            module: self.environment.current_module().unwrap().to_string(),
                        },
                        None => {
                            return Err(Error::Il {
                                ast: source.clone(),
                                message: "unknown variable".to_string(),
                            })
                        }
                    }
                }
                ast::Variable::WithModule { name, module, .. } => {
                    match self.environment.resolve_module_var(module, name.as_str()) {
                        Some(ModuleVar { visible, .. }) if visible => VarRef::Module {
                            source: source.clone(),
                            name: name.clone(),
                            module: module.to_string(),
                        },
                        Some(_) => {
                            return Err(Error::Il {
                                ast: source.clone(),
                                message: "referenced private symbol".to_string(),
                            })
                        }
                        None => {
                            return Err(Error::Il {
                                ast: source.clone(),
                                message: "referenced unknown variable".to_string(),
                            })
                        }
                    }
                }
            },
            body: Box::new(self.compile(&set.body, vm, ast_compiler, find_module)?),
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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::FnCall(FnCall {
            source: source.clone(),
            function: Box::new(self.compile(&fncall.function, vm, ast_compiler, find_module)?),
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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Apply(Apply {
            source: source.clone(),
            function: Box::new(self.compile(&apply.function, vm, ast_compiler, find_module)?),
            list: Box::new(self.compile(&apply.list, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_arithmetic_operation(
        &mut self,
        source: &Ast,
        op: &ast::BinaryArithmeticOperation,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::ArithmeticOperation(ArithmeticOperation {
            source: source.clone(),
            operator: match op.operator {
                ast::BinaryArithmeticOperator::Add => ArithmeticOperator::Add,
                ast::BinaryArithmeticOperator::Sub => ArithmeticOperator::Sub,
                ast::BinaryArithmeticOperator::Mul => ArithmeticOperator::Mul,
                ast::BinaryArithmeticOperator::Div => ArithmeticOperator::Div,
            },
            lhs: Box::new(self.compile(&op.lhs, vm, ast_compiler, find_module)?),
            rhs: Box::new(self.compile(&op.rhs, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_comparison_operation(
        &mut self,
        source: &Ast,
        op: &ast::ComparisonOperation,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::ComparisonOperation(ComparisonOperation {
            source: source.clone(),
            operator: match op.operator {
                ast::ComparisonOperator::Eq => ComparisonOperator::Eq,
                ast::ComparisonOperator::Lt => ComparisonOperator::Lt,
                ast::ComparisonOperator::Gt => ComparisonOperator::Gt,
            },
            lhs: Box::new(self.compile(&op.lhs, vm, ast_compiler, find_module)?),
            rhs: Box::new(self.compile(&op.rhs, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_list(
        &mut self,
        source: &Ast,
        list: &ast::List,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Cons(Cons {
            source: source.clone(),
            lhs: Box::new(self.compile(&cons.lhs, vm, ast_compiler, find_module)?),
            rhs: Box::new(self.compile(&cons.rhs, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_car(
        &mut self,
        source: &Ast,
        car: &ast::Car,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Car(Car {
            source: source.clone(),
            body: Box::new(self.compile(&car.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_cdr(
        &mut self,
        source: &Ast,
        cdr: &ast::Cdr,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Cdr(Cdr {
            source: source.clone(),
            body: Box::new(self.compile(&cdr.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_is_type(
        &mut self,
        source: &Ast,
        is_type: &ast::IsType,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
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
            body: Box::new(self.compile(&is_type.body, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_assert(
        &mut self,
        source: &Ast,
        assert: &ast::Assert,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::Assert(Assert {
            source: source.clone(),
            body: Box::new(self.compile(&assert.body, vm, ast_compiler, find_module)?),
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
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::MapInsert(MapInsert {
            source: source.clone(),
            map: Box::new(self.compile(&map_insert.map, vm, ast_compiler, find_module)?),
            key: Box::new(self.compile(&map_insert.key, vm, ast_compiler, find_module)?),
            value: Box::new(self.compile(&map_insert.value, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_map_retrieve(
        &mut self,
        source: &Ast,
        map_retrieve: &ast::MapRetrieve,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::MapRetrieve(MapRetrieve {
            source: source.clone(),
            map: Box::new(self.compile(&map_retrieve.map, vm, ast_compiler, find_module)?),
            key: Box::new(self.compile(&map_retrieve.key, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_map_items(
        &mut self,
        source: &Ast,
        map_items: &ast::MapItems,
        vm: &mut Vm<&'static Sexpr<'static>>,
        ast_compiler: &mut ast::Compiler,
        find_module: &dyn Fn(&Path) -> Option<Result<PathBuf, Box<dyn std::error::Error>>>,
    ) -> Result<Il, Error> {
        Ok(Il::MapItems(MapItems {
            source: source.clone(),
            map: Box::new(self.compile(&map_items.map, vm, ast_compiler, find_module)?),
        }))
    }

    fn compile_export(&mut self, source: &Ast, export: &ast::Export) -> Result<Il, Error> {
        let current_module = self
            .environment
            .current_module()
            .ok_or(Error::Il {
                ast: source.clone(),
                message: "can't export symbol at global scope".to_string(),
            })?
            .to_string();

        self.environment
            .export_module_var(current_module.as_str(), export.symbol.as_str());

        Ok(Il::Constant(Constant::Nil {
            source: source.clone(),
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
