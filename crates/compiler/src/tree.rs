use std::{collections::HashMap, iter};

use crate::{
    ast::{self, Ast, Decl, DefType, Quoted, Type},
    bytecode,
    environment::{self, Environment, Variable},
};

use error::FileSpan;
use reader::Reader;
use unwrap_enum::{EnumAs, EnumIs};
use vm::{Arity, OpCodeTable, UpValue, Vm};

macro_rules! expect_expression {
    ($e:expr, $span:expr) => {
        match $e {
            Ok(Some(x)) => x,
            Err(e) => return Err(e),
            Ok(None) => {
                return Err(std::boxed::Box::new(Error {
                    span: $span,
                    message: "unexpected expression".to_string(),
                }))
            }
        }
    };
}

#[derive(Debug)]
pub struct Error {
    span: FileSpan,
    message: String,
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
    DefType(DefType),
    MakeType(MakeType),
    IfLet(IfLet),
    LetRec(LetRec),
    Decl(ast::Decl),
}

#[derive(Clone, Debug)]
pub struct Module {
    pub span: FileSpan,
    pub name: String,
}

#[derive(Clone, Debug)]
pub enum Constant {
    Symbol { span: FileSpan, symbol: String },
    String { span: FileSpan, string: String },
    Char { span: FileSpan, char: char },
    Int { span: FileSpan, int: i64 },
    Bool { span: FileSpan, bool: bool },
    Nil { span: FileSpan },
}

#[derive(Clone, Debug)]
pub enum VarRef {
    Local {
        span: FileSpan,
        name: String,
        index: usize,
    },
    UpValue {
        span: FileSpan,
        name: String,
        index: usize,
    },
    Global {
        span: FileSpan,
        name: String,
    },
}

#[derive(Clone, Debug)]
pub struct DefParameter {
    pub span: FileSpan,
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters {
    Nary(Vec<String>),
    Variadic(Vec<String>),
}

#[derive(Clone, Debug)]
pub struct Lambda {
    pub span: FileSpan,
    pub parameters: Parameters,
    pub r#type: Option<Type>,
    pub arity: Arity,
    pub upvalues: Vec<UpValue>,
    pub body: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct If {
    pub span: FileSpan,
    pub predicate: std::boxed::Box<Il>,
    pub then: std::boxed::Box<Il>,
    pub r#else: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct FnCall {
    pub span: FileSpan,
    pub function: std::boxed::Box<Il>,
    pub args: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct Apply {
    pub span: FileSpan,
    pub function: std::boxed::Box<Il>,
    pub list: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct List {
    pub span: FileSpan,
    pub exprs: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct Cons {
    pub span: FileSpan,
    pub lhs: std::boxed::Box<Il>,
    pub rhs: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Car {
    pub span: FileSpan,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Cdr {
    pub span: FileSpan,
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
    pub span: FileSpan,
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
    pub span: FileSpan,
    pub operator: ComparisonOperator,
    pub lhs: std::boxed::Box<Il>,
    pub rhs: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Def {
    pub span: FileSpan,
    pub parameter: DefParameter,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Set {
    pub span: FileSpan,
    pub target: VarRef,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct SetBox {
    pub span: FileSpan,
    pub target: std::boxed::Box<Il>,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Box {
    pub span: FileSpan,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct UnBox {
    pub span: FileSpan,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapCreate {
    pub span: FileSpan,
}

#[derive(Clone, Debug)]
pub struct MapInsert {
    pub span: FileSpan,
    pub map: std::boxed::Box<Il>,
    pub key: std::boxed::Box<Il>,
    pub value: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve {
    pub span: FileSpan,
    pub map: std::boxed::Box<Il>,
    pub key: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MapItems {
    pub span: FileSpan,
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
    pub span: FileSpan,
    pub r#type: IsTypeParameter,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct Assert {
    pub span: FileSpan,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MakeType {
    pub span: FileSpan,
    pub pattern: String,
    pub body: Option<std::boxed::Box<Il>>,
}

#[derive(Clone, Debug)]
pub struct IfLet {
    pub span: FileSpan,
    pub body: std::boxed::Box<Il>,
    pub pattern: String,
    pub binding: Option<String>,
    pub then: std::boxed::Box<Il>,
    pub r#else: std::boxed::Box<Il>,
    pub upvalues: Vec<UpValue>,
}

#[derive(Clone, Debug)]
pub struct LetRec {
    pub span: FileSpan,
    pub bindings: Vec<(String, Il)>,
    pub upvalues: Vec<UpValue>,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub enum DefTypePattern {
    Struct(Type),
    Empty,
}

pub struct Compiler {
    environment: Environment,
    deftype_patterns: HashMap<String, DefTypePattern>,
}

impl VarRef {
    pub fn span(&self) -> FileSpan {
        match self {
            Self::Local { span, .. } | Self::UpValue { span, .. } | Self::Global { span, .. } => {
                *span
            }
        }
    }
}

impl Constant {
    pub fn span(&self) -> FileSpan {
        match self {
            Self::Symbol { span, .. }
            | Self::String { span, .. }
            | Self::Char { span, .. }
            | Self::Int { span, .. }
            | Self::Bool { span, .. }
            | Self::Nil { span } => *span,
        }
    }
}

impl Il {
    pub fn span(&self) -> FileSpan {
        match self {
            Self::Lambda(Lambda { span, .. })
            | Self::ArithmeticOperation(ArithmeticOperation { span, .. })
            | Self::ComparisonOperation(ComparisonOperation { span, .. })
            | Self::Def(Def { span, .. })
            | Self::Set(Set { span, .. })
            | Self::SetBox(SetBox { span, .. })
            | Self::Box(Box { span, .. })
            | Self::UnBox(UnBox { span, .. })
            | Self::If(If { span, .. })
            | Self::FnCall(FnCall { span, .. })
            | Self::Apply(Apply { span, .. })
            | Self::List(List { span, .. })
            | Self::Cons(Cons { span, .. })
            | Self::Car(Car { span, .. })
            | Self::Cdr(Cdr { span, .. })
            | Self::MapCreate(MapCreate { span, .. })
            | Self::MapInsert(MapInsert { span, .. })
            | Self::MapRetrieve(MapRetrieve { span, .. })
            | Self::MapItems(MapItems { span, .. })
            | Self::IsType(IsType { span, .. })
            | Self::Assert(Assert { span, .. })
            | Self::DefType(DefType { span, .. })
            | Self::MakeType(MakeType { span, .. })
            | Self::IfLet(IfLet { span, .. })
            | Self::LetRec(LetRec { span, .. })
            | Self::Decl(Decl { span, .. })
            | Self::VarRef(VarRef::Local { span, .. })
            | Self::VarRef(VarRef::UpValue { span, .. })
            | Self::VarRef(VarRef::Global { span, .. })
            | Self::Constant(Constant::Symbol { span, .. })
            | Self::Constant(Constant::String { span, .. })
            | Self::Constant(Constant::Char { span, .. })
            | Self::Constant(Constant::Int { span, .. })
            | Self::Constant(Constant::Bool { span, .. })
            | Self::Constant(Constant::Nil { span, .. }) => *span,
        }
    }
}

impl DefParameter {
    #[allow(clippy::result_unit_err)]
    pub fn from_ast(ast: &Ast, parameter: &ast::DefParameter) -> Result<Self, ()> {
        Ok(Self {
            span: ast.span(),
            name: parameter.name.clone(),
            r#type: parameter.r#type.clone(),
        })
    }
}

impl Parameters {
    #[allow(clippy::result_unit_err)]
    pub fn from_ast(parameters: &ast::Parameters) -> Result<Self, ()> {
        Ok(match parameters {
            ast::Parameters::Normal(parameters) => Parameters::Nary(parameters.clone()),
            ast::Parameters::Rest(parameters, rest) => Parameters::Variadic(
                parameters
                    .iter()
                    .chain(std::iter::once(rest))
                    .cloned()
                    .collect(),
            ),
        })
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Nary(parameters) | Self::Variadic(parameters) => parameters.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> impl Iterator<Item = String> + '_ {
        self.into_iter()
    }
}

#[allow(clippy::new_without_default)]
impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
            deftype_patterns: HashMap::new(),
        }
    }

    pub fn compile(
        &mut self,
        ast: &Ast,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        match ast {
            Ast::DefMacro(defmacro) => self.compile_defmacro(ast, defmacro, vm, ast_compiler),
            Ast::Lambda(lambda) => self.compile_lambda(ast, lambda, vm, ast_compiler),
            Ast::Def(def) => self.compile_def(ast, def, vm, ast_compiler),
            Ast::Decl(decl) => self.compile_decl(ast, decl),
            Ast::Set(set) => self.compile_set(ast, set, vm, ast_compiler),
            Ast::SetBox(setbox) => self.compile_set_box(ast, setbox, vm, ast_compiler),
            Ast::Box(r#box) => self.compile_box(ast, r#box, vm, ast_compiler),
            Ast::UnBox(unbox) => self.compile_unbox(ast, unbox, vm, ast_compiler),
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
            Ast::MapCreate(_) => self.compile_map_create(ast),
            Ast::MapInsert(map_insert) => {
                self.compile_map_insert(ast, map_insert, vm, ast_compiler)
            }
            Ast::MapRetrieve(map_retrieve) => {
                self.compile_map_retrieve(ast, map_retrieve, vm, ast_compiler)
            }
            Ast::MapItems(map_items) => self.compile_map_items(ast, map_items, vm, ast_compiler),
            Ast::Assert(assert) => self.compile_assert(ast, assert, vm, ast_compiler),
            Ast::GenSym(_) => self.compile_gensym(ast),
            Ast::Constant(constant) => self.compile_constant(ast, constant),
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
            Ast::DefType(deftype) => self.compile_deftype(deftype),
            Ast::MakeType(make_type) => self.compile_make_type(ast, make_type, vm, ast_compiler),
            Ast::IfLet(if_let) => self.compile_if_let(ast, if_let, vm, ast_compiler),
            Ast::LetRec(letrec) => self.compile_letrec(ast, letrec, vm, ast_compiler),
            _ => unreachable!("{ast:?}"),
        }
    }

    fn compile_constant(
        &mut self,
        ast: &Ast,
        constant: &ast::Constant,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(match constant {
            ast::Constant::String { string, .. } => Il::Constant(Constant::String {
                span: ast.span(),
                string: string.clone(),
            }),
            ast::Constant::Char { char, .. } => Il::Constant(Constant::Char {
                span: ast.span(),
                char: *char,
            }),
            ast::Constant::Int { int, .. } => Il::Constant(Constant::Int {
                span: ast.span(),
                int: *int,
            }),
            ast::Constant::Bool { bool, .. } => Il::Constant(Constant::Bool {
                span: ast.span(),
                bool: *bool,
            }),
            ast::Constant::Nil { .. } => Il::Constant(Constant::Nil { span: ast.span() }),
        }))
    }

    fn compile_variable_reference(
        &mut self,
        ast: &Ast,
        variable: &ast::Variable,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(
            match self.environment.resolve(variable.name.as_str()) {
                Some(environment::Variable::Local(index)) => Il::VarRef(VarRef::Local {
                    span: ast.span(),
                    name: variable.name.clone(),
                    index,
                }),
                Some(environment::Variable::Upvalue(index)) => Il::VarRef(VarRef::UpValue {
                    span: ast.span(),
                    name: variable.name.clone(),
                    index,
                }),
                Some(environment::Variable::Global) => Il::VarRef(VarRef::Global {
                    span: ast.span(),
                    name: variable.name.clone(),
                }),
                None => {
                    return Err(std::boxed::Box::new(Error {
                        span: ast.span(),
                        message: format!("unknown variable referenced: {}", variable.name.as_str()),
                    }))
                }
            },
        ))
    }

    fn compile_defmacro(
        &mut self,
        ast: &Ast,
        defmacro: &ast::DefMacro,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        let arity = match &defmacro.parameters {
            ast::Parameters::Normal(_) if defmacro.parameters.is_empty() => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(defmacro.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(defmacro.parameters.len() - 1),
        };

        let parameters = Parameters::from_ast(&defmacro.parameters).map_err(|_| Error {
            span: ast.span(),
            message: "failed to compile parameters".to_string(),
        })?;

        self.environment.push_scope(parameters.iter());

        let body = defmacro
            .body
            .iter()
            .filter_map(|ast| match self.compile(ast, vm, ast_compiler) {
                Ok(Some(tree)) => Some(Ok(tree)),
                Ok(None) => None,
                Err(e) => Some(Err(e)),
            })
            .collect::<Result<Vec<Il>, _>>()?;

        let lambda = Il::Lambda(self::Lambda {
            span: ast.span(),
            parameters,
            r#type: None,
            upvalues: Vec::new(),
            arity,
            body,
        });

        let mut opcodes = OpCodeTable::new();

        bytecode::compile(&lambda, &mut opcodes).map_err(std::boxed::Box::new)?;

        vm.eval(&opcodes)?;

        vm.def_global(defmacro.name.as_str())
            .map_err(std::boxed::Box::new)?;

        Ok(None)
    }

    fn eval_macro(
        &mut self,
        ast: &Ast,
        macro_call: &ast::MacroCall,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        let mut opcode_table = OpCodeTable::new();

        for arg in &macro_call.args {
            let il = self.compile_quoted(ast, arg)?.unwrap();

            bytecode::compile(&il, &mut opcode_table).unwrap();
        }

        vm.get_global(macro_call.r#macro.as_str())?;

        vm.eval(&opcode_table)?;

        vm.call(macro_call.args.len())?;

        vm.eval(&OpCodeTable::new())?;

        let Some(object) = vm.pop().map(|local| local.into_object()) else {
            return Ok(Some(Il::Constant(Constant::Nil { span: ast.span() })));
        };

        let mut buff = String::new();

        object.print(&mut buff).map_err(|_| Error {
            span: ast.span(),
            message: "failed to print macro result".to_string(),
        })?;

        let mut reader = Reader::new(buff.as_str(), ast.span().id);

        let sexpr = reader.next().unwrap()?;

        let ast = ast_compiler.compile(&sexpr)?;

        self.compile(&ast, vm, ast_compiler)
    }

    fn compile_lambda(
        &mut self,
        ast: &Ast,
        lambda: &ast::Lambda,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        let arity = match &lambda.parameters {
            ast::Parameters::Normal(_) if lambda.parameters.is_empty() => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(lambda.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(lambda.parameters.len() - 1),
        };

        let parameters = Parameters::from_ast(&lambda.parameters).map_err(|_| Error {
            span: ast.span(),
            message: "failed to compile parameters".to_string(),
        })?;

        self.environment.push_scope(parameters.iter());

        let body = lambda
            .body
            .iter()
            .filter_map(|ast| match self.compile(ast, vm, ast_compiler) {
                Ok(Some(tree)) => Some(Ok(tree)),
                Ok(None) => None,
                Err(e) => Some(Err(e)),
            })
            .collect::<Result<Vec<Il>, _>>()?;

        let upvalues = self.environment.upvalues().collect::<Vec<UpValue>>();

        let r#type = lambda.r#type.clone();

        self.environment.pop_scope();

        Ok(Some(Il::Lambda(Lambda {
            span: ast.span(),
            parameters,
            r#type,
            arity,
            upvalues,
            body,
        })))
    }

    fn compile_if(
        &mut self,
        ast: &Ast,
        r#if: &ast::If,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::If(If {
            span: ast.span(),
            predicate: std::boxed::Box::new(expect_expression!(
                self.compile(&r#if.predicate, vm, ast_compiler),
                ast.span()
            )),
            then: std::boxed::Box::new(expect_expression!(
                self.compile(&r#if.then, vm, ast_compiler),
                ast.span()
            )),
            r#else: std::boxed::Box::new(expect_expression!(
                self.compile(&r#if.r#else, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_def(
        &mut self,
        ast: &Ast,
        def: &ast::Def,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        self.environment.insert_global(def.parameter.name.as_str());

        let parameter = DefParameter::from_ast(ast, &def.parameter).map_err(|_| Error {
            span: ast.span(),
            message: "failed to parse parameter".to_string(),
        })?;

        Ok(Some(Il::Def(Def {
            span: ast.span(),
            parameter,
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&def.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_decl(
        &mut self,
        ast: &Ast,
        decl: &ast::Decl,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        self.environment.insert_global(decl.parameter.name.as_str());

        Ok(Some(Il::Constant(Constant::Nil { span: ast.span() })))
    }

    fn compile_set(
        &mut self,
        ast: &Ast,
        set: &ast::Set,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::Set(Set {
            span: ast.span(),
            target: match self.environment.resolve(set.target.as_str()) {
                Some(Variable::Local(index)) => VarRef::Local {
                    span: ast.span(),
                    name: set.target.clone(),
                    index,
                },
                Some(Variable::Upvalue(index)) => VarRef::UpValue {
                    span: ast.span(),
                    name: set.target.clone(),
                    index,
                },
                Some(Variable::Global) => VarRef::Global {
                    span: ast.span(),
                    name: set.target.clone(),
                },
                None => {
                    return Err(std::boxed::Box::new(Error {
                        span: ast.span(),
                        message: "unknown variable".to_string(),
                    }))
                }
            },

            body: std::boxed::Box::new(expect_expression!(
                self.compile(&set.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_set_box(
        &mut self,
        ast: &Ast,
        setbox: &ast::SetBox,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::SetBox(SetBox {
            span: ast.span(),
            target: std::boxed::Box::new(expect_expression!(
                self.compile(&setbox.target, vm, ast_compiler),
                ast.span()
            )),
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&setbox.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_box(
        &mut self,
        ast: &Ast,
        r#box: &ast::Box,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::Box(Box {
            span: ast.span(),
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&r#box.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_unbox(
        &mut self,
        ast: &Ast,
        unbox: &ast::UnBox,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::UnBox(UnBox {
            span: ast.span(),
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&unbox.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_quoted(
        &mut self,
        ast: &Ast,
        quoted: &ast::Quoted,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(match &quoted {
            Quoted::List { list, .. } => self.compile_quoted_list(ast, list.as_slice())?,
            Quoted::Symbol { symbol, .. } => Il::Constant(Constant::Symbol {
                span: ast.span(),
                symbol: symbol.clone(),
            }),
            Quoted::String { string, .. } => Il::Constant(Constant::String {
                span: ast.span(),
                string: string.clone(),
            }),
            Quoted::Char { char, .. } => Il::Constant(Constant::Char {
                span: ast.span(),
                char: *char,
            }),
            Quoted::Int { int, .. } => Il::Constant(Constant::Int {
                span: ast.span(),
                int: *int,
            }),
            Quoted::Bool { bool, .. } => Il::Constant(Constant::Bool {
                span: ast.span(),
                bool: *bool,
            }),
            Quoted::Nil { .. } => Il::Constant(Constant::Nil { span: ast.span() }),
        }))
    }

    #[allow(clippy::only_used_in_recursion)]
    fn compile_quoted_list(
        &mut self,
        ast: &Ast,
        list: &[Quoted],
    ) -> Result<Il, std::boxed::Box<dyn error::Error>> {
        Ok(Il::List(List {
            span: ast.span(),
            exprs: list
                .iter()
                .map(|quoted| {
                    Ok(match quoted {
                        Quoted::List { list, .. } => {
                            self.compile_quoted_list(ast, list.as_slice())?
                        }
                        Quoted::Symbol { symbol, .. } => Il::Constant(Constant::Symbol {
                            span: ast.span(),
                            symbol: symbol.clone(),
                        }),
                        Quoted::String { string, .. } => Il::Constant(Constant::String {
                            span: ast.span(),
                            string: string.clone(),
                        }),
                        Quoted::Char { char, .. } => Il::Constant(Constant::Char {
                            span: ast.span(),
                            char: *char,
                        }),
                        Quoted::Int { int, .. } => Il::Constant(Constant::Int {
                            span: ast.span(),
                            int: *int,
                        }),
                        Quoted::Bool { bool, .. } => Il::Constant(Constant::Bool {
                            span: ast.span(),
                            bool: *bool,
                        }),
                        Quoted::Nil { .. } => Il::Constant(Constant::Nil { span: ast.span() }),
                    })
                })
                .collect::<Result<Vec<_>, std::boxed::Box<dyn error::Error>>>()?,
        }))
    }

    fn compile_fncall(
        &mut self,
        ast: &Ast,
        fncall: &ast::FnCall,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::FnCall(FnCall {
            span: ast.span(),
            function: std::boxed::Box::new(expect_expression!(
                self.compile(&fncall.function, vm, ast_compiler),
                ast.span()
            )),
            args: fncall
                .exprs
                .iter()
                .map(|arg| match self.compile(arg, vm, ast_compiler) {
                    Ok(Some(tree)) => Ok(tree),
                    Ok(None) => Err(std::boxed::Box::new(Error {
                        span: ast.span(),
                        message: "unexpected expression".to_string(),
                    }) as _),
                    Err(e) => Err(e),
                })
                .collect::<Result<Vec<Il>, _>>()?,
        })))
    }

    fn compile_apply(
        &mut self,
        ast: &Ast,
        apply: &ast::Apply,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::Apply(Apply {
            span: ast.span(),
            function: std::boxed::Box::new(expect_expression!(
                self.compile(&apply.function, vm, ast_compiler),
                ast.span()
            )),
            list: std::boxed::Box::new(expect_expression!(
                self.compile(&apply.list, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_arithmetic_operation(
        &mut self,
        ast: &Ast,
        op: &ast::BinaryArithmeticOperation,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::ArithmeticOperation(ArithmeticOperation {
            span: ast.span(),
            operator: match op.operator {
                ast::BinaryArithmeticOperator::Add => ArithmeticOperator::Add,
                ast::BinaryArithmeticOperator::Sub => ArithmeticOperator::Sub,
                ast::BinaryArithmeticOperator::Mul => ArithmeticOperator::Mul,
                ast::BinaryArithmeticOperator::Div => ArithmeticOperator::Div,
            },
            lhs: std::boxed::Box::new(expect_expression!(
                self.compile(&op.lhs, vm, ast_compiler),
                ast.span()
            )),
            rhs: std::boxed::Box::new(expect_expression!(
                self.compile(&op.rhs, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_comparison_operation(
        &mut self,
        ast: &Ast,
        op: &ast::ComparisonOperation,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::ComparisonOperation(ComparisonOperation {
            span: ast.span(),
            operator: match op.operator {
                ast::ComparisonOperator::Eq => ComparisonOperator::Eq,
                ast::ComparisonOperator::Lt => ComparisonOperator::Lt,
                ast::ComparisonOperator::Gt => ComparisonOperator::Gt,
            },
            lhs: std::boxed::Box::new(expect_expression!(
                self.compile(&op.lhs, vm, ast_compiler),
                ast.span()
            )),
            rhs: std::boxed::Box::new(expect_expression!(
                self.compile(&op.rhs, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_list(
        &mut self,
        ast: &Ast,
        list: &ast::List,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::List(List {
            span: ast.span(),
            exprs: list
                .exprs
                .iter()
                .map(|expr| match self.compile(expr, vm, ast_compiler) {
                    Ok(Some(tree)) => Ok(tree),
                    Ok(None) => Err(std::boxed::Box::new(Error {
                        span: ast.span(),
                        message: "unexpected expression".to_string(),
                    }) as _),
                    Err(e) => Err(e),
                })
                .collect::<Result<Vec<_>, _>>()?,
        })))
    }

    fn compile_cons(
        &mut self,
        ast: &Ast,
        cons: &ast::Cons,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::Cons(Cons {
            span: ast.span(),
            lhs: std::boxed::Box::new(expect_expression!(
                self.compile(&cons.lhs, vm, ast_compiler),
                ast.span()
            )),
            rhs: std::boxed::Box::new(expect_expression!(
                self.compile(&cons.rhs, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_car(
        &mut self,
        ast: &Ast,
        car: &ast::Car,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::Car(Car {
            span: ast.span(),
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&car.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_cdr(
        &mut self,
        ast: &Ast,
        cdr: &ast::Cdr,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::Cdr(Cdr {
            span: ast.span(),
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&cdr.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_is_type(
        &mut self,
        ast: &Ast,
        is_type: &ast::IsType,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::IsType(IsType {
            span: ast.span(),
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
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&is_type.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_assert(
        &mut self,
        ast: &Ast,
        assert: &ast::Assert,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::Assert(Assert {
            span: ast.span(),
            body: std::boxed::Box::new(expect_expression!(
                self.compile(&assert.body, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_gensym(
        &mut self,
        ast: &Ast,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        let suffix = rand::random::<u32>();

        let symbol = format!("e{suffix}");

        Ok(Some(Il::Constant(Constant::Symbol {
            span: ast.span(),
            symbol,
        })))
    }

    fn compile_map_create(
        &mut self,
        ast: &Ast,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::MapCreate(MapCreate { span: ast.span() })))
    }

    fn compile_map_insert(
        &mut self,
        ast: &Ast,
        map_insert: &ast::MapInsert,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::MapInsert(MapInsert {
            span: ast.span(),
            map: std::boxed::Box::new(expect_expression!(
                self.compile(&map_insert.map, vm, ast_compiler),
                ast.span()
            )),
            key: std::boxed::Box::new(expect_expression!(
                self.compile(&map_insert.key, vm, ast_compiler),
                ast.span()
            )),
            value: std::boxed::Box::new(expect_expression!(
                self.compile(&map_insert.value, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_map_retrieve(
        &mut self,
        ast: &Ast,
        map_retrieve: &ast::MapRetrieve,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::MapRetrieve(MapRetrieve {
            span: ast.span(),
            map: std::boxed::Box::new(expect_expression!(
                self.compile(&map_retrieve.map, vm, ast_compiler),
                ast.span()
            )),
            key: std::boxed::Box::new(expect_expression!(
                self.compile(&map_retrieve.key, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_map_items(
        &mut self,
        ast: &Ast,
        map_items: &ast::MapItems,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::MapItems(MapItems {
            span: ast.span(),
            map: std::boxed::Box::new(expect_expression!(
                self.compile(&map_items.map, vm, ast_compiler),
                ast.span()
            )),
        })))
    }

    fn compile_deftype(
        &mut self,
        deftype: &ast::DefType,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        for variant in &deftype.variants {
            let pattern = format!("{}-{}", deftype.name, variant.name);
            let parameter = match variant.r#type.as_ref() {
                Some(t) => DefTypePattern::Struct(t.clone()),
                None => DefTypePattern::Empty,
            };

            self.deftype_patterns.insert(pattern, parameter);
        }

        Ok(Some(Il::DefType(deftype.clone())))
    }

    fn compile_make_type(
        &mut self,
        ast: &Ast,
        make_type: &ast::MakeType,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        let body = match (
            &self.deftype_patterns[make_type.pattern.as_str()],
            make_type.body.as_ref(),
        ) {
            (DefTypePattern::Struct(_), Some(body)) => Some(body),
            (DefTypePattern::Struct(_), None) => {
                return Err(std::boxed::Box::new(Error {
                    span: ast.span(),
                    message: "tried to construct a type without a value".to_string(),
                }))
            }
            (DefTypePattern::Empty, Some(_)) => {
                return Err(std::boxed::Box::new(Error {
                    span: ast.span(),
                    message: "tried to construct an empty type with a value".to_string(),
                }) as _)
            }
            _ => None,
        };

        Ok(Some(Il::MakeType(MakeType {
            span: ast.span(),
            pattern: make_type.pattern.clone(),
            body: match body
                .as_ref()
                .map(|body| self.compile(body, vm, ast_compiler))
            {
                Some(Ok(Some(body))) => Some(std::boxed::Box::new(body)),
                Some(Err(e)) => return Err(e),
                Some(Ok(None)) => {
                    return Err(std::boxed::Box::new(Error {
                        span: ast.span(),
                        message: "unexpected expression".to_string(),
                    }))
                }
                _ => None,
            },
        })))
    }

    fn compile_if_let(
        &mut self,
        ast: &Ast,
        if_let: &ast::IfLet,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        match (
            &self.deftype_patterns[if_let.pattern.as_str()],
            &if_let.binding,
        ) {
            (DefTypePattern::Struct(_), None) => {
                return Err(std::boxed::Box::new(Error {
                    span: ast.span(),
                    message: "this pattern requires a binding".to_string(),
                }))
            }
            (DefTypePattern::Empty, Some(_)) => {
                return Err(std::boxed::Box::new(Error {
                    span: ast.span(),
                    message: "this pattern can not have a binding".to_string(),
                }))
            }
            _ => (),
        }

        if let Some(binding) = if_let.binding.as_ref() {
            let body = std::boxed::Box::new(expect_expression!(
                self.compile(&if_let.body, vm, ast_compiler),
                ast.span()
            ));

            self.environment.push_scope(iter::once(binding.clone()));

            let then = std::boxed::Box::new(expect_expression!(
                self.compile(&if_let.then, vm, ast_compiler),
                ast.span()
            ));

            let upvalues = self.environment.upvalues().collect();

            self.environment.pop_scope();

            let r#else = std::boxed::Box::new(expect_expression!(
                self.compile(&if_let.r#else, vm, ast_compiler),
                ast.span()
            ));

            Ok(Some(Il::IfLet(IfLet {
                span: ast.span(),
                body,
                pattern: if_let.pattern.clone(),
                binding: Some(binding.clone()),
                then,
                r#else,
                upvalues,
            })))
        } else {
            let body = std::boxed::Box::new(expect_expression!(
                self.compile(&if_let.body, vm, ast_compiler),
                ast.span()
            ));

            let then = std::boxed::Box::new(expect_expression!(
                self.compile(&if_let.then, vm, ast_compiler),
                ast.span()
            ));

            let r#else = std::boxed::Box::new(expect_expression!(
                self.compile(&if_let.r#else, vm, ast_compiler),
                ast.span()
            ));

            Ok(Some(Il::IfLet(IfLet {
                span: ast.span(),
                body,
                pattern: if_let.pattern.clone(),
                binding: None,
                then,
                r#else,
                upvalues: Vec::new(),
            })))
        }
    }

    fn compile_letrec(
        &mut self,
        ast: &Ast,
        letrec: &ast::LetRec,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        self.environment
            .push_scope(letrec.bindings.iter().map(|(binding, _)| binding.clone()));

        let exprs = letrec
            .bindings
            .iter()
            .map(|(_, expr)| match self.compile(expr, vm, ast_compiler) {
                Ok(Some(il)) => Ok(il),
                Ok(None) => Err(std::boxed::Box::new(Error {
                    span: ast.span(),
                    message: "expected expression".to_string(),
                }) as _),
                Err(e) => Err(e),
            })
            .collect::<Result<Vec<Il>, _>>()?;

        let body = expect_expression!(self.compile(&letrec.body, vm, ast_compiler), ast.span());

        let upvalues = self.environment.upvalues().collect();

        self.environment.pop_scope();

        Ok(Some(Il::LetRec(LetRec {
            span: ast.span(),
            bindings: letrec
                .bindings
                .iter()
                .map(|(binding, _)| binding.clone())
                .zip(exprs)
                .collect::<Vec<_>>(),
            upvalues,
            body: std::boxed::Box::new(body),
        })))
    }
}

impl<'parameters> IntoIterator for &'parameters Parameters {
    type Item = String;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Parameters::Nary(params) | Parameters::Variadic(params) => params.iter().cloned(),
        }
    }
}

impl error::Error for Error {
    fn span(&self) -> Option<FileSpan> {
        Some(self.span)
    }

    fn message(&self, writer: &mut dyn std::io::Write) {
        write!(writer, "{}", self.message).unwrap();
    }
}
