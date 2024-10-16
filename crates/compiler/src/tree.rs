use std::{collections::HashMap, rc::Rc};

use crate::{
    ast::{
        self, Ast, Decl, DefStruct, DefType, Quoted, StructAccessor, StructConstructor, Type,
        VariantPattern,
    },
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
    FloatOperation(FloatOperation),
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
    DefStruct(ast::DefStruct),
    MakeStruct(MakeStruct),
    GetField(GetField),
    MakeVec(MakeVec),
    VecPush(VecPush),
    VecPop(VecPop),
    VecRef(VecRef),
    VecSet(VecSet),
    VecLength(VecLength),
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
    Float { span: FileSpan, float: f64 },
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

#[derive(Clone, Debug, EnumAs, EnumIs)]
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
pub enum FloatOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct FloatOperation {
    pub span: FileSpan,
    pub operator: FloatOperator,
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
    Float,
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
    pub pattern: VariantPattern,
    pub exprs: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct IfLet {
    pub span: FileSpan,
    pub body: std::boxed::Box<Il>,
    pub pattern: VariantPattern,
    pub bindings: Vec<String>,
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
    Struct(Vec<Type>),
    Empty,
}

#[derive(Clone, Debug)]
pub struct MakeStruct {
    pub span: FileSpan,
    pub struct_name: String,
    pub constructor: StructConstructor,
    pub exprs: Vec<Il>,
}

#[derive(Clone, Debug)]
pub struct GetField {
    pub span: FileSpan,
    pub struct_name: String,
    pub field_name: String,
    pub accessor: StructAccessor,
    pub index: usize,
    pub body: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct MakeVec {
    pub span: FileSpan,
    pub capacity: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct VecPush {
    pub span: FileSpan,
    pub vec: std::boxed::Box<Il>,
    pub expr: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct VecPop {
    pub span: FileSpan,
    pub vec: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct VecRef {
    pub span: FileSpan,
    pub vec: std::boxed::Box<Il>,
    pub index: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct VecSet {
    pub span: FileSpan,
    pub vec: std::boxed::Box<Il>,
    pub index: std::boxed::Box<Il>,
    pub expr: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
pub struct VecLength {
    pub span: FileSpan,
    pub vec: std::boxed::Box<Il>,
}

#[derive(Clone, Debug)]
struct Struct {
    name: String,
    fields: Vec<String>,
}

pub struct Compiler {
    environment: Environment,
    deftype_patterns: HashMap<VariantPattern, DefTypePattern>,
    structs: HashMap<StructAccessor, Struct>,
    constructors: HashMap<StructConstructor, Struct>,
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
            | Self::Float { span, .. }
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
            | Self::FloatOperation(FloatOperation { span, .. })
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
            | Self::DefStruct(DefStruct { span, .. })
            | Self::MakeStruct(MakeStruct { span, .. })
            | Self::GetField(GetField { span, .. })
            | Self::MakeVec(MakeVec { span, .. })
            | Self::VecPush(VecPush { span, .. })
            | Self::VecPop(VecPop { span, .. })
            | Self::VecRef(VecRef { span, .. })
            | Self::VecSet(VecSet { span, .. })
            | Self::VecLength(VecLength { span, .. })
            | Self::VarRef(VarRef::Local { span, .. })
            | Self::VarRef(VarRef::UpValue { span, .. })
            | Self::VarRef(VarRef::Global { span, .. })
            | Self::Constant(Constant::Symbol { span, .. })
            | Self::Constant(Constant::String { span, .. })
            | Self::Constant(Constant::Char { span, .. })
            | Self::Constant(Constant::Int { span, .. })
            | Self::Constant(Constant::Float { span, .. })
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
            structs: HashMap::new(),
            constructors: HashMap::new(),
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
            Ast::BinaryFloatOperation(op) => {
                self.compile_float_operation(ast, op, vm, ast_compiler)
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
            Ast::Constant(constant) => self.compile_constant(ast, constant),
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
            Ast::DefType(deftype) => self.compile_deftype(deftype),
            Ast::MakeType(make_type) => self.compile_make_type(ast, make_type, vm, ast_compiler),
            Ast::IfLet(if_let) => self.compile_if_let(ast, if_let, vm, ast_compiler),
            Ast::LetRec(letrec) => self.compile_letrec(ast, letrec, vm, ast_compiler),
            Ast::DefStruct(defstruct) => self.compile_defstruct(defstruct),
            Ast::MakeStruct(make_struct) => self.compile_make_struct(make_struct, vm, ast_compiler),
            Ast::GetField(get_field) => self.compile_get_field(get_field, vm, ast_compiler),
            Ast::MakeVec(make_vec) => self.compile_make_vec(make_vec, vm, ast_compiler),
            Ast::VecPush(vec_push) => self.compile_vec_push(vec_push, vm, ast_compiler),
            Ast::VecPop(vec_pop) => self.compile_vec_pop(vec_pop, vm, ast_compiler),
            Ast::VecRef(vec_index) => self.compile_vec_ref(vec_index, vm, ast_compiler),
            Ast::VecSet(vec_set) => self.compile_vec_set(vec_set, vm, ast_compiler),
            Ast::VecLen(vec_length) => self.compile_vec_length(vec_length, vm, ast_compiler),
            _ => Ok(None),
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
            ast::Constant::Float { float, .. } => Il::Constant(Constant::Float {
                span: ast.span(),
                float: *float,
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

        self.environment.pop_scope();

        let lambda = Il::Lambda(self::Lambda {
            span: ast.span(),
            parameters,
            r#type: None,
            upvalues: Vec::new(),
            arity,
            body,
        });

        let mut opcodes = OpCodeTable::new();
        let mut constants = Vec::new();

        bytecode::compile(&lambda, &mut opcodes, &mut constants).map_err(std::boxed::Box::new)?;

        for constant in constants {
            vm.load_constant(constant);
        }

        vm.eval(&opcodes)?;

        let constant = vm::Constant::Symbol(Rc::new(defmacro.name.clone()));
        let hash = bytecode::hash_constant(&constant);

        vm.load_constant(constant);

        vm.def_global(hash).map_err(std::boxed::Box::new)?;

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
        let mut constants = Vec::new();

        for arg in &macro_call.args {
            let il = self.compile_quoted(ast, arg)?.unwrap();

            bytecode::compile(&il, &mut opcode_table, &mut constants).unwrap();
        }

        let constant: vm::Constant<FileSpan> =
            vm::Constant::Symbol(Rc::new(macro_call.r#macro.clone()));
        let hash = bytecode::hash_constant(&constant);

        for constant in constants {
            vm.load_constant(constant);
        }

        vm.get_global(hash)?;

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

        let sexpr = sexpr.set_span(ast.span());

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
        _: &Ast,
        decl: &ast::Decl,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        self.environment.insert_global(decl.parameter.name.as_str());

        Ok(Some(Il::Decl(decl.clone())))
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
            Quoted::Float { float, .. } => Il::Constant(Constant::Float {
                span: ast.span(),
                float: *float,
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
                        Quoted::Float { float, .. } => Il::Constant(Constant::Float {
                            span: ast.span(),
                            float: *float,
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

    fn compile_float_operation(
        &mut self,
        ast: &Ast,
        op: &ast::BinaryFloatOperation,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::FloatOperation(FloatOperation {
            span: ast.span(),
            operator: match op.operator {
                ast::BinaryFloatOperator::Add => FloatOperator::Add,
                ast::BinaryFloatOperator::Sub => FloatOperator::Sub,
                ast::BinaryFloatOperator::Mul => FloatOperator::Mul,
                ast::BinaryFloatOperator::Div => FloatOperator::Div,
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
                ast::IsTypeParameter::Float => IsTypeParameter::Float,
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
            let parameter = if !variant.types.is_empty() {
                DefTypePattern::Struct(variant.types.clone())
            } else {
                DefTypePattern::Empty
            };

            self.deftype_patterns
                .insert(VariantPattern(pattern), parameter);
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
        match self.deftype_patterns[&make_type.pattern].clone() {
            DefTypePattern::Struct(types) if types.len() != make_type.body.len() => {
                return Err(std::boxed::Box::new(Error {
                    span: make_type.span,
                    message: "tried to construct variant with wrong number of fields".to_string(),
                }) as _)
            }
            DefTypePattern::Empty if !make_type.body.is_empty() => {
                return Err(std::boxed::Box::new(Error {
                    span: make_type.span,
                    message: "tried to construct empty variant with fields".to_string(),
                }) as _)
            }
            _ => (),
        }

        Ok(Some(Il::MakeType(MakeType {
            span: ast.span(),
            pattern: make_type.pattern.clone(),
            exprs: make_type
                .body
                .iter()
                .map(|expr| match self.compile(expr, vm, ast_compiler) {
                    Ok(Some(il)) => Ok(il),
                    Ok(None) => Err(std::boxed::Box::new(Error {
                        span: make_type.span,
                        message: "unexpected expression".to_string(),
                    }) as _),
                    Err(e) => Err(e),
                })
                .collect::<Result<Vec<_>, _>>()?,
        })))
    }

    fn compile_if_let(
        &mut self,
        ast: &Ast,
        if_let: &ast::IfLet,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        match self.deftype_patterns[&if_let.pattern].clone() {
            DefTypePattern::Struct(types) if types.len() != if_let.bindings.len() => {
                return Err(std::boxed::Box::new(Error {
                    span: if_let.span,
                    message: format!("this pattern requires {} bindings", types.len()),
                }) as _)
            }
            DefTypePattern::Empty if !if_let.bindings.is_empty() => {
                return Err(std::boxed::Box::new(Error {
                    span: if_let.span,
                    message: "this pattern shouldn't contain any bindings".to_string(),
                }) as _)
            }
            _ => (),
        }

        if !if_let.bindings.is_empty() {
            let body = std::boxed::Box::new(expect_expression!(
                self.compile(&if_let.body, vm, ast_compiler),
                ast.span()
            ));

            self.environment.push_scope(if_let.bindings.iter().cloned());

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
                bindings: if_let.bindings.clone(),
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
                bindings: if_let.bindings.clone(),
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

    fn compile_defstruct(
        &mut self,
        defstruct: &ast::DefStruct,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        let r#struct = Struct {
            name: defstruct.name.clone(),
            fields: defstruct
                .fields
                .iter()
                .map(|(field_name, _)| field_name)
                .cloned()
                .collect(),
        };

        let constructor = StructConstructor(format!("make-{}", r#struct.name));
        self.constructors.insert(constructor, r#struct.clone());

        for field in &r#struct.fields {
            let accessor = format!("{}-{}", r#struct.name, field);
            self.structs
                .insert(StructAccessor(accessor), r#struct.clone());
        }

        Ok(Some(Il::DefStruct(defstruct.clone())))
    }

    fn compile_make_struct(
        &mut self,
        make_struct: &ast::MakeStruct,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        if make_struct.exprs.len() != self.constructors[&make_struct.constructor].fields.len() {
            return Err(std::boxed::Box::new(Error {
                span: make_struct.span,
                message: "wrong number of fields for struct constructor".to_string(),
            }) as _);
        }

        Ok(Some(Il::MakeStruct(MakeStruct {
            span: make_struct.span,
            struct_name: make_struct.name.clone(),
            constructor: make_struct.constructor.clone(),
            exprs: make_struct
                .exprs
                .iter()
                .map(|expr| match self.compile(expr, vm, ast_compiler) {
                    Ok(Some(il)) => Ok(il),
                    Ok(None) => Err(std::boxed::Box::new(Error {
                        span: make_struct.span,
                        message: "unexpected expression".to_string(),
                    }) as _),
                    Err(e) => Err(e),
                })
                .collect::<Result<Vec<_>, _>>()?,
        })))
    }

    fn compile_get_field(
        &mut self,
        get_field: &ast::GetField,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::GetField(GetField {
            span: get_field.span,
            struct_name: get_field.struct_name.clone(),
            field_name: get_field.field_name.clone(),
            accessor: get_field.accessor.clone(),
            index: {
                self.structs[&get_field.accessor]
                    .fields
                    .iter()
                    .enumerate()
                    .find_map(|(i, field)| {
                        if field.as_str() == get_field.field_name.as_str() {
                            Some(i)
                        } else {
                            None
                        }
                    })
                    .unwrap()
            },
            body: std::boxed::Box::new(match self.compile(&get_field.body, vm, ast_compiler) {
                Ok(Some(body)) => body,
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: get_field.span,
                        message: "unexpected expression".to_string(),
                    }) as _)
                }
                Err(e) => return Err(e),
            }),
        })))
    }

    fn compile_make_vec(
        &mut self,
        make_vec: &ast::MakeVec,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::MakeVec(MakeVec {
            span: make_vec.span,
            capacity: match self.compile(&make_vec.capacity, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: make_vec.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
        })))
    }

    fn compile_vec_push(
        &mut self,
        vec_push: &ast::VecPush,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::VecPush(VecPush {
            span: vec_push.span,
            vec: match self.compile(&vec_push.vec, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_push.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
            expr: match self.compile(&vec_push.expr, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_push.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
        })))
    }

    fn compile_vec_pop(
        &mut self,
        vec_pop: &ast::VecPop,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::VecPop(VecPop {
            span: vec_pop.span,
            vec: match self.compile(&vec_pop.vec, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_pop.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
        })))
    }

    fn compile_vec_ref(
        &mut self,
        vec_index: &ast::VecRef,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::VecRef(VecRef {
            span: vec_index.span,
            vec: match self.compile(&vec_index.vec, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_index.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
            index: match self.compile(&vec_index.index, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_index.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
        })))
    }

    fn compile_vec_set(
        &mut self,
        vec_set: &ast::VecSet,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::VecSet(VecSet {
            span: vec_set.span,
            vec: match self.compile(&vec_set.vec, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_set.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
            index: match self.compile(&vec_set.index, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_set.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
            expr: match self.compile(&vec_set.expr, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_set.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
        })))
    }

    fn compile_vec_length(
        &mut self,
        vec_length: &ast::VecLen,
        vm: &mut Vm<FileSpan>,
        ast_compiler: &mut ast::Compiler,
    ) -> Result<Option<Il>, std::boxed::Box<dyn error::Error>> {
        Ok(Some(Il::VecLength(VecLength {
            span: vec_length.span,
            vec: match self.compile(&vec_length.vec, vm, ast_compiler) {
                Ok(Some(expr)) => std::boxed::Box::new(expr),
                Err(e) => return Err(e),
                Ok(None) => {
                    return Err(std::boxed::Box::new(Error {
                        span: vec_length.span,
                        message: "unexpected expression".to_string(),
                    }))
                }
            },
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
