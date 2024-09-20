use core::fmt;
use std::collections::{HashMap, HashSet};

use error::FileSpan;
use reader::Sexpr;
use unwrap_enum::{EnumAs, EnumIs};

static BUILT_INS: &[&str] = &[
    "+",
    "-",
    "*",
    "/",
    "cons",
    "car",
    "cdr",
    "list",
    "apply",
    "cons?",
    "function?",
    "symbol?",
    "string?",
    "int?",
    "char?",
    "nil?",
    "apply",
    "lambda",
    "defmacro",
    "def",
    "set!",
    "eval-when-compile",
    "quote",
    "if",
    "=",
    ">",
    "<",
    "assert",
    "decl",
    "map-create",
    "map-insert!",
    "map-retrieve",
    "map-items",
    "require",
    "box",
    "set-box!",
    "unbox",
    "gensym",
    "let-type",
    "deftype",
    "if-let",
    "letrec",
    "defstruct",
];

#[derive(Clone, Debug)]
pub struct Error {
    pub span: FileSpan,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructConstructor(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructAccessor(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructFieldName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariantPattern(pub String);

#[derive(Clone, Debug)]
pub struct Compiler {
    macros: HashSet<String>,
    deftypes: HashMap<VariantPattern, Variant>,
    structs: HashMap<StructAccessor, Struct>,
    fields: HashMap<StructAccessor, StructFieldName>,
    constructors: HashMap<StructConstructor, Struct>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Ast {
    Require(Require),
    EvalWhenCompile(EvalWhenCompile),
    DefMacro(DefMacro),
    Lambda(Lambda),
    Def(Def),
    Decl(Decl),
    Set(Set),
    SetBox(SetBox),
    UnBox(UnBox),
    Box(Box),
    If(If),
    Apply(Apply),
    BinaryArithemticOperation(BinaryArithmeticOperation),
    ComparisonOperation(ComparisonOperation),
    List(List),
    Cons(Cons),
    Car(Car),
    Cdr(Cdr),
    FnCall(FnCall),
    MacroCall(MacroCall),
    Quote(Quote),
    IsType(IsType),
    MapCreate(MapCreate),
    MapInsert(MapInsert),
    MapRetrieve(MapRetrieve),
    MapItems(MapItems),
    Variable(Variable),
    Constant(Constant),
    Assert(Assert),
    GenSym(GenSym),
    LetType(LetType),
    DefType(DefType),
    MakeType(MakeType),
    IfLet(IfLet),
    LetRec(LetRec),
    DefStruct(DefStruct),
    MakeStruct(MakeStruct),
    GetField(GetField),
}

#[derive(Clone, Debug)]
pub struct EvalWhenCompile {
    pub span: FileSpan,
    pub exprs: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub span: FileSpan,
    pub name: String,
}

#[derive(Clone, Debug)]
pub enum Constant {
    String { span: FileSpan, string: String },
    Char { span: FileSpan, char: char },
    Int { span: FileSpan, int: i64 },
    Bool { span: FileSpan, bool: bool },
    Nil { span: FileSpan },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Scalar(String),
    Composite(Vec<Type>),
    Inferred,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefParameter {
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters {
    Normal(Vec<String>),
    Rest(Vec<String>, String),
}

#[derive(Clone, Debug)]
pub struct Require {
    pub span: FileSpan,
    pub module: String,
}

#[derive(Clone, Debug)]
pub struct DefMacro {
    pub span: FileSpan,
    pub name: String,
    pub parameters: Parameters,
    pub body: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Lambda {
    pub span: FileSpan,
    pub r#type: Option<Type>,
    pub parameters: Parameters,
    pub body: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Def {
    pub span: FileSpan,
    pub parameter: DefParameter,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub span: FileSpan,
    pub parameter: DefParameter,
}

#[derive(Clone, Debug)]
pub struct Set {
    pub span: FileSpan,
    pub target: String,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct SetBox {
    pub span: FileSpan,
    pub target: std::boxed::Box<Ast>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct UnBox {
    pub span: FileSpan,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Box {
    pub span: FileSpan,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct If {
    pub span: FileSpan,
    pub predicate: std::boxed::Box<Ast>,
    pub then: std::boxed::Box<Ast>,
    pub r#else: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Apply {
    pub span: FileSpan,
    pub function: std::boxed::Box<Ast>,
    pub list: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub enum BinaryArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct BinaryArithmeticOperation {
    pub span: FileSpan,
    pub operator: BinaryArithmeticOperator,
    pub lhs: std::boxed::Box<Ast>,
    pub rhs: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum ComparisonOperator {
    Lt,
    Gt,
    Eq,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation {
    pub span: FileSpan,
    pub operator: ComparisonOperator,
    pub lhs: std::boxed::Box<Ast>,
    pub rhs: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct List {
    pub span: FileSpan,
    pub exprs: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Cons {
    pub span: FileSpan,
    pub lhs: std::boxed::Box<Ast>,
    pub rhs: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Car {
    pub span: FileSpan,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Cdr {
    pub span: FileSpan,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct FnCall {
    pub span: FileSpan,
    pub function: std::boxed::Box<Ast>,
    pub exprs: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct MacroCall {
    pub span: FileSpan,
    pub r#macro: String,
    pub args: Vec<Quoted>,
}

#[derive(Clone, Debug)]
pub struct Quote {
    pub span: FileSpan,
    pub body: Quoted,
}

#[derive(Clone, Debug)]
pub enum IsTypeParameter {
    Function,
    Cons,
    Symbol,
    String,
    Int,
    Char,
    Bool,
    Nil,
}

#[derive(Clone, Debug)]
pub struct IsType {
    pub span: FileSpan,
    pub parameter: IsTypeParameter,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Assert {
    pub span: FileSpan,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct MapCreate {
    pub span: FileSpan,
}

#[derive(Clone, Debug)]
pub struct MapInsert {
    pub span: FileSpan,
    pub map: std::boxed::Box<Ast>,
    pub key: std::boxed::Box<Ast>,
    pub value: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve {
    pub span: FileSpan,
    pub map: std::boxed::Box<Ast>,
    pub key: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct MapItems {
    pub span: FileSpan,
    pub map: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub enum Quoted {
    List { span: FileSpan, list: Vec<Quoted> },
    Symbol { span: FileSpan, symbol: String },
    String { span: FileSpan, string: String },
    Char { span: FileSpan, char: char },
    Int { span: FileSpan, int: i64 },
    Bool { span: FileSpan, bool: bool },
    Nil { span: FileSpan },
}

#[derive(Clone, Debug)]
pub struct GenSym {
    pub span: FileSpan,
}

#[derive(Clone, Debug)]
pub struct LetType {
    pub span: FileSpan,
    pub name: String,
    pub r#type: Type,
}

#[derive(Clone, Debug)]
pub struct DefType {
    pub span: FileSpan,
    pub name: String,
    pub variants: Vec<Variant>,
}

#[derive(Clone, Debug)]
pub struct MakeType {
    pub span: FileSpan,
    pub pattern: VariantPattern,
    pub body: Option<std::boxed::Box<Ast>>,
}

#[derive(Clone, Debug)]
pub struct Variant {
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub struct IfLet {
    pub span: FileSpan,
    pub body: std::boxed::Box<Ast>,
    pub pattern: VariantPattern,
    pub binding: Option<String>,
    pub then: std::boxed::Box<Ast>,
    pub r#else: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct LetRec {
    pub span: FileSpan,
    pub bindings: Vec<(String, Ast)>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct DefStruct {
    pub span: FileSpan,
    pub name: String,
    pub fields: Vec<(String, Type)>,
}

#[derive(Clone, Debug)]
pub struct MakeStruct {
    pub span: FileSpan,
    pub name: String,
    pub constructor: StructConstructor,
    pub exprs: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct GetField {
    pub span: FileSpan,
    pub struct_name: String,
    pub field_name: String,
    pub accessor: StructAccessor,
    pub body: std::boxed::Box<Ast>,
}

#[allow(clippy::new_without_default)]
impl Compiler {
    pub fn new() -> Self {
        Self {
            macros: HashSet::new(),
            deftypes: HashMap::new(),
            structs: HashMap::new(),
            fields: HashMap::new(),
            constructors: HashMap::new(),
        }
    }

    pub fn compile(&mut self, sexpr: &Sexpr) -> Result<Ast, Error> {
        use Sexpr::*;
        Ok(match sexpr {
            Sexpr::List { list, .. }
                if list
                    .first()
                    .and_then(|first| first.as_symbol())
                    .is_some_and(|symbol| BUILT_INS.iter().any(|b| symbol == *b))
                    || list
                        .first()
                        .and_then(|first| first.as_symbol())
                        .is_some_and(|symbol| {
                            self.deftypes
                                .contains_key(&VariantPattern(symbol.to_string()))
                        })
                    || list
                        .first()
                        .and_then(|first| first.as_symbol())
                        .is_some_and(|symbol| {
                            self.structs
                                .contains_key(&StructAccessor(symbol.to_string()))
                        })
                    || list
                        .first()
                        .and_then(|first| first.as_symbol())
                        .is_some_and(|symbol| {
                            self.constructors
                                .contains_key(&StructConstructor(symbol.to_string()))
                        }) =>
            {
                match list.as_slice() {
                    [Symbol { symbol, .. }, Symbol { symbol: module, .. }]
                        if symbol == "require" =>
                    {
                        self.compile_require(sexpr, module)?
                    }
                    [Symbol { symbol, .. }, rest @ ..] if symbol == "eval-when-compile" => {
                        self.compile_eval_when_compile(sexpr, rest)?
                    }
                    [Symbol { symbol, .. }, Symbol { symbol: name, .. }, parameters, rest @ ..]
                        if symbol == "defmacro" =>
                    {
                        self.compile_defmacro(sexpr, name, parameters, rest)?
                    }
                    [Symbol { symbol, .. }, parameters, Symbol { symbol: arrow, .. }, r#type, rest @ ..]
                        if symbol == "lambda" && arrow == "->" =>
                    {
                        self.compile_lambda(sexpr, parameters, Some(r#type), rest)?
                    }
                    [Symbol { symbol, .. }, parameters, rest @ ..] if symbol == "lambda" => {
                        self.compile_lambda(sexpr, parameters, None, rest)?
                    }
                    [Symbol { symbol, .. }, parameter, body] if symbol == "def" => {
                        self.compile_def(sexpr, parameter, body)?
                    }
                    [Symbol { symbol, .. }, parameter] if symbol == "decl" => {
                        self.compile_decl(sexpr, parameter)?
                    }
                    [Symbol { symbol, .. }, Symbol { symbol: target, .. }, body]
                        if symbol == "set!" =>
                    {
                        self.compile_set(sexpr, target, body)?
                    }
                    [Symbol { symbol, .. }, target, body] if symbol == "set-box!" => {
                        self.compile_set_box(sexpr, target, body)?
                    }
                    [Symbol { symbol, .. }, body] if symbol == "unbox" => {
                        self.compile_unbox(sexpr, body)?
                    }
                    [Symbol { symbol, .. }, body] if symbol == "box" => {
                        self.compile_box(sexpr, body)?
                    }
                    [Symbol { symbol, .. }, predicate, then, r#else] if symbol == "if" => {
                        self.compile_if(sexpr, predicate, then, r#else)?
                    }
                    [Symbol { symbol, .. }, function, list] if symbol == "apply" => {
                        self.compile_apply(sexpr, function, list)?
                    }
                    [Symbol { symbol, .. }, lhs, rhs]
                        if matches!(symbol.as_str(), "+" | "-" | "*" | "/") =>
                    {
                        self.compile_binary_arithmetic_op(sexpr, symbol, lhs, rhs)?
                    }
                    [Symbol { symbol, .. }, lhs, rhs]
                        if matches!(symbol.as_str(), "=" | "<" | ">") =>
                    {
                        self.compile_comparison_op(sexpr, symbol, lhs, rhs)?
                    }
                    [Symbol { symbol, .. }, rest @ ..] if symbol == "list" => {
                        self.compile_list(sexpr, rest)?
                    }
                    [Symbol { symbol, .. }, lhs, rhs] if symbol == "cons" => {
                        self.compile_cons(sexpr, lhs, rhs)?
                    }
                    [Symbol { symbol, .. }, body] if symbol == "car" => {
                        self.compile_car(sexpr, body)?
                    }
                    [Symbol { symbol, .. }, body] if symbol == "cdr" => {
                        self.compile_cdr(sexpr, body)?
                    }
                    [Symbol { symbol, .. }, body]
                        if matches!(
                            symbol.as_str(),
                            "function?"
                                | "cons?"
                                | "symbol?"
                                | "string?"
                                | "char?"
                                | "int?"
                                | "bool?"
                                | "nil?"
                        ) =>
                    {
                        self.compile_is_type(sexpr, symbol, body)?
                    }
                    [Symbol { symbol, .. }, body] if symbol == "quote" => {
                        self.compile_quote(sexpr, body)?
                    }
                    [Symbol { symbol, .. }, body] if symbol == "assert" => {
                        self.compile_assert(sexpr, body)?
                    }
                    [Symbol { symbol, .. }] if symbol == "map-create" => {
                        Ast::MapCreate(MapCreate { span: sexpr.span() })
                    }
                    [Symbol { symbol, .. }, map, key, value] if symbol == "map-insert!" => {
                        self.compile_map_insert(sexpr, map, key, value)?
                    }
                    [Symbol { symbol, .. }, map, key] if symbol == "map-retrieve" => {
                        self.compile_map_retrieve(sexpr, map, key)?
                    }
                    [Symbol { symbol, .. }, map] if symbol == "map-items" => {
                        self.compile_map_items(sexpr, map)?
                    }
                    [Symbol { symbol, .. }] if symbol == "gensym" => {
                        Ast::GenSym(GenSym { span: sexpr.span() })
                    }
                    [Symbol { symbol, .. }, Symbol { symbol: name, .. }, r#type]
                        if symbol == "let-type" =>
                    {
                        self.compile_let_type(sexpr, name.as_str(), r#type)?
                    }
                    [Sexpr::Symbol {
                        symbol: deftype, ..
                    }, Sexpr::Symbol { symbol: name, .. }, variants @ ..]
                        if deftype == "deftype" =>
                    {
                        self.compile_deftype(sexpr, name.as_str(), variants)?
                    }
                    [Sexpr::Symbol {
                        symbol: function, ..
                    }, body]
                        if self
                            .deftypes
                            .contains_key(&VariantPattern(function.to_string())) =>
                    {
                        self.compile_make_type(sexpr, function, Some(body))?
                    }
                    [Sexpr::Symbol {
                        symbol: function, ..
                    }] if self
                        .deftypes
                        .contains_key(&VariantPattern(function.to_string())) =>
                    {
                        self.compile_make_type(sexpr, function, None)?
                    }
                    [Sexpr::Symbol { symbol: if_let, .. }, body, pattern, then, r#else]
                        if if_let == "if-let" =>
                    {
                        self.compile_if_let(sexpr, body, pattern, then, r#else)?
                    }
                    [Sexpr::Symbol { symbol: letrec, .. }, Sexpr::List { list: bindings, .. }, body]
                        if letrec == "letrec" =>
                    {
                        self.compile_letrec(sexpr, bindings.as_slice(), body)?
                    }
                    [Sexpr::Symbol {
                        symbol: defstruct, ..
                    }, Sexpr::Symbol {
                        symbol: struct_name,
                        ..
                    }, fields @ ..]
                        if defstruct == "defstruct" =>
                    {
                        self.compile_defstruct(sexpr, struct_name.as_str(), fields)?
                    }
                    [Sexpr::Symbol {
                        symbol: constructor,
                        ..
                    }, exprs @ ..]
                        if self
                            .constructors
                            .contains_key(&StructConstructor(constructor.to_string())) =>
                    {
                        self.compile_make_struct(sexpr, constructor, exprs)?
                    }
                    [Sexpr::Symbol {
                        symbol: accessor, ..
                    }, body]
                        if self
                            .structs
                            .contains_key(&StructAccessor(accessor.to_string())) =>
                    {
                        self.compile_get_field(sexpr, accessor, body)?
                    }
                    _ => {
                        return Err(Error {
                            span: sexpr.span(),
                            message: "invalid expression".to_string(),
                        })
                    }
                }
            }
            List { list, .. }
                if list
                    .first()
                    .and_then(|first| first.as_symbol())
                    .is_some_and(|symbol| self.macros.contains(symbol)) =>
            {
                self.compile_macro_call(
                    sexpr,
                    list.first().unwrap().as_symbol().unwrap(),
                    &list.as_slice()[1..],
                )?
            }

            List { list, .. } if !list.is_empty() => {
                self.compile_fncall(sexpr, list.first().unwrap(), &list.as_slice()[1..])?
            }
            Symbol { symbol, .. } => Ast::Variable(Variable {
                span: sexpr.span(),
                name: symbol.clone(),
            }),
            String { string, .. } => Ast::Constant(Constant::String {
                span: sexpr.span(),
                string: string.clone(),
            }),
            Char { char, .. } => Ast::Constant(Constant::Char {
                span: sexpr.span(),
                char: *char,
            }),
            Int { int, .. } => Ast::Constant(Constant::Int {
                span: sexpr.span(),
                int: *int,
            }),
            Bool { bool, .. } => Ast::Constant(Constant::Bool {
                span: sexpr.span(),
                bool: *bool,
            }),
            Nil { .. } => Ast::Constant(Constant::Nil { span: sexpr.span() }),
            _ => unreachable!(),
        })
    }

    fn compile_require(&mut self, sexpr: &Sexpr, module: &str) -> Result<Ast, Error> {
        Ok(Ast::Require(Require {
            span: sexpr.span(),
            module: module.to_string(),
        }))
    }

    fn compile_eval_when_compile(&mut self, sexpr: &Sexpr, args: &[Sexpr]) -> Result<Ast, Error> {
        Ok(Ast::EvalWhenCompile(EvalWhenCompile {
            span: sexpr.span(),
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_defmacro(
        &mut self,
        sexpr: &Sexpr,
        name: &str,
        parameters: &Sexpr,
        rest: &[Sexpr],
    ) -> Result<Ast, Error> {
        self.macros.insert(name.to_string());

        Ok(Ast::DefMacro(DefMacro {
            span: sexpr.span(),
            name: name.to_string(),
            parameters: match parameters {
                Sexpr::List { list, .. } => {
                    parse_parameters(sexpr, list.as_slice()).map_err(|_| Error {
                        span: sexpr.span(),
                        message: "failed to parse parameters".to_string(),
                    })?
                }
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        span: sexpr.span(),
                        message: "expected list for parameters".to_string(),
                    })
                }
            },
            body: rest
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_lambda(
        &mut self,
        sexpr: &Sexpr,
        parameters: &Sexpr,
        r#type: Option<&Sexpr>,
        rest: &[Sexpr],
    ) -> Result<Ast, Error> {
        Ok(Ast::Lambda(Lambda {
            span: sexpr.span(),
            r#type: match r#type.map(Type::from_sexpr) {
                Some(Ok(t)) => Some(t),
                Some(Err(_)) => {
                    return Err(Error {
                        span: sexpr.span(),
                        message: "failed to parse type".to_string(),
                    })
                }
                None => None,
            },
            parameters: match parameters {
                Sexpr::List { list, .. } => {
                    parse_parameters(sexpr, list.as_slice()).map_err(|_| Error {
                        span: sexpr.span(),
                        message: "failed to parse parameters".to_string(),
                    })?
                }
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        span: sexpr.span(),
                        message: "expectes list for parameters".to_string(),
                    })
                }
            },
            body: rest
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_def(
        &mut self,
        sexpr: &Sexpr,
        parameter: &Sexpr,
        body: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::Def(Def {
            span: sexpr.span(),
            parameter: DefParameter::from_sexpr(parameter).map_err(|_| Error {
                span: sexpr.span(),
                message: "failed to parse parameter".to_string(),
            })?,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_decl(&mut self, sexpr: &Sexpr, parameter: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Decl(Decl {
            span: sexpr.span(),
            parameter: DefParameter::from_sexpr(parameter).map_err(|_| Error {
                span: sexpr.span(),
                message: "failed to parse parameter".to_string(),
            })?,
        }))
    }

    fn compile_set(&mut self, sexpr: &Sexpr, target: &str, body: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Set(Set {
            span: sexpr.span(),
            target: target.to_string(),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_set_box(
        &mut self,
        sexpr: &Sexpr,
        target: &Sexpr,
        body: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::SetBox(SetBox {
            span: sexpr.span(),
            target: std::boxed::Box::new(self.compile(target)?),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_box(&mut self, sexpr: &Sexpr, body: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Box(Box {
            span: sexpr.span(),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_unbox(&mut self, sexpr: &Sexpr, body: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::UnBox(UnBox {
            span: sexpr.span(),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_if(
        &mut self,
        sexpr: &Sexpr,
        predicate: &Sexpr,
        then: &Sexpr,
        r#else: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::If(If {
            span: sexpr.span(),
            predicate: std::boxed::Box::new(self.compile(predicate)?),
            then: std::boxed::Box::new(self.compile(then)?),
            r#else: std::boxed::Box::new(self.compile(r#else)?),
        }))
    }

    fn compile_apply(
        &mut self,
        sexpr: &Sexpr,
        function: &Sexpr,
        list: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::Apply(Apply {
            span: sexpr.span(),
            function: std::boxed::Box::new(self.compile(function)?),
            list: std::boxed::Box::new(self.compile(list)?),
        }))
    }

    fn compile_binary_arithmetic_op(
        &mut self,
        sexpr: &Sexpr,
        operator: &str,
        lhs: &Sexpr,
        rhs: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::BinaryArithemticOperation(BinaryArithmeticOperation {
            span: sexpr.span(),
            operator: match operator {
                "+" => BinaryArithmeticOperator::Add,
                "-" => BinaryArithmeticOperator::Sub,
                "*" => BinaryArithmeticOperator::Mul,
                "/" => BinaryArithmeticOperator::Div,
                _ => unreachable!(),
            },
            lhs: std::boxed::Box::new(self.compile(lhs)?),
            rhs: std::boxed::Box::new(self.compile(rhs)?),
        }))
    }

    fn compile_comparison_op(
        &mut self,
        sexpr: &Sexpr,
        operator: &str,
        lhs: &Sexpr,
        rhs: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::ComparisonOperation(ComparisonOperation {
            span: sexpr.span(),
            operator: match operator {
                "=" => ComparisonOperator::Eq,
                "<" => ComparisonOperator::Lt,
                ">" => ComparisonOperator::Gt,
                _ => unreachable!(),
            },
            lhs: std::boxed::Box::new(self.compile(lhs)?),
            rhs: std::boxed::Box::new(self.compile(rhs)?),
        }))
    }

    fn compile_list(&mut self, sexpr: &Sexpr, args: &[Sexpr]) -> Result<Ast, Error> {
        Ok(Ast::List(List {
            span: sexpr.span(),
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_cons(&mut self, sexpr: &Sexpr, lhs: &Sexpr, rhs: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Cons(Cons {
            span: sexpr.span(),
            lhs: std::boxed::Box::new(self.compile(lhs)?),
            rhs: std::boxed::Box::new(self.compile(rhs)?),
        }))
    }

    fn compile_car(&mut self, sexpr: &Sexpr, body: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Car(Car {
            span: sexpr.span(),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_cdr(&mut self, sexpr: &Sexpr, body: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Cdr(Cdr {
            span: sexpr.span(),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_fncall(
        &mut self,
        sexpr: &Sexpr,
        function: &Sexpr,
        args: &[Sexpr],
    ) -> Result<Ast, Error> {
        Ok(Ast::FnCall(FnCall {
            span: sexpr.span(),
            function: std::boxed::Box::new(self.compile(function)?),
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_macro_call(
        &mut self,
        sexpr: &Sexpr,
        r#macro: &str,
        args: &[Sexpr],
    ) -> Result<Ast, Error> {
        Ok(Ast::MacroCall(MacroCall {
            span: sexpr.span(),
            r#macro: r#macro.to_string(),
            args: args.iter().map(|arg| quote(sexpr, arg)).collect(),
        }))
    }

    fn compile_quote(&mut self, sexpr: &Sexpr, body: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Quote(Quote {
            span: sexpr.span(),
            body: quote(sexpr, body),
        }))
    }

    fn compile_is_type(
        &mut self,
        sexpr: &Sexpr,
        parameter: &str,
        body: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::IsType(IsType {
            span: sexpr.span(),
            parameter: match parameter {
                "function?" => IsTypeParameter::Function,
                "cons?" => IsTypeParameter::Cons,
                "symbol?" => IsTypeParameter::Symbol,
                "string?" => IsTypeParameter::String,
                "char?" => IsTypeParameter::Char,
                "int?" => IsTypeParameter::Int,
                "bool?" => IsTypeParameter::Bool,
                "nil?" => IsTypeParameter::Nil,
                _ => unreachable!(),
            },
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_assert(&mut self, sexpr: &Sexpr, body: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::Assert(Assert {
            span: sexpr.span(),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_map_insert(
        &mut self,
        sexpr: &Sexpr,
        map: &Sexpr,
        key: &Sexpr,
        value: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::MapInsert(MapInsert {
            span: sexpr.span(),
            map: std::boxed::Box::new(self.compile(map)?),
            key: std::boxed::Box::new(self.compile(key)?),
            value: std::boxed::Box::new(self.compile(value)?),
        }))
    }

    fn compile_map_retrieve(
        &mut self,
        sexpr: &Sexpr,
        map: &Sexpr,
        key: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::MapRetrieve(MapRetrieve {
            span: sexpr.span(),
            map: std::boxed::Box::new(self.compile(map)?),
            key: std::boxed::Box::new(self.compile(key)?),
        }))
    }

    fn compile_map_items(&mut self, sexpr: &Sexpr, map: &Sexpr) -> Result<Ast, Error> {
        Ok(Ast::MapItems(MapItems {
            span: sexpr.span(),
            map: std::boxed::Box::new(self.compile(map)?),
        }))
    }

    fn compile_let_type(
        &mut self,
        sexpr: &Sexpr,
        name: &str,
        r#type: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::LetType(LetType {
            span: sexpr.span(),
            name: name.to_string(),
            r#type: Type::from_sexpr(r#type).map_err(|_| Error {
                span: sexpr.span(),
                message: "failed to parse type".to_string(),
            })?,
        }))
    }

    fn compile_deftype(
        &mut self,
        sexpr: &Sexpr,
        name: &str,
        variants: &[Sexpr],
    ) -> Result<Ast, Error> {
        let variants = variants
            .iter()
            .map(parse_variant)
            .collect::<Result<Vec<Variant>, _>>()
            .map_err(|_| Error {
                span: sexpr.span(),
                message: "failed to parse variant".to_string(),
            })?;

        for variant in &variants {
            let pattern = format!("{}-{}", name, variant.name);
            self.deftypes
                .insert(VariantPattern(pattern.clone()), variant.clone());
        }

        Ok(Ast::DefType(DefType {
            span: sexpr.span(),
            name: name.to_string(),
            variants,
        }))
    }

    fn compile_make_type(
        &mut self,
        sexpr: &Sexpr,
        pattern: &str,
        body: Option<&Sexpr>,
    ) -> Result<Ast, Error> {
        Ok(Ast::MakeType(MakeType {
            span: sexpr.span(),
            pattern: VariantPattern(pattern.to_string()),
            body: match body.as_ref().map(|body| self.compile(body)) {
                Some(Ok(body)) => Some(std::boxed::Box::new(body)),
                Some(Err(e)) => return Err(e),
                None => None,
            },
        }))
    }

    fn compile_if_let(
        &mut self,
        sexpr: &Sexpr,
        body: &Sexpr,
        pattern: &Sexpr,
        then: &Sexpr,
        r#else: &Sexpr,
    ) -> Result<Ast, Error> {
        let (pattern, binding) = match pattern {
            Sexpr::List { list, .. } => match list.as_slice() {
                [Sexpr::Symbol {
                    symbol: pattern, ..
                }, Sexpr::Symbol {
                    symbol: binding, ..
                }] => (pattern.clone(), Some(binding.clone())),
                [Sexpr::Symbol {
                    symbol: pattern, ..
                }] => (pattern.clone(), None),
                _ => {
                    return Err(Error {
                        span: sexpr.span(),
                        message: "invalid deconstruction expression".to_string(),
                    })
                }
            },
            _ => {
                return Err(Error {
                    span: sexpr.span(),
                    message: "invalid if-let syntax".to_string(),
                })
            }
        };

        Ok(Ast::IfLet(IfLet {
            span: sexpr.span(),
            body: std::boxed::Box::new(self.compile(body)?),
            pattern: VariantPattern(pattern),
            binding,
            then: std::boxed::Box::new(self.compile(then)?),
            r#else: std::boxed::Box::new(self.compile(r#else)?),
        }))
    }

    fn compile_letrec(
        &mut self,
        sexpr: &Sexpr,
        bindings: &[Sexpr],
        body: &Sexpr,
    ) -> Result<Ast, Error> {
        Ok(Ast::LetRec(LetRec {
            span: sexpr.span(),
            bindings: bindings
                .iter()
                .map(|binding| {
                    Ok(
                        match binding.as_list().ok_or(Error {
                            span: sexpr.span(),
                            message: "expected list of bindings".to_string(),
                        })? {
                            [Sexpr::Symbol { symbol: name, .. }, expr] => {
                                (name.to_string(), self.compile(expr)?)
                            }
                            _ => {
                                return Err(Error {
                                    span: sexpr.span(),
                                    message: "failed to parse binding".to_string(),
                                })
                            }
                        },
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_defstruct(
        &mut self,
        sexpr: &Sexpr,
        struct_name: &str,
        fields: &[Sexpr],
    ) -> Result<Ast, Error> {
        let fields = fields
            .iter()
            .map(|sexpr| match sexpr {
                Sexpr::List { list, .. } => match list.as_slice() {
                    [Sexpr::Symbol { symbol: name, .. }, r#type] => Ok((
                        name.clone(),
                        Type::from_sexpr(r#type).map_err(|_| Error {
                            span: sexpr.span(),
                            message: "failed to parse type".to_string(),
                        })?,
                    )),
                    _ => Err(Error {
                        span: sexpr.span(),
                        message: "failed to parse struct field".to_string(),
                    }),
                },
                _ => Err(Error {
                    span: sexpr.span(),
                    message: "failed to parse struct".to_string(),
                }),
            })
            .collect::<Result<Vec<_>, _>>()?;

        let r#struct = Struct {
            name: struct_name.to_string(),
            fields: fields.iter().map(|(name, _)| name).cloned().collect(),
        };

        let constructor = format!("make-{}", struct_name);

        self.constructors
            .insert(StructConstructor(constructor), r#struct.clone());

        for (field_name, _) in &fields {
            let accessor = format!("{struct_name}-{field_name}");
            self.structs
                .insert(StructAccessor(accessor.clone()), r#struct.clone());
            self.fields.insert(
                StructAccessor(accessor.clone()),
                StructFieldName(field_name.clone()),
            );
        }

        Ok(Ast::DefStruct(DefStruct {
            span: sexpr.span(),
            name: struct_name.to_string(),
            fields,
        }))
    }

    fn compile_make_struct(
        &mut self,
        sexpr: &Sexpr,
        constructor: &str,
        exprs: &[Sexpr],
    ) -> Result<Ast, Error> {
        Ok(Ast::MakeStruct(MakeStruct {
            span: sexpr.span(),
            name: self.constructors[&StructConstructor(constructor.to_string())]
                .name
                .clone(),
            constructor: StructConstructor(constructor.to_string()),
            exprs: exprs
                .iter()
                .map(|expr| self.compile(expr))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_get_field(
        &mut self,
        sexpr: &Sexpr,
        accessor: &str,
        body: &Sexpr,
    ) -> Result<Ast, Error> {
        let r#struct = self.structs[&StructAccessor(accessor.to_string())].clone();
        Ok(Ast::GetField(GetField {
            span: sexpr.span(),
            struct_name: r#struct.name.clone(),
            field_name: self.fields[&StructAccessor(accessor.to_string())].0.clone(),
            accessor: StructAccessor(accessor.to_string()),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}", self.message)
    }
}

impl Ast {
    pub fn span(&self) -> FileSpan {
        match self {
            Self::Require(Require { span, .. })
            | Self::EvalWhenCompile(EvalWhenCompile { span, .. })
            | Self::DefMacro(DefMacro { span, .. })
            | Self::Lambda(Lambda { span, .. })
            | Self::Def(Def { span, .. })
            | Self::Decl(Decl { span, .. })
            | Self::Set(Set { span, .. })
            | Self::SetBox(SetBox { span, .. })
            | Self::Box(Box { span, .. })
            | Self::UnBox(UnBox { span, .. })
            | Self::If(If { span, .. })
            | Self::Apply(Apply { span, .. })
            | Self::BinaryArithemticOperation(BinaryArithmeticOperation { span, .. })
            | Self::ComparisonOperation(ComparisonOperation { span, .. })
            | Self::List(List { span, .. })
            | Self::Cons(Cons { span, .. })
            | Self::Car(Car { span, .. })
            | Self::Cdr(Cdr { span, .. })
            | Self::FnCall(FnCall { span, .. })
            | Self::MacroCall(MacroCall { span, .. })
            | Self::Quote(Quote { span, .. })
            | Self::IsType(IsType { span, .. })
            | Self::Assert(Assert { span, .. })
            | Self::MapCreate(MapCreate { span, .. })
            | Self::MapInsert(MapInsert { span, .. })
            | Self::MapRetrieve(MapRetrieve { span, .. })
            | Self::MapItems(MapItems { span, .. })
            | Self::GenSym(GenSym { span })
            | Self::LetType(LetType { span, .. })
            | Self::DefType(DefType { span, .. })
            | Self::MakeType(MakeType { span, .. })
            | Self::IfLet(IfLet { span, .. })
            | Self::LetRec(LetRec { span, .. })
            | Self::DefStruct(DefStruct { span, .. })
            | Self::MakeStruct(MakeStruct { span, .. })
            | Self::GetField(GetField { span, .. })
            | Self::Variable(Variable { span, .. })
            | Self::Constant(Constant::String { span, .. })
            | Self::Constant(Constant::Char { span, .. })
            | Self::Constant(Constant::Int { span, .. })
            | Self::Constant(Constant::Bool { span, .. })
            | Self::Constant(Constant::Nil { span }) => *span,
        }
    }
}

impl Type {
    #[allow(clippy::result_unit_err)]
    pub fn from_sexpr(sexpr: &Sexpr) -> Result<Self, ()> {
        Ok(match sexpr {
            Sexpr::List { list, .. } => Type::Composite(
                list.iter()
                    .map(Type::from_sexpr)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Sexpr::Symbol { symbol, .. } if symbol == "_" => Type::Inferred,
            Sexpr::Symbol { symbol, .. } => Type::Scalar(symbol.clone()),
            Sexpr::Nil { .. } => Type::Scalar("nil".to_string()),
            _ => return Err(()),
        })
    }
}

impl DefParameter {
    #[allow(clippy::result_unit_err)]
    pub fn from_sexpr(sexpr: &Sexpr) -> Result<Self, ()> {
        Ok(match sexpr {
            Sexpr::List { list, .. } => {
                if list.len() != 2 {
                    return Err(());
                }
                let name = list[0].as_symbol().ok_or(())?.to_string();
                let r#type = Type::from_sexpr(&list[1])?;
                DefParameter {
                    name,
                    r#type: Some(r#type),
                }
            }
            Sexpr::Symbol { symbol, .. } => DefParameter {
                name: symbol.clone(),
                r#type: None,
            },
            _ => return Err(()),
        })
    }
}

impl Parameters {
    pub fn len(&self) -> usize {
        match self {
            Parameters::Normal(params) => params.len(),
            Parameters::Rest(params, _) => params.len() + 1,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl error::Error for Error {
    fn span(&self) -> Option<error::FileSpan> {
        Some(self.span)
    }

    fn message(&self, writer: &mut dyn std::io::Write) {
        write!(writer, "{}", self.message).unwrap()
    }
}

fn parse_parameters(sexpr: &Sexpr, list: &[Sexpr]) -> Result<Parameters, Error> {
    let parameters = list
        .iter()
        .map(|sexpr| sexpr.as_symbol().map(|s| s.to_string()))
        .collect::<Option<Vec<_>>>()
        .ok_or(Error {
            span: sexpr.span(),
            message: "failed to parse parameter".to_string(),
        })?;

    let with_rest = micro_nom::map(
        micro_nom::separated(
            micro_nom::take_while::<&[String], _>(|parameter: &String| parameter != "&rest"),
            micro_nom::take_one_if::<&[String], _>(|parameter: &&String| {
                parameter.as_str() == "&rest"
            }),
            micro_nom::take_one,
        ),
        |(parameters, rest)| Parameters::Rest(parameters.to_vec(), rest.clone()),
    );

    let without_rest = micro_nom::map(
        micro_nom::take_while::<&[String], _>(|_| true),
        |parameters| Parameters::Normal(parameters.to_vec()),
    );

    let p = match micro_nom::branch(with_rest, without_rest)(parameters.as_slice()) {
        Ok((_, p)) => p,
        Err(_) => {
            return Err(Error {
                span: sexpr.span(),
                message: "failed to parse parameters".to_string(),
            })
        }
    };

    Ok(p)
}

fn quote(sexpr: &Sexpr, quoted: &Sexpr) -> Quoted {
    match quoted {
        Sexpr::List { list, .. } => quote_list(sexpr, list.as_slice()),
        Sexpr::Symbol { symbol, .. } => Quoted::Symbol {
            span: sexpr.span(),
            symbol: symbol.clone(),
        },
        Sexpr::String { string, .. } => Quoted::String {
            span: sexpr.span(),
            string: string.clone(),
        },
        Sexpr::Char { char, .. } => Quoted::Char {
            span: sexpr.span(),
            char: *char,
        },
        Sexpr::Int { int, .. } => Quoted::Int {
            span: sexpr.span(),
            int: *int,
        },
        Sexpr::Bool { bool, .. } => Quoted::Bool {
            span: sexpr.span(),
            bool: *bool,
        },
        Sexpr::Nil { .. } => Quoted::Nil { span: sexpr.span() },
    }
}

fn quote_list(sexpr: &Sexpr, list: &[Sexpr]) -> Quoted {
    Quoted::List {
        span: sexpr.span(),
        list: list
            .iter()
            .map(|sexpr| match sexpr {
                Sexpr::List { list, .. } => quote_list(sexpr, list.as_slice()),
                Sexpr::Symbol { symbol, .. } => Quoted::Symbol {
                    span: sexpr.span(),
                    symbol: symbol.clone(),
                },
                Sexpr::String { string, .. } => Quoted::String {
                    span: sexpr.span(),
                    string: string.clone(),
                },
                Sexpr::Char { char, .. } => Quoted::Char {
                    span: sexpr.span(),
                    char: *char,
                },
                Sexpr::Int { int, .. } => Quoted::Int {
                    span: sexpr.span(),
                    int: *int,
                },
                Sexpr::Bool { bool, .. } => Quoted::Bool {
                    span: sexpr.span(),
                    bool: *bool,
                },
                Sexpr::Nil { .. } => Quoted::Nil { span: sexpr.span() },
            })
            .collect(),
    }
}

fn parse_variant(sexpr: &Sexpr) -> Result<Variant, ()> {
    let Sexpr::List { list, .. } = sexpr else {
        return Err(());
    };

    match list.as_slice() {
        [Sexpr::Symbol { symbol: name, .. }, r#type] => Ok(Variant {
            name: name.clone(),
            r#type: Some(Type::from_sexpr(r#type)?),
        }),
        [Sexpr::Symbol { symbol: name, .. }] => Ok(Variant {
            name: name.clone(),
            r#type: None,
        }),
        _ => Err(()),
    }
}

fn parse_let(sexpr: &Sexpr) -> Result<Vec<(String, Sexpr)>, ()> {
    let bindings = match sexpr {
        Sexpr::List { list, .. } => match list.as_slice() {
            [_, Sexpr::List { list: bindings, .. }, _] => bindings,
            _ => return Err(()),
        },
        _ => return Err(()),
    };

    bindings
        .iter()
        .map(|binding| {
            Ok(match binding {
                Sexpr::List { list, .. } => match list.as_slice() {
                    [Sexpr::Symbol { symbol: name, .. }, expr] => (name.to_string(), expr.clone()),
                    _ => return Err(()),
                },
                _ => return Err(()),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {

    use reader::Reader;

    use super::*;

    #[test]
    fn test_parse_parameters() {
        let input = "(a b &rest c)";
        let mut reader = Reader::new(input, 0);
        let sexpr = std::boxed::Box::leak(std::boxed::Box::new(reader.next().unwrap().unwrap()));
        let list = sexpr.as_list().unwrap();
        let parameters = parse_parameters(sexpr, list).unwrap();

        match parameters {
            Parameters::Rest(..) => (),
            _ => panic!(),
        };
    }

    #[test]
    fn test_parse_only_rest_parameters() {
        let input = "(&rest c)";
        let mut reader = Reader::new(input, 0);
        let sexpr = std::boxed::Box::leak(std::boxed::Box::new(reader.next().unwrap().unwrap()));
        let list = sexpr.as_list().unwrap();
        let parameters = parse_parameters(sexpr, list).unwrap();

        match parameters {
            Parameters::Rest(params, _) if params.is_empty() => (),
            _ => panic!(),
        };
    }
}
