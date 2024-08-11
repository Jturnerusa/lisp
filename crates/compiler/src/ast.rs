use core::fmt;
use std::collections::HashSet;

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
];

#[derive(Clone, Debug, thiserror::Error)]
pub struct Error {
    sexpr: &'static Sexpr<'static>,
    message: String,
}

#[derive(Clone, Debug)]
pub struct Compiler {
    macros: HashSet<String>,
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
}

#[derive(Clone, Debug)]
pub struct EvalWhenCompile {
    pub source: &'static Sexpr<'static>,
    pub exprs: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub source: &'static Sexpr<'static>,
    pub name: String,
}

#[derive(Clone, Debug)]
pub enum Constant {
    String {
        source: &'static Sexpr<'static>,
        string: String,
    },
    Char {
        source: &'static Sexpr<'static>,
        char: char,
    },
    Int {
        source: &'static Sexpr<'static>,
        int: i64,
    },
    Bool {
        source: &'static Sexpr<'static>,
        bool: bool,
    },
    Nil {
        source: &'static Sexpr<'static>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Scalar(String),
    Composite(Vec<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parameter {
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters {
    Normal(Vec<Parameter>),
    Rest(Vec<Parameter>, Parameter),
}

#[derive(Clone, Debug)]
pub struct Require {
    pub source: &'static Sexpr<'static>,
    pub module: String,
}

#[derive(Clone, Debug)]
pub struct DefMacro {
    pub source: &'static Sexpr<'static>,
    pub name: String,
    pub parameters: Parameters,
    pub body: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Lambda {
    pub source: &'static Sexpr<'static>,
    pub r#type: Option<Type>,
    pub parameters: Parameters,
    pub body: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Def {
    pub source: &'static Sexpr<'static>,
    pub parameter: Parameter,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub source: &'static Sexpr<'static>,
    pub parameter: Parameter,
}

#[derive(Clone, Debug)]
pub struct Set {
    pub source: &'static Sexpr<'static>,
    pub target: String,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct SetBox {
    pub source: &'static Sexpr<'static>,
    pub target: std::boxed::Box<Ast>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct UnBox {
    pub source: &'static Sexpr<'static>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Box {
    pub source: &'static Sexpr<'static>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct If {
    pub source: &'static Sexpr<'static>,
    pub predicate: std::boxed::Box<Ast>,
    pub then: std::boxed::Box<Ast>,
    pub r#else: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Apply {
    pub source: &'static Sexpr<'static>,
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
    pub source: &'static Sexpr<'static>,
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
    pub source: &'static Sexpr<'static>,
    pub operator: ComparisonOperator,
    pub lhs: std::boxed::Box<Ast>,
    pub rhs: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct List {
    pub source: &'static Sexpr<'static>,
    pub exprs: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct Cons {
    pub source: &'static Sexpr<'static>,
    pub lhs: std::boxed::Box<Ast>,
    pub rhs: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Car {
    pub source: &'static Sexpr<'static>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Cdr {
    pub source: &'static Sexpr<'static>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct FnCall {
    pub source: &'static Sexpr<'static>,
    pub function: std::boxed::Box<Ast>,
    pub exprs: Vec<Ast>,
}

#[derive(Clone, Debug)]
pub struct MacroCall {
    pub source: &'static Sexpr<'static>,
    pub r#macro: String,
    pub args: Vec<Quoted>,
}

#[derive(Clone, Debug)]
pub struct Quote {
    pub source: &'static Sexpr<'static>,
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
    pub source: &'static Sexpr<'static>,
    pub parameter: IsTypeParameter,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct Assert {
    pub source: &'static Sexpr<'static>,
    pub body: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct MapCreate {
    pub source: &'static Sexpr<'static>,
}

#[derive(Clone, Debug)]
pub struct MapInsert {
    pub source: &'static Sexpr<'static>,
    pub map: std::boxed::Box<Ast>,
    pub key: std::boxed::Box<Ast>,
    pub value: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve {
    pub source: &'static Sexpr<'static>,
    pub map: std::boxed::Box<Ast>,
    pub key: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub struct MapItems {
    pub source: &'static Sexpr<'static>,
    pub map: std::boxed::Box<Ast>,
}

#[derive(Clone, Debug)]
pub enum Quoted {
    List {
        source: &'static Sexpr<'static>,
        list: Vec<Quoted>,
    },
    Symbol {
        source: &'static Sexpr<'static>,
        symbol: String,
    },
    String {
        source: &'static Sexpr<'static>,
        string: String,
    },
    Char {
        source: &'static Sexpr<'static>,
        char: char,
    },
    Int {
        source: &'static Sexpr<'static>,
        int: i64,
    },
    Bool {
        source: &'static Sexpr<'static>,
        bool: bool,
    },
    Nil {
        source: &'static Sexpr<'static>,
    },
}

#[derive(Clone, Debug)]
pub struct GenSym {
    pub source: &'static Sexpr<'static>,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            macros: HashSet::new(),
        }
    }

    pub fn compile(&mut self, sexpr: &'static Sexpr<'static>) -> Result<Ast, Error> {
        use Sexpr::*;
        Ok(match sexpr {
            Sexpr::List { list, .. }
                if list
                    .first()
                    .and_then(|first| first.as_symbol())
                    .is_some_and(|symbol| BUILT_INS.iter().any(|b| symbol == *b)) =>
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
                        Ast::MapCreate(MapCreate { source: sexpr })
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
                        Ast::GenSym(GenSym { source: sexpr })
                    }
                    _ => {
                        return Err(Error {
                            sexpr,
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
                source: sexpr,
                name: symbol.clone(),
            }),
            String { string, .. } => Ast::Constant(Constant::String {
                source: sexpr,
                string: string.clone(),
            }),
            Char { char, .. } => Ast::Constant(Constant::Char {
                source: sexpr,
                char: *char,
            }),
            Int { int, .. } => Ast::Constant(Constant::Int {
                source: sexpr,
                int: *int,
            }),
            Bool { bool, .. } => Ast::Constant(Constant::Bool {
                source: sexpr,
                bool: *bool,
            }),
            Nil { .. } => Ast::Constant(Constant::Nil { source: sexpr }),
            _ => unreachable!(),
        })
    }

    fn compile_require(
        &mut self,
        source: &'static Sexpr<'static>,
        module: &str,
    ) -> Result<Ast, Error> {
        Ok(Ast::Require(Require {
            source,
            module: module.to_string(),
        }))
    }

    fn compile_eval_when_compile(
        &mut self,
        source: &'static Sexpr<'static>,
        args: &'static [Sexpr<'static>],
    ) -> Result<Ast, Error> {
        Ok(Ast::EvalWhenCompile(EvalWhenCompile {
            source,
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_defmacro(
        &mut self,
        source: &'static Sexpr<'static>,
        name: &str,
        parameters: &'static Sexpr<'static>,
        rest: &'static [Sexpr<'static>],
    ) -> Result<Ast, Error> {
        self.macros.insert(name.to_string());

        Ok(Ast::DefMacro(DefMacro {
            source,
            name: name.to_string(),
            parameters: match parameters {
                Sexpr::List { list, .. } => {
                    parse_parameters(source, list.as_slice()).map_err(|_| Error {
                        sexpr: source,
                        message: "failed to parse parameters".to_string(),
                    })?
                }
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        sexpr: source,
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
        source: &'static Sexpr<'static>,
        parameters: &'static Sexpr<'static>,
        r#type: Option<&'static Sexpr<'static>>,
        rest: &'static [Sexpr<'static>],
    ) -> Result<Ast, Error> {
        Ok(Ast::Lambda(Lambda {
            source,
            r#type: match r#type.map(Type::from_sexpr) {
                Some(Ok(t)) => Some(t),
                Some(Err(_)) => {
                    return Err(Error {
                        sexpr: source,
                        message: "failed to parse type".to_string(),
                    })
                }
                None => None,
            },
            parameters: match parameters {
                Sexpr::List { list, .. } => {
                    parse_parameters(source, list.as_slice()).map_err(|_| Error {
                        sexpr: source,
                        message: "failed to parse parameters".to_string(),
                    })?
                }
                Sexpr::Nil { .. } => Parameters::Normal(Vec::new()),
                _ => {
                    return Err(Error {
                        sexpr: source,
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
        source: &'static Sexpr<'static>,
        parameter: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Def(Def {
            source,
            parameter: Parameter::from_sexpr(parameter).map_err(|_| Error {
                sexpr: source,
                message: "failed to parse parameter".to_string(),
            })?,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_decl(
        &mut self,
        source: &'static Sexpr<'static>,
        parameter: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Decl(Decl {
            source,
            parameter: Parameter::from_sexpr(parameter).map_err(|_| Error {
                sexpr: source,
                message: "failed to parse parameter".to_string(),
            })?,
        }))
    }

    fn compile_set(
        &mut self,
        source: &'static Sexpr<'static>,
        target: &str,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Set(Set {
            source,
            target: target.to_string(),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_set_box(
        &mut self,
        source: &'static Sexpr<'static>,
        target: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::SetBox(SetBox {
            source,
            target: std::boxed::Box::new(self.compile(target)?),
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_box(
        &mut self,
        source: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Box(Box {
            source,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_unbox(
        &mut self,
        source: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::UnBox(UnBox {
            source,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_if(
        &mut self,
        source: &'static Sexpr<'static>,
        predicate: &'static Sexpr<'static>,
        then: &'static Sexpr<'static>,
        r#else: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::If(If {
            source,
            predicate: std::boxed::Box::new(self.compile(predicate)?),
            then: std::boxed::Box::new(self.compile(then)?),
            r#else: std::boxed::Box::new(self.compile(r#else)?),
        }))
    }

    fn compile_apply(
        &mut self,
        source: &'static Sexpr<'static>,
        function: &'static Sexpr<'static>,
        list: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Apply(Apply {
            source,
            function: std::boxed::Box::new(self.compile(function)?),
            list: std::boxed::Box::new(self.compile(list)?),
        }))
    }

    fn compile_binary_arithmetic_op(
        &mut self,
        source: &'static Sexpr<'static>,
        operator: &str,
        lhs: &'static Sexpr<'static>,
        rhs: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::BinaryArithemticOperation(BinaryArithmeticOperation {
            source,
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
        source: &'static Sexpr<'static>,
        operator: &str,
        lhs: &'static Sexpr<'static>,
        rhs: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::ComparisonOperation(ComparisonOperation {
            source,
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

    fn compile_list(
        &mut self,
        source: &'static Sexpr<'static>,
        args: &'static [Sexpr<'static>],
    ) -> Result<Ast, Error> {
        Ok(Ast::List(List {
            source,
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_cons(
        &mut self,
        source: &'static Sexpr<'static>,
        lhs: &'static Sexpr<'static>,
        rhs: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Cons(Cons {
            source,
            lhs: std::boxed::Box::new(self.compile(lhs)?),
            rhs: std::boxed::Box::new(self.compile(rhs)?),
        }))
    }

    fn compile_car(
        &mut self,
        source: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Car(Car {
            source,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_cdr(
        &mut self,
        source: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Cdr(Cdr {
            source,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_fncall(
        &mut self,
        source: &'static Sexpr<'static>,
        function: &'static Sexpr<'static>,
        args: &'static [Sexpr<'static>],
    ) -> Result<Ast, Error> {
        Ok(Ast::FnCall(FnCall {
            source,
            function: std::boxed::Box::new(self.compile(function)?),
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_macro_call(
        &mut self,
        source: &'static Sexpr<'static>,
        r#macro: &str,
        args: &'static [Sexpr<'static>],
    ) -> Result<Ast, Error> {
        Ok(Ast::MacroCall(MacroCall {
            source,
            r#macro: r#macro.to_string(),
            args: args.iter().map(|arg| quote(source, arg)).collect(),
        }))
    }

    fn compile_quote(
        &mut self,
        source: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Quote(Quote {
            source,
            body: quote(source, body),
        }))
    }

    fn compile_is_type(
        &mut self,
        source: &'static Sexpr<'static>,
        parameter: &str,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::IsType(IsType {
            source,
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

    fn compile_assert(
        &mut self,
        source: &'static Sexpr<'static>,
        body: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::Assert(Assert {
            source,
            body: std::boxed::Box::new(self.compile(body)?),
        }))
    }

    fn compile_map_insert(
        &mut self,
        source: &'static Sexpr<'static>,
        map: &'static Sexpr<'static>,
        key: &'static Sexpr<'static>,
        value: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::MapInsert(MapInsert {
            source,
            map: std::boxed::Box::new(self.compile(map)?),
            key: std::boxed::Box::new(self.compile(key)?),
            value: std::boxed::Box::new(self.compile(value)?),
        }))
    }

    fn compile_map_retrieve(
        &mut self,
        source: &'static Sexpr<'static>,
        map: &'static Sexpr<'static>,
        key: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::MapRetrieve(MapRetrieve {
            source,
            map: std::boxed::Box::new(self.compile(map)?),
            key: std::boxed::Box::new(self.compile(key)?),
        }))
    }

    fn compile_map_items(
        &mut self,
        source: &'static Sexpr<'static>,
        map: &'static Sexpr<'static>,
    ) -> Result<Ast, Error> {
        Ok(Ast::MapItems(MapItems {
            source,
            map: std::boxed::Box::new(self.compile(map)?),
        }))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\n{}", self.message, self.sexpr)
    }
}

impl Ast {
    pub fn source_sexpr(&self) -> &'static Sexpr<'static> {
        match self {
            Self::Require(Require { source, .. })
            | Self::EvalWhenCompile(EvalWhenCompile { source, .. })
            | Self::DefMacro(DefMacro { source, .. })
            | Self::Lambda(Lambda { source, .. })
            | Self::Def(Def { source, .. })
            | Self::Decl(Decl { source, .. })
            | Self::Set(Set { source, .. })
            | Self::SetBox(SetBox { source, .. })
            | Self::Box(Box { source, .. })
            | Self::UnBox(UnBox { source, .. })
            | Self::If(If { source, .. })
            | Self::Apply(Apply { source, .. })
            | Self::BinaryArithemticOperation(BinaryArithmeticOperation { source, .. })
            | Self::ComparisonOperation(ComparisonOperation { source, .. })
            | Self::List(List { source, .. })
            | Self::Cons(Cons { source, .. })
            | Self::Car(Car { source, .. })
            | Self::Cdr(Cdr { source, .. })
            | Self::FnCall(FnCall { source, .. })
            | Self::MacroCall(MacroCall { source, .. })
            | Self::Quote(Quote { source, .. })
            | Self::IsType(IsType { source, .. })
            | Self::Assert(Assert { source, .. })
            | Self::MapCreate(MapCreate { source, .. })
            | Self::MapInsert(MapInsert { source, .. })
            | Self::MapRetrieve(MapRetrieve { source, .. })
            | Self::MapItems(MapItems { source, .. })
            | Self::GenSym(GenSym { source })
            | Self::Variable(Variable { source, .. })
            | Self::Constant(Constant::String { source, .. })
            | Self::Constant(Constant::Char { source, .. })
            | Self::Constant(Constant::Int { source, .. })
            | Self::Constant(Constant::Bool { source, .. })
            | Self::Constant(Constant::Nil { source }) => source,
        }
    }
}

impl Type {
    pub fn from_sexpr(sexpr: &Sexpr) -> Result<Self, ()> {
        Ok(match sexpr {
            Sexpr::List { list, .. } => Type::Composite(
                list.iter()
                    .map(Type::from_sexpr)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Sexpr::Symbol { symbol, .. } => Type::Scalar(symbol.clone()),
            Sexpr::Nil { .. } => Type::Scalar("nil".to_string()),
            _ => return Err(()),
        })
    }
}

impl Parameter {
    pub fn from_sexpr(sexpr: &Sexpr) -> Result<Self, ()> {
        Ok(match sexpr {
            Sexpr::List { list, .. } => {
                if list.len() != 2 {
                    return Err(());
                }
                let name = list[0].as_symbol().ok_or(())?.to_string();
                let r#type = Type::from_sexpr(&list[1])?;
                Parameter {
                    name,
                    r#type: Some(r#type),
                }
            }
            Sexpr::Symbol { symbol, .. } => Parameter {
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
}

fn parse_parameters(
    source: &'static Sexpr<'static>,
    list: &'static [Sexpr<'static>],
) -> Result<Parameters, Error> {
    let parameters = list
        .iter()
        .map(Parameter::from_sexpr)
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| Error {
            sexpr: source,
            message: "failed to parse parameter".to_string(),
        })?;

    let with_rest = micro_nom::map(
        micro_nom::separated(
            micro_nom::take_while::<&[Parameter], _>(|parameter: &Parameter| {
                parameter.name != "&rest"
            }),
            micro_nom::take_one_if::<&[Parameter], _>(|parameter: &&Parameter| {
                parameter.name == "&rest"
            }),
            micro_nom::take_one,
        ),
        |(parameters, rest)| Parameters::Rest(parameters.to_vec(), rest.clone()),
    );

    let without_rest = micro_nom::map(
        micro_nom::take_while::<&[Parameter], _>(|_| true),
        |parameters| Parameters::Normal(parameters.to_vec()),
    );

    let p = match micro_nom::branch(with_rest, without_rest)(parameters.as_slice()) {
        Ok((_, p)) => p,
        Err(_) => {
            return Err(Error {
                sexpr: source,
                message: "failed to parse parameters".to_string(),
            })
        }
    };

    Ok(p)
}

fn quote(source: &'static Sexpr<'static>, sexpr: &'static Sexpr<'static>) -> Quoted {
    match sexpr {
        Sexpr::List { list, .. } => quote_list(source, list.as_slice()),
        Sexpr::Symbol { symbol, .. } => Quoted::Symbol {
            source,
            symbol: symbol.clone(),
        },
        Sexpr::String { string, .. } => Quoted::String {
            source,
            string: string.clone(),
        },
        Sexpr::Char { char, .. } => Quoted::Char {
            source,
            char: *char,
        },
        Sexpr::Int { int, .. } => Quoted::Int { source, int: *int },
        Sexpr::Bool { bool, .. } => Quoted::Bool {
            source,
            bool: *bool,
        },
        Sexpr::Nil { .. } => Quoted::Nil { source },
    }
}

fn quote_list(source: &'static Sexpr<'static>, list: &'static [Sexpr<'static>]) -> Quoted {
    Quoted::List {
        source,
        list: list
            .iter()
            .map(|sexpr| match sexpr {
                Sexpr::List { list, .. } => quote_list(source, list.as_slice()),
                Sexpr::Symbol { symbol, .. } => Quoted::Symbol {
                    source,
                    symbol: symbol.clone(),
                },
                Sexpr::String { string, .. } => Quoted::String {
                    source,
                    string: string.clone(),
                },
                Sexpr::Char { char, .. } => Quoted::Char {
                    source,
                    char: *char,
                },
                Sexpr::Int { int, .. } => Quoted::Int { source, int: *int },
                Sexpr::Bool { bool, .. } => Quoted::Bool {
                    source,
                    bool: *bool,
                },
                Sexpr::Nil { .. } => Quoted::Nil { source },
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {

    use reader::Reader;

    use super::*;

    #[test]
    fn test_parse_parameters() {
        let input = "(a b &rest c)";
        let context = std::boxed::Box::leak(std::boxed::Box::new(reader::Context::new(
            input,
            "test_parse_parameters",
        )));
        let mut reader = Reader::new(context);
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
        let context = std::boxed::Box::leak(std::boxed::Box::new(reader::Context::new(
            input,
            "test_parse_parameters",
        )));
        let mut reader = Reader::new(context);
        let sexpr = std::boxed::Box::leak(std::boxed::Box::new(reader.next().unwrap().unwrap()));
        let list = sexpr.as_list().unwrap();
        let parameters = parse_parameters(sexpr, list).unwrap();

        match parameters {
            Parameters::Rest(params, _) if params.is_empty() => (),
            _ => panic!(),
        };
    }
}
