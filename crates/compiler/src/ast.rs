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
];

#[derive(Clone, Debug, thiserror::Error)]
pub struct Error<'sexpr, 'context> {
    sexpr: &'sexpr Sexpr<'context>,
    message: String,
}

#[derive(Clone, Debug)]
pub struct Compiler {
    macros: HashSet<String>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum Ast<'sexpr, 'context> {
    EvalWhenCompile(EvalWhenCompile<'sexpr, 'context>),
    DefMacro(DefMacro<'sexpr, 'context>),
    Lambda(Lambda<'sexpr, 'context>),
    Def(Def<'sexpr, 'context>),
    Decl(Decl<'sexpr, 'context>),
    Set(Set<'sexpr, 'context>),
    If(If<'sexpr, 'context>),
    Apply(Apply<'sexpr, 'context>),
    BinaryArithemticOperation(BinaryArithmeticOperation<'sexpr, 'context>),
    ComparisonOperation(ComparisonOperation<'sexpr, 'context>),
    List(List<'sexpr, 'context>),
    Cons(Cons<'sexpr, 'context>),
    Car(Car<'sexpr, 'context>),
    Cdr(Cdr<'sexpr, 'context>),
    FnCall(FnCall<'sexpr, 'context>),
    MacroCall(MacroCall<'sexpr, 'context>),
    Quote(Quote<'sexpr, 'context>),
    IsType(IsType<'sexpr, 'context>),
    MapCreate(MapCreate<'sexpr, 'context>),
    MapInsert(MapInsert<'sexpr, 'context>),
    MapRetrieve(MapRetrieve<'sexpr, 'context>),
    MapItems(MapItems<'sexpr, 'context>),
    Variable(Variable<'sexpr, 'context>),
    Constant(Constant<'sexpr, 'context>),
    Assert(Assert<'sexpr, 'context>),
}

#[derive(Clone, Debug)]
pub struct EvalWhenCompile<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub enum Constant<'sexpr, 'context> {
    String {
        source: &'sexpr Sexpr<'context>,
        string: String,
    },
    Char {
        source: &'sexpr Sexpr<'context>,
        char: char,
    },
    Int {
        source: &'sexpr Sexpr<'context>,
        int: i64,
    },
    Bool {
        source: &'sexpr Sexpr<'context>,
        bool: bool,
    },
    Nil {
        source: &'sexpr Sexpr<'context>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Scalar(String),
    Composite(Vec<Type>),
}

#[derive(Clone, Debug)]
pub struct Variable<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub name: String,
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
pub struct DefMacro<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub name: String,
    pub parameters: Parameters,
    pub body: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Lambda<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub r#type: Option<Type>,
    pub parameters: Parameters,
    pub body: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Def<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub parameter: Parameter,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Decl<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub parameter: Parameter,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Set<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub variable: String,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct If<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub predicate: Box<Ast<'sexpr, 'context>>,
    pub then: Box<Ast<'sexpr, 'context>>,
    pub r#else: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Apply<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub enum BinaryArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct BinaryArithmeticOperation<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub operator: BinaryArithmeticOperator,
    pub lhs: Box<Ast<'sexpr, 'context>>,
    pub rhs: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum ComparisonOperator {
    Lt,
    Gt,
    Eq,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub operator: ComparisonOperator,
    pub lhs: Box<Ast<'sexpr, 'context>>,
    pub rhs: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct List<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Cons<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub lhs: Box<Ast<'sexpr, 'context>>,
    pub rhs: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Car<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Cdr<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct FnCall<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub function: Box<Ast<'sexpr, 'context>>,
    pub exprs: Vec<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct MacroCall<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub r#macro: String,
    pub args: Vec<Quoted<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Quote<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub body: Quoted<'sexpr, 'context>,
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
pub struct IsType<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub parameter: IsTypeParameter,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct Assert<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub body: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct MapCreate<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
}

#[derive(Clone, Debug)]
pub struct MapInsert<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub map: Box<Ast<'sexpr, 'context>>,
    pub key: Box<Ast<'sexpr, 'context>>,
    pub value: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub map: Box<Ast<'sexpr, 'context>>,
    pub key: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub struct MapItems<'sexpr, 'context> {
    pub source: &'sexpr Sexpr<'context>,
    pub map: Box<Ast<'sexpr, 'context>>,
}

#[derive(Clone, Debug)]
pub enum Quoted<'sexpr, 'context> {
    List {
        source: &'sexpr Sexpr<'context>,
        list: Vec<Quoted<'sexpr, 'context>>,
    },
    Symbol {
        source: &'sexpr Sexpr<'context>,
        symbol: String,
    },
    String {
        source: &'sexpr Sexpr<'context>,
        string: String,
    },
    Char {
        source: &'sexpr Sexpr<'context>,
        char: char,
    },
    Int {
        source: &'sexpr Sexpr<'context>,
        int: i64,
    },
    Bool {
        source: &'sexpr Sexpr<'context>,
        bool: bool,
    },
    Nil {
        source: &'sexpr Sexpr<'context>,
    },
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            macros: HashSet::new(),
        }
    }

    pub fn compile<'sexpr, 'context>(
        &mut self,
        sexpr: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        use Sexpr::*;
        Ok(match sexpr {
            Sexpr::List { list, .. }
                if list
                    .first()
                    .and_then(|first| first.as_symbol())
                    .is_some_and(|symbol| BUILT_INS.iter().any(|b| symbol == *b)) =>
            {
                match list.as_slice() {
                    [Symbol { symbol, .. }, rest @ ..] if symbol == "eval-when-compile" => {
                        self.compile_eval_when_compile(sexpr, rest)?
                    }
                    [Symbol { symbol, .. }, Symbol { symbol: name, .. }, parameters, rest @ ..]
                        if symbol == "defmacro" =>
                    {
                        self.compile_defmacro(sexpr, name, parameters, rest)?
                    }
                    [Symbol { symbol, .. }, parameters, _, Symbol { symbol: arrow, .. }, r#type, rest @ ..]
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
                    [Symbol { symbol, .. }, parameter, body] if symbol == "decl" => {
                        self.compile_decl(sexpr, parameter, body)?
                    }
                    [Symbol { symbol, .. }, parameter, body] if symbol == "set!" => {
                        self.compile_set(sexpr, parameter, body)?
                    }
                    [Symbol { symbol, .. }, predicate, then, r#else] if symbol == "if" => {
                        self.compile_if(sexpr, predicate, then, r#else)?
                    }
                    [Symbol { symbol, .. }, rest @ ..] if symbol == "apply" => {
                        self.compile_apply(sexpr, rest)?
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
                name: symbol.to_string(),
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

    fn compile_eval_when_compile<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        args: &'sexpr [Sexpr<'context>],
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::EvalWhenCompile(EvalWhenCompile {
            source,
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_defmacro<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        name: &str,
        parameters: &'sexpr Sexpr<'context>,
        rest: &'sexpr [Sexpr<'context>],
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
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

    fn compile_lambda<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        parameters: &'sexpr Sexpr<'context>,
        r#type: Option<&'sexpr Sexpr<'context>>,
        rest: &'sexpr [Sexpr<'context>],
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
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

    fn compile_def<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        parameter: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Def(Def {
            source,
            parameter: Parameter::from_sexpr(parameter).map_err(|_| Error {
                sexpr: source,
                message: "failed to parse parameter".to_string(),
            })?,
            body: Box::new(self.compile(body)?),
        }))
    }

    fn compile_decl<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        parameter: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Decl(Decl {
            source,
            parameter: Parameter::from_sexpr(parameter).map_err(|_| Error {
                sexpr: source,
                message: "failed to parse parameter".to_string(),
            })?,
            body: Box::new(self.compile(body)?),
        }))
    }

    fn compile_set<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        parameter: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Set(Set {
            source,
            variable: parameter.as_symbol().map(|s| s.to_string()).ok_or(Error {
                sexpr: source,
                message: "expectes symbol as parameter".to_string(),
            })?,
            body: Box::new(self.compile(body)?),
        }))
    }

    fn compile_if<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        predicate: &'sexpr Sexpr<'context>,
        then: &'sexpr Sexpr<'context>,
        r#else: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::If(If {
            source,
            predicate: Box::new(self.compile(predicate)?),
            then: Box::new(self.compile(then)?),
            r#else: Box::new(self.compile(r#else)?),
        }))
    }

    fn compile_apply<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        args: &'sexpr [Sexpr<'context>],
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Apply(Apply {
            source,
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_binary_arithmetic_op<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        operator: &str,
        lhs: &'sexpr Sexpr<'context>,
        rhs: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::BinaryArithemticOperation(BinaryArithmeticOperation {
            source,
            operator: match operator {
                "+" => BinaryArithmeticOperator::Add,
                "-" => BinaryArithmeticOperator::Sub,
                "*" => BinaryArithmeticOperator::Mul,
                "/" => BinaryArithmeticOperator::Div,
                _ => unreachable!(),
            },
            lhs: Box::new(self.compile(lhs)?),
            rhs: Box::new(self.compile(rhs)?),
        }))
    }

    fn compile_comparison_op<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        operator: &str,
        lhs: &'sexpr Sexpr<'context>,
        rhs: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::ComparisonOperation(ComparisonOperation {
            source,
            operator: match operator {
                "=" => ComparisonOperator::Eq,
                "<" => ComparisonOperator::Lt,
                ">" => ComparisonOperator::Gt,
                _ => unreachable!(),
            },
            lhs: Box::new(self.compile(lhs)?),
            rhs: Box::new(self.compile(rhs)?),
        }))
    }

    fn compile_list<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        args: &'sexpr [Sexpr<'context>],
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::List(List {
            source,
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_cons<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        lhs: &'sexpr Sexpr<'context>,
        rhs: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Cons(Cons {
            source,
            lhs: Box::new(self.compile(lhs)?),
            rhs: Box::new(self.compile(rhs)?),
        }))
    }

    fn compile_car<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Car(Car {
            source,
            body: Box::new(self.compile(body)?),
        }))
    }

    fn compile_cdr<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Cdr(Cdr {
            source,
            body: Box::new(self.compile(body)?),
        }))
    }

    fn compile_fncall<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        function: &'sexpr Sexpr<'context>,
        args: &'sexpr [Sexpr<'context>],
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::FnCall(FnCall {
            source,
            function: Box::new(self.compile(function)?),
            exprs: args
                .iter()
                .map(|arg| self.compile(arg))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_macro_call<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        r#macro: &str,
        args: &'sexpr [Sexpr<'context>],
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::MacroCall(MacroCall {
            source,
            r#macro: r#macro.to_string(),
            args: args.iter().map(|arg| quote(source, arg)).collect(),
        }))
    }

    fn compile_quote<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Quote(Quote {
            source,
            body: quote(source, body),
        }))
    }

    fn compile_is_type<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        parameter: &str,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
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
            body: Box::new(self.compile(body)?),
        }))
    }

    fn compile_assert<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        body: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::Assert(Assert {
            source,
            body: Box::new(self.compile(body)?),
        }))
    }

    fn compile_map_insert<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        map: &'sexpr Sexpr<'context>,
        key: &'sexpr Sexpr<'context>,
        value: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::MapInsert(MapInsert {
            source,
            map: Box::new(self.compile(map)?),
            key: Box::new(self.compile(key)?),
            value: Box::new(self.compile(value)?),
        }))
    }

    fn compile_map_retrieve<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        map: &'sexpr Sexpr<'context>,
        key: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::MapRetrieve(MapRetrieve {
            source,
            map: Box::new(self.compile(map)?),
            key: Box::new(self.compile(key)?),
        }))
    }

    fn compile_map_items<'sexpr, 'context>(
        &mut self,
        source: &'sexpr Sexpr<'context>,
        map: &'sexpr Sexpr<'context>,
    ) -> Result<Ast<'sexpr, 'context>, Error<'sexpr, 'context>> {
        Ok(Ast::MapItems(MapItems {
            source,
            map: Box::new(self.compile(map)?),
        }))
    }
}

impl<'sexpr, 'context> fmt::Display for Error<'sexpr, 'context> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\n{}", self.message, self.sexpr)
    }
}

impl<'sexpr, 'context> Ast<'sexpr, 'context> {
    pub fn source_sexpr(&self) -> &'sexpr Sexpr<'context> {
        match self {
            Self::EvalWhenCompile(EvalWhenCompile { source, .. })
            | Self::DefMacro(DefMacro { source, .. })
            | Self::Lambda(Lambda { source, .. })
            | Self::Def(Def { source, .. })
            | Self::Decl(Decl { source, .. })
            | Self::Set(Set { source, .. })
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

fn parse_parameters<'sexpr, 'context>(
    source: &'sexpr Sexpr<'context>,
    list: &'sexpr [Sexpr<'context>],
) -> Result<Parameters, Error<'sexpr, 'context>> {
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

fn quote<'sexpr, 'context>(
    source: &'sexpr Sexpr<'context>,
    sexpr: &'sexpr Sexpr<'context>,
) -> Quoted<'sexpr, 'context> {
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

fn quote_list<'sexpr, 'context>(
    source: &'sexpr Sexpr<'context>,
    list: &'sexpr [Sexpr<'context>],
) -> Quoted<'sexpr, 'context> {
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
        let context = reader::Context::new(input, "test_parse_parameters");
        let mut reader = Reader::new(&context);
        let sexpr = reader.next().unwrap().unwrap();
        let list = sexpr.as_list().unwrap();
        let parameters = parse_parameters(&sexpr, list).unwrap();

        match parameters {
            Parameters::Rest(..) => (),
            _ => panic!(),
        };
    }

    #[test]
    fn test_parse_only_rest_parameters() {
        let input = "(&rest c)";
        let context = reader::Context::new(input, "test_parse_parameters");
        let mut reader = Reader::new(&context);
        let sexpr = reader.next().unwrap().unwrap();
        let list = sexpr.as_list().unwrap();
        let parameters = parse_parameters(&sexpr, list).unwrap();

        match parameters {
            Parameters::Rest(params, _) if params.is_empty() => (),
            _ => panic!(),
        };
    }
}
