use crate::xxhash;
use gc::Gc;
use identity_hasher::{IdentityHasher, IdentityMap};
use reader::{Reader, Sexpr};
use std::{
    collections::{BTreeSet, HashMap},
    hash::{Hash, Hasher},
};
use vm::{Arity, OpCodeTable, UpValue, Vm};

use crate::{
    ast::{self, Ast, Quoted},
    bytecode,
    environment::{self, Environment, Variable},
    il,
};

#[derive(Debug, thiserror::Error)]
pub enum Error<'a> {
    #[error("il compiler error: {message}")]
    Il { ast: &'a Ast<'a>, message: String },

    #[error("reader error: {0}")]
    Reader(#[from] reader::Error<'static>),

    #[error("ast error: {0}")]
    Ast(#[from] ast::Error<'static>),

    #[error("bytecode compiler error: {0}")]
    Bytecode(#[from] bytecode::Error<'static>),

    #[error("vm error: {0}")]
    Vm(#[from] vm::Error),
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
pub enum Il<'a> {
    Lambda(Lambda<'a>),
    If(If<'a>),
    Apply(Apply<'a>),
    Def(Def<'a>),
    Set(Set<'a>),
    FnCall(FnCall<'a>),
    ArithmeticOperation(ArithmeticOperation<'a>),
    ComparisonOperation(ComparisonOperation<'a>),
    List(List<'a>),
    Cons(Cons<'a>),
    Car(Car<'a>),
    Cdr(Cdr<'a>),
    MapCreate(MapCreate<'a>),
    MapInsert(MapInsert<'a>),
    MapRetrieve(MapRetrieve<'a>),
    VarRef(VarRef<'a>),
    Constant(Constant<'a>),
}

#[derive(Clone, Debug)]
pub enum Constant<'a> {
    Symbol { source: &'a Ast<'a>, symbol: String },
    String { source: &'a Ast<'a>, string: String },
    Char { source: &'a Ast<'a>, char: char },
    Int { source: &'a Ast<'a>, int: i64 },
    Bool { source: &'a Ast<'a>, bool: bool },
    Nil { source: &'a Ast<'a> },
}

#[derive(Clone, Debug)]
pub enum VarRef<'a> {
    Local {
        source: &'a Ast<'a>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    UpValue {
        source: &'a Ast<'a>,
        name: String,
        index: usize,
        r#type: Option<Type>,
    },
    Global {
        source: &'a Ast<'a>,
        name: String,
        r#type: Option<Type>,
    },
}

#[derive(Clone, Debug)]
pub struct Parameter<'a> {
    pub source: &'a Ast<'a>,
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug)]
pub enum Parameters<'a> {
    Nary(Vec<Parameter<'a>>),
    Variadic(Vec<Parameter<'a>>),
}

#[derive(Clone, Debug)]
pub struct Lambda<'a> {
    pub source: &'a Ast<'a>,
    pub parameters: Parameters<'a>,
    pub r#type: Option<Type>,
    pub arity: Arity,
    pub upvalues: Vec<UpValue>,
    pub body: Vec<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct If<'a> {
    pub source: &'a Ast<'a>,
    pub predicate: Box<Il<'a>>,
    pub then: Box<Il<'a>>,
    pub r#else: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct FnCall<'a> {
    pub source: &'a Ast<'a>,
    pub function: Box<Il<'a>>,
    pub args: Vec<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct Apply<'a> {
    pub source: &'a Ast<'a>,
    pub exprs: Vec<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct List<'a> {
    pub source: &'a Ast<'a>,
    pub exprs: Vec<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct Cons<'a> {
    pub source: &'a Ast<'a>,
    pub lhs: Box<Il<'a>>,
    pub rhs: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct Car<'a> {
    pub source: &'a Ast<'a>,
    pub body: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct Cdr<'a> {
    pub source: &'a Ast<'a>,
    pub body: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub enum ArithmeticOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub struct ArithmeticOperation<'a> {
    pub source: &'a Ast<'a>,
    pub operator: ArithmeticOperator,
    pub lhs: Box<Il<'a>>,
    pub rhs: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub enum ComparisonOperator {
    Eq,
    Lt,
    Gt,
}

#[derive(Clone, Debug)]
pub struct ComparisonOperation<'a> {
    pub source: &'a Ast<'a>,
    pub operator: ComparisonOperator,
    pub lhs: Box<Il<'a>>,
    pub rhs: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct Def<'a> {
    pub source: &'a Ast<'a>,
    pub parameter: Parameter<'a>,
    pub body: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct Set<'a> {
    pub source: &'a Ast<'a>,
    pub target: VarRef<'a>,
    pub body: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct MapCreate<'a> {
    pub source: &'a Ast<'a>,
    pub map: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct MapInsert<'a> {
    pub source: &'a Ast<'a>,
    pub map: Box<Il<'a>>,
    pub key: Box<Il<'a>>,
    pub value: Box<Il<'a>>,
}

#[derive(Clone, Debug)]
pub struct MapRetrieve<'a> {
    pub source: &'a Ast<'a>,
    pub map: Box<Il<'a>>,
    pub key: Box<Il<'a>>,
}

pub struct Compiler {
    environment: Environment,
    macros: HashMap<String, u64>,
}

impl<'a> VarRef<'a> {
    pub fn source(&self) -> &'a Ast<'a> {
        match self {
            Self::Local { source, .. }
            | Self::UpValue { source, .. }
            | Self::Global { source, .. } => source,
        }
    }
}

impl<'a> Constant<'a> {
    pub fn source(&self) -> &'a Ast<'a> {
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

impl<'a> Il<'a> {
    pub fn source_ast(&self) -> &Ast<'a> {
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

impl<'a> Parameter<'a> {
    pub fn from_ast(source: &'a Ast<'a>, parameter: &'a ast::Parameter) -> Result<Self, ()> {
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

impl<'a> Parameters<'a> {
    pub fn from_ast(source: &'a Ast<'a>, parameters: &'a ast::Parameters) -> Result<Self, ()> {
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
            macros: HashMap::new(),
        }
    }

    pub fn compile<'a>(
        &mut self,
        ast: &'a Ast<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        match ast {
            Ast::DefMacro(defmacro) => self.compile_defmacro(ast, defmacro, vm),
            Ast::Lambda(lambda) => self.compile_lambda(ast, lambda, vm),
            Ast::Def(def) => self.compile_def(ast, def, vm),
            Ast::Set(set) => self.compile_set(ast, set, vm),
            Ast::If(r#if) => self.compile_if(ast, r#if, vm),
            Ast::FnCall(fncall)
                if fncall
                    .function
                    .as_variable()
                    .is_some_and(|function| self.macros.contains_key(function.name.as_str())) =>
            {
                self.eval_macro(
                    &fncall.function.as_variable().unwrap().name,
                    ast,
                    fncall,
                    vm,
                )
            }
            Ast::FnCall(fncall) => self.compile_fncall(ast, fncall, vm),
            Ast::Quote(quote) => self.compile_quote(ast, quote),
            Ast::Apply(apply) => self.compile_apply(ast, apply, vm),
            Ast::BinaryArithemticOperation(op) => self.compile_arithmetic_operation(ast, op, vm),
            Ast::ComparisonOperation(op) => self.compile_comparison_operation(ast, op, vm),
            Ast::List(list) => self.compile_list(ast, list, vm),
            Ast::Cons(cons) => self.compile_cons(ast, cons, vm),
            Ast::Car(car) => self.compile_car(ast, car, vm),
            Ast::Cdr(cdr) => self.compile_cdr(ast, cdr, vm),
            Ast::Constant(constant) => self.compile_constant(ast, constant),
            Ast::Variable(variable) => self.compile_variable_reference(ast, variable),
            _ => todo!(),
        }
    }

    fn compile_constant<'a>(
        &mut self,
        source: &'a Ast<'a>,
        constant: &'a ast::Constant<'a>,
    ) -> Result<Il<'a>, Error<'a>> {
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

    fn compile_variable_reference<'a>(
        &mut self,
        source: &'a Ast<'a>,
        variable: &ast::Variable<'a>,
    ) -> Result<Il<'a>, Error<'a>> {
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

    fn compile_defmacro<'a>(
        &mut self,
        source: &'a Ast<'a>,
        defmacro: &'a ast::DefMacro<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        let arity = match &defmacro.parameters {
            ast::Parameters::Normal(_) if defmacro.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(defmacro.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(defmacro.parameters.len()),
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
            .map(|ast| self.compile(ast, vm))
            .collect::<Result<Vec<Il>, Error>>()?;

        let lambda: &'static _ = Box::leak(Box::new(Il::Lambda(il::Lambda {
            source,
            parameters,
            r#type: None,
            upvalues: Vec::new(),
            arity,
            body,
        })));

        let mut opcodes = OpCodeTable::new();
        let mut constants = IdentityMap::with_hasher(IdentityHasher::new());
        let constant: vm::Constant<&Sexpr> = vm::Constant::Symbol(Gc::new(defmacro.name.clone()));
        let hash = xxhash(&constant);

        bytecode::compile(lambda, &mut opcodes, &mut constants).unwrap();

        vm.load_constants(constants.into_values());
        vm.eval(&opcodes).map_err(|(e, _)| e)?;

        vm.load_constants(std::iter::once(constant));
        vm.def_global(hash).unwrap();

        self.macros.insert(defmacro.name.clone(), hash);

        Ok(Il::Constant(Constant::Nil { source }))
    }

    fn eval_macro<'a>(
        &mut self,
        r#macro: &str,
        source: &'a Ast<'a>,
        fncall: &'a ast::FnCall<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        let args = fncall
            .exprs
            .iter()
            .map(|expr| Box::leak(Box::new(expr.source_sexpr().quote())))
            .map(|sexpr| Box::leak(Box::new(Ast::from_sexpr(sexpr).unwrap())))
            .map(|ast| self.compile(ast, vm))
            .collect::<Result<Vec<_>, _>>()?;

        let mut opcode_table = OpCodeTable::new();
        let mut constants = IdentityMap::with_hasher(IdentityHasher::new());

        for arg in &args {
            bytecode::compile(
                Box::leak(Box::new(arg.clone())),
                &mut opcode_table,
                &mut constants,
            )
            .unwrap();
        }

        let macro_symbol_hash = *self.macros.get(r#macro).unwrap();

        vm.load_constants(constants.into_values());
        vm.get_global(macro_symbol_hash)?;
        vm.eval(&opcode_table).map_err(|(e, _)| e)?;
        vm.call(args.len())?;
        vm.eval(&OpCodeTable::new()).map_err(|(e, _)| e)?;

        let Some(object) = vm.pop().map(|local| local.into_object()) else {
            return Ok(Il::Constant(Constant::Nil { source }));
        };

        let mut buff = String::new();

        object.print(&mut buff).map_err(|_| Error::Il {
            ast: source,
            message: "failed to print macro result".to_string(),
        })?;

        dbg!(&buff);

        let context: &'static _ = Box::leak(Box::new(reader::Context::new(
            buff.as_str(),
            "macro-expansion",
        )));
        let mut reader = Reader::new(context);
        let sexpr: &'static _ = Box::leak(Box::new(reader.next().unwrap()?));
        let ast: &'static _ = Box::leak(Box::new(Ast::from_sexpr(sexpr)?));

        self.compile(ast, vm)
    }

    fn compile_lambda<'a>(
        &mut self,
        source: &'a Ast<'a>,
        lambda: &'a ast::Lambda<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        let arity = match &lambda.parameters {
            ast::Parameters::Normal(_) if lambda.parameters.len() == 0 => Arity::Nullary,
            ast::Parameters::Normal(_) => Arity::Nary(lambda.parameters.len()),
            ast::Parameters::Rest(..) => Arity::Variadic(lambda.parameters.len()),
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
            .map(|ast| self.compile(ast, vm))
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

    fn compile_if<'a, 'b>(
        &mut self,
        source: &'a Ast<'a>,
        r#if: &'a ast::If<'a>,
        vm: &'b mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::If(If {
            source,
            predicate: Box::new(self.compile(&r#if.predicate, vm)?),
            then: Box::new(self.compile(&r#if.then, vm)?),
            r#else: Box::new(self.compile(&r#if.r#else, vm)?),
        }))
    }

    fn compile_def<'a, 'b>(
        &mut self,
        source: &'a Ast<'a>,
        def: &'a ast::Def<'a>,
        vm: &'b mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
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
            body: Box::new(self.compile(&def.body, vm)?),
        }))
    }

    fn compile_set<'a, 'b>(
        &mut self,
        source: &'a Ast<'a>,
        set: &'a ast::Set<'a>,
        vm: &'b mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
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
            body: Box::new(self.compile(&set.body, vm)?),
        }))
    }

    fn compile_quote<'a>(
        &mut self,
        source: &'a Ast<'a>,
        quote: &'a ast::Quote<'a>,
    ) -> Result<Il<'a>, Error<'a>> {
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
    fn compile_quoted_list<'a>(
        &mut self,
        source: &'a Ast<'a>,
        list: &'a [Quoted<'a>],
    ) -> Result<Il<'a>, Error<'a>> {
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
                .collect::<Result<Vec<_>, Error<'a>>>()?,
        }))
    }

    fn compile_fncall<'a>(
        &mut self,
        source: &'a Ast<'a>,
        fncall: &'a ast::FnCall<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::FnCall(FnCall {
            source,
            function: Box::new(self.compile(&fncall.function, vm)?),
            args: fncall
                .exprs
                .iter()
                .map(|arg| self.compile(arg, vm))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_apply<'a>(
        &mut self,
        source: &'a Ast<'a>,
        apply: &'a ast::Apply<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::Apply(Apply {
            source,
            exprs: apply
                .exprs
                .iter()
                .map(|expr| self.compile(expr, vm))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_arithmetic_operation<'a>(
        &mut self,
        source: &'a Ast<'a>,
        op: &'a ast::BinaryArithmeticOperation<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::ArithmeticOperation(ArithmeticOperation {
            source,
            operator: match op.operator {
                ast::BinaryArithmeticOperator::Add => ArithmeticOperator::Add,
                ast::BinaryArithmeticOperator::Sub => ArithmeticOperator::Sub,
                ast::BinaryArithmeticOperator::Mul => ArithmeticOperator::Mul,
                ast::BinaryArithmeticOperator::Div => ArithmeticOperator::Div,
            },
            lhs: Box::new(self.compile(&op.lhs, vm)?),
            rhs: Box::new(self.compile(&op.rhs, vm)?),
        }))
    }

    fn compile_comparison_operation<'a>(
        &mut self,
        source: &'a Ast<'a>,
        op: &'a ast::ComparisonOperation<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::ComparisonOperation(ComparisonOperation {
            source,
            operator: match op.operator {
                ast::ComparisonOperator::Eq => ComparisonOperator::Eq,
                ast::ComparisonOperator::Lt => ComparisonOperator::Lt,
                ast::ComparisonOperator::Gt => ComparisonOperator::Gt,
            },
            lhs: Box::new(self.compile(&op.lhs, vm)?),
            rhs: Box::new(self.compile(&op.rhs, vm)?),
        }))
    }

    fn compile_list<'a>(
        &mut self,
        source: &'a Ast<'a>,
        list: &'a ast::List<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::List(List {
            source,
            exprs: list
                .exprs
                .iter()
                .map(|expr| self.compile(expr, vm))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }

    fn compile_cons<'a>(
        &mut self,
        source: &'a Ast<'a>,
        cons: &'a ast::Cons<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::Cons(Cons {
            source,
            lhs: Box::new(self.compile(&cons.lhs, vm)?),
            rhs: Box::new(self.compile(&cons.rhs, vm)?),
        }))
    }

    fn compile_car<'a>(
        &mut self,
        source: &'a Ast<'a>,
        car: &'a ast::Car<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::Car(Car {
            source,
            body: Box::new(self.compile(&car.body, vm)?),
        }))
    }

    fn compile_cdr<'a>(
        &mut self,
        source: &'a Ast<'a>,
        cdr: &'a ast::Cdr<'a>,
        vm: &mut Vm<&'a Sexpr<'a>>,
    ) -> Result<Il<'a>, Error<'a>> {
        Ok(Il::Cdr(Cdr {
            source,
            body: Box::new(self.compile(&cdr.body, vm)?),
        }))
    }
}

impl<'a> IntoIterator for &'a Parameters<'a> {
    type Item = Parameter<'a>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Parameters::Nary(params) | Parameters::Variadic(params) => params.iter().cloned(),
        }
    }
}
