use core::fmt;

use logos::{Lexer, Logos};
use std::{
    any::Any,
    fmt::Display,
    fs,
    hash::{Hash, Hasher},
    io::Read,
    ops::Range,
    path::{Path, PathBuf},
};

use unwrap_enum::EnumIs;

pub trait Context: fmt::Debug {
    fn context(&self) -> Box<dyn fmt::Display>;

    fn source(&self) -> &str;

    fn span(&self, range: Range<usize>) -> &str {
        &self.source()[range]
    }

    fn dyn_clone(&self) -> Box<dyn Context>;

    fn dyn_hash(&self, hasher: &mut dyn Hasher);

    fn dyn_partial_eq(&self, other: &dyn Any) -> bool;
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum Error<'a> {
    #[error("lexer error: remaining input: {0}")]
    Lexer(&'a str),

    #[error("unbalanced parens")]
    UnbalancedParens,

    #[error("unexpected end of file")]
    UnExpectedEof,
}

#[derive(Logos)]
#[logos(skip r#"[\s\t\n]|[;][\s]*"#)]
enum Token {
    #[token("(")]
    LeftParen,

    #[token(")")]
    RightParen,

    #[token("'")]
    Quote,

    #[token("`")]
    QuasiQuote,

    #[token(",")]
    UnQuote,

    #[token(",@")]
    Splice,

    #[token("true")]
    True,

    #[token("false")]
    False,

    #[regex(r#"[a-zA-Z+_*/?@^-][a-zA-Z0-9+_*/?@^-]"#)]
    Symbol,

    #[regex(r#""[^"]*""#)]
    String,

    #[regex(r#"'[*]{1}'"#)]
    Char,

    #[regex("[0-9]+")]
    Int,
}

#[derive(Clone, Copy, Debug)]
enum Macro {
    Quote,
    QuasiQuote,
    UnQuote,
    Splice,
}

#[derive(Clone, Debug, EnumIs)]
pub enum Sexpr<'a> {
    List {
        list: Vec<Sexpr<'a>>,
        context: &'a dyn Context,
        span: Range<usize>,
    },
    Symbol {
        symbol: String,
        context: &'a dyn Context,
        span: Range<usize>,
    },
    String {
        string: String,
        context: &'a dyn Context,
        span: Range<usize>,
    },
    Char {
        char: char,
        context: &'a dyn Context,
        span: Range<usize>,
    },
    Int {
        int: i64,
        context: &'a dyn Context,
        span: Range<usize>,
    },
    Bool {
        bool: bool,
        context: &'a dyn Context,
        span: Range<usize>,
    },
    Nil {
        context: &'a dyn Context,
        span: Range<usize>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceFile {
    path: PathBuf,
    source: String,
}

pub struct Reader<'a> {
    lexer: Lexer<'a, Token>,
    context: &'a dyn Context,
}

impl SourceFile {
    pub fn new(path: &Path) -> Result<Self, Box<dyn std::error::Error>> {
        let mut file = fs::File::open(path)?;
        let mut source = String::new();
        file.read_to_string(&mut source)?;

        Ok(Self {
            path: path.to_owned(),
            source,
        })
    }
}

impl<'a> Reader<'a> {
    pub fn new(context: &'a dyn Context) -> Self {
        Self {
            lexer: Lexer::new(context.source()),
            context,
        }
    }
}

impl<'a> Sexpr<'a> {
    pub fn as_list(&self) -> Option<&[Sexpr]> {
        match self {
            Self::List { list, .. } => Some(list.as_slice()),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<&str> {
        match self {
            Self::Symbol { symbol, .. } => Some(symbol.as_str()),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        match self {
            Self::String { string, .. } => Some(string.as_str()),
            _ => None,
        }
    }

    pub fn as_char(&self) -> Option<char> {
        match self {
            Self::Char { char, .. } => Some(*char),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int { int, .. } => Some(*int),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool { bool, .. } => Some(*bool),
            _ => None,
        }
    }
}

impl<'a> Iterator for Reader<'a> {
    type Item = Result<Sexpr<'a>, Error<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        read(&mut self.lexer, self.context)
    }
}

impl<'a> fmt::Display for Sexpr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexpr::List { list, .. } => {
                write!(f, "(")?;
                for (i, sexpr) in list.iter().enumerate() {
                    write!(f, "{sexpr}")?;
                    if i < list.len() - 1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
            Sexpr::Symbol { symbol, .. } => write!(f, "{symbol}"),
            Sexpr::String { string, .. } => write!(f, r#""{string}""#),
            Sexpr::Char { char, .. } => write!(f, "'{char}'"),
            Sexpr::Int { int, .. } => write!(f, "{int}"),
            Sexpr::Bool { bool, .. } if !bool => write!(f, "false"),
            Sexpr::Bool { .. } => write!(f, "true"),
            Self::Nil { .. } => write!(f, "()"),
        }
    }
}

fn read<'a>(
    lexer: &mut Lexer<'a, Token>,
    context: &'a dyn Context,
) -> Option<Result<Sexpr<'a>, Error<'a>>> {
    Some(Ok(match lexer.next()? {
        Ok(Token::LeftParen) => match read_list(lexer, context) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::RightParen) => return Some(Err(Error::UnbalancedParens)),
        Ok(Token::Quote) => match expand_macro(lexer, context, Macro::Quote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::QuasiQuote) => match expand_macro(lexer, context, Macro::QuasiQuote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::UnQuote) => match expand_macro(lexer, context, Macro::UnQuote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::Splice) => match expand_macro(lexer, context, Macro::Splice) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::Symbol) => Sexpr::Symbol {
            symbol: lexer.slice().to_string(),
            context,
            span: lexer.span(),
        },
        Ok(Token::String) => Sexpr::String {
            string: lexer.slice().to_string(),
            context,
            span: lexer.span(),
        },
        Ok(Token::Char) => Sexpr::Char {
            char: lexer.slice().parse().unwrap(),
            context,
            span: lexer.span(),
        },
        Ok(Token::Int) => Sexpr::Int {
            int: lexer.slice().parse().unwrap(),
            context,
            span: lexer.span(),
        },
        Ok(Token::True) => Sexpr::Bool {
            bool: true,
            context,
            span: lexer.span(),
        },
        Ok(Token::False) => Sexpr::Bool {
            bool: false,
            context,
            span: lexer.span(),
        },
        Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
    }))
}

fn read_list<'a>(
    lexer: &mut Lexer<'a, Token>,
    context: &'a dyn Context,
) -> Result<Sexpr<'a>, Error<'a>> {
    let mut list = Vec::new();

    loop {
        match lexer.next() {
            Some(Ok(Token::LeftParen)) => list.push(read_list(lexer, context)?),
            Some(Ok(Token::RightParen)) if list.is_empty() => {
                return Ok(Sexpr::Nil {
                    context,
                    span: lexer.span(),
                })
            }
            Some(Ok(Token::RightParen)) => {
                return Ok(Sexpr::List {
                    list,
                    context,
                    span: lexer.span(),
                })
            }
            Some(Ok(Token::Quote)) => list.push(expand_macro(lexer, context, Macro::Quote)?),
            Some(Ok(Token::QuasiQuote)) => {
                list.push(expand_macro(lexer, context, Macro::QuasiQuote)?)
            }
            Some(Ok(Token::UnQuote)) => list.push(expand_macro(lexer, context, Macro::UnQuote)?),
            Some(Ok(Token::Splice)) => list.push(expand_macro(lexer, context, Macro::Splice)?),
            Some(Ok(Token::Symbol)) => list.push(Sexpr::Symbol {
                symbol: lexer.slice().to_string(),
                context,
                span: lexer.span(),
            }),
            Some(Ok(Token::String)) => list.push(Sexpr::String {
                string: lexer.slice().to_string(),
                context,
                span: lexer.span(),
            }),
            Some(Ok(Token::Char)) => list.push(Sexpr::Char {
                char: lexer.slice().parse().unwrap(),
                context,
                span: lexer.span(),
            }),
            Some(Ok(Token::Int)) => list.push(Sexpr::Int {
                int: lexer.slice().parse().unwrap(),
                context,
                span: lexer.span(),
            }),
            Some(Ok(Token::True)) => list.push(Sexpr::Bool {
                bool: true,
                context,
                span: lexer.span(),
            }),
            Some(Ok(Token::False)) => list.push(Sexpr::Bool {
                bool: false,
                context,
                span: lexer.span(),
            }),
            Some(Err(_)) => return Err(Error::Lexer(lexer.remainder())),
            None => return Err(Error::UnExpectedEof),
        }
    }
}

fn expand_macro<'a>(
    lexer: &mut Lexer<'a, Token>,
    context: &'a dyn Context,
    r#macro: Macro,
) -> Result<Sexpr<'a>, Error<'a>> {
    let span = lexer.span();

    let symbol = Sexpr::Symbol {
        symbol: match r#macro {
            Macro::Quote => "quote",
            Macro::QuasiQuote => "quasiquote",
            Macro::UnQuote => "unquote",
            Macro::Splice => "splice",
        }
        .to_string(),
        context,
        span: span.clone(),
    };

    let body = match read(lexer, context) {
        Some(Ok(sexpr)) => sexpr,
        Some(Err(_)) => return Err(Error::Lexer(lexer.remainder())),
        None => return Err(Error::UnExpectedEof),
    };

    Ok(Sexpr::List {
        list: vec![symbol, body],
        context,
        span,
    })
}

impl Context for SourceFile {
    fn context(&self) -> Box<dyn Display> {
        Box::new(self.path.as_path().to_str().unwrap().to_string())
    }

    fn source(&self) -> &str {
        &self.source
    }

    fn span(&self, range: Range<usize>) -> &str {
        &self.source[range]
    }

    fn dyn_hash(&self, hasher: &mut dyn Hasher) {
        let mut boxed_hasher = Box::new(hasher);
        self.path.hash(&mut boxed_hasher);
        self.source.hash(&mut boxed_hasher);
    }

    fn dyn_clone(&self) -> Box<dyn Context> {
        Box::new(Self {
            path: self.path.clone(),
            source: self.source.clone(),
        })
    }

    fn dyn_partial_eq(&self, other: &dyn Any) -> bool {
        match other.downcast_ref::<Self>() {
            Some(s) => self == s,
            None => false,
        }
    }
}

impl<'a: 'static> PartialEq for Sexpr<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::List {
                    list: list_a,
                    context: context_a,
                    span: span_a,
                },
                Self::List {
                    list: list_b,
                    context: context_b,
                    span: span_b,
                },
            ) => list_a == list_b && context_a.dyn_partial_eq(context_b) && span_a == span_b,
            (
                Self::Symbol {
                    symbol: symbol_a,
                    context: context_a,
                    span: span_a,
                },
                Self::Symbol {
                    symbol: symbol_b,
                    context: context_b,
                    span: span_b,
                },
            ) => symbol_a == symbol_b && context_a.dyn_partial_eq(context_b) && span_a == span_b,
            (
                Self::String {
                    string: string_a,
                    context: context_a,
                    span: span_a,
                },
                Self::String {
                    string: string_b,
                    context: context_b,
                    span: span_b,
                },
            ) => string_a == string_b && context_a.dyn_partial_eq(context_b) && span_a == span_b,
            (
                Self::Char {
                    char: char_a,
                    context: context_a,
                    span: span_a,
                },
                Self::Char {
                    char: char_b,
                    context: context_b,
                    span: span_b,
                },
            ) => char_a == char_b && context_a.dyn_partial_eq(context_b) && span_a == span_b,
            (
                Self::Int {
                    int: int_a,
                    context: context_a,
                    span: span_a,
                },
                Self::Int {
                    int: int_b,
                    context: context_b,
                    span: span_b,
                },
            ) => int_a == int_b && context_a.dyn_partial_eq(context_b) && span_a == span_b,
            (
                Self::Bool {
                    bool: bool_a,
                    context: context_a,
                    span: span_a,
                },
                Self::Bool {
                    bool: bool_b,
                    context: context_b,
                    span: span_b,
                },
            ) => bool_a == bool_b && context_a.dyn_partial_eq(context_b) && span_a == span_b,
            (
                Self::Nil {
                    context: context_a,
                    span: span_a,
                },
                Self::Nil {
                    context: context_b,
                    span: span_b,
                },
            ) => context_a.dyn_partial_eq(context_b) && span_a == span_b,
            _ => false,
        }
    }
}

impl<'a> Hash for Sexpr<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let context = match self {
            Self::List { context, .. }
            | Self::Symbol { context, .. }
            | Self::String { context, .. }
            | Self::Char { context, .. }
            | Self::Int { context, .. }
            | Self::Bool { context, .. }
            | Self::Nil { context, .. } => context,
        };

        let span = match self {
            Self::List { span, .. }
            | Self::Symbol { span, .. }
            | Self::String { span, .. }
            | Self::Char { span, .. }
            | Self::Int { span, .. }
            | Self::Bool { span, .. }
            | Self::Nil { span, .. } => span,
        };

        context.dyn_hash(state);
        span.hash(state);

        match self {
            Self::List { list, .. } => list.hash(state),
            Self::Symbol { symbol, .. } => symbol.hash(state),
            Self::String { string, .. } => string.hash(state),
            Self::Char { char, .. } => char.hash(state),
            Self::Int { int, .. } => int.hash(state),
            Self::Bool { bool, .. } => bool.hash(state),
            _ => (),
        }
    }
}
