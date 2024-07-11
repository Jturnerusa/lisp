use core::fmt;
use logos::{Lexer, Logos};
use std::{cmp::Ordering, ops::Range};
use thiserror::Error;
use unwrap_enum::EnumIs;

#[derive(Clone, Debug, Error)]
pub enum Error<'a> {
    #[error("lexer error: remaining input: {0}")]
    Lexer(&'a str),

    #[error("unbalanced parens")]
    UnbalancedParens,

    #[error("unexpected end of file")]
    UnExpectedEof,
}

#[derive(Clone, Debug, Logos)]
#[logos(skip r#"[\s\t\n]|[;][\s]*[\n]"#)]
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

    #[token("nil")]
    Nil,

    #[regex(r#"[a-zA-Z+_*/?@^=-][a-zA-Z0-9+_*/?@^=-]*"#)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, EnumIs)]
pub enum Sexpr<'a, T> {
    List {
        list: Vec<Sexpr<'a, T>>,
        context: &'a Context<T>,
        span: Range<usize>,
    },
    Symbol {
        symbol: String,
        context: &'a Context<T>,
        span: Range<usize>,
    },
    String {
        string: String,
        context: &'a Context<T>,
        span: Range<usize>,
    },
    Char {
        char: char,
        context: &'a Context<T>,
        span: Range<usize>,
    },
    Int {
        int: i64,
        context: &'a Context<T>,
        span: Range<usize>,
    },
    Bool {
        bool: bool,
        context: &'a Context<T>,
        span: Range<usize>,
    },
    Nil {
        context: &'a Context<T>,
        span: Range<usize>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Context<T> {
    display: T,
    source: String,
}

#[derive(Clone, Debug)]
pub struct Reader<'a, T> {
    lexer: Lexer<'a, Token>,
    context: &'a Context<T>,
}

impl<T> Context<T> {
    pub fn new(source: &str, display: T) -> Self {
        Self {
            display,
            source: source.to_string(),
        }
    }

    pub fn source(&self) -> &str {
        self.source.as_str()
    }

    pub fn span(&self, span: Range<usize>) -> &str {
        &self.source[span.start..span.end]
    }

    pub fn display(&self) -> &T {
        &self.display
    }
}

impl<'a, T> Reader<'a, T> {
    pub fn new(context: &'a Context<T>) -> Self {
        Self {
            lexer: Lexer::new(context.source()),
            context,
        }
    }
}

impl<'a, T> Sexpr<'a, T> {
    pub fn as_list(&self) -> Option<&[Sexpr<T>]> {
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

    pub fn context(&self) -> &Context<T> {
        match self {
            Self::List { context, .. }
            | Self::Symbol { context, .. }
            | Self::String { context, .. }
            | Self::Char { context, .. }
            | Self::Int { context, .. }
            | Self::Bool { context, .. }
            | Self::Nil { context, .. } => context,
        }
    }

    pub fn span(&self) -> Range<usize> {
        match self {
            Self::List { span, .. }
            | Self::Symbol { span, .. }
            | Self::String { span, .. }
            | Self::Char { span, .. }
            | Self::Int { span, .. }
            | Self::Bool { span, .. }
            | Self::Nil { span, .. } => span.clone(),
        }
    }
}

impl<'a, T: Clone> Sexpr<'a, T> {
    pub fn quote(&'a self) -> Sexpr<'a, T> {
        let quote = Sexpr::Symbol {
            symbol: "quote".to_string(),
            context: self.context(),
            span: self.span(),
        };

        Sexpr::List {
            list: vec![quote, self.clone()],
            context: self.context(),
            span: self.span(),
        }
    }
}

impl<'a, T> Iterator for Reader<'a, T> {
    type Item = Result<Sexpr<'a, T>, Error<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        read(&mut self.lexer, self.context)
    }
}

impl<'a, T> fmt::Display for Sexpr<'a, T> {
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

fn read<'a, T>(
    lexer: &mut Lexer<'a, Token>,
    context: &'a Context<T>,
) -> Option<Result<Sexpr<'a, T>, Error<'a>>> {
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
        Ok(Token::Nil) => Sexpr::Nil {
            context,
            span: lexer.span(),
        },
        Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
    }))
}

fn read_list<'a, T>(
    lexer: &mut Lexer<'a, Token>,
    context: &'a Context<T>,
) -> Result<Sexpr<'a, T>, Error<'a>> {
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
            Some(Ok(Token::Nil)) => list.push(Sexpr::Nil {
                context,
                span: lexer.span(),
            }),
            Some(Err(_)) => return Err(Error::Lexer(lexer.remainder())),
            None => return Err(Error::UnExpectedEof),
        }
    }
}

fn expand_macro<'a, T>(
    lexer: &mut Lexer<'a, Token>,
    context: &'a Context<T>,
    r#macro: Macro,
) -> Result<Sexpr<'a, T>, Error<'a>> {
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

impl<'a, T: PartialEq> PartialOrd for Sexpr<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::List { list: a, .. }, Self::List { list: b, .. }) => a.partial_cmp(b),
            (Self::Symbol { symbol: a, .. }, Self::Symbol { symbol: b, .. }) => a.partial_cmp(b),
            (Self::String { string: a, .. }, Self::String { string: b, .. }) => a.partial_cmp(b),
            (Self::Char { char: a, .. }, Self::Char { char: b, .. }) => a.partial_cmp(b),
            (Self::Int { int: a, .. }, Self::Int { int: b, .. }) => a.partial_cmp(b),
            (Self::Bool { bool: a, .. }, Self::Bool { bool: b, .. }) => a.partial_cmp(b),
            (Self::Nil { .. }, Self::Nil { .. }) => Some(Ordering::Equal),
            _ => None,
        }
    }
}
