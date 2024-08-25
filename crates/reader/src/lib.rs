use core::fmt;
use logos::{Lexer, Logos};
use std::cmp::Ordering;
use thiserror::Error;
use unwrap_enum::EnumIs;

#[derive(Clone, Error)]
pub enum Error {
    #[error("lexer error: remaining input: {0}")]
    Lexer(String),

    #[error("unbalanced parens")]
    UnbalancedParens,

    #[error("unexpected end of file")]
    UnExpectedEof,
}

#[derive(Clone, Debug, Logos)]
#[logos(skip r#"[\s\t\n]|;.*\n"#)]
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

    #[regex(r#"[a-zA-Z+_*/?@^=!<>&.-][a-zA-Z0-9+_*/?@^=!<>&:.-]*"#)]
    Symbol,

    #[regex(r#""[^"]*""#)]
    String,

    #[regex(r#"\?."#)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileSpan {
    pub id: u64,
    pub start: usize,
    pub stop: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, EnumIs)]
pub enum Sexpr {
    List { list: Vec<Sexpr>, span: FileSpan },
    Symbol { symbol: String, span: FileSpan },
    String { string: String, span: FileSpan },
    Char { char: char, span: FileSpan },
    Int { int: i64, span: FileSpan },
    Bool { bool: bool, span: FileSpan },
    Nil { span: FileSpan },
}

#[derive(Clone, Debug)]
pub struct Reader<'src> {
    lexer: Lexer<'src, Token>,
    file_id: u64,
}

impl<'src> Reader<'src> {
    pub fn new(source: &'src str, file_id: u64) -> Self {
        Self {
            lexer: Lexer::new(source),
            file_id,
        }
    }
}

impl Sexpr {
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

    pub fn span(&self) -> FileSpan {
        match self {
            Self::List { span, .. }
            | Self::Symbol { span, .. }
            | Self::String { span, .. }
            | Self::Char { span, .. }
            | Self::Int { span, .. }
            | Self::Bool { span, .. }
            | Self::Nil { span, .. } => *span,
        }
    }
}

impl<'src> Iterator for Reader<'src> {
    type Item = Result<Sexpr, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        read(&mut self.lexer, self.file_id)
    }
}

impl fmt::Display for Sexpr {
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

fn read<'src>(lexer: &mut Lexer<'src, Token>, file_id: u64) -> Option<Result<Sexpr, Error>> {
    Some(Ok(match lexer.next()? {
        Ok(Token::LeftParen) => match read_list(lexer, file_id) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder().to_string()))),
        },
        Ok(Token::RightParen) => return Some(Err(Error::UnbalancedParens)),
        Ok(Token::Quote) => match expand_macro(lexer, file_id, Macro::Quote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder().to_string()))),
        },
        Ok(Token::QuasiQuote) => match expand_macro(lexer, file_id, Macro::QuasiQuote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder().to_string()))),
        },
        Ok(Token::UnQuote) => match expand_macro(lexer, file_id, Macro::UnQuote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder().to_string()))),
        },
        Ok(Token::Splice) => match expand_macro(lexer, file_id, Macro::Splice) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder().to_string()))),
        },
        Ok(Token::Symbol) => Sexpr::Symbol {
            symbol: lexer.slice().to_string(),
            span: FileSpan {
                id: file_id,
                start: lexer.span().start,
                stop: lexer.span().end,
            },
        },
        Ok(Token::String) => Sexpr::String {
            string: lexer.slice()[1..lexer.slice().len() - 1].to_string(),
            span: FileSpan {
                id: file_id,
                start: lexer.span().start,
                stop: lexer.span().end,
            },
        },
        Ok(Token::Char) => Sexpr::Char {
            char: lexer.slice()[1..lexer.slice().len()].parse().unwrap(),
            span: FileSpan {
                id: file_id,
                start: lexer.span().start,
                stop: lexer.span().end,
            },
        },
        Ok(Token::Int) => Sexpr::Int {
            int: lexer.slice().parse().unwrap(),
            span: FileSpan {
                id: file_id,
                start: lexer.span().start,
                stop: lexer.span().end,
            },
        },
        Ok(Token::True) => Sexpr::Bool {
            bool: true,
            span: FileSpan {
                id: file_id,
                start: lexer.span().start,
                stop: lexer.span().end,
            },
        },
        Ok(Token::False) => Sexpr::Bool {
            bool: false,
            span: FileSpan {
                id: file_id,
                start: lexer.span().start,
                stop: lexer.span().end,
            },
        },
        Ok(Token::Nil) => Sexpr::Nil {
            span: FileSpan {
                id: file_id,
                start: lexer.span().start,
                stop: lexer.span().end,
            },
        },
        Err(_) => return Some(Err(Error::Lexer(lexer.remainder().to_string()))),
    }))
}

fn read_list<'src>(lexer: &mut Lexer<'src, Token>, file_id: u64) -> Result<Sexpr, Error> {
    let mut list = Vec::new();

    loop {
        match lexer.next() {
            Some(Ok(Token::LeftParen)) => list.push(read_list(lexer, file_id)?),
            Some(Ok(Token::RightParen)) if list.is_empty() => {
                return Ok(Sexpr::Nil {
                    span: FileSpan {
                        id: file_id,
                        start: lexer.span().start,
                        stop: lexer.span().end,
                    },
                })
            }
            Some(Ok(Token::RightParen)) => {
                return Ok(Sexpr::List {
                    list,
                    span: FileSpan {
                        id: file_id,
                        start: lexer.span().start,
                        stop: lexer.span().end,
                    },
                })
            }
            Some(Ok(Token::Quote)) => list.push(expand_macro(lexer, file_id, Macro::Quote)?),
            Some(Ok(Token::QuasiQuote)) => {
                list.push(expand_macro(lexer, file_id, Macro::QuasiQuote)?)
            }
            Some(Ok(Token::UnQuote)) => list.push(expand_macro(lexer, file_id, Macro::UnQuote)?),
            Some(Ok(Token::Splice)) => list.push(expand_macro(lexer, file_id, Macro::Splice)?),
            Some(Ok(Token::Symbol)) => list.push(Sexpr::Symbol {
                symbol: lexer.slice().to_string(),
                span: FileSpan {
                    id: file_id,
                    start: lexer.span().start,
                    stop: lexer.span().end,
                },
            }),
            Some(Ok(Token::String)) => list.push(Sexpr::String {
                string: lexer.slice()[1..lexer.slice().len() - 1].to_string(),
                span: FileSpan {
                    id: file_id,
                    start: lexer.span().start,
                    stop: lexer.span().end,
                },
            }),
            Some(Ok(Token::Char)) => list.push(Sexpr::Char {
                char: lexer.slice()[1..lexer.slice().len()].parse().unwrap(),
                span: FileSpan {
                    id: file_id,
                    start: lexer.span().start,
                    stop: lexer.span().end,
                },
            }),
            Some(Ok(Token::Int)) => list.push(Sexpr::Int {
                int: lexer.slice().parse().unwrap(),
                span: FileSpan {
                    id: file_id,
                    start: lexer.span().start,
                    stop: lexer.span().end,
                },
            }),
            Some(Ok(Token::True)) => list.push(Sexpr::Bool {
                bool: true,
                span: FileSpan {
                    id: file_id,
                    start: lexer.span().start,
                    stop: lexer.span().end,
                },
            }),
            Some(Ok(Token::False)) => list.push(Sexpr::Bool {
                bool: false,
                span: FileSpan {
                    id: file_id,
                    start: lexer.span().start,
                    stop: lexer.span().end,
                },
            }),
            Some(Ok(Token::Nil)) => list.push(Sexpr::Nil {
                span: FileSpan {
                    id: file_id,
                    start: lexer.span().start,
                    stop: lexer.span().end,
                },
            }),
            Some(Err(_)) => return Err(Error::Lexer(lexer.remainder().to_string())),
            None => return Err(Error::UnExpectedEof),
        }
    }
}

fn expand_macro<'src>(
    lexer: &mut Lexer<'src, Token>,
    file_id: u64,
    r#macro: Macro,
) -> Result<Sexpr, Error> {
    let span = FileSpan {
        id: file_id,
        start: lexer.span().start,
        stop: lexer.span().end,
    };

    let symbol = Sexpr::Symbol {
        symbol: match r#macro {
            Macro::Quote => "quote",
            Macro::QuasiQuote => "quasiquote",
            Macro::UnQuote => "unquote",
            Macro::Splice => "unquote-splice",
        }
        .to_string(),
        span,
    };

    let body = match read(lexer, file_id) {
        Some(Ok(sexpr)) => sexpr,
        Some(Err(_)) => return Err(Error::Lexer(lexer.remainder().to_string())),
        None => return Err(Error::UnExpectedEof),
    };

    Ok(Sexpr::List {
        list: vec![symbol, body],
        span: FileSpan {
            id: file_id,
            start: lexer.span().start,
            stop: lexer.span().end,
        },
    })
}

impl PartialOrd for Sexpr {
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

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lexer(remainder) => {
                write!(f, "lexer error: {}", remainder)
            }
            Self::UnExpectedEof => write!(f, "unexpected eof"),
            Self::UnbalancedParens => write!(f, "unbalanced parens"),
        }
    }
}
