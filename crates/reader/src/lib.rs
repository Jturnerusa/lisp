use core::fmt;
use logos::{Lexer, Logos};
use thiserror::Error;
use unwrap_enum::{EnumAs, EnumIs};

#[derive(Clone, Debug, Error)]
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

#[derive(Clone, Debug, PartialEq, PartialOrd, Hash, EnumAs, EnumIs)]
pub enum Sexpr {
    List(Vec<Sexpr>),
    Symbol(String),
    String(String),
    Char(char),
    Int(i64),
    Bool(bool),
    Nil,
}

pub struct Reader<'a> {
    lexer: Lexer<'a, Token>,
}

impl<'a> Reader<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            lexer: Lexer::new(input),
        }
    }
}

impl<'a> Iterator for Reader<'a> {
    type Item = Result<Sexpr, Error<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        read(&mut self.lexer)
    }
}

impl fmt::Display for Sexpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexpr::List(list) => {
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
            Sexpr::Symbol(symbol) => write!(f, "{symbol}"),
            Sexpr::String(string) => write!(f, r#""{string}""#),
            Sexpr::Char(char) => write!(f, "'{char}'"),
            Sexpr::Int(int) => write!(f, "{int}"),
            Sexpr::Bool(bool) if !bool => write!(f, "false"),
            Sexpr::Bool(_) => write!(f, "true"),
            Self::Nil => write!(f, "()"),
        }
    }
}

fn read<'a>(lexer: &mut Lexer<'a, Token>) -> Option<Result<Sexpr, Error<'a>>> {
    Some(Ok(match lexer.next()? {
        Ok(Token::LeftParen) => match read_list(lexer) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::RightParen) => return Some(Err(Error::UnbalancedParens)),
        Ok(Token::Quote) => match expand_macro(lexer, Macro::Quote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::QuasiQuote) => match expand_macro(lexer, Macro::QuasiQuote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::UnQuote) => match expand_macro(lexer, Macro::UnQuote) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::Splice) => match expand_macro(lexer, Macro::Splice) {
            Ok(sexpr) => sexpr,
            Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
        },
        Ok(Token::Symbol) => Sexpr::Symbol(lexer.slice().to_string()),
        Ok(Token::String) => Sexpr::String(lexer.slice().to_string()),
        Ok(Token::Char) => Sexpr::Char(lexer.slice().parse().unwrap()),
        Ok(Token::Int) => Sexpr::Int(lexer.slice().parse().unwrap()),
        Ok(Token::True) => Sexpr::Bool(true),
        Ok(Token::False) => Sexpr::Bool(false),
        Err(_) => return Some(Err(Error::Lexer(lexer.remainder()))),
    }))
}

fn read_list<'a>(lexer: &mut Lexer<'a, Token>) -> Result<Sexpr, Error<'a>> {
    let mut list = Vec::new();

    loop {
        match lexer.next() {
            Some(Ok(Token::LeftParen)) => list.push(read_list(lexer)?),
            Some(Ok(Token::RightParen)) if list.is_empty() => return Ok(Sexpr::Nil),
            Some(Ok(Token::RightParen)) => return Ok(Sexpr::List(list)),
            Some(Ok(Token::Quote)) => list.push(expand_macro(lexer, Macro::Quote)?),
            Some(Ok(Token::QuasiQuote)) => list.push(expand_macro(lexer, Macro::QuasiQuote)?),
            Some(Ok(Token::UnQuote)) => list.push(expand_macro(lexer, Macro::UnQuote)?),
            Some(Ok(Token::Splice)) => list.push(expand_macro(lexer, Macro::Splice)?),
            Some(Ok(Token::Symbol)) => list.push(Sexpr::Symbol(lexer.slice().to_string())),
            Some(Ok(Token::String)) => list.push(Sexpr::String(lexer.slice().to_string())),
            Some(Ok(Token::Char)) => list.push(Sexpr::Char(lexer.slice().parse().unwrap())),
            Some(Ok(Token::Int)) => list.push(Sexpr::Int(lexer.slice().parse().unwrap())),
            Some(Ok(Token::True)) => list.push(Sexpr::Bool(true)),
            Some(Ok(Token::False)) => list.push(Sexpr::Bool(false)),
            Some(Err(_)) => return Err(Error::Lexer(lexer.remainder())),
            None => return Err(Error::UnExpectedEof),
        }
    }
}

fn expand_macro<'a>(lexer: &mut Lexer<'a, Token>, r#macro: Macro) -> Result<Sexpr, Error<'a>> {
    Ok(Sexpr::List(vec![
        Sexpr::Symbol(
            match r#macro {
                Macro::Quote => "quote",
                Macro::QuasiQuote => "quasiquote",
                Macro::UnQuote => "unquote",
                Macro::Splice => "splice",
            }
            .to_string(),
        ),
        match read(lexer) {
            Some(Ok(sexpr)) => sexpr,
            Some(Err(_)) => return Err(Error::Lexer(lexer.remainder())),
            None => return Err(Error::UnExpectedEof),
        },
    ]))
}
