use logos::{Lexer, Logos, SpannedIter};
use std::ops::Range;
use thiserror::Error;
use unwrap_enum::{EnumAs, EnumIs};

#[derive(Clone, Debug, Error)]
pub enum Error<'a> {
    #[error("lexer error: remaining input {0}")]
    Lexer(&'a str),

    #[error("unbalanced parens")]
    UnBalancedParen(&'a str),

    #[error("unexpected paren")]
    UnExpectedParen(&'a str),

    #[error("unexpected eof")]
    UnExpectedEof,
}

#[derive(Clone, Copy, Debug, Logos)]
#[logos(skip r#"[\s\t\n]+|[;][\s]*"#)]
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

    #[regex(r#"[a-zA-Z+*/<>?-][a-zA-Z0-9+*/<>?-]*"#)]
    Symbol,

    #[regex(r#""[^"]+""#)]
    String,

    #[regex(r#"'[*]{1}'"#)]
    Char,

    #[regex("[0-9]+")]
    Int,

    #[token("true")]
    True,

    #[token("false")]
    False,
}

#[derive(Clone, Copy, Debug)]
enum Macro {
    Quote,
    QuasiQuote,
    UnQuote,
    Splice,
}

#[derive(Clone, Debug, EnumAs, EnumIs)]
pub enum SExpr {
    List {
        span: Range<usize>,
        list: Vec<SExpr>,
    },
    Symbol {
        span: Range<usize>,
        symbol: String,
    },
    String {
        span: Range<usize>,
        string: String,
    },
    Char {
        span: Range<usize>,
        char: char,
    },
    Int {
        span: Range<usize>,
        int: i64,
    },
}

pub struct Reader<'a>(SpannedIter<'a, Token>);

impl<'a> Reader<'a> {
    pub fn new(input: &'a str) -> Self {
        Self(Lexer::new(input).spanned())
    }
}

impl<'a> Iterator for Reader<'a> {
    type Item = Result<SExpr, Error<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        read(&mut self.0)
    }
}

fn read<'a>(tokens: &mut SpannedIter<'a, Token>) -> Option<Result<SExpr, Error<'a>>> {
    Some(Ok(match tokens.next()? {
        (Ok(Token::LeftParen), _) => match read_list(tokens) {
            Ok(list) => list,
            Err(e) => return Some(Err(e)),
        },
        (Ok(Token::RightParen), _) => return Some(Err(Error::UnExpectedParen(tokens.remainder()))),
        (Ok(Token::Quote), _) => match quote(tokens, Macro::Quote) {
            Ok(quoted) => quoted,
            Err(e) => return Some(Err(e)),
        },
        (Ok(Token::QuasiQuote), _) => match quote(tokens, Macro::QuasiQuote) {
            Ok(quoted) => quoted,
            Err(e) => return Some(Err(e)),
        },
        (Ok(Token::UnQuote), _) => match quote(tokens, Macro::UnQuote) {
            Ok(quoted) => quoted,
            Err(e) => return Some(Err(e)),
        },
        (Ok(Token::Splice), _) => match quote(tokens, Macro::Splice) {
            Ok(quoted) => quoted,
            Err(e) => return Some(Err(e)),
        },
        (Ok(Token::Symbol), span) => SExpr::Symbol {
            span,
            symbol: tokens.slice().to_string(),
        },
        (Ok(Token::String), span) => SExpr::String {
            span,
            string: tokens.slice().to_string(),
        },
        (Ok(Token::Int), span) => SExpr::Int {
            span,
            int: tokens.slice().parse().unwrap(),
        },
        (Err(_), _) => return Some(Err(Error::Lexer(tokens.remainder()))),
        _ => todo!(),
    }))
}

fn read_list<'a>(tokens: &mut SpannedIter<'a, Token>) -> Result<SExpr, Error<'a>> {
    let mut list = Vec::new();
    let start = tokens.span().start;

    loop {
        match tokens.next() {
            Some((Ok(Token::LeftParen), _)) => list.push(read_list(tokens)?),
            Some((Ok(Token::RightParen), span)) => {
                return Ok(SExpr::List {
                    span: start..span.end,
                    list,
                })
            }
            Some((Ok(Token::Quote), _)) => list.push(quote(tokens, Macro::Quote)?),
            Some((Ok(Token::QuasiQuote), _)) => list.push(quote(tokens, Macro::QuasiQuote)?),
            Some((Ok(Token::UnQuote), _)) => list.push(quote(tokens, Macro::UnQuote)?),
            Some((Ok(Token::Splice), _)) => list.push(quote(tokens, Macro::Splice)?),
            Some((Ok(Token::Symbol), span)) => list.push(SExpr::Symbol {
                span,
                symbol: tokens.slice().to_string(),
            }),
            Some((Ok(Token::String), span)) => list.push(SExpr::String {
                span,
                string: tokens.slice().to_string(),
            }),
            Some((Ok(Token::Int), span)) => list.push(SExpr::Int {
                span,
                int: tokens.slice().parse().unwrap(),
            }),
            Some((Err(_), _)) => return Err(Error::Lexer(tokens.remainder())),
            None => return Err(Error::UnExpectedEof),
            _ => todo!(),
        }
    }
}

fn quote<'a>(tokens: &mut SpannedIter<'a, Token>, r#macro: Macro) -> Result<SExpr, Error<'a>> {
    let mut list = Vec::new();
    let start = tokens.span().start;

    list.push(SExpr::Symbol {
        span: start..start,
        symbol: match r#macro {
            Macro::Quote => "quote",
            Macro::QuasiQuote => "quasiquote",
            Macro::UnQuote => "unquote",
            Macro::Splice => "unquote-splice",
        }
        .to_string(),
    });

    list.push(match read(tokens) {
        Some(Ok(sexpr)) => sexpr,
        Some(Err(e)) => return Err(e),
        None => return Err(Error::UnExpectedEof),
    });

    Ok(SExpr::List {
        span: start..start,
        list,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple() {
        let input = "(a b c)";
        let mut reader = Reader::new(input);

        let list = match reader.next().unwrap().unwrap() {
            SExpr::List { list, .. } => list,
            _ => panic!(),
        };

        assert!(matches!(&list[0], SExpr::Symbol {  symbol, .. } if symbol == "a"));
        assert!(matches!(&list[1], SExpr::Symbol {  symbol, .. } if symbol == "b"));
        assert!(matches!(&list[2], SExpr::Symbol {  symbol, .. } if symbol == "c"));
    }

    #[test]
    fn test_nested() {
        let input = "(a b (c))";
        let mut reader = Reader::new(input);

        let list = reader
            .next()
            .unwrap()
            .unwrap()
            .as_list()
            .map(|(_, list)| list.clone())
            .unwrap();

        assert!(matches!(&list[0], SExpr::Symbol {  symbol, .. } if symbol == "a"));
        assert!(matches!(&list[1], SExpr::Symbol {  symbol, .. } if symbol == "b"));

        let inner_list = match &list[2] {
            SExpr::List { list, .. } => list,
            _ => panic!(),
        };

        assert!(matches!(&inner_list[0], SExpr::Symbol {  symbol, .. } if symbol == "c"));
    }

    #[test]
    fn test_quote() {
        let input = "('a)";
        let mut reader = Reader::new(input);

        let list = reader
            .next()
            .unwrap()
            .unwrap()
            .as_list()
            .map(|(_, list)| list.clone())
            .unwrap();

        let inner_list = &list[0].as_list().map(|(_, list)| list).unwrap();

        assert!(matches!(
            &inner_list[0],
            SExpr::Symbol { symbol, .. } if symbol == "quote"
        ));

        assert!(matches!(
            &inner_list[1],
            SExpr::Symbol { symbol, .. } if symbol == "a"
        ));
    }
}
