use nom::branch;
use nom::bytes::complete as bytes;
use nom::combinator;
use nom::sequence;

type Result<'a, I = &'a str, O = I> = nom::IResult<I, O>;

const SYMBOL_ALLOWED_CHARS: &[char] = &[
    '!', '@', '#', '$', '%', '^', '&', '*', '-', '_', '=', '+', '.', '/', '>', '<', '?',
];

#[derive(Clone, Copy, Debug)]
pub enum Node<'a> {
    LeftParen,
    RightParen,
    Quote,
    String(&'a str),
    Symbol(&'a str),
    Int(&'a str),
}

#[derive(Clone, Copy, Debug)]
pub struct Parser<'a> {
    data: &'a str,
}

fn parse_node(input: &str) -> Result<&str, Node> {
    sequence::preceded(
        combinator::opt(comment),
        sequence::delimited(
            combinator::opt(whitespace),
            branch::alt((left_paren, right_paren, quote, string, symbol, int)),
            combinator::opt(whitespace),
        ),
    )(input)
}

fn left_paren(input: &str) -> Result<&str, Node> {
    combinator::map(bytes::tag("("), |_| Node::LeftParen)(input)
}

fn right_paren(input: &str) -> Result<&str, Node> {
    combinator::map(bytes::tag(")"), |_| Node::RightParen)(input)
}

fn quote(input: &str) -> Result<&str, Node> {
    combinator::map(bytes::tag("'"), |_| Node::Quote)(input)
}

fn string(input: &str) -> Result<&str, Node> {
    combinator::map(
        sequence::delimited(
            bytes::tag(r#"""#),
            bytes::is_not(r#"""#),
            bytes::tag(r#"""#),
        ),
        Node::String,
    )(input)
}

fn symbol(input: &str) -> Result<&str, Node> {
    combinator::map(
        combinator::recognize(sequence::preceded(
            bytes::take_while_m_n(1, 1, |c: char| {
                c.is_alphabetic()
                    || SYMBOL_ALLOWED_CHARS
                        .iter()
                        .cloned()
                        .any(|allowed| c == allowed)
            }),
            bytes::take_while(|c: char| {
                c.is_alphanumeric()
                    || SYMBOL_ALLOWED_CHARS
                        .iter()
                        .cloned()
                        .any(|allowed| c == allowed)
            }),
        )),
        Node::Symbol,
    )(input)
}

fn int(input: &str) -> Result<&str, Node> {
    combinator::map(bytes::take_while1(|c: char| c.is_ascii_digit()), Node::Int)(input)
}

fn whitespace(input: &str) -> Result {
    bytes::take_while1(|c: char| c.is_whitespace())(input)
}

fn comment(input: &str) -> Result {
    sequence::terminated(bytes::tag(";"), bytes::take_while1(|c: char| c != '\n'))(input)
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { data: input }
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = std::result::Result<Node<'a>, &'a str>;
    fn next(&mut self) -> Option<Self::Item> {
        if !self.data.is_empty() {
            match parse_node(self.data) {
                Ok((rest, node)) => {
                    self.data = rest;
                    Some(Ok(node))
                }
                Err(nom::Err::Error(e) | nom::Err::Failure(e)) => Some(Err(e.input)),
                _ => unreachable!(),
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simple() {
        const INPUT: &str = r#"(hello "world" 1)"#;
        let mut parser = Parser::new(INPUT);
        assert!(matches!(parser.next().unwrap().unwrap(), Node::LeftParen));
        assert!(matches!(
            parser.next().unwrap().unwrap(),
            Node::Symbol("hello")
        ));
        assert!(matches!(
            parser.next().unwrap().unwrap(),
            Node::String("world")
        ));
        assert!(matches!(parser.next().unwrap().unwrap(), Node::Int("1")));
        assert!(matches!(parser.next().unwrap().unwrap(), Node::RightParen));
        assert!(parser.next().is_none());
    }

    #[test]
    fn test_comment() {
        let input = "; comment
                     (hello world)";
        let mut parser = Parser::new(input);
        assert!(matches!(parser.next().unwrap().unwrap(), Node::LeftParen));
    }
}
