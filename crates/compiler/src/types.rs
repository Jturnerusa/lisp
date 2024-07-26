use crate::ast;
use std::collections::BTreeSet;

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
