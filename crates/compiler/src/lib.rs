#![allow(dead_code)]

mod ast;
mod environment;

use std::iter::ExactSizeIterator;

use value::Value;
use vm::OpCode;

use ast::Ast;
use environment::{Environment, Variable};

#[derive(Debug)]
pub enum Error {}

pub struct Compiler {
    environment: Environment,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
        }
    }

    pub fn compile(&mut self, ast: &Ast, opcodes: &mut Vec<OpCode>) -> Result<(), Error> {
        match ast {
            Ast::Lambda(lambda) => self.compile_lambda(lambda, opcodes),
            Ast::Add(args) => self.compile_add(args.iter(), opcodes),
            Ast::Sub(args) => self.compile_sub(args.iter(), opcodes),
            Ast::Mul(args) => self.compile_mul(args.iter(), opcodes),
            Ast::Div(args) => self.compile_div(args.iter(), opcodes),
            Ast::List(list) => self.compile_list(list.iter(), opcodes),
            Ast::Symbol(symbol) => self.compile_symbol(symbol, opcodes),
            Ast::String(string) => self.compile_string(string, opcodes),
            Ast::Int(int) => self.compile_int(*int, opcodes),
            _ => todo!(),
        }
    }

    fn compile_lambda(
        &mut self,
        lambda: &ast::Lambda,
        opcodes: &mut Vec<OpCode>,
    ) -> Result<(), Error> {
        self.environment
            .push_scope(lambda.parameters.iter().map(|s| s.as_str()));

        let mut lambda_opcodes = Vec::new();
        self.compile(&lambda.body, &mut lambda_opcodes)?;
        lambda_opcodes.push(OpCode::Return);

        opcodes.push(OpCode::Lambda {
            arity: match lambda.parameters.len() {
                0 => vm::Arity::Nullary,
                i => vm::Arity::Nary(i),
            },
            body: lambda_opcodes,
            upvalues: self.environment.upvalues().collect(),
        });

        self.environment.pop_scope();

        Ok(())
    }

    fn compile_add<'a>(
        &mut self,
        args: impl ExactSizeIterator<Item = &'a Ast>,
        opcodes: &mut Vec<OpCode>,
    ) -> Result<(), Error> {
        let parameter_count = args.len();

        for arg in args {
            self.compile(arg, opcodes)?;
        }

        opcodes.push(OpCode::Add(parameter_count));

        Ok(())
    }

    fn compile_sub<'a>(
        &mut self,
        args: impl ExactSizeIterator<Item = &'a Ast>,
        opcodes: &mut Vec<OpCode>,
    ) -> Result<(), Error> {
        let parameter_count = args.len();

        for arg in args {
            self.compile(arg, opcodes)?;
        }

        opcodes.push(OpCode::Sub(parameter_count));

        Ok(())
    }

    fn compile_mul<'a>(
        &mut self,
        args: impl ExactSizeIterator<Item = &'a Ast>,
        opcodes: &mut Vec<OpCode>,
    ) -> Result<(), Error> {
        let parameter_count = args.len();

        for arg in args {
            self.compile(arg, opcodes)?;
        }

        opcodes.push(OpCode::Mul(parameter_count));

        Ok(())
    }

    fn compile_div<'a>(
        &mut self,
        args: impl ExactSizeIterator<Item = &'a Ast>,
        opcodes: &mut Vec<OpCode>,
    ) -> Result<(), Error> {
        let parameter_count = args.len();

        for arg in args {
            self.compile(arg, opcodes)?;
        }

        opcodes.push(OpCode::Div(parameter_count));

        Ok(())
    }

    fn compile_list<'a>(
        &mut self,
        list: impl ExactSizeIterator<Item = &'a Ast>,
        opcodes: &mut Vec<OpCode>,
    ) -> Result<(), Error> {
        let parameter_count = dbg!(list.len()) - 1;

        for element in list {
            self.compile(element, opcodes)?;
        }

        opcodes.push(OpCode::Call(parameter_count));

        Ok(())
    }

    fn compile_symbol(&mut self, symbol: &str, opcodes: &mut Vec<OpCode>) -> Result<(), Error> {
        opcodes.push(if self.environment.is_global_scope() {
            OpCode::GetGlobal(symbol.to_string())
        } else {
            self.environment.insert(symbol);
            match self.environment.get(symbol) {
                Some(Variable::Local(index)) => OpCode::GetLocal(index),
                Some(Variable::Upvalue(index)) => OpCode::GetUpValue(index),
                None => OpCode::GetGlobal(symbol.to_string()),
            }
        });

        Ok(())
    }

    fn compile_string(&mut self, string: &str, opcodes: &mut Vec<OpCode>) -> Result<(), Error> {
        opcodes.push(OpCode::Push(Value::String(string.to_string())));
        Ok(())
    }

    fn compile_int(&mut self, int: i64, opcodes: &mut Vec<OpCode>) -> Result<(), Error> {
        opcodes.push(OpCode::Push(Value::Int(int)));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compile(input: &str) -> Result<Vec<OpCode>, Error> {
        let mut reader = reader::Reader::new(input);
        let read = reader.next().unwrap().unwrap();
        let ast = crate::ast::parse(&read).unwrap();
        let mut opcodes = Vec::new();
        let mut compiler = Compiler::new();
        compiler.compile(&ast, &mut opcodes)?;
        Ok(opcodes)
    }

    #[test]
    fn test_compile_add() {
        let input = "(+ 1 1)";
        let opcodes = compile(input).unwrap();

        assert!(matches!(&opcodes[0], OpCode::Push(Value::Int(1))));
        assert!(matches!(&opcodes[1], OpCode::Push(Value::Int(1))));
        assert!(matches!(&opcodes[2], OpCode::Add(2)));
    }

    #[test]
    fn test_compile_lambda() {
        let input = "(lambda (a b) (+ a b c))";
        let opcodes = compile(input).unwrap();
        let (body, upvalues) = opcodes[0].as_lambda().unwrap();

        assert!(matches!(&body[0], OpCode::GetLocal(0)));
        assert!(matches!(&body[1], OpCode::GetLocal(1)));
        assert!(matches!(&body[2], OpCode::GetGlobal(global) if global.as_str() == "c"));
        assert!(upvalues.is_empty());
    }

    #[test]
    fn test_compile_list() {
        let input = "(f a b)";
        let opcodes = compile(input).unwrap();

        assert!(matches!(&opcodes[0], OpCode::GetGlobal(global) if global.as_str() == "f"));
        assert!(matches!(&opcodes[1], OpCode::GetGlobal(global) if global.as_str() == "a"));
        assert!(matches!(&opcodes[2], OpCode::GetGlobal(global) if global.as_str() == "b"));
        assert!(matches!(&opcodes[3], OpCode::Call(2)));
    }
}
