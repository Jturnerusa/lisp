#![allow(dead_code)]

pub mod ast;
mod environment;

use std::{collections::HashMap, ops::Deref};

use thiserror::Error;

use value::Value;
use vm::{OpCode, Vm};

pub use ast::Ast;
use environment::{Environment, Variable};

#[derive(Debug, Error)]
pub enum Error {
    #[error("vm error: {0}")]
    Vm(#[from] vm::Error),
}

pub struct Compiler {
    environment: Environment,
    macros: HashMap<String, ast::Macro>,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
            macros: HashMap::new(),
        }
    }

    pub fn compile(
        &mut self,
        ast: &Ast,
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        match ast {
            Ast::Lambda(lambda) => self.compile_lambda(lambda, opcodes, vm),
            Ast::DefMacro(defmacro) => self.compile_defmacro(defmacro, vm),
            Ast::If(ast::If {
                predicate,
                then,
                els,
            }) => self.compile_if(predicate, then, els, opcodes, vm),
            Ast::Def(name, expr) => {
                self.compile_def(expr, || OpCode::DefGlobal(name.clone()), opcodes, vm)
            }
            Ast::Set(name, expr) => self.compile_set(name, expr, opcodes, vm),
            Ast::Add(a, b) => self.compile_binary_op(a, b, || OpCode::Add, opcodes, vm),
            Ast::Sub(a, b) => self.compile_binary_op(a, b, || OpCode::Sub, opcodes, vm),
            Ast::Mul(a, b) => self.compile_binary_op(a, b, || OpCode::Mul, opcodes, vm),
            Ast::Div(a, b) => self.compile_binary_op(a, b, || OpCode::Div, opcodes, vm),
            Ast::FnCall(list)
                if list
                    .first()
                    .and_then(|ast| ast.as_symbol())
                    .and_then(|symbol| self.macros.get(symbol))
                    .is_some() =>
            {
                self.eval_macro(
                    self.macros
                        .get(list.first().unwrap().as_symbol().unwrap())
                        .cloned()
                        .unwrap(),
                    &list[1..],
                    opcodes,
                    vm,
                )
            }
            Ast::FnCall(list) => self.compile_fncall(list.as_slice(), opcodes, vm),
            Ast::List(list) => self.compile_list(list.as_slice(), opcodes, vm),
            Ast::Symbol(symbol) => self.compile_symbol(symbol, opcodes),
            Ast::String(string) => {
                opcodes.push(OpCode::Push(Value::String(string.clone())));
                Ok(())
            }
            Ast::Int(i) => {
                opcodes.push(OpCode::Push(Value::Int(*i)));
                Ok(())
            }
            Ast::True => {
                opcodes.push(OpCode::Push(Value::True));
                Ok(())
            }
            Ast::Nil => {
                opcodes.push(OpCode::Push(Value::Nil));
                Ok(())
            }
            _ => todo!(),
        }
    }

    fn quote(&mut self, ast: &Ast, opcodes: &mut Vec<OpCode>) -> Result<(), Error> {
        match ast {
            Ast::
        }

        todo!()
    }

    fn compile_lambda(
        &mut self,
        lambda: &ast::Lambda,
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        self.environment
            .push_scope(lambda.parameters.iter().map(|s| s.as_str()));

        let mut lambda_opcodes = Vec::new();
        self.compile(&lambda.body, &mut lambda_opcodes, vm)?;
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

    fn compile_defmacro(&mut self, defmacro: &ast::Macro, vm: &mut Vm) -> Result<(), Error> {
        let mut opcodes = Vec::new();

        self.environment.push_scope(
            defmacro
                .parameters
                .iter()
                .map(|s| s.as_str())
                .chain(["&rest"]),
        );

        let mut defmacro_opcodes = Vec::new();
        self.compile(&defmacro.body, &mut defmacro_opcodes, vm)?;
        defmacro_opcodes.push(OpCode::Return);

        opcodes.push(OpCode::Lambda {
            arity: vm::Arity::Variadic,
            body: defmacro_opcodes,
            upvalues: Vec::new(),
        });

        opcodes.push(OpCode::DefGlobal(defmacro.name.clone()));

        vm.eval(opcodes.as_slice())?;

        self.environment.pop_scope();

        self.macros.insert(defmacro.name.clone(), defmacro.clone());

        Ok(())
    }

    fn compile_if(
        &mut self,
        predicate: &Ast,
        then: &Ast,
        els: &Ast,
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        self.compile(predicate, opcodes, vm)?;

        let mut then_ops = Vec::new();
        let mut els_ops = Vec::new();

        self.compile(then, &mut then_ops, vm)?;
        self.compile(els, &mut els_ops, vm)?;

        opcodes.push(OpCode::Branch(then_ops.len() + 1));
        opcodes.extend(then_ops);
        opcodes.push(OpCode::Jmp(els_ops.len().try_into().unwrap()));
        opcodes.extend(els_ops);

        Ok(())
    }

    fn compile_def(
        &mut self,
        expr: &Ast,
        opcode: impl Fn() -> OpCode,
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        self.compile(expr, opcodes, vm)?;
        opcodes.push(opcode());
        Ok(())
    }

    fn compile_set(
        &mut self,
        name: &str,
        expr: &Ast,
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        self.compile(expr, opcodes, vm)?;

        opcodes.push(if self.environment.is_global_scope() {
            OpCode::SetGlobal(name.to_string())
        } else {
            match self.environment.get(name) {
                Some(Variable::Local(index)) => OpCode::SetLocal(index),
                Some(Variable::Upvalue(index)) => OpCode::SetUpValue(index),
                None => OpCode::SetGlobal(name.to_string()),
            }
        });

        Ok(())
    }

    fn compile_binary_op(
        &mut self,
        a: &Ast,
        b: &Ast,
        op: impl Fn() -> OpCode,
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        self.compile(a, opcodes, vm)?;
        self.compile(b, opcodes, vm)?;
        opcodes.push(op());
        Ok(())
    }

    fn compile_fncall(
        &mut self,
        exprs: &[Ast],
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        let parameter_count = exprs.len() - 1;

        for expr in exprs {
            self.compile(expr, opcodes, vm)?;
        }

        opcodes.push(OpCode::Call(parameter_count));

        Ok(())
    }

    fn compile_list(
        &mut self,
        exprs: &[Ast],
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        for expr in exprs {
            self.compile(expr, opcodes, vm)?;
        }

        opcodes.push(OpCode::List(exprs.len()));

        Ok(())
    }

    fn eval_macro(
        &mut self,
        defmacro: ast::Macro,
        exprs: &[Ast],
        opcodes: &mut Vec<OpCode>,
        vm: &mut Vm,
    ) -> Result<(), Error> {
        let mut eval_defmacro_opcodes = Vec::new();

        eval_defmacro_opcodes.push(OpCode::GetGlobal(defmacro.name.clone()));

        for expr in exprs {
            self.compile(expr, &mut eval_defmacro_opcodes, vm)?;
        }

        eval_defmacro_opcodes.push(OpCode::List(exprs.len() - defmacro.parameters.len()));
        eval_defmacro_opcodes.push(OpCode::Call(exprs.len() + 1));

        let ret = vm.eval(&eval_defmacro_opcodes)?.unwrap();

        let val = Value::try_from(ret.borrow().deref()).unwrap();
        let ast = Ast::parse(&val).unwrap();

        self.compile(&ast, opcodes, vm)?;

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

    fn compile_value(
        &mut self,
        op: impl Fn() -> OpCode,
        opcodes: &mut Vec<OpCode>,
    ) -> Result<(), Error> {
        opcodes.push(op());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compile(input: &str) -> Result<Vec<OpCode>, Error> {
        let mut reader = reader::Reader::new(input);
        let mut vm = Vm::new();
        let read = reader.next().unwrap().unwrap();
        let ast = crate::Ast::parse(&read).unwrap();
        let mut opcodes = Vec::new();
        let mut compiler = Compiler::new();
        compiler.compile(&ast, &mut opcodes, &mut vm)?;
        Ok(opcodes)
    }

    #[test]
    fn test_compile_add() {
        let input = "(+ 1 1)";
        let opcodes = compile(input).unwrap();

        assert!(matches!(&opcodes[0], OpCode::Push(Value::Int(1))));
        assert!(matches!(&opcodes[1], OpCode::Push(Value::Int(1))));
        assert!(matches!(&opcodes[2], OpCode::Add));
    }

    #[test]
    fn test_compile_lambda() {
        let input = "(lambda (a) (+ a b))";
        let opcodes = compile(input).unwrap();
        let (parameters, body, upvalues) = opcodes[0].as_lambda().unwrap();

        assert!(matches!(parameters, vm::Arity::Nary(1)));
        assert!(matches!(&body[0], OpCode::GetLocal(0)));
        assert!(matches!(&body[1], OpCode::GetGlobal(global) if global == "b"));
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

    #[test]
    fn test_compile_def() {
        let input = "(def x 1)";
        let opcodes = compile(input).unwrap();

        assert!(matches!(&opcodes[0], OpCode::Push(Value::Int(1))));

        assert!(matches!(
            &opcodes[1],
            OpCode::DefGlobal(global) if global == "x"
        ));
    }

    #[test]
    fn test_compile_set() {
        let input = "(lambda (x) (set x 1))";
        let opcodes = compile(input).unwrap();
        let (_, body, _) = &opcodes[0].as_lambda().unwrap();

        assert!(matches!(&body[0], OpCode::Push(Value::Int(1))));
        assert!(matches!(&body[1], OpCode::SetLocal(0)));
    }

    #[test]
    fn test_compile_if() {
        let input = "(if (= 1 1) (+ 1 1) (+ 2 2))";
        let opcodes = compile(input).unwrap();

        assert!(matches!(&opcodes[4], OpCode::Branch(4)));
        assert!(matches!(&opcodes[8], OpCode::Jmp(3)));
    }

    #[test]
    fn test_compile_quote() {
        let input = "(quote (a b c))";
        let opcodes = compile(input).unwrap();

        assert!(matches!(&opcodes[0], OpCode::Push(Value::Cons(_))));
    }
}
