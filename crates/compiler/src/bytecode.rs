use core::fmt;
use std::rc::Rc;

use crate::{
    il::{self, Il},
    xxhash,
};

use gc::Gc;
use identity_hasher::IdentityMap;
use reader::Sexpr;
use vm::{OpCode, OpCodeTable};

type ConstantMap<D> = IdentityMap<u64, vm::Constant<D>>;

#[derive(Clone, Debug)]
pub struct Error<'a> {
    il: &'a Il<'a>,
    message: String,
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl<'a> std::error::Error for Error<'a> {}

pub fn compile<'a, 'b>(
    il: &'a Il<'a>,
    opcodes: &'b mut OpCodeTable<&'a Sexpr<'a>>,
    constants: &'b mut ConstantMap<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    match il {
        Il::Lambda(lambda) => compile_lambda(lambda, opcodes, constants),
        Il::Def(def) => compile_def(def, opcodes, constants),
        Il::VarRef(varref) => compile_varref(varref, opcodes),
        Il::Constant(constant) => compile_constant(constant, opcodes, constants),
        Il::List(list) => compile_list(list, opcodes, constants),
        Il::FnCall(fncall) => compile_fncall(fncall, opcodes, constants),
        Il::ArithmeticOperation(op) => compile_arithmetic_operation(op, opcodes, constants),
        _ => todo!("{il:?}"),
    }
}

fn compile_varref<'a>(
    varref: &'a il::VarRef<'a>,
    opcodes: &mut OpCodeTable<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    let op = match varref {
        il::VarRef::Local { index, .. } => OpCode::GetLocal(*index),
        il::VarRef::UpValue { index, .. } => OpCode::GetUpValue(*index),
        il::VarRef::Global { name, .. } => {
            OpCode::GetGlobal(xxhash(vm::Constant::Symbol::<&'a Sexpr<'a>>(Gc::new(
                name.clone(),
            ))))
        }
    };

    opcodes.push(op, varref.source().source_sexpr());

    Ok(())
}

fn compile_constant<'a, 'b>(
    constant: &'a il::Constant<'a>,
    opcodes: &'b mut OpCodeTable<&'a Sexpr<'a>>,
    constants: &'b mut ConstantMap<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    let op = match constant {
        il::Constant::Symbol { symbol, .. } => {
            let constant = vm::Constant::Symbol(Gc::new(symbol.clone()));
            let hash = xxhash(&constant);
            constants.insert(hash, constant);
            OpCode::PushSymbol(hash)
        }
        il::Constant::String { string, .. } => {
            let constant = vm::Constant::String(Gc::new(string.clone()));
            let hash = xxhash(&constant);
            constants.insert(hash, constant);
            OpCode::PushString(hash)
        }
        il::Constant::Char { char, .. } => OpCode::PushChar(*char),
        il::Constant::Int { int, .. } => OpCode::PushInt(*int),
        il::Constant::Bool { bool, .. } => OpCode::PushBool(*bool),
        il::Constant::Nil { .. } => OpCode::PushNil,
    };

    opcodes.push(op, constant.source().source_sexpr());

    Ok(())
}

fn compile_lambda<'a, 'b>(
    lambda: &'a il::Lambda<'a>,
    opcodes: &'b mut OpCodeTable<&'a Sexpr<'a>>,
    constants: &'b mut ConstantMap<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    let mut lambda_opcode_table = OpCodeTable::new();

    for expr in &lambda.body {
        compile(expr, &mut lambda_opcode_table, constants)?;
    }

    lambda_opcode_table.push(OpCode::Return, lambda.source.source_sexpr());

    let lambda_opcode_table_constant = vm::Constant::Opcodes(Rc::new(lambda_opcode_table));
    let lambda_opcode_table_hash = xxhash(&lambda_opcode_table_constant);

    constants.insert(lambda_opcode_table_hash, lambda_opcode_table_constant);

    opcodes.push(
        vm::OpCode::Lambda {
            arity: lambda.arity,
            body: lambda_opcode_table_hash,
        },
        lambda.source.source_sexpr(),
    );

    for upvalue in &lambda.upvalues {
        opcodes.push(
            vm::OpCode::CreateUpValue(*upvalue),
            lambda.source.source_sexpr(),
        );
    }

    Ok(())
}

fn compile_def<'a, 'b>(
    def: &'a il::Def<'a>,
    opcodes: &'b mut OpCodeTable<&'a Sexpr<'a>>,
    constants: &'b mut ConstantMap<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    let constant: vm::Constant<&'a Sexpr<'a>> =
        vm::Constant::Symbol(Gc::new(def.parameter.name.clone()));
    let hash = xxhash(&constant);

    compile(&def.body, opcodes, constants)?;

    constants.insert(hash, constant);

    opcodes.push(OpCode::DefGlobal(hash), def.source.source_sexpr());

    Ok(())
}

fn compile_arithmetic_operation<'a, 'b>(
    arithmetic_op: &'a il::ArithmeticOperation<'a>,
    opcodes: &'b mut OpCodeTable<&'a Sexpr<'a>>,
    constants: &'b mut ConstantMap<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    compile(&arithmetic_op.lhs, opcodes, constants)?;
    compile(&arithmetic_op.rhs, opcodes, constants)?;

    opcodes.push(
        match arithmetic_op.operator {
            il::ArithmeticOperator::Add => OpCode::Add,
            il::ArithmeticOperator::Sub => OpCode::Sub,
            il::ArithmeticOperator::Mul => OpCode::Mul,
            il::ArithmeticOperator::Div => OpCode::Div,
        },
        arithmetic_op.source.source_sexpr(),
    );

    Ok(())
}

fn compile_list<'a, 'b>(
    list: &'a il::List<'a>,
    opcodes: &'b mut OpCodeTable<&'a Sexpr<'a>>,
    constants: &'b mut ConstantMap<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    for expr in &list.exprs {
        compile(expr, opcodes, constants)?;
    }

    opcodes.push(OpCode::List(list.exprs.len()), list.source.source_sexpr());

    Ok(())
}

fn compile_fncall<'a, 'b>(
    fncall: &'a il::FnCall<'a>,
    opcodes: &'b mut OpCodeTable<&'a Sexpr<'a>>,
    constants: &'b mut ConstantMap<&'a Sexpr<'a>>,
) -> Result<(), Error<'a>> {
    compile(&fncall.function, opcodes, constants)?;

    for arg in &fncall.args {
        compile(arg, opcodes, constants)?
    }

    opcodes.push(
        OpCode::Call(fncall.args.len()),
        fncall.source.source_sexpr(),
    );

    Ok(())
}
