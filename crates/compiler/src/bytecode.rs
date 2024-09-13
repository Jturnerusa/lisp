mod optimizer;

use crate::tree::{self, Il};
use core::fmt;
use error::FileSpan;
use gc::Gc;
use vm::{OpCode, OpCodeTable};

#[derive(Clone, Debug)]
pub struct Error {
    il: Il,
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl std::error::Error for Error {}

pub fn compile(il: &Il, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    match il {
        Il::Lambda(lambda) => compile_lambda(lambda, opcodes),
        Il::Def(def) => compile_def(def, opcodes),
        Il::Set(set) => compile_set(set, opcodes),
        Il::SetBox(setbox) => compile_setbox(setbox, opcodes),
        Il::Box(r#box) => compile_box(r#box, opcodes),
        Il::UnBox(unbox) => compile_unbox(unbox, opcodes),
        Il::If(r#if) => compile_if(r#if, opcodes),
        Il::Cons(cons) => compile_cons(cons, opcodes),
        Il::Car(car) => compile_car(car, opcodes),
        Il::Cdr(cdr) => compile_cdr(cdr, opcodes),
        Il::VarRef(varref) => compile_varref(varref, opcodes),
        Il::Constant(constant) => compile_constant(constant, opcodes),
        Il::List(list) => compile_list(list, opcodes),
        Il::FnCall(fncall) => compile_fncall(fncall, opcodes),
        Il::ArithmeticOperation(op) => compile_arithmetic_operation(op, opcodes),
        Il::ComparisonOperation(op) => compile_comparison_operation(op, opcodes),
        Il::IsType(is_type) => compile_is_type(is_type, opcodes),
        Il::Apply(apply) => compile_apply(apply, opcodes),
        Il::Assert(assert) => compile_assert(assert, opcodes),
        Il::MapCreate(map_create) => compile_map_create(map_create, opcodes),
        Il::MapInsert(map_insert) => compile_map_insert(map_insert, opcodes),
        Il::MapRetrieve(map_retrieve) => compile_map_retrieve(map_retrieve, opcodes),
        Il::MapItems(map_items) => compile_map_items(map_items, opcodes),
        Il::MakeType(make_type) => compile_make_type(make_type, opcodes),
        Il::IfLet(if_let) => compile_if_let(if_let, opcodes),
        Il::LetRec(letrec) => compile_letrec(letrec, opcodes),
        _ => Ok(()),
    }
}

fn compile_varref(varref: &tree::VarRef, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    match varref {
        tree::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::GetLocal(*index), varref.span());
        }
        tree::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::GetUpValue(*index), varref.span());
        }
        tree::VarRef::Global { name, .. } => {
            opcodes.push(OpCode::GetGlobal(Gc::new(name.clone())), varref.span())
        }
    };

    Ok(())
}

fn compile_constant(
    constant: &tree::Constant,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    let op = match constant {
        tree::Constant::Symbol { symbol, .. } => OpCode::PushSymbol(Gc::new(symbol.clone())),
        tree::Constant::String { string, .. } => OpCode::PushString(Gc::new(string.clone())),
        tree::Constant::Char { char, .. } => OpCode::PushChar(*char),
        tree::Constant::Int { int, .. } => OpCode::PushInt(*int),
        tree::Constant::Bool { bool, .. } => OpCode::PushBool(*bool),
        tree::Constant::Nil { .. } => OpCode::PushNil,
    };

    opcodes.push(op, constant.span());

    Ok(())
}

fn compile_lambda(lambda: &tree::Lambda, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    let mut lambda_opcode_table = OpCodeTable::new();

    for expr in &lambda.body {
        compile(expr, &mut lambda_opcode_table)?;
    }

    lambda_opcode_table.push(OpCode::Return, lambda.span);

    let optimized_opcode_table = optimizer::optimize(&lambda_opcode_table);

    opcodes.push(
        OpCode::Lambda {
            arity: lambda.arity,
            body: Gc::new(optimized_opcode_table),
        },
        lambda.span,
    );

    for upvalue in &lambda.upvalues {
        opcodes.push(vm::OpCode::CreateUpValue(*upvalue), lambda.span);
    }

    Ok(())
}

fn compile_if(r#if: &tree::If, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    let mut then_opcodes = OpCodeTable::new();
    let mut else_opcodes = OpCodeTable::new();

    compile(&r#if.predicate, opcodes)?;
    compile(&r#if.then, &mut then_opcodes)?;
    compile(&r#if.r#else, &mut else_opcodes)?;

    opcodes.push(OpCode::Branch(then_opcodes.len() + 1), r#if.span);

    then_opcodes.push(OpCode::Jmp(else_opcodes.len() as isize), r#if.span);

    opcodes.append(then_opcodes);
    opcodes.append(else_opcodes);

    Ok(())
}

fn compile_def(def: &tree::Def, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&def.body, opcodes)?;

    opcodes.push(
        OpCode::DefGlobal(Gc::new(def.parameter.name.clone())),
        def.span,
    );

    Ok(())
}

fn compile_set(set: &tree::Set, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&set.body, opcodes)?;

    match &set.target {
        tree::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::SetLocal(*index), set.span);
        }
        tree::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::SetUpValue(*index), set.span);
        }
        tree::VarRef::Global { name, .. } => {
            opcodes.push(OpCode::SetGlobal(Gc::new(name.clone())), set.span);
        }
    };

    Ok(())
}

fn compile_setbox(setbox: &tree::SetBox, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&setbox.target, opcodes)?;
    compile(&setbox.body, opcodes)?;

    opcodes.push(OpCode::SetBox, setbox.span);

    Ok(())
}

fn compile_box(r#box: &tree::Box, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&r#box.body, opcodes)?;

    opcodes.push(OpCode::Box, r#box.span);

    Ok(())
}

fn compile_unbox(unbox: &tree::UnBox, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&unbox.body, opcodes)?;

    opcodes.push(OpCode::UnBox, unbox.span);

    Ok(())
}

fn compile_arithmetic_operation(
    arithmetic_op: &tree::ArithmeticOperation,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    compile(&arithmetic_op.lhs, opcodes)?;
    compile(&arithmetic_op.rhs, opcodes)?;

    opcodes.push(
        match arithmetic_op.operator {
            tree::ArithmeticOperator::Add => OpCode::Add,
            tree::ArithmeticOperator::Sub => OpCode::Sub,
            tree::ArithmeticOperator::Mul => OpCode::Mul,
            tree::ArithmeticOperator::Div => OpCode::Div,
        },
        arithmetic_op.span,
    );

    Ok(())
}

fn compile_comparison_operation(
    comparison_op: &tree::ComparisonOperation,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    compile(&comparison_op.lhs, opcodes)?;
    compile(&comparison_op.rhs, opcodes)?;

    opcodes.push(
        match comparison_op.operator {
            tree::ComparisonOperator::Eq => OpCode::Eq,
            tree::ComparisonOperator::Lt => OpCode::Lt,
            tree::ComparisonOperator::Gt => OpCode::Gt,
        },
        comparison_op.span,
    );

    Ok(())
}

fn compile_list(list: &tree::List, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    for expr in &list.exprs {
        compile(expr, opcodes)?;
    }

    opcodes.push(OpCode::List(list.exprs.len()), list.span);

    Ok(())
}

fn compile_fncall(fncall: &tree::FnCall, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&fncall.function, opcodes)?;

    for arg in &fncall.args {
        compile(arg, opcodes)?
    }

    opcodes.push(OpCode::Call(fncall.args.len()), fncall.span);

    Ok(())
}

fn compile_cons(cons: &tree::Cons, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&cons.lhs, opcodes)?;
    compile(&cons.rhs, opcodes)?;

    opcodes.push(OpCode::Cons, cons.span);

    Ok(())
}

fn compile_car(car: &tree::Car, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&car.body, opcodes)?;

    opcodes.push(OpCode::Car, car.span);

    Ok(())
}

fn compile_cdr(cdr: &tree::Cdr, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&cdr.body, opcodes)?;

    opcodes.push(OpCode::Cdr, cdr.span);

    Ok(())
}

fn compile_is_type(
    is_type: &tree::IsType,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    compile(&is_type.body, opcodes)?;

    let vm_type = match is_type.r#type {
        tree::IsTypeParameter::Function => vm::object::Type::Function,
        tree::IsTypeParameter::Cons => vm::object::Type::Cons,
        tree::IsTypeParameter::Symbol => vm::object::Type::Symbol,
        tree::IsTypeParameter::String => vm::object::Type::String,
        tree::IsTypeParameter::Char => vm::object::Type::Char,
        tree::IsTypeParameter::Int => vm::object::Type::Int,
        tree::IsTypeParameter::Bool => vm::object::Type::Bool,
        tree::IsTypeParameter::Nil => vm::object::Type::Nil,
    };

    opcodes.push(OpCode::IsType(vm_type), is_type.span);

    Ok(())
}

fn compile_apply(apply: &tree::Apply, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&apply.function, opcodes)?;
    compile(&apply.list, opcodes)?;

    opcodes.push(OpCode::Apply, apply.span);

    Ok(())
}

fn compile_assert(assert: &tree::Assert, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    compile(&assert.body, opcodes)?;

    opcodes.push(OpCode::Assert, assert.span);

    Ok(())
}

fn compile_map_create(
    map_create: &tree::MapCreate,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    opcodes.push(OpCode::MapCreate, map_create.span);

    Ok(())
}

fn compile_map_insert(
    map_insert: &tree::MapInsert,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    compile(&map_insert.map, opcodes)?;
    compile(&map_insert.key, opcodes)?;
    compile(&map_insert.value, opcodes)?;

    opcodes.push(OpCode::MapInsert, map_insert.span);

    Ok(())
}

fn compile_map_retrieve(
    map_retrieve: &tree::MapRetrieve,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    compile(&map_retrieve.map, opcodes)?;
    compile(&map_retrieve.key, opcodes)?;

    opcodes.push(OpCode::MapRetrieve, map_retrieve.span);

    Ok(())
}

fn compile_map_items(
    map_items: &tree::MapItems,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    compile(&map_items.map, opcodes)?;

    opcodes.push(OpCode::MapItems, map_items.span);

    Ok(())
}

fn compile_make_type(
    make_type: &tree::MakeType,
    opcodes: &mut OpCodeTable<FileSpan>,
) -> Result<(), Error> {
    opcodes.push(
        OpCode::PushSymbol(Gc::new(make_type.pattern.clone())),
        make_type.span,
    );

    if let Some(body) = &make_type.body {
        compile(body, opcodes)?;
    } else {
        opcodes.push(OpCode::PushNil, make_type.span);
    }

    opcodes.push(OpCode::Cons, make_type.span);

    Ok(())
}

fn compile_if_let(if_let: &tree::IfLet, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    let mut then = OpCodeTable::new();
    let mut r#else = OpCodeTable::new();

    compile(&if_let.body, opcodes)?;
    compile(&if_let.then, &mut then)?;
    compile(&if_let.r#else, &mut r#else)?;

    then.push(OpCode::Return, if_let.span);

    let else_length = r#else.len();

    let lambda = OpCode::Lambda {
        arity: vm::Arity::Nary(1),
        body: Gc::new(then),
    };

    opcodes.push(OpCode::Dup, if_let.span);

    opcodes.push(OpCode::Car, if_let.span);

    opcodes.push(
        OpCode::PushSymbol(Gc::new(if_let.pattern.clone())),
        if_let.span,
    );

    opcodes.push(OpCode::Eq, if_let.span);

    opcodes.push(OpCode::Branch(7), if_let.span);

    opcodes.push(lambda, if_let.span);

    opcodes.push(OpCode::Peek(1), if_let.span);

    opcodes.push(OpCode::Cdr, if_let.span);

    opcodes.push(OpCode::Call(1), if_let.span);

    opcodes.push(OpCode::Swap, if_let.span);

    opcodes.push(OpCode::Pop, if_let.span);

    opcodes.push(OpCode::Jmp(else_length as isize), if_let.span);

    opcodes.append(r#else);

    Ok(())
}

fn compile_letrec(letrec: &tree::LetRec, opcodes: &mut OpCodeTable<FileSpan>) -> Result<(), Error> {
    let mut lambda_opcodes = OpCodeTable::new();

    for (_, expr) in &letrec.bindings {
        compile(expr, &mut lambda_opcodes)?;
    }

    compile(&letrec.body, &mut lambda_opcodes)?;

    lambda_opcodes.push(OpCode::Return, letrec.span);

    opcodes.push(
        OpCode::Lambda {
            arity: vm::Arity::Nary(0),
            body: Gc::new(lambda_opcodes),
        },
        letrec.span,
    );

    opcodes.push(OpCode::Call(0), letrec.span);

    Ok(())
}
