mod optimizer;

use crate::tree::{self, Il};
use core::fmt;
use gc::Gc;
use reader::Sexpr;
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

pub fn compile(il: &Il, opcodes: &mut OpCodeTable<&'static Sexpr<'static>>) -> Result<(), Error> {
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
    }
}

fn compile_varref(
    varref: &tree::VarRef,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    match varref {
        tree::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::GetLocal(*index), varref.source().source_sexpr());
        }
        tree::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::GetUpValue(*index), varref.source().source_sexpr());
        }
        tree::VarRef::Global { name, .. } => opcodes.push(
            OpCode::GetGlobal(Gc::new(name.clone())),
            varref.source().source_sexpr(),
        ),
    };

    Ok(())
}

fn compile_constant(
    constant: &tree::Constant,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    let op = match constant {
        tree::Constant::Symbol { symbol, .. } => OpCode::PushSymbol(Gc::new(symbol.clone())),
        tree::Constant::String { string, .. } => OpCode::PushString(Gc::new(string.clone())),
        tree::Constant::Char { char, .. } => OpCode::PushChar(*char),
        tree::Constant::Int { int, .. } => OpCode::PushInt(*int),
        tree::Constant::Bool { bool, .. } => OpCode::PushBool(*bool),
        tree::Constant::Nil { .. } => OpCode::PushNil,
    };

    opcodes.push(op, constant.source().source_sexpr());

    Ok(())
}

fn compile_lambda(
    lambda: &tree::Lambda,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    let mut lambda_opcode_table = OpCodeTable::new();

    for expr in &lambda.body {
        compile(expr, &mut lambda_opcode_table)?;
    }

    lambda_opcode_table.push(OpCode::Return, lambda.source.source_sexpr());

    let optimized_opcode_table = optimizer::optimize(&lambda_opcode_table);

    opcodes.push(
        OpCode::Lambda {
            arity: lambda.arity,
            body: Gc::new(optimized_opcode_table),
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

fn compile_if(
    r#if: &tree::If,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    let mut then_opcodes = OpCodeTable::new();
    let mut else_opcodes = OpCodeTable::new();

    compile(&r#if.predicate, opcodes)?;
    compile(&r#if.then, &mut then_opcodes)?;
    compile(&r#if.r#else, &mut else_opcodes)?;

    opcodes.push(
        OpCode::Branch(then_opcodes.len() + 1),
        r#if.source.source_sexpr(),
    );

    then_opcodes.push(
        OpCode::Jmp(else_opcodes.len() as isize),
        r#if.source.source_sexpr(),
    );

    opcodes.append(then_opcodes);
    opcodes.append(else_opcodes);

    Ok(())
}

fn compile_def(
    def: &tree::Def,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&def.body, opcodes)?;

    opcodes.push(
        OpCode::DefGlobal(Gc::new(def.parameter.name.clone())),
        def.source.source_sexpr(),
    );

    Ok(())
}

fn compile_set(
    set: &tree::Set,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&set.body, opcodes)?;

    match &set.target {
        tree::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::SetLocal(*index), set.source.source_sexpr());
        }
        tree::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::SetUpValue(*index), set.source.source_sexpr());
        }
        tree::VarRef::Global { name, .. } => {
            opcodes.push(
                OpCode::SetGlobal(Gc::new(name.clone())),
                set.source.source_sexpr(),
            );
        }
    };

    Ok(())
}

fn compile_setbox(
    setbox: &tree::SetBox,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&setbox.target, opcodes)?;
    compile(&setbox.body, opcodes)?;

    opcodes.push(OpCode::SetBox, setbox.source.source_sexpr());

    Ok(())
}

fn compile_box(
    r#box: &tree::Box,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&r#box.body, opcodes)?;

    opcodes.push(OpCode::Box, r#box.source.source_sexpr());

    Ok(())
}

fn compile_unbox(
    unbox: &tree::UnBox,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&unbox.body, opcodes)?;

    opcodes.push(OpCode::UnBox, unbox.source.source_sexpr());

    Ok(())
}

fn compile_arithmetic_operation(
    arithmetic_op: &tree::ArithmeticOperation,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
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
        arithmetic_op.source.source_sexpr(),
    );

    Ok(())
}

fn compile_comparison_operation(
    comparison_op: &tree::ComparisonOperation,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&comparison_op.lhs, opcodes)?;
    compile(&comparison_op.rhs, opcodes)?;

    opcodes.push(
        match comparison_op.operator {
            tree::ComparisonOperator::Eq => OpCode::Eq,
            tree::ComparisonOperator::Lt => OpCode::Lt,
            tree::ComparisonOperator::Gt => OpCode::Gt,
        },
        comparison_op.source.source_sexpr(),
    );

    Ok(())
}

fn compile_list(
    list: &tree::List,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    for expr in &list.exprs {
        compile(expr, opcodes)?;
    }

    opcodes.push(OpCode::List(list.exprs.len()), list.source.source_sexpr());

    Ok(())
}

fn compile_fncall(
    fncall: &tree::FnCall,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&fncall.function, opcodes)?;

    for arg in &fncall.args {
        compile(arg, opcodes)?
    }

    opcodes.push(
        OpCode::Call(fncall.args.len()),
        fncall.source.source_sexpr(),
    );

    Ok(())
}

fn compile_cons(
    cons: &tree::Cons,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&cons.lhs, opcodes)?;
    compile(&cons.rhs, opcodes)?;

    opcodes.push(OpCode::Cons, cons.source.source_sexpr());

    Ok(())
}

fn compile_car(
    car: &tree::Car,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&car.body, opcodes)?;

    opcodes.push(OpCode::Car, car.source.source_sexpr());

    Ok(())
}

fn compile_cdr(
    cdr: &tree::Cdr,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&cdr.body, opcodes)?;

    opcodes.push(OpCode::Cdr, cdr.source.source_sexpr());

    Ok(())
}

fn compile_is_type(
    is_type: &tree::IsType,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
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

    opcodes.push(OpCode::IsType(vm_type), is_type.source.source_sexpr());

    Ok(())
}

fn compile_apply(
    apply: &tree::Apply,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&apply.function, opcodes)?;
    compile(&apply.list, opcodes)?;

    opcodes.push(OpCode::Apply, apply.source.source_sexpr());

    Ok(())
}

fn compile_assert(
    assert: &tree::Assert,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&assert.body, opcodes)?;

    opcodes.push(OpCode::Assert, assert.source.source_sexpr());

    Ok(())
}

fn compile_map_create(
    map_create: &tree::MapCreate,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    opcodes.push(OpCode::MapCreate, map_create.source.source_sexpr());

    Ok(())
}

fn compile_map_insert(
    map_insert: &tree::MapInsert,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&map_insert.map, opcodes)?;
    compile(&map_insert.key, opcodes)?;
    compile(&map_insert.value, opcodes)?;

    opcodes.push(OpCode::MapInsert, map_insert.source.source_sexpr());

    Ok(())
}

fn compile_map_retrieve(
    map_retrieve: &tree::MapRetrieve,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&map_retrieve.map, opcodes)?;
    compile(&map_retrieve.key, opcodes)?;

    opcodes.push(OpCode::MapRetrieve, map_retrieve.source.source_sexpr());

    Ok(())
}

fn compile_map_items(
    map_items: &tree::MapItems,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&map_items.map, opcodes)?;

    opcodes.push(OpCode::MapItems, map_items.source.source_sexpr());

    Ok(())
}
