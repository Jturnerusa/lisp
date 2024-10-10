mod optimizer;

use crate::tree::{self, Il};
use core::fmt;
use error::FileSpan;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use vm::{Constant, OpCode, OpCodeTable};

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

pub fn compile(
    il: &Il,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    match il {
        Il::Lambda(lambda) => compile_lambda(lambda, opcodes, constants),
        Il::Def(def) => compile_def(def, opcodes, constants),
        Il::Set(set) => compile_set(set, opcodes, constants),
        Il::SetBox(setbox) => compile_setbox(setbox, opcodes, constants),
        Il::Box(r#box) => compile_box(r#box, opcodes, constants),
        Il::UnBox(unbox) => compile_unbox(unbox, opcodes, constants),
        Il::If(r#if) => compile_if(r#if, opcodes, constants),
        Il::Cons(cons) => compile_cons(cons, opcodes, constants),
        Il::Car(car) => compile_car(car, opcodes, constants),
        Il::Cdr(cdr) => compile_cdr(cdr, opcodes, constants),
        Il::VarRef(varref) => compile_varref(varref, opcodes, constants),
        Il::Constant(constant) => compile_constant(constant, opcodes, constants),
        Il::List(list) => compile_list(list, opcodes, constants),
        Il::FnCall(fncall) => compile_fncall(fncall, opcodes, constants),
        Il::ArithmeticOperation(op) => compile_arithmetic_operation(op, opcodes, constants),
        Il::FloatOperation(op) => compile_float_operation(op, opcodes, constants),
        Il::ComparisonOperation(op) => compile_comparison_operation(op, opcodes, constants),
        Il::IsType(is_type) => compile_is_type(is_type, opcodes, constants),
        Il::Apply(apply) => compile_apply(apply, opcodes, constants),
        Il::Assert(assert) => compile_assert(assert, opcodes, constants),
        Il::MapCreate(map_create) => compile_map_create(map_create, opcodes),
        Il::MapInsert(map_insert) => compile_map_insert(map_insert, opcodes, constants),
        Il::MapRetrieve(map_retrieve) => compile_map_retrieve(map_retrieve, opcodes, constants),
        Il::MapItems(map_items) => compile_map_items(map_items, opcodes, constants),
        Il::MakeType(make_type) => compile_make_type(make_type, opcodes, constants),
        Il::IfLet(if_let) => compile_if_let(if_let, opcodes, constants),
        Il::LetRec(letrec) => compile_letrec(letrec, opcodes, constants),
        Il::MakeStruct(make_struct) => compile_make_struct(make_struct, opcodes, constants),
        Il::GetField(field) => compile_get_field(field, opcodes, constants),
        _ => Ok(()),
    }
}

fn compile_varref(
    varref: &tree::VarRef,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    match varref {
        tree::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::GetLocal(*index), varref.span());
        }
        tree::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::GetUpValue(*index), varref.span());
        }
        tree::VarRef::Global { name, .. } => {
            let constant = Constant::Symbol(Rc::new(name.clone()));
            let hash = hash_constant(&constant);
            constants.push(constant);
            opcodes.push(OpCode::GetGlobal(hash), varref.span())
        }
    };

    Ok(())
}

fn compile_constant(
    constant: &tree::Constant,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    let op = match constant {
        tree::Constant::Symbol { symbol, .. } => {
            let constant = Constant::Symbol(Rc::new(symbol.clone()));
            let hash = hash_constant(&constant);
            constants.push(constant);
            OpCode::PushSymbol(hash)
        }
        tree::Constant::String { string, .. } => {
            let constant = Constant::String(Rc::new(string.clone()));
            let hash = hash_constant(&constant);
            constants.push(constant);
            OpCode::PushString(hash)
        }
        tree::Constant::Char { char, .. } => OpCode::PushChar(*char),
        tree::Constant::Int { int, .. } => OpCode::PushInt(*int),
        tree::Constant::Float { float, .. } => OpCode::PushFloat(*float),
        tree::Constant::Bool { bool, .. } => OpCode::PushBool(*bool),
        tree::Constant::Nil { .. } => OpCode::PushNil,
    };

    opcodes.push(op, constant.span());

    Ok(())
}

fn compile_lambda(
    lambda: &tree::Lambda,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    let mut lambda_opcode_table = OpCodeTable::new();

    for expr in &lambda.body {
        compile(expr, &mut lambda_opcode_table, constants)?;
    }

    lambda_opcode_table.push(OpCode::Return, lambda.span);

    let optimized_opcode_table = optimizer::optimize(&lambda_opcode_table);

    let constant = Constant::OpCodeTable(Rc::new(optimized_opcode_table));
    let hash = hash_constant(&constant);
    constants.push(constant);

    opcodes.push(OpCode::Lambda(lambda.arity, hash), lambda.span);

    for upvalue in &lambda.upvalues {
        opcodes.push(vm::OpCode::CreateUpValue(*upvalue), lambda.span);
    }

    Ok(())
}

fn compile_if(
    r#if: &tree::If,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    let mut then_opcodes = OpCodeTable::new();
    let mut else_opcodes = OpCodeTable::new();

    compile(&r#if.predicate, opcodes, constants)?;
    compile(&r#if.then, &mut then_opcodes, constants)?;
    compile(&r#if.r#else, &mut else_opcodes, constants)?;

    opcodes.push(OpCode::Branch(then_opcodes.len() + 1), r#if.span);

    then_opcodes.push(OpCode::Jmp(else_opcodes.len() as isize), r#if.span);

    opcodes.append(then_opcodes);
    opcodes.append(else_opcodes);

    Ok(())
}

fn compile_def(
    def: &tree::Def,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&def.body, opcodes, constants)?;

    let constant = Constant::Symbol(Rc::new(def.parameter.name.clone()));
    let hash = hash_constant(&constant);
    constants.push(constant);

    opcodes.push(OpCode::DefGlobal(hash), def.span);

    Ok(())
}

fn compile_set(
    set: &tree::Set,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&set.body, opcodes, constants)?;

    match &set.target {
        tree::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::SetLocal(*index), set.span);
        }
        tree::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::SetUpValue(*index), set.span);
        }
        tree::VarRef::Global { name, .. } => {
            let constant = Constant::Symbol(Rc::new(name.clone()));
            let hash = hash_constant(&constant);
            constants.push(constant);
            opcodes.push(OpCode::SetGlobal(hash), set.span);
        }
    };

    Ok(())
}

fn compile_setbox(
    setbox: &tree::SetBox,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&setbox.target, opcodes, constants)?;
    compile(&setbox.body, opcodes, constants)?;

    opcodes.push(OpCode::SetBox, setbox.span);

    Ok(())
}

fn compile_box(
    r#box: &tree::Box,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&r#box.body, opcodes, constants)?;

    opcodes.push(OpCode::Box, r#box.span);

    Ok(())
}

fn compile_unbox(
    unbox: &tree::UnBox,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&unbox.body, opcodes, constants)?;

    opcodes.push(OpCode::UnBox, unbox.span);

    Ok(())
}

fn compile_arithmetic_operation(
    arithmetic_op: &tree::ArithmeticOperation,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&arithmetic_op.lhs, opcodes, constants)?;
    compile(&arithmetic_op.rhs, opcodes, constants)?;

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

fn compile_float_operation(
    arithmetic_op: &tree::FloatOperation,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&arithmetic_op.lhs, opcodes, constants)?;
    compile(&arithmetic_op.rhs, opcodes, constants)?;

    opcodes.push(
        match arithmetic_op.operator {
            tree::FloatOperator::Add => OpCode::Add,
            tree::FloatOperator::Sub => OpCode::Sub,
            tree::FloatOperator::Mul => OpCode::Mul,
            tree::FloatOperator::Div => OpCode::Div,
        },
        arithmetic_op.span,
    );

    Ok(())
}

fn compile_comparison_operation(
    comparison_op: &tree::ComparisonOperation,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&comparison_op.lhs, opcodes, constants)?;
    compile(&comparison_op.rhs, opcodes, constants)?;

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

fn compile_list(
    list: &tree::List,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    for expr in &list.exprs {
        compile(expr, opcodes, constants)?;
    }

    opcodes.push(OpCode::List(list.exprs.len()), list.span);

    Ok(())
}

fn compile_fncall(
    fncall: &tree::FnCall,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&fncall.function, opcodes, constants)?;

    for arg in &fncall.args {
        compile(arg, opcodes, constants)?
    }

    opcodes.push(OpCode::Call(fncall.args.len()), fncall.span);

    Ok(())
}

fn compile_cons(
    cons: &tree::Cons,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&cons.lhs, opcodes, constants)?;
    compile(&cons.rhs, opcodes, constants)?;

    opcodes.push(OpCode::Cons, cons.span);

    Ok(())
}

fn compile_car(
    car: &tree::Car,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&car.body, opcodes, constants)?;

    opcodes.push(OpCode::Car, car.span);

    Ok(())
}

fn compile_cdr(
    cdr: &tree::Cdr,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&cdr.body, opcodes, constants)?;

    opcodes.push(OpCode::Cdr, cdr.span);

    Ok(())
}

fn compile_is_type(
    is_type: &tree::IsType,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&is_type.body, opcodes, constants)?;

    let vm_type = match is_type.r#type {
        tree::IsTypeParameter::Function => vm::object::Type::Function,
        tree::IsTypeParameter::Cons => vm::object::Type::Cons,
        tree::IsTypeParameter::Symbol => vm::object::Type::Symbol,
        tree::IsTypeParameter::String => vm::object::Type::String,
        tree::IsTypeParameter::Char => vm::object::Type::Char,
        tree::IsTypeParameter::Int => vm::object::Type::Int,
        tree::IsTypeParameter::Float => vm::object::Type::Float,
        tree::IsTypeParameter::Bool => vm::object::Type::Bool,
        tree::IsTypeParameter::Nil => vm::object::Type::Nil,
    };

    opcodes.push(OpCode::IsType(vm_type), is_type.span);

    Ok(())
}

fn compile_apply(
    apply: &tree::Apply,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&apply.function, opcodes, constants)?;
    compile(&apply.list, opcodes, constants)?;

    opcodes.push(OpCode::Apply, apply.span);

    Ok(())
}

fn compile_assert(
    assert: &tree::Assert,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&assert.body, opcodes, constants)?;

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
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&map_insert.map, opcodes, constants)?;
    compile(&map_insert.key, opcodes, constants)?;
    compile(&map_insert.value, opcodes, constants)?;

    opcodes.push(OpCode::MapInsert, map_insert.span);

    Ok(())
}

fn compile_map_retrieve(
    map_retrieve: &tree::MapRetrieve,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&map_retrieve.map, opcodes, constants)?;
    compile(&map_retrieve.key, opcodes, constants)?;

    opcodes.push(OpCode::MapRetrieve, map_retrieve.span);

    Ok(())
}

fn compile_map_items(
    map_items: &tree::MapItems,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&map_items.map, opcodes, constants)?;

    opcodes.push(OpCode::MapItems, map_items.span);

    Ok(())
}

fn compile_make_type(
    make_type: &tree::MakeType,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    let constant = Constant::Symbol(Rc::new(make_type.pattern.0.clone()));
    let hash = hash_constant(&constant);
    constants.push(constant);

    opcodes.push(OpCode::PushSymbol(hash), make_type.span);

    if !make_type.exprs.is_empty() {
        for expr in &make_type.exprs {
            compile(expr, opcodes, constants)?;
        }

        opcodes.push(OpCode::MakeStruct(make_type.exprs.len()), make_type.span);
    } else {
        opcodes.push(OpCode::PushNil, make_type.span)
    }

    opcodes.push(OpCode::Cons, make_type.span);

    Ok(())
}

fn compile_if_let(
    if_let: &tree::IfLet,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    let mut then = OpCodeTable::new();
    let mut r#else = OpCodeTable::new();

    compile(&if_let.body, opcodes, constants)?;
    compile(&if_let.then, &mut then, constants)?;
    compile(&if_let.r#else, &mut r#else, constants)?;

    then.push(OpCode::Return, if_let.span);

    let else_length = r#else.len();

    let lambda_opcode_table_constant = Constant::OpCodeTable(Rc::new(then));
    let hash = hash_constant(&lambda_opcode_table_constant);
    constants.push(lambda_opcode_table_constant);

    let lambda = OpCode::Lambda(vm::Arity::Nary(if_let.bindings.len()), hash);

    opcodes.push(OpCode::Dup, if_let.span);

    opcodes.push(OpCode::Car, if_let.span);

    let symbol_constant = Constant::Symbol(Rc::new(if_let.pattern.0.clone()));
    let hash = hash_constant(&symbol_constant);
    constants.push(symbol_constant);

    opcodes.push(OpCode::PushSymbol(hash), if_let.span);

    opcodes.push(OpCode::Eq, if_let.span);

    opcodes.push(
        OpCode::Branch(6 + (if_let.bindings.len() * 3) + if_let.upvalues.len()),
        if_let.span,
    );

    opcodes.push(lambda, if_let.span);

    for upvalue in &if_let.upvalues {
        opcodes.push(OpCode::CreateUpValue(*upvalue), if_let.span);
    }

    opcodes.push(OpCode::Swap, if_let.span);

    opcodes.push(OpCode::Cdr, if_let.span);

    for i in 0..if_let.bindings.len() {
        opcodes.push(OpCode::Dup, if_let.span);
        opcodes.push(OpCode::GetField(i), if_let.span);
        opcodes.push(OpCode::Swap, if_let.span);
    }

    opcodes.push(OpCode::Pop, if_let.span);

    opcodes.push(OpCode::Call(if_let.bindings.len()), if_let.span);

    opcodes.push(OpCode::Jmp(else_length as isize), if_let.span);

    opcodes.append(r#else);

    Ok(())
}

fn compile_letrec(
    letrec: &tree::LetRec,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    let mut lambda_opcodes = OpCodeTable::new();

    for (i, (_, expr)) in letrec.bindings.iter().enumerate() {
        compile(expr, &mut lambda_opcodes, constants)?;
        lambda_opcodes.push(OpCode::SetLocal(i), letrec.span);
    }

    compile(&letrec.body, &mut lambda_opcodes, constants)?;

    lambda_opcodes.push(OpCode::Return, letrec.span);

    let constant = Constant::OpCodeTable(Rc::new(lambda_opcodes));
    let hash = hash_constant(&constant);
    constants.push(constant);

    opcodes.push(
        OpCode::Lambda(vm::Arity::Nary(letrec.bindings.len()), hash),
        letrec.span,
    );

    for upvalue in &letrec.upvalues {
        opcodes.push(OpCode::CreateUpValue(*upvalue), letrec.span);
    }

    for _ in 0..letrec.bindings.len() {
        opcodes.push(OpCode::PushNil, letrec.span);
    }

    opcodes.push(OpCode::Call(letrec.bindings.len()), letrec.span);

    Ok(())
}

fn compile_make_struct(
    make_struct: &tree::MakeStruct,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    for expr in &make_struct.exprs {
        compile(expr, opcodes, constants)?;
    }

    opcodes.push(
        OpCode::MakeStruct(make_struct.exprs.len()),
        make_struct.span,
    );

    Ok(())
}

fn compile_get_field(
    get_field: &tree::GetField,
    opcodes: &mut OpCodeTable<FileSpan>,
    constants: &mut Vec<Constant<FileSpan>>,
) -> Result<(), Error> {
    compile(&get_field.body, opcodes, constants)?;

    opcodes.push(OpCode::GetField(get_field.index), get_field.span);

    Ok(())
}

pub(crate) fn hash_constant<D: Hash>(constant: &Constant<D>) -> u64 {
    let mut hasher = std::hash::DefaultHasher::new();
    constant.hash(&mut hasher);
    hasher.finish()
}
