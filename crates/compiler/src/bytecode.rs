mod optimizer;

use crate::il::{self, Il};
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
        Il::Module(module) => compile_module(module, opcodes),
        Il::Lambda(lambda) => compile_lambda(lambda, opcodes),
        Il::Def(def) => compile_def(def, opcodes),
        Il::Set(set) => compile_set(set, opcodes),
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

fn compile_module(
    module: &il::Module,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    opcodes.push(
        OpCode::CreateModule(Gc::new(module.name.clone())),
        module.source.source_sexpr(),
    );

    opcodes.push(
        OpCode::DefGlobal(Gc::new(module.name.clone())),
        module.source.source_sexpr(),
    );

    Ok(())
}

fn compile_varref(
    varref: &il::VarRef,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    match varref {
        il::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::GetLocal(*index), varref.source().source_sexpr());
        }
        il::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::GetUpValue(*index), varref.source().source_sexpr());
        }
        il::VarRef::Global { name, .. } => opcodes.push(
            OpCode::GetGlobal(Gc::new(name.clone())),
            varref.source().source_sexpr(),
        ),
        il::VarRef::Module { name, module, .. } => {
            opcodes.push(
                OpCode::GetGlobal(Gc::new(module.clone())),
                varref.source().source_sexpr(),
            );
            opcodes.push(
                OpCode::GetModuleVar(Gc::new(name.clone())),
                varref.source().source_sexpr(),
            );
        }
    };

    Ok(())
}

fn compile_constant(
    constant: &il::Constant,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    let op = match constant {
        il::Constant::Symbol { symbol, .. } => OpCode::PushSymbol(Gc::new(symbol.clone())),
        il::Constant::String { string, .. } => OpCode::PushString(Gc::new(string.clone())),
        il::Constant::Char { char, .. } => OpCode::PushChar(*char),
        il::Constant::Int { int, .. } => OpCode::PushInt(*int),
        il::Constant::Bool { bool, .. } => OpCode::PushBool(*bool),
        il::Constant::Nil { .. } => OpCode::PushNil,
    };

    opcodes.push(op, constant.source().source_sexpr());

    Ok(())
}

fn compile_lambda(
    lambda: &il::Lambda,
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
    r#if: &il::If,
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
    def: &il::Def,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(def.body(), opcodes)?;

    match def {
        il::Def::Global { parameter, .. } => opcodes.push(
            OpCode::DefGlobal(Gc::new(parameter.name.clone())),
            def.source().source_sexpr(),
        ),
        il::Def::Module {
            parameter, module, ..
        } => {
            opcodes.push(
                OpCode::GetGlobal(Gc::new(module.clone())),
                def.source().source_sexpr(),
            );
            opcodes.push(
                OpCode::DefModuleVar(Gc::new(parameter.name.clone())),
                def.source().source_sexpr(),
            );
        }
    }

    Ok(())
}

fn compile_set(
    set: &il::Set,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&set.body, opcodes)?;

    match &set.target {
        il::VarRef::Local { index, .. } => {
            opcodes.push(OpCode::SetLocal(*index), set.source.source_sexpr());
        }
        il::VarRef::UpValue { index, .. } => {
            opcodes.push(OpCode::SetUpValue(*index), set.source.source_sexpr());
        }
        il::VarRef::Global { name, .. } => {
            opcodes.push(
                OpCode::SetGlobal(Gc::new(name.clone())),
                set.source.source_sexpr(),
            );
        }
        il::VarRef::Module { name, module, .. } => {
            opcodes.push(
                OpCode::GetGlobal(Gc::new(module.clone())),
                set.source.source_sexpr(),
            );
            opcodes.push(
                OpCode::SetModuleVar(Gc::new(name.clone())),
                set.source.source_sexpr(),
            );
        }
    };

    Ok(())
}

fn compile_arithmetic_operation(
    arithmetic_op: &il::ArithmeticOperation,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&arithmetic_op.lhs, opcodes)?;
    compile(&arithmetic_op.rhs, opcodes)?;

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

fn compile_comparison_operation(
    comparison_op: &il::ComparisonOperation,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&comparison_op.lhs, opcodes)?;
    compile(&comparison_op.rhs, opcodes)?;

    opcodes.push(
        match comparison_op.operator {
            il::ComparisonOperator::Eq => OpCode::Eq,
            il::ComparisonOperator::Lt => OpCode::Lt,
            il::ComparisonOperator::Gt => OpCode::Gt,
        },
        comparison_op.source.source_sexpr(),
    );

    Ok(())
}

fn compile_list(
    list: &il::List,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    for expr in &list.exprs {
        compile(expr, opcodes)?;
    }

    opcodes.push(OpCode::List(list.exprs.len()), list.source.source_sexpr());

    Ok(())
}

fn compile_fncall(
    fncall: &il::FnCall,
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
    cons: &il::Cons,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&cons.lhs, opcodes)?;
    compile(&cons.rhs, opcodes)?;

    opcodes.push(OpCode::Cons, cons.source.source_sexpr());

    Ok(())
}

fn compile_car(
    car: &il::Car,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&car.body, opcodes)?;

    opcodes.push(OpCode::Car, car.source.source_sexpr());

    Ok(())
}

fn compile_cdr(
    cdr: &il::Cdr,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&cdr.body, opcodes)?;

    opcodes.push(OpCode::Cdr, cdr.source.source_sexpr());

    Ok(())
}

fn compile_is_type(
    is_type: &il::IsType,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&is_type.body, opcodes)?;

    let vm_type = match is_type.r#type {
        il::IsTypeParameter::Function => vm::object::Type::Function,
        il::IsTypeParameter::Cons => vm::object::Type::Cons,
        il::IsTypeParameter::Symbol => vm::object::Type::Symbol,
        il::IsTypeParameter::String => vm::object::Type::String,
        il::IsTypeParameter::Char => vm::object::Type::Char,
        il::IsTypeParameter::Int => vm::object::Type::Int,
        il::IsTypeParameter::Bool => vm::object::Type::Bool,
        il::IsTypeParameter::Nil => vm::object::Type::Nil,
    };

    opcodes.push(OpCode::IsType(vm_type), is_type.source.source_sexpr());

    Ok(())
}

fn compile_apply(
    apply: &il::Apply,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&apply.function, opcodes)?;
    compile(&apply.list, opcodes)?;

    opcodes.push(OpCode::Apply, apply.source.source_sexpr());

    Ok(())
}

fn compile_assert(
    assert: &il::Assert,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&assert.body, opcodes)?;

    opcodes.push(OpCode::Assert, assert.source.source_sexpr());

    Ok(())
}

fn compile_map_create(
    map_create: &il::MapCreate,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    opcodes.push(OpCode::MapCreate, map_create.source.source_sexpr());

    Ok(())
}

fn compile_map_insert(
    map_insert: &il::MapInsert,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&map_insert.map, opcodes)?;
    compile(&map_insert.key, opcodes)?;
    compile(&map_insert.value, opcodes)?;

    opcodes.push(OpCode::MapInsert, map_insert.source.source_sexpr());

    Ok(())
}

fn compile_map_retrieve(
    map_retrieve: &il::MapRetrieve,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&map_retrieve.map, opcodes)?;
    compile(&map_retrieve.key, opcodes)?;

    opcodes.push(OpCode::MapRetrieve, map_retrieve.source.source_sexpr());

    Ok(())
}

fn compile_map_items(
    map_items: &il::MapItems,
    opcodes: &mut OpCodeTable<&'static Sexpr<'static>>,
) -> Result<(), Error> {
    compile(&map_items.map, opcodes)?;

    opcodes.push(OpCode::MapItems, map_items.source.source_sexpr());

    Ok(())
}
