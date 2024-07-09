use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

use crate::il::{self, Il};
use gc::Gc;
use identity_hasher::IdentityMap;
use vm::OpCodeTable;

type ConstantMap = IdentityMap<u64, vm::Constant>;

pub struct Error<'a> {
    source: &'a Il<'a>,
    message: String,
}

pub struct Compiler {
    macros: HashMap<String, u64>,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            macros: HashMap::new(),
        }
    }

    pub fn compile<'a: 'static>(
        &mut self,
        il: &'a Il<'a>,
        opcodes: &'a mut OpCodeTable,
        constants: &'a mut ConstantMap,
    ) -> Result<(), Error<'a>> {
        match il {
            Il::Lambda(lambda) => self.compile_lambda(il, lambda, opcodes, constants),
            _ => todo!(),
        }
    }

    fn compile_lambda<'a>(
        &mut self,
        source: &'a Il<'a>,
        lambda: &'a il::Lambda<'a>,
        opcodes: &'a mut OpCodeTable,
        constants: &'a mut ConstantMap,
    ) -> Result<(), Error> {
        let mut lambda_opcode_table = OpCodeTable::new();

        for expr in &lambda.body {
            self.compile(expr, &mut lambda_opcode_table, constants)?;
        }

        let lambda_opcode_table_hash = xxhash(&lambda_opcode_table);

        constants.insert(
            lambda_opcode_table_hash,
            vm::Constant::Opcodes(Gc::new(lambda_opcode_table)),
        );

        opcodes.insert(
            vm::OpCode::Lambda {
                arity: lambda.arity,
                body: lambda_opcode_table_hash,
            },
            Box::new(source.source_ast().source_sexpr()),
        );

        for upvalue in &lambda.upvalues {
            opcodes.insert(
                vm::OpCode::CreateUpValue(*upvalue),
                Box::new(source.source_ast().source_sexpr()),
            );
        }

        Ok(())
    }
}

fn xxhash(x: impl Hash) -> u64 {
    let mut hasher = twox_hash::xxh3::Hash64::with_seed(0);
    x.hash(&mut hasher);
    hasher.finish()
}
