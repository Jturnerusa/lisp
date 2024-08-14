use vm::{OpCode, OpCodeTable};

pub(super) fn optimize<D: Clone>(opcode_table: &OpCodeTable<D>) -> OpCodeTable<D> {
    tco(opcode_table)
}

pub(super) fn tco<D: Clone>(opcode_table: &OpCodeTable<D>) -> OpCodeTable<D> {
    let mut optimized: OpCodeTable<D> = OpCodeTable::new();
    let mut index = 0;

    loop {
        if index >= opcode_table.len() {
            break optimized;
        }

        match (
            &opcode_table.opcodes()[index],
            opcode_table.opcodes().get(index + 1),
        ) {
            (OpCode::Call(args), Some(OpCode::Return)) => {
                optimized.push(OpCode::Tail(*args), opcode_table.debug()[index].clone());
            }
            (OpCode::Call(args), Some(OpCode::Jmp(jmp)))
                if opcode_table
                    .opcodes()
                    .get(index + *jmp as usize + 2)
                    .is_some_and(|opcode| opcode.is_return()) =>
            {
                optimized.push(OpCode::Tail(*args), opcode_table.debug()[index].clone())
            }
            (opcode, _) => optimized.push(opcode.clone(), opcode_table.debug()[index].clone()),
        }

        index += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! push_opcodes {
        ($table:expr, $($e:expr),+) => {
            $($table.push($e, ());)+
        }
    }

    #[test]
    fn test_last_opcode() {
        let mut opcode_table: OpCodeTable<()> = OpCodeTable::new();
        push_opcodes!(
            opcode_table,
            OpCode::PushInt(1),
            OpCode::PushInt(1),
            OpCode::Add,
            OpCode::Call(0),
            OpCode::Return
        );

        let optimized = tco(&opcode_table);

        assert!(matches!(
            optimized.opcodes(),
            [
                OpCode::PushInt(1),
                OpCode::PushInt(1),
                OpCode::Add,
                OpCode::Tail(0),
                OpCode::Return
            ]
        ))
    }

    #[test]
    fn test_jmp() {
        let mut opcode_table: OpCodeTable<()> = OpCodeTable::new();
        push_opcodes!(
            opcode_table,
            OpCode::PushInt(1),
            OpCode::PushInt(1),
            OpCode::Branch(2),
            OpCode::Call(0),
            OpCode::Jmp(3),
            OpCode::PushInt(1),
            OpCode::Call(1),
            OpCode::Jmp(2),
            OpCode::Add,
            OpCode::Add,
            OpCode::Return
        );

        let optimized = tco(&opcode_table);

        assert!(matches!(
            optimized.opcodes(),
            [
                OpCode::PushInt(1),
                OpCode::PushInt(1),
                OpCode::Branch(2),
                OpCode::Call(0),
                OpCode::Jmp(3),
                OpCode::PushInt(1),
                OpCode::Tail(1),
                OpCode::Jmp(2),
                OpCode::Add,
                OpCode::Add,
                OpCode::Return
            ]
        ))
    }
}
