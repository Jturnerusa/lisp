mod io;
mod string;

use vm::Vm;

#[macro_export]
macro_rules! check_arity {
    ($fn:literal, $count:literal, $objects:expr) => {
        if $objects.len() != $count {
            return Err(::vm::Error::Parameters(
                concat!($fn, " ", "expects", $count, " ", "parameters").to_string(),
            ));
        }
    };
}

#[macro_export]
macro_rules! check_type {
    ($object:expr, Symbol) => {
        $object.with(|object| match object {
            Object::Symbol(symbol) => Ok(symbol.clone()),
            object => Err(::vm::Error::Type {
                expected: Type::Symbol,
                recieved: Type::from(object),
            }),
        })?
    };
    ($object:expr, String) => {
        $object.with(|object| match object {
            Object::String(string) => Ok(string.clone()),
            object => Err(::vm::Error::Type {
                expected: Type::String,
                recieved: Type::from(object),
            }),
        })?
    };
    ($object:expr, Int) => {
        $object.with(|object| match object {
            Object::Int(i) => Ok(*i),
            object => Err(::vm::Error::Type {
                expected: Type::Int,
                recieved: Type::from(object),
            }),
        })?
    };
    ($object:expr, Char) => {
        $object.with(|object| match object {
            Object::Char(c) => Ok(*c),
            object => Err(::vm::Error::Type {
                expected: Type::Char,
                recieved: Type::from(object),
            }),
        })?
    };
}

pub fn load_module(vm: &mut Vm) {
    vm.load_native_function("print", io::print);
    vm.load_native_function("read-file", io::read_file);
    vm.load_native_function("string-split", string::split);
    vm.load_native_function("string->list", string::to_list);
    vm.load_native_function("string-lines", string::lines);
    vm.load_native_function("is-digit?", string::is_digit);
}
