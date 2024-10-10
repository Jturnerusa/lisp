mod io;
mod string;

use std::{fmt::Debug, hash::Hash};

use gc::Gc;
use vm::{Error, Local, Object, Vm};

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
    ($object:expr, Cons) => {{
        $object.with(|object| match object {
            Object::Cons(cons) => Ok(cons.clone()),
            object => Err(::vm::Error::Type {
                expected: Type::Cons,
                recieved: Type::from(object),
            }),
        })?
    }};
    ($object:expr, Symbol) => {{
        use std::ops::Deref;
        $object.with(|object| match object {
            Object::Symbol(symbol) => Ok(symbol.deref().clone()),
            object => Err(::vm::Error::Type {
                expected: Type::Symbol,
                recieved: Type::from(object),
            }),
        })?
    }};
    ($object:expr, String) => {{
        use std::ops::Deref;
        $object.with(|object| match object {
            Object::String(string) => Ok(string.deref().clone()),
            object => Err(::vm::Error::Type {
                expected: Type::String,
                recieved: Type::from(object),
            }),
        })?
    }};
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

pub fn load_module<D: Clone + PartialEq + PartialOrd + Hash + Debug>(vm: &mut Vm<D>) {
    vm.load_native_function("gensym", gensym);
    vm.load_native_function("print", io::print);
    vm.load_native_function("println", io::println);
    vm.load_native_function("dbg", io::dbg);
    vm.load_native_function("read-file", io::read_file);
    vm.load_native_function("argv", io::argv);
    vm.load_native_function("string-split", string::split);
    vm.load_native_function("string->list", string::to_list);
    vm.load_native_function("string-lines", string::lines);
    vm.load_native_function("is-digit?", string::is_digit);
    vm.load_native_function("list->string", string::from_list);
    vm.load_native_function("string->int", string::parse);
    vm.load_native_function("string-split-whitespace", string::split_ascii_whitespace);
    vm.load_native_function("string-contains?", string::contains);
    vm.load_native_function("string-substr", string::substr);
    vm.load_native_function("string-find", string::find);
    vm.load_native_function("string-starts-with?", string::starts_with);
}

pub fn gensym<D: Clone>(_: &mut [Local<D>]) -> Result<Object<D>, Error> {
    let int = rand::random::<u64>();
    let symbol = format!("e{int}");
    Ok(Object::Symbol(Gc::new(symbol)))
}
