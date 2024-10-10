use vm::{object::Type, Error, Local, Object};

use crate::{check_arity, check_type};

pub fn sqrt<D: Clone>(locals: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("sqrt", 1, locals);

    let a = check_type!(locals[0], Float);

    Ok(Object::Float(a.sqrt()))
}

pub fn float_to_int<D: Clone>(locals: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("sqrt", 1, locals);

    let a = check_type!(locals[0], Float);

    Ok(Object::Int(a as i64))
}

pub fn int_to_float<D: Clone>(locals: &mut [Local<D>]) -> Result<Object<D>, Error> {
    check_arity!("sqrt", 1, locals);

    let a = check_type!(locals[0], Int);

    Ok(Object::Float(a as f64))
}
