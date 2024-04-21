use std::cell::RefCell;
use std::rc::Rc;

use crate::{Error, Object, ObjectRef, Type};

pub fn filter_ints(
    args: Box<crate::object::NativeArgs>,
) -> Result<impl Iterator<Item = i64>, Error> {
    args.map(|arg| match &*(*arg).borrow() {
        Object::Int(i) => Ok(*i),
        object => Err(Error::Type(Type::Int, Type::from(object))),
    })
    .collect::<Result<Vec<i64>, Error>>()
    .map(|vec| vec.into_iter())
}

pub fn add(args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    if args.len() < 1 {
        return Err(Error::Parameters);
    }

    let result = filter_ints(args)?.sum();

    Ok(Rc::new(RefCell::new(Object::Int(result))))
}

pub fn sub(args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    if args.len() < 1 {
        return Err(Error::Parameters);
    }

    let result = filter_ints(args)?.reduce(|acc, e| acc - e).unwrap();

    Ok(Rc::new(RefCell::new(Object::Int(result))))
}

pub fn div(args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    if args.len() < 1 {
        return Err(Error::Parameters);
    }

    let result = filter_ints(args)?.reduce(|acc, e| acc / e).unwrap();

    Ok(Rc::new(RefCell::new(Object::Int(result))))
}

pub fn mul(args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    if args.len() < 1 {
        return Err(Error::Parameters);
    }

    let result = filter_ints(args)?.reduce(|acc, e| acc * e).unwrap();

    Ok(Rc::new(RefCell::new(Object::Int(result))))
}

pub fn expt(args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    if args.len() < 1 {
        return Err(Error::Parameters);
    }

    let result = filter_ints(args)?
        .reduce(|acc, e| acc.pow(e.try_into().unwrap()))
        .unwrap();

    Ok(Rc::new(RefCell::new(Object::Int(result))))
}

pub fn less_than(mut args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    let cell = match args.next() {
        Some(c) => c,
        None => return Err(Error::Parameters),
    };

    let first = match &*(*cell).borrow() {
        Object::Int(i) => *i,
        object => return Err(Error::Type(Type::Int, Type::from(object))),
    };

    let rest = args
        .map(|arg| match Rc::unwrap_or_clone(arg).into_inner() {
            Object::Int(i) => Ok(i),
            object => Err(Error::Type(Type::Int, Type::from(&object))),
        })
        .collect::<Result<Vec<_>, Error>>()?;

    if rest.is_empty() {
        Err(Error::Parameters)
    } else if rest.into_iter().all(|arg| first < arg) {
        Ok(Rc::new(RefCell::new(Object::True)))
    } else {
        Ok(Rc::new(RefCell::new(Object::Nil)))
    }
}

pub fn greater_than(mut args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    let first = match args
        .next()
        .map(|arg| Rc::unwrap_or_clone(Rc::clone(&arg)).into_inner())
    {
        Some(Object::Int(i)) => i,
        Some(object) => return Err(Error::Type(Type::Int, Type::from(&object))),
        None => return Err(Error::Parameters),
    };

    let rest = args
        .map(
            |arg| match Rc::unwrap_or_clone(Rc::clone(&arg)).into_inner() {
                Object::Int(i) => Ok(i),
                object => Err(Error::Type(Type::Int, Type::from(&object))),
            },
        )
        .collect::<Result<Vec<_>, Error>>()?;

    if rest.is_empty() {
        Err(Error::Parameters)
    } else if rest.into_iter().all(|arg| first > arg) {
        Ok(Rc::new(RefCell::new(Object::True)))
    } else {
        Ok(Rc::new(RefCell::new(Object::Nil)))
    }
}

pub fn modulo(mut args: Box<crate::object::NativeArgs>) -> Result<ObjectRef, Error> {
    if args.len() != 2 {
        return Err(Error::Parameters);
    }

    let first = match args
        .next()
        .map(|arg| Rc::unwrap_or_clone(Rc::clone(&arg)).into_inner())
        .unwrap()
    {
        Object::Int(i) => i,
        object => return Err(Error::Type(Type::Int, Type::from(&object))),
    };

    let second = match args
        .next()
        .map(|arg| Rc::unwrap_or_clone(Rc::clone(&arg)).into_inner())
        .unwrap()
    {
        Object::Int(i) => i,
        object => return Err(Error::Type(Type::Int, Type::from(&object))),
    };

    let result = first % second;

    Ok(Rc::new(RefCell::new(Object::Int(result))))
}
