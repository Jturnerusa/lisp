use vm::{
    object::{Cons, Type},
    Error, Object, Value,
};

pub fn split(objects: &mut [Value]) -> Result<Object, Error> {
    if objects.len() != 2 {
        Err(Error::Parameters(
            "string-split expects two parameters".to_string(),
        ))
    } else {
        let string = objects.first().unwrap().with(|object| match object {
            Object::String(string) => Ok(string.clone()),
            object => Err(Error::Type {
                expected: Type::String,
                recieved: Type::from(object),
            }),
        })?;

        let separator = objects.get(1).unwrap().with(|object| match object {
            Object::String(string) => Ok(string.clone()),
            object => Err(Error::Type {
                expected: Type::String,
                recieved: Type::from(object),
            }),
        })?;

        Ok(make_list_of_string(
            string.split(separator.as_str()).map(|s| s.to_string()),
        ))
    }
}

pub fn to_list(objects: &mut [Value]) -> Result<Object, Error> {
    if objects.len() != 1 {
        Err(Error::Parameters(
            "string->list expects one parameter".to_string(),
        ))
    } else {
        let string = objects.first().unwrap().with(|object| match object {
            Object::String(string) => Ok(string.clone()),
            object => Err(Error::Type {
                expected: Type::String,
                recieved: Type::from(object),
            }),
        })?;

        Ok(make_list_of_string(string.chars().map(|c| c.to_string())))
    }
}

fn make_list_of_string(mut strings: impl Iterator<Item = String>) -> Object {
    match strings.next() {
        Some(string) => Object::Cons(Box::new(Cons(
            Object::String(string.clone()),
            make_list_of_string(strings),
        ))),
        None => Object::Nil,
    }
}
