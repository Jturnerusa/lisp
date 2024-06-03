use std::{fs::File, io::Read};

use vm::{object::Type, Error, Object, Value};

pub fn print(objects: &mut [Value]) -> Result<Object, Error> {
    if objects.len() > 1 {
        Err(vm::Error::Parameters(
            "print accepts a single parameter".to_string(),
        ))
    } else {
        objects.first().unwrap().with(|object| println!("{object}"));
        Ok(Object::Nil)
    }
}

pub fn read_file(objects: &mut [Value]) -> Result<Object, Error> {
    if objects.len() > 1 {
        Err(Error::Parameters(
            "read-file expects a single parameter".to_string(),
        ))
    } else {
        let path = objects.first().unwrap().with(|object| match object {
            Object::String(string) => Ok(string.clone()),
            object => Err(Error::Type {
                expected: Type::String,
                recieved: Type::from(object),
            }),
        })?;

        let mut file = File::open(path).map_err(|e| Error::Other(Box::new(e)))?;
        let mut buff = String::new();

        file.read_to_string(&mut buff)
            .map_err(|e| Error::Other(Box::new(e)))?;

        Ok(Object::String(buff))
    }
}
