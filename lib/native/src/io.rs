use vm::{Error, Object, Value};

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
