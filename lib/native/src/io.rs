use std::fs::File;
use std::io::Read;
use std::rc::Rc;
use std::{cell::RefCell, ops::Deref};
use vm::{Error, Object, Type, Vm};

pub fn load_module(vm: &mut Vm) {
    vm.load_native_function("print", print);
    vm.load_native_function("read-file", read_file);
}

pub fn print(objects: &[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> {
    if objects.len() > 1 {
        Err(vm::Error::Parameters(
            "print accepts a single parameter".to_string(),
        ))
    } else {
        println!("{}", objects[0].borrow().deref());
        Ok(Rc::new(RefCell::new(Object::Nil)))
    }
}

pub fn read_file(objects: &[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> {
    if objects.len() > 1 {
        Err(Error::Parameters(
            "read_file expects a single parameter".to_string(),
        ))
    } else {
        let path = match objects.first().unwrap().borrow().deref() {
            Object::String(string) => string.clone(),
            object => {
                return Err(Error::Type {
                    expected: Type::String,
                    recieved: Type::from(object),
                })
            }
        };
        let mut file = File::open(path).map_err(|e| Error::Other(Rc::new(e)))?;
        let mut buff = String::new();
        file.read_to_string(&mut buff)
            .map_err(|e| Error::Other(Rc::new(e)))?;

        Ok(Rc::new(RefCell::new(Object::String(buff))))
    }
}
