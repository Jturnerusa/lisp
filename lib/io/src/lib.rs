use std::rc::Rc;
use std::{cell::RefCell, ops::Deref};
use vm::{Error, Object, Vm};

pub fn load_module(vm: &mut Vm) {
    let functions = [("print", print)];

    for (name, function) in functions {
        vm.load_native_function(name, function);
    }
}

pub fn print(objects: &[Rc<RefCell<Object>>]) -> Result<Rc<RefCell<Object>>, Error> {
    if objects.len() > 1 {
        Err(Error::Parameters(
            "print accepts a single parameter".to_string(),
        ))
    } else {
        println!("{}", objects[0].borrow().deref());
        Ok(Rc::new(RefCell::new(Object::Nil)))
    }
}
