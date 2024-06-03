mod io;
mod string;

use vm::Vm;

pub fn load_module(vm: &mut Vm) {
    vm.load_native_function("print", io::print);
    vm.load_native_function("read-file", io::read_file);
    vm.load_native_function("string-split", string::split);
    vm.load_native_function("string->list", string::to_list);
}
