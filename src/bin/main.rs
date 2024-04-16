use std::env;
use std::error::Error;
use std::fs;
use std::io::Read;

use lisp::Interpreter;

fn main() -> Result<(), Box<dyn Error>> {
    let source_file = env::args().nth(1).ok_or("no source file provided")?;
    let mut buff = String::new();
    let mut file = fs::File::open(source_file)?;
    file.read_to_string(&mut buff)?;

    let mut interpreter = Interpreter::new();
    let reader = lisp::Reader::new(buff.as_str());

    for r in reader {
        let expr = interpreter.read(r?);
        interpreter.eval(expr)?;
    }
    Ok(())
}
