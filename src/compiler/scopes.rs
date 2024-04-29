use crate::vm::UpValue;

pub enum Variable {
    Global,
    Local(usize),
    UpValue(UpValue),
}

pub struct Scopes(Vec<Vec<String>>);

impl Scopes {
    pub fn push_scope(&mut self) {
        self.0.push(Vec::new());
    }

    pub fn push_local(&mut self, name: &str) {
        self.0.last_mut().unwrap().push(name.to_string());
    }

    pub fn resolve(&self, name: &str) -> Variable {
        if let Some(i) = self.find_local(name) {
            Variable::Local(i)
        } else if let Some(upvalue) = self.find_upvalue(name) {
            Variable::UpValue(upvalue)
        } else {
            Variable::Global
        }
    }

    fn find_upvalue(&self, name: &str) -> Option<UpValue> {
        self.0
            .iter()
            .enumerate()
            .find_map(|(frame, locals)| {
                locals.iter().enumerate().find_map(|(i, local)| {
                    if local.as_str() == name {
                        Some((frame, i))
                    } else {
                        None
                    }
                })
            })
            .map(|(frame, i)| UpValue { frame, index: i })
    }

    fn find_local(&self, name: &str) -> Option<usize> {
        self.0.last().and_then(|locals| {
            locals.iter().enumerate().find_map(|(i, local)| {
                if local.as_str() == name {
                    Some(i)
                } else {
                    None
                }
            })
        })
    }
}
