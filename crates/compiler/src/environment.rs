use vm::UpValue;

use unwrap_enum::EnumIs;

#[derive(Debug, Clone, Copy, EnumIs)]
pub(super) enum Variable {
    Local(usize),
    Upvalue(usize),
    Global,
}

struct Scope {
    locals: Vec<String>,
    upvalues: Vec<(String, UpValue)>,
}

pub struct Environment {
    scopes: Vec<Scope>,
}

impl Scope {
    pub fn new() -> Self {
        Self {
            locals: Vec::new(),
            upvalues: Vec::new(),
        }
    }
}

impl Scope {
    fn get_local(&self, var: &str) -> Option<usize> {
        self.locals.iter().enumerate().find_map(
            |(i, local)| {
                if local == var {
                    Some(i)
                } else {
                    None
                }
            },
        )
    }

    fn get_upvalue(&self, var: &str) -> Option<usize> {
        self.upvalues.iter().enumerate().find_map(
            |(i, (upvalue, _))| {
                if upvalue == var {
                    Some(i)
                } else {
                    None
                }
            },
        )
    }
}

impl Environment {
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    #[allow(clippy::manual_map)]
    pub fn resolve(&mut self, var: &str) -> Variable {
        let Some(current_scope) = self.scopes.last() else {
            return Variable::Global;
        };
        if let Some(i) = current_scope.get_local(var) {
            Variable::Local(i)
        } else if let Some(i) = current_scope.get_upvalue(var) {
            Variable::Upvalue(i)
        } else if let Some(upvalue) = search_for_upvalue(var, self.scopes.iter_mut().rev().skip(1))
        {
            self.scopes
                .last_mut()
                .unwrap()
                .upvalues
                .push((var.to_string(), upvalue));
            let i = self.scopes.last().unwrap().get_upvalue(var).unwrap();
            Variable::Upvalue(i)
        } else {
            Variable::Global
        }
    }

    pub fn push_scope(&mut self, locals: impl Iterator<Item = String>) {
        let mut scope = Scope::new();
        scope.locals = locals.collect();
        self.scopes.push(scope);
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop().unwrap();
    }

    pub fn upvalues(&self) -> impl Iterator<Item = UpValue> + '_ {
        self.scopes
            .last()
            .unwrap()
            .upvalues
            .iter()
            .map(|(_, upvalue)| *upvalue)
    }

    pub fn is_global_scope(&self) -> bool {
        self.scopes.is_empty()
    }
}

fn search_for_upvalue<'a>(
    var: &str,
    mut scopes: impl Iterator<Item = &'a mut Scope>,
) -> Option<UpValue> {
    let scope = scopes.next()?;
    if let Some(i) = scope.get_local(var) {
        Some(UpValue::Local(i))
    } else {
        let upvalue = search_for_upvalue(var, scopes)?;
        scope.upvalues.push((var.to_string(), upvalue));
        Some(UpValue::UpValue(scope.upvalues.len() - 1))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_locals() {
        let mut env = Environment::new();

        env.push_scope(["a", "b", "c"].into_iter().map(str::to_string));

        assert!(matches!(env.get("a"), Some(Variable::Local(0))));
        assert!(env.get("d").is_none());
    }

    #[test]
    fn test_upvalues() {
        let mut env = Environment::new();

        env.push_scope(["a", "b", "c"].into_iter().map(str::to_string));
        env.push_scope(["d", "e", "f"].into_iter().map(str::to_string));
        env.push_scope(["g", "h", "i"].into_iter().map(str::to_string));
    }
}
