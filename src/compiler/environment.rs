use crate::vm::UpValue;
use unwrap_enum::EnumIs;

#[derive(EnumIs)]
pub(super) enum Variable {
    Local(usize),
    Upvalue(usize),
}

struct Scope {
    locals: Vec<String>,
    upvalues: Vec<(String, UpValue)>,
}

impl Scope {
    fn get_local(&self, var: &str) -> Option<usize> {
        self.locals
            .iter()
            .enumerate()
            .find_map(|(i, local)| if local.as_str() == var { Some(i) } else { None })
    }

    fn get_upvalue(&self, var: &str) -> Option<usize> {
        self.upvalues
            .iter()
            .enumerate()
            .find_map(|(i, (upvalue_name, _))| {
                if upvalue_name.as_str() == var {
                    Some(i)
                } else {
                    None
                }
            })
    }

    #[allow(clippy::manual_map)]
    fn get(&self, var: &str) -> Option<Variable> {
        if let Some(local_index) = self.get_local(var) {
            Some(Variable::Local(local_index))
        } else if let Some(upvalue_index) = self.get_upvalue(var) {
            Some(Variable::Upvalue(upvalue_index))
        } else {
            None
        }
    }
}

pub(super) struct Environment {
    scopes: Vec<Scope>,
}

impl Environment {
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    pub fn push_scope<'a>(&mut self, locals: impl Iterator<Item = &'a str>) {
        self.scopes.push(Scope {
            locals: locals.map(|s| s.to_string()).collect(),
            upvalues: Vec::new(),
        })
    }

    pub fn insert(&mut self, var: &str) {
        if self
            .scopes
            .last()
            .and_then(|scope| scope.get_local(var))
            .is_none()
        {
            if let Some(upvalue) = self.get_upvalue(var) {
                self.scopes
                    .last_mut()
                    .unwrap()
                    .upvalues
                    .push((var.to_string(), upvalue))
            }
        }
    }

    pub fn get(&self, var: &str) -> Option<Variable> {
        self.scopes.last().and_then(|scope| scope.get(var))
    }

    pub fn upvalues(&self) -> impl Iterator<Item = UpValue> + '_ {
        self.scopes
            .last()
            .unwrap()
            .upvalues
            .iter()
            .map(|(_, upvalue)| upvalue)
            .copied()
    }

    fn get_upvalue(&self, var: &str) -> Option<UpValue> {
        for (frame_index, scope) in (0..self.scopes.len() - 1)
            .rev()
            .zip(self.scopes.iter().rev().skip(1))
        {
            if let Some(local_index) = scope.get_local(var) {
                return Some(UpValue {
                    frame: frame_index,
                    index: local_index,
                });
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_locals() {
        let mut env = Environment::new();

        env.push_scope(["a", "b", "c"].into_iter());

        assert!(matches!(env.get("a"), Some(Variable::Local(0))));
        assert!(env.get("d").is_none());
    }

    #[test]
    fn test_upvalue() {
        let mut env = Environment::new();

        env.push_scope(["a", "b", "c"].into_iter());
        env.push_scope(["d", "e", "f"].into_iter());
        env.push_scope(std::iter::empty());
        env.insert("a");
        env.insert("f");

        assert!(matches!(env.get("a"), Some(Variable::Upvalue(0))));
        assert!(matches!(env.get("f"), Some(Variable::Upvalue(1))));

        assert!(matches!(
            env.upvalues().next().unwrap(),
            UpValue { frame: 0, index: 0 }
        ));
        assert!(matches!(
            env.upvalues().nth(1).unwrap(),
            UpValue { frame: 1, index: 2 }
        ));
    }
}
