use std::collections::HashSet;
use vm::UpValue;

#[derive(Clone, Debug)]
pub(crate) enum Variable {
    Local(usize),
    Upvalue(usize),
    Global,
}

#[derive(Clone, Debug)]
struct Scope {
    locals: Vec<String>,
    upvalues: Vec<(String, UpValue)>,
}

#[derive(Clone, Debug)]
pub(crate) struct Environment {
    globals: HashSet<String>,
    scopes: Vec<Scope>,
}

impl Scope {
    fn get_local(&self, name: &str) -> Option<usize> {
        self.locals.iter().enumerate().find_map(
            |(i, local)| {
                if name == local {
                    Some(i)
                } else {
                    None
                }
            },
        )
    }

    fn get_upvalue(&self, name: &str) -> Option<(usize, UpValue)> {
        self.upvalues
            .iter()
            .enumerate()
            .find_map(
                |(i, (n, upvalue))| {
                    if n == name {
                        Some((i, *upvalue))
                    } else {
                        None
                    }
                },
            )
    }
}

impl Environment {
    pub(crate) fn new() -> Self {
        Self {
            globals: HashSet::new(),

            scopes: Vec::new(),
        }
    }

    pub(crate) fn insert_global(&mut self, name: &str) {
        self.globals.insert(name.to_string());
    }

    pub(crate) fn push_scope(&mut self, locals: impl Iterator<Item = String>) {
        self.scopes.push(Scope {
            locals: locals.collect(),
            upvalues: Vec::new(),
        });
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop().unwrap();
    }

    #[allow(clippy::manual_map)]
    pub(crate) fn resolve(&mut self, name: &str) -> Option<Variable> {
        if let Some(scope) = self.scopes.last()
            && let Some(i) = scope.get_local(name)
        {
            Some(Variable::Local(i))
        } else if let Some(scope) = self.scopes.last()
            && let Some((i, _)) = scope.get_upvalue(name)
        {
            Some(Variable::Upvalue(i))
        } else if let Some(upvalue) = search_for_upvalue(name, self.scopes.iter_mut().rev().skip(1))
        {
            self.scopes
                .last_mut()
                .unwrap()
                .upvalues
                .push((name.to_string(), upvalue));

            let i = self.scopes.last().unwrap().upvalues.len() - 1;

            Some(Variable::Upvalue(i))
        } else {
            self.globals.get(name).map(|_| Variable::Global)
        }
    }

    pub(crate) fn upvalues(&self) -> impl Iterator<Item = UpValue> + '_ {
        self.scopes
            .last()
            .unwrap()
            .upvalues
            .iter()
            .map(|(_, upvalue)| *upvalue)
    }

    pub(crate) fn is_global_scope(&self) -> bool {
        self.scopes.is_empty()
    }
}

fn search_for_upvalue<'a>(
    name: &str,
    mut scopes: impl Iterator<Item = &'a mut Scope>,
) -> Option<UpValue> {
    let scope = scopes.next()?;
    if let Some(local) = scope.get_local(name) {
        Some(UpValue::Local(local))
    } else {
        let upvalue = search_for_upvalue(name, scopes)?;
        scope.upvalues.push((name.to_string(), upvalue));
        Some(UpValue::UpValue(scope.upvalues.len() - 1))
    }
}
