use crate::Type;
use std::collections::HashMap;
use vm::UpValue;

#[derive(Clone, Debug)]
pub(crate) enum Variable {
    Local(usize, Option<Type>),
    Upvalue(usize, Option<Type>),
    Global(Option<Type>),
}

#[derive(Clone, Debug)]
struct Scope {
    locals: Vec<(String, Option<Type>)>,
    upvalues: Vec<(String, UpValue)>,
}

#[derive(Clone, Debug)]
pub(crate) struct Environment {
    globals: HashMap<String, Option<Type>>,
    scopes: Vec<Scope>,
}

impl Scope {
    fn get_local(&self, name: &str) -> Option<(usize, Option<Type>)> {
        self.locals
            .iter()
            .enumerate()
            .find_map(|(i, (local, r#type))| {
                if name == local {
                    Some((i, r#type.clone()))
                } else {
                    None
                }
            })
    }

    fn get_upvalue(&self, name: &str) -> Option<usize> {
        self.upvalues.iter().enumerate().find_map(
            |(i, (upvalue, _))| {
                if name == upvalue {
                    Some(i)
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
            globals: HashMap::new(),
            scopes: Vec::new(),
        }
    }

    pub(crate) fn insert_global(&mut self, name: &str, r#type: Option<Type>) {
        self.globals.insert(name.to_string(), r#type);
    }

    pub(crate) fn push_scope(&mut self, locals: impl Iterator<Item = (String, Option<Type>)>) {
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
        if let Some((i, r#type)) = self.scopes.last().unwrap().get_local(name) {
            Some(Variable::Local(i, r#type))
        } else if let Some(i) = self.scopes.last().unwrap().get_upvalue(name) {
            let r#type = search_upvalue_type(
                self.scopes.last().unwrap().upvalues[i].1,
                self.scopes.iter(),
            );

            Some(Variable::Upvalue(i, r#type))
        } else if let Some(upvalue) = search_for_upvalue(name, self.scopes.iter_mut()) {
            self.scopes
                .last_mut()
                .unwrap()
                .upvalues
                .push((name.to_string(), upvalue));

            let r#type = search_upvalue_type(upvalue, self.scopes.iter());
            let i = self.scopes.last().unwrap().get_upvalue(name).unwrap();

            Some(Variable::Upvalue(i, r#type))
        } else if let Some(r#type) = self.globals.get(name) {
            Some(Variable::Global(r#type.clone()))
        } else {
            None
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
    if let Some((local, _)) = scope.get_local(name) {
        Some(UpValue::Local(local))
    } else {
        let upvalue = search_for_upvalue(name, scopes)?;
        scope.upvalues.push((name.to_string(), upvalue));
        Some(UpValue::UpValue(scope.upvalues.len() - 1))
    }
}

fn search_upvalue_type<'a>(
    upvalue: UpValue,
    mut scopes: impl Iterator<Item = &'a Scope>,
) -> Option<Type> {
    let scope = scopes.next().unwrap();
    match upvalue {
        UpValue::Local(i) => scope.locals[i].1.clone(),
        UpValue::UpValue(i) => search_upvalue_type(scope.upvalues[i].1, scopes),
    }
}
