use crate::types::Type;
use std::collections::HashMap;
use vm::UpValue;

#[derive(Clone, Debug)]
pub(crate) enum Variable {
    Local(usize, Option<Type>),
    Upvalue(usize, Option<Type>),
    Module(Option<Type>),
    Global(Option<Type>),
}

#[derive(Clone, Debug)]
struct Scope {
    locals: Vec<(String, Option<Type>)>,
    upvalues: Vec<(String, UpValue)>,
}

#[derive(Clone, Debug)]
pub(crate) struct ModuleVar {
    pub r#type: Option<Type>,
    pub visible: bool,
}

#[derive(Clone, Debug)]
struct Module(HashMap<String, ModuleVar>);

#[derive(Clone, Debug)]
pub(crate) struct Environment {
    globals: HashMap<String, Option<Type>>,
    modules: HashMap<String, Module>,
    current_module: Option<String>,
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
            globals: HashMap::new(),
            modules: HashMap::new(),
            current_module: None,
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
        if let Some(scope) = self.scopes.last()
            && let Some((i, r#type)) = scope.get_local(name)
        {
            Some(Variable::Local(i, r#type))
        } else if let Some(scope) = self.scopes.last()
            && let Some((i, upvalue)) = scope.get_upvalue(name)
        {
            let r#type = search_upvalue_type(upvalue, self.scopes.iter().rev().skip(1));
            Some(Variable::Upvalue(i, r#type))
        } else if let Some(upvalue) = search_for_upvalue(name, self.scopes.iter_mut().rev().skip(1))
        {
            self.scopes
                .last_mut()
                .unwrap()
                .upvalues
                .push((name.to_string(), upvalue));

            let r#type = search_upvalue_type(upvalue, self.scopes.iter().rev().skip(1));
            let i = self.scopes.last().unwrap().upvalues.len() - 1;

            Some(Variable::Upvalue(i, r#type))
        } else if let Some(module) = &self.current_module {
            self.modules
                .get(module)
                .unwrap()
                .0
                .get(name)
                .map(|module_var| Variable::Module(module_var.r#type.clone()))
                .or_else(|| {
                    self.globals
                        .get(name)
                        .map(|r#type| Variable::Global(r#type.clone()))
                })
        } else {
            self.globals
                .get(name)
                .map(|r#type| Variable::Global(r#type.clone()))
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

    pub(crate) fn create_module(&mut self, name: &str) {
        self.modules
            .insert(name.to_string(), Module(HashMap::new()));
    }

    pub(crate) fn insert_module_var(&mut self, module: &str, name: &str, r#type: Option<Type>) {
        self.modules.get_mut(module).unwrap().0.insert(
            name.to_string(),
            ModuleVar {
                r#type,
                visible: false,
            },
        );
    }

    pub(crate) fn resolve_module_var(&self, module: &str, name: &str) -> Option<ModuleVar> {
        self.modules
            .get(module)
            .cloned()
            .and_then(|module| module.0.get(name).cloned())
    }

    pub(crate) fn export_module_var(&mut self, module: &str, name: &str) {
        self.modules
            .get_mut(module)
            .unwrap()
            .0
            .get_mut(name)
            .unwrap()
            .visible = true;
    }

    pub(crate) fn set_current_module(&mut self, module: Option<&str>) {
        self.current_module = module.map(|s| s.to_string());
    }

    pub(crate) fn current_module(&self) -> Option<&str> {
        self.current_module.as_deref()
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
