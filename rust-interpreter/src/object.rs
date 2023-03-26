use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    ast::{BlockStatement, Identifier},
    evaluator::EvalError,
};

pub type RObject = Rc<Object>;
pub type MutableEnvironment = Rc<RefCell<Environment>>;

pub enum Object {
    Integer(i64),
    String(String),
    Boolean(bool),
    Null(),
    Return(RObject),
    Function(Function),
    Builtin(Builtin),
}

pub struct Function {
    pub environment: MutableEnvironment,
    pub parameters: Rc<Vec<Identifier>>,
    pub body: Rc<BlockStatement>,
}

type BuiltinFunction = Box<dyn Fn(&Vec<RObject>) -> Result<Object, EvalError>>;

pub struct Builtin {
    pub(crate) func: BuiltinFunction,
    pub(crate) name: String,
}

impl Function {
    fn inspect(&self) -> String {
        let params = self
            .parameters
            .iter()
            .map(|i| i.name.clone())
            .collect::<Vec<String>>()
            .join(", ");
        format!("fn ({}) {{\n{}\n}}", params, self.body.to_string())
    }
}

impl Object {
    pub fn inspect(&self) -> String {
        match &self {
            Object::Integer(x) => x.to_string(),
            Object::Boolean(x) => x.to_string(),
            Object::String(x) => x.to_string(),
            Object::Null() => "null".to_string(),
            Object::Return(x) => x.inspect(),
            Object::Function(f) => f.inspect(),
            Object::Builtin(f) => f.name.clone(),
        }
    }

    pub fn type_name(&self) -> String {
        match &self {
            Object::Integer(_) => "INTEGER",
            Object::String(_) => "STRING",
            Object::Boolean(_) => "BOOLEAN",
            Object::Null() => "NULL",
            Object::Return(_) => "RETURN",
            Object::Function(_) => "FUNCTION",
            Object::Builtin(_) => "BUILTIN",
        }
        .to_string()
    }

    pub fn is_return(&self) -> bool {
        match self {
            Object::Return(_) => true,
            _ => false,
        }
    }

    pub fn get_return(&self) -> Option<RObject> {
        match self {
            Object::Return(x) => Some(Rc::clone(x)),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&String> {
        if let Self::String(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

pub struct Environment {
    parent: Option<MutableEnvironment>,
    store: HashMap<String, Rc<Object>>,
}

impl Environment {
    pub fn new() -> MutableEnvironment {
        Rc::new(RefCell::new(Environment {
            parent: None,
            store: HashMap::new(),
        }))
    }

    pub fn new_enclosed(parent: Option<&MutableEnvironment>) -> MutableEnvironment {
        Rc::new(RefCell::new(Environment {
            parent: parent.and_then(|p| Some(Rc::clone(p))),
            store: HashMap::new(),
        }))
    }

    pub fn get(&self, name: &str) -> Option<Rc<Object>> {
        let ret = self.store.get(name);
        if ret.is_some() {
            return Some(ret.unwrap().clone());
        }

        if self.parent.is_none() {
            return None;
        }

        match self.parent.as_ref().unwrap().borrow_mut().get(name) {
            Some(x) => Some(x.clone()),
            None => None,
        }
    }

    pub fn set(&mut self, name: &str, value: &Rc<Object>) {
        self.store.insert(name.to_owned(), Rc::clone(value));
    }
}
