use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::ast::{BlockStatement, Identifier};

pub type RObject = Rc<Object>;
pub type MutableEnvironment = Rc<RefCell<Environment>>;

pub enum Object {
    Integer(i64),
    Boolean(bool),
    Null(),
    Return(RObject),
    Function(Function),
}

pub struct Function {
    pub environment: Environment,
    pub parameters: Rc<Vec<Identifier>>,
    pub body: Rc<BlockStatement>,
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
            Object::Null() => "null".to_string(),
            Object::Return(x) => x.inspect(),
            Object::Function(f) => f.inspect(),
        }
    }

    pub fn type_name(&self) -> String {
        match &self {
            Object::Integer(_) => "INTEGER",
            Object::Boolean(_) => "BOOLEAN",
            Object::Null() => "NULL",
            Object::Return(_) => "RETURN",
            Object::Function(_) => "FUNCTION",
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

    pub fn get_integer(&self) -> Option<i64> {
        match self {
            Object::Integer(x) => Some(*x),
            _ => None,
        }
    }

    pub fn is_null(&self) -> bool {
        match self {
            Object::Null() => true,
            _ => false,
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

    pub fn new_owned(parent: Option<&MutableEnvironment>) -> Environment {
        Environment {
            parent: parent.and_then(|p| Some(Rc::clone(p))),
            store: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&Rc<Object>> {
        self.store.get(name)
    }

    pub fn set(&mut self, name: &str, value: &Rc<Object>) {
        self.store.insert(name.to_owned(), Rc::clone(value));
    }
}
