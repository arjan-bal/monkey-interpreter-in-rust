use std::collections::HashMap;


#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Null(),
    Return(Box<Object>),
}

impl Object {
    pub fn inspect(&self) -> String {
        match &self {
            Object::Integer(x) => x.to_string(),
            Object::Boolean(x) => x.to_string(),
            Object::Null() => "null".to_string(),
            Object::Return(x) => x.inspect(),
        }
    }

    pub fn type_name(&self) -> String {
        match &self {
            Object::Integer(_) => "INTEGER",
            Object::Boolean(_) => "BOOLEAN",
            Object::Null() => "NULL",
            Object::Return(_) => "RETURN",
        }.to_string()
    }

    pub fn is_return(&self) -> bool {
        match self {
            Object::Return(_) => true,
            _ => false,
        }
    }

    pub fn get_return(self) -> Option<Object> {
        match self {
           Object::Return(x) => Some(*x),
           _ => None,
        }
    }
}

pub struct Environment {
    store: HashMap<String, Object>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment { store: HashMap::new() }
    }

    pub fn get(&self, name: &str) -> Option<&Object> {
        self.store.get(name)
    }

    pub fn set(&mut self, name: &str, value: Object) {
        self.store.insert(name.to_owned(), value);
    }
}