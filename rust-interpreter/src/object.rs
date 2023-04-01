use std::{cell::RefCell, collections::HashMap, fmt::Display, rc::Rc};

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
    Null,
    Return(RObject),
    Function(Function),
    Builtin(Builtin),
    Array(Array),
    Hash(Hash),
}

impl Object {
    pub fn inspect(&self) -> String {
        match &self {
            Object::Integer(x) => x.to_string(),
            Object::Boolean(x) => x.to_string(),
            Object::String(x) => x.to_string(),
            Object::Null => "null".to_string(),
            Object::Return(x) => x.inspect(),
            Object::Function(f) => f.inspect(),
            Object::Builtin(f) => f.name.clone(),
            Object::Array(a) => {
                format!(
                    "[{}]",
                    a.elements
                        .iter()
                        .map(|e| e.inspect())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Object::Hash(h) => {
                format!(
                    "{{{}}}",
                    h.elements
                        .iter()
                        .map(|(key, value)| format!("{}: {}", key.to_string(), value.inspect()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }

    pub fn type_name(&self) -> String {
        match &self {
            Object::Integer(_) => "INTEGER",
            Object::String(_) => "STRING",
            Object::Boolean(_) => "BOOLEAN",
            Object::Null => "NULL",
            Object::Return(_) => "RETURN",
            Object::Function(_) => "FUNCTION",
            Object::Builtin(_) => "BUILTIN",
            Object::Array(_) => "ARRAY",
            Object::Hash(_) => "HASH",
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

pub struct Function {
    pub environment: MutableEnvironment,
    pub parameters: Rc<Vec<Identifier>>,
    pub body: Rc<BlockStatement>,
}

type BuiltinFunction = Box<dyn Fn(&Vec<RObject>) -> Result<RObject, EvalError>>;

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

pub struct Array {
    pub elements: Vec<RObject>,
}

pub struct Hash {
    elements: HashMap<HashKey, RObject>,
}

impl Hash {
    pub fn new(pairs: Vec<(RObject, RObject)>) -> Result<Hash, EvalError> {
        let elements: Result<HashMap<_, _>, _> = pairs
            .iter()
            .map(|(k, v)| {
                let k = Self::get_key(Rc::clone(k))?;
                Ok((k, Rc::clone(v)))
            })
            .collect();
        Ok(Hash {
            elements: elements?,
        })
    }

    pub fn get(&self, key: RObject) -> Result<RObject, EvalError> {
        let key = Self::get_key(key)?;
        let res = match self.elements.get(&key) {
            Some(o) => Rc::clone(o),
            None => Rc::new(Object::Null),
        };
        Ok(res)
    }

    fn get_key(object: RObject) -> Result<HashKey, EvalError> {
        let ret = match *Rc::clone(&object) {
            Object::Boolean(b) => HashKey::Boolean(b),
            Object::Integer(i) => HashKey::Integer(i),
            Object::String(_) => HashKey::String(object.as_string().unwrap().clone()),
            _ => {
                return Err(EvalError(format!(
                    "Un-hashable type {} used to index hash map.",
                    object.inspect()
                )))
            }
        };
        Ok(ret)
    }
}

#[derive(Hash, PartialEq, Eq)]
pub enum HashKey {
    Integer(i64),
    Boolean(bool),
    String(String),
}

impl Display for HashKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                HashKey::Boolean(b) => Object::Boolean(*b).inspect(),
                HashKey::Integer(i) => Object::Integer(*i).inspect(),
                HashKey::String(s) => Object::String(s.clone()).inspect(),
            }
        )
    }
}

pub struct Environment {
    parent: Option<MutableEnvironment>,
    store: HashMap<String, RObject>,
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
