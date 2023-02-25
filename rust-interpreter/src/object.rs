
#[derive(PartialEq, Eq, Debug)]
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