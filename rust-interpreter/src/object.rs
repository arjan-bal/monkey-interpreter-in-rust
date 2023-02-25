
#[derive(PartialEq, Eq, Debug)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Null(),
}

impl Object {
    pub fn inspect(&self) -> String {
        match &self {
            Object::Integer(x) => x.to_string(),
            Object::Boolean(x) => x.to_string(),
            Object::Null() => "null".to_string(),
        }
    }
}