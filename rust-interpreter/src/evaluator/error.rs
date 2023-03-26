use std::{
    error::Error,
    fmt::{self, Display},
};

#[derive(Debug)]
pub struct EvalError(pub String);

impl Error for EvalError {}

impl Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
