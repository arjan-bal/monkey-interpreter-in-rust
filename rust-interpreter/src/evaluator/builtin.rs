use std::{collections::HashMap, rc::Rc};

use crate::object::{Builtin, Object, RObject};

use super::EvalError;

pub fn get_builtins() -> HashMap<&'static str, RObject> {
    HashMap::from([(
        "len",
        wrapped_builtin(Builtin {
            name: "len".to_owned(),
            func: Box::new(|args: &Vec<RObject>| {
                if args.len() != 1 {
                    return Err(EvalError(format!(
                        "wrong number of arguments. got={}, want=1",
                        args.len()
                    )));
                }
                let arg = &*args[0];
                let len = match arg {
                    Object::String(s) => s.len(),
                    _ => {
                        return Err(EvalError(format!(
                            "argument to `len` not supported, got {}",
                            arg.type_name()
                        )))
                    }
                };
                return Ok(Object::Integer(len as i64));
            }),
        }),
    )])
}

fn wrapped_builtin(b: Builtin) -> RObject {
    Rc::new(Object::Builtin(b))
}
