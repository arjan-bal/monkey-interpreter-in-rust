use std::{collections::HashMap, rc::Rc};

use crate::object::{Array, Builtin, Object, RObject};

use super::EvalError;

pub fn get_builtins() -> HashMap<&'static str, RObject> {
    HashMap::from([
        (
            "len",
            wrapped_builtin(Builtin {
                name: "len".to_owned(),
                func: Box::new(|args: &Vec<RObject>| {
                    validate_argument_count(args.len(), 1)?;
                    let arg = &*args[0];
                    let len = match arg {
                        Object::String(s) => s.len(),
                        Object::Array(a) => a.elements.len(),
                        _ => {
                            return Err(incorrect_type_error("list", arg));
                        }
                    };
                    Ok(Rc::new(Object::Integer(len as i64)))
                }),
            }),
        ),
        (
            "first",
            wrapped_builtin(Builtin {
                name: "first".to_owned(),
                func: Box::new(|args: &Vec<RObject>| {
                    validate_argument_count(args.len(), 1)?;
                    let arg = &*args[0];
                    let element = match arg {
                        Object::Array(a) => {
                            if a.elements.len() >= 1 {
                                Rc::clone(&a.elements[0])
                            } else {
                                Rc::new(Object::Null)
                            }
                        }
                        _ => {
                            return Err(incorrect_type_error("first", arg));
                        }
                    };
                    Ok(element)
                }),
            }),
        ),
        (
            "last",
            wrapped_builtin(Builtin {
                name: "last".to_owned(),
                func: Box::new(|args: &Vec<RObject>| {
                    validate_argument_count(args.len(), 1)?;
                    let arg = &*args[0];
                    let element = match arg {
                        Object::Array(a) => {
                            if a.elements.len() >= 1 {
                                Rc::clone(&a.elements.last().unwrap())
                            } else {
                                Rc::new(Object::Null)
                            }
                        }
                        _ => {
                            return Err(incorrect_type_error("last", arg));
                        }
                    };
                    Ok(element)
                }),
            }),
        ),
        (
            "rest",
            wrapped_builtin(Builtin {
                name: "rest".to_owned(),
                func: Box::new(|args: &Vec<RObject>| {
                    validate_argument_count(args.len(), 1)?;
                    let arg = &*args[0];
                    let element = match arg {
                        Object::Array(a) => {
                            if a.elements.len() >= 1 {
                                Rc::new(Object::Array(Array {
                                    elements: a
                                        .elements
                                        .iter()
                                        .skip(1)
                                        .map(|e| Rc::clone(e))
                                        .collect(),
                                }))
                            } else {
                                Rc::new(Object::Null)
                            }
                        }
                        _ => {
                            return Err(incorrect_type_error("rest", arg));
                        }
                    };
                    Ok(element)
                }),
            }),
        ),
        (
            "push",
            wrapped_builtin(Builtin {
                name: "push".to_owned(),
                func: Box::new(|args: &Vec<RObject>| {
                    validate_argument_count(args.len(), 2)?;
                    let arg = &*args[0];
                    let element = match arg {
                        Object::Array(a) => Rc::new(Object::Array(Array {
                            elements: a
                                .elements
                                .iter()
                                .chain([Rc::clone(&args[1])].iter())
                                .map(|e| Rc::clone(e))
                                .collect(),
                        })),
                        _ => {
                            return Err(incorrect_type_error("push", arg));
                        }
                    };
                    Ok(element)
                }),
            }),
        ),
    ])
}

fn validate_argument_count(got: usize, want: usize) -> Result<(), EvalError> {
    if got != want {
        Err(EvalError(format!(
            "wrong number of arguments. got={}, want={}",
            got, want
        )))
    } else {
        Ok(())
    }
}

fn incorrect_type_error(method_name: &str, arg: &Object) -> EvalError {
    EvalError(format!(
        "argument to `{}` not supported, got {}",
        method_name,
        arg.type_name()
    ))
}

fn wrapped_builtin(b: Builtin) -> RObject {
    Rc::new(Object::Builtin(b))
}
