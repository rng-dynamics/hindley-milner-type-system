use crate::type_var::TypeVar;

/// Type in the type system.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Type {
    Int,
    Bool,
    Var(TypeVar),
    Func(Vec<Type>),
}

const LPAREN: char = '(';
const RPAREN: char = ')';
const SEPARATOR: &str = " * ";
const ARROW: &str = " -> ";
const SPACE: char = ' ';

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ss: String = match self {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Var(oo) => oo.0.clone(),
            Type::Func(vs) => {
                let mut result: String;
                result = LPAREN.to_string();
                let mut sep = "";
                for (ii, vv) in vs.iter().enumerate() {
                    result.push_str(sep);
                    // the last separator is an arrow, the other separators are asterisks.
                    sep = if (vs.len() - ii) <= 2 {
                        ARROW
                    } else {
                        SEPARATOR
                    };
                    result.push_str(&vv.to_string());
                }
                result.push(RPAREN);
                result
            }
        };
        write!(f, "{ss}")
    }
}

#[derive(Debug)]
pub(crate) struct ParseTypeError {
    pub message: String,
    // no chained error
}

fn find_rightmost_matching_parentheses(ss: &str) -> Option<(usize, usize)> {
    let ridx: usize = ss.rfind(RPAREN)?;
    let mut cnt: usize = 0;
    for (idx, ch) in ss[..=ridx].chars().rev().enumerate() {
        match ch {
            RPAREN => {
                cnt += 1;
            }
            LPAREN => {
                cnt -= 1;
            }
            _ => {}
        }
        if cnt == 0 {
            let result = Some((ridx - idx, ridx));
            return result;
        }
    }
    None
}

fn find_rightmost_space_delimited_string(ss: &str) -> Option<(usize, usize)> {
    let ss_trim = ss.trim_end();
    if ss_trim.is_empty() {
        None
    } else {
        let lidx = match ss_trim.rfind(SPACE) {
            Some(idx) => idx + 1,
            None => 0,
        };
        Some((lidx, ss.len() - 1))
    }
}

impl std::str::FromStr for Type {
    type Err = ParseTypeError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        // trim whitespace
        let input_white_trimmed = input.trim();
        if input_white_trimmed.is_empty() {
            return Err(ParseTypeError {
                message: "got empty string".to_string(),
            });
        }

        // If there are two matching parentheses on the outside, ...
        if let Some((lidx, ridx)) = find_rightmost_matching_parentheses(input_white_trimmed) {
            if lidx == 0 && ridx == input_white_trimmed.len() - 1 {
                // .. remove them and recurse.
                return Self::from_str(&input_white_trimmed[1..input_white_trimmed.len() - 1]);
            }
        }

        // Parse atoms.
        if !input_white_trimmed.contains(SPACE) {
            let type_: Type = match input_white_trimmed {
                "Int" => Type::Int,
                "Bool" => Type::Bool,
                str => Type::Var(TypeVar(str.to_string())),
            };
            return Ok(type_);
        }

        // Parse functions from the back (because of different separators for parameters and return
        // types).
        let mut first_iteration = true;
        let mut accumulator = Vec::<(Self, usize, usize)>::new();
        let mut substring: &str = input_white_trimmed;
        'outer: loop {
            match substring.chars().last() {
                Some(RPAREN) => match find_rightmost_matching_parentheses(substring) {
                    None => {
                        return Err(ParseTypeError {
                            message: format!("parentheses do not match in {substring}"),
                        });
                    }
                    Some((lidx, ridx)) => {
                        let sub_type: Type = Self::from_str(&substring[lidx..=ridx])?;
                        accumulator.push((sub_type, lidx, ridx));
                        substring = &substring[..lidx];
                    }
                },
                Some(_other_char) => match find_rightmost_space_delimited_string(substring) {
                    None => {
                        return Err(ParseTypeError {
                            message: format!("got invalid string \"{substring}\""),
                        });
                    }
                    Some((lidx, ridx)) => {
                        let sub_type = Self::from_str(&substring[lidx..=ridx])?;
                        accumulator.push((sub_type, lidx, ridx));
                        substring = &substring[..lidx];
                    }
                },
                None => {
                    return Err(ParseTypeError {
                        message: format!("error parsing \"{input_white_trimmed}\""),
                    });
                }
            };
            if substring.trim().is_empty() {
                break 'outer;
            }
            let function_delimiter: &str = if first_iteration { ARROW } else { SEPARATOR };
            first_iteration = false;
            if substring.ends_with(function_delimiter) {
                substring = &substring[..substring.len() - function_delimiter.len()];
                substring = substring.trim_end();
            } else {
                return Err(ParseTypeError {
                    message: format!(
                        "could not find expected delimiter \"{function_delimiter}\" in {substring}"
                    ),
                });
            }
        }

        // If we parsed only one single type, ...
        if let [single] = &accumulator[..] {
            // ... then it is an atomic type and ...
            Ok(single.0.clone())
        } else {
            // ... otherwise it is a function type.

            // Since input was parsed from back to front we still have to reverse the vector.
            let vec_rev_iter = accumulator.iter().rev();
            Ok(Type::Func(vec_rev_iter.map(|ee| ee.0.clone()).collect()))
        }
    }
}

impl Type {
    pub(crate) fn new_type_var(input: &str) -> Self {
        Type::Var(TypeVar::new(input))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn from_str_atomic_types() {
        assert_eq!(Type::Int, Type::from_str("Int").unwrap());
        assert_eq!(Type::Bool, Type::from_str("Bool").unwrap());
        assert_eq!(Type::new_type_var("type0"), "type0".parse().unwrap());
    }

    #[test]
    fn from_str_function_type_one_param() {
        assert_eq!(
            Type::Func(vec![Type::Int, Type::Bool]),
            "Int -> Bool".parse().unwrap()
        );
    }

    #[test]
    fn from_str_function_type_two_params() {
        assert_eq!(
            Type::Func(vec![Type::new_type_var("type0"), Type::Int, Type::Bool]),
            "(type0 * Int -> Bool)".parse().unwrap()
        );
    }

    #[test]
    fn from_str_function_type_nested_function_1() {
        assert_eq!(
            Type::Func(vec![
                Type::Func(vec![Type::new_type_var("type0"), Type::Int, Type::Bool,]),
                Type::Int,
                Type::Bool
            ]),
            "((type0 * Int -> Bool) * Int -> Bool)".parse().unwrap()
        );
    }

    #[test]
    fn from_str_function_type_nested_function_2() {
        assert_eq!(
            Type::Func(vec![
                Type::new_type_var("type0"),
                Type::Func(vec![Type::Int, Type::Bool,]),
            ]),
            "(type0 -> (Int -> Bool))".parse().unwrap()
        );
    }

    #[test]
    fn from_str_function_type_nested_function_3() {
        assert_eq!(
            Type::Func(vec![
                Type::Func(vec![Type::new_type_var("X"), Type::new_type_var("Y")]),
                Type::Func(vec![Type::new_type_var("Y"), Type::new_type_var("X")]),
            ]),
            "((X -> Y) -> (Y -> X))".parse().unwrap()
        );
    }

    #[test]
    fn from_str_function_type_nested_function_4() {
        assert_eq!(
            Type::Func(vec![
                Type::Func(vec![Type::new_type_var("X"), Type::new_type_var("Y")]),
                Type::Func(vec![Type::new_type_var("Y"), Type::new_type_var("X")]),
            ]),
            "(X -> Y) -> (Y -> X)".parse().unwrap()
        );
    }

    #[test]
    fn to_string_atomic_types() {
        assert_eq!("Int", Type::Int.to_string());
        assert_eq!("Bool", Type::Bool.to_string());
        assert_eq!("type0", Type::new_type_var("type0").to_string());
    }

    #[test]
    fn to_string_function_type_1() {
        assert_eq!(
            "(type0 * Int -> Bool)",
            Type::Func(vec![
                Type::Var(TypeVar::new("type0")),
                Type::Int,
                Type::Bool
            ])
            .to_string()
        );
    }

    #[test]
    fn to_string_function_type_2() {
        assert_eq!(
            "((type0 * Int -> Bool) * Int -> Bool)",
            Type::Func(vec![
                Type::Func(vec![Type::new_type_var("type0"), Type::Int, Type::Bool]),
                Type::Int,
                Type::Bool
            ])
            .to_string()
        );
    }

    #[test]
    fn to_string_function_type_3() {
        assert_eq!(
            "((Int -> Int) * (Int -> Bool) -> Bool)",
            Type::Func(vec![
                Type::Func(vec![Type::Int, Type::Int]),
                Type::Func(vec![Type::Int, Type::Bool]),
                Type::Bool
            ])
            .to_string()
        );
    }

    #[test]
    fn to_string_function_type_4() {
        assert_eq!(
            "((Int -> Int) -> (Int -> Bool))",
            Type::Func(vec![
                Type::Func(vec![Type::Int, Type::Int]),
                Type::Func(vec![Type::Int, Type::Bool]),
            ])
            .to_string()
        );
    }
}
