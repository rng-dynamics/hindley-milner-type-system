const SPACE: char = ' ';

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TypeVar(pub String);

impl TypeVar {
    pub(crate) fn new(name: &str) -> Self {
        TypeVar(name.to_string())
    }
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug)]
pub(crate) struct ParseTypeVarError {
    pub message: String,
    // no chained error
}

impl std::str::FromStr for TypeVar {
    type Err = ParseTypeVarError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let input_white_trimmed = input.trim();
        if input_white_trimmed.contains(SPACE) {
            return Err(ParseTypeVarError {
                message: format!("cannot parse input as TypeVar: {input}"),
            });
        }
        Ok(TypeVar(input_white_trimmed.into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn fmt() {
        let type_var = TypeVar::new("type-0");
        let fmt_str = format!("{type_var}");
        assert_eq!("type-0", fmt_str);
    }

    #[test]
    fn from_str() {
        let type_var = TypeVar::from_str("type-1").unwrap();
        assert_eq!(TypeVar::new("type-1"), type_var);
    }
}
