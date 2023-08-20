use crate::r#type::Type;
use crate::type_var::TypeVar;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct TypeVarEquation {
    pub lhs: TypeVar,
    pub rhs: Type,
}

impl TypeVarEquation {
    pub(crate) fn new(lhs: TypeVar, rhs: Type) -> Self {
        Self { lhs, rhs }
    }
}

impl std::fmt::Display for TypeVarEquation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ==> {}", self.lhs, self.rhs)
    }
}
