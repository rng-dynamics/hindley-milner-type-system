use std::collections::HashSet;

use crate::type_var::TypeVar;
use crate::{r#type::Type, type_var_equation::TypeVarEquation};

#[derive(Clone)]
pub(crate) struct TypeVarEquationSet {
    set: HashSet<TypeVarEquation>,
}

impl TypeVarEquationSet {
    pub(crate) fn new() -> Self {
        Self {
            set: HashSet::new(),
        }
    }

    pub(crate) fn insert_1(&mut self, eq: TypeVarEquation) -> bool {
        self.set.insert(eq)
    }

    pub(crate) fn insert_2(&mut self, var: TypeVar, type_: Type) -> bool {
        self.set.insert(TypeVarEquation::new(var, type_))
    }

    pub(crate) fn contains_1(&self, eq: &TypeVarEquation) -> bool {
        self.set.contains(eq)
    }

    pub(crate) fn contains_2(&self, var: TypeVar, type_: Type) -> bool {
        self.set.contains(&TypeVarEquation::new(var, type_))
    }

    pub(crate) fn lookup_lhs(&self, lhs: &TypeVar) -> Option<Type> {
        Some(self.set.iter().find(|ee| ee.lhs == *lhs)?.rhs.clone())
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

pub(crate) struct TypeVarAssignmentSetIntoIterator {
    iter: <std::collections::HashSet<TypeVarEquation> as std::iter::IntoIterator>::IntoIter,
}

impl std::iter::IntoIterator for TypeVarEquationSet {
    type Item = <std::collections::HashSet<TypeVarEquation> as std::iter::IntoIterator>::Item;
    type IntoIter = TypeVarAssignmentSetIntoIterator;

    fn into_iter(self) -> Self::IntoIter {
        TypeVarAssignmentSetIntoIterator {
            iter: self.set.into_iter(),
        }
    }
}

impl Iterator for TypeVarAssignmentSetIntoIterator {
    type Item = <std::collections::HashSet<TypeVarEquation> as std::iter::IntoIterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_contains_1() {
        let mut sut = TypeVarEquationSet::new();
        sut.insert_1(TypeVarEquation {
            lhs: TypeVar::new("t0"),
            rhs: Type::Bool,
        });
        assert!(sut.contains_1(&TypeVarEquation {
            lhs: TypeVar::new("t0"),
            rhs: Type::Bool,
        }));
    }

    #[test]
    fn insert_and_contains_2() {
        let mut sut = TypeVarEquationSet::new();
        sut.insert_2(TypeVar::new("t0"), Type::Bool);
        assert!(sut.contains_2(TypeVar::new("t0"), Type::Bool));
    }

    #[test]
    fn lookup_lhs() {
        let mut sut = TypeVarEquationSet::new();
        sut.insert_2(TypeVar::new("t0"), Type::Int);
        let lookup_type = sut.lookup_lhs(&TypeVar::new("t0")).unwrap();
        assert_eq!(Type::Int, lookup_type);
    }

    #[test]
    fn is_empty() {
        let mut sut = TypeVarEquationSet::new();
        assert!(sut.is_empty());
        sut.insert_2(TypeVar::new("t0"), Type::Int);
        assert!(!sut.is_empty());
    }

    #[test]
    fn interator() {
        let mut sut = TypeVarEquationSet::new();
        sut.insert_2(TypeVar::new("t0"), Type::Bool);
        for eq in sut {
            assert_eq!(TypeVarEquation::new(TypeVar::new("t0"), Type::Bool), eq);
        }
    }
}
