use crate::r#type::Type;
use crate::type_var::TypeVar;
use crate::type_var_equation_set::TypeVarEquationSet;

pub(crate) fn unify_variable(
    type_var: &TypeVar,
    type_: &Type,
    type_var_equation_set: &mut TypeVarEquationSet,
) -> Result<(), String> {
    // If var is bound to type, then the two types are unified already.
    if let Type::Var(type_var_2) = type_ {
        if type_var == type_var_2 {
            return Ok(());
        }
    }

    let var_lookup = type_var_equation_set.lookup_lhs(type_var);
    if let Some(var_lookup) = var_lookup {
        return unify_aux(&var_lookup, type_, type_var_equation_set);
    }
    // If type_ is a variable, ...
    if let Type::Var(type_var_for_type_) = type_ {
        // ... check whether it is bound ...
        if let Some(type_lookup) = type_var_equation_set.lookup_lhs(type_var_for_type_) {
            // ... and unify against the bound type.
            return unify_variable(type_var, &type_lookup, type_var_equation_set);
        }
    }

    if occurs_check(type_var, type_, type_var_equation_set) {
        return Err("cannot unify {type_var} and {type_}".into());
    }

    type_var_equation_set.insert_2(type_var.clone(), type_.clone());
    Ok(())
}

fn unify(type_1: &Type, type_2: &Type) -> Result<TypeVarEquationSet, String> {
    let mut type_var_equations = TypeVarEquationSet::new();
    unify_aux(type_1, type_2, &mut type_var_equations)?;
    Ok(type_var_equations)
}

fn unify_aux(
    type_1: &Type,
    type_2: &Type,
    type_var_equation_set: &mut TypeVarEquationSet,
) -> Result<(), String> {
    if type_1 == type_2 {
        return Ok(());
    }

    if let Type::Var(type_1_var) = type_1 {
        return unify_variable(type_1_var, type_2, type_var_equation_set);
    }
    if let Type::Var(type_2_var) = type_2 {
        return unify_variable(type_2_var, type_1, type_var_equation_set);
    }
    if let Type::Func(vec_1) = type_1 {
        if let Type::Func(vec_2) = type_2 {
            if vec_1.len() != vec_2.len() {
                return Err("cannot unify function types {type_1} and {type_2}".into());
            }
            for (e1, e2) in vec_1.iter().zip(vec_2.iter()) {
                unify_aux(e1, e2, type_var_equation_set)?;
            }
            return Ok(());
        }
    }
    Err("cannot unify types {type_1} and {type_2}".into())
}

fn occurs_check(
    type_var: &TypeVar,
    type_: &Type,
    type_var_equation_set: &TypeVarEquationSet,
) -> bool {
    match type_ {
        Type::Var(type_var_2) => {
            if type_var == type_var_2 {
                return true;
            }
            if let Some(type_lookup) = type_var_equation_set.lookup_lhs(type_var_2) {
                return occurs_check(type_var, &type_lookup, type_var_equation_set);
            }
            #[allow(clippy::needless_return)]
            return false;
        }
        Type::Func(vec) => {
            return vec
                .iter()
                .any(|ee| occurs_check(type_var, ee, type_var_equation_set));
        }
        _ => {
            #[allow(clippy::needless_return)]
            return false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_1() {
        let left: Type = "X -> Y".parse().unwrap();
        let right: Type = "Y -> X".parse().unwrap();

        let unification = unify(&left, &right).unwrap();

        // crate::type_inference::print_type_var_equations(unification);
        assert!(unification.contains_2(TypeVar::new("X"), Type::new_type_var("Y")));
    }

    #[test]
    fn test_unify_2() {
        let left: Type = "X * Y -> Int".parse().unwrap();
        let right: Type = "Y * X -> X".parse().unwrap();

        let unification = unify(&left, &right).unwrap();

        // crate::type_inference::print_type_var_equations(unification);
        assert!(unification.contains_2(TypeVar::new("Y"), Type::Int));
        assert!(unification.contains_2(TypeVar::new("X"), Type::new_type_var("Y")));
    }

    #[test]
    fn test_unify_3() {
        let left: Type = "((X -> Y) -> (Y -> X))".parse().unwrap();
        let right: Type = "Z -> Z".parse().unwrap();

        let unification = unify(&left, &right).unwrap();

        // crate::type_inference::print_type_var_equations(&unification);
        assert!(unification.contains_2(TypeVar::new("X"), Type::new_type_var("Y")));
        assert!(unification.contains_2(TypeVar::new("Z"), "(X -> Y)".parse().unwrap(),));
    }

    #[test]
    fn test_unify_4() {
        let left: Type = "X * Y -> Int".parse().unwrap();
        let right: Type = "Y * X -> X".parse().unwrap();

        let unification = unify(&left, &right).unwrap();

        // crate::type_inference::print_type_var_equations(&unification);
        assert!(unification.contains_2(TypeVar::new("X"), Type::new_type_var("Y")));
        assert!(unification.contains_2(TypeVar::new("Y"), Type::Int));
    }
}
