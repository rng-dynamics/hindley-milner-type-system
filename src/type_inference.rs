use std::collections::HashMap;

use crate::ast::Def;
use crate::ast::Node;
use crate::r#type::Type;
use crate::token::TokenType;
use crate::type_var::TypeVar;
use crate::type_var_equation_set::TypeVarEquationSet;

struct TypeVarGenerator {
    count: u64,
}

impl TypeVarGenerator {
    fn new() -> Self {
        Self { count: 0 }
    }

    fn get_next(&mut self) -> TypeVar {
        let string = format!("type{}", self.count);
        self.count += 1;
        TypeVar::new(&string)
    }
}

struct TypeInference {}

impl TypeInference {
    pub(crate) fn generate_typenames(def: &mut Def) -> Result<(), String> {
        Self::generate_typenames_aux(&mut def.node, HashMap::new(), &mut TypeVarGenerator::new())?;
        Ok(())
    }

    pub(crate) fn create_type_var_equations(root_node: &Def) -> Result<TypeVarEquationSet, String> {
        Self::create_type_var_equations_from_node(&root_node.node)
    }

    pub(crate) fn unify_type_var_equations(
        equations: &TypeVarEquationSet,
    ) -> Result<TypeVarEquationSet, String> {
        let mut substitutions = TypeVarEquationSet::new();
        for va in equations.clone() {
            crate::unification::unify_variable(&va.lhs, &va.rhs, &mut substitutions)?;
        }
        Ok(substitutions)
    }

    pub(crate) fn apply_unifier(type_: &Type, substitutions: &TypeVarEquationSet) -> Type {
        if substitutions.is_empty() {
            return type_.clone();
        }
        match &type_ {
            Type::Int | Type::Bool => type_.clone(),
            Type::Var(type_var) => match substitutions.lookup_lhs(type_var) {
                Some(type_2) => Self::apply_unifier(&type_2, substitutions),
                _ => type_.clone(),
            },
            Type::Func(func_vec) => {
                let mut new_vec = vec![];
                for pp in func_vec {
                    let new_type = Self::apply_unifier(pp, substitutions);
                    new_vec.push(new_type);
                }
                Type::Func(new_vec)
            }
        }
    }

    fn generate_typenames_aux(
        node: &mut Node,
        symbol_table: HashMap<String, TypeVar>,
        type_var_generator: &mut TypeVarGenerator,
    ) -> Result<(), String> {
        match node.details {
            crate::ast::Details::IntLiteral(_) | crate::ast::Details::BoolLiteral(_) => {
                node.eval_type = Some(type_var_generator.get_next());
            }
            crate::ast::Details::Identifier => {
                if let Some(node_type) = symbol_table.get(&node.token.literal) {
                    node.eval_type = Some(node_type.clone());
                } else {
                    return Err(format!("name {} is not bound", node.token.literal));
                }
            }
            crate::ast::Details::OpExpr => {
                node.eval_type = Some(type_var_generator.get_next());
                Self::generate_typenames_aux(
                    &mut node.children[0],
                    symbol_table.clone(),
                    type_var_generator,
                )?;
                Self::generate_typenames_aux(
                    &mut node.children[1],
                    symbol_table,
                    type_var_generator,
                )?;
            }
            crate::ast::Details::FnAppExpr(ref mut fn_app_expr) => {
                if let Some(node_type) = symbol_table.get(&node.token.literal) {
                    fn_app_expr.fn_type = Some(node_type.clone());
                } else {
                    return Err(format!("name {} is not bound", node.token.literal));
                }
                node.eval_type = Some(type_var_generator.get_next());
                for arg in &mut node.children {
                    Self::generate_typenames_aux(arg, symbol_table.clone(), type_var_generator)?;
                }
            }
            crate::ast::Details::IfExpr => {
                node.eval_type = Some(type_var_generator.get_next());
                Self::generate_typenames_aux(
                    &mut node.children[0],
                    symbol_table.clone(),
                    type_var_generator,
                )?;
                Self::generate_typenames_aux(
                    &mut node.children[1],
                    symbol_table.clone(),
                    type_var_generator,
                )?;
                Self::generate_typenames_aux(
                    &mut node.children[2],
                    symbol_table,
                    type_var_generator,
                )?;
            }
            crate::ast::Details::LambdaExpr(ref mut lambda_expr) => {
                node.eval_type = Some(type_var_generator.get_next());
                lambda_expr.fn_type = Some(type_var_generator.get_next());
                let mut local_symbol_table = HashMap::new();
                let len = node.children.len();
                for arg in &mut node.children.iter_mut().take(len - 1) {
                    let type_var = type_var_generator.get_next();
                    local_symbol_table.insert(arg.token.literal.clone(), type_var.clone());
                    arg.eval_type = Some(type_var);
                }
                let extended_symbol_table: HashMap<String, TypeVar> =
                    symbol_table.into_iter().chain(local_symbol_table).collect();
                Self::generate_typenames_aux(
                    &mut node.children[len - 1],
                    extended_symbol_table,
                    type_var_generator,
                )?;
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn create_type_var_equations_from_node(root_node: &Node) -> Result<TypeVarEquationSet, String> {
        let mut type_var_assignment_set = TypeVarEquationSet::new();
        let mut stack: Vec<&Node> = vec![root_node];
        while let Some(curr_node) = stack.pop() {
            match &curr_node.details {
                crate::ast::Details::IntLiteral(_) => {
                    if let Some(tt) = &curr_node.eval_type {
                        type_var_assignment_set.insert_2(tt.clone(), Type::Int);
                    } else {
                        return Err("int literal does not have type".into());
                    }
                }
                crate::ast::Details::BoolLiteral(_) => {
                    if let Some(tt) = &curr_node.eval_type {
                        type_var_assignment_set.insert_2(tt.clone(), Type::Bool);
                    } else {
                        return Err("bool literal does not have type".into());
                    }
                }
                crate::ast::Details::Identifier => {
                    // nop
                }
                crate::ast::Details::OpExpr => {
                    for child in &curr_node.children {
                        stack.push(child);
                    }
                    // type depends on operator
                    let (ltype, rtype, rettype) = match &curr_node.token.type_ {
                        TokenType::Plus | TokenType::Asterisk => (Type::Int, Type::Int, Type::Int),
                        TokenType::Eq | TokenType::NotEq | TokenType::GtEq | TokenType::LtEq => {
                            (Type::Int, Type::Int, Type::Bool)
                        }
                        _ => {
                            return Err("unknown operator".into());
                        }
                    };
                    type_var_assignment_set.insert_2(
                        curr_node.children[0]
                            .eval_type
                            .clone()
                            .ok_or("operand does not have type")?,
                        ltype,
                    );
                    type_var_assignment_set.insert_2(
                        curr_node.children[1]
                            .eval_type
                            .clone()
                            .ok_or("operand does not have type")?,
                        rtype,
                    );
                    type_var_assignment_set.insert_2(
                        curr_node
                            .eval_type
                            .clone()
                            .ok_or("operand does not have return type")?,
                        rettype,
                    );
                }
                crate::ast::Details::FnAppExpr(fn_app_expr) => {
                    let mut fn_app_types: Vec<Type> = vec![];
                    for arg in &curr_node.children {
                        stack.push(arg);
                        fn_app_types.push(Type::Var(
                            arg.eval_type
                                .clone()
                                .ok_or("function argument does not have type")?,
                        ));
                    }
                    // Add return type
                    fn_app_types.push(Type::Var(
                        curr_node
                            .eval_type
                            .clone()
                            .ok_or("function does not have return type")?,
                    ));

                    type_var_assignment_set.insert_2(
                        fn_app_expr
                            .fn_type
                            .clone()
                            .ok_or("function does not have function type")?,
                        Type::Func(fn_app_types),
                    );
                }
                crate::ast::Details::IfExpr => {
                    for child in &curr_node.children {
                        stack.push(child);
                    }
                    type_var_assignment_set.insert_2(
                        curr_node.children[0]
                            .eval_type
                            .clone()
                            .ok_or("conditional expression does not have type")?,
                        Type::Bool,
                    );

                    // The then expression needs to be equal to the return type of the expression.
                    type_var_assignment_set.insert_2(
                        curr_node
                            .eval_type
                            .clone()
                            .ok_or("if expression does not have type")?,
                        Type::Var(
                            curr_node.children[1]
                                .eval_type
                                .clone()
                                .ok_or("then expression does not have type")?,
                        ),
                    );

                    // The else expression needs to be equal to the return type of the expression.
                    type_var_assignment_set.insert_2(
                        curr_node
                            .eval_type
                            .clone()
                            .ok_or("if expression does not have type")?,
                        Type::Var(
                            curr_node.children[2]
                                .eval_type
                                .clone()
                                .ok_or("else expression does not have type")?,
                        ),
                    );
                }
                crate::ast::Details::LambdaExpr(lambda_expr) => {
                    let mut child_types: Vec<Type> = vec![];
                    for child in &curr_node.children {
                        stack.push(child);
                        child_types.push(Type::Var(
                            child
                                .eval_type
                                .clone()
                                .ok_or("lambda expression parameter does not have type")?,
                        ));
                    }
                    type_var_assignment_set.insert_2(
                        lambda_expr
                            .fn_type
                            .clone()
                            .ok_or("lambda expression does not have function type")?,
                        Type::Func(child_types),
                    );

                    type_var_assignment_set.insert_2(
                        curr_node
                            .children
                            .last()
                            .ok_or("lambda expression does not have body")?
                            .eval_type
                            .clone()
                            .ok_or("lambda body does not have type")?,
                        Type::Var(
                            curr_node
                                .eval_type
                                .clone()
                                .ok_or("lambda expression does not have return type")?,
                        ),
                    );
                }
            }
        }
        Ok(type_var_assignment_set)
    }
}

pub(crate) fn print_type_var_equations(equations: &TypeVarEquationSet) {
    for va in equations.clone() {
        println!("{va}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parser::Parser, s_expr::SExpr};

    #[test]
    fn generate_typenames_1() {
        let input = "three = 3";
        let mut ast = Parser::new().parse_def(input).unwrap();

        TypeInference::generate_typenames(&mut ast).unwrap();

        assert_eq!("(def three 3 :: type0)", SExpr::from(&ast).to_string());
    }

    #[test]
    fn generate_typenames_2() {
        let input = "somedef = false";
        let mut ast = Parser::new().parse_def(input).unwrap();

        TypeInference::generate_typenames(&mut ast).unwrap();

        assert_eq!(
            "(def somedef false :: type0)",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn generate_typenames_3() {
        let input = "funcname param = true";
        let mut ast = Parser::new().parse_def(input).unwrap();

        TypeInference::generate_typenames(&mut ast).unwrap();

        assert_eq!(
            "(def funcname (lambda :: type1 (param :: type2) true :: type3) :: type0)",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn generate_typenames_4() {
        let input = "func p1 p2 = 5";
        let mut ast = Parser::new().parse_def(input).unwrap();

        TypeInference::generate_typenames(&mut ast).unwrap();

        assert_eq!(
            "(def func (lambda :: type1 (p1 :: type2 p2 :: type3) 5 :: type4) :: type0)",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn generate_typenames_5() {
        let input = "sum p1 p2 = p1 + p2";
        let mut ast = Parser::new().parse_def(input).unwrap();

        TypeInference::generate_typenames(&mut ast).unwrap();

        assert_eq!(
            "(def sum (lambda :: type1 (p1 :: type2 p2 :: type3) (+ p1 :: type2 p2 :: type3) :: type4) :: type0)",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn generate_typenames_6() {
        let input = "func f1 f2 p3 = if f1(p3 + 1) then f2(p3) else 42";
        let mut ast = Parser::new().parse_def(input).unwrap();

        TypeInference::generate_typenames(&mut ast).unwrap();

        assert_eq!(
            "(def func (lambda :: type1 (f1 :: type2 f2 :: type3 p3 :: type4) (if (f1 :: type2 (+ p3 :: type4 1 :: type8) :: type7) :: type6 (f2 :: type3 p3 :: type4) :: type9 42 :: type10) :: type5) :: type0)",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_create_type_var_equations() {
        let input = "foo f x = f(3) + f(x)";
        let mut ast = Parser::new().parse_def(input).unwrap();
        TypeInference::generate_typenames(&mut ast).unwrap();

        let type_assignment: TypeVarEquationSet =
            TypeInference::create_type_var_equations(&ast).unwrap();

        // print_type_var_equations(&type_assignment);

        assert!(type_assignment.contains_2(
            "type2".parse::<TypeVar>().unwrap(),
            "type3 -> type7".parse::<Type>().unwrap(),
        ));
        assert!(type_assignment.contains_2(
            "type2".parse::<TypeVar>().unwrap(),
            "type6 -> type5".parse::<Type>().unwrap(),
        ));
    }

    #[test]
    fn test_unify_type_var_equations_1() {
        let input = "func f1 f2 p3 = if f1(p3 + 1) then f2(p3) else 42";

        let mut ast = Parser::new().parse_def(input).unwrap();
        TypeInference::generate_typenames(&mut ast).unwrap();
        let type_var_assignment_set: TypeVarEquationSet =
            TypeInference::create_type_var_equations(&ast).unwrap();
        let type_equations =
            TypeInference::unify_type_var_equations(&type_var_assignment_set).unwrap();

        // print_type_var_equations(&type_var_assignment_set);
        // print_type_var_equations(&type_equations.clone());

        let rhs_for_t1 = type_var_assignment_set
            .lookup_lhs(&TypeVar::new("type1"))
            .unwrap();
        let rhs_for_t1_subst = TypeInference::apply_unifier(&rhs_for_t1, &type_equations);

        assert_eq!(
            rhs_for_t1_subst,
            "((Int -> Bool) * (Int -> Int) * Int -> Int)"
                .parse::<Type>()
                .unwrap()
        );
    }

    #[test]
    fn test_unify_type_var_equations_2() {
        let input = "func p1 = 42 != p1";

        let mut ast = Parser::new().parse_def(input).unwrap();
        TypeInference::generate_typenames(&mut ast).unwrap();
        let type_var_assignment_set: TypeVarEquationSet =
            TypeInference::create_type_var_equations(&ast).unwrap();
        let type_equations: TypeVarEquationSet =
            TypeInference::unify_type_var_equations(&type_var_assignment_set).unwrap();

        // print_type_var_equations(&type_var_assignment_set);
        // print_type_var_equations(&type_equations);

        let rhs_for_t1 = type_var_assignment_set
            .lookup_lhs(&TypeVar::new("type1"))
            .unwrap();
        let rhs_for_t1_subst = TypeInference::apply_unifier(&rhs_for_t1, &type_equations);

        assert_eq!(rhs_for_t1_subst, "Int -> Bool".parse::<Type>().unwrap());
    }

    #[test]
    fn test_unify_type_var_equations_3() {
        let input = "foo f x = f(3) + f(x)";
        let mut ast = Parser::new().parse_def(input).unwrap();
        TypeInference::generate_typenames(&mut ast).unwrap();

        let type_var_assignment_set: TypeVarEquationSet =
            TypeInference::create_type_var_equations(&ast).unwrap();
        let type_equations: TypeVarEquationSet =
            TypeInference::unify_type_var_equations(&type_var_assignment_set).unwrap();

        // print_type_var_equations(&type_var_assignment_set);
        // print_type_var_equations(&type_equations);

        let rhs_for_t1 = type_var_assignment_set
            .lookup_lhs(&TypeVar::new("type1"))
            .unwrap();
        let rhs_for_t1_subst = TypeInference::apply_unifier(&rhs_for_t1, &type_equations);

        assert_eq!(
            rhs_for_t1_subst,
            "(Int -> Int) * Int -> Int".parse::<Type>().unwrap()
        );
    }

    #[test]
    fn test_unify_type_var_equations_4() {
        let input = "double x = x + x";
        let mut ast = Parser::new().parse_def(input).unwrap();
        TypeInference::generate_typenames(&mut ast).unwrap();

        let type_var_assignment_set: TypeVarEquationSet =
            TypeInference::create_type_var_equations(&ast).unwrap();
        let type_equations: TypeVarEquationSet =
            TypeInference::unify_type_var_equations(&type_var_assignment_set).unwrap();

        // print_type_var_equations(&type_var_assignment_set);
        // print_type_var_assignments(&type_equations);

        let rhs_for_t1 = type_var_assignment_set
            .lookup_lhs(&TypeVar::new("type1"))
            .unwrap();
        let rhs_for_t1_subst = TypeInference::apply_unifier(&rhs_for_t1, &type_equations);

        assert_eq!(rhs_for_t1_subst, "Int -> Int".parse::<Type>().unwrap());
    }
}
