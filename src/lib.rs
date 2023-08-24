#![warn(rust_2018_idioms)]
#![warn(clippy::pedantic)]
#![cfg(test)]
#![allow(dead_code)]

#[macro_use]
extern crate lazy_static;

mod ast;
mod lexer;
mod parser;
mod s_expr;
mod token;
mod r#type;
mod type_var;
mod type_var_equation;
mod type_var_equation_set;
mod unification;
