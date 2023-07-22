#![warn(rust_2018_idioms)]
#![warn(clippy::pedantic)]

#![cfg(test)]
#![allow(dead_code)]

#[macro_use]
extern crate lazy_static;

mod lexer;
mod token;
