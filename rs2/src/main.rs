use symbol_table::GlobalSymbol as Symbol;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

mod uf;
pub use uf::*;

mod egraph;
pub use egraph::*;

// Examples:
mod slotted;
mod linear;

fn main() {}
