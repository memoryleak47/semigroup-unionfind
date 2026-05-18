use symbol_table::GlobalSymbol as Symbol;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::fmt::Debug;

mod api;
pub use api::*;

mod uf;
pub use uf::*;

mod egraph;
pub use egraph::*;

// Examples:
mod slotted;
mod linear;
mod proofs;

fn main() {}
