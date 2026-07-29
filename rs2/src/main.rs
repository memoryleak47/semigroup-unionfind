use symbol_table::GlobalSymbol as Symbol;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::fmt::Debug;

mod api;
pub use api::*;

mod fmt;

mod uf;
pub use uf::*;

mod egraph;
pub use egraph::*;

mod baseline_ematch;
pub use baseline_ematch::*;

mod ematch;
pub use ematch::*;

mod eqsat;
pub use eqsat::*;

// Examples:
mod cases;

fn main() {
    cases::caviar_offset::run_caviar();
}
