#![allow(dead_code)]
#![feature(let_chains, impl_trait_in_assoc_type)]

use std::hash::{Hash, Hasher};

pub mod ast;
pub mod bytecode;
mod environment;
pub mod il;

fn xxhash(x: impl Hash) -> u64 {
    let mut hasher = twox_hash::xxh3::Hash64::with_seed(0);
    x.hash(&mut hasher);
    hasher.finish()
}
