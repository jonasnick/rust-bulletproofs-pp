//! Implementation of Bulletproofs++ in rust

mod norm_arg;
mod rangeproof;

pub use rangeproof::{Proof, Prover, Verifier, commit};
use norm_arg::log;
use norm_arg::VerifyVectors;

fn main() {
    println!("{}", VerifyVectors::new().to_C());
}
