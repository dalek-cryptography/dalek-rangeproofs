# dalek-rangeproofs

This repo **was**:

A pure-Rust implementation of the Back-Maxwell rangeproof scheme defined in
["Confidential Assets" (2017) by Poelstra, Back, Friedenbach, Maxwell, Wuille](https://blockstream.com/bitcoin17-final41.pdf).

**THIS IS A PROOF-OF-CONCEPT OF A SCHEME WHICH IS NOW OBSOLETE, USE BULLETPROOFS**

## Warning

This code has **not** yet received sufficient peer review by other qualified
cryptographers to be considered in any way, shape, or form, safe.

**USE AT YOUR OWN RISK**

## Documentation

Extensive documentation is available [here](https://docs.rs/dalek-rangeproofs).

# Installation

To install, add the following to the dependencies section of your project's
`Cargo.toml`:

    dalek-rangeproofs = "^0.1"

Then, in your library or executable source, add:

    extern crate dalek_rangeproofs

# Tests and benchmarks

Tests may be run with:

    cargo test

Benchmarks may be taken with:

    cargo bench --features 'bench'


# Pre-Release TODOs

* move RangeProof code to `back_maxwell.rs` module
* double check documentation
* double check code
* don't use any yolocrypto features (i.e. stabilise decaf in curve25519-dalek)
* make a CONTRIBUTING.md

# Future TODOs

* support other rangeproof schemes?
* make hash function choice configurable?
* make the code generic w.r.t. to a future Group trait
