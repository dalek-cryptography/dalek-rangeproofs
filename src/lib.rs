// -*- coding: utf-8; mode: rust; -*-
//
// To the extent possible under law, the authors have waived all
// copyright and related or neighboring rights to dalek-rangeproofs,
// using the Creative Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full
// details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! A pure-Rust implementation of the Back-Maxwell rangeproof scheme defined in
//! ["Confidential Assets" (2017) by Poelstra, Back, Friedenbach, Maxwell,
//! Wuille](https://blockstream.com/bitcoin17-final41.pdf).
//!
//! # Examples
//!
//! To construct a proof that `134492616741` is within `[0,3^RANGEPROOF_N]`,
//! first, select your basepoints (usually this will be set or distributed
//! within some system-wide parameters):
//!
//! ```
//! # extern crate curve25519_dalek;
//! # fn main() {
//! use curve25519_dalek::constants as dalek_constants;
//! use curve25519_dalek::decaf::DecafBasepointTable;
//! use curve25519_dalek::scalar::Scalar;
//!
//! let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
//! let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));
//! # }
//!
//! ```
//!
//! You'll also need your value and a CSPRNG:
//!
//! ```
//! # extern crate rand;
//! # fn main() {
//! use rand::OsRng;
//!
//! let mut csprng = OsRng::new().unwrap();
//! let value = 134492616741;
//! # }
//! ```
//!
//! We can now create the rangeproof and blinding factor, like so:
//!
//! ```
//! # extern crate dalek_rangeproofs;
//! # extern crate curve25519_dalek;
//! # extern crate rand;
//! # fn main() {
//! # use curve25519_dalek::constants as dalek_constants;
//! # use curve25519_dalek::decaf::DecafBasepointTable;
//! # use curve25519_dalek::scalar::Scalar;
//! # use rand::OsRng;
//! #
//! # let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
//! # let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));
//! # let mut csprng = OsRng::new().unwrap();
//! # let value = 134492616741;
//!
//! use dalek_rangeproofs::RangeProof;
//!
//! let (proof, blinding) = RangeProof::create(value, G, &H, &mut csprng).unwrap();
//! # }
//! ```
//!
//! Another party can verify this `proof` by doing:
//!
//! ```
//! # extern crate dalek_rangeproofs;
//! # extern crate curve25519_dalek;
//! # extern crate rand;
//! # fn main() {
//! # use curve25519_dalek::constants as dalek_constants;
//! # use curve25519_dalek::decaf::DecafBasepointTable;
//! # use curve25519_dalek::scalar::Scalar;
//! # use rand::OsRng;
//! #
//! # let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
//! # let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));
//! # let mut csprng = OsRng::new().unwrap();
//! # let value = 134492616741;
//!
//! use dalek_rangeproofs::RangeProof;
//!
//! # let (proof, blinding) = RangeProof::create(value, G, &H, &mut csprng).unwrap();
//!
//! let C_option = proof.verify(G, &H);
//! assert!(C_option.is_some());
//!
//! let C = C_option.unwrap();
//! # }
//! ```
//!
//! As we can see above, verifying the `proof` returns an option for
//! something we've called `C`.  This `C` is a Pedersen commitment to
//! `value`.  However, without knowing both `blinding` and the actual
//! `value`, the verifier cannot open this commitment, because Pedersen
//! commitments are computationally binding and perfectly hiding (in
//! addition to being additively homomorphic, a feature used within this
//! scheme).
//!
//! To open this commitment, one would do:
//!
//! ```
//! # extern crate dalek_rangeproofs;
//! # extern crate curve25519_dalek;
//! # extern crate rand;
//! # fn main() {
//! # use curve25519_dalek::constants as dalek_constants;
//! # use curve25519_dalek::decaf::DecafBasepointTable;
//! # use curve25519_dalek::scalar::Scalar;
//! # use rand::OsRng;
//! #
//! # use dalek_rangeproofs::RangeProof;
//! #
//! # let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
//! # let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));
//! # let mut csprng = OsRng::new().unwrap();
//! # let value = 134492616741;
//! #
//! # let (proof, blinding) = RangeProof::create(value, G, &H, &mut csprng).unwrap();
//! # let C_option = proof.verify(G, &H);
//! # let C = C_option.unwrap();
//! let C_hat = &(G * &blinding) + &(&H * &Scalar::from_u64(value));
//! assert_eq!(C.compress(), C_hat.compress());
//! # }
//! ```
//!
//! However, obviously, the prover should *not* give either the `blinding`
//! or the `value` to any other party, unless the prover wishes to reveal
//! the `value` *not* in zero-knowledge.

#![allow(non_snake_case)]

#![feature(test)]
extern crate test;

extern crate curve25519_dalek;
extern crate sha2;
extern crate rand;

use rand::OsRng;

use sha2::Sha512;
use sha2::Digest;

use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::curve::{Identity};
use curve25519_dalek::decaf::{DecafPoint, DecafBasepointTable};
use curve25519_dalek::decaf::vartime;

pub const RANGEPROOF_N: usize = 40;

struct RangeProof {
    e_0: Scalar,
    C: [DecafPoint; RANGEPROOF_N],
    s_1: [Scalar; RANGEPROOF_N],
    s_2: [Scalar; RANGEPROOF_N],
}

impl RangeProof {
    /// Verify the rangeproof, returning a Pedersen commitment to the
    /// in-range value if successful.
    pub fn verify(&self,
                  G: &DecafBasepointTable,
                  H: &DecafBasepointTable)
                  -> Option<DecafPoint> {
        let mut e_0_hash = Sha512::default();
        let mut C = DecafPoint::identity();

        let mut mi_H = H.basepoint();

        for i in 0..RANGEPROOF_N {
            let mi2_H = &mi_H + &mi_H;

            let Ci_minus_miH = &self.C[i] - &mi_H;
            let P = vartime::k_fold_scalar_mult(&[self.s_1[i], -&self.e_0],
                                                &[G.basepoint(), Ci_minus_miH]);
            let ei_1 = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

            let Ci_minus_2miH = &self.C[i] - &mi2_H;
            let P = vartime::k_fold_scalar_mult(&[self.s_2[i], -&ei_1],
                                                &[G.basepoint(), Ci_minus_2miH]);
            let ei_2 = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

            let Ri = &self.C[i] * &ei_2;
            e_0_hash.input(Ri.compress().as_bytes());
            C = &C + &self.C[i];

            // Set mi_H <-- 3*m_iH, so that mi_H is always 3^i * H in the loop
            mi_H = &mi_H + &mi2_H;
        }

        let e_0_hat = Scalar::from_hash(e_0_hash);

        if e_0_hat == self.e_0 {
            return Some(C);
        } else {
            return None;
        }
    }

    /// Construct a rangeproof for `value` in variable time.
    pub fn create_vartime(value: u64,
                          G: &DecafBasepointTable,
                          H: &DecafBasepointTable,
    ) -> Option<(RangeProof,Scalar)> {
        let v = base3_digits(value);

        // Check that v is in range: all digits above N should be 0
        for i in RANGEPROOF_N..41 {
            if v[i] != 0 { return None; }
        }

        let mut rng = OsRng::new().unwrap();

        let mut R = [DecafPoint::identity(); RANGEPROOF_N];
        let mut C = [DecafPoint::identity(); RANGEPROOF_N];
        let mut k   = [Scalar::zero(); RANGEPROOF_N];
        let mut r   = [Scalar::zero(); RANGEPROOF_N];
        let mut s_1 = [Scalar::zero(); RANGEPROOF_N];
        let mut s_2 = [Scalar::zero(); RANGEPROOF_N];
        let mut e_1 = [Scalar::zero(); RANGEPROOF_N];
        let mut e_2 = [Scalar::zero(); RANGEPROOF_N];

        let mut mi_H = H.basepoint();
        for i in 0..RANGEPROOF_N {
            let mi2_H = &mi_H + &mi_H;
            k[i] = Scalar::random(&mut rng);

            if v[i] == 0 {
                R[i] = G * &k[i];
            } else if v[i] == 1 {
                // Commitment to i-th digit is r^i G + 1 * m^i H
                r[i] = Scalar::random(&mut rng);
                C[i] = &(G * &r[i]) + &mi_H;
                // Begin at index 1 in the ring, choosing random e_1
                let P = G * &k[i];
                e_1[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());
                // Choose random scalar for s_2
                s_2[i] = Scalar::random(&mut rng);
                // Compute e_2 = Hash(s_2^i G - e_1^i (C^i - 2m^i H) )
                let Ci_minus_mi2H = &C[i] - &mi2_H;
                let P = vartime::k_fold_scalar_mult(&[s_2[i],       -&e_1[i]],
                                                    &[G.basepoint(), Ci_minus_mi2H]);
                e_2[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

                R[i] = &C[i] * &e_2[i];
            } else if v[i] == 2 {
                // Commitment to i-th digit is r^i G + 2 * m^i H
                r[i] = Scalar::random(&mut rng);
                C[i] = &(G * &r[i]) + &mi2_H;
                // Begin at index 2 in the ring, choosing random e_2
                let P = G * &k[i];
                e_2[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

                R[i] = &C[i] * &e_2[i];
            } else {
                panic!(); /* invalid digit */
            } 

            // Set mi_H <- m * mi_H so that mi_H = m^i H in the loop
            mi_H = &mi2_H + &mi_H;
        }

        // Compute e_0 = Hash( R^0 || ... || R^{n-1} )
        let mut e_0_hash = Sha512::default();
        for i in 0..RANGEPROOF_N {
            e_0_hash.input(R[i].compress().as_bytes());
        }
        let e_0 = Scalar::from_hash(e_0_hash);

        let mut mi_H = H.basepoint();
        for i in 0..RANGEPROOF_N {
            let mi2_H = &mi_H + &mi_H;
            if v[i] == 0 {
                let k_1 = Scalar::random(&mut rng);
                let P = vartime::k_fold_scalar_mult(&[k_1, e_0], &[G.basepoint(), mi_H]);
                e_1[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

                let k_2 = Scalar::random(&mut rng);
                let P = vartime::k_fold_scalar_mult(&[k_2, e_1[i]], &[G.basepoint(), mi2_H]);
                e_2[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

                let e_2_inv = e_2[i].invert();
                r[i] = &e_2_inv * &k[i];
                C[i] = G * &r[i];

                s_1[i] = &k_1 + &(&e_0    * &(&k[i] * &e_2_inv));
                s_2[i] = &k_2 + &(&e_1[i] * &(&k[i] * &e_2_inv));
            } else if v[i] == 1 {
                s_1[i] = Scalar::multiply_add(&e_0, &r[i], &k[i]);
            } else if v[i] == 2 { 
                s_1[i] = Scalar::random(&mut rng);
                // Compute e_1^i = Hash(s_1^i G - e_0^i (C^i - 1 m^i H) )
                let Ci_minus_miH = &C[i] - &mi_H;
                let P = vartime::k_fold_scalar_mult(&[s_1[i],        -&e_0],
                                                    &[G.basepoint(), Ci_minus_miH]);
                e_1[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());
                s_2[i] = Scalar::multiply_add(&e_1[i], &r[i], &k[i]);
            }
            // Set mi_H <-- 3*m_iH, so that mi_H is always 3^i * H in the loop
            mi_H = &mi_H + &mi2_H;
        }
    
        let mut r_sum = Scalar::zero();
        for i in 0..RANGEPROOF_N {
            r_sum += &r[i];
        }

        Some((RangeProof{e_0: e_0, C: C, s_1: s_1, s_2: s_2}, r_sum))
    }

    /// Construct a rangeproof for `value` in constant time.
    ///
    /// Executes in constant time for all values of `value` in range.
    ///
    /// If `value` is out of range, returns an error early.
    pub fn create(value: u64) -> Option<RangeProof> {
        unimplemented!();
    }
}

pub fn base3_digits(mut x: u64) -> [u8; 41] {
    let mut digits = [0u8; 41];
    for i in 0..41 {
        let rem = x % 3;
        digits[i] = rem as u8;
        x = x / 3;
    }
    digits
}

#[cfg(test)]
mod tests {
    use super::*;
    
    use curve25519_dalek::constants as dalek_constants;

    #[test]
    fn base3_digits_vs_sage() {
        let values: [u64; 10] = [10352669767914021650,  7804842618637096123,
                                  7334633556203117754,  8160423201521470302,
                                 17232767106382697250,  8845500362072010910,
                                  9696550650556789001,   769845413554321661,
                                  3398590720602317514, 14390516357262902374];
        let digits_sage: [[u8;41]; 10] = [
            [2, 2, 0, 2, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 0, 1, 0, 2, 2, 1, 0, 1, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 2, 1, 1, 2, 0],
            [1, 1, 2, 2, 1, 0, 1, 2, 1, 0, 0, 1, 0, 2, 2, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 0, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 0, 2, 2, 1, 0],
            [0, 1, 1, 0, 2, 2, 1, 2, 0, 0, 0, 2, 0, 2, 1, 1, 0, 2, 1, 0, 0, 0, 2, 0, 0, 1, 2, 1, 1, 2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1, 0],
            [0, 2, 0, 1, 2, 2, 0, 0, 2, 2, 2, 2, 0, 2, 2, 0, 1, 1, 1, 1, 0, 1, 0, 2, 0, 2, 1, 2, 2, 1, 1, 2, 2, 0, 0, 1, 0, 0, 0, 2, 0],
            [0, 1, 2, 1, 2, 2, 0, 2, 0, 0, 2, 2, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 2, 1, 2, 2, 2, 0, 1, 1, 2, 2, 0, 1, 2, 0, 2, 0, 1, 1],
            [1, 2, 0, 2, 2, 0, 2, 1, 0, 1, 2, 1, 2, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 1, 1, 0, 2, 0, 0, 0, 2, 1, 0, 1, 2, 2, 1, 1, 0, 2, 0],
            [2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 2, 2, 0, 0, 2, 2, 1, 0, 1, 0, 2, 1, 1, 1, 2, 0, 1, 2, 1, 1, 0, 1, 2, 0],
            [2, 2, 2, 1, 2, 2, 1, 2, 0, 2, 1, 0, 2, 1, 1, 2, 2, 2, 2, 0, 2, 1, 0, 1, 2, 0, 1, 2, 0, 0, 1, 1, 1, 0, 1, 0, 2, 1, 0, 0, 0],
            [0, 1, 1, 2, 0, 1, 1, 1, 2, 1, 0, 0, 2, 2, 2, 0, 0, 1, 1, 1, 2, 2, 0, 0, 0, 2, 2, 1, 0, 2, 0, 0, 1, 2, 2, 1, 1, 1, 2, 0, 0],
            [1, 2, 0, 0, 1, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 2, 0, 0, 2, 1, 0, 1, 2, 2, 1, 2, 2, 0, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 0, 1],
        ];

        for i in 0..10 {
            let digits = base3_digits(values[i]);
            for j in 0..41 {
                assert_eq!(digits[j], digits_sage[i][j]);
            }
        }
    }

    #[test]
    fn prove_and_verify() {
        let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
        let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));

        let value = 134492616741;
        let (proof, blinding) = RangeProof::create_vartime(value, G, &H).unwrap();

        let C_option = proof.verify(G, &H);
        assert!(C_option.is_some());

        let C = C_option.unwrap();
        let C_hat = &(G * &blinding) + &(&H * &Scalar::from_u64(value));

        assert_eq!(C.compress(), C_hat.compress());
    }
}

#[cfg(test)]
mod bench {
    use test::Bencher;
    use super::*;

    use curve25519_dalek::constants as dalek_constants;

    #[bench]
    fn verify(b: &mut Bencher) {
        let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
        let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));

        let value = 0;
        let (proof, _) = RangeProof::create_vartime(value, G, &H).unwrap();

        b.iter(|| proof.verify(G, &H));
    }

    #[bench]
    fn prove(b: &mut Bencher) {
        let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
        let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));

        let value = 1666;
        b.iter(|| RangeProof::create_vartime(value, G, &H));
    }

    #[bench]
    fn bench_base3_digits(b: &mut Bencher) {
        b.iter(|| base3_digits(10352669767914021650) );
    }
}
