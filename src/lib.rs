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
use curve25519_dalek::decaf::{DecafPoint, CompressedDecaf, DecafBasepointTable};
use curve25519_dalek::decaf::vartime;

use curve25519_dalek::constants as dalek_constants;

pub const RANGEPROOF_N: usize = 24;

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
        let mut points = vec![G.basepoint(), H.basepoint(), DecafPoint::identity()];
        let mut scalars = vec![Scalar::zero(), Scalar::zero(), Scalar::zero()];

        let two = Scalar::from_u64(2);

        let mut e_0_hash = Sha512::default();
        let mut C = DecafPoint::identity();

        for i in 0..RANGEPROOF_N {
            points[2] = self.C[i];

            scalars[0] = self.s_1[i]; 
            scalars[1] = &self.e_0 * &POWERS_OF_THREE[i];
            scalars[2] = -&self.e_0;
            // P = s_1[i]*G + e_0*m^i*H - e_0*C[i] 
            let P = vartime::k_fold_scalar_mult(&scalars, &points);
            let e_1_i = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

            scalars[0] = self.s_2[i];
            scalars[1] = &(&e_1_i * &two) * &POWERS_OF_THREE[i];
            scalars[2] = -&e_1_i;
            // P = s_2[i]*G + 2*e_1*m^i*H - e_1*C[i] 
            let P = vartime::k_fold_scalar_mult(&scalars, &points);
            let e_2_i = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

            let R_i = &self.C[i] * &e_2_i;
            e_0_hash.input(R_i.compress().as_bytes());
            C = self.C[i];
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
        let mut k_0 = [Scalar::zero(); RANGEPROOF_N];
        let mut r   = [Scalar::zero(); RANGEPROOF_N];
        let mut s_1 = [Scalar::zero(); RANGEPROOF_N];
        let mut s_2 = [Scalar::zero(); RANGEPROOF_N];
        let mut e_1 = [Scalar::zero(); RANGEPROOF_N];
        let mut e_2 = [Scalar::zero(); RANGEPROOF_N];

        let mut e_0_hash = Sha512::default();

        let two = Scalar::from_u64(2);

        for i in 0..RANGEPROOF_N {
            if v[i] == 0 {
                k_0[i] = Scalar::random(&mut rng);
                R[i] = G * &k_0[i];
            } else if v[i] == 1 {
                r[i] = Scalar::random(&mut rng);
                C[i] = &(H * &POWERS_OF_THREE[i]) + &(G * &r[i]);
                k_0[i] = Scalar::random(&mut rng);
                e_1[i] = Scalar::hash_from_bytes::<Sha512>((G * &k_0[i]).compress().as_bytes());
                s_2[i] = Scalar::random(&mut rng);
                let mi_e1i_2 = &(&POWERS_OF_THREE[i] * &two) * &e_1[i];
                let P = &(&(G * &s_2[i]) - &(&C[i] * &e_1[i])) + &(H * &mi_e1i_2);
                // XXX fix the fucking RHS bullshit
                e_2[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());
                R[i] = &C[i] * &e_2[i];
            } else {
                // XXX these three lines are repeateed above
                r[i] = Scalar::random(&mut rng);
                C[i] = &(H * &POWERS_OF_THREE[i]) + &(G * &r[i]);
                k_0[i] = Scalar::random(&mut rng);
                e_2[i] = Scalar::hash_from_bytes::<Sha512>((G * &k_0[i]).compress().as_bytes());
                R[i] = &C[i] * &e_2[i];
            }
            e_0_hash.input(R[i].compress().as_bytes());
        }
            
        let e_0 = Scalar::from_hash(e_0_hash);

        for i in 0..RANGEPROOF_N {
            if v[i] == 0 {
                let k_1 = Scalar::random(&mut rng);
                let P = &(G * &k_1) + &(H * &(&e_0 * &POWERS_OF_THREE[i]));
                e_1[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

                let k_2 = Scalar::random(&mut rng);
                let P = &(G * &k_2) + &(H * &(&e_1[i] * &(&POWERS_OF_THREE[i] * &two)));
                e_2[i] = Scalar::hash_from_bytes::<Sha512>(P.compress().as_bytes());

                let e_2_inv = e_2[i].invert();

                C[i] = G * &(&e_2_inv * &k_0[i]);

                s_1[i] = &k_1 + &(&k_0[i] * &(&e_0 * &e_2_inv));
                s_2[i] = &k_2 + &(&k_0[i] * &(&e_1[i] * &e_2_inv));
            } else if v[i] == 1 {
                s_1[i] = Scalar::multiply_add(&e_0, &r[i], &k_0[i]);
            } else { 
                s_1[i] = Scalar::random(&mut rng);
                let P = &(&(G * &s_1[i]) - &(&C[i] * &e_0)) - &(H * &(&e_0 * &POWERS_OF_THREE[i]));
                s_2[i] = Scalar::multiply_add(&e_1[i], &r[i], &k_0[i]);
            }
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

pub const POWERS_OF_THREE: [Scalar; 41] = [
    Scalar([  1,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([  3,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([  9,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 27,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 81,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([243,   0,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([217,   2,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([139,   8,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([161,  25,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([227,  76,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([169, 230,   0,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([251, 179,   2,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([241,  27,   8,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([211,  83,  24,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([121, 251,  72,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([107, 242, 218,   0,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 65, 215, 144,   2,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([195, 133, 178,   7,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 73, 145,  23,  23,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([219, 179,  70,  69,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([145,  27, 212, 207,   0,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([179,  82, 124, 111,   2,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 25, 248, 116,  78,   7,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 75, 232,  94, 235,  21,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([225, 184,  28, 194,  65,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([163,  42,  86,  70, 197,   0,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([233, 127,   2, 211,  79,   2,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([187, 127,   7, 121, 239,   6,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 49, 127,  22, 107, 206,  20,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([147, 125,  67,  65, 107,  62,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([185, 120, 202, 195,  65, 187,   0,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 43, 106,  95,  75, 197,  49,   2,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([129,  62,  30, 226,  79, 149,   6,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([131, 187,  90, 166, 239, 191,  19,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([137,  50,  16, 243, 206,  63,  59,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([155, 151,  48, 217, 108, 191, 177,   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([209, 198, 145, 139,  70,  62,  21,   2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([115,  84, 181, 162, 211, 186,  63,   6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 89, 253,  31, 232, 122,  48, 191,  18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 11, 248,  95, 184, 112, 145,  61,  56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    Scalar([ 33, 232,  31,  41,  82, 180, 184, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    ];


#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn it_works() {
    }

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
    fn check_powers_of_three_table() {
        let mut m = Scalar::zero();
        m[0] = 3;
        let mut x = Scalar::one();
        for i in 0..41 {
            assert_eq!(x, POWERS_OF_THREE[i]);
            x *= &m;
        }
    }

    #[test]
    fn prove_seven() {
        let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
        let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));

        let value = 7;
        let (proof, blinding) = RangeProof::create_vartime(value, G, &H).unwrap();

        let C = proof.verify(G, &H).unwrap();
    }
}

#[cfg(test)]
mod bench {
    use test::Bencher;
    use super::*;

    #[bench]
    fn bench_verify_seven(b: &mut Bencher) {
        let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
        let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));

        let value = 7;
        let (proof, blinding) = RangeProof::create_vartime(value, G, &H).unwrap();

        b.iter(|| proof.verify(G, &H));
    }

    #[bench]
    fn bench_prove_seven(b: &mut Bencher) {
        let G = &dalek_constants::DECAF_ED25519_BASEPOINT_TABLE;
        let H = DecafBasepointTable::create(&(G * &Scalar::from_u64(10352669767914021650)));

        let value = 7;
        b.iter(|| RangeProof::create_vartime(value, G, &H));
    }

    #[bench]
    fn bench_base3_digits(b: &mut Bencher) {
        b.iter(|| base3_digits(10352669767914021650) );
    }
}
