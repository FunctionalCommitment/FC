#![deny(missing_docs)]
#![allow(non_snake_case)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use clear_on_drop::clear::Clear;
// use curve25519_dalek::scalar::Scalar;
use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective};
use ff_zeroize::{Field, PrimeField};
use crate::inner_product_proof::inner_product;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct VecPoly1(pub Vec<FrRepr>, pub Vec<FrRepr>);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[cfg(feature = "yoloproofs")]
pub struct VecPoly3(
    pub Vec<FrRepr>,
    pub Vec<FrRepr>,
    pub Vec<FrRepr>,
    pub Vec<FrRepr>,
);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct Poly2(pub FrRepr, pub FrRepr, pub FrRepr);

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp {
    x: FrRepr,
    next_exp_x: FrRepr,
}

impl Iterator for ScalarExp {
    type Item = FrRepr;

    fn next(&mut self) -> Option<FrRepr> {
        let exp_x = self.next_exp_x;
        // self.next_exp_x *= self.x;
        let mut tmp = Fr::from_repr(self.next_exp_x).unwrap();
        tmp.mul_assign(&Fr::from_repr(self.x).unwrap());
        self.next_exp_x = tmp.into();
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: FrRepr) -> ScalarExp {
    let next_exp_x = FrRepr([1, 0, 0, 0]);
    ScalarExp { x, next_exp_x }
}

pub fn add_vec(a: &[FrRepr], b: &[FrRepr]) -> Vec<FrRepr> {
    if a.len() != b.len() {
        // throw some error
        //println!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![FrRepr([0, 0, 0, 0]); b.len()];
    for i in 0..a.len() {
        let mut tmp = Fr::from_repr(a[i]).unwrap();
        tmp.add_assign(&Fr::from_repr(b[i]).unwrap());
        out[i] = tmp.into();
        // out[i] = a[i] + b[i];
    }
    out
}

impl VecPoly1 {
    pub fn zero(n: usize) -> Self {
        // VecPoly1(vec![Scalar::ZERO; n], vec![Scalar::ZERO; n])
        VecPoly1(vec![FrRepr([0, 0, 0, 0]); n], vec![FrRepr([0, 0, 0, 0]); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1) -> Poly2 {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        // let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;
        let mut tmp = Fr::from_repr(inner_product(&l0_plus_l1, &r0_plus_r1)).unwrap();
        tmp.sub_assign(&Fr::from_repr(t0).unwrap());
        tmp.sub_assign(&Fr::from_repr(t2).unwrap());
        let t1 = tmp.into();

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: FrRepr) -> Vec<FrRepr> {
        let n = self.0.len();
        let mut out = vec![FrRepr([0, 0, 0, 0]); n];
        for i in 0..n {
            // out[i] = self.0[i] + self.1[i] * x;
            let mut tmp = Fr::from_repr(self.1[i]).unwrap();
            tmp.mul_assign(&Fr::from_repr(x).unwrap());
            tmp.add_assign(&Fr::from_repr(self.0[i]).unwrap());
            out[i] = tmp.into();
        }
        out
    }
}

#[cfg(feature = "yoloproofs")]
impl VecPoly3 {
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![FrRepr([0 0 0 0]); n],
            vec![FrRepr([0 0 0 0]); n],
            vec![FrRepr([0 0 0 0]); n],
            vec![FrRepr([0 0 0 0]); n],
        )
    }

    pub fn eval(&self, x: FrRepr) -> Vec<FrRepr> {
        let n = self.0.len();
        let mut out = vec![FrRepr([0 0 0 0]); n];
        for i in 0..n {
            // out[i] = self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
            let mut tmp = Fr::fr_repr(self.3[i]);
            let x_fr = Fr::fr_repr(x);
            tmp.mul_assign(&x_fr);
            tmp.add_assign(&Fr::fr_repr(self.2[i]));
            tmp.mul_assign(&x_fr);
            tmp.add_assign(&Fr::fr_repr(self.1[i]));
            tmp.mul_assign(&x_fr);
            tmp.add_assign(&Fr::fr_repr(self.0[i]));
            out[i] = tmp.into();
        }
        out
    }
}

impl Poly2 {
    pub fn eval(&self, x: FrRepr) -> FrRepr {
        // self.0 + x * (self.1 + x * self.2)
        let mut tmp = Fr::from_repr(self.2).unwrap();
        tmp.mul_assign(&Fr::from_repr(x).unwrap());
        tmp.add_assign(&Fr::from_repr(self.1).unwrap());
        tmp.mul_assign(&Fr::from_repr(x).unwrap());
        tmp.add_assign(&Fr::from_repr(self.0).unwrap());

        tmp.into()
    }
}

impl Drop for VecPoly1 {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.clear();
        }
        for e in self.1.iter_mut() {
            e.clear();
        }
    }
}

impl Drop for Poly2 {
    fn drop(&mut self) {
        self.0.clear();
        self.1.clear();
        self.2.clear();
    }
}

#[cfg(feature = "yoloproofs")]
impl Drop for VecPoly3 {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.clear();
        }
        for e in self.1.iter_mut() {
            e.clear();
        }
        for e in self.2.iter_mut() {
            e.clear();
        }
        for e in self.3.iter_mut() {
            e.clear();
        }
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with (1 to 2)*lg(n) scalar multiplications.
/// TODO: a consttime version of this would be awfully similar to a Montgomery ladder.
pub fn scalar_exp_vartime(x: &FrRepr, mut n: u64) -> FrRepr {
    // let mut result = Scalar::ONE;
    let mut result = Fr::one();
    let mut aux = Fr::from_repr(*x).unwrap(); // x, x^2, x^4, x^8, ...
    while n > 0 {
        let bit = n & 1;
        if bit == 1 {
            // result = result * aux;
            result.mul_assign(&aux);
        }
        n = n >> 1;
        // aux = aux * aux; // FIXME: one unnecessary mult at the last step here!
        let tmp = aux.clone();
        aux.mul_assign(&tmp);
    }
    result.into()
}

/// Takes the sum of all the powers of `x`, up to `n`
/// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
/// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
/// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn sum_of_powers(x: &FrRepr, n: usize) -> FrRepr {
    // if !n.is_power_of_two() {
    //     return sum_of_powers_slow(x, n);
    // }
    if n == 0 || n == 1 {
        // return Scalar::from(n as u64);
        return FrRepr([0, 0, 0, 0]);
    }
    let mut m = n;
    // let mut result = Scalar::ONE + x;
    let mut result = Fr::from_repr(*x).unwrap();
    result.add_assign(&Fr::one());
    // let mut factor = *x;
    let mut factor = Fr::from_repr(*x).unwrap();
    while m > 2 {
        // factor = factor * factor;
        let factor_tmp = factor;
        factor.mul_assign(&factor_tmp);
        // result = result + factor * result;
        let mut tmp = result;
        tmp.mul_assign(&factor);
        result.add_assign(&tmp);       

        m = m / 2;
    }
    result.into()
}

// takes the sum of all of the powers of x, up to n
// fn sum_of_powers_slow(x: &FrRepr, n: usize) -> FrRepr {
//     exp_iter(*x).take(n).sum()
// }

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}
