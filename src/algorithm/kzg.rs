use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use super::basic::*;

pub fn setup(n: &usize) -> KZGpp{

    let alpha = Fr::from_repr(hash_to_field_repr("KZG seed")).unwrap();

    let mut g2_vec = Vec::with_capacity(*n); 
    let mut alpha_power = Fr::one();
    for _ in 0..*n {
        alpha_power.mul_assign(&alpha); // compute beta^{2i}
        g2_vec.push(G2Affine::one().mul(alpha_power).into_affine());
    }

    let g1_alpha = G1Affine::one().mul(alpha).into_affine();
   KZGpp {g1_alpha, g2_vec}
}

pub fn commit(pp: &KZGpp, poly_values: &[FrRepr]) -> G2 {

    let scalars_u64: Vec<&[u64; 4]> = poly_values.iter().map(|s| &s.0).collect();
    let commitment = G2Affine::sum_of_products(&pp.g2_vec, &scalars_u64);
    
    commitment
}

pub fn open(pp: &KZGpp, poly: &[Fr], z: Fr) -> G2 {
    let y = evaluate(poly, z);

    let mut coeffs = poly.to_vec();
    // divide (x - z)
    let quotient = compute_quotient_coeffs(&coeffs, z, y);

    //generate proof
    let quo_fr: Vec<FrRepr> = quotient.iter().map(|x| (*x).into()).collect();
    let quo_scalars_u64: Vec<&[u64; 4]> = quo_fr.iter().map(|s| &s.0).collect();
    let pi = G2Affine::sum_of_products(&pp.g2_vec[0..quotient.len()], &quo_scalars_u64);

    pi
}


pub fn verify(
    pp: &KZGpp,
    point: Fr,
    value: Fr,
    commitment: G2Affine,
    pi: G2Affine
) -> bool {
    let mut lhsR = G2::from(commitment);
    let tmp1 = G2::from(G2Affine::one().mul(value));//.negate()
    lhsR.add_assign(&tmp1);
    let lhs = Bls12::pairing(G1Affine::one(), lhsR);//commitment - G2Affine::one().mul(value)

    let mut rhsL = G1::from(pp.g1_alpha);
    let tmp2 = G1::from(G1Affine::one().mul(point));//.negate()
    rhsL.add_assign(&tmp2);
    let rhs = Bls12::pairing(rhsL, pi);//pp.g2_vec[1] - G1Affine::one().mul(point)
    lhs == rhs
}


// evaluation of polynomial
fn evaluate(coefficients: &[Fr], point: Fr) -> Fr {
    let mut result = Fr::zero();
    let mut power = Fr::one();

    for coeff in coefficients {
        let mut term = coeff.clone();
        term.mul_assign(&power);
        result.add_assign(&term);
        power.mul_assign(&point);
    }

    result
}

// compute quotient
fn compute_quotient_coeffs(coeffs: &[Fr], z: Fr, y: Fr) -> Vec<Fr> {
    // f(x) - f(z)
    let mut a = coeffs.to_vec();
    a[0].sub_assign(&y);

    let degree = a.len() - 1;
    let mut q_coeffs = vec![Fr::zero(); degree]; //  degree - 1

    // divide of polynomial
    q_coeffs[degree - 1] = a[degree];
    for i in (1..degree).rev() {
        let mut tmpz = z.clone();
        tmpz.mul_assign(&q_coeffs[i]);
        q_coeffs[i - 1] = a[i];
        q_coeffs[i - 1].add_assign(&tmpz);
    }

    // check whether remainder is zero
    let mut tmpz = z.clone();
    tmpz.mul_assign(&q_coeffs[0]);
    let mut remainder = a[0];
    remainder.add_assign(&tmpz);
    assert_eq!(remainder, Fr::zero(), "Invalid quotient polynomial");

    q_coeffs
}

