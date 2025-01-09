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

pub fn open(pp: &KZGpp, poly: &[Fr], point: Fr) -> G2 {
    let value = evaluate(poly, point);
    
    let mut point_tmp = point.clone();
    point_tmp.negate();
    let a = Fr::from_repr(FrRepr::from(1)).unwrap();
    let denominator = [point_tmp, a];
  
    let mut value_neg = Fr::from_repr(FrRepr::from(value)).unwrap();
    value_neg.negate();
    let mut cons = Fr::from_repr(FrRepr::from(poly[0])).unwrap();
    cons.add_assign(&value_neg);
    let rest = &poly[1..];
    let temp: Vec<Fr> = std::iter::once(cons).chain(rest.iter().cloned()).collect();
    let numerator: &[Fr] = &temp;

    let quotient = div(numerator, &denominator);

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
    let lhs = Bls12::pairing(G1Affine::one(),  lhsR);//commitment - G2Affine::one().mul(value)

    let mut rhsL = G1::from(pp.g1_alpha);
    let tmp2 = G1::from(G1Affine::one().mul(point));//.negate()
    rhsL.add_assign(&tmp2);
    let rhs = Bls12::pairing(rhsL, pi);//pp.g2_vec[1] - G1Affine::one().mul(point)
    lhs == rhs
}


pub fn div<Fr: PrimeField>(p1: &[Fr], p2: &[Fr]) -> Vec<Fr> {
    let mut quotient = vec![Fr::zero(); p1.len() - p2.len() + 1];
    // let mut remainder: Vec<Fr> = p1.to_vec();

    // while remainder.len() >= p2.len() {
    //     let coeff = *remainder.last().unwrap() / *p2.last().unwrap();
    //     let pos = remainder.len() - p2.len();

    //     quotient[pos] = coeff;

    //     for (i, &factor) in p2.iter().enumerate() {
    //         remainder[pos + i] -= factor * coeff;
    //     }

    //     while let Some(true) = remainder.last().map(|x| *x == Fr::from(0)) {
    //         remainder.pop();
    //     }
    // }

    quotient
}

pub fn evaluate<Fr: Field>(poly: &[Fr], point: Fr) -> Fr {
    let mut value = Fr::zero();

    let mut x = Fr::one();
    value = poly[0];
    for i in 1..poly.len() {
        x.mul_assign(&point); // compute point^{i}

        let mut polyi = poly[i];
        polyi.mul_assign(&x);
        value.add_assign(&polyi);//value += poly[i] * x;
    }

    value
}