use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use super::basic::*;

pub fn setup() -> Cpp {
     let scalar = Fr::from_repr(hash_to_field_repr("commitment seed")).unwrap();
 
     // generate two G1Affine elements
     let g = G1Affine::one();
     let h = G1Affine::one().mul(scalar).into_affine();

    Cpp{g, h}
}
pub fn com(pp:Cpp, m:&FrRepr, r:&FrRepr)-> G1Affine {
    let base = vec![pp.g, pp.h];
    let exp = vec![m, r];
    let exp_u64: Vec<&[u64; 4]> = exp.iter().map(|s| &s.0).collect();
    let c = G1Affine::sum_of_products(&base, &exp_u64).into_affine();

    c
}
