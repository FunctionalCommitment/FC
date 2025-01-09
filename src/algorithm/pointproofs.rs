use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use super::basic::*;



pub fn pointproof_setup(
    n: usize,
) -> (ProverParams, VerifierParams) {
    let alpha = Fr::from_repr(hash_to_field_repr("pointproofs seed")).unwrap();
    let mut g1_vec = Vec::with_capacity(2 * n);
    // prover vector at index i-1 contains g1^{alpha^i} for i ranging from 1 to 2n
    // except that at index i, prover vector contains nothing useful
    // (we'll use G1::one as a placeholder in order to maintain the indexing)
    let mut g2_vec = Vec::with_capacity(n);
    // verifier vector at index i-1 contains g2^{alpha^i} for i ranging from 1 to n
    let mut alpha_power = Fr::one();
    for _ in 0..n {
        alpha_power.mul_assign(&alpha); // compute alpha^i
        g1_vec.push(G1Affine::one().mul(alpha_power).into_affine());
        g2_vec.push(G2Affine::one().mul(alpha_power).into_affine());
    }

    // skip g1^{alpha^{n+1}}
    alpha_power.mul_assign(&alpha);
    g1_vec.push(G1::zero().into_affine()); // this 0 is important -- without it, prove will not work correctly

    // Now do the rest of the prover
    for _ in n..2 * n - 1 {
        alpha_power.mul_assign(&alpha); // compute alpha^i
        g1_vec.push(G1Affine::one().mul(alpha_power).into_affine());
    }

    // verifier also gets gt^{alpha^{n+1}} in the target group
    let gt = Bls12::pairing(g1_vec[0], g2_vec[n - 1]);

    (
        ProverParams {
            n,
            generators_alpha: g1_vec,
        },
        VerifierParams {
            n,
            generators_alpha: g2_vec,
            gt_elt: gt,
        },
    )
}

pub fn pointproof_commit(
    prover_params: &ProverParams,
    values: &[FrRepr],
) -> G1 {
    let scalars_u64: Vec<&[u64; 4]> = values.iter().map(|s| &s.0).collect();

    //C1=(c_1, ..., c_n)
    let mut commitment = G1Affine::sum_of_products(
        &prover_params.generators_alpha[0..prover_params.n], &scalars_u64);

    commitment
}

pub fn pointproofs_prove(
    prover_params: &ProverParams,
    values: &[FrRepr],//M_i
    index: usize,//j \in [N-1]
) -> G1 {
    // check index is valid
    if index >= prover_params.n{
        println!("Invalid Index");
    };
    // check param
    if values.len() != prover_params.n {
        println!("Invalid Size");
    }

    let scalars_u64: Vec<&[u64; 4]> = values.iter().map(|s| &s.0).collect();

    // proof = \sum_{i=prover_params.n - index}^{2 * prover_params.n - index}
    //          param.generator[i]^scarlar_u64[i]
    let proof = G1Affine::sum_of_products(&prover_params.generators_alpha[prover_params.n-index..2*prover_params.n-index], &scalars_u64);
    
    proof
}

pub fn pointproofs_verify(
    verifier_params: &VerifierParams,
    com: &G1,
    proof: &G1,
    value: FrRepr,
    index: usize,
) -> bool {
    if index >= verifier_params.n{
        return false;
    }

    // step 1. compute hash_inverse
    let hash = Fr::from_repr(value).unwrap();
    // we can safely assume that hash is invertible
    // see `hash_to_field` function
    let hash_inverse = hash.inverse().unwrap();

    // step 2, compute com^hash_inverse and proof^{-hash_inverse}
    let mut com_mut = com.clone();
    let mut proof_mut = proof.clone();
    proof_mut.negate();
    com_mut.mul_assign(hash_inverse);
    proof_mut.mul_assign(hash_inverse);

    // step 3. check pairing product
    Bls12::pairing_product(
        com_mut.into_affine(),
        verifier_params.generators_alpha[verifier_params.n - index - 1],
        proof_mut.into_affine(),
        G2Affine::one(),
    ) == verifier_params.gt_elt
}