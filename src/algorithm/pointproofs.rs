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

// Aggregate a 2-dim array of proofs, each row corresponding to a commit, into a single proof.
pub fn pointproofs_aggregate_proof(
    commits: &[G1],//C1[R(S)]
    proofs: &[Vec<G1>],//\pi_{ij}
    set: &[Vec<usize>],//S
    value_sub_vector: &[Vec<FrRepr>],//M[S]
    n: usize,
) -> Result<G1, String>{
    for e in set.iter() {
        for ee in e.iter() {
            if *ee >= n {
                return Err(String::from("Invalid Index"));
            }
        }
    }

    // check the length are correct
    if commits.len() != proofs.len()
        || commits.len() != set.len()
        || commits.len() != value_sub_vector.len()
        || commits.is_empty()
    {
        return Err(String::from("Mismatch Size"));
    };

    // start aggregation
    // generate the random Fr-s
    let ti = dim2_hash_fr(&commits, &set, &value_sub_vector, n)?;
    let mut ti_s: Vec<Vec<Fr>> = Vec::with_capacity(commits.len());
    for i in 0..commits.len() {
        ti_s.push(dim1_hash_fr(
            &commits[i],
            &set[i],
            &value_sub_vector[i],
            n,
        )?);
    }
    // form the final scalars by multiplying Fr-s
    // for i in 0..# com, for k in 0..#proof, ti[i] * ti_s[i,k]
    let mut scalars_repr: Vec<FrRepr> = vec![];
    for i in 0..ti.len() {
        for e in ti_s[i].iter() {
            let mut tmp = *e;
            tmp.mul_assign(&ti[i]);
            scalars_repr.push(tmp.into_repr());
        }
    }
    let scalars_u64: Vec<&[u64; 4]> = scalars_repr.iter().map(|s| &s.0).collect();

    // form the final basis
    let mut bases: Vec<G1> = proofs.concat().iter().map(|x| *x).collect();
    CurveProjective::batch_normalization(&mut bases);

    // the CurveProjective points are already normalized via batch nomarlization
    let bases_affine: Vec<G1Affine> =
        bases.iter().map(|s| s.into_affine()).collect();

    // inner_proof_content = \prod pi[j] ^ {ti[i] * ti_s[i,j]}
    let proof = G1Affine::sum_of_products(&bases_affine[..], &scalars_u64);

    Ok(proof)
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

pub fn pointproofs_batch_verify(
    verifier_params: &VerifierParams,
    com: &[G1],
    proof: &G1,
    set: &[Vec<usize>],
    value_sub_vector: &[Vec<FrRepr>],
) -> bool {
    // check length
    let num_commit = com.len();
    if num_commit != set.len() || num_commit != value_sub_vector.len() || num_commit == 0 {
        // length does not match
        return false;
    }
    for j in 0..num_commit {
        if set[j].len() != value_sub_vector[j].len()
            || set[j].is_empty()
            || set[j].len() > verifier_params.n
        {
            // length does not match
            return false;
        }
    }

    // generate all the t_i-s for j \in [num_commit] as in aggregating algorithm
    let mut ti_s: Vec<Vec<Fr>> = Vec::with_capacity(num_commit);
    for j in 0..num_commit {
        let ti_v = match dim1_hash_fr(&com[j], &set[j], &value_sub_vector[j], verifier_params.n)
        {
            Err(_e) => return false,
            Ok(p) => p,
        };
        ti_s.push(ti_v);
    }
    // generate tj
    let ti = match dim2_hash_fr(&com, &set, &value_sub_vector, verifier_params.n) {
        Err(_e) => return false,
        Ok(p) => p,
    };

    // we want to check
    //  \prod_{i=1}^num_commit e(com[i], g2^{\sum alpha^{n + 1 -j} * t_i,j} ) ^ t_i
    //      ?= e (proof, g2) * e (g1, g2)^{alpha^{n+1} * {\sum m_i,j * t_i,j * ti}}
    // step 1. compute tmp = \sum m_i,j * t_i,j * ti
    let mut tmp = Fr::zero();
    for j in 0..num_commit {
        let mut tmp2 = Fr::zero();

        // tmp2 = sum_i m_ij * t_ij
        for k in 0..ti_s[j].len() {
            let mut tmp3 = ti_s[j][k];
            let mij = Fr::from_repr(value_sub_vector[j][k]).unwrap();
            tmp3.mul_assign(&mij);
            tmp2.add_assign(&tmp3);
        }
        // tmp2 = tj * tmp2
        // safe to unwrap here
        // the output of hash should always be a field element
        let tmp3 = ti[j];
        tmp2.mul_assign(&tmp3);
        // tmp += tj * (sum_i m_ji * t_ij)
        tmp.add_assign(&tmp2);
    }

    let tmp_inverse = match tmp.inverse() {
        Some(p) => p,
        // tmp == 0 should never happen in practice
        None => panic!("some thing is wrong, check verification formula"),
    };

    // step 2. now the formula becomes
    // \prod e(com[i], g2^{\sum alpha^{n + 1 - j} * t_i,j * ti/tmp} )
    //  * e(proof^{-1/tmp}, g2)
    //  ?= e(g1, g2)^{alpha^{n+1}} == verifier_params.gt_elt

    // g1_vec stores the g1 components for the pairing product
    // for j \in [num_commit], store com[j]
    let mut g1_proj: Vec<G1> = com.to_vec();
    // the last element for g1_vec is proof^{-1/tmp}
    let mut tmp2 = *proof;
    tmp2.negate();
    tmp2.mul_assign(tmp_inverse);
    g1_proj.push(tmp2);

    // convert g1_proj into g1_affine
    G1::batch_normalization(&mut g1_proj);
    let g1_vec: Vec<G1Affine> = g1_proj.iter().map(|s| s.into_affine()).collect();

    // g2_vec stores the g2 components for the pairing product
    // for j \in [num_commit], g2^{\sum alpha^{n + 1 - j} * t_i,j} * ti/tmp )
    let mut g2_proj: Vec<G2> = Vec::with_capacity(num_commit + 1);
    for j in 0..num_commit {
        let num_proof = ti_s[j].len();
        let mut tmp3 = tmp_inverse;
        // safe to unwrap here
        // the output of hash should always be a field element
        let scalar = ti[j];
        tmp3.mul_assign(&scalar);

        // subset_sum = \sum alpha^{n + 1 - j} * t_i,j}
        let mut bases: Vec<G2Affine> = Vec::with_capacity(num_proof);
        let mut scalars_u64: Vec<[u64; 4]> = Vec::with_capacity(num_proof);
        for k in 0..num_proof {
            bases.push(verifier_params.generators_alpha[verifier_params.n - set[j][k] - 1]);
            let mut t = ti_s[j][k];
            t.mul_assign(&tmp3);
            scalars_u64.push(t.into_repr().0);
        }
        let scalars_u64_ref: Vec<&[u64; 4]> = scalars_u64.iter().collect();

        let param_subset_sum = {
            G2Affine::sum_of_products(&bases, &scalars_u64_ref)
        };
        g2_proj.push(param_subset_sum);
    }
    // the last element for g1_vec is g2
    g2_proj.push(G2::one());
    // convert g2_proj into g2_affine
    G2::batch_normalization(&mut g2_proj);
    let g2_vec: Vec<G2Affine> = g2_proj.iter().map(|s| s.into_affine()).collect();
    
    // println!("batch_verify_inner_proof");
    // println!("lhs={}", Bls12::pairing_multi_product(&g1_vec[..], &g2_vec[..]));
    // println!("rhs={}", verifier_params.gt_elt);
    // now check the pairing product ?= verifier_params.gt_elt
    Bls12::pairing_multi_product(&g1_vec[..], &g2_vec[..]) == verifier_params.gt_elt
}