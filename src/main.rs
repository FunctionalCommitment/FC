mod algorithm;

use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use algorithm::basic::*;
use crate::algorithm::*;
use vector_element_range_proof::PedersenGens;
use vector_element_range_proof::BulletproofGens;
use rand::thread_rng;
use merlin::Transcript;
use vector_element_range_proof::RangeProof;
use rand::Rng;
// use std::mem;

fn main() {
    
    for exp  in [15, 17]{
        test_fc(exp);
    }

    // for exp in [16, 18, 20, 22]{
    //     println!("==============================pointproofs================================");
    //     test_pointproofs(exp);
    //     println!("=============================mc=============================");
    //     test_mc(exp);
    // }
    
    // test_rp();
    // verp();
}


fn test_fc(exp: u32){
    let n: usize = 2_usize.pow(exp);
    //generate public parameter
    let pp = algorithm::fc::gen(&n);
    let kzp_size = 2*n+1;
    let kzg_pp = algorithm::kzg::setup(&kzp_size);
    println!("n = {:?}, parameters generated", n);

    //generate a random vector consisting of G1 elements
    let mut a_vec:Vec<G1Affine> = Vec::with_capacity(n);
    let mut b_vec:Vec<FrRepr> = Vec::with_capacity(n);
    for i in 0..n {
        let mut randomStr = format!("this is message number {}", i);
        let mut randomNum:FrRepr = hash_to_field_repr(&randomStr);
        a_vec.push(G1Affine::one().mul(randomNum).into_affine()); 
        let mut rand = format!("this is message {}", i);
        let mut randNum:FrRepr = hash_to_field_repr(&rand);
        b_vec.push(randNum);
    }
    println!("values generated");

    //generate the commitment of a_vec
    let start = time::now();//get the start time
    let mut com = fc::com(&pp, &a_vec.clone());
    let end = time::now();//get the end time
    println!("com generated:{:?}",end-start);
    
    // let size_of_gt = mem::size_of_val(&com);
    // println!("gt:{:?}",size_of_gt);

    //generate a proof
    let start = time::now();//get the start time
    let pi = fc::open(pp.clone(), &kzg_pp, b_vec.clone(), a_vec.clone());
    let end = time::now();//get the end time
    println!("proof generated:{:?}",end-start);

    //verify
    let mut com_copy = com;

    let start = time::now();//get the start time
    let b_vec_u64: Vec<&[u64; 4]> = b_vec.iter().map(|s| &s.0).collect();
    let y = G1Affine::sum_of_products(&a_vec, &b_vec_u64);
    let end = time::now();//get the end time
    println!("the time cost by direct computation is {:?}",  end-start);

    let start = time::now();//get the start time
    let result = fc::verify(&pp, &kzg_pp, com_copy, b_vec, y.into_affine(), &pi);
    let end = time::now();//get the end time
    println!("the verification result is {:?}, the required time is {:?}", result, end-start);
}

fn test_pointproofs(exp: u32){
    let n: usize = 2_usize.pow(exp);
    //generate public parameter
    let start = time::now();//get the start time
    let (prover_params, verifier_params) = algorithm::pointproofs::pointproof_setup(n);
    let end = time::now();//get the end time
    println!("n = {:?}, pointproofs parameters generated in {:?}", n, end-start);

    //generate a random vector consisting of G1 elements
    let mut m_vec:Vec<FrRepr> = Vec::with_capacity(n);
    for i in 0..n {
        let mut randomStr = format!("this is message number {}", i);
        let mut randomNum:FrRepr = hash_to_field_repr(&randomStr);
        m_vec.push(randomNum); 
    }
    println!("pointproofs values generated");

    //generate the commitment of a_vec
    let start = time::now();//get the start time
    let mut com = pointproofs::pointproof_commit(&prover_params, &m_vec);
    let end = time::now();//get the end time
    println!("pointproofs com generated:{:?}",end-start);

    //generate a proof
    let i: usize = 0;
    let start = time::now();//get the start time
    let pi = pointproofs::pointproofs_prove(&prover_params, &m_vec, i);
    let end = time::now();//get the end time
    println!("proof generated:{:?}",end-start);

    //verify
    let mut com_copy = com;
    let m_i = m_vec[i];
    let start = time::now();//get the start time
    let result = pointproofs::pointproofs_verify(&verifier_params, &com_copy, &pi, m_i, i);
    let end = time::now();//get the end time
    println!("the verification result is {:?}, the required time is {:?}", result, end-start);
}

fn test_mc(exp: u32){
    let N: usize = 2_usize.pow(exp);
    let n: usize = 2_usize.pow(exp>>1);
    //generate public parameter
    let start = time::now();//get the start time
    let (prover_params, verifier_params) = algorithm::pointproofs::pointproof_setup(n);
    let pp = algorithm::vc::gen(&n);
    let kzp_size = 2*n+1;
    let kzg_pp = algorithm::kzg::setup(&kzp_size);
    let end = time::now();//get the end time
    println!("N = {:?}, n = {:?}, parameters generated in {:?}", N, n, end-start);

    //generate a random vector consisting of G1 elements
    let mut m_vec:Vec<FrRepr> = Vec::with_capacity(N);
    for i in 0..N {
        let mut randomStr = format!("this is message number {}", i);
        let mut randomNum:FrRepr = hash_to_field_repr(&randomStr);
        m_vec.push(randomNum); 
    }
    println!("values generated");

    //generate the commitment of a_vec
    let start = time::now();//get the start time
    let mut c_vec:Vec<G1Affine> = Vec::with_capacity(n);
    //generate (c_1, c_2, ..., c_n)
    for i in 0..n {
        c_vec.push(pointproofs::pointproof_commit(&prover_params, &m_vec[i*n..(i+1)*n]).into_affine());
    }
    let mut commitment = vc::com(&pp, &c_vec.clone());
    let end = time::now();//get the end time
    println!("com generated:{:?}",end-start);

    //generate a proof
    let i: usize = 0;
    let j: usize = 0;
    let start = time::now();//get the start time
    let pi_i = vc::open(pp.clone(), &kzg_pp, &i, c_vec.clone());
    let pi_ij = pointproofs::pointproofs_prove(&prover_params, &m_vec[i*n..(i+1)*n], j);
    let end = time::now();//get the end time
    println!("proof generated:{:?}",end-start);

    //verify
    let mut com_copy = commitment;
    let mut c_i = c_vec[i];
    let m_ij = m_vec[i*n+j];
    let start = time::now();//get the start time
    let resulti = vc::verify(&pp, &kzg_pp, com_copy, &i, c_i, &pi_i);
    let c_i_G1 = G1::from(c_i);
    let resultj = pointproofs::pointproofs_verify(&verifier_params, &c_i_G1, &pi_ij, m_ij, j);
    let end = time::now();//get the end time
    println!("the verification result is {:?}, the required time is {:?}", resulti & resultj, end-start);
}


fn test_rp(){
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, 1);
    
    // A secret value we want to prove lies in the range [0, 2^64)
    let secret_value = 1037578891u64;
    //let secret_value = 10375u64;
    
    // The API takes a blinding factor for the commitment.
    let blinding = Fr::from_repr(hash_to_field_repr("RP seed")).unwrap().into();
 
    // The proof can be chained to an existing transcript.
    // Here we create a transcript with a doctest domain separator.
    let mut prover_transcript = Transcript::new(b"doctest example");
    
    // Create a 64-bit rangeproof.
    let start = time::now();//获取开始时间
    let proof = RangeProof::prove_single(//, committed_value
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
        secret_value,
        &blinding,
        64,
    ).expect("A real program could handle errors");
    let end = time::now();//获取结束时间
    println!("Proving time:{:?}",end-start);
    
    let committed_value = G1Affine::one();
    // Verification requires a transcript with identical initial state:
    let start = time::now();//获取开始时间
    let mut verifier_transcript = Transcript::new(b"doctest example");
    assert!(
        proof
            .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 64)
            .is_ok()
    );
    let end = time::now();//获取结束时间
    println!("Verify time:{:?}",end-start);
 }
  
fn verp(){
    /* setup algorithm */
    let n: usize = 2_usize.pow(12);
    let k:usize = 64;
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(k, 1); 
    let vc_gens = algorithm::vc::gen(&n);
    let kzp_size = 2*n+1;
    let kzg_pp = algorithm::kzg::setup(&kzp_size);
    println!("n = {:?}, k = {:?}, parameters generated", n, k);

    //generate a random vector consisting of Z_p elements
    let mut rng = rand::thread_rng();
    let mut m_vec_u:Vec<u64> = Vec::with_capacity(n);
    let mut m_vec:Vec<FrRepr> = Vec::with_capacity(n);
    let mut r_vec:Vec<FrRepr> = Vec::with_capacity(n);
    for i in 0..n {
        // [0, 2^32-1]
        // let random_number: u32 = rng.gen();
        // [0, 2^64-1]
        // let random_number: u64 = rng.gen();
        // let mut mStr = format!("this is message number {}", i);
        // let mut mNum:FrRepr = hash_to_field_repr(&mStr);
        let mNum: u64 = rng.gen();
        m_vec_u.push(mNum.into()); 
        m_vec.push(FrRepr::from(100)); 
        let rStr = format!("this is random number {}", i);
        let rNum:FrRepr = hash_to_field_repr(&rStr);
        r_vec.push(rNum); 
    }
    println!("vectors are generated");

    /* commit algorithm */ 
    let mut c_vec:Vec<G1Affine> = Vec::with_capacity(n);
    
    let start = time::now();//get the start time
     //firstly, commit to every vector element
    for i in 0..n {
        let c_i = pc_gens.commit(m_vec[i], r_vec[i]);
        c_vec.push(c_i);
    }
    //secondly, commit to the vector consisting of G1 elements
    let com = vc::com(&vc_gens, &c_vec.clone());
    let end = time::now();//get the end time
    println!("com generated:{:?}",end-start);

    /* prove algorithm */
    let i: usize = 0;
    let a = m_vec_u[i] / 2;
    let mut prover_transcript = Transcript::new(b"doctest example");
    
    let start = time::now();//get the start time
    let pi = vc::open(vc_gens.clone(), &kzg_pp, &i, c_vec.clone());
    let proof = RangeProof::prove_single(//, committed_value
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
        m_vec_u[i]-a,
        &r_vec[i],
        k,
    ).expect("A real program could handle errors");
    let end = time::now();//get the end time
    println!("proof generated:{:?}",end-start);

    /* verify algorithm */
    let com_copy = com.clone();
    let c_i = c_vec[i];
    let mut verifier_transcript = Transcript::new(b"doctest example");
    
    let start = time::now();//get the start time
    let result = vc::verify(&vc_gens, &kzg_pp, com_copy, &i, c_i, &pi);
    let a_repr = Fr::from_repr(FrRepr::from(a)).unwrap();
    let mut a_repr_neg = a_repr;
    a_repr_neg.negate();
    let a_com = pc_gens.commit(a_repr_neg.into(), FrRepr([0, 0, 0, 0]));
    let mut c_i_sub_a = G1::from(c_i);
    c_i_sub_a.add_assign(&G1::from(a_com));
    assert!(
        proof
            .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &c_i_sub_a.into(), k)
            .is_ok()
    );    
    let end = time::now();//get the end time
    println!("the verification result is {:?}, the required time {:?}", result, end-start);
    
    /* updcom algorithm */  
    let delta = FrRepr([1, 0, 0, 0]);

    let start = time::now();//get the start time
    let delta_com = pc_gens.commit(delta, FrRepr([0, 0, 0, 0]));
    let delta_pairing = Bls12::pairing(delta_com, vc_gens.v_vec[i]);
    let mut new_com = com;
    new_com.add_assign(&delta_pairing);
    let end = time::now();//get the end time
    println!("update commitment: {:?}", end-start);
}