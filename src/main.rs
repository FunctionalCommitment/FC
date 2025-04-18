mod algorithm;

use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use algorithm::basic::*;
use crate::algorithm::*;
use rand::thread_rng;
use merlin::Transcript;
use rand::Rng;
// use std::mem;

fn main() {
    // for exp in [12, 14, 16, 18]{
    //     for batchsize in [16, 256] {
    //         test_fc(exp, batchsize);
    //     } 
    // }

    for exp in [12, 14, 16, 18]{
        println!("=============================mc=============================");
        test_mc(exp);
    }
    
}

fn test_fc(exp: u32, batchsize: usize){
    let n: usize = 2_usize.pow(exp);
    let s: usize = batchsize;//batch size>1

    //generate public parameter
    let pp = algorithm::fc::gen(&n);
    let kzp_size = 2*n+1;
    let kzg_pp = algorithm::kzg::setup(&kzp_size);
    println!("n = {:?}, s = {:?}, parameters generated", n, s);

    //generate a random vector consisting of G1 elements
    let mut a_vec:Vec<G1Affine> = Vec::with_capacity(n);
    for i in 0..n {
        let mut randomStr = format!("this is message number {}", i);
        let mut randomNum:FrRepr = hash_to_field_repr(&randomStr);
        a_vec.push(G1Affine::one().mul(randomNum).into_affine()); 
    }
    let mut b_matrix:Vec<Vec<FrRepr>> = (0..s)
        .map(|i| (0..n).map(|j| hash_to_field_repr(&format!("this is message {}{}", i, j))).collect())
        .collect();
    println!("values generated");

    //generate the commitment of a_vec
    let start = time::now();//get the start time
    let mut com = fc::com(&pp, &a_vec.clone());
    let end = time::now();//get the end time
    println!("com generated:{:?}",end-start);
    
    // let size_of_gt = mem::size_of_val(&com);
    // println!("gt:{:?}",size_of_gt);

    //direct computation
    let mut y_vec:Vec<G1Affine> = Vec::with_capacity(s);
    let start = time::now();//get the start time
    for i in 0..s {
        let b_vec_u64: Vec<&[u64; 4]> = b_matrix[i].iter().map(|s| &s.0).collect();
        let y = G1Affine::sum_of_products(&a_vec, &b_vec_u64);
        y_vec.push(y.into());
    }
    let end = time::now();//get the end time
    println!("the time cost by {} direct computation is {:?}", s, end-start);

    //generate a proof
    let start = time::now();//get the start time
    let pi = fc::open(&pp, &kzg_pp, &b_matrix[0], &a_vec);
    let end = time::now();//get the end time
    println!("proof generated:{:?}",end-start);

    //verify
    let start = time::now();//get the start time
    let result = fc::verify(&pp, &kzg_pp, &com, &b_matrix[0], &y_vec[0], &pi);
    let end = time::now();//get the end time
    println!("the verification result is {:?}, the required time is {:?}", result, end-start);
    

    /******************************batch opening and verification****************************/
    //batch opening
    let start = time::now();//get the start time
    let batch_pi = fc::batchOpen(&pp, &kzg_pp, &com, &a_vec, &b_matrix, &y_vec);
    let end = time::now();//get the end time
    println!("batch proof generated:{:?}",end-start);

    // //batch verification
    let mut com_copy = com;
    let start = time::now();//get the start time
    let result = fc::batchVerify(&pp, &kzg_pp, &com, &b_matrix, &y_vec, &batch_pi);
    let end = time::now();//get the end time
    println!("the batch verification result is {:?}, the required time is {:?}", result, end-start);    
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
    let mut com = vc::com(&pp, &c_vec);
    let end = time::now();//get the end time
    println!("com generated:{:?}",end-start);

    //generate a proof
    let i: usize = 0;
    let j: usize = 0;
    let mut b_vec:Vec<FrRepr> = vec![FrRepr([0, 0, 0, 0]); n];
    b_vec[i] = FrRepr([1, 0, 0, 0]);
    let start = time::now();//get the start time
    let pi_i = fc::open(&pp, &kzg_pp, &b_vec, &c_vec);
    let pi_ij = pointproofs::pointproofs_prove(&prover_params, &m_vec[i*n..(i+1)*n], j);
    let end = time::now();//get the end time
    println!("a proof generated:{:?}",end-start);

    //verify a proof
    let mut c_i = c_vec[i];
    let m_ij = m_vec[i*n+j];
    let start = time::now();//get the start time
    let resulti = vc::verify(&pp, &kzg_pp, &com, &i, c_i, &pi_i);
    let c_i_G1 = G1::from(c_i);
    let resultj = pointproofs::pointproofs_verify(&verifier_params, &c_i_G1, &pi_ij, m_ij, j);
    let end = time::now();//get the end time
    println!("the verification result of a proof is {:?}, the required time is {:?}", resulti & resultj, end-start);

    /*generate a batch proof*/
    let start = time::now();//get the start time
    //1. prepare the aggregated proofs
    let outer_size = 1;
    let inner_size = 2_usize.pow(6);
    let mut in_set: Vec<Vec<usize>> = vec![];//S
    let mut in_sub_value: Vec<Vec<FrRepr>> = vec![];//M[S]
    let mut in_sub_proof: Vec<Vec<G1>> = vec![];//{\pi_ij}(i, j)\in S
    let mut b_matrix:Vec<Vec<FrRepr>> = vec![];
    let mut vecI:Vec<usize> = vec![];
    let mut out_sub_value: Vec<G1> =vec![];
    let mut out_sub_value_affine: Vec<G1Affine> =vec![];
    for i in 0..outer_size {
        let mut line_in_set: Vec<usize> = vec![];
        let mut line_in_sub_value: Vec<FrRepr> = vec![];
        let mut line_in_sub_proof: Vec<G1> = vec![];
        for j in 0..inner_size {
            line_in_set.push(j);
            line_in_sub_value.push(m_vec[i*n+j].clone());
            line_in_sub_proof.push(pointproofs::pointproofs_prove(&prover_params, &m_vec[i*n..(i+1)*n], j));
        }
        in_set.push(line_in_set);
        in_sub_value.push(line_in_sub_value);
        in_sub_proof.push(line_in_sub_proof);

        let mut b_vec:Vec<FrRepr> = vec![FrRepr([0, 0, 0, 0]); n];
        b_vec[i] = FrRepr([1, 0, 0, 0]);
        b_matrix.push(b_vec);
        vecI.push(i);

        out_sub_value.push(c_vec[i].clone().into());
        out_sub_value_affine.push(c_vec[i].clone());
    }
    
    //2. aggregate proofs
    let agg_pf=pointproofs::pointproofs_aggregate_proof(&out_sub_value, &in_sub_proof, &in_set, &in_sub_value, n).unwrap();
    let batch_pi = fc::batchOpen(&pp, &kzg_pp, &com, &c_vec, &b_matrix, &out_sub_value_affine);
    let end = time::now();//get the end time
    println!("Open subvector of size {}x{} in {:?}",outer_size, inner_size, end-start);

    /*verify a batch proof*/
    let start = time::now();//get the start time 
    let res1 = pointproofs::pointproofs_batch_verify(&verifier_params, &out_sub_value, &agg_pf, &in_set, &in_sub_value);
    let res2 = vc::batch_verify(&pp, &kzg_pp, &com, &vecI, &out_sub_value_affine, &batch_pi);
    // let res3 = fc::batchVerify(&pp, &kzg_pp, &com, &b_matrix, &out_sub_value_affine, &batch_pi);
    let end = time::now();//get the end time
    println!("Batch verify result is {}, the required time is {:?}", res1&res2, end-start);
}