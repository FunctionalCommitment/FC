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
    // test_rp();
    // test_vc();
    group_scheme();
}

fn group_scheme(){
    /* setup algorithm */
    let n: usize = 2_usize.pow(12);
    let k:usize = 64;
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(k, 1); 
    let vc_gens = algorithm::vc::gen(&n);
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
    let pi = vc::open(vc_gens.clone(), &i, c_vec.clone());
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
    let result = vc::verify(&vc_gens, com_copy, &i, c_i, &pi);
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

fn test_vc(){
    let n: usize = 2_usize.pow(2);
    //generate public parameter
    let pp = algorithm::vc::gen(&n);
    println!("n = {:?}, parameters generated", n);

    //generate a random vector consisting of G1 elements
    let mut a_vec:Vec<G1Affine> = Vec::with_capacity(n);
    for i in 0..n {
        let mut randomStr = format!("this is message number {}", i);
        let mut randomNum:FrRepr = hash_to_field_repr(&randomStr);
        a_vec.push(G1Affine::one().mul(randomNum).into_affine()); 
    }
    println!("values generated");

    //generate the commitment of a_vec
    let start = time::now();//get the start time
    let mut com = vc::com(&pp, &a_vec.clone());
    let end = time::now();//get the end time
    println!("com generated:{:?}",end-start);
    
    // let size_of_gt = mem::size_of_val(&com);
    // println!("gt:{:?}",size_of_gt);

    //generate a proof
    let i: usize = 0;
    let start = time::now();//get the start time
    let pi = vc::open(pp.clone(), &i, a_vec.clone());
    let end = time::now();//get the end time
    println!("proof generated:{:?}",end-start);

    //verify
    let mut com_copy = com;
    let a_i = a_vec[i];
    let start = time::now();//get the start time
    let result = vc::verify(&pp, com_copy, &i, a_i, &pi);
    let end = time::now();//get the end time
    println!("the verification result is {:?}, the required time is {:?}", result, end-start);
}

// fn test_random(){
//     let mut rng = rand::thread_rng();
//     let mNum16: u16 = rng.gen();
//     println!("mNum16 = {:?}", mNum16);
//     let mNum32: u32= rng.gen();
//     println!("mNum32 = {:?}", mNum32);
//     let mNum64: u64= rng.gen();
//     println!("mNum64 = {:?}", mNum64);
// }



use polynomial::{Polynomial};
use rand::prelude::*;
use std::ops::Mul;
use std::ops::Add;
use rand::rngs::OsRng;
// use alloc::vec;

extern crate time;

extern crate polynomial;
extern crate rand;

fn generate_random_polynomial(degree: usize) -> Polynomial<u128> {
    // create a random number generator
    let mut rng = rand::thread_rng();

    // the coefficients of the polynomial are randomly generated
    let mut coefficients = Vec::new();
    for _ in 0..=degree {
        coefficients.push(rng.gen_range(0..100000));// assume coefficients range from 0 to 10
    }
    Polynomial::new(coefficients)
}

fn generate_random_poly_matrix(rows: usize, cols: usize, degree: usize) -> Vec<Vec<Polynomial<u128>>> {
    let mut matrix = Vec::new();
    for _ in 0..rows {
        let mut row = Vec::new();
        for _ in 0..cols {
            row.push(generate_random_polynomial(degree));
        }
        matrix.push(row);
    }
    matrix
}

fn generate_random_poly_vector(rows: usize, degree: usize) -> Vec<Polynomial<u128>> {
    let mut vector = Vec::with_capacity(rows);
    for _ in 0..rows {
        vector.push(generate_random_polynomial(degree));
    }
    vector
}

fn multiply_poly_matrix_vector(matrix: &[Vec<Polynomial<u128>>], vector: &[Polynomial<u128>]) -> Vec<Polynomial<u128>> {
    let mut result = Vec::new();
    for row in matrix.iter() {
        let mut sum = Polynomial::new(vec![0]);
        for (poly, scalar) in row.iter().zip(vector.iter()) {
            let mult_result = poly.clone().mul(scalar.clone());
            sum = sum.add(mult_result);
        }
        result.push(sum);
    }
    result
}

////////////////////////////////////////////////////////////////
fn generate_random_matrix(rows: usize, cols: usize) -> Vec<Vec<u128>> {
    let mut rng = rand::thread_rng();
    let mut matrix = Vec::new();
    for _ in 0..rows {
        let mut row = Vec::new();
        for _ in 0..cols {
            let random_value: u128 = rng.gen(); // generate a random number
            row.push(random_value);
        }
        matrix.push(row);
    }
    matrix
}
fn generate_random_vector(rows: usize) -> Vec<u128> {
    let mut rng = rand::thread_rng();
    let mut vector = Vec::with_capacity(rows);
    for _ in 0..rows {
        let random_value: u128 = rng.gen(); // generate a random number
        vector.push(random_value);
    }
    vector
}
fn multiply_matrix_vector(matrix: &[Vec<u128>], vector: &[u128]) -> Vec<u128> {
    let mut result = Vec::new();
    for row in matrix.iter() {
        let mut sum:u128 = 0;
        for (poly, scalar) in row.iter().zip(vector.iter()) {
            let tmp = poly.clone().wrapping_mul(scalar.clone());
            sum = sum.wrapping_add(tmp);
        }
        result.push(sum);
    }
    result
}

fn lattice_commit() {
    //Some parameter about committing
    let lambda = 128;
    let d = 32;
    let g_rows = lambda/d+1;
    let g_cols = g_rows+1;
   
    let vector_size = g_cols;

    let g_matrix = generate_random_poly_matrix(g_rows, g_cols, d);
    let r_vector = generate_random_poly_vector(vector_size, d);

    //Some parameters about hMT
    let m_rows = lambda;
    let m_cols = 2*lambda*lambda;
    let vector_size = m_cols/2;

    let m_matrix = generate_random_matrix(m_rows, m_cols);
    let mut x_vector = generate_random_vector(vector_size);
    let zero_vector: Vec<_> = vec![0; vector_size]; // create a zero vector
    x_vector.extend(zero_vector); // append the zero vector to the original vector

    let start = time::now();//get the start time
    //Commit to n values
    let n = 2u32.pow(10);
    for _i in 0..n{
        // multiply a matrix with a vector
        let _result = multiply_poly_matrix_vector(&g_matrix, &r_vector);
    }
    //Compute Homomorphic Merkle tree: n lattice-based hash function
    for _i in 0..n{
        let _result = multiply_matrix_vector(&m_matrix, &x_vector);
        let _result = multiply_matrix_vector(&m_matrix, &x_vector);
    }
    let end = time::now();//get the end time
    println!("Committing time:{:?}",end-start);
}

fn lattice_prove() {
    //Some parameter about committing
    let lambda = 128;
    let d = 32;
    let s = 8;
    let d_divide_s = d/s;
    let g_rows = lambda/d+1;
    let g_cols = g_rows+1;
   
    let vector_size = g_cols;

    let g_matrix = generate_random_poly_matrix(g_rows, g_cols, d);
    let r_vector = generate_random_poly_vector(vector_size, d);

     //Some parameter about k polynomial ring addition
     let k = 64;
     let x = generate_random_polynomial(d_divide_s);
     let a = generate_random_polynomial(d_divide_s);
     //let mut rng = rand::thread_rng();
     //let bool_vector: Vec<bool> = (0..k).map(|_| rng.gen()).collect();

    let start = time::now();//获取开始时间 
     //5 lattice-based commitment
    for _i in 0..5{
        // 矩阵与向量相乘
        let _result = multiply_poly_matrix_vector(&g_matrix, &r_vector);
    }
    //k polynomial ring addition
    // 检查向量的每个位置，并输出相应的结果
    for _i in 0..k {
        let _tmp = x.clone().add(a.clone());
    }
    let end = time::now();//获取结束时间
    println!("Proving time:{:?}",end-start);
}

fn lattice_verify() {
    //Some parameter about committing
    let lambda = 128;

    //Some parameters about hMT
    let m_rows = lambda;
    let m_cols = 2*lambda*lambda;
    let vector_size = m_cols/2;

    let m_matrix = generate_random_matrix(m_rows, m_cols);
    let mut x_vector = generate_random_vector(vector_size);
    let zero_vector: Vec<_> = vec![0; vector_size]; // 创建一个相同长度的零向量
    x_vector.extend(zero_vector); // 将零向量添加到原始向量的末尾

    let logn = 10;
    let start = time::now();//获取开始时间 
    //logn lattice-based hash function
    for _i in 0..logn{
        let _result = multiply_matrix_vector(&m_matrix, &x_vector);
        let _result = multiply_matrix_vector(&m_matrix, &x_vector);
    }
    let end = time::now();//获取结束时间
    println!("Verifying time:{:?}",end-start);
}

fn lattice_upd_com() {
    //Some parameter about committing
    let lambda = 128;

    //Some parameters about hMT
    let m_rows = lambda;
    let m_cols = 2*lambda*lambda;
    let vector_size = m_cols/2;

    let m_matrix = generate_random_matrix(m_rows, m_cols);
    let mut x_vector = generate_random_vector(vector_size);
    let zero_vector: Vec<_> = vec![0; vector_size]; // 创建一个相同长度的零向量
    x_vector.extend(zero_vector); // 将零向量添加到原始向量的末尾

    let logn = 10;
    let start = time::now();//获取开始时间 
    //logn lattice-based hash function
    for _i in 0..logn{
        let _result = multiply_matrix_vector(&m_matrix, &x_vector);
    }
    let end = time::now();//获取结束时间
    println!("Updating commitment time:{:?}",end-start);
}