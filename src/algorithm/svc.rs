use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use super::basic::*;
use crate::algorithm::kzg;
use crate::algorithm::fc;

pub fn gen(n: &usize) -> FCpp {
    let beta = Fr::from_repr(hash_to_field_repr("VC seed")).unwrap();

    let mut v_vec = Vec::with_capacity(*n); 
    let mut beta_square = beta;
    beta_square.mul_assign(&beta);
    let mut beta_power = Fr::one();
    for _ in 0..*n {
        beta_power.mul_assign(&beta_square); // compute beta^{2i}
        v_vec.push(G2Affine::one().mul(beta_power).into_affine());
    }

   FCpp {v_vec}
}
pub fn com(pp:&FCpp, a_vec:&Vec<G1Affine>)-> Fq12 {
   let com = Bls12::pairing_multi_product(&a_vec, &pp.v_vec);
   
   com
}

pub fn open(pp:&FCpp, kzgpp: &KZGpp, i: &usize, a_vec:&[G1Affine])-> PI {
    let n = pp.v_vec.len();
    let l:usize = (n as f64).log2() as usize;
    if *i >= n {
        panic!("Index out of bounds");
    }
    let i_binary_vec = to_fixed_length_binary_vec(i, &l);
    let mut b_loop:Vec<FrRepr> = vec![FrRepr([0, 0, 0, 0]); n];
    b_loop[*i] = FrRepr([1, 0, 0, 0]);

    let mut x_inverse_vec = Vec::with_capacity(l); 
    let mut l_vec = Vec::with_capacity(l); 
    let mut r_vec = Vec::with_capacity(l); 
    let mut a_loop = Vec::with_capacity(n); 
    let mut v_loop = Vec::with_capacity(n); 
    for i in 0..n{
        a_loop.push(a_vec[i]);
        v_loop.push(pp.v_vec[i]);
    }
   
    let mut x_loop = FrRepr([0, 0, 0, 0]);
    let mut final_b_acc:Fr = Fr::one();
    let mut mid = n >> 1;
    for j in 1..l+1 {
        let a_left = a_loop[..mid].to_vec();
        let a_right = a_loop[mid..].to_vec();
        let v_left = v_loop[..mid].to_vec();
        let v_right = v_loop[mid..].to_vec();
        let b_left = b_loop[..mid].to_vec();
        let b_right = b_loop[mid..].to_vec();
        let b_left_u64: Vec<&[u64; 4]> = b_left.iter().map(|s| &s.0).collect();
        let b_right_u64: Vec<&[u64; 4]> = b_right.iter().map(|s| &s.0).collect();

        let left1 = Bls12::pairing_multi_product(&a_right, &v_left);
        let left2 = G1Affine::sum_of_products(&a_right, &b_left_u64).into_affine();    
        l_vec.push((left1, left2));      
        let right1 = Bls12::pairing_multi_product(&a_left, &v_right);
        let right2 = G1Affine::sum_of_products(&a_left, &b_right_u64).into_affine();
        r_vec.push((right1, right2));

        // hash the values into scalars
        x_loop = hash_to_x(&x_loop, &left1, &left2, &right1, &right2);
        // println!("x_loop in proof: {:?}", x_loop);
        let x_loop_inverse = Fr::from_repr(x_loop).unwrap().inverse().unwrap();
        x_inverse_vec.push(x_loop_inverse);
        
        let mut a_right_exp: Vec<G1Affine> = vec![G1Affine::one(); mid];
        a_loop.clear();
        a_loop.extend(a_left.to_vec().clone());
        let mut v_right_exp: Vec<G2Affine> = vec![G2Affine::one(); mid];
        v_loop.clear();
        v_loop.extend(v_left.to_vec().clone());
        b_loop.clear();
        b_loop.extend(vec![FrRepr([0, 0, 0, 0]); mid]);
        for k in 0..mid{
            a_right_exp[k] = a_right[k].mul(x_loop).into();
            let mut tmp1 = G1::from(a_left[k]);
            tmp1.add_assign(&G1::from(a_right_exp[k]));
            a_loop[k] = tmp1.into();  

            v_right_exp[k] = v_right[k].mul(x_loop_inverse).into();
            let mut tmp2 = G2::from(v_left[k]);
            tmp2.add_assign(&G2::from(v_right_exp[k]));
            v_loop[k] = tmp2.into(); 
        } 
        if i_binary_vec[j-1] == 1{
            final_b_acc.mul_assign(&x_loop_inverse);
        }
        let index = binary_vec_to_decimal(&i_binary_vec[j..]);
        b_loop[index]=final_b_acc.into();

        mid = mid >> 1;   
    }
    
    let finalA = a_loop[0];
    let finalv = v_loop[0];

    //prepare the polynomial for kzg 
    x_inverse_vec.reverse();
    let root = find_root_of_unity(l-1);
    let coeffs = expand_fx_fft(l-1, &x_inverse_vec, root, l);
    let point = Fr::from_repr(hash_to_field_repr("KZG point")).unwrap();
    let finalv_proof = kzg::open(kzgpp, &coeffs, point).into_affine();

    PI {
        l_vec,
        r_vec,
        finalA, 
        finalv,
        finalv_proof,
    }
}

pub fn batch_open(pp:&FCpp, kzgpp: &KZGpp, com:&Fq12, a_vec:&[G1Affine], I: &[usize], y_vec:&[G1Affine])-> PI {
    let n = pp.v_vec.len();
    let r_vec = hash_to_r_svc(com, I, y_vec);

    let l:usize = (n as f64).log2() as usize;
    let I_size = I.len();
    let mut I_binary_vec: Vec<Vec<u8>> = Vec::with_capacity(I_size);
    let mut final_ur_i: Vec<Fr> = vec![Fr::one(); I_size];
    let mut b_loop:Vec<FrRepr> = vec![FrRepr([0, 0, 0, 0]); n];        
    for index in 0..I_size{
        I_binary_vec.push(to_fixed_length_binary_vec(&I[index], &l));
        final_ur_i[index] = Fr::from_repr(r_vec[I[index]]).unwrap();
        b_loop[I[index]] = r_vec[I[index]];
    }

    let mut x_inverse_vec = Vec::with_capacity(l); 
    let mut l_vec = Vec::with_capacity(l); 
    let mut r_vec = Vec::with_capacity(l); 
    let mut a_loop = Vec::with_capacity(n); 
    let mut v_loop = Vec::with_capacity(n); 
    for i in 0..n{
        a_loop.push(a_vec[i]);
        v_loop.push(pp.v_vec[i]);
    }
   
    let mut x_loop = FrRepr([0, 0, 0, 0]);
    let mut final_b_acc:Fr = Fr::one();
    let mut mid = n >> 1;
    for j in 1..l+1 {
        let a_left = a_loop[..mid].to_vec();
        let a_right = a_loop[mid..].to_vec();
        let v_left = v_loop[..mid].to_vec();
        let v_right = v_loop[mid..].to_vec();
        let b_left = b_loop[..mid].to_vec();
        let b_right = b_loop[mid..].to_vec();
        let b_left_u64: Vec<&[u64; 4]> = b_left.iter().map(|s| &s.0).collect();
        let b_right_u64: Vec<&[u64; 4]> = b_right.iter().map(|s| &s.0).collect();

        let left1 = Bls12::pairing_multi_product(&a_right, &v_left);
        let left2 = G1Affine::sum_of_products(&a_right, &b_left_u64).into_affine();    
        l_vec.push((left1, left2));      
        let right1 = Bls12::pairing_multi_product(&a_left, &v_right);
        let right2 = G1Affine::sum_of_products(&a_left, &b_right_u64).into_affine();
        r_vec.push((right1, right2));

        // hash the values into scalars
        x_loop = hash_to_x(&x_loop, &left1, &left2, &right1, &right2);
        // println!("x_loop in proof: {:?}", x_loop);
        let x_loop_inverse = Fr::from_repr(x_loop).unwrap().inverse().unwrap();
        x_inverse_vec.push(x_loop_inverse);
        
        let mut a_right_exp: Vec<G1Affine> = vec![G1Affine::one(); mid];
        a_loop.clear();
        a_loop.extend(a_left.to_vec().clone());
        let mut v_right_exp: Vec<G2Affine> = vec![G2Affine::one(); mid];
        v_loop.clear();
        v_loop.extend(v_left.to_vec().clone());
        b_loop.clear();
        b_loop.extend(vec![FrRepr([0, 0, 0, 0]); mid]);
        for k in 0..mid{
            a_right_exp[k] = a_right[k].mul(x_loop).into();
            let mut tmp1 = G1::from(a_left[k]);
            tmp1.add_assign(&G1::from(a_right_exp[k]));
            a_loop[k] = tmp1.into();  

            v_right_exp[k] = v_right[k].mul(x_loop_inverse).into();
            let mut tmp2 = G2::from(v_left[k]);
            tmp2.add_assign(&G2::from(v_right_exp[k]));
            v_loop[k] = tmp2.into(); 
        } 
        for index in 0..I_size{
            if I_binary_vec[index][j-1] == 1{
                final_ur_i[index].mul_assign(&x_loop_inverse);
            }
            let tenForm = &I_binary_vec[index][j..];
            let mut tmp_fr = Fr::from_repr(b_loop[binary_vec_to_decimal(tenForm)]).unwrap();
            tmp_fr.add_assign(&final_ur_i[index]);
            b_loop[binary_vec_to_decimal(tenForm)] = tmp_fr.into();
        }
        mid = mid >> 1;   
    }
    
    // println!("b_l in svc is {}", b_loop[0]);
    let finalA = a_loop[0];
    let finalv = v_loop[0];

    //prepare the polynomial for kzg 
    x_inverse_vec.reverse();
    let root = find_root_of_unity(l-1);
    let coeffs = expand_fx_fft(l-1, &x_inverse_vec, root, l);
    let point = Fr::from_repr(hash_to_field_repr("KZG point")).unwrap();
    let finalv_proof = kzg::open(kzgpp, &coeffs, point).into_affine();

    PI {
        l_vec,
        r_vec,
        finalA, 
        finalv,
        finalv_proof,
    }
}

pub fn verify(pp:&FCpp, kzgpp: &KZGpp, com:&Fq12, i:&usize, a_i: G1Affine, pi:&PI)-> bool {
    
    let n = pp.v_vec.len();
    let l:usize = (n as f64).log2() as usize;
    if *i >= n {
        panic!("Index out of bounds");
    }
    let i_binary_vec = to_fixed_length_binary_vec(i, &l);
    
    let c_loop1 = *com;
    let c_loop2 = G1::from(a_i);
    let mut c_loop = (c_loop1, c_loop2);
    let mut x_loop:FrRepr = FrRepr([0, 0, 0, 0]);
    let mut x_inverse_vec = Vec::with_capacity(l); 

    let mut final_b:Fr = Fr::one();
    for j in 1..l+1 {
        let (left1, left2) = pi.l_vec[j-1];
        let (right1, right2) = pi.r_vec[j-1];
        x_loop = hash_to_x(&x_loop, &left1, &left2, &right1, &right2);
        // println!("x_loop in verification: {:?}", x_loop);
        let x_loop_inverse = Fr::from_repr(x_loop).unwrap().inverse().unwrap();
        x_inverse_vec.push(x_loop_inverse);

        let left1_exp = left1.pow(x_loop);
        // println!("left1_pow: {:?}", left1_exp);

        let x_loop_inverse1:FrRepr = x_loop_inverse.into();
        let right1_exp = right1.pow(x_loop_inverse1);

        c_loop.0.mul_assign(&left1_exp);
        c_loop.0.mul_assign(&right1_exp);

        let left2_exp = left2.mul(x_loop);
        let right2_exp = right2.mul(x_loop_inverse);
        c_loop.1.add_assign(&left2_exp);
        c_loop.1.add_assign(&right2_exp);

        if i_binary_vec[j-1] == 1{
            final_b.mul_assign(&x_loop_inverse);
        }
    }

    let point = Fr::from_repr(hash_to_field_repr("KZG point")).unwrap();
    let mut value = Fr::zero();
    let mut term = point.clone();
    for i in 0..l {
        term.square();// compute point^{2^{i+1}}
        let mut coffi = x_inverse_vec[l-i-1];
        coffi.mul_assign(&term);
        coffi.add_assign(&Fr::one());        
        value.mul_assign(&coffi);
    }
    term.square();// compute point^{2^{i+1}}
    let mut coffi = term.clone();
    coffi.add_assign(&Fr::one());        
    value.mul_assign(&coffi);
    kzg::verify(kzgpp, point, value, pi.finalv, pi.finalv_proof);


    let r1:bool = c_loop.0 == Bls12::pairing(pi.finalA, pi.finalv);
    let r2:bool = c_loop.1 == pi.finalA.mul(final_b).into();

    // println!("r1: {:?}, r2: {:?}", r1, r2);
    r1 && r2
}

pub fn batch_verify(pp:&FCpp, kzgpp: &KZGpp, com:&Fq12, I: &[usize], y_vec:&[G1Affine], pi:&PI)-> bool {
    let n = pp.v_vec.len();
 
    // let mut b_matrix:Vec<Vec<FrRepr>> = vec![];
    // for i in I{
    //     let mut b_vec:Vec<FrRepr> = vec![FrRepr([0, 0, 0, 0]); n];
    //     b_vec[*i] = FrRepr([1, 0, 0, 0]);
    //     b_matrix.push(b_vec);
    // }
    let r_vec = hash_to_r_svc(com, I, y_vec);

    let r_vec_u64: Vec<&[u64; 4]> = r_vec.iter().map(|s| &s.0).collect();
    let y = G1Affine::sum_of_products(y_vec, &r_vec_u64).into_affine();  

    let l:usize = (n as f64).log2() as usize;
    let I_size = I.len();
    let mut I_binary_vec: Vec<Vec<u8>> = Vec::with_capacity(I_size);
    let mut final_ur_i: Vec<Fr> = vec![Fr::one(); I_size];
    for index in 0..I_size{
        I_binary_vec.push(to_fixed_length_binary_vec(&I[index], &l));
        final_ur_i[index] = Fr::from_repr(r_vec[I[index]]).unwrap();
    }
    
    let c_loop1 = *com;
    let c_loop2 = G1::from(y);
    let mut c_loop = (c_loop1, c_loop2);
    let mut x_loop:FrRepr = FrRepr([0, 0, 0, 0]);
    let mut x_inverse_vec = Vec::with_capacity(l); 
    
    for j in 1..l+1 {
        let (left1, left2) = pi.l_vec[j-1];
        let (right1, right2) = pi.r_vec[j-1];
        x_loop = hash_to_x(&x_loop, &left1, &left2, &right1, &right2);
        // println!("x_loop in verification: {:?}", x_loop);
        let x_loop_inverse = Fr::from_repr(x_loop).unwrap().inverse().unwrap();
        x_inverse_vec.push(x_loop_inverse);

        let left1_exp = left1.pow(x_loop);
        // println!("left1_pow: {:?}", left1_exp);

        let x_loop_inverse1:FrRepr = x_loop_inverse.into();
        let right1_exp = right1.pow(x_loop_inverse1);

        c_loop.0.mul_assign(&left1_exp);
        c_loop.0.mul_assign(&right1_exp);

        let left2_exp = left2.mul(x_loop);
        let right2_exp = right2.mul(x_loop_inverse);
        c_loop.1.add_assign(&left2_exp);
        c_loop.1.add_assign(&right2_exp);

        for index in 0..I_size{
            if I_binary_vec[index][j-1] == 1{
                final_ur_i[index].mul_assign(&x_loop_inverse);
            }
        }
    }

    let mut final_b:Fr = Fr::zero();
    for index in 0..I_size{
        final_b.add_assign(&final_ur_i[index]);
    }    

    let point = Fr::from_repr(hash_to_field_repr("KZG point")).unwrap();
    let mut value = Fr::zero();
    let mut term = point.clone();
    for i in 0..l {
        term.square();// compute point^{2^{i+1}}
        let mut coffi = x_inverse_vec[l-i-1];
        coffi.mul_assign(&term);
        coffi.add_assign(&Fr::one());        
        value.mul_assign(&coffi);
    }
    term.square();// compute point^{2^{i+1}}
    let mut coffi = term.clone();
    coffi.add_assign(&Fr::one());        
    value.mul_assign(&coffi);
    kzg::verify(kzgpp, point, value, pi.finalv, pi.finalv_proof);

    let r1:bool = c_loop.0 == Bls12::pairing(pi.finalA, pi.finalv);
    let r2:bool = c_loop.1 == pi.finalA.mul(final_b).into();

    // println!("r1: {:?}, r2: {:?}", r1, r2);
    r1 && r2
}





