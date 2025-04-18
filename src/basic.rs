use pairing_plus::{bls12_381::*};
use ff_zeroize::{PrimeField};
use sha2::{Digest, Sha512};
use bigint::U512;
use std::ops::Rem;
use pairing_plus::serdes::SerDes;
use byteorder::{LittleEndian, ByteOrder};
use pairing_plus::CurveProjective;
// use std::mem;

use pairing_plus::bls12_381::Fr;
use std::collections::HashMap;
use rustfft::{FftPlanner, num_complex::Complex, Length};
use rustfft::num_traits::Zero;
use ff_zeroize::Field;

#[derive(Clone, Debug)]
pub struct Cpp {
    pub g: G1Affine,
    pub h: G1Affine,
}

#[derive(Clone, Debug)]
pub struct FCpp {
    pub v_vec: Vec<G2Affine>
}

#[derive(Clone, Debug)]
pub struct KZGpp {
    pub g1_alpha: G1Affine,
    pub g2_vec: Vec<G2Affine>
}

#[derive(Clone, Debug)]
pub struct PI {
    pub l_vec: Vec<(Fq12, G1Affine)>,
    pub r_vec: Vec<(Fq12, G1Affine)>,
    pub finalA: G1Affine,
    pub finalv: G2Affine,
    pub finalv_proof: G2Affine
}

#[derive(Clone, Debug)]
pub struct ProverParams {
    pub n: usize,
    pub generators_alpha: Vec<G1Affine>,
}

#[derive(Clone, Debug)]
pub struct VerifierParams {
    pub(crate) n: usize,
    pub generators_alpha: Vec<G2Affine>,
    pub gt_elt: Fq12,
}

/// Hashes a blob into a non-zero field element.
/// hash_to_field_pointproofs use SHA 512 to hash a blob into a non-zero field element.
pub(crate) fn hash_to_field_repr<Blob: AsRef<[u8]>>(input: Blob) -> FrRepr {
    let mut hasher = Sha512::new();
    hasher.input(input);
    let hash_output = hasher.result();
    let mut t = os2ip_mod_p(&hash_output);

    // if we get 0, return 1
    // this should not happen in practise
    if t == FrRepr([0, 0, 0, 0]) {
        t = FrRepr([1, 0, 0, 0]);
    }
    t
}

pub(crate) fn os2ip_mod_p(oct_str: &[u8]) -> FrRepr {
    // "For the purposes of this document, and consistent with ASN.1 syntax,
    // an octet string is an ordered sequence of octets (eight-bit bytes).
    // The sequence is indexed from first (conventionally, leftmost) to last
    // (rightmost).  For purposes of conversion to and from integers, the
    // first octet is considered the most significant in the following
    // conversion primitives.
    //
    // OS2IP converts an octet string to a nonnegative integer.
    // OS2IP (X)
    // Input:  X octet string to be converted
    // Output:  x corresponding nonnegative integer
    // Steps:
    // 1.  Let X_1 X_2 ... X_xLen be the octets of X from first to last,
    //  and let x_(xLen-i) be the integer value of the octet X_i for 1
    //  <= i <= xLen.
    // 2.  Let x = x_(xLen-1) 256^(xLen-1) + x_(xLen-2) 256^(xLen-2) +
    //  ...  + x_1 256 + x_0.
    // 3.  Output x. "

    let r_sec = U512::from(oct_str);

    // hard coded modulus p
    let p = U512::from([
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0x73, 0xED, 0xA7, 0x53, 0x29, 0x9D, 0x7D, 0x48, 0x33, 0x39, 0xD8, 0x08, 0x09, 0xA1,
        0xD8, 0x05, 0x53, 0xBD, 0xA4, 0x02, 0xFF, 0xFE, 0x5B, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
        0x00, 0x00, 0x01,
    ]);
    // t = r % p
    let t_sec = r_sec.rem(p);

    // convert t from a U512 into a primefield object s
    let mut tslide: [u8; 64] = [0; 64];
    let bytes: &mut [u8] = tslide.as_mut();
    t_sec.to_big_endian(bytes);

    FrRepr([
        u64::from_be_bytes([
            bytes[56], bytes[57], bytes[58], bytes[59], bytes[60], bytes[61], bytes[62], bytes[63],
        ]),
        u64::from_be_bytes([
            bytes[48], bytes[49], bytes[50], bytes[51], bytes[52], bytes[53], bytes[54], bytes[55],
        ]),
        u64::from_be_bytes([
            bytes[40], bytes[41], bytes[42], bytes[43], bytes[44], bytes[45], bytes[46], bytes[47],
        ]),
        u64::from_be_bytes([
            bytes[32], bytes[33], bytes[34], bytes[35], bytes[36], bytes[37], bytes[38], bytes[39],
        ]),
    ])
}

/// Hashes a blob into a non-zero field element.
pub(crate) fn hash_to_x(x_loop: &FrRepr, left1: &Fq12, left2: &G1Affine, right1: &Fq12, right2: &G1Affine) -> FrRepr {
        // hash the values into scalars
        let mut ser_left1: Vec<u8> = vec![];
        let mut ser_right1: Vec<u8> = vec![];
        let mut ser_left2: Vec<u8> = vec![];
        let mut ser_right2: Vec<u8> = vec![];
        match GT_serialize(left1, &mut ser_left1, true) {
            Ok(_p) => _p,
            Err(_e) => (),
        };

        match G1_serialize(left2, &mut ser_left2, true) {
            Ok(_p) => _p,
            Err(_e) => (),
        };
        match GT_serialize(right1, &mut ser_right1, true) {
            Ok(_p) => _p,
            Err(_e) => (),
        };
        match G1_serialize(right2, &mut ser_right2, true) {
            Ok(_p) => _p,
            Err(_e) => (),
        };

        let ser_left = [ser_left1, ser_left2].concat();
        let ser_right = [ser_right1, ser_right2].concat();   
        let ser_x_loop: Vec<u8> = fr_repr_to_string(x_loop)[..].as_bytes().to_vec(); 
        let result = hash_to_field_repr([ser_x_loop, ser_left, ser_right].concat());

        result
}

/// Hash a array of bytes into non-zero scalars. 
pub(crate) fn hash_to_r(
    com: &Fq12,
    b_matrix: &[Vec<FrRepr>],
    y_vec: &[G1Affine],
) -> Vec<FrRepr> {
    // tmp = C | b_matrix | y_vec
    let mut tmp: Vec<u8> = vec![];
    // add C
    match GT_serialize(&com, &mut tmp, true) {
        Ok(_p) => _p,
        Err(e) => (),
    };
    //add a b_matrix
    for i in 0..b_matrix.len() {
        for j in 0..b_matrix[i].len() {
            let t = b_matrix[i][j].as_ref();
           // tmp.append(&mut t.to_vec());
            let input = t.to_vec();//u64
            let mut output: Vec<u8> = vec!(0;32);
            LittleEndian::write_u64_into(&input, &mut output);
            tmp.append(&mut output);
        }
    }

    // add b_vec
    for i in 0..y_vec.len() {
        // serialize commitment
        match G1_serialize(&y_vec[i], &mut tmp, true) {
            Ok(_p) => _p,
            Err(e) => (),
        };
    }

    let mut hasher = Sha512::new();
    hasher.input(tmp);
    let digest = hasher.result();

    let mut r_vec:Vec<FrRepr> = Vec::with_capacity(y_vec.len());
    for b_vec in b_matrix{
        let mut b_vec_ser: Vec<u8> = vec![];
        for e in b_vec {
            let t = e.as_ref();
            let input = t.to_vec();//u64
            let mut output: Vec<u8> = vec!(0;32);
            LittleEndian::write_u64_into(&input, &mut output);
            b_vec_ser.append(&mut output);
        }
        r_vec.push(hash_to_field_repr([b_vec_ser, digest.as_ref().to_vec()].concat()));
    }

    r_vec
}

/// Convert a pop into a blob:
///
/// `| element |` => bytes
///
/// Returns an error if ciphersuite id is invalid or serialization fails.
pub fn G1_serialize<W: std::io::Write>(
    element: &G1Affine,
    writer: &mut W,
    compressed: bool,
) -> std::io::Result<()> {
    // compressed must be true
    if !compressed {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            String::from("Error Compress"),
        ));
    }

    let mut buf: Vec<u8> = vec![0];
    element.serialize(&mut buf, compressed)?;

    // format the output
    writer.write_all(&buf)?;
    Ok(())
}

/// Convert a pop into a blob:
///
/// `| element |` => bytes
///
/// Returns an error if ciphersuite id is invalid or serialization fails.
pub fn GT_serialize<W: std::io::Write>(
    element: &Fq12,
    writer: &mut W,
    compressed: bool,
) -> std::io::Result<()> {
    // compressed must be true
    if !compressed {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            String::from("Error Compress"),
        ));
    }

    let mut buf: Vec<u8> = vec![0];
    element.serialize(&mut buf, compressed)?;

    // format the output
    writer.write_all(&buf)?;
    Ok(())
}

pub fn fr_repr_to_string(fr_repr: &FrRepr) -> String {
    format!("{}", fr_repr)  // transfer to string with Display trait
}

pub fn to_fixed_length_binary_vec(value: &usize, length: &usize) -> Vec<u8> {
    // convert `usize` into binary string
    let binary_str = format!("{:b}", value);
    
    // pad zeros before real number
    let padded_binary_str = format!("{:0>width$}", binary_str, width = length);
    
    // convert binary string into `Vec<u8>`
    padded_binary_str.chars()
        .map(|c| c.to_digit(2).unwrap() as u8) // convert char '0' or '1' into number 0 or 1
        .collect()
}

pub fn expand_fx_fft(l: usize, r_vec: &[Fr], root: Fr, log_n: usize) -> Vec<Fr> {
    assert_eq!(r_vec.len(), l + 1);

    let mut coeffs = vec![Fr::one()];
    let n = (1 << log_n)+1;

    for j in 0..=l {
        let k = 2usize.pow((j + 1) as u32);
        let r = r_vec[j];
        let mut factor = vec![Fr::one()];
        factor.resize(k, Fr::zero());
        factor.push(r);

        factor.resize(n, Fr::zero());
        coeffs.resize(n, Fr::zero());

        coeffs = polynomial_multiply(&coeffs, &factor);
    }

    while coeffs.last() == Some(&Fr::zero()) {
        coeffs.pop();
    }
    coeffs
}

pub fn find_root_of_unity(log_n: usize) -> Fr {
    Fr::from_str("5").unwrap()
}

fn fr_to_complex(fr: Fr) -> Complex<f64> {
    let fr_value = fr.into_repr().0; 
    Complex::new(fr_value[0] as f64, 0.0)
}

pub fn polynomial_multiply(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
    let len = a.len() + b.len() - 1;
    let fft_len = len.next_power_of_two();
    let mut planner = FftPlanner::<f64>::new();
    
    let fft = planner.plan_fft_forward(fft_len);
    let ifft = planner.plan_fft_inverse(fft_len);

    let mut a_complex: Vec<Complex<f64>> = a.iter().map(|&x| fr_to_complex(x)).collect();
    let mut b_complex: Vec<Complex<f64>> = b.iter().map(|&x| fr_to_complex(x)).collect();

    a_complex.resize(fft_len, Complex::zero());
    b_complex.resize(fft_len, Complex::zero());

    fft.process(&mut a_complex);
    fft.process(&mut b_complex);

    let mut c_complex: Vec<Complex<f64>> = a_complex.iter().zip(&b_complex)
        .map(|(&a, &b)| a * b)
        .collect();

    ifft.process(&mut c_complex);

    c_complex.iter()
        .take(len)
        .map(|c| {
            let real = c.re / fft_len as f64;
            Fr::from_str(&(real.round() as u64).to_string()).unwrap()
        })
        .collect()
}

// A wrapper of `hash_to_outer_repr` that outputs `Fr`s instead of `FrRepr`s.
pub(crate) fn dim2_hash_fr(
    commits: &[G1],
    set: &[Vec<usize>],
    value_sub_vector: &[Vec<FrRepr>],
    n: usize,
) -> Result<Vec<Fr>, String> {
    Ok(dim2_hash_repr(commits, set, value_sub_vector, n)?
        .iter()
        .map(|s| Fr::from_repr(*s).unwrap())
        .collect())
}

/// Hash a two dim array of bytes into non-zero scalars.
pub(crate) fn dim2_hash_repr(
    commits: &[G1],
    set: &[Vec<usize>],
    value_sub_vector: &[Vec<FrRepr>],
    n: usize,
) -> Result<Vec<FrRepr>, String> {
    if commits.len() != set.len() || commits.len() != value_sub_vector.len() {
        return Err(String::from("Mismatch Size"));
    };

    if commits.len() == 1 {
        return Ok(vec![FrRepr([1, 0, 0, 0])]);
    }

    // tmp = {C | S | m[S]} for i \in [0 .. commit.len-1]
    let mut tmp: Vec<u8> = vec![];
    for i in 0..commits.len() {
        // serialize commitment
        match commitment_serialize(&commits[i], &mut tmp, true) {
            Ok(_p) => _p,
            Err(e) => return Err(e.to_string()),
        };
        // add the set to tmp
        for j in 0..set[i].len() {
            let t = set[i][j].to_be_bytes();
            tmp.append(&mut t.to_vec());
        }

        // if the set leng does not mathc values, return an error
        if set[i].len() != value_sub_vector[i].len() {
            return Err(String::from("Mismatch Size"));
        }

        // add values to set; returns an error if index is out of range
        for j in 0..set[i].len() {
            if set[i][j] >= n {
                return Err(String::from("Invalid Index"));
            }
            let t = value_sub_vector[i][j].as_ref();
           // tmp.append(&mut t.to_vec());
            let input = t.to_vec();//u64
            let mut output: Vec<u8> = vec!(0;32);
            LittleEndian::write_u64_into(&input, &mut output);
            tmp.append(&mut output);
        }
    }

    let mut hasher = Sha512::new();
    hasher.input(tmp);
    let digest = hasher.result();

    // formulate the output
    Ok((0..commits.len())
        .map(|i| {
            // each field element t_i is generated as
            // t_i = hash_to_field (i | C | S | m[S])
            hash_to_field_repr([&i.to_be_bytes()[..], digest.as_ref()].concat())
        })
        .collect::<Vec<FrRepr>>())
}

// A wrapper of `hash_to_ti` that outputs `Fr`s instead of `FrRepr`s.
pub(crate) fn dim1_hash_fr(
    commit: &G1,
    set: &[usize],
    value_sub_vector: &[FrRepr],
    n: usize,
) -> Result<Vec<Fr>, String> {
    Ok(dim1_hash_repr(commit, set, value_sub_vector, n)?
        .iter()
        // the hash_to_ti_repr should already produce valid Fr elements
        // so it is safe to unwrap here
        .map(|s| Fr::from_repr(*s).unwrap())
        .collect())
}

/// Hash a array of bytes into non-zero scalars. 
pub(crate) fn dim1_hash_repr(
    commit: &G1,
    set: &[usize],
    value_sub_vector: &[FrRepr],
    n: usize,
) -> Result<Vec<FrRepr>, String> {
    // if the set leng does not mathc values, return an error
    if set.len() != value_sub_vector.len() {
        return Err(String::from("Mismatch Size"));
    }

    // handle the case where there is only one input
    // in this case, simply return FrRepr::one()
    if set.len() == 1 {
        return Ok(vec![FrRepr([1, 0, 0, 0])]);
    }

    // add values to set; returns an error if index is out of range
    for e in set {
        if *e >= n {
            return Err(String::from("Invalid Index"));
        }
    }

    // tmp = C | S | m[S]
    let mut tmp: Vec<u8> = vec![];
    // serialize commitment
    match commitment_serialize(commit, &mut tmp, true) {
        Ok(_p) => _p,
        Err(e) => return Err(e.to_string()),
    };
    // add the set to tmp
    for index in set {
        let t = index.to_be_bytes();
        tmp.append(&mut t.to_vec());
    }
    // add values to set; returns an error if index is out of range
    for e in value_sub_vector {
        let t = e.as_ref();

        let input = t.to_vec();//u64
        let mut output: Vec<u8> = vec!(0;32);
        LittleEndian::write_u64_into(&input, &mut output);
        tmp.append(&mut output);
    }

    let mut hasher = Sha512::new();
    hasher.input(tmp);
    let digest = hasher.result();

    // formulate the output
    Ok(set
        .iter()
        .map(|index| {
            hash_to_field_repr([&index.to_be_bytes()[..], digest.as_ref()].concat())
        })
        .collect())
}


/// Convert a pop into a blob:
///
/// `| commit |` => bytes
///
/// Returns an error if ciphersuite id is invalid or serialization fails.
fn commitment_serialize<W: std::io::Write>(
    commit: &G1,
    writer: &mut W,
    compressed: bool,
) -> std::io::Result<()> {
    // compressed must be true
    if !compressed {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            String::from("Error Compress"),
        ));
    }

    let mut buf: Vec<u8> = vec![0];
    commit.into_affine().serialize(&mut buf, compressed)?;

    // format the output
    writer.write_all(&buf)?;
    Ok(())
}
