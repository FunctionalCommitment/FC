use pairing_plus::{bls12_381::*};
use ff_zeroize::{PrimeField};
use sha2::{Digest, Sha512};
use bigint::U512;
use std::ops::Rem;
use pairing_plus::serdes::SerDes;
use byteorder::{LittleEndian, ByteOrder};
// use std::mem;

#[derive(Clone, Debug)]
pub struct Cpp {
    pub g: G1Affine,
    pub h: G1Affine,
}

#[derive(Clone, Debug)]
pub struct VCpp {
    pub v_vec: Vec<G2Affine>
}

#[derive(Clone, Debug)]
pub struct PI {
    pub l_vec: Vec<(Fq12, G1Affine)>,
    pub r_vec: Vec<(Fq12, G1Affine)>,
    pub finalA: G1Affine,
    pub finalv: G2Affine,
    // pub finalv_proof: G2
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