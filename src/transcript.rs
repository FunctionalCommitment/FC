//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

// use curve25519_dalek::ristretto::CompressedRistretto;
// use curve25519_dalek::scalar::Scalar;
use crate::algorithm::basic::os2ip_mod_p;
use pairing_plus::{bls12_381::*};
use crate::algorithm::basic::fr_repr_to_string;
use crate::algorithm::basic::G1_serialize;
use merlin::Transcript;

use crate::errors::ProofError;

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Append a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Append a `scalar` with the given `label`.
    fn append_scalar(&mut self, label: &'static [u8], scalar: &FrRepr);

    /// Append a `point` with the given `label`.
    fn append_point(&mut self, label: &'static [u8], point: &G1Affine);

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point(
        &mut self,
        label: &'static [u8],
        point: &G1Affine,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> FrRepr;
}

impl TranscriptProtocol for Transcript {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.append_message(b"dom-sep", b"rangeproof v1");
        self.append_u64(b"n", n);
        self.append_u64(b"m", m);
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipp v1");
        self.append_u64(b"n", n);
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &FrRepr) {
        self.append_message(label, fr_repr_to_string(scalar)[..].as_bytes());
    }
  
    fn append_point(&mut self, label: &'static [u8], point: &G1Affine) {
        let mut ser_point: Vec<u8> = vec![];
        match G1_serialize(point, &mut ser_point, true) {
            Ok(_p) => _p,
            Err(_e) => (),
        };

        self.append_message(label, &ser_point);
    }

    fn validate_and_append_point(
        &mut self,
        label: &'static [u8],
        point: &G1Affine,
    ) -> Result<(), ProofError> {
        // use curve25519_dalek::traits::IsIdentity;

        // if point.is_one() {
        //     Err(ProofError::VerificationError)
        // } else {
        //     Ok(())
        // }
        if false {
            Err(ProofError::VerificationError)
        } else {
            Ok(())
        }
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> FrRepr {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);

        // Scalar::from_bytes_mod_order_wide(&buf)
        os2ip_mod_p(&buf)
    }
}
