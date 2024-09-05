//! The `messages` module contains the API for the messages passed between the parties and the dealer
//! in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

extern crate alloc;

use alloc::vec::Vec;
// use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
// use curve25519_dalek::scalar::Scalar;
// use curve25519_dalek::traits::VartimeMultiscalarMul;
use pairing_plus::{bls12_381::*};

/// A commitment to the bits of a party's value.
#[derive(Copy, Clone, Debug)]
pub struct BitCommitment {
    // pub(super) V_j: G1,
    pub(super) A_j: G1Affine,
    pub(super) S_j: G1Affine,
}

/// Challenge values derived from all parties' [`BitCommitment`]s.
#[derive(Copy, Clone, Debug)]
pub struct BitChallenge {
    pub(super) y: FrRepr,
    pub(super) z: FrRepr,
}

/// A commitment to a party's polynomial coefficents.
#[derive(Copy, Clone, Debug)]
pub struct PolyCommitment {
    pub(super) T_1_j: G1Affine,
    pub(super) T_2_j: G1Affine,
}

/// Challenge values derived from all parties' [`PolyCommitment`]s.
#[derive(Copy, Clone, Debug)]
pub struct PolyChallenge {
    pub(super) x: FrRepr,
}

/// A party's proof share, ready for aggregation into the final
/// [`RangeProof`](::RangeProof).
#[derive(Clone, Debug)]
pub struct ProofShare {
    pub(super) t_x: FrRepr,
    pub(super) t_x_blinding: FrRepr,
    pub(super) e_blinding: FrRepr,
    pub(super) l_vec: Vec<FrRepr>,
    pub(super) r_vec: Vec<FrRepr>,
}