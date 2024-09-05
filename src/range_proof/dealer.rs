//! The `dealer` module contains the API for the dealer state while the dealer is
//! engaging in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use core::iter;

extern crate alloc;

use alloc::vec::Vec;

// use curve25519_dalek::ristretto::RistrettoPoint;
// use curve25519_dalek::scalar::Scalar;
use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use merlin::Transcript;

use crate::errors::MPCError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof;
use crate::range_proof::RangeProof;
use crate::transcript::TranscriptProtocol;

use crate::util;

use super::messages::*;

/// Used to construct a dealer for the aggregated rangeproof MPC protocol.
pub struct Dealer {}

impl Dealer {
    /// Creates a new dealer coordinating `m` parties proving `n`-bit ranges.
    pub fn new<'a, 'b>(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        n: usize,
        m: usize,
    ) -> Result<DealerAwaitingBitCommitments<'a, 'b>, MPCError> {
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(MPCError::InvalidBitsize);
        }
        if !m.is_power_of_two() {
            return Err(MPCError::InvalidAggregation);
        }
        if bp_gens.gens_capacity < n {
            return Err(MPCError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(MPCError::InvalidGeneratorsLength);
        }

        // At the end of the protocol, the dealer will attempt to
        // verify the proof, and if it fails, determine which party's
        // shares were invalid.
        //
        // However, verifying the proof requires either knowledge of
        // all of the challenges, or a copy of the initial transcript
        // state.
        //
        // The dealer has all of the challenges, but using them for
        // verification would require duplicating the verification
        // logic.  Instead, we keep a copy of the initial transcript
        // state.
        let initial_transcript = transcript.clone();

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        Ok(DealerAwaitingBitCommitments {
            bp_gens,
            pc_gens,
            transcript,
            initial_transcript,
            n,
            m,
        })
    }
}

/// A dealer waiting for the parties to send their [`BitCommitment`]s.
pub struct DealerAwaitingBitCommitments<'a, 'b> {
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    transcript: &'a mut Transcript,
    /// The dealer keeps a copy of the initial transcript state, so
    /// that it can attempt to verify the aggregated proof at the end.
    initial_transcript: Transcript,
    n: usize,
    m: usize,
}

impl<'a, 'b> DealerAwaitingBitCommitments<'a, 'b> {
    /// Receive each party's [`BitCommitment`]s and compute the [`BitChallenge`].
    pub fn receive_bit_commitments(
        self,
        bit_commitments: Vec<BitCommitment>,
    ) -> Result<(DealerAwaitingPolyCommitments<'a, 'b>, BitChallenge), MPCError> {
        if self.m != bit_commitments.len() {
            return Err(MPCError::WrongNumBitCommitments);
        }

        // Commit each V_j individually
        // for vc in bit_commitments.iter() {
        //     self.transcript.append_point(b"V", &vc.V_j.into());
        // }

        // Commit aggregated A_j, S_j
        // let A: G1Affine = bit_commitments.iter().map(|vc| vc.A_j).sum();
        let mut A = G1::from(G1Affine::one());
        // let S: G1Affine = bit_commitments.iter().map(|vc| vc.S_j).sum();
        let mut S = G1::from(G1Affine::one());
        for i in 0..bit_commitments.len(){    
            let A_tmp = G1::from(bit_commitments[i].A_j);
            let S_tmp = G1::from(bit_commitments[i].S_j);
            A.add_assign(&A_tmp);
            S.add_assign(&S_tmp);
        }
        self.transcript.append_point(b"A", &A.into());
        self.transcript.append_point(b"S", &S.into());

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");
        let bit_challenge = BitChallenge { y, z };

        Ok((
            DealerAwaitingPolyCommitments {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                bit_challenge,
                bit_commitments,
                A: A.into(),
                S: S.into(),
            },
            bit_challenge,
        ))
    }
}

/// A dealer which has sent the [`BitChallenge`] to the parties and
/// is waiting for their [`PolyCommitment`]s.
pub struct DealerAwaitingPolyCommitments<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    bit_challenge: BitChallenge,
    bit_commitments: Vec<BitCommitment>,
    /// Aggregated commitment to the parties' bits
    A: G1Affine,
    /// Aggregated commitment to the parties' bit blindings
    S: G1Affine,
}

impl<'a, 'b> DealerAwaitingPolyCommitments<'a, 'b> {
    /// Receive [`PolyCommitment`]s from the parties and compute the
    /// [`PolyChallenge`].
    pub fn receive_poly_commitments(
        self,
        poly_commitments: Vec<PolyCommitment>,
    ) -> Result<(DealerAwaitingProofShares<'a, 'b>, PolyChallenge), MPCError> {
        if self.m != poly_commitments.len() {
            return Err(MPCError::WrongNumPolyCommitments);
        }

        // Commit sums of T_1_j's and T_2_j's
        // let T_1: G1Affine = poly_commitments.iter().map(|pc| pc.T_1_j).sum();
        // let T_2: G1Affine = poly_commitments.iter().map(|pc| pc.T_2_j).sum();
        let mut T_1 = G1::from(G1Affine::one());
        let mut T_2 = G1::from(G1Affine::one());
        for i in 0..poly_commitments.len(){
            T_1.add_assign(&G1::from(poly_commitments[i].T_1_j));
            T_2.add_assign(&G1::from(poly_commitments[i].T_2_j));
        }

        self.transcript.append_point(b"T_1", &T_1.into());//.compress());
        self.transcript.append_point(b"T_2", &T_2.into());//.compress());

        let x = self.transcript.challenge_scalar(b"x");
        let poly_challenge = PolyChallenge { x };

        Ok((
            DealerAwaitingProofShares {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                bit_challenge: self.bit_challenge,
                bit_commitments: self.bit_commitments,
                A: self.A,
                S: self.S,
                poly_challenge,
                poly_commitments,
                T_1: T_1.into(),
                T_2: T_2.into(),
            },
            poly_challenge,
        ))
    }
}

/// A dealer which has sent the [`PolyChallenge`] to the parties and
/// is waiting to aggregate their [`ProofShare`]s into a
/// [`RangeProof`].
pub struct DealerAwaitingProofShares<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    bit_challenge: BitChallenge,
    bit_commitments: Vec<BitCommitment>,
    poly_challenge: PolyChallenge,
    poly_commitments: Vec<PolyCommitment>,
    A: G1Affine,
    S: G1Affine,
    T_1: G1Affine,
    T_2: G1Affine,
}

impl<'a, 'b> DealerAwaitingProofShares<'a, 'b> {
    /// Assembles proof shares into an `RangeProof`.
    ///
    /// Used as a helper function by `receive_trusted_shares` (which
    /// just hands back the result) and `receive_shares` (which
    /// validates the proof shares.
    fn assemble_shares(&mut self, proof_shares: &[ProofShare]) -> Result<RangeProof, MPCError> {
        if self.m != proof_shares.len() {
            return Err(MPCError::WrongNumProofShares);
        }

        // Validate lengths for each share
        // let mut bad_shares = Vec::<usize>::new(); // no allocations until we append
        // for (j, share) in proof_shares.iter().enumerate() {
        //     share
        //         .check_size(self.n, &self.bp_gens, j)
        //         .unwrap_or_else(|_| {
        //             bad_shares.push(j);
        //         });
        // }

        // if bad_shares.len() > 0 {
        //     return Err(MPCError::MalformedProofShares { bad_shares });
        // }

        // let t_x: FrRepr = proof_shares.iter().map(|ps| ps.t_x).sum();
        // let t_x_blinding: FrRepr = proof_shares.iter().map(|ps| ps.t_x_blinding).sum();
        // let e_blinding: FrRepr = proof_shares.iter().map(|ps| ps.e_blinding).sum();
        let mut t_x = Fr::from_repr(FrRepr([0, 0, 0, 0])).unwrap();
        let mut t_x_blinding = Fr::from_repr(FrRepr([0, 0, 0, 0])).unwrap();
        let mut e_blinding = Fr::from_repr(FrRepr([0, 0, 0, 0])).unwrap();
        for i in 0..proof_shares.len(){
            t_x.add_assign(&Fr::from_repr(proof_shares[i].t_x).unwrap());
            t_x_blinding.add_assign(&Fr::from_repr(proof_shares[i].t_x_blinding).unwrap());
            e_blinding.add_assign(&Fr::from_repr(proof_shares[i].e_blinding).unwrap());         
        }

        self.transcript.append_scalar(b"t_x", &t_x.into());
        self.transcript
            .append_scalar(b"t_x_blinding", &t_x_blinding.into());
        self.transcript.append_scalar(b"e_blinding", &e_blinding.into());

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        // let Q = w * self.pc_gens.B;
        let q_tmp = self.pc_gens.B;
        let Q = q_tmp.mul(w).into();

        let G_factors: Vec<FrRepr> = iter::repeat(FrRepr([1, 0, 0, 0])).take(self.n * self.m).collect();

        let inverse = Fr::from_repr(self.bit_challenge.y).unwrap().inverse().unwrap();
        let H_factors: Vec<FrRepr> = util::exp_iter(inverse.into())
            .take(self.n * self.m)
            .collect();

        let l_vec: Vec<FrRepr> = proof_shares
            .iter()
            .flat_map(|ps| ps.l_vec.clone().into_iter())
            .collect();
        let r_vec: Vec<FrRepr> = proof_shares
            .iter()
            .flat_map(|ps| ps.r_vec.clone().into_iter())
            .collect();

        let ipp_proof = inner_product_proof::InnerProductProof::create(
            self.transcript,
            &Q,
            &G_factors,
            &H_factors,
            self.bp_gens.G(self.n, self.m).cloned().collect(),
            self.bp_gens.H(self.n, self.m).cloned().collect(),
            l_vec,
            r_vec,
        );

        Ok(RangeProof {
            A: self.A,
            S: self.S,
            T_1: self.T_1,
            T_2: self.T_2,
            t_x: t_x.into(),
            t_x_blinding: t_x_blinding.into(),
            e_blinding: e_blinding.into(),
            ipp_proof,
        })
    }

    /// Assemble the final aggregated [`RangeProof`] from the given
    /// `proof_shares`, but skip validation of the proof.
    ///
    /// ## WARNING
    ///
    /// This function does **NOT** validate the proof shares.  It is
    /// suitable for creating aggregated proofs when all parties are
    /// known by the dealer to be honest (for instance, when there's
    /// only one party playing all roles).
    ///
    /// Otherwise, use
    /// [`receive_shares`](DealerAwaitingProofShares::receive_shares),
    /// which validates that all shares are well-formed, or else
    /// detects which party(ies) submitted malformed shares.
    pub fn receive_trusted_shares(
        mut self,
        proof_shares: &[ProofShare],
    ) -> Result<RangeProof, MPCError> {
        self.assemble_shares(proof_shares)
    }
}
