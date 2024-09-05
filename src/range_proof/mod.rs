extern crate alloc;

extern crate rand;


use self::rand::thread_rng;
use alloc::vec::Vec;

use core::iter;

// use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
// use curve25519_dalek::scalar::Scalar;
use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use crate::algorithm::basic::hash_to_field_repr;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::transcript::TranscriptProtocol;
use crate::util;

use rand_core::{CryptoRng, RngCore};
use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize};

// Modules for MPC protocol

pub mod dealer;
pub mod messages;
pub mod party;

/// The `RangeProof` struct represents a proof that one or more values
/// are in a range.
///
/// The `RangeProof` struct contains functions for creating and
/// verifying aggregated range proofs.  The single-value case is
/// implemented as a special case of aggregated range proofs.
///
/// The bitsize of the range, as well as the list of commitments to
/// the values, are not included in the proof, and must be known to
/// the verifier.
///
/// This implementation requires that both the bitsize `n` and the
/// aggregation size `m` be powers of two, so that `n = 8, 16, 32, 64`
/// and `m = 1, 2, 4, 8, 16, ...`.  Note that the aggregation size is
/// not given as an explicit parameter, but is determined by the
/// number of values or commitments passed to the prover or verifier.
///
/// # Note
///
/// For proving, these functions run the multiparty aggregation
/// protocol locally.  That API is exposed in the [`aggregation`](::range_proof_mpc)
/// module and can be used to perform online aggregation between
/// parties without revealing secret values to each other.
#[derive(Clone, Debug)]
pub struct RangeProof {
    /// Commitment to the bits of the value
    A: G1Affine,
    /// Commitment to the blinding factors
    S: G1Affine,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: G1Affine,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: G1Affine,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: FrRepr,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: FrRepr,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: FrRepr,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl RangeProof {
    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple`].
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate bulletproofs;
    /// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 1.
    /// let bp_gens = BulletproofGens::new(64, 1);
    ///
    /// // A secret value we want to prove lies in the range [0, 2^32)
    /// let secret_value = 1037578891u64;
    ///
    /// // The API takes a blinding factor for the commitment.
    /// let blinding = Scalar::random(&mut thread_rng());
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create a 32-bit rangeproof.
    /// let (proof, committed_value) = RangeProof::prove_single(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     secret_value,
    ///     &blinding,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    
    
    pub fn prove_single_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &FrRepr,
        n: usize,
        rng: &mut T,
    ) -> Result<RangeProof, ProofError> {
        let p = RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            &[v],
            &[*v_blinding],
            n,
            rng,
        )?;
        Ok(p)
    }

    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_single_with_rng`],
    /// passing in a threadsafe RNG.
    // #[cfg(feature = "std")]
    pub fn prove_single(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &FrRepr,
        n: usize,
    ) -> Result<RangeProof, ProofError> {
        RangeProof::prove_single_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            v,
            v_blinding,
            n,
            &mut thread_rng(),
        )
    }

    /// Create a rangeproof for a set of values.
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate bulletproofs;
    /// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 16.
    /// let bp_gens = BulletproofGens::new(64, 16);
    ///
    /// // Four secret values we want to prove lie in the range [0, 2^32)
    /// let secrets = [4242344947u64, 3718732727u64, 2255562556u64, 2526146994u64];
    ///
    /// // The API takes blinding factors for the commitments.
    /// let blindings: Vec<_> = (0..4).map(|_| Scalar::random(&mut thread_rng())).collect();
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create an aggregated 32-bit rangeproof and corresponding commitments.
    /// let (proof, commitments) = RangeProof::prove_multiple(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     &secrets,
    ///     &blindings,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_multiple(&bp_gens, &pc_gens, &mut verifier_transcript, &commitments, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_multiple_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[FrRepr],
        n: usize,
        rng: &mut T,
    ) -> Result<RangeProof, ProofError> {
        use self::dealer::*;
        use self::party::*;

        if values.len() != blindings.len() {
            return Err(ProofError::WrongNumBlindingFactors);
        }

        let dealer = Dealer::new(bp_gens, pc_gens, transcript, n, values.len())?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| Party::new(bp_gens, pc_gens, v, v_blinding, n))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let (parties, bit_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| {
                p.assign_position_with_rng(j, rng)
                    .expect("We already checked the parameters, so this should never happen")
            })
            .unzip();

        // let value_commitments: Vec<_> = bit_commitments.iter().map(|c| c.V_j).collect();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(bit_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge_with_rng(&bit_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let proof = dealer.receive_trusted_shares(&proof_shares)?;

        // Ok((proof, value_commitments))
        Ok(proof)
    }

    /// Create a rangeproof for a set of values.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    // #[cfg(feature = "std")]
    pub fn prove_multiple(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[FrRepr],
        n: usize,
    ) -> Result<RangeProof, ProofError> {
        RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            values,
            blindings,
            n,
            &mut thread_rng(),
        )
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around `verify_multiple` for the `m=1` case.
    pub fn verify_single_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &G1Affine,
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(bp_gens, pc_gens, transcript, &[*V], n, rng)
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around [`RangeProof::verify_single_with_rng`],
    /// passing in a threadsafe RNG.
    // #[cfg(feature = "std")]
    pub fn verify_single(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &G1Affine,
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_single_with_rng(bp_gens, pc_gens, transcript, V, n, &mut thread_rng())
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    pub fn verify_multiple_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[G1Affine],
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        let m = value_commitments.len();

        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        
        transcript.rangeproof_domain_sep(n as u64, m as u64);

        for V in value_commitments.iter() {
            // Allow the commitments to be zero (0 value, 0 blinding)
            // See https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r255167177
            transcript.append_point(b"V", V);
        }
        
        transcript.validate_and_append_point(b"A", &self.A.into())?;
        transcript.validate_and_append_point(b"S", &self.S.into())?;

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        let z_fr = Fr::from_repr(z).unwrap();
        // let zz = z * z;
        let mut zz = z_fr;
        zz.mul_assign(&z_fr);
        // let minus_z = -z;
        let mut minus_z = z_fr;
        minus_z.negate();
        
        transcript.validate_and_append_point(b"T_1", &self.T_1.into())?;
        transcript.validate_and_append_point(b"T_2", &self.T_2.into())?;

        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &self.t_x);
        transcript.append_scalar(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &self.e_blinding);

        let w = transcript.challenge_scalar(b"w");
        
        // Challenge value for batching statements to be verified
        let c = hash_to_field_repr("c");

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(n * m, transcript)?;
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;
        
        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<FrRepr> = util::exp_iter(FrRepr::from(2u64)).take(n).collect();
        let concat_z_and_2: Vec<FrRepr> = util::exp_iter(z)
            .take(m)
            .flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| {
                // exp_2 * exp_z 
                let mut exp_2_tmp = Fr::from_repr(*exp_2).unwrap();
                exp_2_tmp.mul_assign(&Fr::from_repr(exp_z).unwrap());
                exp_2_tmp.into()
            }))
            .collect();
        
        let g = s.iter().map(|s_i| {
            // minus_z - a * s_i
            let mut minus_z_fr:Fr = minus_z.clone();
            let mut a_fr:Fr = Fr::from_repr(a).unwrap();
            a_fr.mul_assign(&Fr::from_repr(*s_i).unwrap());
            minus_z_fr.sub_assign(&a_fr);
            a_fr.into()
        });
        
        let y_inverse = Fr::from_repr(y).unwrap().inverse().unwrap();
        let h = s_inv
            .zip(util::exp_iter(y_inverse.into_repr()))//y.invert()))
            .zip(concat_z_and_2.iter())
            .map(|((s_i_inv, exp_y_inv), z_and_2)| {
                // z + exp_y_inv * (zz * z_and_2 - b * s_i_inv)
                let mut term1 = zz;
                term1.mul_assign(&Fr::from_repr(*z_and_2).unwrap());
                let mut term2 = Fr::from_repr(*s_i_inv).unwrap();
                term2.mul_assign(&Fr::from_repr(b).unwrap());
                term1.sub_assign(&term2);
                term1.mul_assign(&Fr::from_repr(exp_y_inv).unwrap());
                term1.add_assign(&Fr::from_repr(z).unwrap());
                term1.into()
            });
        
        let value_commitment_scalars = util::exp_iter(z).take(m).map(|z_exp| {
            // c * zz * z_exp
            let mut tmp = zz;
            tmp.mul_assign(&Fr::from_repr(c).unwrap());
            tmp.mul_assign(&Fr::from_repr(z_exp).unwrap());
            tmp.into()
        });
        
        // let basepoint_scalar = w * (self.t_x - a * b) + c * (delta(n, m, &y, &z) - self.t_x);
        let mut term1_sub1 = Fr::from_repr(self.t_x).unwrap();
        let mut term1_sub2 = Fr::from_repr(a).unwrap();
        term1_sub2.mul_assign(&Fr::from_repr(b).unwrap());
        term1_sub1.sub_assign(&term1_sub2);
        term1_sub1.mul_assign(&Fr::from_repr(w).unwrap());
        let mut term2 = Fr::from_repr(delta(n, m, &y, &z)).unwrap();
        term2.sub_assign(&Fr::from_repr(self.t_x).unwrap());
        term2.mul_assign(&Fr::from_repr(c).unwrap());
        term1_sub1.add_assign(&term2);
        let basepoint_scalar = term1_sub1.into();
        
        // c * x
        let x_fr = Fr::from_repr(x).unwrap();
        let mut c_time_x = x_fr;
        c_time_x.mul_assign(&Fr::from_repr(c).unwrap());
        let c_time_x_repr:FrRepr = c_time_x.into();
        let mut c_time_x_two = c_time_x;
        c_time_x_two.mul_assign(&x_fr);
        let c_time_x_two_repr:FrRepr = c_time_x_two.into();
        
        // -self.e_blinding - c * self.t_x_blinding
        let mut term1:Fr = Fr::from_repr(self.e_blinding).unwrap();
        term1.negate();
        let mut term2 = Fr::from_repr(self.t_x_blinding).unwrap();
        term2.mul_assign(&Fr::from_repr(c).unwrap());
        term1.sub_assign(&term2);
        let e_sub_x_repr:FrRepr = term1.into();
        
        let repr_one = FrRepr([1, 0, 0, 0]);
        let x_sq_iter = x_sq.iter().cloned();
        let x_inv_sq_iter= x_inv_sq.iter().cloned();
        let a_iter:Vec<_> = iter::once(repr_one)
                        .chain(iter::once(x))
                        .chain(iter::once(c_time_x_repr))
                        .chain(iter::once(c_time_x_two_repr))
                        .chain(x_sq_iter)
                        .chain(x_inv_sq_iter)
                        .chain(iter::once(e_sub_x_repr))
                        .chain(iter::once(basepoint_scalar))
                        .chain(g)
                        .chain(h)
                        .chain(value_commitment_scalars).collect();
                      
        // use curve25519_dalek::traits::VartimeMultiscalarMul;
        let mega_check = G1Affine::sum_of_products(
            &iter::once(self.A)
                .chain(iter::once(self.S))
                .chain(iter::once(self.T_1))
                .chain(iter::once(self.T_2))
                .chain(self.ipp_proof.L_vec.iter().map(|L| *L))
                .chain(self.ipp_proof.R_vec.iter().map(|R| *R))
                .chain(iter::once(Some(pc_gens.B_blinding).unwrap()))
                .chain(iter::once(Some(pc_gens.B).unwrap()))
                .chain(bp_gens.G(n, m).map(|&x| Some(x).unwrap()))
                .chain(bp_gens.H(n, m).map(|&x| Some(x).unwrap()))
                .chain(value_commitments.iter().map(|V| *V)).collect::<Vec<_>>()[..],
            &a_iter.iter().map(|s| &s.0).collect::<Vec<_>>()[..],        
        );
        Ok(())
        // .ok_or_else(|| ProofError::VerificationError)?;
        // use group::Group;
        // if mega_check.is_identity().into() {
        //     Ok(())   
        // } else {
        //     Err(ProofError::VerificationError)
        // }
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    /// This is a convenience wrapper around [`RangeProof::verify_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    // #[cfg(feature = "std")]
    pub fn verify_multiple(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[G1Affine],
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            value_commitments,
            n,
            &mut thread_rng(),
        )
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle \mathbf{1}, {\mathbf{y}}^{n \cdot m} \rangle - \sum_{j=0}^{m-1} z^{j+3} \cdot \langle \mathbf{1}, {\mathbf{2}}^{n \cdot m} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &FrRepr, z: &FrRepr) -> FrRepr {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&FrRepr::from(2u64), n);
    let sum_z = util::sum_of_powers(z, m);

    // (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
    let z_fr = Fr::from_repr(*z).unwrap();
    let mut z_square = z_fr;
    z_square.mul_assign(&z_fr);
    let mut z_cube_mul_others = z_square;
    z_cube_mul_others.mul_assign(&z_fr);
    z_cube_mul_others.mul_assign(&Fr::from_repr(sum_2).unwrap());
    z_cube_mul_others.mul_assign(&Fr::from_repr(sum_z).unwrap());

    let mut tmp = z_fr;
    tmp.sub_assign(&z_square);
    tmp.mul_assign(&Fr::from_repr(sum_y).unwrap());
    tmp.sub_assign(&z_cube_mul_others);
    
    tmp.into()
}
