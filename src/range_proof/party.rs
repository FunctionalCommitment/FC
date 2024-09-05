//! The `party` module contains the API for the party state while the party is
//! engaging in an aggregated multiparty computation protocol.
//!
//! Each state of the MPC protocol is represented by a different Rust
//! type.  The state transitions consume the previous state, making it
//! a compile error to perform the steps out of order or to repeat a
//! step.
//!
//! For more explanation of how the `dealer`, `party`, and `messages`
//! modules orchestrate the protocol execution, see the documentation
//! in the [`aggregation`](::range_proof_mpc) module.

extern crate alloc;

use alloc::vec::Vec;
use clear_on_drop::clear::Clear;
use core::iter;
// use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
// use curve25519_dalek::scalar::Scalar;
use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective};
use ff_zeroize::{Field, PrimeField};
use crate::algorithm::basic::hash_to_field_repr;
use rand_core::{CryptoRng, RngCore};

use crate::errors::MPCError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::util;

// #[cfg(feature = "std")]
use rand::thread_rng;

use super::messages::*;

/// Used to construct a party for the aggregated rangeproof MPC protocol.
pub struct Party {}

impl Party {
    /// Constructs a `PartyAwaitingPosition` with the given rangeproof parameters.
    pub fn new<'a>(
        bp_gens: &'a BulletproofGens,
        pc_gens: &'a PedersenGens,
        v: u64,
        v_blinding: FrRepr,
        n: usize,
    ) -> Result<PartyAwaitingPosition<'a>, MPCError> {
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(MPCError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(MPCError::InvalidGeneratorsLength);
        }

        // let V = pc_gens.commit(v.into(), v_blinding);

        Ok(PartyAwaitingPosition {
            bp_gens,
            pc_gens,
            n,
            v,
            v_blinding,
            // V,
        })
    }
}

/// A party waiting for the dealer to assign their position in the aggregation.
pub struct PartyAwaitingPosition<'a> {
    bp_gens: &'a BulletproofGens,
    pc_gens: &'a PedersenGens,
    n: usize,
    v: u64,
    v_blinding: FrRepr,
    // V: G1Affine,
}

impl<'a> PartyAwaitingPosition<'a> {
    /// Assigns a position in the aggregated proof to this party,
    /// allowing the party to commit to the bits of their value.
    // #[cfg(feature = "std")]
    // pub fn assign_position(
    //     self,
    //     j: usize,
    // ) -> Result<(PartyAwaitingBitChallenge<'a>, BitCommitment), MPCError> {
    //     self.assign_position_with_rng(j, &mut thread_rng())
    // }

    /// Assigns a position in the aggregated proof to this party,
    /// allowing the party to commit to the bits of their value.
    pub fn assign_position_with_rng<T: RngCore + CryptoRng>(
        self,
        j: usize,
        rng: &mut T,
    ) -> Result<(PartyAwaitingBitChallenge<'a>, BitCommitment), MPCError> {
        if self.bp_gens.party_capacity <= j {
            return Err(MPCError::InvalidGeneratorsLength);
        }

        let bp_share = self.bp_gens.share(j);

        let a_blinding = hash_to_field_repr("a_blinding");
        // Compute A = <a_L, G> + <a_R, H> + a_blinding * B_blinding
        // let mut A = self.pc_gens.B_blinding * a_blinding;
        let mut A = self.pc_gens.B_blinding.mul(a_blinding);

        use subtle::Choice;
        // use subtle::ConditionallySelectable;
        let mut i = 0;
        for (G_i, H_i) in bp_share.G(self.n).zip(bp_share.H(self.n)) {
            // If v_i = 0, we add a_L[i] * G[i] + a_R[i] * H[i] = - H[i]
            // If v_i = 1, we add a_L[i] * G[i] + a_R[i] * H[i] =   G[i]
            let v_i = Choice::from(((self.v >> i) & 1) as u8);
            // let mut point = -H_i;
            let point = H_i; //G1::from(H_i.into_projective().negate());
            // let point = G1Affine::conditional_select(&point, G_i, v_i);
            if v_i.into() {
                let point = G_i;
            }else{
                let point = &point;
            }
            // A += point;
            let point_tmp = (*point).into();
            A.add_assign(&point_tmp);         
            i += 1;
        }

        let s_blinding = hash_to_field_repr("s_blinding");
        let s_L: Vec<FrRepr> = (0..self.n).map(|i| hash_to_field_repr(format!("s_L {}", i))).collect();
        let s_R: Vec<FrRepr> = (0..self.n).map(|i| hash_to_field_repr(format!("s_R {}", i))).collect();

        // Compute S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        // use curve25519_dalek::traits::MultiscalarMul;
        let S = G1Affine::sum_of_products(
            &iter::once(&self.pc_gens.B_blinding)
                .chain(bp_share.G(self.n))
                .chain(bp_share.H(self.n)).map(|s| *s).collect::<Vec<_>>()[..],
            &iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()).map(|s| &s.0).collect::<Vec<_>>()[..],
        );

        // Return next state and all commitments
        let bit_commitment = BitCommitment {
            // V_j: self.V.into(),
            A_j: A.into(),
            S_j: S.into(),
        };
        let next_state = PartyAwaitingBitChallenge {
            n: self.n,
            v: self.v,
            v_blinding: self.v_blinding,
            pc_gens: self.pc_gens,
            j,
            a_blinding,
            s_blinding,
            s_L,
            s_R,
        };
        Ok((next_state, bit_commitment))
    }
}

/// Overwrite secrets with null bytes when they go out of scope.
impl<'a> Drop for PartyAwaitingPosition<'a> {
    fn drop(&mut self) {
        self.v.clear();
        self.v_blinding.clear();
    }
}

/// A party which has committed to the bits of its value
/// and is waiting for the aggregated value challenge from the dealer.
pub struct PartyAwaitingBitChallenge<'a> {
    n: usize, // bitsize of the range
    v: u64,
    v_blinding: FrRepr,
    j: usize,
    pc_gens: &'a PedersenGens,
    a_blinding: FrRepr,
    s_blinding: FrRepr,
    s_L: Vec<FrRepr>,
    s_R: Vec<FrRepr>,
}

impl<'a> PartyAwaitingBitChallenge<'a> {
    /// Receive a [`BitChallenge`] from the dealer and use it to
    /// compute commitments to the party's polynomial coefficients.
    // #[cfg(feature = "std")]
    // pub fn apply_challenge(
    //     self,
    //     vc: &BitChallenge,
    // ) -> (PartyAwaitingPolyChallenge, PolyCommitment) {
    //     self.apply_challenge_with_rng(vc, &mut thread_rng())
    // }

    /// Receive a [`BitChallenge`] from the dealer and use it to
    /// compute commitments to the party's polynomial coefficients.
    pub fn apply_challenge_with_rng<T: RngCore + CryptoRng>(
        self,
        vc: &BitChallenge,
        rng: &mut T,
    ) -> (PartyAwaitingPolyChallenge, PolyCommitment) {
        let n = self.n;
        let offset_y = util::scalar_exp_vartime(&vc.y, (self.j * n) as u64);
        let offset_z = util::scalar_exp_vartime(&vc.z, self.j as u64);

        // Calculate t by calculating vectors l0, l1, r0, r1 and multiplying
        let mut l_poly = util::VecPoly1::zero(n);
        let mut r_poly = util::VecPoly1::zero(n);

        // let offset_zz = vc.z * vc.z * offset_z;
        let mut vc_z_fr = Fr::from_repr(vc.z).unwrap();
        let mut offset_zz = vc_z_fr;
        offset_zz.mul_assign(&vc_z_fr);
        offset_zz.mul_assign(&Fr::from_repr(offset_z).unwrap());
        
        let exp_y = offset_y; // start at y^j
        let mut exp_2 = FrRepr([1, 0, 0, 0]);//::ONE; // start at 2^0 = 1
        for i in 0..n {
            let a_L_i = FrRepr::from((self.v >> i) & 1);
            // let a_R_i = a_L_i - Scalar::ONE;
            let mut a_L_i_fr = Fr::from_repr(a_L_i).unwrap();
            a_L_i_fr.sub_assign(&Fr::one());
            let a_R_i = a_L_i_fr.into();       

            // l_poly.0[i] = a_L_i - vc.z;
            let mut tmp = Fr::from_repr(a_L_i).unwrap();
            tmp.sub_assign(&Fr::from_repr(vc.z).unwrap());
            l_poly.0[i] = tmp.into();
            l_poly.1[i] = self.s_L[i];

            // r_poly.0[i] = exp_y * (a_R_i + vc.z) + offset_zz * exp_2;
            offset_zz.mul_assign(&Fr::from_repr(exp_2).unwrap());
            vc_z_fr.add_assign(&Fr::from_repr(a_R_i).unwrap());
            let mut exp_y_fr = Fr::from_repr(exp_y).unwrap();
            vc_z_fr.mul_assign(&exp_y_fr);
            vc_z_fr.add_assign(&offset_zz);
            r_poly.0[i] = vc_z_fr.into();

            // r_poly.1[i] = exp_y * self.s_R[i];
            let mut s_R_fr =  Fr::from_repr(self.s_R[i]).unwrap();
            s_R_fr.mul_assign(&exp_y_fr);
            r_poly.1[i] = s_R_fr.into();

            // exp_y *= vc.y; // y^i -> y^(i+1)
            exp_y_fr.mul_assign(&Fr::from_repr(vc.y).unwrap());
            // exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
            let mut exp_2_fr =  Fr::from_repr(exp_2).unwrap();
            let exp_2_fr_tmp = exp_2_fr;
            exp_2_fr.add_assign(&exp_2_fr_tmp);
            exp_2 = exp_2_fr.into();
        }

        let t_poly = l_poly.inner_product(&r_poly);

        // Generate x by committing to T_1, T_2 (line 49-54)
        let t_1_blinding = hash_to_field_repr("t_1_blinding");
        let t_2_blinding = hash_to_field_repr("t_2_blinding");
        let T_1 = self.pc_gens.commit(t_poly.1, t_1_blinding);
        let T_2 = self.pc_gens.commit(t_poly.2, t_2_blinding);

        let poly_commitment = PolyCommitment {
            T_1_j: T_1,
            T_2_j: T_2,
        };

        let papc = PartyAwaitingPolyChallenge {
            v_blinding: self.v_blinding,
            a_blinding: self.a_blinding,
            s_blinding: self.s_blinding,
            offset_zz: offset_zz.into(),
            l_poly,
            r_poly,
            t_poly,
            t_1_blinding,
            t_2_blinding,
        };

        (papc, poly_commitment)
    }
}

/// Overwrite secrets with null bytes when they go out of scope.
impl<'a> Drop for PartyAwaitingBitChallenge<'a> {
    fn drop(&mut self) {
        self.v.clear();
        self.v_blinding.clear();
        self.a_blinding.clear();
        self.s_blinding.clear();

        // Important: due to how ClearOnDrop auto-implements InitializableFromZeroed
        // for T: Default, calling .clear() on Vec compiles, but does not
        // clear the content. Instead, it only clears the Vec's header.
        // Clearing the underlying buffer item-by-item will do the job, but will
        // keep the header as-is, which is fine since the header does not contain secrets.
        for e in self.s_L.iter_mut() {
            e.clear();
        }
        for e in self.s_R.iter_mut() {
            e.clear();
        }
    }
}

/// A party which has committed to their polynomial coefficents
/// and is waiting for the polynomial challenge from the dealer.
pub struct PartyAwaitingPolyChallenge {
    offset_zz: FrRepr,
    l_poly: util::VecPoly1,
    r_poly: util::VecPoly1,
    t_poly: util::Poly2,
    v_blinding: FrRepr,
    a_blinding: FrRepr,
    s_blinding: FrRepr,
    t_1_blinding: FrRepr,
    t_2_blinding: FrRepr,
}

impl PartyAwaitingPolyChallenge {
    /// Receive a [`PolyChallenge`] from the dealer and compute the
    /// party's proof share.
    pub fn apply_challenge(self, pc: &PolyChallenge) -> Result<ProofShare, MPCError> {
        // Prevent a malicious dealer from annihilating the blinding
        // factors by supplying a zero challenge.
        if pc.x == FrRepr([0, 0, 0, 0]) {
            return Err(MPCError::MaliciousDealer);
        }

        let mut offset_zz_fr = Fr::from_repr(self.offset_zz).unwrap();
        offset_zz_fr.mul_assign(&Fr::from_repr(self.v_blinding).unwrap());
        let t_blinding_poly = util::Poly2(
            offset_zz_fr.into(), // self.offset_zz * self.v_blinding,
            self.t_1_blinding,
            self.t_2_blinding,
        );

        let t_x = self.t_poly.eval(pc.x);
        let t_x_blinding = t_blinding_poly.eval(pc.x);
        // let e_blinding = self.a_blinding + self.s_blinding * &pc.x;
        let mut pcx_fr = Fr::from_repr(pc.x).unwrap();
        pcx_fr.mul_assign(&Fr::from_repr(self.s_blinding).unwrap());
        pcx_fr.add_assign(&Fr::from_repr(self.a_blinding).unwrap());
        let e_blinding = pcx_fr.into();
        let l_vec = self.l_poly.eval(pc.x);
        let r_vec = self.r_poly.eval(pc.x);

        Ok(ProofShare {
            t_x_blinding,
            t_x,
            e_blinding,
            l_vec,
            r_vec,
        })
    }
}

/// Overwrite secrets with null bytes when they go out of scope.
impl Drop for PartyAwaitingPolyChallenge {
    fn drop(&mut self) {
        self.v_blinding.clear();
        self.a_blinding.clear();
        self.s_blinding.clear();
        self.t_1_blinding.clear();
        self.t_2_blinding.clear();

        // Note: polynomials r_poly, l_poly and t_poly
        // are cleared within their own Drop impls.
    }
}
