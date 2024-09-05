extern crate alloc;

use alloc::borrow::Borrow;
use alloc::vec::Vec;

use core::iter;
// use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
// use curve25519_dalek::scalar::Scalar;
// use curve25519_dalek::traits::VartimeMultiscalarMul;
use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective};
use ff_zeroize::{Field, PrimeField};

use merlin::Transcript;
use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;

#[derive(Clone, Debug)]
pub struct InnerProductProof {
    pub(crate) L_vec: Vec<G1Affine>,
    pub(crate) R_vec: Vec<G1Affine>,
    pub(crate) a: FrRepr,
    pub(crate) b: FrRepr,
}

impl InnerProductProof {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        Q: &G1Affine,
        G_factors: &[FrRepr],
        H_factors: &[FrRepr],
        mut G_vec: Vec<G1Affine>,
        mut H_vec: Vec<G1Affine>,
        mut a_vec: Vec<FrRepr>,
        mut b_vec: Vec<FrRepr>,
    ) -> InnerProductProof {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        if n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let a_L_length = a_L.len();
            let mut a_L_zip_g_fractor:Vec<FrRepr> = Vec::with_capacity(a_L_length);
            for k in 0..a_L_length{
                let mut a = Fr::from_repr(a_L[k].clone()).unwrap();
                let b = Fr::from_repr((G_factors[n+k]).clone()).unwrap();
                a.mul_assign(&b);
                let tmp:FrRepr = a.into();
                a_L_zip_g_fractor.push(tmp);       
            }
            let b_R_length = b_R.len();
            let mut b_R_zip_h_fractor:Vec<FrRepr> = Vec::with_capacity(b_R_length);
            for k in 0..b_R_length{
                let mut a = Fr::from_repr((b_R[k]).clone()).unwrap();
                let b = Fr::from_repr((H_factors[k]).clone()).unwrap();
                a.mul_assign(&b);
                let tmp:FrRepr = a.into();
                b_R_zip_h_fractor.push(tmp);       
            }
            let mut c_L_vec:Vec<FrRepr> = Vec::new();
            c_L_vec.push(c_L);

            let L = G1Affine::sum_of_products(
                &G_R.iter().chain(H_L.iter()).chain(iter::once(Q)).cloned().collect::<Vec<_>>()[..],
                &a_L_zip_g_fractor.iter()
                    .chain(b_R_zip_h_fractor.iter())
                    .chain(c_L_vec.iter()).map(|s| &s.0).collect::<Vec<_>>()[..],          
            )
            .into_affine();

            let a_R_length = a_R.len();
            let mut a_R_zip_g_fractor:Vec<FrRepr> = Vec::with_capacity(a_R_length);
            for k in 0..a_R_length{
                let mut a = Fr::from_repr(a_R[k].clone()).unwrap();
                let b = Fr::from_repr((G_factors[k]).clone()).unwrap();
                a.mul_assign(&b);
                let tmp:FrRepr = a.into();
                a_R_zip_g_fractor.push(tmp);       
            }
            let b_L_length = b_L.len();
            let mut b_L_zip_h_fractor:Vec<FrRepr> = Vec::with_capacity(b_L_length);
            for k in 0..b_L_length{
                let mut a = Fr::from_repr((b_L[k]).clone()).unwrap();
                let b = Fr::from_repr((H_factors[n+k]).clone()).unwrap();
                a.mul_assign(&b);
                let tmp:FrRepr = a.into();
                b_L_zip_h_fractor.push(tmp);       
            }
            let mut c_R_vec:Vec<FrRepr> = Vec::new();
            c_R_vec.push(c_R);
            let R = G1Affine::sum_of_products(
                &G_L.iter().chain(H_R.iter()).chain(iter::once(Q)).map(|s| *s).collect::<Vec<_>>()[..],
                &a_R_zip_g_fractor.iter()
                    .chain(b_L_zip_h_fractor.iter())
                    .chain(c_R_vec.iter()).map(|s| &s.0).collect::<Vec<_>>()[..],       
            )
            .into_affine();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            // let u_inv = u.invert();
            let u_inv = Fr::from_repr(u).unwrap().inverse().unwrap();
            

            for i in 0..n {
                // a_L[i] = a_L[i] * u + u_inv * a_R[i];
                let mut tmp1 = Fr::from_repr(a_L[i]).unwrap();
                tmp1.mul_assign(&Fr::from_repr(u).unwrap());
                let mut tmp2 = Fr::from_repr(a_R[i]).unwrap();
                tmp2.mul_assign(&u_inv);
                tmp1.add_assign(&tmp2);
                a_L[i] = tmp1.into();
                // b_L[i] = b_L[i] * u_inv + u * b_R[i];
                let mut tmp3 = Fr::from_repr(b_L[i]).unwrap();
                tmp3.mul_assign(&u_inv);
                let mut tmp4 = Fr::from_repr(b_R[i]).unwrap();
                tmp4.mul_assign(&Fr::from_repr(u).unwrap());
                tmp3.add_assign(&tmp4);
                b_L[i] = tmp3.into();

                let mut g_fr1 = Fr::from_repr(G_factors[i]).unwrap();
                g_fr1.mul_assign(&u_inv);
                let mut g_fr2 = Fr::from_repr(G_factors[n + i]).unwrap();
                g_fr2.mul_assign(&Fr::from_repr(u).unwrap());
                let g_vec:Vec<FrRepr> = vec![g_fr1.into(), g_fr2.into()];
                let g_vec_u64: Vec<&[u64; 4]> = g_vec.iter().map(|s| &s.0).collect();
                G_L[i] = G1Affine::sum_of_products(
                    &[G_L[i], G_R[i]],
                    &g_vec_u64 //[u_inv * G_factors[i], u * G_factors[n + i]],
                ).into();

                let mut h_fr1 = Fr::from_repr(H_factors[i]).unwrap();
                h_fr1.mul_assign(&Fr::from_repr(u).unwrap());
                let mut h_fr2 = Fr::from_repr(H_factors[n + i]).unwrap();
                h_fr2.mul_assign(&u_inv);
                let h_vec:Vec<FrRepr> = vec![h_fr1.into(), h_fr2.into()];
                let h_vec_u64: Vec<&[u64; 4]> = h_vec.iter().map(|s| &s.0).collect();
                H_L[i] = G1Affine::sum_of_products(
                    &[H_L[i], H_R[i]],
                    &h_vec_u64//[u * H_factors[i], u_inv * H_factors[n + i]],       
                ).into();
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        while n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let L = G1Affine::sum_of_products(
                &G_R.iter().chain(H_L.iter()).chain(iter::once(Q)).map(|s| *s).collect::<Vec<_>>()[..],
                &a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)).map(|s| &s.0).collect::<Vec<_>>()[..],     
            )
            .into_affine();

            
            let R = G1Affine::sum_of_products(
                &G_L.iter().chain(H_R.iter()).chain(iter::once(Q)).map(|s| *s).collect::<Vec<_>>()[..],
                &a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)).map(|s| &s.0).collect::<Vec<_>>()[..],          
            )
            .into_affine();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = Fr::from_repr(u).unwrap().inverse().unwrap();
            // let u_inv = u.invert();

            for i in 0..n {
                // a_L[i] = a_L[i] * u + u_inv * a_R[i];
                let mut a_l_fr = Fr::from_repr(a_L[i]).unwrap();
                a_l_fr.mul_assign(&Fr::from_repr(u).unwrap());
                let mut a_r_fr = Fr::from_repr(a_R[i]).unwrap();
                a_r_fr.mul_assign(&u_inv);
                a_l_fr.add_assign(&a_r_fr);
                a_L[i] = a_l_fr.into();

                // b_L[i] = b_L[i] * u_inv + u * b_R[i];
                let mut b_l_fr = Fr::from_repr(b_L[i]).unwrap();
                b_l_fr.mul_assign(&u_inv);
                let mut b_r_fr = Fr::from_repr(b_R[i]).unwrap();
                b_r_fr.mul_assign(&Fr::from_repr(u).unwrap());
                b_l_fr.add_assign(&b_r_fr);
                b_L[i] = b_l_fr.into();

                let u_inv_frep:FrRepr = u_inv.into();
                let vec1 = vec![u_inv_frep.clone(), u.clone()];
                let vec2 = vec![u.clone(), u_inv_frep.clone()];
                let g_vec_u64: Vec<&[u64; 4]> = vec1.iter().map(|s| &s.0).collect();
                let h_vec_u64: Vec<&[u64; 4]> = vec2.iter().map(|s| &s.0).collect();
                G_L[i] = G1Affine::sum_of_products(&[G_L[i], G_R[i]], &g_vec_u64).into();
                H_L[i] = G1Affine::sum_of_products(&[H_L[i], H_R[i]], &h_vec_u64).into();
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        InnerProductProof {
            L_vec: L_vec,
            R_vec: R_vec,
            a: a[0],
            b: b[0],
        }
    }

    /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
    /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<FrRepr>, Vec<FrRepr>, Vec<FrRepr>), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges.push(transcript.challenge_scalar(b"u"));
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        // let allinv = Scalar::batch_invert(&mut challenges_inv);
        let mut challenges_inv = challenges.clone();
        let mut allinv = FrRepr([1, 0, 0, 0]);
        for i in 0..lg_n{
            challenges_inv[i] = Fr::from_repr(challenges_inv[i]).unwrap().inverse().unwrap().into();
            let mut tmp = Fr::from_repr(allinv).unwrap();
            tmp.mul_assign(&Fr::from_repr(challenges_inv[i]).unwrap());
            allinv = allinv.into();
        }       

        // 3. Compute u_i^2 and (1/u_i)^2

        for i in 0..lg_n {
            // XXX missing square fn upstream
            // challenges[i] = challenges[i] * challenges[i];
            let mut cha_tmp = Fr::from_repr(challenges[i]).unwrap();
            let tmp = cha_tmp.clone();
            cha_tmp.mul_assign(&tmp);
            challenges[i]=cha_tmp.into();
            // challenges_inv[i] = challenges_inv[i] * challenges_inv[i];
            let mut cha_inv_tmp = Fr::from_repr(challenges_inv[i]).unwrap();
            let tmp2 = cha_inv_tmp.clone();
            cha_inv_tmp.mul_assign(&tmp2);
            challenges_inv[i]=cha_inv_tmp.into();
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.

        let mut s = Vec::with_capacity(n);
        s.push(allinv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            let mut tmp = Fr::from_repr(s[i - k]).unwrap();
            tmp.mul_assign(&Fr::from_repr(u_lg_i_sq).unwrap());
            // s.push(s[i - k] * u_lg_i_sq);
            s.push(tmp.into());
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &G1Affine,
        Q: &G1Affine,
        G: &[G1Affine],
        H: &[G1Affine],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<FrRepr>,
        IH: IntoIterator,
        IH::Item: Borrow<FrRepr>,
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| {
                // (self.a * s_i) * g_i.borrow()
                let mut a = Fr::from_repr(self.a.clone()).unwrap();
                a.mul_assign(&Fr::from_repr((*s_i).clone()).unwrap());
                a.mul_assign(&Fr::from_repr(*g_i.borrow()).unwrap());
                let result:FrRepr = a.into();
                result
            }).take(G.len()).map(|s| s);
        // let mut g_times_a_times_s = Vec::with_capacity(G.len());
        // for i in 0..G.len(){
        //     let mut a = Fr::from_repr(self.a).unwrap();
        //     a.mul_assign(&Fr::from_repr(s[i].clone()).unwrap());
        //     a.mul_assign(&Fr::from_repr(G_factors[i].borrow()).unwrap());
        //     let result = a.into();
        //     g_times_a_times_s.push(result);
        // }

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| {
                // (self.b * s_i_inv) * h_i.borrow()
                let mut a = Fr::from_repr(self.b).unwrap();
                a.mul_assign(&Fr::from_repr((*s_i_inv).clone()).unwrap());
                a.mul_assign(&Fr::from_repr(*h_i.borrow()).unwrap());
                let result:FrRepr = a.into();
                result
            });
        // let mut h_times_b_div_s = Vec::with_capacity(H_factors.len());
        // for i in 0..H_factors.len(){
        //     let mut a = Fr::from_repr(self.b).unwrap();
        //     a.mul_assign(&Fr::from_repr(inv_s[i]).unwrap());
        //     a.mul_assign(&Fr::from_repr(H_factors[i].borrow()).unwrap());
        //     let result = a.into();
        //     h_times_b_div_s.push(result);
        // }

        // let neg_u_sq = u_sq.iter().map(|ui| -ui);
        // let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -ui);
        let neg_u_sq = u_sq.iter().map(|ui| 
            {let mut result = Fr::from_repr(*ui).unwrap(); 
                result.negate(); 
                let result_repr:FrRepr = result.into();
                result_repr
            });
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| 
            {let mut result = Fr::from_repr(*ui).unwrap(); 
                result.negate(); 
                let result_repr:FrRepr = result.into();
                result_repr
            });

        // let Ls = self
        //     .L_vec
        //     .iter()
        //     .map(|p| p)
        //     .collect()::<Result<Vec<_>, _>>()?;
        let Ls = self.L_vec.clone();

        // let Rs = self
        //     .R_vec
        //     .iter()
        //     .map(|p| p)
        //     .collect()::<Result<Vec<_>, _>>()?;
        let Rs = self.R_vec.clone();

        let mut a_tmp = Fr::from_repr(self.a).unwrap();
        a_tmp.mul_assign(&Fr::from_repr(self.b).unwrap());
        let a_tmp_frep:FrRepr = a_tmp.into();
        let a_iter = iter::once(a_tmp_frep)
                        .chain(g_times_a_times_s)
                        .chain(h_times_b_div_s)
                        .chain(neg_u_sq)
                        .chain(neg_u_inv_sq);
        let a_iter_u64 = a_iter.map(|s| s.0).collect::<Vec<_>>();
        let expect_P = G1Affine::sum_of_products(
            &iter::once(Q)
                .chain(G.iter())
                .chain(H.iter())
                .chain(Ls.iter())
                .chain(Rs.iter()).map(|s| *s).collect::<Vec<_>>()[..],
            &a_iter_u64.iter().map(|s| s).collect::<Vec<_>>()[..],           
        );

        if expect_P == (*P).into() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[FrRepr], b: &[FrRepr]) -> FrRepr {
    let mut out = Fr::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        let mut tmp = Fr::from_repr(a[i]).unwrap();
        tmp.mul_assign(&Fr::from_repr(b[i]).unwrap());
        out.add_assign(&tmp);
        // out += a[i] * b[i];
    }
    out.into()
}