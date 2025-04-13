use crate::autochunker::{intermediate_state::*, proof::RawProof};
use crate::bn254::ell_coeffs::{ell_affine, AffinePairing, BnAffinePairing, G2Prepared};
use crate::bn254::fp254impl::Fp254Impl;
use crate::bn254::utils::fq_to_bits;
use crate::groth16::constants::LAMBDA;
use crate::groth16::offchain_checker::compute_c_wi;
use ark_bn254::Config;
use ark_bn254::Fq6Config;
use ark_bn254::{Fq, Fq12, Fq2, Fq6, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::bn::BnConfig;
use ark_ec::pairing::MillerLoopOutput;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, Field, One, PrimeField};
use ark_ff::{CyclotomicMultSubgroup, Fp6Config};
use ark_std::cfg_chunks_mut;
use bitcoin_script::{script, Script};
use core::ops::Neg;
use itertools::Itertools;
use log::{debug, error, info, warn};
use num_bigint::BigUint;
use std::sync::Arc;

pub type ComputeFn = Box<dyn Fn(&mut ComputeCtx, Vec<State>) -> State>;
pub type ScriptFn = Box<dyn Fn(&mut ComputeCtx, Vec<State>) -> (Script, Vec<Vec<u8>>)>;

#[derive(Debug, Clone)]
pub struct ComputeCtx {
    pub proof: RawProof,
    pub msm_points_from_pk: Vec<G1Affine>,
    pub msm_scalars: Vec<Fr>,
    pub vky0: G1Affine,
    pub p1q1: Fq6,                // immutable
    pub p2: G1Affine,             // immutable
    pub p4: G1Affine,             // immutable
    pub q4: G2Affine,             // immutable
    pub q3: G2Affine,             // immutable
    pub q2: G2Affine,             // immutable
    pub t4: G2Affine,             // mutable
    pub t3: G2Affine,             // mutable
    pub t2: G2Affine,             // mutable
    pub f: Option<Fq6>,           // mutable
    pub evaluate_p4: Option<Fq6>, // mutable, the result of evaluate line of p4
    pub evaluate_p3: Option<Fq6>, // mutable, the result of evaluate line of p3
    pub evaluate_p2: Option<Fq6>, // mutable, the result of evaluate line of p2
    pub c: Fq6,
    pub c_inv: Fq6,
}

impl From<RawProof> for ComputeCtx {
    fn from(raw_proof: RawProof) -> Self {
        info!("proof public inputs: {}", raw_proof.public.len());

        let mut msm_scalar = raw_proof.public.clone();
        msm_scalar.reverse();

        let mut msm_gs = raw_proof.vk.gamma_abc_g1.clone(); // vk.vk_pubs[0]
        msm_gs.reverse();

        let vky0 = msm_gs.pop().unwrap();

        let mut p3 = G1Projective::ZERO;

        p3 = p3 + vky0 * ark_bn254::Fr::ONE;

        for i in 0..raw_proof.public.len() {
            let result = msm_gs[i] * msm_scalar[i];
            debug!(
                "msm for {}, scalar {:?} x point {:?} = {:?}",
                i, msm_gs[i], msm_scalar[i], result
            );
            p3 += result;
            info!(
                "rawproof result of msm step {}: {:?}",
                i,
                p3.clone().into_affine()
            );
        }

        info!("rawproof result of msm: {:?}", p3.clone().into_affine());

        let p3 = p3.into_affine();

        let (p2, p1, p4) = (raw_proof.proof.c, raw_proof.vk.alpha_g1, raw_proof.proof.a);
        let (q3, q2, q1, q4) = (
            raw_proof.vk.gamma_g2.into_group().neg().into_affine(),
            raw_proof.vk.delta_g2.into_group().neg().into_affine(),
            -raw_proof.vk.beta_g2,
            raw_proof.proof.b,
        );
        let pairing = BnAffinePairing;
        let f_fixed = pairing.multi_miller_loop_affine([p1], [q1]).0;
        let f = pairing
            .multi_miller_loop_affine([p1, p2, p3, p4], [q1, q2, q3, q4])
            .0;
        let f_without_p1q1 = pairing
            .multi_miller_loop_affine([p2, p3, p4], [q2, q3, q4])
            .0;
        assert_eq!(f, f_fixed * f_without_p1q1);
        let (c, _) = compute_c_wi(f);
        let c_inv = c.inverse().unwrap();
        let result = f * (c_inv.pow(LAMBDA.to_u64_digits()));

        assert_eq!(result.c1, Fq6::ZERO);

        let f = pairing
            .multi_miller_loop_affine_with_c([p1, p2, p3, p4], [q1, q2, q3, q4], c, c_inv)
            .0;
        assert_eq!(f, result);

        let f = pairing
            .multi_miller_loop_affine_with_c([p2, p3, p4], [q2, q3, q4], c, c_inv)
            .0;
        assert_eq!(f * f_fixed, result);

        if result.c1 != Fq6::ZERO {
            error!(
                "check the result of pairing: {:?}, proof is not correct",
                result
            );
        } else {
            info!(
                "check the result of pairing: {:?}, proof is correct",
                result
            );
        }

        Self {
            proof: raw_proof,
            msm_points_from_pk: msm_gs,
            msm_scalars: msm_scalar,
            vky0: vky0,
            p1q1: f_fixed.c1 / f_fixed.c0,
            p2: p2,
            p4: p4,
            c: c.c1 / c.c0,
            c_inv: c_inv.c1 / c_inv.c0,
            t4: q4,
            t3: q3,
            t2: q2,
            q4: q4,
            q3: q3,
            q2: q2,
            f: Some(c_inv.c1 / c_inv.c0),
            evaluate_p4: None,
            evaluate_p3: None,
            evaluate_p2: None,
        }
    }
}

impl BnAffinePairing {
    pub fn multi_miller_loop_affine_with_c(
        &self,
        a: impl IntoIterator<Item = impl Into<ark_ec::bn::G1Prepared<ark_bn254::Config>>>,
        b: impl IntoIterator<Item = impl Into<G2Prepared>>,
        c: Fq12,
        c_inv: Fq12,
    ) -> MillerLoopOutput<ark_bn254::Bn254> {
        let mut pairs = a
            .into_iter()
            .zip_eq(b)
            .filter_map(|(p, q)| {
                // if input q is projective coordinates, then we will enter `into` computing pairing mode
                // otherwise if input q is affine coordinates, then we will enter `into` verifying pairing mode
                let (p, q) = (p.into(), q.into());
                match !p.is_zero() && !q.is_zero() {
                    true => Some((
                        -p.0.x / p.0.y,
                        p.0.y.inverse().unwrap(),
                        q.ell_coeffs.into_iter(),
                    )),
                    false => None,
                }
            })
            .collect::<Vec<_>>();

        let mut f = cfg_chunks_mut!(pairs, 4)
            .map(|pairs| {
                let mut f = ark_bn254::Fq12::one();
                f = c_inv;
                for i in (1..Config::ATE_LOOP_COUNT.len()).rev() {
                    // if i != Config::ATE_LOOP_COUNT.len() - 1 {
                    f.square_in_place();
                    // }

                    for (coeff_1, coeff_2, coeffs) in pairs.iter_mut() {
                        ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
                    }

                    let bit = Config::ATE_LOOP_COUNT[i - 1];

                    if bit == 1 {
                        f = f * c_inv;
                    } else if bit == -1 {
                        f = f * c;
                    }

                    if bit == 1 || bit == -1 {
                        for (coeff_1, coeff_2, coeffs) in pairs.iter_mut() {
                            ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
                        }
                    }
                }
                f
            })
            .product::<ark_bn254::Fq12>();

        if Config::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }

        let c_invp = c_inv.frobenius_map(1);
        let c_p2 = c.frobenius_map(2);
        let c_invp3 = c_inv.frobenius_map(3);
        f = f * c_invp * c_p2 * c_invp3;

        for (coeff_1, coeff_2, coeffs) in &mut pairs {
            ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
        }

        for (coeff_1, coeff_2, coeffs) in &mut pairs {
            ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
        }

        MillerLoopOutput(f)
    }
}

mod tests {
    use crate::autochunker::{compute_ctx::ComputeCtx, proof::RawProof};
    use ark_bn254::{Fq, Fq2, Fq6};
    use core::ops::Neg;
    use log::info;

    #[test_log::test]
    fn test_raw_proof_to_compute_ctx() {
        let raw_proof = RawProof::mock_proof();
        let _: ComputeCtx = raw_proof.into();
    }
}
