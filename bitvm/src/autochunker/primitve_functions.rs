use crate::autochunker::{intermediate_state::*, proof::RawProof};
use crate::bn254::ell_coeffs::{AffinePairing, BnAffinePairing};
use crate::groth16::offchain_checker::compute_c_wi;
use ark_bn254::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use log::info;
use std::ops::Neg;
use std::sync::Arc;

pub type ComputeFn = Box<Arc<dyn Fn(ComputeCtx, Vec<State>) -> State + Send + Sync + 'static>>;

pub struct ComputeCtx {
    proof: RawProof,
    msm_points_from_pk: Vec<G1Affine>,
}

// TODO: abstract to a well-defined script
pub fn msm_step_initial() -> (ComputeFn, usize) {
    fn func(compute_ctx: ComputeCtx, inputs: Vec<State>) -> State {
        assert!(inputs.len() == 1);
        let input = inputs[0].get_fq();
        // todo: some bits of input
        State::Fq(None)
    }
    (Box::new(Arc::new(func)), 302955)
}

pub fn fake_input() -> ComputeFn {
    fn func(compute_ctx: ComputeCtx, _inputs: Vec<State>) -> State {
        State::Fq(None)
    }
    Box::new(Arc::new(func))
}

impl From<RawProof> for ComputeCtx {
    fn from(raw_proof: RawProof) -> Self {
        info!("proof public inputs: {}", raw_proof.public.len());

        let mut msm_scalar = raw_proof.public.clone();
        msm_scalar.reverse();
        let mut msm_gs = raw_proof.vk.gamma_abc_g1.clone(); // vk.vk_pubs[0]
        msm_gs.reverse();

        let vky0 = msm_gs.pop().unwrap();

        let mut p3 = vky0 * ark_bn254::Fr::ONE;

        for i in 0..raw_proof.public.len() {
            let result = msm_gs[i] * msm_scalar[i];
            info!(
                "msm for {}, scalar {:?} x point {:?} = {:?}",
                i, msm_gs[i], msm_scalar[i], result
            );
            p3 += result;
        }
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
        let (c, _) = compute_c_wi(f);

        Self {
            proof: raw_proof,
            msm_points_from_pk: msm_gs,
        }
    }
}
