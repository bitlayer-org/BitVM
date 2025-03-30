use crate::autochunker::{intermediate_state::*, proof::RawProof};
use crate::bn254::ell_coeffs::{AffinePairing, BnAffinePairing};
use crate::bn254::fp254impl::Fp254Impl;
use crate::bn254::utils::fq_to_bits;
use crate::groth16::constants::LAMBDA;
use crate::groth16::offchain_checker::compute_c_wi;
use ark_bn254::{Fq, Fq6, Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, Field, One, PrimeField};
use log::{info, warn};
use num_bigint::BigUint;
use std::ops::Neg;
use std::sync::Arc;

pub type ComputeFn = Box<Arc<dyn Fn(ComputeCtx, Vec<State>) -> State + Send + Sync + 'static>>;

#[derive(Debug, Clone)]
pub struct ComputeCtx {
    proof: RawProof,
    msm_points_from_pk: Vec<G1Affine>,
    msm_scalars: Vec<Fr>,
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
        let f_without_p1q1 = pairing
            .multi_miller_loop_affine([p2, p3, p4], [q2, q3, q4])
            .0;
        let (c, _) = compute_c_wi(f);
        let c_inv = c.inverse().unwrap();
        let result = f * (c_inv.pow(LAMBDA.to_u64_digits()));

        if result.c1 != Fq6::ZERO {
            warn!(
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
        }
    }
}

/// window multiplication
pub fn msm_initial(window: usize) -> (ComputeFn, usize) {
    // the first step of msm
    let (index, chunk_index) = (0, 0);

    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        assert!(inputs.len() == 1);

        // get the scalar and base
        let scalar = inputs[index].get_fr();
        let base: G1Affine = compute_ctx
            .msm_points_from_pk
            .get(index)
            .expect("at least one public input")
            .clone();

        // precompute fr to bits
        let scalar_chunks = fq_to_bits(scalar.into_bigint(), window); // {a_0, ..,a_N}
        info!(
            "windows of mul table: {}",
            (crate::bn254::fr::Fr::N_BITS as usize + window - 1) / window
        );

        // doubled based + current windows' result
        let doubled_base = (base * Fr::from(1 << (chunk_index * window))).into_affine(); // (2^(w.i) P)
        let window_result = (base * Fr::from(scalar_chunks[chunk_index])).into_affine();

        State::G1(Some((doubled_base + window_result).into_affine()))
    };

    (Box::new(Arc::new(func)), 302955)
}

pub fn windows_of_mul_table(window: usize) -> usize {
    let tables = (crate::bn254::fr::Fr::N_BITS as usize + window - 1) / window;
    info!("windows of mul table: {}", tables);
    tables
}

pub fn msm_steps(index: usize, chunk_index: usize, window: usize) -> (ComputeFn, usize) {
    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        assert!(inputs.len() == 2);

        // get the accumulator of msm
        let msm_acc = inputs[1].get_g1();

        // get the scalar and base
        let scalar = inputs[0].get_fr();
        let base: G1Affine = compute_ctx
            .msm_points_from_pk
            .get(index)
            .expect("at least one public input")
            .clone();

        // precompute fr to bits
        let scalar_chunks = fq_to_bits(scalar.into_bigint(), window); // {a_0, ..,a_N}

        // doubled based + current windows' result
        let doubled_base =
            (base * Fr::from(BigUint::one() << (chunk_index * window))).into_affine(); // (2^(w.i) P)
        let window_result = (base * Fr::from(scalar_chunks[chunk_index])).into_affine();

        State::G1(Some((doubled_base + window_result + msm_acc).into_affine()))
    };

    (Box::new(Arc::new(func)), 302955)
}

pub fn extract_scalar(index: usize) -> ComputeFn {
    let func = move |compute_ctx: ComputeCtx, _inputs: Vec<State>| -> State {
        State::Fr(Some(
            compute_ctx
                .msm_scalars
                .get(index)
                .expect("index out of range")
                .clone(),
        ))
    };
    Box::new(Arc::new(func))
}

mod tests {
    use crate::autochunker::{primitve_functions::ComputeCtx, proof::RawProof};

    #[test_log::test]
    fn test_raw_proof_to_compute_ctx() {
        let raw_proof = RawProof::mock_proof();
        let _: ComputeCtx = raw_proof.into();
    }
}
