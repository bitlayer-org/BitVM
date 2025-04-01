use crate::autochunker::{intermediate_state::*, proof::RawProof};
use crate::bn254::ell_coeffs::{AffinePairing, BnAffinePairing};
use crate::bn254::fp254impl::Fp254Impl;
use crate::bn254::utils::fq_to_bits;
use crate::groth16::constants::LAMBDA;
use crate::groth16::offchain_checker::compute_c_wi;
use ark_bn254::{Fq, Fq6, Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, Field, One, PrimeField};
use core::ops::Neg;
use log::{debug, info, warn};
use num_bigint::BigUint;
use std::sync::Arc;

pub type ComputeFn = Box<Arc<dyn Fn(ComputeCtx, Vec<State>) -> State + Send + Sync + 'static>>;

#[derive(Debug, Clone)]
pub struct ComputeCtx {
    proof: RawProof,
    msm_points_from_pk: Vec<G1Affine>,
    msm_scalars: Vec<Fr>,
    vky0: G1Affine,
    p2: G1Affine,
    p4: G1Affine,
    c: Fq6,
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
        let (c, _) = compute_c_wi(f);
        let c_inv = c.inverse().unwrap();
        let result = f * (c_inv.pow(LAMBDA.to_u64_digits()));

        assert_eq!(result.c1, Fq6::ZERO);

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
            vky0: vky0,
            p2: p2,
            p4: p4,
            c: c.c1 / c.c0,
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
        debug!(
            "windows of mul table: {}, chunks of scalar {}: {:?}",
            (crate::bn254::fr::Fr::N_BITS as usize + window - 1) / window,
            index,
            scalar_chunks,
        );

        // doubled based + current windows' result
        let doubled_base = (base * Fr::from(1 << (chunk_index * window))).into_affine(); // (2^(w.i) P)
        let window_result = (doubled_base * Fr::from(scalar_chunks[chunk_index])).into_affine();

        State::G1(Some((compute_ctx.vky0 + window_result).into_affine()))
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
        debug!(
            "windows of mul table: {}, chunks of scalar {}: {:?}",
            (crate::bn254::fr::Fr::N_BITS as usize + window - 1) / window,
            index,
            scalar_chunks,
        );

        // doubled based + current windows' result
        let doubled_base =
            (base * Fr::from(BigUint::one() << (chunk_index * window))).into_affine(); // (2^(w.i) P)
        let window_result = (doubled_base * Fr::from(scalar_chunks[chunk_index])).into_affine();

        State::G1(Some((window_result + msm_acc).into_affine()))
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

pub fn scalar_valid() -> (ComputeFn, usize) {
    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        State::CheckValid(Some(true))
    };
    // TODO: check valid of scalar from script
    (Box::new(Arc::new(func)), 0)
}

// extract proof.c
pub fn extract_p2() -> ComputeFn {
    let func = move |compute_ctx: ComputeCtx, _inputs: Vec<State>| -> State {
        State::G1(Some(compute_ctx.p2.clone()))
    };
    Box::new(Arc::new(func))
}

// check validation of a G1 point
pub fn check_g1_point() -> (ComputeFn, usize) {
    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        State::CheckValid(Some(true))
    };
    // TODO: check valid of scalar from script
    (Box::new(Arc::new(func)), 0)
}

// for the optimization of line evaluation
pub fn tweak_point() -> (ComputeFn, usize) {
    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let point = inputs[0].get_g1();
        let tweak_point = G1 {
            x: -point.x / point.y,
            y: point.y.inverse().unwrap(),
            infinity: false,
        };
        State::G1(Some(compute_ctx.p2.clone()))
    };
    (Box::new(Arc::new(func)), 0)
}

// extrac proof.a
pub fn extract_p4() -> ComputeFn {
    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        State::G1(Some(compute_ctx.p4.clone()))
    };
    Box::new(Arc::new(func))
}

pub fn extract_c(idx: usize) -> ComputeFn {
    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        match idx {
            0 => State::Fq2(Some(compute_ctx.c.c0)),
            1 => State::Fq2(Some(compute_ctx.c.c1)),
            2 => State::Fq2(Some(compute_ctx.c.c2)),
            _ => panic!("index out of range"),
        }
    };
    Box::new(Arc::new(func))
}

pub fn neg_fq2() -> (ComputeFn, usize) {
    let func = move |compute_ctx: ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let fq2 = inputs[0].get_fq2();
        State::Fq2(Some(fq2.neg()))
    };
    (Box::new(Arc::new(func)), 0)
}

mod tests {
    use crate::autochunker::{primitve_functions::ComputeCtx, proof::RawProof};
    use ark_bn254::{Fq, Fq2, Fq6};
    use core::ops::Neg;
    use log::info;

    #[test_log::test]
    fn test_raw_proof_to_compute_ctx() {
        let raw_proof = RawProof::mock_proof();
        let _: ComputeCtx = raw_proof.into();
    }

    #[test_log::test]
    fn test_fq6_inverse() {
        let now = std::time::Instant::now();
        let c0 = Fq2::new(Fq::from(1), Fq::from(2));
        let c1 = Fq2::new(Fq::from(3), Fq::from(4));
        let c2 = Fq2::new(Fq::from(5), Fq::from(6));
        let fq6 = Fq6::new(c0.clone(), c1.clone(), c2.clone());
        let neg = fq6.neg();
        info!("neg: {:?}", neg);
        info!("c0, c1, c2: {:?}", (c0.neg(), c1.neg(), c2.neg()));
        assert_eq!(c0.neg(), neg.c0);
        assert_eq!(c1.neg(), neg.c1);
        assert_eq!(c2.neg(), neg.c2);
        info!("time elapsed: {:?}", now.elapsed());
    }
}
