use crate::autochunker::{compute_ctx::*, intermediate_state::*, proof::RawProof};
use crate::bn254::ell_coeffs::{AffinePairing, BnAffinePairing};
use crate::bn254::fp254impl::Fp254Impl;
use crate::bn254::utils::fq_to_bits;
use crate::groth16::constants::LAMBDA;
use crate::groth16::offchain_checker::compute_c_wi;
use ark_bn254::Fq6Config;
use ark_bn254::{Fq, Fq12, Fq2, Fq6, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Fp6Config;
use ark_ff::{AdditiveGroup, Field, One, PrimeField};
use bitcoin_script::{script, Script};
use core::ops::Neg;
use log::{debug, error, info, warn};
use num_bigint::BigUint;
use std::sync::Arc;

pub fn placeholder_script_fn() -> ScriptFn {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> (Script, Vec<Vec<u8>>) {
        assert_eq!(inputs.len(), 1);
        let script = script! {};
        let data = vec![];
        (script, data)
    };
    Box::new(func)
}

/// window multiplication
pub fn msm_initial(window: usize) -> (ComputeFn, ScriptFn) {
    // the first step of msm
    let (index, chunk_index) = (0, 0);

    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
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

    (Box::new(func), placeholder_script_fn())
}

pub fn windows_of_mul_table(window: usize) -> usize {
    let tables = (crate::bn254::fr::Fr::N_BITS as usize + window - 1) / window;
    info!("windows of mul table: {}", tables);
    tables
}

pub fn msm_steps(index: usize, chunk_index: usize, window: usize) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
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

    (Box::new(func), placeholder_script_fn())
}

pub fn extract_scalar(index: usize) -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, _inputs: Vec<State>| -> State {
        State::Fr(Some(
            compute_ctx
                .msm_scalars
                .get(index)
                .expect("index out of range")
                .clone(),
        ))
    };
    Box::new(func)
}

pub fn scalar_valid() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        State::CheckValid(Some(true))
    };
    // TODO: check valid of scalar from script
    (Box::new(func), placeholder_script_fn())
}

// check validation of a G1 point
pub fn check_g1_point() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        State::CheckValid(Some(true))
    };
    // TODO: check valid of scalar from script
    (Box::new(func), placeholder_script_fn())
}

// for the optimization of line evaluation
pub fn tweak_point() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let point = inputs[0].get_g1();
        let tweak_point = G1 {
            x: -point.x / point.y,
            y: point.y.inverse().unwrap(),
            infinity: false,
        };
        State::G1(Some(compute_ctx.p2.clone()))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn neg_fq2() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let fq2 = inputs[0].get_fq2();
        State::Fq2(Some(fq2.neg()))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn fq2_mul_lc4() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 4);
            let a = inputs[0].get_fq2();
            let b = inputs[1].get_fq2();
            let c = inputs[2].get_fq2();
            let d = inputs[3].get_fq2();
            let result = a * b + c * d;
            State::Fq2(Some(result))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_mul_nonresidue() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 1);
            let a = inputs[0].get_fq2();
            let b = a * Fq6Config::NONRESIDUE;
            State::Fq2(Some(b))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_plus_one() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 1);
            let a = inputs[0].get_fq2();
            let b = a + Fq2::from(1);
            State::Fq2(Some(b))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_add() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 2);
            let a = inputs[0].get_fq2();
            let b = inputs[1].get_fq2();
            let c = a + b;
            State::Fq2(Some(c))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_mul() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 2);
            let a = inputs[0].get_fq2();
            let b = inputs[1].get_fq2();
            let c = a * b;
            State::Fq2(Some(c))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_sub() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 2);
            let a = inputs[0].get_fq2();
            let b = inputs[1].get_fq2();
            let c = a - b;
            State::Fq2(Some(c))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_sub2() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 3);
            let a = inputs[0].get_fq2();
            let b = inputs[1].get_fq2();
            let c = inputs[2].get_fq2();
            let d = a - b - c;
            State::Fq2(Some(d))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_neg() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 1);
            let a = inputs[0].get_fq2();
            let b = a.neg();
            State::Fq2(Some(b))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_div6() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert!(inputs.len() == 1);
        let c0 = inputs[0].get_fq2();
        let c0_tweak = c0 / Fq2::from(6);
        State::Fq2(Some(c0_tweak))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn fq2_div2() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert!(inputs.len() == 1);
        let c0 = inputs[0].get_fq2();
        let c0_tweak = c0 / Fq2::from(2);
        State::Fq2(Some(c0_tweak))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn check_fq2_equal() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 2);
            let a = inputs[0].get_fq2();
            let b = inputs[1].get_fq2();
            State::CheckValid(Some(a == b))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_mul_by_constant(x: Fq2) -> (ComputeFn, ScriptFn) {
    (
        Box::new(move |_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 1);
            let a = inputs[0].get_fq2();
            let b = a * x;
            State::Fq2(Some(b))
        }),
        placeholder_script_fn(),
    )
}

pub fn fq2_mul_by_integer(i: i32) -> (ComputeFn, ScriptFn) {
    assert!(i < 10, "mul_by_constant, {} too large", i);
    assert!(i > -10, "mul_by_constant, {} too small", i);
    let x = Fq2::from(i);
    fq2_mul_by_constant(x)
}

pub fn fq2_square() -> (ComputeFn, ScriptFn) {
    (
        Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
            assert!(inputs.len() == 1);
            let a = inputs[0].get_fq2();
            let b = a.square();
            State::Fq2(Some(b))
        }),
        placeholder_script_fn(),
    )
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
