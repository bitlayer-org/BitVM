use crate::autochunker::{compute_ctx::*, intermediate_state::*, proof::RawProof};
use crate::bn254::ell_coeffs::{AffinePairing, BnAffinePairing};
use crate::bn254::fp254impl::Fp254Impl;
use crate::bn254::utils::fq_to_bits;
use crate::groth16::constants::LAMBDA;
use crate::groth16::offchain_checker::compute_c_wi;
use ark_bn254::Fq6Config;
use ark_bn254::{Fq, Fq12, Fq2, Fq6, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::bn::BnConfig;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, Field, One, PrimeField};
use ark_ff::{Fp6Config, MontFp};
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
        State::G1(Some(tweak_point))
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

pub fn fq2_conjugate() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let mut fq2 = inputs[0].get_fq2();
        fq2.conjugate_in_place();
        State::Fq2(Some(fq2))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn fq2_frobinus_map(power: usize) -> (ComputeFn, ScriptFn) {
    assert!(power <= 3 && power >= 1, "power out of range: {}", power);
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let x = inputs[0].get_fq2();
        let y = x.frobenius_map(power);
        State::Fq2(Some(y))
    };
    (Box::new(func), placeholder_script_fn())
}

pub const BETA32: Fq2 = Fq2::new(
    MontFp!("3772000881919853776433695186713858239009073593817195771773381919316419345261"),
    MontFp!("2236595495967245188281701248203181795121068902605861227855261137820944008926"),
);
pub const BETA33: Fq2 = Fq2::new(
    MontFp!("19066677689644738377698246183563772429336693972053703295610958340458742082029"),
    MontFp!("18382399103927718843559375435273026243156067647398564021675359801612095278180"),
);
pub const BETA22: Fq2 = Fq2::new(
    MontFp!("21888242871839275220042445260109153167277707414472061641714758635765020556616"),
    MontFp!("0"),
);
pub const BETA12: Fq2 = ark_bn254::Config::TWIST_MUL_BY_Q_X;
pub const BETA13: Fq2 = ark_bn254::Config::TWIST_MUL_BY_Q_Y;

// compute q' = (q.x.conjugate()*beta_12, q.y.conjugate() * beta_13)
pub fn mul_by_char(r: G2Affine) -> G2Affine {
    let mut s = r;
    s.x.frobenius_map_in_place(1);
    s.x *= &BETA12;
    s.y.frobenius_map_in_place(1);
    s.y *= &BETA13;
    s
}

// compute q'' = (q.x * beta_22, q.y)
pub fn mul_by_2char_neg(r: G2Affine) -> G2Affine {
    let mut s = r;
    s.x *= &BETA22;
    s
}

// inputs
pub fn add_chord_line_x() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 3);
        let t4x = inputs[0].get_fq2();
        let q4x = inputs[1].get_fq2();
        let lambda = inputs[2].get_fq2();

        // t4x' = \lambda^2 - 2 \cdot t4x
        let t4x_new = lambda.square() - t4x - q4x;
        State::Fq2(Some(t4x_new))
    };

    (Box::new(func), placeholder_script_fn())
}

// the same with `double_tangent_line_y`
pub fn add_chord_line_y() -> (ComputeFn, ScriptFn) { double_tangent_line_y() }

// inputs t4x, lambda, v
pub fn double_tangent_line_y() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 3);
        let t4x_new = inputs[0].get_fq2();
        let lambda = inputs[1].get_fq2();
        let v = inputs[2].get_fq2();

        // t4y' = - (v + \lambda * t4x')
        let t4y_new = -(v + lambda * t4x_new);

        State::Fq2(Some(t4y_new))
    };

    (Box::new(func), placeholder_script_fn())
}

// inputs: t4x, lambda
pub fn double_tangent_line_x() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 2);
        let t4x = inputs[0].get_fq2();
        let lambda = inputs[1].get_fq2();

        // t4x' = \lambda^2 - 2 \cdot t4x
        let t4x_new = lambda.square() - Fq2::from(2) * t4x;
        State::Fq2(Some(t4x_new))
    };

    (Box::new(func), placeholder_script_fn())
}

// inputs: t4x, t4y, lambda, v
pub fn check_line_through_point(selector: Selector) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 4);
        let t4x = inputs[0].get_fq2();
        let t4y = inputs[1].get_fq2();
        let lambda = inputs[2].get_fq2();
        let v = inputs[3].get_fq2();

        debug!(
            "check_line_through_point selector: {:?}: t4x: {:?}, t4y: {:?}, lambda: {:?}, v: {:?}",
            selector, t4x, t4y, lambda, v
        );

        // check if t4y = t4x * lambda + v
        State::CheckValid(Some(t4y == t4x * lambda + v))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn check_slope_of_tangent_line() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 3);
        let t4x = inputs[0].get_fq2();
        let t4y = inputs[1].get_fq2();
        let lambda = inputs[2].get_fq2();

        // check if 3 * t4x^2 = 2 * y * lambda
        State::CheckValid(Some(
            Fq2::from(3) * t4x.square() == Fq2::from(2) * t4y * lambda,
        ))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn nonconstant_line_evaluate_c0(selector: Selector) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 2);
        let lambda = inputs[0].get_fq2();
        let p4 = inputs[1].get_g1();

        let mut c0 = lambda;
        c0.mul_assign_by_basefield(&p4.x().unwrap());

        debug!(
            "lambda: {:?}, p_point.x {:?} for selector {:?}",
            lambda,
            p4.x().unwrap(),
            selector
        );

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c0))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn nonconstant_line_evaluate_c1(selector: Selector) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 2);
        let v = inputs[0].get_fq2();
        let p4 = inputs[1].get_g1();

        let mut c1 = v.neg();
        c1.mul_assign_by_basefield(&p4.y().unwrap());

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c1))
    };
    (Box::new(func), placeholder_script_fn())
}

pub fn constant_line_eval_c0(
    selector: TPointSelector,
    is_neg: bool,
    is_double: bool,
) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let p_point = inputs[0].get_g1();

        let (lambda, _) = if is_double {
            double_line(compute_ctx, selector.clone())
        } else {
            add_line(compute_ctx, selector.clone(), is_neg)
        };

        debug!(
            "lambda: {:?}, p_point.x {:?} for selector {:?}",
            lambda,
            p_point.x().unwrap(),
            selector
        );

        let mut c0 = lambda;
        c0.mul_assign_by_basefield(&p_point.x().unwrap());

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c0))
    };
    (Box::new(func), placeholder_script_fn())
}
pub fn constant_line_eval_c1(
    selector: TPointSelector,
    is_neg: bool,
    is_double: bool,
) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let p_point = inputs[0].get_g1();

        let (_, v) = if is_double {
            double_line(compute_ctx, selector.clone())
        } else {
            add_line(compute_ctx, selector.clone(), is_neg)
        };

        debug!(
            "-bias: {:?}, p_point.x {:?} for selector {:?}",
            v.neg(),
            p_point.y().unwrap(),
            selector
        );

        let mut c1 = v.neg();
        c1.mul_assign_by_basefield(&p_point.y().unwrap());

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c1))
    };
    (Box::new(func), placeholder_script_fn())
}

mod tests {
    use crate::autochunker::{primitve_functions::ComputeCtx, proof::RawProof};
    use ark_bn254::{Fq, Fq2, Fq6};
    use core::ops::Neg;
    use log::info;

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
