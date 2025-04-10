use super::{computation_graph::*, intermediate_state::*, primitve_functions::*};
use crate::{define_input, define_overide_script, define_script};
use ark_bn254::{Fq12, Fq2, Fq6, Fq6Config, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, Fp6Config};
use serde::de;
use std::ops::Neg;

/// three input each which is fq2
pub fn new_square_fq6(ctx: &mut GraphContext, inputs: [&BitVMNode; 3]) -> [BitVMNode; 3] {
    let (a0, a1, a2) = (inputs[0], inputs[1], inputs[2]);

    // s0 = a0^2
    define_script!(
        ctx,
        s0,
        Fq2,
        [a0],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| -> State {
                assert!(inputs.len() == 1);
                let a0 = inputs[0].get_fq2();
                let s0 = a0.square();
                State::Fq2(Some(s0))
            }),
            placeholder_script_fn()
        )
    );

    // s1 = (a_0 + a_1 + a_2)^2
    define_script!(
        ctx,
        s1,
        Fq2,
        [a0, a1, a2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 3);
                let a0 = inputs[0].get_fq2();
                let a1 = inputs[1].get_fq2();
                let a2 = inputs[2].get_fq2();
                let s1 = (a0 + a1 + a2).square();
                State::Fq2(Some(s1))
            }),
            placeholder_script_fn()
        )
    );

    // s2 = (a_0 - a_1 + a_2)^2
    define_script!(
        ctx,
        s2,
        Fq2,
        [a0, a1, a2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 3);
                let a0 = inputs[0].get_fq2();
                let a1 = inputs[1].get_fq2();
                let a2 = inputs[2].get_fq2();
                let s2 = (a0 - a1 + a2).square();
                State::Fq2(Some(s2))
            }),
            placeholder_script_fn()
        )
    );

    // s3 = 2 \cdot a_1 \cdot a_2
    define_script!(
        ctx,
        s3,
        Fq2,
        [a1, a2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 2);
                let a1 = inputs[0].get_fq2();
                let a2 = inputs[1].get_fq2();
                let s3 = a1 * a2 * Fq2::from(2);
                State::Fq2(Some(s3))
            }),
            placeholder_script_fn()
        )
    );

    // s4 = a_2^2
    define_script!(
        ctx,
        s4,
        Fq2,
        [a2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 1);
                let a2 = inputs[0].get_fq2();
                let s4 = a2.square();
                State::Fq2(Some(s4))
            }),
            placeholder_script_fn()
        )
    );

    // t4 = (s1 + s2) / 2
    define_script!(
        ctx,
        t4,
        Fq2,
        [s1, s2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 2);
                let s1 = inputs[0].get_fq2();
                let s2 = inputs[1].get_fq2();
                let t4 = (s1 + s2) / Fq2::from(2);
                State::Fq2(Some(t4))
            }),
            placeholder_script_fn()
        )
    );

    // c0 = s0 + \beta \cdot s_3
    define_script!(
        ctx,
        c0,
        Fq2,
        [s0, s3],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 2);
                let s0 = inputs[0].get_fq2();
                let s3 = inputs[1].get_fq2();
                let c0 = s0 + s3 * Fq6Config::NONRESIDUE;
                State::Fq2(Some(c0))
            }),
            placeholder_script_fn()
        )
    );

    // c1 = s1 - s3 - t1 + \beta s4
    define_script!(
        ctx,
        c1,
        Fq2,
        [s1, s3, t4, s4],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 4);
                let s1 = inputs[0].get_fq2();
                let s3 = inputs[1].get_fq2();
                let t4 = inputs[2].get_fq2();
                let s4 = inputs[3].get_fq2();
                let c1 = s1 - s3 - t4 + s4 * Fq6Config::NONRESIDUE;
                State::Fq2(Some(c1))
            }),
            placeholder_script_fn()
        )
    );

    // c2 = t1 - s0 - s4
    define_script!(
        ctx,
        c2,
        Fq2,
        [t4, s0, s4],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 3);
                let t4 = inputs[0].get_fq2();
                let s0 = inputs[1].get_fq2();
                let s4 = inputs[2].get_fq2();
                let c2 = t4 - s0 - s4;
                State::Fq2(Some(c2))
            }),
            placeholder_script_fn()
        )
    );

    [c0.clone(), c1.clone(), c2.clone()]
}

fn new_mul_fq6(ctx: &mut GraphContext, a: [&BitVMNode; 3], b: [&BitVMNode; 3]) -> [BitVMNode; 3] {
    let (a0, a1, a2) = (a[0], a[1], a[2]);
    let (b0, b1, b2) = (b[0], b[1], b[2]);
    // v0 = a0 * b0
    define_script!(
        ctx,
        v0,
        Fq2,
        [a0, b0],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 2);
                let a0 = inputs[0].get_fq2();
                let b0 = inputs[1].get_fq2();
                let v0 = a0 * b0;
                State::Fq2(Some(v0))
            }),
            placeholder_script_fn()
        )
    );

    // v1 = (a0 + a1 + a2) * (b0 + b1 + b2)
    define_script!(
        ctx,
        v1,
        Fq2,
        [a0, a1, a2, b0, b1, b2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 6);
                let a0 = inputs[0].get_fq2();
                let a1 = inputs[1].get_fq2();
                let a2 = inputs[2].get_fq2();
                let b0 = inputs[3].get_fq2();
                let b1 = inputs[4].get_fq2();
                let b2 = inputs[5].get_fq2();
                let v1 = (a0 + a1 + a2) * (b0 + b1 + b2);
                State::Fq2(Some(v1))
            }),
            placeholder_script_fn()
        )
    );

    // v2 = (a0 - a1 + a2) * (b0 - b1 + b2)
    define_script!(
        ctx,
        v2,
        Fq2,
        [a0, a1, a2, b0, b1, b2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 6);
                let a0 = inputs[0].get_fq2();
                let a1 = inputs[1].get_fq2();
                let a2 = inputs[2].get_fq2();
                let b0 = inputs[3].get_fq2();
                let b1 = inputs[4].get_fq2();
                let b2 = inputs[5].get_fq2();
                let v2 = (a0 - a1 + a2) * (b0 - b1 + b2);
                State::Fq2(Some(v2))
            }),
            placeholder_script_fn()
        )
    );

    // v3 = (a0 + 2a1 + 4a2) * (b0 + 2b1 + 4b2)
    define_script!(
        ctx,
        v3,
        Fq2,
        [a0, a1, a2, b0, b1, b2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 6);
                let a0 = inputs[0].get_fq2();
                let a1 = inputs[1].get_fq2();
                let a2 = inputs[2].get_fq2();
                let b0 = inputs[3].get_fq2();
                let b1 = inputs[4].get_fq2();
                let b2 = inputs[5].get_fq2();
                let v3 = (a0 + Fq2::from(2) * a1 + Fq2::from(4) * a2)
                    * (b0 + Fq2::from(2) * b1 + Fq2::from(4) * b2);
                State::Fq2(Some(v3))
            }),
            placeholder_script_fn()
        )
    );

    // v4 = a2 * b2
    define_script!(
        ctx,
        v4,
        Fq2,
        [a2, b2],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 2);
                let a2 = inputs[0].get_fq2();
                let b2 = inputs[1].get_fq2();
                let v4 = a2 * b2;
                State::Fq2(Some(v4))
            }),
            placeholder_script_fn()
        )
    );

    // x = 3v0 - 3v1 - v2 + v3 - 12v4
    define_script!(
        ctx,
        x,
        Fq2,
        [v0, v1, v2, v3, v4],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 5);
                let v0 = inputs[0].get_fq2();
                let v1 = inputs[1].get_fq2();
                let v2 = inputs[2].get_fq2();
                let v3 = inputs[3].get_fq2();
                let v4 = inputs[4].get_fq2();
                let x = v0 * Fq2::from(3) - v1 * Fq2::from(3) - v2 + v3 - v4 * Fq2::from(12);
                State::Fq2(Some(x))
            }),
            placeholder_script_fn()
        )
    );

    // c0 = 6v0 + \beta x
    define_script!(ctx, x_tweak, Fq2, [x], mul_nonresidue());
    define_script!(
        ctx,
        c0,
        Fq2,
        [v0, x_tweak],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 2);
                let v0 = inputs[0].get_fq2();
                let x_tweak = inputs[1].get_fq2();
                let c0 = v0 * Fq2::from(6) + x_tweak;
                State::Fq2(Some(c0))
            }),
            placeholder_script_fn()
        )
    );

    // y = -3v0 + 6v1 - 2v2 - v3 + 12v4
    define_script!(
        ctx,
        y,
        Fq2,
        [v0, v1, v2, v3, v4],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 5);
                let v0 = inputs[0].get_fq2();
                let v1 = inputs[1].get_fq2();
                let v2 = inputs[2].get_fq2();
                let v3 = inputs[3].get_fq2();
                let v4 = inputs[4].get_fq2();
                let y = -v0 * Fq2::from(3) + v1 * Fq2::from(6) - v2 * Fq2::from(2) - v3
                    + v4 * Fq2::from(12);
                State::Fq2(Some(y))
            }),
            placeholder_script_fn()
        )
    );

    // c1 = y + \beta 6v4
    define_script!(
        ctx,
        v4_times_6,
        Fq2,
        [v4],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 1);
                let v4 = inputs[0].get_fq2();
                let c1 = v4 * Fq2::from(6);
                State::Fq2(Some(c1))
            }),
            placeholder_script_fn()
        )
    );
    define_script!(ctx, v4_tweak, Fq2, [v4_times_6], mul_nonresidue());
    define_script!(ctx, c1, Fq2, [y, v4_tweak], fq2_add());

    // c2 = 3v1 - 6v0 + 3v2 - 6v4
    define_script!(
        ctx,
        c2,
        Fq2,
        [v0, v1, v2, v4],
        (
            Box::new(|_: &mut ComputeCtx, inputs: Vec<State>| {
                assert!(inputs.len() == 4);
                let v0 = inputs[0].get_fq2();
                let v1 = inputs[1].get_fq2();
                let v2 = inputs[2].get_fq2();
                let v4 = inputs[3].get_fq2();
                let c2 =
                    v1 * Fq2::from(3) - v0 * Fq2::from(6) + v2 * Fq2::from(3) - v4 * Fq2::from(6);
                State::Fq2(Some(c2))
            }),
            placeholder_script_fn()
        )
    );

    // c0/6, c1/6, c2/6
    define_script!(ctx, c0_tweak, Fq2, [c0], fq2_div6());
    define_script!(ctx, c1_tweak, Fq2, [c1], fq2_div6());
    define_script!(ctx, c2_tweak, Fq2, [c2], fq2_div6());

    [c0_tweak, c1_tweak, c2_tweak]
}

fn fq2_div6() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert!(inputs.len() == 1);
        let c0 = inputs[0].get_fq2();
        let c0_tweak = c0 / Fq2::from(6);
        State::Fq2(Some(c0_tweak))
    };
    (Box::new(func), placeholder_script_fn())
}

// the BN254 curve is represented by Y^2 = X^3 + aX + b, where b = 3 and a = 0
// For D-type twist (BN254), y^2 = x^3 + b / w^6
// mapping from BN254 to twisted-BN254: x -> x / w and y -> y / w^3
// mapping from wisted-BN254 to BN254: x -> x \cdot w^2 and y -> y \cdot w^3
//
// for a point (x_0, y_0) in twisted-BN254, (x_0 w^2, y_0 w^3) the tangent line is y = \lambda x + v
// first define the tagent line: y = \lambda x + v
// (1) \lambda = (3(x_0 w^2)^2) / 2(y_0 w^3) = (3x_0^2)/2y_0 \cdot w
// (2) v = y_0 w^3 - \lambda x_0 w^2 = y_0 -  ((3x_0^2)/2y_0) x_0 \cdot w^3
// where \lambda is the slop and v is bias
//
// use \lambda = \lambda / w, v = v / w^3 to represent the Fq2 parts of coefficients.
//
// since w^6 = u+9, the evaluation on G1 point (x_p, y_p) would be
// (y_p - \lambda x_p - v) = 1 / y_p \cdot (1 + \lambda x_p' + (-v) y_p')
// because 1 / y_p is F_p element, can be elimnated by the multiplication
//                         = 1 + \lambda x_p' + (-v) y_p' = F_{q^6}(1) + (F_{a^6}(\lamdba x_p' + (-v)y_p' \cdot w^2 + 0 \cdot w^4)) \cdot w
//
// function outputs: t4x, t4y, evaluate_c0, evaluate_c1
pub fn double_by_tangent_line(
    ctx: &mut GraphContext,
    t4x: &BitVMNode,
    t4y: &BitVMNode,
    p4: &BitVMNode,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    // define lambda
    define_input!(
        ctx,
        lambda,
        Fq2,
        Box::new(|ctx: &mut ComputeCtx, _: Vec<State>| {
            assert!(ctx.t4.xy().is_some());
            let (t4x, t4y) = ctx.t4.xy().unwrap();
            let lambda = (Fq2::from(3) * t4x.square()) / (Fq2::from(2) * t4y);
            State::Fq2(Some(lambda))
        })
    );

    // define v
    define_input!(
        ctx,
        v,
        Fq2,
        Box::new(|ctx: &mut ComputeCtx, _: Vec<State>| {
            assert!(ctx.t4.xy().is_some());
            let (t4x, t4y) = ctx.t4.xy().unwrap();
            let lambda = (Fq2::from(3) * t4x.square()) / (Fq2::from(2) * t4y);
            let v = t4y - lambda * t4x;
            State::Fq2(Some(v))
        })
    );

    // t4y =?= t4x \cdot \lambda + v
    define_script!(
        ctx,
        _check_line_through_point,
        CheckValid,
        [t4x, t4y, lambda, v],
        check_line_through_point()
    );

    // 3 \cdot t4x^2 \cdot \lambda = 2 \cdot y^2
    define_script!(
        ctx,
        _check_slope_of_line,
        CheckValid,
        [t4x, t4y, lambda],
        check_slope_of_tangent_line()
    );

    // t4x' = \lambda^2 - 2 \cdot t4x
    define_script!(
        ctx,
        updated_t4x,
        Fq2,
        [t4x, lambda],
        double_tangent_line_x()
    );

    // t4y' = - (v + \lambda * t4x')
    define_script!(
        ctx,
        updated_t4y,
        Fq2,
        [t4x, lambda, v],
        double_tangent_line_y()
    );

    // evaluate the point by the line (divisor)
    define_script!(ctx, c0, Fq2, [lambda, p4], nonconstant_line_evaluate_c0());
    define_script!(ctx, c1, Fq2, [v, p4], nonconstant_line_evaluate_c1());

    (updated_t4x, updated_t4y, c0, c1)
}

// inputs t4x, lambda, v
fn double_tangent_line_y() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 3);
        let t4x = inputs[0].get_fq2();
        let lambda = inputs[1].get_fq2();
        let v = inputs[2].get_fq2();

        // t4y' = - (v + \lambda * t4x')
        let t4x_new = lambda.square() - Fq2::from(2) * t4x;
        let t4y_new = -(v + lambda * t4x);
        compute_ctx.t4 = G2Affine {
            x: t4x_new,
            y: t4y_new,
            infinity: false,
        };
        State::Fq2(Some(t4y_new))
    };

    (Box::new(func), placeholder_script_fn())
}

// inputs: t4x, lambda
fn double_tangent_line_x() -> (ComputeFn, ScriptFn) {
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
fn check_line_through_point() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 4);
        let t4x = inputs[0].get_fq2();
        let t4y = inputs[1].get_fq2();
        let lambda = inputs[2].get_fq2();
        let v = inputs[3].get_fq2();

        // check if t4y = t4x * lambda + v
        State::CheckValid(Some(t4y == t4x * lambda + v))
    };
    (Box::new(func), placeholder_script_fn())
}

fn check_slope_of_tangent_line() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 3);
        let t4x = inputs[0].get_fq2();
        let t4y = inputs[1].get_fq2();
        let lambda = inputs[2].get_fq2();

        // check if 3 * t4x^2 * lambda = 2 * y^2
        State::CheckValid(Some(
            Fq2::from(3) * t4x.square() * lambda == Fq2::from(2) * t4y.square(),
        ))
    };
    (Box::new(func), placeholder_script_fn())
}

fn nonconstant_line_evaluate_c0() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 2);
        let lambda = inputs[0].get_fq2();
        let p4 = inputs[1].get_g1();

        let mut c0 = lambda;
        c0.mul_assign_by_basefield(&p4.x().unwrap());

        // update c0 of ctx.evaluate_p4
        compute_ctx.evaluate_p4 = Some(Fq6::new(c0, Fq2::from(0), Fq2::from(0)));

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c0))
    };
    (Box::new(func), placeholder_script_fn())
}

fn nonconstant_line_evaluate_c1() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 2);
        let v = inputs[0].get_fq2();
        let p4 = inputs[1].get_g1();

        let mut c1 = v.neg();
        c1.mul_assign_by_basefield(&p4.y().unwrap());

        // update c1 of ctx.evaluate_p4
        compute_ctx.evaluate_p4 = Some(Fq6::new(
            compute_ctx.evaluate_p4.unwrap().c0,
            c1,
            Fq2::from(0),
        ));

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c1))
    };
    (Box::new(func), placeholder_script_fn())
}

// outputs [lambda, v]
fn constant_line_compute(
    compute_ctx: &ComputeCtx,
    t3_or_t2: bool,
    is_double: bool,
    is_neg_bit: bool,
) -> (Fq2, Fq2, G2Affine) {
    // select t_point
    let (t_point, q_point) = if t3_or_t2 {
        (compute_ctx.t3, compute_ctx.q3)
    } else {
        (compute_ctx.t2, compute_ctx.q2)
    };

    // select is_neg_bit
    let q_point = if is_neg_bit { q_point.neg() } else { q_point };

    // select is_double
    let lambda = if is_double {
        (t_point.x.square() + t_point.x.square() + t_point.x.square()) / (t_point.y + t_point.y)
    } else {
        (t_point.y - q_point.y) / (t_point.x - q_point.x)
    };

    // update t_point
    let new_t_point = if is_double {
        t_point + t_point
    } else if is_neg_bit {
        t_point - q_point
    } else {
        t_point + q_point
    };

    let v = t_point.y - lambda * t_point.x;

    (lambda, v, new_t_point.into_affine())
}

// t3_or_t2: true means t3, false means t2
// is_double: true means double point, false means add point
// is_neg_bit: true means negation, false means no negation
pub const evalute_t3: bool = true;
pub const evalute_t2: bool = false;
pub const use_double: bool = true;
pub const use_add: bool = false;
pub const use_neg: bool = true;
pub const use_pos: bool = false;
pub fn constant_line_evaluate_c0(
    t3_or_t2: bool,
    is_double: bool,
    is_neg_bit: bool,
) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let p_point = inputs[0].get_g1();

        let (lambda, _, _) = constant_line_compute(compute_ctx, t3_or_t2, is_double, is_neg_bit);

        let mut c0 = lambda;
        c0.mul_assign_by_basefield(&p_point.x().unwrap());

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c0))
    };
    (Box::new(func), placeholder_script_fn())
}
pub fn constant_line_evaluate_c1(
    t3_or_t2: bool,
    is_double: bool,
    is_neg_bit: bool,
) -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let p_point = inputs[0].get_g1();

        let (lambda, v, new_t_point) =
            constant_line_compute(compute_ctx, t3_or_t2, is_double, is_neg_bit);

        let mut c0 = lambda;
        c0.mul_assign_by_basefield(&p_point.x().unwrap());
        let mut c1 = v.neg();
        c1.mul_assign_by_basefield(&p_point.y().unwrap());

        // update t point and point evaluate
        if t3_or_t2 {
            compute_ctx.t3 = new_t_point;
            compute_ctx.evaluate_p3 = Some(Fq6::new(c0, c1, Fq2::from(0)));
        } else {
            compute_ctx.t2 = new_t_point;
            compute_ctx.evaluate_p2 = Some(Fq6::new(c0, c1, Fq2::from(0)));
        }

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c1))
    };
    (Box::new(func), placeholder_script_fn())
}

// outputs: t3_c0, t3_c1, t2_c0, t2_c1
pub fn evaluate_t2_and_t3(
    ctx: &mut GraphContext,
    p3_tweak: &BitVMNode,
    p2_tweak: &BitVMNode,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    // update t3 by tagent line
    define_script!(
        ctx,
        t3_c0,
        Fq2,
        [p3_tweak],
        constant_line_evaluate_c0(evalute_t3, use_double, use_neg)
    );

    define_script!(
        ctx,
        t3_c1,
        Fq2,
        [p3_tweak],
        constant_line_evaluate_c1(evalute_t3, use_double, use_neg)
    );

    // update t2 by tagent line
    define_script!(
        ctx,
        t2_c0,
        Fq2,
        [p2_tweak],
        constant_line_evaluate_c0(evalute_t2, use_double, use_neg)
    );
    define_script!(
        ctx,
        t2_c1,
        Fq2,
        [p2_tweak],
        constant_line_evaluate_c1(evalute_t2, use_double, use_neg)
    );

    (t3_c0, t3_c1, t2_c0, t2_c1)
}

// line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
// equals
// [1 + (t4_c0, t4_c1, 0) J] * [1 + (t3_c0, t3_c1, 0) J] * [1 + (t2_c0, t2_c1, 0) J]
fn line_evaluate_multiplication(
    ctx: &mut GraphContext,
    t4_c0: &BitVMNode,
    t4_c1: &BitVMNode,
    t3_c0: &BitVMNode,
    t3_c1: &BitVMNode,
    t2_c0: &BitVMNode,
    t2_c1: &BitVMNode,
) -> (BitVMNode, BitVMNode, BitVMNode) {
    // step 1:
    // [1 + (t4_c0, t4_c1, 0) J] * [1 + (t3_c0, t3_c1, 0) J] ->
    // (1 + (s0, s1, s2) J^2)+ (d0, d1, 0) J ->
    // (m0, m1, m2) + (d0, d1, 0) J
    //
    // d0 = t3_c0 + t3_c1
    define_script!(ctx, d0, Fq2, [t3_c0, t3_c1], fq2_add());
    // d1 = t4_c0 + t4_c1
    define_script!(ctx, d1, Fq2, [t4_c0, t4_c1], fq2_add());
    // s0 = t4_c0 * t3_c0
    define_script!(ctx, s0, Fq2, [t4_c0, t3_c0], fq2_mul());
    // s2 = t4_c1 * t3_c1
    define_script!(ctx, s2, Fq2, [t4_c1, t3_c1], fq2_mul());
    // [b]inomial = (t3_c0 + t3_c1) * (t4_c0 + t4_c1)
    define_script!(ctx, b, Fq2, [d0, d1], fq2_mul());
    // s1 = b - s0 - s2
    define_script!(ctx, s1, Fq2, [b, s0, s2], fq2_sub2());
    // (m0, m1, m2) = (s0, s1, s2) * mul_fq6_by_nonresidue + 1
    //              = (s2 * (9+u), s0, s1) + 1
    //              = (s2 * (9+u) + 1, s0, s1)
    define_script!(ctx, s2_tweak, Fq2, [s2], mul_nonresidue());
    define_script!(ctx, m0, Fq2, [s2_tweak], fq2_plus_one());
    let (m1, m2) = (s0, s1);
    //
    // step 2:
    // [ (m0, m1, m2) + (d0, d1, 0) J ] * [1 + (t2_c0, t2_c1, 0) J] ->
    // (1 + (e0, e1, e2) J^2) + ((d0, d1, 0) + (t2_c0, t2_c1, 0) * (m0, m1, m2) ) J ->
    // ((m0, m1, m2) + (h0, h1, h2)) +  ((d0, d1, 0) + (t2_c0, t2_c1, 0) * (m0, m1, m2) ) J
    //
    // d_sum = d0 + d1
    define_script!(ctx, d_sum, Fq2, [d0, d1], fq2_add());
    // t2_sum = t2_c0 + t2_c1
    define_script!(ctx, t2_sum, Fq2, [t2_c0, t2_c1], fq2_add());
    // [bi]nomial = (d0 + d1) * (t2_c0 + t2_c1)
    define_script!(ctx, bi, Fq2, [t2_sum, d_sum], fq2_mul());
    // e0 = t2_c0 * d0
    define_script!(ctx, e0, Fq2, [t2_c0, d0], fq2_mul());
    // e2 = t2_c1 * d1
    define_script!(ctx, e2, Fq2, [t2_c1, d1], fq2_mul());
    // e1 = bi - e0 - e2
    define_script!(ctx, e1, Fq2, [bi, e0, e2], fq2_sub2());
    // (h0, h1, h2) = (e0, e1, e2) * mul_fq6_by_nonresidue + 1
    //             = (e2 * (9+u), e0, e1) + 1
    //             = (e2 * (9+u) + 1, e0, e1)
    define_script!(ctx, e2_tweak, Fq2, [e2], mul_nonresidue());
    define_script!(ctx, h0, Fq2, [e2_tweak], fq2_plus_one());
    let (h1, h2) = (e0, e1);
    //
    // step 3:
    // ((m0, m1, m2) + (h0, h1, h2)) +  ((d0, d1, 0) + (t2_c0, t2_c1, 0) * (m0, m1, m2) ) J ->
    // (mh0, mh1, mh2) + ((d0, d1, 0) + (k0, k1, k2)) J ->
    // (mh0, mh1, mh2) + (dk0, dk1, dk2) J
    //
    define_script!(ctx, mh0, Fq2, [m0, h0], fq2_add());
    define_script!(ctx, mh1, Fq2, [m1, h1], fq2_add());
    define_script!(ctx, mh2, Fq2, [m2, h2], fq2_add());
    // k0 = t2_c0 * m0 + t2_c1 * m2 * mul_fq6_by_nonresidue
    //    = t2_c0 * m0 + t2_c1 * m2_tweak
    define_script!(ctx, m2_tweak, Fq2, [m2], mul_nonresidue());
    define_script!(ctx, k0, Fq2, [t2_c0, m0, t2_c1, m2_tweak], fq2_mul_lc4());
    // k1 = t2_c0 * m1 + t2_c1 * m0
    define_script!(ctx, k1, Fq2, [t2_c0, m1, t2_c1, m0], fq2_mul_lc4());
    // k2 = t2_c0 * m2 + t2_c1 * m1
    define_script!(ctx, k2, Fq2, [t2_c0, m2, t2_c1, m1], fq2_mul_lc4());
    // (dk0, dk1, dk2) = (d0, d1, 0) + (k0, k1, k2)
    define_script!(ctx, dk0, Fq2, [d0, k0], fq2_add());
    define_script!(ctx, dk1, Fq2, [d1, k1], fq2_add());
    let dk2 = k2;
    //
    // step 4:
    // (mh0, mh1, mh2) + (dk0, dk1, dk2) J ->
    // 1 + (dk0, dk1, dk2) * 1 / (mh0, mh1, mh2) J ->
    // 1 + (g0, g1, g2) J, and check (g0, g1, g2) * (mh0, mh1, mh2) == (dk0, dk1, dk2)
    //
    define_input!(ctx, g0, Fq2, extract_line_evaluation_g(0));
    define_input!(ctx, g1, Fq2, extract_line_evaluation_g(1));
    define_input!(ctx, g2, Fq2, extract_line_evaluation_g(2));
    //
    // check if (g0, g1, g2) * (mh0, mh1, mh2) == (dk0, dk1, dk2)
    let [x0, x1, x2] = new_mul_fq6(ctx, [&g0, &g1, &g2], [&mh0, &mh1, &mh2]);
    define_script!(ctx, _check_mul_x0, CheckValid, [x0, dk0], check_fq2_equal());
    define_script!(ctx, _check_mul_x1, CheckValid, [x1, dk1], check_fq2_equal());
    define_script!(ctx, _check_mul_x2, CheckValid, [x2, dk2], check_fq2_equal());

    (g0, g1, g2)
}

#[cfg(test)]
mod tests {
    use crate::autochunker::computation_graph::{
        compute_states, new_input, BitVMNode, GraphContext,
    };
    use crate::autochunker::functions::{new_mul_fq6, new_square_fq6};
    use crate::autochunker::intermediate_state::State;
    use crate::autochunker::primitve_functions::ComputeCtx;
    use crate::autochunker::proof::RawProof;
    use crate::{define_input, define_overide_script, define_script};
    use ark_bn254::{Fq2, Fq6, Fq6Config};
    use ark_ff::Field;
    use ark_ff::Fp6Config;
    use log::{debug, info};

    fn new_fq2_1(ctx: &mut GraphContext) -> BitVMNode {
        define_input!(
            ctx,
            _o,
            Fq2,
            Box::new(|_: &mut ComputeCtx, _: Vec<State>| State::Fq2(Some(Fq2::from(1))))
        );
        _o
    }

    fn get_state(ctx: &GraphContext, name: &str) -> State {
        let lock_guard = ctx.graph.lock().unwrap();
        let node = lock_guard.get_node(name.to_string()).unwrap();
        node.attributes.clone().unwrap().state
    }

    #[test_log::test]
    fn test_square_fq6() {
        let mut ctx = GraphContext::new("test");
        let a0 = new_fq2_1(&mut ctx.inner_context("a0"));
        let a1 = new_fq2_1(&mut ctx.inner_context("a1"));
        let a2 = new_fq2_1(&mut ctx.inner_context("a2"));
        let [c0, c1, c2] = new_square_fq6(&mut ctx, [&a0, &a1, &a2]);
        // compute states
        let mut compute_ctx = RawProof::mock_proof().into();
        compute_states(&ctx, &mut compute_ctx);
        // check result
        let lock_guard = ctx.graph.lock().unwrap();
        let a = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
        let c = a.square();
        for (idx, (node, cx)) in vec![c0, c1, c2]
            .into_iter()
            .zip(vec![c.c0, c.c1, c.c2].into_iter())
            .enumerate()
        {
            let node = lock_guard.get_node(node.name.clone()).unwrap();
            let value = node.attributes.clone().unwrap().state.get_fq2();
            info!("c{}: {:?}", idx, value);
            assert_eq!(value, cx);
        }
    }

    #[test_log::test]
    fn test_mul_fq6() {
        let mut ctx = GraphContext::new("test");
        let a0 = new_fq2_1(&mut ctx.inner_context("a0"));
        let a1 = new_fq2_1(&mut ctx.inner_context("a1"));
        let a2 = new_fq2_1(&mut ctx.inner_context("a2"));
        let b0 = new_fq2_1(&mut ctx.inner_context("b0"));
        let b1 = new_fq2_1(&mut ctx.inner_context("b1"));
        let b2 = new_fq2_1(&mut ctx.inner_context("b2"));
        let [c0, c1, c2] = new_mul_fq6(&mut ctx, [&a0, &a1, &a2], [&b0, &b1, &b2]);
        // compute states
        let mut compute_ctx = RawProof::mock_proof().into();
        compute_states(&ctx, &mut compute_ctx);

        // computation process
        {
            let a = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
            let b = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
            let (a0, a1, a2) = (a.c0, a.c1, a.c2);
            let (b0, b1, b2) = (b.c0, b.c1, b.c2);
            let v0 = a0 * b0;
            let v1 = (a0 + a1 + a2) * (b0 + b1 + b2);
            let v2 = (a0 - a1 + a2) * (b0 - b1 + b2);
            let v3 = (a0 + Fq2::from(2) * a1 + Fq2::from(4) * a2)
                * (b0 + Fq2::from(2) * b1 + Fq2::from(4) * b2);
            let v4 = a2 * b2;
            let x = Fq2::from(3) * v0 - Fq2::from(3) * v1 - v2 + v3 - Fq2::from(12) * v4;
            let c0 = Fq2::from(6) * v0 + x * Fq6Config::NONRESIDUE;
            debug!("c0: {:?}", c0 / Fq2::from(6));
            debug!("v0: {:?}", v0);
            debug!("v1: {:?}", v1);
            debug!("v2: {:?}", v2);
            debug!("v3: {:?}", v3);
            debug!("v4: {:?}", v4);
        }

        // check result
        let a = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
        let b = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));

        let c = a * b;
        for (idx, (node, cx)) in vec![c0, c1, c2]
            .into_iter()
            .zip(vec![c.c0, c.c1, c.c2].into_iter())
            .enumerate()
        {
            let state = get_state(&ctx, &node.name);
            info!("name: {}, c{}: {:?}", node.name, idx, state);
            assert_eq!(state.get_fq2(), cx);
        }
        info!("v0: {:?}", get_state(&ctx, "test_v0"));
        info!("v1: {:?}", get_state(&ctx, "test_v1"));
        info!("v2: {:?}", get_state(&ctx, "test_v2"));
        info!("v3: {:?}", get_state(&ctx, "test_v3"));
        info!("v4: {:?}", get_state(&ctx, "test_v4"));
    }
}
