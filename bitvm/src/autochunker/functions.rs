use super::{computation_graph::*, intermediate_state::*, primitve_functions::*};
use crate::{define_input, define_overide_script, define_script};
use ark_bn254::{Fq12, Fq2, Fq6, Fq6Config, G2Affine};
use ark_ec::bn::BnConfig;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::MontFp;
use ark_ff::{Field, Fp12Config, Fp6Config};
use bitcoin::pow;
use eval_args::T3OrT2;
use serde::de;
use std::ops::Neg;

// check a * b is equal to c
pub fn new_mul_fq12(
    ctx: &mut GraphContext,
    a: [&BitVMNode; 3],
    b: [&BitVMNode; 3],
    c: [&BitVMNode; 3],
) {
    let (a0, a1, a2) = (a[0], a[1], a[2]);
    let (b0, b1, b2) = (b[0], b[1], b[2]);
    let (c0, c1, c2) = (c[0], c[1], c[2]);

    define_script!(ctx, ab0, Fq2, [a0, b0], fq2_add()); // ab0 = a0 + b0
    define_script!(ctx, ab1, Fq2, [a1, b1], fq2_add()); // ab1 = a1 + b1
    define_script!(ctx, ab2, Fq2, [a2, b2], fq2_add()); // ab2 = a2 + b2

    // (v0, v1, v2) = (a0, a1, a2) * (b0, b1, b2)
    let [v0, v1, v2] = new_mul_fq6(
        &mut ctx.inner_context("axb"),
        [&a0, &a1, &a2],
        [&b0, &b1, &b2],
    );
    // (r0, r1, r2) = (v0, v1, v2) * \beta + 1
    define_script!(ctx, v2_tweak, Fq2, [v2], fq2_mul_nonresidue());
    define_script!(ctx, r0, Fq2, [v2_tweak], fq2_plus_one());
    let (r1, r2) = (v0, v1);

    // (rc0, rc1, rc2) = (r0, r1, r2) * (c0, c1, c2)
    let [rc0, rc1, rc2] = new_mul_fq6(
        &mut ctx.inner_context("rxc"),
        [&r0, &r1, &r2],
        [&c0, &c1, &c2],
    );

    // check (rc0, rc1, rc2) == (ab0, ab1, ab2)
    define_script!(ctx, _check0, CheckValid, [rc0, ab0], check_fq2_equal());
    define_script!(ctx, _check1, CheckValid, [rc1, ab1], check_fq2_equal());
    define_script!(ctx, _check2, CheckValid, [rc2, ab2], check_fq2_equal());
}

/// three input each which is fq2
pub fn new_square_fq6(ctx: &mut GraphContext, inputs: [&BitVMNode; 3]) -> [BitVMNode; 3] {
    let (a0, a1, a2) = (inputs[0], inputs[1], inputs[2]);

    // s0 = a0^2
    define_script!(ctx, s0, Fq2, [a0], fq2_square());

    // s1 = (a_0 + a_1 + a_2)^2
    define_script!(ctx, a0_plus_a2, Fq2, [a0, a2], fq2_add());
    define_script!(ctx, a_sum, Fq2, [a0_plus_a2, a1], fq2_add());
    define_script!(ctx, s1, Fq2, [a_sum], fq2_square());

    // s2 = (a_0 - a_1 + a_2)^2
    define_script!(ctx, a_sub, Fq2, [a0_plus_a2, a1], fq2_sub());
    define_script!(ctx, s2, Fq2, [a_sub], fq2_square());

    // s3 = 2 \cdot a_1 \cdot a_2
    define_script!(ctx, a1_times_2, Fq2, [a1], fq2_mul_by_integer(2));
    define_script!(ctx, s3, Fq2, [a1_times_2, a2], fq2_mul());

    // s4 = a_2^2
    define_script!(ctx, s4, Fq2, [a2], fq2_square());

    // t4 = (s1 + s2) / 2
    define_script!(ctx, s1_plus_s2, Fq2, [s1, s2], fq2_add());
    define_script!(ctx, t4, Fq2, [s1_plus_s2], fq2_div2());

    // c0 = s0 + \beta \cdot s_3
    define_script!(ctx, s3_tweak, Fq2, [s3], fq2_mul_nonresidue());
    define_script!(ctx, c0, Fq2, [s0, s3_tweak], fq2_add());

    // c1 = s1 - s3 - t4 + \beta s4
    define_script!(ctx, c11, Fq2, [s1, s3], fq2_sub()); // c11 = s1 - s3
    define_script!(ctx, c12, Fq2, [c11, t4], fq2_sub()); // c12 = c11 - t1
    define_script!(ctx, s4_tweak, Fq2, [s4], fq2_mul_nonresidue());
    define_script!(ctx, c1, Fq2, [c12, s4_tweak], fq2_add()); // c1 = c12 + s4

    // c2 = t4 - s0 - s4
    define_script!(ctx, c2, Fq2, [t4, s0, s4], fq2_sub2());

    [c0.clone(), c1.clone(), c2.clone()]
}

pub fn new_mul_fq6(
    ctx: &mut GraphContext,
    a: [&BitVMNode; 3],
    b: [&BitVMNode; 3],
) -> [BitVMNode; 3] {
    let (a0, a1, a2) = (a[0], a[1], a[2]);
    let (b0, b1, b2) = (b[0], b[1], b[2]);
    // v0 = a0 * b0
    define_script!(ctx, v0, Fq2, [a0, b0], fq2_mul());

    // v1 = (a0 + a1 + a2) * (b0 + b1 + b2)
    define_script!(ctx, a0_plus_a2, Fq2, [a0, a2], fq2_add());
    define_script!(ctx, b0_plus_b2, Fq2, [b0, b2], fq2_add());
    define_script!(ctx, v1_l, Fq2, [a0_plus_a2, a1], fq2_add()); // l -> left
    define_script!(ctx, v1_r, Fq2, [b0_plus_b2, b1], fq2_add()); // r -> right
    define_script!(ctx, v1, Fq2, [v1_l, v1_r], fq2_mul());

    // v2 = (a0 - a1 + a2) * (b0 - b1 + b2)
    define_script!(ctx, v2_l, Fq2, [a0_plus_a2, a1], fq2_sub());
    define_script!(ctx, v2_r, Fq2, [b0_plus_b2, b1], fq2_sub());
    define_script!(ctx, v2, Fq2, [v2_l, v2_r], fq2_mul());

    // v3 = (a0 + 2a1 + 4a2) * (b0 + 2b1 + 4b2)
    define_script!(ctx, a2_times_3, Fq2, [a2], fq2_mul_by_integer(3));
    define_script!(ctx, a1_p_a2_times_3, Fq2, [a1, a2_times_3], fq2_add());
    define_script!(ctx, v3_l, Fq2, [v1_l, a1_p_a2_times_3], fq2_add());
    define_script!(ctx, b2_times_3, Fq2, [b2], fq2_mul_by_integer(3));
    define_script!(ctx, b1_p_b2_times_3, Fq2, [b1, b2_times_3], fq2_add());
    define_script!(ctx, v3_r, Fq2, [v1_r, b1_p_b2_times_3], fq2_add());
    define_script!(ctx, v3, Fq2, [v3_l, v3_r], fq2_mul());

    // v4 = a2 * b2
    define_script!(ctx, v4, Fq2, [a2, b2], fq2_mul());

    // x = 3v0 - 3v1 - v2 + v3 - 12v4
    define_script!(ctx, v0_times_3, Fq2, [v0], fq2_mul_by_integer(3));
    define_script!(ctx, v1_times_3, Fq2, [v1], fq2_mul_by_integer(3));
    define_script!(ctx, v4_times_6, Fq2, [v4], fq2_mul_by_integer(6));
    define_script!(ctx, v4_times_12, Fq2, [v4_times_6], fq2_mul_by_integer(2));
    define_script!(ctx, x1, Fq2, [v0_times_3, v1_times_3], fq2_sub()); // x1 = 3v0 - 3v1
    define_script!(ctx, x2, Fq2, [x1, v2], fq2_sub()); // x2 = x1 - v2
    define_script!(ctx, x3, Fq2, [x2, v3], fq2_add()); // x3 = x2 + v3
    define_script!(ctx, x, Fq2, [x3, v4_times_12], fq2_sub()); // x = x3 - 12v4

    // c0 = 6v0 + \beta x
    define_script!(ctx, x_tweak, Fq2, [x], fq2_mul_nonresidue());
    define_script!(ctx, v0_times_6, Fq2, [v0], fq2_mul_by_integer(6));
    define_script!(ctx, c0, Fq2, [v0_times_6, x_tweak], fq2_add());

    // y = -3v0 + 6v1 - 2v2 - v3 + 12v4
    define_script!(ctx, y1, Fq2, [v1_times_3, x1], fq2_sub()); // y1 = -3v0 + 6v1 = 3v1 - x1
    define_script!(ctx, v2_times_2, Fq2, [v2], fq2_mul_by_integer(2));
    define_script!(ctx, y2, Fq2, [y1, v2_times_2], fq2_sub()); // y2 = y1 - 2v2
    define_script!(ctx, y3, Fq2, [y2, v3], fq2_sub()); // y3 = y2 - v3
    define_script!(ctx, y, Fq2, [y3, v4_times_12], fq2_add()); // y = y3 + 12v4

    // c1 = y + \beta 6v4
    define_script!(ctx, v4_tweak, Fq2, [v4_times_6], fq2_mul_nonresidue());
    define_script!(ctx, c1, Fq2, [y, v4_tweak], fq2_add());

    // c2 = 3v1 - 6v0 + 3v2 - 6v4
    define_script!(ctx, c2_1, Fq2, [v1_times_3, v0_times_6], fq2_sub()); // c2_1 = 3v1 - 6v0
    define_script!(ctx, v2_times_3, Fq2, [v2_times_2, v2], fq2_add());
    define_script!(ctx, c2_2, Fq2, [c2_1, v2_times_3], fq2_add());
    define_script!(ctx, c2, Fq2, [c2_2, v4_times_6], fq2_sub()); // c2 = c2_2 - 6v4

    // c0 = c0/6, c1 = c1/6, c2 = c2/6
    define_script!(ctx, c0_tweak, Fq2, [c0], fq2_div6());
    define_script!(ctx, c1_tweak, Fq2, [c1], fq2_div6());
    define_script!(ctx, c2_tweak, Fq2, [c2], fq2_div6());

    [c0_tweak, c1_tweak, c2_tweak]
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
    define_script!(ctx, new_t4x, Fq2, [t4x, lambda], double_tangent_line_x());

    // t4y' = - (v + \lambda * t4x') and update t4
    define_script!(
        ctx,
        new_t4y,
        Fq2,
        [new_t4x, lambda, v],
        double_tangent_line_y()
    );

    // evaluate the point by the line (divisor)
    define_script!(ctx, c0, Fq2, [lambda, p4], nonconstant_line_evaluate_c0());
    define_script!(ctx, c1, Fq2, [v, p4], nonconstant_line_evaluate_c1());

    (new_t4x, new_t4y, c0, c1)
}

// if bit == 1, add q4, else add q4.neg()
// the only difference with tangent line is the way to compute the updated t4 point
// for tangent line: x3 = \lambda^2 - 2 \cdot t4x
//                   y3 = - (v + \lambda * x3)
// for chord line:   x3 = \lambda^2 - t4x - q4x
//                   y3 = - (v + \lambda * x3)
// return (t4x', t4y', c0, c1)
pub fn add_by_chord_line(
    ctx: &mut GraphContext,
    t4x: &BitVMNode,
    t4y: &BitVMNode,
    q4x: &BitVMNode,
    q4y: &BitVMNode,
    q4y_neg: &BitVMNode,
    p4: &BitVMNode,
    bit: i8,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    // lambda
    define_input!(
        ctx,
        lambda,
        Fq2,
        Box::new(move |ctx: &mut ComputeCtx, _: Vec<State>| {
            assert!(ctx.t4.xy().is_some());
            let (t4x, t4y) = ctx.t4.xy().unwrap();
            let (q4x, q4y) = ctx.q4.xy().unwrap();
            let (q4x, q4y) = if bit == 1 {
                (q4x, q4y)
            } else {
                (q4x, q4y.neg())
            };
            let lambda = (t4y - q4y) / (t4x - q4x);
            State::Fq2(Some(lambda))
        })
    );

    // define bias
    define_input!(
        ctx,
        v,
        Fq2,
        Box::new(move |ctx: &mut ComputeCtx, _: Vec<State>| {
            assert!(ctx.t4.xy().is_some());
            let (t4x, t4y) = ctx.t4.xy().unwrap();
            let (q4x, q4y) = ctx.q4.xy().unwrap();
            let (q4x, q4y) = if bit == 1 {
                (q4x, q4y)
            } else {
                (q4x, q4y.neg())
            };
            let lambda = (t4y - q4y) / (t4x - q4x);
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

    // q4y =?= q4x \cdot \lambda + v
    if bit == 1 {
        define_script!(
            ctx,
            _check_line_through_point_q4,
            CheckValid,
            [q4x, q4y, lambda, v],
            check_line_through_point()
        );
    } else {
        define_script!(
            ctx,
            _check_line_through_point_q4,
            CheckValid,
            [q4x, q4y_neg, lambda, v],
            check_line_through_point()
        );
    }

    // t4x' = \lambda^2 - 2 \cdot t4x
    define_script!(ctx, new_t4x, Fq2, [t4x, q4x, lambda], add_chord_line_x());

    // t4y' = - (v + \lambda * t4x') and update t4
    define_script!(ctx, new_t4y, Fq2, [q4x, lambda, v], add_chord_line_y());

    // evaluate the point by the line (divisor)
    define_script!(ctx, c0, Fq2, [lambda, p4], nonconstant_line_evaluate_c0());
    define_script!(ctx, c1, Fq2, [v, p4], nonconstant_line_evaluate_c1());

    (new_t4x, new_t4y, c0, c1)
}

// return (t4x', t4y', c0, c1)
pub fn add_by_chord_line_with_frob(
    ctx: &mut GraphContext,
    t4x: &BitVMNode,
    t4y: &BitVMNode,
    frob_q4x: &BitVMNode,
    frob_q4y: &BitVMNode,
    p4: &BitVMNode,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    add_by_chord_line(ctx, t4x, t4y, frob_q4x, frob_q4y, frob_q4y, p4, 1)
}

// compute q' = (q.x.conjugate()*beta_12, q.y.conjugate() * beta_13)
pub fn frob_point_mul_by_char(
    ctx: &mut GraphContext,
    q4x: &BitVMNode,
    q4y: &BitVMNode,
) -> (BitVMNode, BitVMNode) {
    define_script!(ctx, q4x_con, Fq2, [q4x], fq2_conjugate());
    define_script!(ctx, new_x, Fq2, [q4x_con], fq2_mul_by_constant(BETA12));

    define_script!(ctx, q4y_con, Fq2, [q4y], fq2_conjugate());
    define_script!(ctx, new_y, Fq2, [q4y_con], fq2_mul_by_constant(BETA13));

    (new_x, new_y)
}

pub fn frob_point_mul_by_char3(
    ctx: &mut GraphContext,
    q4x: &BitVMNode,
    q4y: &BitVMNode,
) -> (BitVMNode, BitVMNode) {
    define_script!(ctx, q4x_con, Fq2, [q4x], fq2_conjugate());
    define_script!(ctx, new_x, Fq2, [q4x_con], fq2_mul_by_constant(BETA32));

    define_script!(ctx, q4y_con, Fq2, [q4y], fq2_conjugate());
    define_script!(ctx, new_y, Fq2, [q4y_con], fq2_mul_by_constant(BETA33));

    (new_x, new_y)
}

// compute q' = (q.x*beta_22, q.y)
pub fn frob_point_mul_by_2char_neg<'a>(
    ctx: &mut GraphContext,
    q4x: &'a BitVMNode,
    q4y: &'a BitVMNode,
) -> (BitVMNode, &'a BitVMNode) {
    define_script!(ctx, new_x, Fq2, [q4x], fq2_mul_by_constant(BETA22));

    (new_x, q4y)
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

// inputs
fn add_chord_line_x() -> (ComputeFn, ScriptFn) {
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
fn add_chord_line_y() -> (ComputeFn, ScriptFn) { double_tangent_line_y() }

// inputs t4x, lambda, v
fn double_tangent_line_y() -> (ComputeFn, ScriptFn) {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 3);
        let t4x_new = inputs[0].get_fq2();
        let lambda = inputs[1].get_fq2();
        let v = inputs[2].get_fq2();

        // t4y' = - (v + \lambda * t4x')
        let t4y_new = -(v + lambda * t4x_new);
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
fn constant_line_compute(compute_ctx: &ComputeCtx, args: eval_args::Args) -> (Fq2, Fq2, G2Affine) {
    // select t_point
    let (t_point, q_point) = match args.t3_or_t2 {
        T3OrT2::T3 => (compute_ctx.t3, compute_ctx.q3),
        T3OrT2::T2 => (compute_ctx.t2, compute_ctx.q2),
    };

    let (lambda, new_t_point) = match args.mode {
        eval_args::Mode::Double => {
            // select is_double
            (
                (t_point.x.square() + t_point.x.square() + t_point.x.square())
                    / (t_point.y + t_point.y),
                t_point + t_point,
            )
        }
        eval_args::Mode::Add(is_neg_bit) => {
            // select is_double
            let q_point = match is_neg_bit {
                eval_args::IsNegBit::Neg => q_point.neg(),
                eval_args::IsNegBit::Pos => q_point,
            };
            (
                (t_point.y - q_point.y) / (t_point.x - q_point.x),
                t_point + q_point,
            )
        }
        eval_args::Mode::Frob(mul_type) => {
            // select is_double
            let q_point = match mul_type {
                eval_args::MulType::Char => mul_by_char(q_point),
                eval_args::MulType::Char2Neg => mul_by_2char_neg(q_point),
            };
            (
                (t_point.y - q_point.y) / (t_point.x - q_point.x),
                t_point + q_point,
            )
        }
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

pub mod eval_args {
    #[derive(Debug, Clone)]
    pub struct Args {
        pub t3_or_t2: T3OrT2,
        pub mode: Mode,
    }
    #[derive(Debug, Clone)]
    pub enum T3OrT2 {
        T3,
        T2,
    }
    #[derive(Debug, Clone)]
    pub enum Mode {
        Double,
        Add(IsNegBit),
        Frob(MulType),
    }
    #[derive(Debug, Clone)]
    pub enum IsNegBit {
        Neg,
        Pos,
    }
    #[derive(Debug, Clone)]
    pub enum MulType {
        Char,
        Char2Neg,
    }
}

pub fn constant_line_eval_c0(args: &eval_args::Args) -> (ComputeFn, ScriptFn) {
    let args = args.clone();
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let p_point = inputs[0].get_g1();

        let (lambda, _, _) = constant_line_compute(compute_ctx, args.clone());

        let mut c0 = lambda;
        c0.mul_assign_by_basefield(&p_point.x().unwrap());

        // evaluate the point by the line (divisor)
        State::Fq2(Some(c0))
    };
    (Box::new(func), placeholder_script_fn())
}
pub fn constant_line_eval_c1(args: &eval_args::Args) -> (ComputeFn, ScriptFn) {
    let args = args.clone();
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        assert_eq!(inputs.len(), 1);
        let p_point = inputs[0].get_g1();

        let (lambda, v, new_t_point) = constant_line_compute(compute_ctx, args.clone());

        let mut c0 = lambda;
        c0.mul_assign_by_basefield(&p_point.x().unwrap());
        let mut c1 = v.neg();
        c1.mul_assign_by_basefield(&p_point.y().unwrap());

        // update t point and point evaluate
        match args.t3_or_t2 {
            eval_args::T3OrT2::T3 => {
                compute_ctx.t3 = new_t_point;
                compute_ctx.evaluate_p3 = Some(Fq6::new(c0, c1, Fq2::from(0)));
            }
            eval_args::T3OrT2::T2 => {
                compute_ctx.t2 = new_t_point;
                compute_ctx.evaluate_p2 = Some(Fq6::new(c0, c1, Fq2::from(0)));
            }
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
    mode: eval_args::Mode,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    let t2_args = eval_args::Args {
        t3_or_t2: eval_args::T3OrT2::T2,
        mode: mode.clone(),
    };
    let t3_args = eval_args::Args {
        t3_or_t2: eval_args::T3OrT2::T3,
        mode: mode,
    };

    // update t3 by chord line
    define_script!(ctx, t3_c0, Fq2, [p3_tweak], constant_line_eval_c0(&t3_args));
    define_script!(ctx, t3_c1, Fq2, [p3_tweak], constant_line_eval_c1(&t3_args));

    // update t2 by chord line
    define_script!(ctx, t2_c0, Fq2, [p2_tweak], constant_line_eval_c0(&t2_args));
    define_script!(ctx, t2_c1, Fq2, [p2_tweak], constant_line_eval_c1(&t2_args));

    (t3_c0, t3_c1, t2_c0, t2_c1)
}

// line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
// equals
// [1 + (t4_c0, t4_c1, 0) J] * [1 + (t3_c0, t3_c1, 0) J] * [1 + (t2_c0, t2_c1, 0) J]
pub fn line_evaluate_multiplication(
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
    define_script!(ctx, s2_tweak, Fq2, [s2], fq2_mul_nonresidue());
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
    define_script!(ctx, e2_tweak, Fq2, [e2], fq2_mul_nonresidue());
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
    define_script!(ctx, m2_tweak, Fq2, [m2], fq2_mul_nonresidue());
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

pub fn fq12_frobinus_map(
    ctx: &mut GraphContext,
    c: [&BitVMNode; 3],
    power: usize,
) -> [BitVMNode; 3] {
    assert!(power <= 3 && power >= 1, "power out of range: {}", power);
    let [frob_c0, frob_c1, frob_c2] = fq6_frobinus_map(ctx, c, power);

    // (d0, d1, d2) = (frob_c0, frob_c1, frob_c2) * fq12::frob_coeff_c1
    let coeff = ark_bn254::Fq12Config::FROBENIUS_COEFF_FP12_C1
        [power % ark_bn254::Fq12Config::FROBENIUS_COEFF_FP12_C1.len()];
    define_script!(ctx, d0, Fq2, [frob_c0], fq2_mul_by_constant(coeff));
    define_script!(ctx, d1, Fq2, [frob_c1], fq2_mul_by_constant(coeff));
    define_script!(ctx, d2, Fq2, [frob_c2], fq2_mul_by_constant(coeff));
    [d0, d1, d2]
}

pub fn fq6_frobinus_map(
    ctx: &mut GraphContext,
    c: [&BitVMNode; 3],
    power: usize,
) -> [BitVMNode; 3] {
    assert!(power <= 3 && power >= 1, "power out of range: {}", power);
    let [c0, c1, c2] = c;

    // c0' = c0^q
    define_script!(ctx, frob_c0, Fq2, [c0], fq2_frobinus_map(power));
    // c1' = c1^q * fq6::frob_coeff_c1
    let coeff = ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C1
        [power % ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C1.len()];
    define_script!(ctx, frob_c1, Fq2, [c1], fq2_frobinus_map(power));
    define_script!(ctx, c1_tweak, Fq2, [frob_c1], fq2_mul_by_constant(coeff));

    // c2' = c2^q * fq6::frob_coeff_c2
    let coeff = ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C2
        [power % ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C2.len()];
    define_script!(ctx, frob_c2, Fq2, [c2], fq2_frobinus_map(power));
    define_script!(ctx, c2_tweak, Fq2, [frob_c2], fq2_mul_by_constant(coeff));

    [frob_c0, c1_tweak, c2_tweak]
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

const BETA32: Fq2 = Fq2::new(
    MontFp!("3772000881919853776433695186713858239009073593817195771773381919316419345261"),
    MontFp!("2236595495967245188281701248203181795121068902605861227855261137820944008926"),
);
const BETA33: Fq2 = Fq2::new(
    MontFp!("19066677689644738377698246183563772429336693972053703295610958340458742082029"),
    MontFp!("18382399103927718843559375435273026243156067647398564021675359801612095278180"),
);
const BETA22: Fq2 = Fq2::new(
    MontFp!("21888242871839275220042445260109153167277707414472061641714758635765020556616"),
    MontFp!("0"),
);
const BETA12: Fq2 = ark_bn254::Config::TWIST_MUL_BY_Q_X;
const BETA13: Fq2 = ark_bn254::Config::TWIST_MUL_BY_Q_Y;

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

#[cfg(test)]
mod tests {
    use crate::autochunker::computation_graph::{
        compute_states, new_input, BitVMNode, GraphContext,
    };
    use crate::autochunker::functions::{
        double_by_tangent_line, fq12_frobinus_map, mul_by_2char_neg, mul_by_char, new_mul_fq12,
        new_mul_fq6, new_square_fq6,
    };
    use crate::autochunker::intermediate_state::State;
    use crate::autochunker::primitve_functions::ComputeCtx;
    use crate::autochunker::proof::RawProof;
    use crate::{define_input, define_overide_script, define_script};
    use ark_bn254::G2Affine;
    use ark_bn254::{Fq, Fq12, Fq2, Fq6, Fq6Config, G1Affine};
    use ark_ec::bn::BnConfig;
    use ark_ec::AffineRepr;
    use ark_ff::Fp6Config;
    use ark_ff::{AdditiveGroup, Field};
    use graphrs::Graph;
    use log::{debug, info, warn};
    use std::ffi::CStr;
    use std::ops::*;
    use std::os::raw::c_char;

    fn new_fq2(ctx: &mut GraphContext, x: Fq2) -> BitVMNode {
        define_input!(
            ctx,
            _o,
            Fq2,
            Box::new(move |_: &mut ComputeCtx, _: Vec<State>| State::Fq2(Some(Fq2::from(x))))
        );
        _o
    }

    fn new_fq6(ctx: &mut GraphContext, x: Fq6) -> [BitVMNode; 3] {
        [
            new_fq2(&mut ctx.inner_context("c0"), x.c0),
            new_fq2(&mut ctx.inner_context("c1"), x.c1),
            new_fq2(&mut ctx.inner_context("c2"), x.c2),
        ]
    }

    fn new_g1(ctx: &mut GraphContext) -> BitVMNode {
        define_input!(
            ctx,
            _o,
            Fq6,
            Box::new(|_: &mut ComputeCtx, _: Vec<State>| State::G1(Some(
                G1Affine::from_random_bytes(b"bytes").unwrap()
            )))
        );
        _o
    }

    fn get_state(ctx: &GraphContext, name: &str) -> State {
        let lock_guard = ctx.graph.lock().unwrap();
        let node = lock_guard.get_node(name.to_string()).unwrap();
        node.attributes.clone().unwrap().state
    }

    fn get_state_debug(ctx: &GraphContext, name: *const c_char) -> State {
        let rust_string = unsafe {
            let c_str = CStr::from_ptr(name);
            c_str.to_str().unwrap()
        };
        let state = get_state(ctx, rust_string);
        println!("state: {:?}", state);
        state
    }

    fn show_all_states(ctx: &GraphContext) {
        let lock_guard = ctx.graph.lock().unwrap();
        for name in lock_guard.get_all_node_names() {
            let node = lock_guard.get_node(name.to_string()).unwrap();
            let state = node.attributes.clone().unwrap().state;
            match state {
                State::CheckValid(Some(x)) => {
                    if !x {
                        warn!("{} state: {:?}", name, state);
                    }
                }
                _ => {
                    info!("{} state: {:?}", name, state);
                }
            }
        }
    }

    #[test_log::test]
    fn test_square_fq6() {
        let mut ctx = GraphContext::new("test");
        let a = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
        let [a0, a1, a2] = new_fq6(&mut ctx, a);
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
        {
            // graph
            let a = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
            let b = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
            let [a0, a1, a2] = new_fq6(&mut ctx.inner_context("a"), a);
            let [b0, b1, b2] = new_fq6(&mut ctx.inner_context("b"), b);
            let [c0, c1, c2] = new_mul_fq6(&mut ctx, [&a0, &a1, &a2], [&b0, &b1, &b2]);
            // compute states
            let mut compute_ctx = RawProof::mock_proof().into();
            compute_states(&ctx, &mut compute_ctx);

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
                info!(
                    "name: {}, c{} state: {:?}, c{}: {}",
                    node.name, idx, state, idx, cx
                );
                // assert_eq!(state.get_fq2(), cx);
            }
        }

        // computation process
        {
            let a = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
            let b = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
            let (a0, a1, a2) = (a.c0, a.c1, a.c2);
            let (b0, b1, b2) = (b.c0, b.c1, b.c2);
            let v0 = a0 * b0;
            let k = a0.mul(b0);
            let v1 = (a0 + a1 + a2) * (b0 + b1 + b2);
            let v2 = (a0 - a1 + a2) * (b0 - b1 + b2);
            let v3 = (a0 + Fq2::from(2) * a1 + Fq2::from(4) * a2)
                * (b0 + Fq2::from(2) * b1 + Fq2::from(4) * b2);
            let v4 = a2 * b2;
            let x = Fq2::from(3) * v0 - Fq2::from(3) * v1 - v2 + v3 - Fq2::from(12) * v4;
            let c0 = Fq2::from(6) * v0 + x * Fq6Config::NONRESIDUE;
            info!("c0: {:?}", c0 / Fq2::from(6));
            info!("v0: {:?}", v0);
            info!("v1: {:?}", v1);
            info!("v2: {:?}", v2);
            info!("v3: {:?}", v3);
            info!("v4: {:?}", v4);
            info!("v3_l: {:?}", a0 + Fq2::from(2) * a1 + Fq2::from(4) * a2);
            info!("v3_r: {:?}", b0 + Fq2::from(2) * b1 + Fq2::from(4) * b2);
        }

        show_all_states(&ctx);
    }

    #[test_log::test]
    fn test_mul_fq12() {
        let mut ctx = GraphContext::new("test");
        let a = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
        let b = Fq6::new(Fq2::from(1), Fq2::from(1), Fq2::from(1));
        let c = Fq12::new(Fq6::from(1), a) * Fq12::new(Fq6::from(1), b);
        let c = c.c1 / c.c0;

        let [a0, a1, a2] = new_fq6(&mut ctx.inner_context("a"), a);
        let [b0, b1, b2] = new_fq6(&mut ctx.inner_context("b"), b);
        let [c0, c1, c2] = new_fq6(&mut ctx.inner_context("c"), c);

        new_mul_fq12(&mut ctx, [&a0, &a1, &a2], [&b0, &b1, &b2], [&c0, &c1, &c2]);

        // compute states
        let mut compute_ctx = RawProof::mock_proof().into();
        compute_states(&ctx, &mut compute_ctx);

        // check result
        show_all_states(&ctx);
    }

    #[test_log::test]
    fn test_frobinus() {
        let mut ctx = GraphContext::new("test");
        let x = Fq6::new(Fq2::from(1), Fq2::from(2), Fq2::from(3));
        let a = Fq12::new(Fq6::from(1), x);
        let a = a.frobenius_map(1);

        let [a0, a1, a2] = new_fq6(&mut ctx, x);
        let [b0, b1, b2] = fq12_frobinus_map(&mut ctx, [&a0, &a1, &a2], 1);

        // compute states
        let mut compute_ctx = RawProof::mock_proof().into();
        compute_states(&ctx, &mut compute_ctx);

        for (idx, (node, cx)) in vec![b0, b1, b2]
            .into_iter()
            .zip(vec![a.c1.c0, a.c1.c1, a.c1.c2].into_iter())
            .enumerate()
        {
            let state = get_state(&ctx, &node.name);
            info!(
                "name: {}, c{} state: {:?}, c{}: {}",
                node.name, idx, state, idx, cx
            );
            assert_eq!(state.get_fq2(), cx);
        }
    }

    #[test_log::test]
    fn test_eval_mul_by_char() {
        let g2 = G2Affine::from_random_bytes(b"bytes").unwrap();
        let frob_g2 = mul_by_char(g2);
        let frob2_g2 = mul_by_char(frob_g2);
        let neg_frob2_g2 = frob2_g2.neg();
        let g2_tweak = mul_by_2char_neg(g2);
        info!("g2: {:?}", g2);
        info!("frob_g2: {:?}", frob_g2);
        info!("frob2_g2: {:?}", frob2_g2);
        info!("neg_frob2_g2: {:?}", neg_frob2_g2);
        info!("g2_tweak: {:?}", g2_tweak);
        assert_eq!(neg_frob2_g2, g2_tweak);
    }
}
