use super::{computation_graph::*, compute_ctx::*, intermediate_state::*, primitve_functions::*};
use crate::{define_input, define_overide_script, define_script};
use ark_bn254::Config as Bn254Config;
use ark_bn254::{Config, Fq12, Fq2, Fq6, Fq6Config, G2Affine};
use ark_ec::bn::BnConfig;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::MontFp;
use ark_ff::{Field, Fp12Config, Fp6Config};
use bitcoin::pow;
use serde::de;
use std::ops::Neg;

pub fn new_square_fq12(
    ctx: &mut GraphContext,
    inputs: [&BitVMNode; 3],
    selector: &Selector,
) -> [BitVMNode; 3] {
    define_input!(ctx, c0, Fq2, extract_eval_multi_f(0, selector.clone()));
    define_input!(ctx, c1, Fq2, extract_eval_multi_f(1, selector.clone()));
    define_input!(ctx, c2, Fq2, extract_eval_multi_f(2, selector.clone()));

    new_square_fq12_with_hint(ctx, inputs, [&c0, &c1, &c2]);
    [c0, c1, c2]
}

pub fn new_square_fq12_with_hint(
    ctx: &mut GraphContext,
    inputs: [&BitVMNode; 3],
    c: [&BitVMNode; 3],
) {
    let [c0, c1, c2] = c;
    let [a0, a1, a2] = inputs;

    // (v0, v1, v2) = (a0, a1, a2)^2
    let [v0, v1, v2] = new_square_fq6(&mut ctx.inner_context("a^2"), [a0, a1, a2]);

    // (r0, r1, r2) = (v0, v1, v2) * \beta + 1 = (a0, a1, a2)^2 * \beta + 1
    define_script!(ctx, v2_tweak, Fq2, [v2], fq2_mul_nonresidue());
    define_script!(ctx, r0, Fq2, [v2_tweak], fq2_plus_one());
    let (r1, r2) = (v0, v1);

    // check (c0, c1, c2) * (r0, r1, r2) = 2 * (a0, a1, a2)
    define_script!(ctx, d_a0, Fq2, [a0], fq2_mul_by_integer(2)); // [d]ouble_a0
    define_script!(ctx, d_a1, Fq2, [a1], fq2_mul_by_integer(2)); // [d]ouble_a1
    define_script!(ctx, d_a2, Fq2, [a2], fq2_mul_by_integer(2)); // [d]ouble_a2
    let [cr0, cr1, cr2] = new_mul_fq6(
        &mut ctx.inner_context("cxr"),
        [&c0, &c1, &c2],
        [&r0, &r1, &r2],
    );

    // check (cr0, cr1, cr2) == (double_a0, double_a1, double_a2)
    define_script!(ctx, _check0, CheckValid, [cr0, d_a0], check_fq2_equal());
    define_script!(ctx, _check1, CheckValid, [cr1, d_a1], check_fq2_equal());
    define_script!(ctx, _check2, CheckValid, [cr2, d_a2], check_fq2_equal());
}

pub fn new_mul_fq12(
    ctx: &mut GraphContext,
    a: [&BitVMNode; 3],
    b: [&BitVMNode; 3],
    selector: &Selector,
) -> [BitVMNode; 3] {
    define_input!(ctx, c0, Fq2, extract_eval_multi_f(0, selector.clone()));
    define_input!(ctx, c1, Fq2, extract_eval_multi_f(1, selector.clone()));
    define_input!(ctx, c2, Fq2, extract_eval_multi_f(2, selector.clone()));
    // check a * b is equal to c
    new_mul_fq12_with_hint(ctx, a, b, [&c0, &c1, &c2]);
    [c0, c1, c2]
}

// check a * b is equal to c
pub fn new_mul_fq12_with_hint(
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
pub fn t4_double_by_tangent_line(
    ctx: &mut GraphContext,
    t4x: &BitVMNode,
    t4y: &BitVMNode,
    p4: &BitVMNode,
    selector: &Selector,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    // define lambda
    define_input!(
        ctx,
        lambda,
        Fq2,
        extract_double_lambda(TPointSelector::T4(selector.clone()))
    );

    // define v
    define_input!(
        ctx,
        v,
        Fq2,
        extract_double_bias(TPointSelector::T4(selector.clone()))
    );

    // t4y =?= t4x \cdot \lambda + v
    define_script!(
        ctx,
        _check_line_through_point,
        CheckValid,
        [t4x, t4y, lambda, v],
        check_line_through_point(selector.clone())
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

    // t4y' = - (v + \lambda * t4x')
    define_script!(
        ctx,
        new_t4y,
        Fq2,
        [new_t4x, lambda, v],
        double_tangent_line_y()
    );

    // evaluate the point by the line (divisor)
    define_script!(
        ctx,
        c0,
        Fq2,
        [lambda, p4],
        nonconstant_line_evaluate_c0(selector.clone())
    );
    define_script!(
        ctx,
        c1,
        Fq2,
        [v, p4],
        nonconstant_line_evaluate_c1(selector.clone())
    );

    (new_t4x, new_t4y, c0, c1)
}

// if bit == 1, add q4, else add q4.neg()
// the only difference with tangent line is the way to compute the new t4 point
// for tangent line: x3 = \lambda^2 - 2 \cdot t4x
//                   y3 = - (v + \lambda * x3)
// for chord line:   x3 = \lambda^2 - t4x - q4x
//                   y3 = - (v + \lambda * x3)
// return (t4x', t4y', c0, c1)
pub fn t4_add_by_chord_line(
    ctx: &mut GraphContext,
    t4x: &BitVMNode,
    t4y: &BitVMNode,
    q4x: &BitVMNode,
    q4y: &BitVMNode,
    q4y_neg: &BitVMNode,
    p4: &BitVMNode,
    bit: i8,
    selector: &Selector,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    let is_neg = if bit == 1 { false } else { true };

    // lambda
    define_input!(
        ctx,
        lambda,
        Fq2,
        extract_add_lambda(TPointSelector::T4(selector.clone()), is_neg)
    );

    // define bias
    define_input!(
        ctx,
        v,
        Fq2,
        extract_add_bias(TPointSelector::T4(selector.clone()), is_neg)
    );

    // t4y =?= t4x \cdot \lambda + v
    define_script!(
        ctx,
        _check_line_through_point,
        CheckValid,
        [t4x, t4y, lambda, v],
        check_line_through_point(selector.clone())
    );

    // q4y =?= q4x \cdot \lambda + v
    if bit == 1 {
        define_script!(
            ctx,
            _check_line_through_point_q4,
            CheckValid,
            [q4x, q4y, lambda, v],
            check_line_through_point(selector.clone())
        );
    } else {
        define_script!(
            ctx,
            _check_line_through_point_q4,
            CheckValid,
            [q4x, q4y_neg, lambda, v],
            check_line_through_point(selector.clone())
        );
    }

    // t4x' = \lambda^2 -  t4x - q4x
    define_script!(ctx, new_t4x, Fq2, [t4x, q4x, lambda], add_chord_line_x());

    // t4y' = - (v + \lambda * t4x')
    define_script!(ctx, new_t4y, Fq2, [new_t4x, lambda, v], add_chord_line_y());

    // evaluate the point by the line (divisor)
    define_script!(
        ctx,
        c0,
        Fq2,
        [lambda, p4],
        nonconstant_line_evaluate_c0(selector.clone())
    );
    define_script!(
        ctx,
        c1,
        Fq2,
        [v, p4],
        nonconstant_line_evaluate_c1(selector.clone())
    );

    (new_t4x, new_t4y, c0, c1)
}

// return (t4x', t4y', c0, c1)
pub fn t4_add_by_chord_line_with_frob(
    ctx: &mut GraphContext,
    t4x: &BitVMNode,
    t4y: &BitVMNode,
    frob_q4x: &BitVMNode,
    frob_q4y: &BitVMNode,
    p4: &BitVMNode,
    selector: &Selector,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    t4_add_by_chord_line(ctx, t4x, t4y, frob_q4x, frob_q4y, frob_q4y, p4, 1, selector)
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

// outputs: t3_c0, t3_c1, t2_c0, t2_c1
pub fn evaluate_t2_and_t3(
    ctx: &mut GraphContext,
    p3_tweak: &BitVMNode,
    p2_tweak: &BitVMNode,
    selector: Selector,
) -> (BitVMNode, BitVMNode, BitVMNode, BitVMNode) {
    let (is_neg, is_double) = match selector {
        Selector::Loop(i, LoopSelector::AddPoint) => {
            let bit = Bn254Config::ATE_LOOP_COUNT[i - 1];
            (if bit == 1 { false } else { true }, false)
        }
        Selector::Loop(_, LoopSelector::DoublePoint) => (false, true),
        Selector::FrobPoint(_) => (false, false),
        _ => panic!("Invalid selector {:?}", selector),
    };

    // update t3 by chord line
    define_script!(
        ctx,
        t3_c0,
        Fq2,
        [p3_tweak],
        constant_line_eval_c0(TPointSelector::T3(selector.clone()), is_neg, is_double)
    );
    define_script!(
        ctx,
        t3_c1,
        Fq2,
        [p3_tweak],
        constant_line_eval_c1(TPointSelector::T3(selector.clone()), is_neg, is_double)
    );

    // update t2 by chord line
    define_script!(
        ctx,
        t2_c0,
        Fq2,
        [p2_tweak],
        constant_line_eval_c0(TPointSelector::T2(selector.clone()), is_neg, is_double)
    );
    define_script!(
        ctx,
        t2_c1,
        Fq2,
        [p2_tweak],
        constant_line_eval_c1(TPointSelector::T2(selector.clone()), is_neg, is_double)
    );

    (t3_c0, t3_c1, t2_c0, t2_c1)
}

// line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
// equals
// [1 + (t4_c0, t4_c1, 0) J] * [1 + (t3_c0, t3_c1, 0) J] * [1 + (t2_c0, t2_c1, 0) J]
pub fn line_evaluate_multiplication_with_hint(
    ctx: &mut GraphContext,
    t4_c0: &BitVMNode,
    t4_c1: &BitVMNode,
    t3_c0: &BitVMNode,
    t3_c1: &BitVMNode,
    t2_c0: &BitVMNode,
    t2_c1: &BitVMNode,
    [g0, g1, g2]: [&BitVMNode; 3],
) {
    // step 1:
    // [1 + (t4_c0, t4_c1, 0) J] * [1 + (t3_c0, t3_c1, 0) J] ->
    // (1 + (s0, s1, s2) J^2)+ (d0, d1, 0) J ->
    // (m0, m1, m2) + (d0, d1, 0) J
    //
    // d0 = t3_c0 + t4_c0
    define_script!(ctx, d0, Fq2, [t3_c0, t4_c0], fq2_add());
    // d1 = t3_c1 + t4_c1
    define_script!(ctx, d1, Fq2, [t3_c1, t4_c1], fq2_add());

    // t3_sum = t3_c0 + t3_c1
    define_script!(ctx, t3_sum, Fq2, [t3_c0, t3_c1], fq2_add());
    // t4_sum = t4_c0 + t4_c1
    define_script!(ctx, t4_sum, Fq2, [t4_c0, t4_c1], fq2_add());

    // s0 = t4_c0 * t3_c0
    define_script!(ctx, s0, Fq2, [t4_c0, t3_c0], fq2_mul());
    // s2 = t4_c1 * t3_c1
    define_script!(ctx, s2, Fq2, [t4_c1, t3_c1], fq2_mul());
    // [b]inomial = (t3_c0 + t3_c1) * (t4_c0 + t4_c1)
    define_script!(ctx, b, Fq2, [t3_sum, t4_sum], fq2_mul());
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
    // ((m0, m1, m2) + (e0, e1, e2) J^2) + ((d0, d1, 0) + (t2_c0, t2_c1, 0) * (m0, m1, m2) ) J ->
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
    let (h0, h1, h2) = (e2_tweak, e0, e1);
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
    let [x0, x1, x2] = new_mul_fq6(ctx, [&g0, &g1, &g2], [&mh0, &mh1, &mh2]);
    define_script!(ctx, _check_mul_x0, CheckValid, [x0, dk0], check_fq2_equal());
    define_script!(ctx, _check_mul_x1, CheckValid, [x1, dk1], check_fq2_equal());
    define_script!(ctx, _check_mul_x2, CheckValid, [x2, dk2], check_fq2_equal());
}

pub fn line_evaluate_multiplication(
    ctx: &mut GraphContext,
    t4_c0: &BitVMNode,
    t4_c1: &BitVMNode,
    t3_c0: &BitVMNode,
    t3_c1: &BitVMNode,
    t2_c0: &BitVMNode,
    t2_c1: &BitVMNode,
    selector: &Selector,
) -> (BitVMNode, BitVMNode, BitVMNode) {
    define_input!(ctx, g0, Fq2, extract_line_evaluation_g(0, selector.clone()));
    define_input!(ctx, g1, Fq2, extract_line_evaluation_g(1, selector.clone()));
    define_input!(ctx, g2, Fq2, extract_line_evaluation_g(2, selector.clone()));

    line_evaluate_multiplication_with_hint(
        ctx,
        t4_c0,
        t4_c1,
        t3_c0,
        t3_c1,
        t2_c0,
        t2_c1,
        [&g0, &g1, &g2],
    );

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

#[cfg(test)]
mod tests {
    use crate::autochunker::computation_graph::{
        compute_states, new_input, BitVMNode, GraphContext,
    };
    use crate::autochunker::compute_ctx::ComputeCtx;
    use crate::autochunker::functions::{
        fq12_frobinus_map, line_evaluate_multiplication_with_hint, mul_by_2char_neg, new_mul_fq12,
        new_mul_fq12_with_hint, new_mul_fq6, new_square_fq12, new_square_fq12_with_hint,
        new_square_fq6, t4_double_by_tangent_line,
    };
    use crate::autochunker::intermediate_state::State;
    use crate::autochunker::primitve_functions::mul_by_char;
    use crate::autochunker::proof::RawProof;
    use crate::autochunker::test::{get_state, show_all_states};
    use crate::{define_input, define_overide_script, define_script};
    use ark_bn254::G2Affine;
    use ark_bn254::{Fq, Fq12, Fq2, Fq6, Fq6Config, G1Affine};
    use ark_ec::bn::BnConfig;
    use ark_ec::AffineRepr;
    use ark_ff::{AdditiveGroup, Field};
    use ark_ff::{Fp6Config, UniformRand};
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

    fn get_state_debug(ctx: &GraphContext, name: *const c_char) -> State {
        let rust_string = unsafe {
            let c_str = CStr::from_ptr(name);
            c_str.to_str().unwrap()
        };
        let state = get_state(ctx, rust_string);
        println!("state: {:?}", state);
        state
    }

    fn random_fq6() -> Fq6 {
        let mut rng = ark_std::test_rng();
        let a = Fq6::new(
            Fq2::rand(&mut rng),
            Fq2::rand(&mut rng),
            Fq2::rand(&mut rng),
        );
        a
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

        new_mul_fq12_with_hint(&mut ctx, [&a0, &a1, &a2], [&b0, &b1, &b2], [&c0, &c1, &c2]);

        // compute states
        let mut compute_ctx = RawProof::mock_proof().into();
        compute_states(&ctx, &mut compute_ctx);

        // check result
        show_all_states(&ctx);
    }

    #[test_log::test]
    fn test_square_fq12() {
        let a = random_fq6();
        let a_fq12 = Fq12::new(Fq6::from(1), a);
        let a_square = a_fq12.square();
        let c = a_square.c1 / a_square.c0;

        let mut ctx = GraphContext::new("test");
        let [a0, a1, a2] = new_fq6(&mut ctx.inner_context("a"), a);
        let [c0, c1, c2] = new_fq6(&mut ctx.inner_context("c"), c);
        new_square_fq12_with_hint(
            &mut ctx.inner_context("sqaure"),
            [&a0, &a1, &a2],
            [&c0, &c1, &c2],
        );

        // compute states
        let mut compute_ctx = RawProof::mock_proof().into();
        let states = compute_states(&ctx, &mut compute_ctx);

        assert_eq!(states, ctx.graph.lock().unwrap().number_of_nodes());

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

    #[test_log::test]
    fn test_line_evaluation() {
        let t2 = Fq6::new(Fq2::from(1), Fq2::from(2), Fq2::from(0));
        let t3 = Fq6::new(Fq2::from(4), Fq2::from(5), Fq2::from(0));
        let t4 = Fq6::new(Fq2::from(7), Fq2::from(8), Fq2::from(0));

        let (real_t2, real_t3, real_t4) = (
            Fq12::new(Fq6::from(1), t2),
            Fq12::new(Fq6::from(1), t3),
            Fq12::new(Fq6::from(1), t4),
        );

        let evaluation_multi = real_t2 * real_t3 * real_t4;
        let g = evaluation_multi.c1 / evaluation_multi.c0;

        let mut ctx = GraphContext::new("test");
        let [t2_c0, t2_c1, t2_c2] = new_fq6(&mut ctx.inner_context("t2"), t2);
        let [t3_c0, t3_c1, t3_c2] = new_fq6(&mut ctx.inner_context("t3"), t3);
        let [t4_c0, t4_c1, t4_c2] = new_fq6(&mut ctx.inner_context("t4"), t4);
        let [g_c0, g_c1, g_c2] = new_fq6(&mut ctx.inner_context("g"), g);

        line_evaluate_multiplication_with_hint(
            &mut ctx,
            &t4_c0,
            &t4_c1,
            &t3_c0,
            &t3_c1,
            &t2_c0,
            &t2_c1,
            [&g_c0, &g_c1, &g_c2],
        );

        // compute states
        let mut compute_ctx = RawProof::mock_proof().into();
        compute_states(&ctx, &mut compute_ctx);

        // check result
        show_all_states(&ctx);

        info! {"(m0, m1, m2) + (d0, d1, 0)J: {:?}", (real_t3 * real_t4)};
        info! {"(mh0, mh1, mh2) + (dk0, dk1, dk2)J: {:?}", (real_t2 * real_t3 * real_t4)};
        info! {"(e0, e1, e2): {:?}", (real_t3 * real_t4).c1 * real_t2.c1}
    }
}
