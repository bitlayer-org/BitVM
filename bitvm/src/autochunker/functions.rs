use std::sync::Arc;

use super::{computation_graph::*, intermediate_state::*, primitve_functions::*};
use crate::{define_input, define_overide_script, define_script};
use ark_bn254::{Fq2, Fq6, Fq6Config};
use ark_ec::AffineRepr;
use ark_ff::{Field, Fp6Config};

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
            137000
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
            137000
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
            137000
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
            137000
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
            137000
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
            137000
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
            137000
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
            137000
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
            137000
        )
    );

    [c0.clone(), c1.clone(), c2.clone()]
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
//                         = 1 + \lambda x_p' + (-v) y_p' = F_{q^6}(1) + (F_{a^6}(\lamdba + (-v)y_p' \cdot w^2)) \cdot w
pub fn double_by_tagent_line(ctx: &mut GraphContext, t4x: &BitVMNode, t4y: &BitVMNode) {
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

    let lambda = new_input(&mut graph, format!("t4_lambda_in_loop_{}", i));
    let v = new_input(&mut graph, format!("t4_v_in_loop_{}", i));
}

#[cfg(test)]
mod tests {
    use crate::autochunker::computation_graph::{compute_states, new_input, GraphContext};
    use crate::autochunker::functions::new_square_fq6;
    use crate::autochunker::intermediate_state::State;
    use crate::autochunker::primitve_functions::ComputeCtx;
    use crate::autochunker::proof::RawProof;
    use crate::{define_input, define_overide_script, define_script};
    use ark_bn254::{Fq2, Fq6};
    use ark_ff::Field;
    use log::info;

    #[test_log::test]
    fn test_square_fq6() {
        let mut ctx = GraphContext::new("test");
        define_input!(
            ctx,
            a0,
            Fq2,
            Box::new(|_: &mut ComputeCtx, _: Vec<State>| State::Fq2(Some(Fq2::from(1))))
        );
        define_input!(
            ctx,
            a1,
            Fq2,
            Box::new(|_: &mut ComputeCtx, _: Vec<State>| State::Fq2(Some(Fq2::from(1))))
        );
        define_input!(
            ctx,
            a2,
            Fq2,
            Box::new(|_: &mut ComputeCtx, _: Vec<State>| State::Fq2(Some(Fq2::from(1))))
        );

        let [c0, c1, c2] = new_square_fq6(&mut ctx, [&a0, &a1, &a2]);
        let mut compute_ctx = RawProof::mock_proof().into();
        compute_states(&ctx, &mut compute_ctx);
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
}
