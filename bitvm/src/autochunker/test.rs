use crate::autochunker::computation_graph::*;
use crate::autochunker::functions::*;
use crate::{define_input, define_overide_script, define_script};
use std::sync::Arc;
use std::time;
// use utils::*;
use crate::autochunker::intermediate_state::*;
use crate::autochunker::primitve_functions::*;
use crate::autochunker::proof::*;
use ark_bn254::Config as Bn254Config;
use ark_ec::bn::BnConfig;
use log::info;
use paste::paste;

#[test_log::test]
fn main_test() {
    // refer to groth16 https://eprint.iacr.org/2016/260.pdf Section 3.1
    // A \cdot B = \alpha \cdot \beta + C \codt \delta + P3 \cdot \gamma
    // where A, B, C are proof, P3 is the result of MSM and \alpha, \beta, \gamma, \delta are fixed by verifying key
    // By changing the equlity to \alpha \cdot \beta + C \codt \delta + P3 \cdot \gamma - A \cdot B = 0, two phases are needed.

    // Phase 1: multiple scalar multiplication to get P3
    // Phase 2: calculate the equlity \alpha \cdot \beta + C \codt \delta + P3 \cdot \gamma - A \cdot B = 0
    // We only need to calculate three pairs, since \alpha \cdot \beta is fixed.

    // Rename these varible by C = P2, \delta = Q2, P3 = P3, \gamma = Q3, A = P4, B = Q4

    // =========================================================================================================
    let ctx = GraphContext::new("groth16_verifier");
    let p3 = {
        let mut ctx = ctx.inner_context("MSM");

        // Phase 1: multiple scalar multiplication
        // Saying we have 5 scalars to multiply, we can use a graph to represent the computation
        // [scalar0, scalar1, scalar2, scalar3, scalar4] X [K0, K1, K2, K3, K4] = P3

        define_input!(ctx, scalar0, Fr, extract_scalar(0));
        define_input!(ctx, scalar1, Fr, extract_scalar(1));
        define_input!(ctx, scalar2, Fr, extract_scalar(2));
        define_input!(ctx, scalar3, Fr, extract_scalar(3));
        define_input!(ctx, scalar4, Fr, extract_scalar(4));

        // check the valid of scalar, scalar should be less than Fq::MOUDLES
        define_script!(ctx, _check_scalar0, CheckValid, [scalar0], scalar_valid());
        define_script!(ctx, _check_scalar1, CheckValid, [scalar1], scalar_valid());
        define_script!(ctx, _check_scalar2, CheckValid, [scalar2], scalar_valid());
        define_script!(ctx, _check_scalar3, CheckValid, [scalar3], scalar_valid());
        define_script!(ctx, _check_scalar4, CheckValid, [scalar4], scalar_valid());

        // pub const WINDOW_G1_MSM: u32 = 8; pub const BATCH_SIZE_PER_CHUNK: u32 = 1;
        // --> 302955
        // msm0 script, scalar0 is a input a msm0 script
        let window_size = 8;
        define_script!(ctx, msm0_0, G1, [scalar0], msm_initial(window_size));
        let mut msm_acc = msm0_0;

        for i in 1..windows_of_mul_table(window_size) {
            let mut ctx = ctx.inner_context(&format!("0_{}", i));
            define_overide_script!(
                ctx,
                msm_acc,
                G1,
                [scalar0, msm_acc],
                msm_steps(0, i, window_size)
            );
        }

        for (idx, input_node) in [scalar1, scalar2, scalar3, scalar4].into_iter().enumerate() {
            for i in 0..windows_of_mul_table(window_size) {
                let mut ctx = ctx.inner_context(&format!("{}_{}", idx + 1, i));
                define_overide_script!(
                    ctx,
                    msm_acc,
                    G1,
                    [input_node, msm_acc],
                    msm_steps(idx + 1, i, window_size)
                );
            }
        }

        msm_acc
    };

    // =========================================================================================================

    // Phase 2: Pairing Computation

    // 2.1 precompute point in G1 for the optimization in https://eprint.iacr.org/2013/722.pdf
    // y_p' -> 1 / y_p, x_p' -> - y_p / x_p
    // chunk_precompute_p disprovable(true) script 340846 stack 654
    {
        let mut ctx = ctx.inner_context("Pairing");

        define_input!(ctx, p2, G1, extract_p2());
        define_script!(ctx, _p2_check, CheckValid, [p2], check_g1_point());
        define_script!(ctx, p2_tweak, G1, [p2], tweak_point());

        define_input!(ctx, p4, G1, extract_p4());
        define_script!(ctx, _p4_check, CheckValid, [p4], check_g1_point());
        define_script!(ctx, p4_tweak, G1, [p4], tweak_point());

        define_script!(ctx, p3_tweak, G1, [p3], tweak_point());

        // saying c = 1 + a J, c_inv will be 1 - a J, because c * c_inv = (1+a^2) + 0 J = 1
        // so we can use neg(c) to represent the inverse of c
        define_input!(ctx, c0, Fq2, extract_c(0));
        define_input!(ctx, c1, Fq2, extract_c(1));
        define_input!(ctx, c2, Fq2, extract_c(2));
        define_script!(ctx, c_inv0, Fq6, [c0], neg_fq2());
        define_script!(ctx, c_inv1, Fq6, [c1], neg_fq2());
        define_script!(ctx, c_inv2, Fq6, [c2], neg_fq2());

        // define t4x and t4y
        define_input!(ctx, t4x, Fq2, extract_t4x());
        define_input!(ctx, t4y, Fq2, extract_t4y());
        let (mut t4x, mut t4y) = (t4x, t4y);

        let (mut f0, mut f1, mut f2) = (c_inv0.clone(), c_inv1.clone(), c_inv2.clone());

        for i in (1..Bn254Config::ATE_LOOP_COUNT.len()).rev() {
            let mut ctx = ctx.inner_context(&format!("ate_loop_{}", i));

            // square f
            [f0, f1, f2] = new_square_fq6(&mut ctx.inner_context("square_f"), [&f0, &f1, &f2]);

            // evaluate t4 by tagent line
            let res =
                double_by_tangent_line(&mut ctx.inner_context("double_t4"), &t4x, &t4y, &p4_tweak);
            (t4x, t4y) = (res.0, res.1);
            let (t4_c0, t4_c1) = (res.2, res.3);

            // evaluate t2 and t3 by precomputed tangent line
            let (t3_c0, t3_c1, t2_c0, t2_c1) = evaluate_tangent_t2_and_t3(
                &mut ctx.inner_context("double_t2_t3"),
                &p3_tweak,
                &p2_tweak,
            );

            // line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
            let eval_multi = line_evaluate_multiplication(
                &mut ctx.inner_context("square_eval"),
                &t4_c0,
                &t4_c1,
                &t3_c0,
                &t3_c1,
                &t2_c0,
                &t2_c1,
            );

            // (eval_multi_f0, eval_multi_f1, eval_multi_f2) = (f0, f1, f2) * (eval_multi);
            define_input!(ctx, eval_multi_f0, Fq6, extract_eval_multi_f(0));
            define_input!(ctx, eval_multi_f1, Fq6, extract_eval_multi_f(1));
            define_input!(ctx, eval_multi_f2, Fq6, extract_eval_multi_f(2));
            new_mul_fq12(
                &mut ctx.inner_context("eval_multi"),
                [&f0, &f1, &f2],
                [&eval_multi.0, &eval_multi.1, &eval_multi.2],
                [&eval_multi_f0, &eval_multi_f1, &eval_multi_f2],
            );
            (f0, f1, f2) = (eval_multi_f0, eval_multi_f1, eval_multi_f2);

            // if ate bit is 1, we need to multiply the c, else we need to multiply the c_inv
            let bit = Bn254Config::ATE_LOOP_COUNT[i];
            let (d0, d1, d2) = if bit == -1 {
                (&c0, &c1, &c2)
            } else {
                (&c_inv0, &c_inv1, &c_inv2)
            };

            // (fd0, fd1, fd2) = (f0, f1, f2) * (d0, d1, d2)
            define_input!(ctx, fd0, Fq6, extract_fd(0, bit));
            define_input!(ctx, fd1, Fq6, extract_fd(1, bit));
            define_input!(ctx, fd2, Fq6, extract_fd(1, bit));
            new_mul_fq12(
                &mut ctx.inner_context("fd"),
                [&f0, &f1, &f2],
                [d0, d1, d2],
                [&fd0, &fd1, &fd2],
            );
            (f0, f1, f2) = (fd0, fd1, fd2);

            // if ate bit is 1, we need to add the point, else we need to subtract the point
        }
    }

    let time = time::Instant::now();

    // compute all states
    let mut compute_ctx = RawProof::mock_proof().into();
    compute_states(&ctx, &mut compute_ctx);
    {
        let lock_guard = ctx.graph.lock().unwrap();
        for i in 0..5 {
            let node = lock_guard
                .get_node(format!("groth16_verifierMSM{}_31_msm_acc", i))
                .unwrap();
            let state = &node.attributes.as_ref().unwrap().state;
            let msm_result = state.get_g1();
            info!("step {}, msm_result: {:?}", i, msm_result);
        }
    }

    info!("the cost time of computing states: {:?}", time.elapsed());

    ctx.write_local("/Users/yufengzhang/Workplace/bitlayer/graphml2mermaid/graph.graphml")
        .expect("write graph fail");
}
