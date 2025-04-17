use crate::autochunker::computation_graph::*;
use crate::autochunker::compute_ctx::*;
use crate::autochunker::functions::*;
use crate::{define_input, define_overide_script, define_script};
use std::sync::Arc;
use std::time;
// use utils::*;
use crate::autochunker::intermediate_state::*;
use crate::autochunker::primitve_functions::*;
use crate::autochunker::proof::*;
use ark_bn254::Config as Bn254Config;
use ark_bn254::{Fq, Fq12, Fq2, Fq6};
use ark_ec::bn::BnConfig;
use fuzzy_matcher::skim::SkimMatcherV2;
use fuzzy_matcher::FuzzyMatcher;
use log::debug;
use log::info;
use log::warn;
use paste::paste;
use rayon::prelude::*;

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
    let mut ctx = GraphContext::new("groth16_verifier");
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
    //
    // Phase 2: Pre Computing

    define_input!(ctx, p2, G1, extract_p2());
    define_script!(ctx, _p2_check, CheckValid, [p2], check_g1_point());
    define_script!(ctx, p2_tweak, G1, [p2], tweak_point());

    define_input!(ctx, p4, G1, extract_p4());
    define_script!(ctx, _p4_check, CheckValid, [p4], check_g1_point());
    define_script!(ctx, p4_tweak, G1, [p4], tweak_point());

    define_script!(ctx, p3_tweak, G1, [p3], tweak_point());

    define_input!(ctx, q4x, Fq2, extract_q4x());
    define_input!(ctx, q4y, Fq2, extract_q4y());
    define_script!(ctx, q4y_neg, Fq2, [q4y], fq2_neg());

    // saying c = 1 + a J, c_inv will be 1 - a J, because c * c_inv = (1+a^2) + 0 J = 1
    // so we can use neg(c) to represent the inverse of c
    define_input!(ctx, c0, Fq2, extract_c(0));
    define_input!(ctx, c1, Fq2, extract_c(1));
    define_input!(ctx, c2, Fq2, extract_c(2));
    define_script!(ctx, c_inv0, Fq2, [c0], neg_fq2());
    define_script!(ctx, c_inv1, Fq2, [c1], neg_fq2());
    define_script!(ctx, c_inv2, Fq2, [c2], neg_fq2());

    // define t4x and t4y
    let (mut t4x, mut t4y) = (q4x.clone(), q4y.clone());

    // =========================================================================================================
    //
    // Phase 3: Pairing Computation

    // 2.1 precompute point in G1 for the optimization in https://eprint.iacr.org/2013/722.pdf
    // y_p' -> 1 / y_p, x_p' -> - y_p / x_p
    // chunk_precompute_p disprovable(true) script 340846 stack 654
    let (mut f0, mut f1, mut f2) = {
        let mut ctx = ctx.inner_context("Pairing");

        let (mut f0, mut f1, mut f2) = (c_inv0.clone(), c_inv1.clone(), c_inv2.clone());

        for i in (1..Bn254Config::ATE_LOOP_COUNT.len()).rev() {
            let mut ctx = ctx.inner_context(&format!("ate_loop_{}", i));

            // square f
            // TODO: square fq12
            [f0, f1, f2] = new_square_fq12(
                &mut ctx.inner_context("square_f"),
                [&f0, &f1, &f2],
                &Selector::Loop(i, LoopSelector::SquareF),
            );

            // evaluate t4 by tagent line
            let res = t4_double_by_tangent_line(
                &mut ctx.inner_context("double_t4"),
                &t4x,
                &t4y,
                &p4_tweak,
                &Selector::Loop(i, LoopSelector::DoublePoint),
            );
            (t4x, t4y) = (res.0, res.1);
            let (t4_c0, t4_c1) = (res.2, res.3);

            // evaluate t2 and t3 by precomputed tangent line
            let (t3_c0, t3_c1, t2_c0, t2_c1) = evaluate_t2_and_t3(
                &mut ctx.inner_context("double_t2_t3"),
                &p3_tweak,
                &p2_tweak,
                Selector::Loop(i, LoopSelector::DoublePoint),
            );

            // line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
            let eval_multi = line_evaluate_multiplication(
                &mut ctx.inner_context("double_eval"),
                &t4_c0,
                &t4_c1,
                &t3_c0,
                &t3_c1,
                &t2_c0,
                &t2_c1,
                &Selector::Loop(i, LoopSelector::MultiSquareEval),
            );

            // (eval_multi_f0, eval_multi_f1, eval_multi_f2) = (f0, f1, f2) * (eval_multi);
            [f0, f1, f2] = new_mul_fq12(
                &mut ctx.inner_context("double_multi"),
                [&f0, &f1, &f2],
                [&eval_multi.0, &eval_multi.1, &eval_multi.2],
                &Selector::Loop(i, LoopSelector::MultiSquareEval),
            );

            // if ate bit is 1, we need to multiply the c, else we need to multiply the c_inv
            let bit = Bn254Config::ATE_LOOP_COUNT[i - 1];

            if bit == 0 {
                continue;
            }

            let (d0, d1, d2) = if bit == -1 {
                (&c0, &c1, &c2)
            } else {
                (&c_inv0, &c_inv1, &c_inv2)
            };

            // (f0, f1, f2) = (f0, f1, f2) * (d0, d1, d2)
            [f0, f1, f2] = new_mul_fq12(
                &mut ctx.inner_context("c_multi"),
                [&f0, &f1, &f2],
                [d0, d1, d2],
                &Selector::Loop(i, LoopSelector::MultiC),
            );

            // if ate bit is 1, we need to add the point, else we need to subtract the point
            let res = t4_add_by_chord_line(
                &mut ctx.inner_context("add_t4"),
                &t4x,
                &t4y,
                &q4x,
                &q4y,
                &q4y_neg,
                &p4_tweak,
                bit,
                &Selector::Loop(i, LoopSelector::AddPoint),
            );
            (t4x, t4y) = (res.0, res.1);
            let (t4_c0, t4_c1) = (res.2, res.3);

            // evaluate t2 and t3 by precomputed chord line
            let (t3_c0, t3_c1, t2_c0, t2_c1) = evaluate_t2_and_t3(
                &mut ctx.inner_context("add_t2_t3"),
                &p3_tweak,
                &p2_tweak,
                Selector::Loop(i, LoopSelector::AddPoint),
            );

            // line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
            let eval_multi = line_evaluate_multiplication(
                &mut ctx.inner_context("add_eval"),
                &t4_c0,
                &t4_c1,
                &t3_c0,
                &t3_c1,
                &t2_c0,
                &t2_c1,
                &Selector::Loop(i, LoopSelector::MultiAddEval),
            );

            // (f0, f1, f2) = (f0, f1, f2) * (eval_multi);
            [f0, f1, f2] = new_mul_fq12(
                &mut ctx.inner_context("add_multi"),
                [&f0, &f1, &f2],
                [&eval_multi.0, &eval_multi.1, &eval_multi.2],
                &Selector::Loop(i, LoopSelector::MultiAddEval),
            );
        }
        (f0, f1, f2)
    };

    // =========================================================================================================
    //
    // Phase 4: Final Computation

    {
        let mut ctx = ctx.inner_context("final");
        // frobinus mapping: c_inv^p
        let cinv_p = fq12_frobinus_map(&mut ctx.inner_context("p"), [&c_inv0, &c_inv1, &c_inv2], 1);
        // froninus mapping: c^2p
        let c_p2 = fq12_frobinus_map(&mut ctx.inner_context("2p"), [&c0, &c1, &c2], 2);
        // forninus mapping: c_inv^3p
        let cinv_p3 =
            fq12_frobinus_map(&mut ctx.inner_context("3p"), [&c_inv0, &c_inv1, &c_inv2], 3);

        // f = f * c_inv^p
        [f0, f1, f2] = new_mul_fq12(
            &mut ctx.inner_context("fp"),
            [&f0, &f1, &f2],
            [&cinv_p[0], &cinv_p[1], &cinv_p[2]],
            &Selector::CFrob(1),
        );

        // f = f * c^2p
        [f0, f1, f2] = new_mul_fq12(
            &mut ctx.inner_context("fp2"),
            [&f0, &f1, &f2],
            [&c_p2[0], &c_p2[1], &c_p2[2]],
            &Selector::CFrob(2),
        );

        // f = f * c_inv^3p
        [f0, f1, f2] = new_mul_fq12(
            &mut ctx.inner_context("fp3"),
            [&f0, &f1, &f2],
            [&cinv_p3[0], &cinv_p3[1], &cinv_p3[2]],
            &Selector::CFrob(3),
        );

        // (q4x_p, q4y_p) = (q4x, q4y)p
        let (q4x_p, q4y_p) = frob_point_mul_by_char(&mut ctx.inner_context("q4_p"), &q4x, &q4y);
        // (q4x_p2, q4y_p2) = (q4x, q4y)2p.neg()
        let res = frob_point_mul_by_2char_neg(&mut ctx.inner_context("q4_2p"), &q4x, &q4y);
        let q4x_p2 = res.0;
        let q4y_p2 = res.1;
        // (q4x_p3, q4y_p3) = (q4x, q4y)3p
        let (q4x_p3, q4y_p3) = frob_point_mul_by_char3(&mut ctx.inner_context("q4_3p"), &q4x, &q4y);

        // t4 = t4 + (q4x_p, q4y_p)
        let res = t4_add_by_chord_line_with_frob(
            &mut ctx.inner_context("frob_t4"),
            &t4x,
            &t4y,
            &q4x_p,
            &q4y_p,
            &p4_tweak,
            &Selector::FrobPoint(1),
        );
        (t4x, t4y) = (res.0, res.1);
        let (t4_c0, t4_c1) = (res.2, res.3);

        // evaluate t2 and t3 by precomputed chord line
        let (t3_c0, t3_c1, t2_c0, t2_c1) = evaluate_t2_and_t3(
            &mut ctx.inner_context("frob_t2_t3"),
            &p3_tweak,
            &p2_tweak,
            Selector::FrobPoint(1),
        );

        // line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
        let eval_multi = line_evaluate_multiplication(
            &mut ctx.inner_context("frob_eval"),
            &t4_c0,
            &t4_c1,
            &t3_c0,
            &t3_c1,
            &t2_c0,
            &t2_c1,
            &Selector::MultiFrobEval(1),
        );

        // (eval_multi_f0, eval_multi_f1, eval_multi_f2) = (f0, f1, f2) * (eval_multi);
        [f0, f1, f2] = new_mul_fq12(
            &mut ctx.inner_context("frob_multi"),
            [&f0, &f1, &f2],
            [&eval_multi.0, &eval_multi.1, &eval_multi.2],
            &Selector::MultiFrobEval(1),
        );

        // t4 = t4 + (q4x_p2, q4y_p2)
        let res = t4_add_by_chord_line_with_frob(
            &mut ctx.inner_context("frob2_t4"),
            &t4x,
            &t4y,
            &q4x_p2,
            &q4y_p2,
            &p4_tweak,
            &Selector::FrobPoint(2),
        );
        (t4x, t4y) = (res.0, res.1);
        let (t4_c0, t4_c1) = (res.2, res.3);

        // evaluate t2 and t3 by precomputed chord line
        let (t3_c0, t3_c1, t2_c0, t2_c1) = evaluate_t2_and_t3(
            &mut ctx.inner_context("frob2_t2_t3"),
            &p3_tweak,
            &p2_tweak,
            Selector::FrobPoint(2),
        );

        // line evaluation multiplication (t4_c0, t4_c1, 0) * (t3_c0, t3_c1, 0) * (t2_c0, t2_c1, 0)
        let eval_multi = line_evaluate_multiplication(
            &mut ctx.inner_context("frob2_eval"),
            &t4_c0,
            &t4_c1,
            &t3_c0,
            &t3_c1,
            &t2_c0,
            &t2_c1,
            &Selector::MultiFrobEval(2),
        );

        // (eval_multi_f0, eval_multi_f1, eval_multi_f2) = (f0, f1, f2) * (eval_multi);
        [f0, f1, f2] = new_mul_fq12(
            &mut ctx.inner_context("frob2_multi"),
            [&f0, &f1, &f2],
            [&eval_multi.0, &eval_multi.1, &eval_multi.2],
            &Selector::MultiFrobEval(2),
        );

        // check (t4x, t4y).neg() == 3q * (q4x, q4y)
        define_script!(ctx, t4y_neg, Fq2, [t4y], fq2_neg());
        let t4x_neg = t4x;
        define_script!(
            ctx,
            _check_x,
            CheckValid,
            [t4x_neg, q4x_p3],
            check_fq2_equal()
        );
        define_script!(
            ctx,
            _check_y,
            CheckValid,
            [t4y_neg, q4y_p3],
            check_fq2_equal()
        );

        // check (f0, f1, f2).neg() + fixed
        define_input!(ctx, f_fixed0, Fq2, extract_p1q1(0));
        define_input!(ctx, f_fixed1, Fq2, extract_p1q1(1));
        define_input!(ctx, f_fixed2, Fq2, extract_p1q1(2));
        define_script!(ctx, f0_neg, Fq2, [f0], fq2_neg());
        define_script!(ctx, f1_neg, Fq2, [f1], fq2_neg());
        define_script!(ctx, f2_neg, Fq2, [f2], fq2_neg());
        define_script!(
            ctx,
            _check_f0,
            CheckValid,
            [f0_neg, f_fixed0],
            check_fq2_equal()
        );
        define_script!(
            ctx,
            _check_f1,
            CheckValid,
            [f1_neg, f_fixed1],
            check_fq2_equal()
        );
        define_script!(
            ctx,
            _check_f2,
            CheckValid,
            [f2_neg, f_fixed2],
            check_fq2_equal()
        );
    }

    let time = time::Instant::now();

    // compute all states
    let compute_ctx = RawProof::mock_proof().into();
    compute_states(&ctx, &compute_ctx);

    show_all_states(&ctx);

    // cache script info
    generate_script_cache(&ctx, &compute_ctx);

    // merge and organize scripts

    // query state
    {
        for i in 0..5 {
            info!(
                "step {}, msm_result: {:?}",
                i,
                get_state(&ctx, &format!("groth16_verifier_MSM_{}_31_msm_acc", i))
            );
        }

        let t4_c0 = get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_t4_c0").get_fq2();
        let t4_c1 = get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_t4_c1").get_fq2();
        let t3_c0 =
            get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_t2_t3_t3_c0").get_fq2();
        let t3_c1 =
            get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_t2_t3_t3_c1").get_fq2();
        let t2_c0 =
            get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_t2_t3_t2_c0").get_fq2();
        let t2_c1 =
            get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_t2_t3_t2_c1").get_fq2();
        let g0 = get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_eval_g0").get_fq2();
        let g1 = get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_eval_g1").get_fq2();
        let g2 = get_state(&ctx, "groth16_verifier_Pairing_ate_loop_64_add_eval_g2").get_fq2();

        let result = Fq12::new(Fq6::from(1), Fq6::new(t4_c0, t4_c1, Fq2::from(0)))
            * Fq12::new(Fq6::from(1), Fq6::new(t3_c0, t3_c1, Fq2::from(0)))
            * Fq12::new(Fq6::from(1), Fq6::new(t2_c0, t2_c1, Fq2::from(0)));
        assert_eq!(result.c1 / result.c0, Fq6::new(g0, g1, g2));

        for i in 0..3 {
            info!(
                "f_final: {:?}",
                get_state(&ctx, &format!("groth16_verifier_final__check_f{}", i))
            );
        }
    }

    info!("the cost time of computing states: {:?}", time.elapsed());

    ctx.write_local("/Users/yufengzhang/Workplace/bitlayer/graphml2mermaid/graph.graphml")
        .expect("write graph fail");
}

pub fn get_state(ctx: &GraphContext, name: &str) -> State {
    let lock_guard = ctx.graph.lock().unwrap();
    let node = match lock_guard.get_node(name.to_string()) {
        Some(node) => node,
        None => {
            // try fuzzy match
            let node_names = lock_guard.get_all_node_names();
            let matcher = SkimMatcherV2::default();

            // use Rayon to parallelize the fuzzy matching
            let result = node_names
                .par_iter()
                .filter_map(|item| matcher.fuzzy_match(item, name).map(|score| (item, score)))
                .max_by_key(|&(_, score)| score);

            if let Some((best_match, _)) = result {
                panic!(
                    "Node not found: {}, but best fuzzy match: '{}'",
                    name, best_match
                );
            } else {
                panic!("Node not found: {}", name);
            }
        }
    };
    node.attributes.clone().unwrap().state
}

pub fn show_all_states(ctx: &GraphContext) {
    let lock_guard = ctx.graph.lock().unwrap();
    for name in lock_guard.get_all_node_names() {
        let node = lock_guard.get_node(name.to_string()).unwrap();
        let state = node.attributes.clone().unwrap().state;
        match state {
            State::CheckValid(Some(x)) => {
                if !x {
                    panic!("{} state fail to check : {:?}", name, state);
                }
            }
            x => {
                if !x.is_filled() {
                    panic!("{} state are not filled: {:?}", name, x);
                }
                debug!("{} state: {:?}", name, x);
            }
        }
    }
}
