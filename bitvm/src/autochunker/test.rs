use std::time;

use crate::autochunker::computation_graph::*;
// use utils::*;
use crate::autochunker::intermediate_state::*;
use crate::autochunker::primitve_functions::*;
use crate::autochunker::proof::*;

use log::info;
use paste::paste;

// Define the `define_script` macro
macro_rules! define_input {
    ($context:ident, $name:tt, $state_type:ident, $func:expr) => {
        paste! {
            let state = State::[<new_ $state_type:lower>]();
            let var_name = $context.variable_prefix.clone() + &stringify!($name).to_owned();
            let $name = new_input(&mut $context.graph, var_name, state, $func);
        }
    };
}

macro_rules! define_script {
    // name hasn't been defined
    ($context: ident, $name: ident, $state_type:ident, [$($input:ident),*], $func:expr) => {
        let (function, script_size) = $func;
        let var_name = $context.variable_prefix.clone() + "_" + &stringify!($name).to_owned();
        let mut inputs = vec![];
        $(inputs.push($input.clone());)*
        paste!{
            let state = State::[<new_ $state_type:lower>]();
            let $name = new_script(
                &mut $context.graph,
                var_name,
                script_size,
                function,
                state,
                inputs,
            );
        }
    };
}

macro_rules! define_overide_script {
    // name has been defined and override
    ($context: ident, $name: ident, $state_type:ident, [$($input:ident),*], $func:expr) => {
        let (function, script_size) = $func;
        let var_name = $context.variable_prefix.clone() + "_" + &stringify!($name).to_owned();
        let mut inputs = vec![];
        $(inputs.push($input.clone());)*
        paste!{
            let state = State::[<new_ $state_type:lower>]();
            $name = new_script(
                &mut $context.graph,
                var_name,
                script_size,
                function,
                state,
                inputs,
            );
        }
    };
}

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
    {
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
    }

    // =========================================================================================================

    // Phase 2: Pairing Computation

    // 2.1 precompute point in G1 for the optimization in https://eprint.iacr.org/2013/722.pdf
    // y_p' -> 1 / y_p, x_p' -> - y_p / x_p
    // chunk_precompute_p disprovable(true) script 340846 stack 654
    {
        let mut ctx = ctx.inner_context("Pairing");
        define_input!(ctx, p2, G1, extract_p2());
        define_script!(ctx, p2_check, CheckValid, [p2], check_g1_point());
        define_script!(ctx, _p2_tweak, G1, [p2], tweak_point());

        define_input!(ctx, p4, G1, extract_p4());
        define_script!(ctx, _p4_check, CheckValid, [p4], check_g1_point());
        define_script!(ctx, p4_tweak, G1, [p4], tweak_point());
    }
    /*
    let p2_tweak = new_script(&mut graph, "p2_tweak".into(), 340846, vec![(&p2, G1_BYTES)]);

    let p4 = new_input(&mut graph, "P4(alias proof.a)".into());
    let p4_tweak = new_script(&mut graph, "p4_tweak".into(), 340846, vec![(&p4, G1_BYTES)]);

    let p3 = msm_acc;
    let p3_tweak = new_script(&mut graph, "p3_tweak".into(), 340301, vec![(&p3, G1_BYTES)]);

    // 2.2 check c \cdot c_inv is the identity
    // decompose c to "c0, c1, c2" and c_inv to "c_inv0, c_inv1, c_inv2"
    let c0 = new_input(&mut graph, "c0".into());
    let c1 = new_input(&mut graph, "c1".into());
    let c2 = new_input(&mut graph, "c2".into());
    let c_inv0 = new_script(&mut graph, "c_inv".into(), 1000, vec![(&c0, FQ2_BYTES)]);
    let c_inv1 = new_script(&mut graph, "c_inv".into(), 1000, vec![(&c1, FQ2_BYTES)]);
    let c_inv2 = new_script(&mut graph, "c_inv".into(), 1000, vec![(&c2, FQ2_BYTES)]);

    // 2.3 assign c to accumulator
    let (mut f0, mut f1, mut f2) = (c0, c1, c2);

    let q4x = new_input(&mut graph, "q4x".into());
    let q4y = new_input(&mut graph, "q4y".into());

    let (mut t4x, mut t4y) = (q4x, q4y);

    // loop of ATE_LOOP_COUNT
    for i in 1..65 {
        // square f
        [f0, f1, f2] = new_square_fq6(&mut graph, format!("square_f_loop_{}", i), [&f0, &f1, &f2]);

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

        // 2.4 caculation tangent line of t4
        let lambda = new_input(&mut graph, format!("t4_lambda_in_loop_{}", i));
        let v = new_input(&mut graph, format!("t4_v_in_loop_{}", i));
        // t4y = t4x \cdot \lambda + v
        let _check_tangent_line = new_script(
            &mut graph,
            format!("double_t4_check_line_through_point_in_loop_{}", i),
            193429,
            vec![(&t4x, FQ2_BYTES), (&lambda, FQ2_BYTES), (&v, FQ2_BYTES)],
        );
        // 3 \cdot t4x^2 \cdot \lambda = 2 \cdot y^2
        let _check_slope_of_line = new_script(
            &mut graph,
            format!("t4_check_slope_of_line_in_loop_{}", i),
            190871 + 137000,
            vec![(&t4x, FQ2_BYTES), (&t4y, FQ2_BYTES), (&lambda, FQ2_BYTES)],
        );
        // t4 = 2 (t4), double the point
        // t4x' = \lambda^2 - 2 \cdot t4x, t4y' = -b - \lambda * t4x'
        t4x = new_script(
            &mut graph,
            format!("t4x_double_in_loop_{}", i),
            137000,
            vec![(&t4x, FQ2_BYTES), (&lambda, FQ2_BYTES)],
        );
        t4y = new_script(
            &mut graph,
            format!("t4y_double_in_loop_{}", i),
            190871,
            vec![(&t4x, FQ2_BYTES), (&lambda, FQ2_BYTES), (&v, FQ2_BYTES)],
        );
        // evaluate the point by the line (divisor)
        let evaluate_t4_line = new_script(
            &mut graph,
            format!("double_evaluate_t4_in_loop_{}", i),
            271496,
            vec![(&p4_tweak, G1_BYTES), (&lambda, FQ2_BYTES), (&v, FQ2_BYTES)],
        );

        // 2.5 evaluate line of t3, whose slope and bias is fixed.
        // evaluate the point by the line (divisor)
        let evaluate_t3_line = new_script(
            &mut graph,
            format!("double_evaluate_t4_in_loop_{}", i),
            271496,
            vec![(&p3_tweak, G1_BYTES)],
        );

        // 2.6 evaluate line of t2, whose slope and bias is fixed.
        let evaluate_t2_line = new_script(
            &mut graph,
            format!("double_evaluate_t4_in_loop_{}", i),
            271496,
            vec![(&p3_tweak, G1_BYTES)],
        );
    }
    */

    let time = time::Instant::now();

    // compute all states
    compute_states(&ctx, RawProof::mock_proof().into());
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
