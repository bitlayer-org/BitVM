use super::assigner::BCAssigner;
use super::segment::*;
use super::elements::*;
use super::elements::DataType::*;

use crate::bigint::BigIntImpl;
// utils for push fields into stack
use crate::bn254::ell_coeffs::EllCoeff;
use crate::bn254::ell_coeffs::G2Prepared;
use crate::bn254::fq::bigint_to_u32_limbs;
use crate::bn254::fr::Fr;
use crate::bn254::{fq12::Fq12, fq2::Fq2};
use crate::bn254::utils::*;

use ark_ec::{bn::BnConfig, AffineRepr};
use ark_ff::Field;
use ark_ff::{AdditiveGroup, BigInt};
use num_bigint::BigUint;

use crate::{
    bn254::{fp254impl::Fp254Impl, fq::Fq},
    treepp::*,
};

fn make_tc<T: BCAssigner>(assigner: &mut T, c:(ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2), i:usize, j:usize, k: &mut Vec<usize>) -> (Fq2Type, Fq2Type, Fq2Type) {
    let mut tc0 = Fq2Type::new(assigner, &format!("constant_{}_{}_{}_init", i, j, k[j]));
    tc0.fill_with_data(Fq2Data(c.0));
    let mut tc1 = Fq2Type::new(assigner, &format!("constant_{}_{}_{}_init", i, j, k[j]));
    tc1.fill_with_data(Fq2Data(c.1));
    let mut tc2 = Fq2Type::new(assigner, &format!("constant_{}_{}_{}_init", i, j, k[j]));
    tc2.fill_with_data(Fq2Data(c.2));

    k[j] += 1;
    
    (tc0,tc1,tc2)
}

pub fn collect_line_coeffs_stable<T: BCAssigner>(
    assigner: &mut T,
    constants: Vec<G2Prepared>,
) -> (Vec<Vec<Vec<(ark_bn254::Fq2, ark_bn254::Fq2, ark_bn254::Fq2)>>>,Vec<Vec<Vec<(Fq2Type, Fq2Type, Fq2Type)>>>) {
    let mut constant_iters = constants
        .iter()
        .map(|item| item.ell_coeffs.iter())
        .collect::<Vec<_>>();
    let mut all_line_coeffs = vec![];
    let mut all_line_coeffs_tc = vec![];

    let mut k: Vec<usize> = vec![0,0,0,0];
    for i in (1..ark_bn254::Config::ATE_LOOP_COUNT.len()).rev() {
        let mut line_coeffs = vec![];
        let mut line_coeffs_tc = vec![];

        for j in 0..constants.len() {
            // double line coeff
            let mut line_coeff = vec![];
            let mut line_coeff_tc = vec![];

            let c = *constant_iters[j].next().unwrap();
            line_coeff.push(c);
            let tc = make_tc(assigner, c, all_line_coeffs.len(), j, &mut k);
            line_coeff_tc.push(tc);
            // add line coeff
            if ark_bn254::Config::ATE_LOOP_COUNT[i - 1] == 1
                || ark_bn254::Config::ATE_LOOP_COUNT[i - 1] == -1
            {
                let c = *constant_iters[j].next().unwrap();
                line_coeff.push(c);
                let tc = make_tc(assigner, c, all_line_coeffs.len(), j, &mut k);
                line_coeff_tc.push(tc);
            }
            // line coeff for single point
            line_coeffs.push(line_coeff);
            line_coeffs_tc.push(line_coeff_tc);            
        }
        // line coeffs for all points
        all_line_coeffs.push(line_coeffs);
        all_line_coeffs_tc.push(line_coeffs_tc);

    }
    {
        let mut line_coeffs = vec![];
        let mut line_coeffs_tc = vec![];
        for j in 0..constants.len() {
            // add line coeff
            let c = *constant_iters[j].next().unwrap();
            line_coeffs.push(vec![c]);
            let tc = make_tc(assigner, c, all_line_coeffs.len(), j, &mut k);
            line_coeffs_tc.push(vec![tc]);

        }
        all_line_coeffs.push(line_coeffs);
        all_line_coeffs_tc.push(line_coeffs_tc);
    }
    {
        let mut line_coeffs = vec![];
        let mut line_coeffs_tc = vec![];

        for j in 0..constants.len() {
            // add line coeff
            let c = *constant_iters[j].next().unwrap();
            line_coeffs.push(vec![c]);
            let tc = make_tc(assigner, c, all_line_coeffs.len(), j, &mut k);
            line_coeffs_tc.push(vec![tc]);
        }
        all_line_coeffs.push(line_coeffs);
        all_line_coeffs_tc.push(line_coeffs_tc);

    }
    for i in 0..constant_iters.len() {
        assert_eq!(constant_iters[i].next(), None);
    }
    assert_eq!(
        all_line_coeffs.len(),
        ark_bn254::Config::ATE_LOOP_COUNT.len() - 1 + 2
    );
    assert_eq!(
        all_line_coeffs_tc.len(),
        ark_bn254::Config::ATE_LOOP_COUNT.len() - 1 + 2
    );
    (all_line_coeffs, all_line_coeffs_tc)
}



pub fn hinted_check_tangent_line_stable(
    t: ark_bn254::G2Affine,
    c3: ark_bn254::Fq2,
    c4: ark_bn254::Fq2,
) -> (Script, Vec<Hint>) {
    let mut hints = Vec::new();

    // let (hinted_script1, hint1) = Fq2::hinted_mul_by_constant(t.y.double(), &c3);
    let (hinted_script1, hint1) = Fq2::hinted_mul(2, t.y.double(), 0, c3);
    let (hinted_script2, hint2) = Fq2::hinted_square(t.x);
    let (hinted_script3, hint3) = hinted_check_line_through_point_stable(t.x, c3, c4);
    
    // [c3(2),c4(2),t(4) ]
    let script_lines = vec![
        // alpha * (2 * T.y) = 3 * T.x^2
        Fq2::copy(0),
        Fq2::double(0),
        // [c3(2),c4(2),t(4),t.y*2 (2)]
        Fq2::copy(8),
        // [c3(2),c4(2),t(4),t.y*2 (2), c3(2)]
        hinted_script1,
        // [c3(2),c4(2), T.x(2), T.y(2), alpha * 2 * T.y (2)]
        Fq2::copy(4),
        // [c3(2),c4(2), T.x(2), T.y(2), alpha * 2 * T.y (2), T.x(2)]
        hinted_script2,
        // [c3(2),c4(2), T.x(2), T.y(2), alpha * 2 * T.y (2), T.x^2(2)]
        Fq2::copy(0),
        // [c3(2),c4(2), T.x(2), T.y(2), alpha * 2 * T.y (2), T.x^2(2), T.x^2(2) ]
        Fq2::double(0),
        // [c3(2),c4(2), T.x(2), T.y(2), alpha * 2 * T.y (2), T.x^2(2), 2 * T.x^2(2) ]
        Fq2::add(2, 0),
        // [c3(2),c4(2), T.x(2), T.y(2), alpha * 2 * T.y(2), 3 * T.x^2(2)]
        Fq2::neg(0),
        Fq2::add(2, 0),
        Fq2::push_zero(),
        Fq2::equalverify(),
        // [c3(2),c4(2), T.x(2), T.y(2)]

        // check: T.y - alpha * T.x - bias = 0
        hinted_script3,
        // [c3(2),c4(2)]
    ];

    let mut script = script! {};
    for script_line in script_lines {
        script = script.push_script(script_line.compile());
    }
    hints.extend(hint1);
    hints.extend(hint2);
    hints.extend(hint3);

    (script, hints)
}


pub fn hinted_check_line_through_point_stable(
    x: ark_bn254::Fq2,
    c3: ark_bn254::Fq2,
    c4: ark_bn254::Fq2,
) -> (Script, Vec<Hint>) {
    let mut hints: Vec<Hint> = Vec::new();

    // let (hinted_script1, hint1) = Fq2::hinted_mul_by_constant(x, &c3);
    let (hinted_script1, hint1) = Fq2::hinted_mul(2, x, 0, c3);

    let script_lines = vec![
        // [c3, c4, x, y]
        Fq2::roll(2),
        // [c3, c4, y, x]
        Fq2::copy(6),
        // [c3, c4, y, x,c3]
        hinted_script1,
        // [c3, c4, y, alpha * x]
        Fq2::neg(0),
        // [c3, c4, y, -alpha * x]
        Fq2::add(2, 0),
        // [c3, c4, y - alpha * x]
        Fq2::copy(2), // fq2_push_not_montgomery(c4),
        // [c3, c4, y - alpha * x, -bias]
        Fq2::add(2, 0),
        // [c3, c4, y - alpha * x - bias]
        Fq2::push_zero(),
        // [c3, c4, y - alpha * x - bias, 0]
        Fq2::equalverify(),
        // [c3, c4]
    ];

    let mut script = script! {};
    for script_line in script_lines {
        script = script.push_script(script_line.compile());
    }
    hints.extend(hint1);

    (script, hints)
}


pub fn hinted_affine_double_line_stable(
    tx: ark_bn254::Fq2,
    c3: ark_bn254::Fq2,
    c4: ark_bn254::Fq2,
) -> (Script, Vec<Hint>) {
    let mut hints = Vec::new();

    let (hinted_script0, hint0) = Fq2::hinted_square(c3);
    let (hinted_script1, hint1) = Fq2::hinted_mul(4, c3, 0, c3.square() - tx - tx);

    //[c3(2), c4(2), t.x(2)]
    let script_lines = vec![
        Fq2::double(0),
        Fq2::neg(0),
        // [c3(2), c4(2), - 2 * T.x(2)]
        Fq2::copy(4),// fq2_push_not_montgomery(c3),
        Fq2::copy(0),
        hinted_script0, // fq2_push_not_montgomery(c3.square()),
        // [c3(2), c4(2), - 2 * T.x, alpha, alpha^2]
        Fq2::add(4, 0),
        Fq2::copy(0),
        // [c3(2), c4(2), alpha, x', x']
        hinted_script1,
        Fq2::neg(0),
        // [c3(2), c4(2), x', -alpha * x']
        Fq2::copy(4),//fq2_push_not_montgomery(c4),
        // [c3(2), c4(2), x', -alpha * x', c4(2)]
        Fq2::add(2, 0),
        // [c3(2), c4(2), x', y']
    ];

    let mut script = script! {};
    for script_line in script_lines {
        script = script.push_script(script_line.compile());
    }
    hints.extend(hint0);
    hints.extend(hint1);

    (script, hints)
}


pub fn hinted_check_chord_line_stable(
    t: ark_bn254::G2Affine,
    q: ark_bn254::G2Affine,
    c3: ark_bn254::Fq2,
    c4: ark_bn254::Fq2,
) -> (Script, Vec<Hint>) {
    let mut hints = Vec::new();

    let (script1, hint1) = hinted_check_line_through_point_stable(q.x, c3, c4);
    let (script2, hint2) = hinted_check_line_through_point_stable(t.x, c3, c4);

     
    //[c3(2),c4(2),t(4),q(4)]
     let script_lines = vec![
        Fq2::copy(10),
        // [c3(2),c4(2),t(4),q(4),c3(2)]
        Fq2::copy(10),
        // [c3(2),c4(2),t(4),q(4),c3(2),c4(2)]
        Fq2::roll(6),
        Fq2::roll(6),
        //[c3(2),c4(2),t(4),c3(2),c4(2),q(4)]
        script1,
        // // [c3(2),c4(2),t4(4),c3(2),c4(2)]
        Fq2::roll(6),
        Fq2::roll(6),
        // [c3(2),c4(2),c3(2),c4(2),t4(4)]
        script2,
        // [c3(2),c4(2),c3(2),c4(2)]
        Fq2::drop(),
        Fq2::drop(),
        // [c3(2),c4(2)]
    ];

    let mut script = script! {};
    for script_line in script_lines {
        script = script.push_script(script_line.compile());
    }

    hints.extend(hint1);
    hints.extend(hint2);

    (script, hints)
}


pub fn hinted_affine_add_line_stable(
    tx: ark_bn254::Fq2,
    qx: ark_bn254::Fq2,
    c3: ark_bn254::Fq2,
    c4: ark_bn254::Fq2,
) -> (Script, Vec<Hint>) {
    let mut hints = Vec::new();
    let (hinted_script0, hint0) = Fq2::hinted_square(c3);
    let (hinted_script1, hint1) = Fq2::hinted_mul(4, c3, 0, c3.square() - tx - qx);

    let script_lines = vec![
        // [c3, c4, T.x, Q.x]
        Fq2::neg(0),
        // [c3, c4,T.x, -Q.x]
        Fq2::roll(2),
        // [c3, c4,-Q.x, T.x]
        Fq2::neg(0),
        // [c3, c4, -Q.x. -T.x]
        Fq2::add(2, 0),
        // [c3, c4, -T.x - Q.x]
        Fq2::copy(4), // fq2_push_not_montgomery(c3),
        // [c3, c4, -T.x - Q.x, alpha]
        Fq2::copy(0),
        hinted_script0, // fq2_push_not_montgomery(c3.square()),
        // [c3, c4, -T.x - Q.x, alpha, alpha^2]
        // calculate x' = alpha^2 - T.x - Q.x
        Fq2::add(4, 0),
        // [c3, c4, alpha, x']
        Fq2::copy(0),
        // [c3, c4, alpha, x', x']
        hinted_script1,
        // [c3, c4, x', alpha * x']
        Fq2::neg(0),
        // [c3, c4, x', -alpha * x']
        Fq2::copy(4),// fq2_push_not_montgomery(c4),
        // [x', -alpha * x', -bias]
        // compute y' = -bias - alpha * x'
        Fq2::add(2, 0),
        // [c3, c4, x', y']
    ];

    let mut script = script! {};
    for script_line in script_lines {
        script = script.push_script(script_line.compile());
    }
    hints.extend(hint0);
    hints.extend(hint1);

    (script, hints)
}

// #[cfg(test)]
// mod test {
//     use crate::{execute_script_with_inputs,execute_script};
//     use crate::bn254::*;
//     use crate::bn254::utils::*;
//     use crate::bn254::fq::Fq;
//     use crate::bn254::fq2::Fq2;
//     use crate::bn254::fq6::Fq6;
//     use crate::bn254::fq12::Fq12;

//     use ark_ff::AdditiveGroup;
//     use ark_ff::Field;
//     use ark_std::UniformRand;
//     use bitcoin_script::script;
//     use num_traits::One;
//     use rand::SeedableRng;
//     use rand_chacha::ChaCha20Rng;
    

    
//     #[test]
//     fn test_hinted_check_tangent_line() {
//         let mut prng = ChaCha20Rng::seed_from_u64(0);
//         let t = ark_bn254::G2Affine::rand(&mut prng);
//         let two_inv = ark_bn254::Fq::one().double().inverse().unwrap();
//         let three_div_two = (ark_bn254::Fq::one().double() + ark_bn254::Fq::one()) * two_inv;
//         let mut alpha = t.x.square();
//         alpha /= t.y;
//         alpha.mul_assign_by_fp(&three_div_two);
//         // -bias
//         let bias_minus = alpha * t.x - t.y;
//         assert_eq!(alpha * t.x - t.y, bias_minus);

//         let (hinted_check_line, hints) = hinted_check_line_through_point(t.x, alpha, bias_minus);

//         let script = script! {
//             for hint in hints {
//                 { hint.push() }
//             }
//             { fq2_push_not_montgomery(t.x) }
//             { fq2_push_not_montgomery(t.y) }
//             { hinted_check_line.clone() }
//             OP_TRUE
//         };
//         let exec_result = execute_script(script);
//         assert!(exec_result.success);
//         println!(
//             "hinted_check_line: {} @ {} stack",
//             hinted_check_line.len(),
//             exec_result.stats.max_nb_stack_items
//         );
//     }



//     #[test]
//     fn test_hinted_affine_double_line() {
//         // slope: alpha = 3 * x^2 / 2 * y
//         // intercept: bias = y - alpha * x
//         // x' = alpha^2 - 2 * x
//         // y' = -bias - alpha * x'
//         let mut prng = ChaCha20Rng::seed_from_u64(0);
//         let t = ark_bn254::G2Affine::rand(&mut prng);
//         let two_inv = ark_bn254::Fq::one().double().inverse().unwrap();
//         let three_div_two = (ark_bn254::Fq::one().double() + ark_bn254::Fq::one()) * two_inv;
//         let mut alpha = t.x.square();
//         alpha /= t.y;
//         alpha.mul_assign_by_fp(&three_div_two);
//         // -bias
//         let bias_minus = alpha * t.x - t.y;

//         let x = alpha.square() - t.x.double();
//         let y = bias_minus - alpha * x;
//         let (hinted_double_line, hints) = hinted_affine_double_line(t.x, alpha, bias_minus);
//         println!("hinted_affine_double_line: {}", hinted_double_line.len());

//         let script = script! {
//             for hint in hints {
//                 { hint.push() }
//             }
//             { fq2_push_not_montgomery(t.x) }
//             { hinted_double_line }
//             // [x']
//             { fq2_push_not_montgomery(y) }
//             // [x', y', y]
//             { Fq2::equalverify() }
//             // [x']
//             { fq2_push_not_montgomery(x) }
//             // [x', x]
//             { Fq2::equalverify() }
//             // []
//             OP_TRUE
//             // [OP_TRUE]
//         };
//         assert!(execute_script(script).success);
//     }


//     #[test]
//     fn test_hinted_affine_add_line() {
//         // alpha = (t.y - q.y) / (t.x - q.x)
//         // bias = t.y - alpha * t.x
//         // x' = alpha^2 - T.x - Q.x
//         // y' = -bias - alpha * x'
//         let mut prng = ChaCha20Rng::seed_from_u64(0);
//         let t = ark_bn254::G2Affine::rand(&mut prng);
//         let q = ark_bn254::G2Affine::rand(&mut prng);
//         let alpha = (t.y - q.y) / (t.x - q.x);
//         // -bias
//         let bias_minus = alpha * t.x - t.y;

//         let x = alpha.square() - t.x - q.x;
//         let y = bias_minus - alpha * x;
//         let (hinted_add_line, hints) = hinted_affine_add_line(t.x, q.x, alpha, bias_minus);

//         let script = script! {
//             for hint in hints {
//                 { hint.push() }
//             }
//             { fq2_push_not_montgomery(t.x) }
//             { fq2_push_not_montgomery(q.x) }
//             { hinted_add_line.clone() }
//             // [x']
//             { fq2_push_not_montgomery(y) }
//             // [x', y', y]
//             { Fq2::equalverify() }
//             // [x']
//             { fq2_push_not_montgomery(x) }
//             // [x', x]
//             { Fq2::equalverify() }
//             // []
//             OP_TRUE
//             // [OP_TRUE]
//         };
//         let exec_result = execute_script(script);
//         assert!(exec_result.success);
//         println!(
//             "hinted_add_line: {} @ {} stack",
//             hinted_add_line.len(),
//             exec_result.stats.max_nb_stack_items
//         );
//     }

//     #[test]
//     fn test_hinted_check_chord_line() {
//         let mut prng = ChaCha20Rng::seed_from_u64(0);
//         let t = ark_bn254::G2Affine::rand(&mut prng);
//         let q = ark_bn254::G2Affine::rand(&mut prng);
//         let alpha = (t.y - q.y) / (t.x - q.x);
//         // -bias
//         let bias_minus = alpha * t.x - t.y;
//         assert_eq!(alpha * t.x - t.y, bias_minus);
//         let (hinted_check_line, hints) = hinted_check_chord_line(t, q, alpha, bias_minus);

//         let script = script! {
//             for hint in hints {
//                 { hint.push() }
//             }
//             { fq2_push_not_montgomery(t.x) }
//             { fq2_push_not_montgomery(t.y) }
//             { fq2_push_not_montgomery(q.x) }
//             { fq2_push_not_montgomery(q.y) }
//             { hinted_check_line.clone() }
//             OP_TRUE
//         };
//         let exec_result = execute_script(script);
//         assert!(exec_result.success);
//         println!(
//             "hinted_check_line: {} @ {} stack",
//             hinted_check_line.len(),
//             exec_result.stats.max_nb_stack_items
//         );
//     }
// }