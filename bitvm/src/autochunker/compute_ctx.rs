use crate::autochunker::functions::mul_by_char;
use crate::autochunker::{intermediate_state::*, proof::RawProof};
use crate::bn254::ell_coeffs::{ell_affine, AffinePairing, BnAffinePairing, G2Prepared};
use crate::bn254::fp254impl::Fp254Impl;
use crate::bn254::utils::fq_to_bits;
use crate::groth16::constants::{LAMBDA, T};
use crate::groth16::offchain_checker::compute_c_wi;
use ark_bn254::Config;
use ark_bn254::Fq6Config;
use ark_bn254::{Fq, Fq12, Fq2, Fq6, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::bn::BnConfig;
use ark_ec::pairing::MillerLoopOutput;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, Field, One, PrimeField};
use ark_ff::{CyclotomicMultSubgroup, Fp6Config};
use ark_std::cfg_chunks_mut;
use bitcoin_script::{script, Script};
use core::ops::Neg;
use itertools::Itertools;
use log::{debug, error, info, warn};
use num_bigint::BigUint;
use std::collections::HashMap;
use std::sync::Arc;

use super::functions::mul_by_2char_neg;

pub type ComputeFn = Box<dyn Fn(&mut ComputeCtx, Vec<State>) -> State>;
pub type ScriptFn = Box<dyn Fn(&mut ComputeCtx, Vec<State>) -> (Script, Vec<Vec<u8>>)>;

#[derive(Debug, Clone)]
pub struct ComputeCtx {
    pub proof: RawProof,
    pub msm_points_from_pk: Vec<G1Affine>,
    pub msm_scalars: Vec<Fr>,
    pub vky0: G1Affine,
    pub p1q1: Fq6,                                  // immutable
    pub p2: G1Affine,                               // immutable
    pub p4: G1Affine,                               // immutable
    pub q4: G2Affine,                               // immutable
    pub q3: G2Affine,                               // immutable
    pub q2: G2Affine,                               // immutable
    pub tpoints: HashMap<TPointSelector, G2Affine>, // mutable
    pub f: HashMap<Selector, Fq6>,                  // mutable
    pub evaluate_p4: Option<Fq6>,                   // mutable, the result of evaluate line of p4
    pub evaluate_p3: Option<Fq6>,                   // mutable, the result of evaluate line of p3
    pub evaluate_p2: Option<Fq6>,                   // mutable, the result of evaluate line of p2
    pub c: Fq6,
    pub c_inv: Fq6,
}

impl From<RawProof> for ComputeCtx {
    fn from(raw_proof: RawProof) -> Self {
        info!("proof public inputs: {}", raw_proof.public.len());

        let mut msm_scalar = raw_proof.public.clone();
        msm_scalar.reverse();

        let mut msm_gs = raw_proof.vk.gamma_abc_g1.clone(); // vk.vk_pubs[0]
        msm_gs.reverse();

        let vky0 = msm_gs.pop().unwrap();

        let mut p3 = G1Projective::ZERO;

        p3 = p3 + vky0 * ark_bn254::Fr::ONE;

        for i in 0..raw_proof.public.len() {
            let result = msm_gs[i] * msm_scalar[i];
            debug!(
                "msm for {}, scalar {:?} x point {:?} = {:?}",
                i, msm_gs[i], msm_scalar[i], result
            );
            p3 += result;
            info!(
                "rawproof result of msm step {}: {:?}",
                i,
                p3.clone().into_affine()
            );
        }

        info!("rawproof result of msm: {:?}", p3.clone().into_affine());

        let p3 = p3.into_affine();

        let (p2, p1, p4) = (raw_proof.proof.c, raw_proof.vk.alpha_g1, raw_proof.proof.a);
        let (q3, q2, q1, q4) = (
            raw_proof.vk.gamma_g2.into_group().neg().into_affine(),
            raw_proof.vk.delta_g2.into_group().neg().into_affine(),
            -raw_proof.vk.beta_g2,
            raw_proof.proof.b,
        );
        let pairing = BnAffinePairing;
        let f_fixed = pairing.multi_miller_loop_affine([p1], [q1]).0;
        let f = pairing
            .multi_miller_loop_affine([p1, p2, p3, p4], [q1, q2, q3, q4])
            .0;
        let f_without_p1q1 = pairing
            .multi_miller_loop_affine([p2, p3, p4], [q2, q3, q4])
            .0;
        assert_eq!(f, f_fixed * f_without_p1q1);
        let (c, _) = compute_c_wi(f);
        let c_inv = c.inverse().unwrap();
        let result = f * (c_inv.pow(LAMBDA.to_u64_digits()));

        assert_eq!(result.c1, Fq6::ZERO);

        // check the result of pairing
        let mut f_map: HashMap<Selector, Fq6> = HashMap::new();
        let mut tpoint_map: HashMap<TPointSelector, G2Affine> = HashMap::new();
        let (mut t2, mut t3, mut t4) = (q2, q3, q4);

        let f = {
            let a = [p2, p3, p4];
            let b = [q2, q3, q4];

            let mut pairs: Vec<_> = a
                .into_iter()
                .zip_eq(b)
                .filter_map(|(p, q)| {
                    // if input q is projective coordinates, then we will enter `into` computing pairing mode
                    // otherwise if input q is affine coordinates, then we will enter `into` verifying pairing mode
                    let (p, q): (ark_ec::bn::G1Prepared<ark_bn254::Config>, G2Prepared) =
                        (p.into(), q.into());
                    match !p.is_zero() && !q.is_zero() {
                        true => Some((
                            -p.0.x / p.0.y,
                            p.0.y.inverse().unwrap(),
                            q.ell_coeffs.into_iter(),
                        )),
                        false => None,
                    }
                })
                .collect::<Vec<_>>();

            let mut f = {
                #[allow(unused_assignments)]
                let mut f = ark_bn254::Fq12::one();

                f = c_inv;
                f_map.insert(Selector::Initial, f.c1 / f.c0);
                tpoint_map_insert(&mut tpoint_map, Selector::Initial, t2, t3, t4);

                for i in (1..Config::ATE_LOOP_COUNT.len()).rev() {
                    f.square_in_place();
                    f_map.insert(Selector::Loop(i, LoopSelector::SquareF), f.c1 / f.c0);

                    tpoint_map_insert(
                        &mut tpoint_map,
                        Selector::Loop(i, LoopSelector::DoublePoint),
                        t2,
                        t3,
                        t4,
                    );
                    for (coeff_1, coeff_2, coeffs) in pairs.iter_mut() {
                        ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
                    }
                    (t2, t3, t4) = (
                        (t2 + t2).into_affine(),
                        (t3 + t3).into_affine(),
                        (t4 + t4).into_affine(),
                    );
                    f_map.insert(
                        Selector::Loop(i, LoopSelector::MultiSquareEval),
                        f.c1 / f.c0,
                    );

                    let bit = Config::ATE_LOOP_COUNT[i - 1];

                    if bit == 1 {
                        f = f * c_inv;
                    } else if bit == -1 {
                        f = f * c;
                    }
                    f_map.insert(Selector::Loop(i, LoopSelector::MultiC), f.c1 / f.c0);

                    if bit == 1 || bit == -1 {
                        tpoint_map_insert(
                            &mut tpoint_map,
                            Selector::Loop(i, LoopSelector::AddPoint),
                            t2,
                            t3,
                            t4,
                        );

                        for (coeff_1, coeff_2, coeffs) in pairs.iter_mut() {
                            ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
                        }

                        if bit == 1 {
                            t2 = (t2 + q2).into_affine();
                            t3 = (t3 + q3).into_affine();
                            t4 = (t4 + q4).into_affine();
                        } else {
                            t2 = (t2 - q2).into_affine();
                            t3 = (t3 - q3).into_affine();
                            t4 = (t4 - q4).into_affine();
                        }
                    }
                    f_map.insert(Selector::Loop(i, LoopSelector::MultiAddEval), f.c1 / f.c0);
                }
                f
            };

            if Config::X_IS_NEGATIVE {
                f.cyclotomic_inverse_in_place();
            }

            let c_invp = c_inv.frobenius_map(1);
            let c_p2 = c.frobenius_map(2);
            let c_invp3 = c_inv.frobenius_map(3);

            f = f * c_invp;
            f_map.insert(Selector::CFrob(1), f.c1 / f.c0);

            f = f * c_p2;
            f_map.insert(Selector::CFrob(2), f.c1 / f.c0);

            f = f * c_invp3;
            f_map.insert(Selector::CFrob(3), f.c1 / f.c0);

            tpoint_map_insert(&mut tpoint_map, Selector::FrobPoint(1), t2, t3, t4);
            for (coeff_1, coeff_2, coeffs) in &mut pairs {
                ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
            }
            t2 = (t2 + mul_by_char(q2)).into_affine();
            t3 = (t3 + mul_by_char(q3)).into_affine();
            t4 = (t4 + mul_by_char(q4)).into_affine();
            f_map.insert(Selector::MultiFrobEval(1), f.c1 / f.c0);

            tpoint_map_insert(&mut tpoint_map, Selector::FrobPoint(2), t2, t3, t4);
            for (coeff_1, coeff_2, coeffs) in &mut pairs {
                ell_affine(&mut f, &coeffs.next().unwrap(), coeff_1, coeff_2);
            }
            f_map.insert(Selector::MultiFrobEval(2), f.c1 / f.c0);

            f
        };

        assert_eq!(f * f_fixed, result);

        if result.c1 != Fq6::ZERO {
            error!(
                "check the result of pairing: {:?}, proof is not correct",
                result
            );
        } else {
            info!(
                "check the result of pairing: {:?}, proof is correct",
                result
            );
        }

        Self {
            proof: raw_proof,
            msm_points_from_pk: msm_gs,
            msm_scalars: msm_scalar,
            vky0: vky0,
            p1q1: f_fixed.c1 / f_fixed.c0,
            p2: p2,
            p4: p4,
            c: c.c1 / c.c0,
            c_inv: c_inv.c1 / c_inv.c0,
            tpoints: tpoint_map,
            q4: q4,
            q3: q3,
            q2: q2,
            f: f_map,
            evaluate_p4: None,
            evaluate_p3: None,
            evaluate_p2: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TPointSelector {
    T2(Selector),
    T3(Selector),
    T4(Selector),
}

pub fn tpoint_map_insert(
    t_point_map: &mut HashMap<TPointSelector, G2Affine>,
    selector: Selector,
    t2: G2Affine,
    t3: G2Affine,
    t4: G2Affine,
) {
    t_point_map.insert(TPointSelector::T2(selector.clone()), t2);
    t_point_map.insert(TPointSelector::T3(selector.clone()), t3);
    t_point_map.insert(TPointSelector::T4(selector), t4);
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Selector {
    Initial,                   // initial state
    Loop(usize, LoopSelector), // i in (1..Config::ATE_LOOP_COUNT.len()).rev()
    CFrob(usize),              // 1, 2, 3
    FrobPoint(usize),          // 1, 2
    MultiFrobEval(usize),      // 1, 2
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LoopSelector {
    SquareF,
    MultiSquareEval,
    DoublePoint,
    MultiC,
    MultiAddEval,
    AddPoint,
}

// return: lambda, bias
pub fn double_line(ctx: &ComputeCtx, selector: TPointSelector) -> (Fq2, Fq2) {
    let (tx, ty) = ctx.tpoints.get(&selector).unwrap().xy().unwrap();
    let lambda = (Fq2::from(3) * tx.square()) / (Fq2::from(2) * ty);
    let bias = ty - lambda * tx;
    (lambda, bias)
}

// return: lambda, bias
pub fn add_line(ctx: &ComputeCtx, selector: TPointSelector, is_neg: bool) -> (Fq2, Fq2) {
    let (tx, ty) = ctx.tpoints.get(&selector).unwrap().xy().unwrap();
    let q_point = match selector {
        TPointSelector::T2(Selector::FrobPoint(1)) => mul_by_char(ctx.q2),
        TPointSelector::T2(Selector::FrobPoint(2)) => mul_by_2char_neg(ctx.q2),
        TPointSelector::T3(Selector::FrobPoint(1)) => mul_by_char(ctx.q3),
        TPointSelector::T3(Selector::FrobPoint(2)) => mul_by_2char_neg(ctx.q3),
        TPointSelector::T2(_) => ctx.q2,
        TPointSelector::T3(_) => ctx.q3,
        TPointSelector::T4(_) => ctx.q4,
    };

    let q_point = if is_neg { -q_point } else { q_point };
    let (qx, qy) = q_point.xy().unwrap();

    let lambda = (ty - qy) / (tx - qx);
    let bias = ty - lambda * tx;

    (lambda, bias)
}

pub fn extract_double_lambda(selector: TPointSelector) -> ComputeFn {
    let func = move |ctx: &mut ComputeCtx, _: Vec<State>| -> State {
        State::Fq2(Some(double_line(ctx, selector.clone()).0))
    };
    Box::new(func)
}

pub fn extract_double_bias(selector: TPointSelector) -> ComputeFn {
    let func = move |ctx: &mut ComputeCtx, _: Vec<State>| -> State {
        State::Fq2(Some(double_line(ctx, selector.clone()).1))
    };
    Box::new(func)
}

pub fn extract_add_lambda(selector: TPointSelector, is_neg: bool) -> ComputeFn {
    let func = move |ctx: &mut ComputeCtx, _: Vec<State>| -> State {
        State::Fq2(Some(add_line(ctx, selector.clone(), is_neg).0))
    };
    Box::new(func)
}

pub fn extract_add_bias(selector: TPointSelector, is_neg: bool) -> ComputeFn {
    let func = move |ctx: &mut ComputeCtx, _: Vec<State>| -> State {
        State::Fq2(Some(add_line(ctx, selector.clone(), is_neg).1))
    };
    Box::new(func)
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

// extract proof.c
pub fn extract_p2() -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, _inputs: Vec<State>| -> State {
        State::G1(Some(compute_ctx.p2.clone()))
    };
    Box::new(func)
}

pub fn extract_q4x() -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, _inputs: Vec<State>| -> State {
        State::Fq2(Some(compute_ctx.q4.x().unwrap()))
    };
    Box::new(func)
}

pub fn extract_q4y() -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, _inputs: Vec<State>| -> State {
        State::Fq2(Some(compute_ctx.q4.y().unwrap()))
    };
    Box::new(func)
}

// extrac proof.a
pub fn extract_p4() -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        State::G1(Some(compute_ctx.p4.clone()))
    };
    Box::new(func)
}

pub fn extract_c(idx: usize) -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        match idx {
            0 => State::Fq2(Some(compute_ctx.c.c0)),
            1 => State::Fq2(Some(compute_ctx.c.c1)),
            2 => State::Fq2(Some(compute_ctx.c.c2)),
            _ => panic!("index out of range"),
        }
    };
    Box::new(func)
}

pub fn extract_t4x() -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        State::Fq2(Some(compute_ctx.t4.x().unwrap()))
    };
    Box::new(func)
}

pub fn extract_t4y() -> ComputeFn {
    let func = move |compute_ctx: &mut ComputeCtx, inputs: Vec<State>| -> State {
        State::Fq2(Some(compute_ctx.t4.y().unwrap()))
    };
    Box::new(func)
}

pub fn extract_line_evaluation_g(index: usize) -> ComputeFn {
    assert!(index < 3);
    Box::new(move |compute_ctx: &mut ComputeCtx, _: Vec<State>| {
        let evaluate_p2 = Fq12::new(Fq6::from(1), compute_ctx.evaluate_p2.unwrap());
        let evaluate_p3 = Fq12::new(Fq6::from(1), compute_ctx.evaluate_p3.unwrap());
        let evaluate_p4 = Fq12::new(Fq6::from(1), compute_ctx.evaluate_p4.unwrap());

        let result = evaluate_p2 * evaluate_p3 * evaluate_p4;
        let g = result.c1 / result.c0;
        let select_array = [g.c0, g.c1, g.c2];
        State::Fq2(Some(Fq2::from(select_array[index])))
    })
}

pub fn extract_eval_multi_f(index: usize, selector: Selector) -> ComputeFn {
    assert!(index < 3);
    Box::new(move |compute_ctx: &mut ComputeCtx, _: Vec<State>| {
        let f = compute_ctx.f.get(&selector).unwrap();
        let select_array = [f.c0, f.c1, f.c2];
        State::Fq2(Some(Fq2::from(select_array[index])))
    })
}

pub fn extract_p1q1(index: usize) -> ComputeFn {
    assert!(index < 3);
    Box::new(move |compute_ctx: &mut ComputeCtx, _: Vec<State>| {
        let g = compute_ctx.p1q1.clone();
        let select_array = [g.c0, g.c1, g.c2];
        State::Fq2(Some(Fq2::from(select_array[index])))
    })
}

mod tests {
    use crate::autochunker::{compute_ctx::ComputeCtx, proof::RawProof};
    use ark_bn254::{Fq, Fq2, Fq6};
    use core::ops::Neg;
    use log::info;

    #[test_log::test]
    fn test_raw_proof_to_compute_ctx() {
        let raw_proof = RawProof::mock_proof();
        let _: ComputeCtx = raw_proof.into();
    }
}
