use std::collections::HashMap;
use std::default;
use std::fs::File;
use std::io::Write;
use std::os::macos::raw::stat;
use std::rc::Rc;

use crate::bn254::curves::{G1Affine, G1Projective};
use crate::bn254::fp254impl::Fp254Impl;
use crate::bn254::fq::Fq;
use crate::bn254::fr::Fr;
use crate::bn254::msm::{fr_push, g1_projective_push};
use crate::groth16::verifier::Verifier;
use crate::{execute_script, execute_script_without_stack_limit, execute_sub_script};
use ark_bn254::Bn254;
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_relations::lc;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{end_timer, start_timer, test_rng, UniformRand};
use bitcoin::opcodes::all::OP_TOALTSTACK;
use bitcoin::ScriptBuf;
use bitcoin_script::builder::Block;
use bitcoin_script::{script, Chunker, StackAnalyzer};
use rand::{RngCore, SeedableRng};

use super::verifier::constants;

#[derive(Copy)]
struct DummyCircuit<F: PrimeField> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_variables: usize,
    pub num_constraints: usize,
}

impl<F: PrimeField> Clone for DummyCircuit<F> {
    fn clone(&self) -> Self {
        DummyCircuit {
            a: self.a,
            b: self.b,
            num_variables: self.num_variables,
            num_constraints: self.num_constraints,
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for DummyCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            Ok(a * b)
        })?;

        for _ in 0..(self.num_variables - 3) {
            let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for _ in 0..self.num_constraints - 1 {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }

        cs.enforce_constraint(lc!(), lc!(), lc!())?;

        Ok(())
    }
}

#[test]
fn test_sub_script() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let choose_code = script! {
        OP_4
        OP_FROMALTSTACK OP_DUP OP_ADD
        OP_FROMALTSTACK OP_ADD
        OP_SUB // 4-index
        { G1Projective::pick_with_5lookup() }
        { G1Projective::add() }
    };

    let mut script = script!(
        {1}
        OP_TOALTSTACK
        {1}
        OP_TOALTSTACK

        { g1_projective_push(ark_bn254::G1Projective::rand(&mut rng)) }
        { g1_projective_push(ark_bn254::G1Projective::rand(&mut rng)) }
        { g1_projective_push(ark_bn254::G1Projective::rand(&mut rng)) }
        { g1_projective_push(ark_bn254::G1Projective::rand(&mut rng)) }
        { g1_projective_push(ark_bn254::G1Projective::rand(&mut rng)) }

        { G1Projective::double() }
        { choose_code.clone() }
    );

    let status = script.get_stack();
    println!("stack status: {:?}", status);

    let res = execute_sub_script(script.clone().compile().to_bytes(), vec![], vec![]);
    println!("res: {}, {}", res.final_stack.len(), res.alt_stack.len());
    let res = execute_script(script);
    println!("res: {}, {}", res.final_stack.len(), res.alt_stack.len());
}

#[test]
fn test_groth16_verifier_script_total() {
    type E = Bn254;
    let k = 6;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let circuit = DummyCircuit::<<E as Pairing>::ScalarField> {
        a: Some(<E as Pairing>::ScalarField::rand(&mut rng)),
        b: Some(<E as Pairing>::ScalarField::rand(&mut rng)),
        num_variables: 10,
        num_constraints: 1 << k,
    };
    let (pk, vk) = Groth16::<E>::setup(circuit, &mut rng).unwrap();
    let pvk = prepare_verifying_key::<E>(&vk);
    let c = circuit.a.unwrap() * circuit.b.unwrap();
    let proof = Groth16::<E>::prove(&pk, circuit, &mut rng).unwrap();
    assert!(Groth16::<E>::verify_with_processed_vk(&pvk, &[c], &proof).unwrap());

    let start = start_timer!(|| "collect_script");
    let script = Verifier::verify_proof(&vec![c], &proof, &vk);
    end_timer!(start);
    println!("groth16::test_verify_proof = {} bytes", script.len());

    let start = start_timer!(|| "execute_script");
    let exec_result = execute_script_without_stack_limit(script);
    end_timer!(start);

    assert!(exec_result.success);
}

#[test]
fn test_groth16_verifier() {
    type E = Bn254;
    let k = 6;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let circuit = DummyCircuit::<<E as Pairing>::ScalarField> {
        a: Some(<E as Pairing>::ScalarField::rand(&mut rng)),
        b: Some(<E as Pairing>::ScalarField::rand(&mut rng)),
        num_variables: 10,
        num_constraints: 1 << k,
    };
    let (pk, vk) = Groth16::<E>::setup(circuit, &mut rng).unwrap();
    let pvk = prepare_verifying_key::<E>(&vk);

    let c = circuit.a.unwrap() * circuit.b.unwrap();

    let proof = Groth16::<E>::prove(&pk, circuit, &mut rng).unwrap();
    assert!(Groth16::<E>::verify_with_processed_vk(&pvk, &[c], &proof).unwrap());

    let script = Verifier::verify_proof_script(&vk);
    let witness = Verifier::push_proof_script(&proof, &vec![c], &vk);
    let exec_result = execute_script_without_stack_limit(script!(
        {witness}
        {script}
    ));
    println!("final stack {}", exec_result.final_stack.len());
    println!("remain_script {}", exec_result.remaining_script.len());
    assert!(exec_result.success);

    /*
    let total_script = Verifier::verify_proof(&vec![c], &proof, &vk);
    let total_exec_result = execute_script_without_stack_limit(total_script);
    println!("total_final stack {}", total_exec_result.final_stack.len());
    println!(
        "total_remain_script {}",
        total_exec_result.remaining_script.len()
    );

    assert_eq!(
        exec_result.final_stack.len(),
        total_exec_result.final_stack.len(),
        "stack"
    );

    for i in 0..exec_result.final_stack.0.len() {
        assert_eq!(
            exec_result.final_stack.0.get(i),
            total_exec_result.final_stack.0.get(i),
            "i: {}",
            i
        );
    }
    */
}

#[test]
fn test_groth16_verifier_chunk() {
    type E = Bn254;
    let k = 6;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let circuit = DummyCircuit::<<E as Pairing>::ScalarField> {
        a: Some(<E as Pairing>::ScalarField::rand(&mut rng)),
        b: Some(<E as Pairing>::ScalarField::rand(&mut rng)),
        num_variables: 10,
        num_constraints: 1 << k,
    };
    let (pk, vk) = Groth16::<E>::setup(circuit, &mut rng).unwrap();
    let pvk = prepare_verifying_key::<E>(&vk);

    let c = circuit.a.unwrap() * circuit.b.unwrap();

    let proof = Groth16::<E>::prove(&pk, circuit, &mut rng).unwrap();
    assert!(Groth16::<E>::verify_with_processed_vk(&pvk, &[c], &proof).unwrap());

    let start = start_timer!(|| "collect_script");
    let mut script = Verifier::verify_proof(&vec![c], &proof, &vk);
    end_timer!(start);

    println!("groth16::test_verify_proof = {} bytes", script.len());

    let start = start_timer!(|| "analyze_stack");
    let status = script.get_stack();
    end_timer!(start);
    assert_eq!(status.stack_changed, 1); // leave "true" on the statck
    assert_eq!(status.altstack_changed, 0); // leave nothing on the altstatck

    println!("stack analyze done {:?}", status);

    let mut chunker = Chunker::new(script.clone(), 4 * 1000 * 1000, 1 * 1000 * 1000);

    /*
    let first_chunk = chunker.find_next_chunk();
    let mut a = StackAnalyzer::new();
    let chunk = a.analyze_blocks(&first_chunk);
    println!("chunk: {:?}", chunk);

    println!("===========");
    let second_chunk = chunker.find_next_chunk();
    let mut a = StackAnalyzer::new();
    let chunk = a.analyze_blocks(&second_chunk);
    println!("chunk: {:?}", chunk);

    println!("===========");
    let third_chunk = chunker.find_next_chunk();
    let mut a = StackAnalyzer::new();
    let chunk = a.analyze_blocks(&third_chunk);
    println!("chunk: {:?}", chunk);

    println!("===========");

    return;
    */

    let chunks = chunker.find_chunks_and_analyze_stack();
    assert_eq!(
        chunks.iter().fold(0, |sum, chunk| chunk.0 + sum),
        script.len(),
        "total chunks length is not equal to the script length"
    );

    // write to a file
    let bitcoin_script_bytes = script.compile().into_bytes();
    let file_path = "chunker.txt";
    let mut file = File::create(&file_path).unwrap();
    let mut begin = 0;
    let mut end = 0;
    let mut stack = vec![];
    let mut alt_stack = vec![];

    // verify the chunks
    for chunk in chunks {
        // split subscript
        end += chunk.0;
        let mut sub_script = vec![0; chunk.0];
        sub_script.copy_from_slice(&bitcoin_script_bytes[begin..end]);
        begin = end;

        /*
        let asm_string = ScriptBuf::from_bytes(sub_script.clone()).to_asm_string();
        let map = asm_string.split(" ").fold(HashMap::new(), |mut init, x| {
            *init.entry(x).or_insert(0) += 1;
            init
        });
        println!("map: {:?}", map);
        */

        // execute subscript
        assert!(stack.len() >= chunk.1);
        assert!(alt_stack.len() >= chunk.3);
        let res = execute_sub_script(
            sub_script,
            stack.split_off(stack.len() - chunk.1),
            alt_stack.split_off(alt_stack.len() - chunk.3),
        );

        // write to a file
        let output = format!(
            "chunk size {} input size {} output size {} altinput size {} altoutput size {} \n",
            chunk.0, chunk.1, chunk.2, chunk.3, chunk.4,
        );
        write!(file, "{}", output).unwrap();
        // println!("{}", output);

        assert_eq!(res.final_stack.len(), chunk.2);
        assert_eq!(res.alt_stack.len(), chunk.4);
        res.final_stack.0.iter_str().for_each(|x| stack.push(x));
        res.alt_stack.0.iter_str().for_each(|x| alt_stack.push(x));
    }

    assert_eq!(stack.len(), 1);
    assert_eq!(alt_stack.len(), 0);

    println!("chunker done");

    /*
    let start = start_timer!(|| "execute_script");
    let exec_result = execute_script_without_stack_limit(script);
    end_timer!(start);

    assert!(exec_result.success);
    */
}
