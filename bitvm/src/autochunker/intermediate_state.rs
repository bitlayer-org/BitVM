use ark_bn254::{Fq, Fq2, Fq6, Fr};
use ark_ec::models::bn::Bn;
use ark_ec::pairing::Pairing;
use paste::paste;

use crate::bn254::utils::Hint;

pub type G1 = <Bn<ark_bn254::Config> as Pairing>::G1Affine;
pub type CheckValid = bool;
const U254_BYTES: usize = 4 * 9;

#[derive(Debug, Clone)]
pub enum State {
    Fr(Option<Fr>),
    Fq(Option<Fq>),
    G1(Option<G1>),
    Fq2(Option<Fq2>),
    Fq6(Option<Fq6>),
    CheckValid(Option<CheckValid>), // Use CheckValid for input verify or final accumulator verify
}

macro_rules! basic_functions {
    ($state_type: ident) => {
        paste! {
            #[allow(unused)]
            pub fn [<get_ $state_type:lower>](&self) -> $state_type {
                match self {
                    State::$state_type(Some(fq)) => *fq,
                    _ => panic!("get unexpected state {}", stringify!($state_type)),
                }
            }

            #[allow(unused)]
            pub fn [<new_ $state_type:lower>]() -> State {
                State::$state_type(None)
            }

            #[allow(unused)]
            pub fn [<set_ $state_type:lower>](&mut self, value: $state_type) {
                match self {
                    State::$state_type(ref mut fq) => *fq = Some(value),
                    _ => panic!("set unexpected state {}", stringify!($state_type)),
                }
            }
        }
    };
}

macro_rules! impl_state_functions {
    ($($state_type:ident, $fq_count:expr, $bit_cost:expr, $to_witness_func:expr);*) => {
        paste!{
        impl State {
            $(
                basic_functions!($state_type);
            )*

            #[allow(unused)]
            pub fn is_filled(&self) -> bool {
                match self {
                    $(State::$state_type(Some(_)) => true,)*
                    _ => false,
                }
            }

            #[allow(unused)]
            pub fn to_hint(&self) -> Hint {
                match self {
                    $(State::$state_type(Some(x)) => $to_witness_func(x),)*
                    _ => panic!("to_witness unexpected state"),
                }
            }

            #[allow(unused)]
            pub fn get_type_name(&self) -> &str {
                match self {
                    $(State::$state_type(_) => stringify!($state_type),)*
                }
            }

            #[allow(unused)]
            pub fn spawn_new_state(&self) -> State {
                match self {
                    $(State::$state_type(_) => State::$state_type(None),)*
                }
            }

            pub fn get_number_of_fq_elements(&self) -> usize {
                match self {
                    $(State::$state_type(_) => $fq_count,)*
                }
            }

            #[allow(unused)]
            pub fn bit_commitment_cost(&self) -> usize {
                match self {
                    $(State::$state_type(_) => $bit_cost,)*
                }
            }

            #[allow(unused)]
            pub fn get_bytes_of_state(&self) -> usize {
                self.get_number_of_fq_elements() * U254_BYTES
            }

        }
    }
    };
}

// Implement the basic functions for each state type
// (Type, number of Fq elements, bit commitment cost)
impl_state_functions! {
    Fq, 1, 6788, |x: &Fq| Hint::Fq(*x);
    G1, 2, 13196, |x: &G1| Hint::G1(*x);
    Fq2, 2, 13196, |x: &Fq2| Hint::Fq2(*x);
    Fr, 1, 6788, |x: &Fr| Hint::Fr(*x);
    Fq6, 6, 123, |x: &Fq6| Hint::Fq6(*x);
    CheckValid, 0, 0, |x: &CheckValid| {
        let mut bytes = vec![0; 1];
        if *x {
            bytes[0] = 1;
        } else {
            bytes[0] = 0;
        }
        bytes
    }
}
