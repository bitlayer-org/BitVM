use ark_bn254::{Fq, Fq2};
use ark_ec::models::bn::Bn;
use ark_ec::pairing::Pairing;
use paste::paste;

pub type G1 = <Bn<ark_bn254::Config> as Pairing>::G1Affine;

const U254_BYTES: usize = 4 * 9;

#[derive(Debug, Clone)]
pub enum State {
    Fq(Option<Fq>),
    G1(Option<G1>),
    Fq2(Option<Fq2>),
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
    ($($state_type:ident, $fq_count:expr, $bit_cost:expr);*) => {
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
    Fq, 1, 6788;
    G1, 2, 13196;
    Fq2, 2, 13196
}
