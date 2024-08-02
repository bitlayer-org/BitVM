#[allow(dead_code)]
// Re-export what is needed to write treepp scripts
pub mod treepp {
    pub use crate::execute_script;
    pub use bitcoin_script::script;
    pub use bitcoin_script::Script;
}

use core::fmt;

use bitcoin::{hashes::Hash, hex::DisplayHex, Opcode, ScriptBuf, TapLeafHash, Transaction};
use bitcoin_scriptexec::{Exec, ExecCtx, ExecError, ExecStats, Options, Stack, TxTemplate};

pub mod bigint;
pub mod bn254;
//pub mod bridge;
pub mod fflonk;
pub mod groth16;
pub mod hash;
pub mod pseudo;
pub mod signatures;
pub mod u32;
pub mod u4;

/// A wrapper for the stack types to print them better.
pub struct FmtStack(Stack);
impl fmt::Display for FmtStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut iter = self.0.iter_str().enumerate().peekable();
        write!(f, "\n0:\t\t ")?;
        while let Some((index, item)) = iter.next() {
            write!(f, "0x{:8}", item.as_hex())?;
            if iter.peek().is_some() {
                if (index + 1) % f.width().unwrap() == 0 {
                    write!(f, "\n{}:\t\t", index + 1)?;
                }
                write!(f, " ")?;
            }
        }
        Ok(())
    }
}

impl FmtStack {
    pub fn len(&self) -> usize { self.0.len() }

    pub fn get(&self, index: usize) -> Vec<u8> { self.0.get(index) }
}

impl fmt::Debug for FmtStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct ExecuteInfo {
    pub success: bool,
    pub error: Option<ExecError>,
    pub final_stack: FmtStack,
    pub alt_stack: FmtStack,
    pub remaining_script: ScriptBuf,
    pub last_opcode: Option<Opcode>,
    pub stats: ExecStats,
}

impl fmt::Display for ExecuteInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.success {
            writeln!(f, "Script execution successful.")?;
        } else {
            writeln!(f, "Script execution failed!")?;
        }
        if let Some(ref error) = self.error {
            writeln!(f, "Error: {:?}", error)?;
        }
        if !self.remaining_script.is_empty() {
            writeln!(f, "Remaining Script: {}", self.remaining_script)?;
        }
        if self.final_stack.len() > 0 {
            match f.width() {
                None => writeln!(f, "Final Stack: {:4}", self.final_stack)?,
                Some(width) => {
                    writeln!(f, "Final Stack: {:width$}", self.final_stack, width = width)?
                }
            }
        }
        if let Some(ref opcode) = self.last_opcode {
            writeln!(f, "Last Opcode: {:?}", opcode)?;
        }
        writeln!(f, "Stats: {:?}", self.stats)?;
        Ok(())
    }
}

pub fn execute_script(script: treepp::Script) -> ExecuteInfo {
    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        Options::default(),
        TxTemplate {
            tx: Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
                input: vec![],
                output: vec![],
            },
            prevouts: vec![],
            input_idx: 0,
            taproot_annex_scriptleaf: Some((TapLeafHash::all_zeros(), None)),
        },
        script.compile(),
        vec![],
    )
    .expect("error creating exec");

    loop {
        if exec.exec_next().is_err() {
            break;
        }
    }
    let res = exec.result().unwrap();
    ExecuteInfo {
        success: res.success,
        error: res.error.clone(),
        last_opcode: res.opcode,
        final_stack: FmtStack(exec.stack().clone()),
        alt_stack: FmtStack(exec.altstack().clone()),
        remaining_script: exec.remaining_script().to_owned(),
        stats: exec.stats().clone(),
    }
}

// Execute a script on stack without `MAX_STACK_SIZE` limit.
// This function is only used for script test, not for production.
//
// NOTE: Only for test purposes.
pub fn execute_script_without_stack_limit(script: treepp::Script) -> ExecuteInfo {
    // Get the default options for the script exec.
    let mut opts = Options::default();
    // Do not enforce the stack limit.
    opts.enforce_stack_limit = false;

    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        opts,
        TxTemplate {
            tx: Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
                input: vec![],
                output: vec![],
            },
            prevouts: vec![],
            input_idx: 0,
            taproot_annex_scriptleaf: Some((TapLeafHash::all_zeros(), None)),
        },
        script.compile(),
        vec![],
    )
    .expect("error creating exec");

    loop {
        if exec.exec_next().is_err() {
            break;
        }
    }
    let res = exec.result().unwrap();
    ExecuteInfo {
        success: res.success,
        error: res.error.clone(),
        last_opcode: res.opcode,
        final_stack: FmtStack(exec.stack().clone()),
        alt_stack: FmtStack(exec.altstack().clone()),
        remaining_script: exec.remaining_script().to_owned(),
        stats: exec.stats().clone(),
    }
}

fn execute_sub_script(
    script: Vec<u8>,
    stack: Vec<Vec<u8>>,
    mut alt_stack: Vec<Vec<u8>>,
) -> ExecuteInfo {
    // Get the default options for the script exec.
    let mut opts = Options::default();
    // Do not enforce the stack limit.
    opts.enforce_stack_limit = false;

    alt_stack.reverse();
    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        opts,
        TxTemplate {
            tx: Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
                input: vec![],
                output: vec![],
            },
            prevouts: vec![],
            input_idx: 0,
            taproot_annex_scriptleaf: Some((TapLeafHash::all_zeros(), None)),
        },
        ScriptBuf::from(vec![vec![0x6b; alt_stack.len()], script].concat()), // Add to_alt_stack
        vec![stack, alt_stack].concat(),
    )
    .expect("error creating exec");

    loop {
        if exec.exec_next().is_err() {
            break;
        }
    }
    let res = exec.result().unwrap();
    let execute_info = ExecuteInfo {
        success: res.success,
        error: res.error.clone(),
        last_opcode: res.opcode,
        final_stack: FmtStack(exec.stack().clone()),
        alt_stack: FmtStack(exec.altstack().clone()),
        remaining_script: exec.remaining_script().to_owned(),
        stats: exec.stats().clone(),
    };

    execute_info
}

#[cfg(test)]
mod test {
    use crate::bn254;
    use crate::bn254::fp254impl::Fp254Impl;
    use crate::execute_sub_script;

    use super::execute_script_without_stack_limit;
    use super::treepp::*;

    #[test]
    fn test_script_debug() {
        let script = script! {
            OP_TRUE
            DEBUG
            OP_TRUE
            OP_VERIFY
        };
        let exec_result = execute_script(script);
        assert!(!exec_result.success);
    }

    #[test]
    fn test_script_execute() {
        let script = script! {
            for i in 0..36 {
                { 0x0babe123 + i }
            }
        };
        let exec_result = execute_script(script);
        // The width decides how many stack elements are printed per row
        println!(
            "{:width$}",
            exec_result,
            width = bn254::fq::Fq::N_LIMBS as usize
        );
        println!("{:4}", exec_result);
        println!("{}", exec_result);
        assert!(!exec_result.success);
        assert_eq!(exec_result.error, None);
    }
    #[test]
    fn test_execute_script_without_stack_limit() {
        let script = script! {
            for _ in 0..1001 {
                OP_1
            }
            for _ in 0..1001 {
                OP_DROP
            }
            OP_1
        };
        let exec_result = execute_script_without_stack_limit(script);
        assert!(exec_result.success);
    }

    #[test]
    fn test_sub_script() {
        let script = script! {
            for _ in 0..1001 {
                OP_1
            }
            for _ in 0..1001 {
                OP_DROP
            }
            OP_1
        };
        let exec_result = execute_sub_script(script.compile().to_bytes(), vec![], vec![]);
        println!("res: {:?}", exec_result);
        assert!(exec_result.success);
    }
}
