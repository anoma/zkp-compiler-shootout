use std::fs;
use risc0_zkvm_core::Digest;
use risc0_zkvm_host::Prover;
use risc0_zkvm_serde::{from_slice, to_vec};
use risc0_zkvm_host::Receipt;
use std::path::Path;

// to rexport them for rust, ugh
pub const FIB_ID             : &[u8]        = methods::FIB_ID;
pub const FIB_PATH           : &'static str = methods::FIB_PATH;
pub const FIB_FIFTY_ID       : &[u8]        = methods::FIB_FIFTY_ID;
pub const FIB_FIFTY_PATH     : &'static str = methods::FIB_FIFTY_PATH;
pub const FIB_NINTY_TWO_ID   : &[u8]        = methods::FIB_NINTY_TWO_ID;
pub const FIB_NINTY_TWO_PATH : &'static str = methods::FIB_NINTY_TWO_PATH;

pub fn setup(up_to : u32) -> Prover {
    let file_contents = fs::read(FIB_PATH).unwrap();
    let mut prover    = Prover::new(&file_contents, FIB_ID).unwrap();
    prover.add_input(&[up_to]).unwrap();
    prover
}

pub fn setup_fix(method_id : &[u8], method_path : &dyn AsRef<Path>) -> Prover {
    let file_contents = fs::read(method_path).unwrap();
    let mut prover    = Prover::new(&file_contents, method_id).unwrap();
    prover.add_input(&[0, 1]).unwrap();
    prover
}

pub fn prove(prover : Prover) -> Receipt {
    prover.run().unwrap()
}

pub fn digest(receipt : &Receipt) -> Digest {
    let journal = receipt.get_journal_vec().unwrap();
    from_slice(&journal).unwrap()
}

pub fn verify(method : &[u8], receipt : &Receipt) {
    receipt.verify(method).unwrap();
}
