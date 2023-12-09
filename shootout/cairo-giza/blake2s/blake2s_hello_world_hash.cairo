%builtins range_check bitwise

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.cairo_blake2s.blake2s import blake2s
from starkware.cairo.common.cairo_builtins import BitwiseBuiltin

// Computes the hash of "Hello World"
func main{range_check_ptr, bitwise_ptr: BitwiseBuiltin*}() {
    alloc_locals;
    let inputs: felt* = alloc();
    assert inputs[0] = 'a';
    assert inputs[1] = 'b';
    assert inputs[2] = 'c';
    let (local blake2s_ptr_start) = alloc();
    let blake2s_ptr = blake2s_ptr_start;
    let (output) = blake2s{range_check_ptr=range_check_ptr, blake2s_ptr=blake2s_ptr}(inputs, 9);
    return ();
}
