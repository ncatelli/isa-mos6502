pub mod mnemonic;

/// Cyclable represents an object that can take n cycles to process.
/// typically this will be assigned to an instruction.
pub trait Cyclable {
    fn cycles(&self) -> usize {
        1
    }
}

/// Offset represents a type that has a byte representable size.
/// often this will be a fixed sized type like a mnemonic, addressing mode or
/// instruction.
pub trait Offset {
    fn offset(&self) -> usize {
        1
    }
}
