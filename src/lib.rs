use parcel::{parsers::byte::expect_byte, ParseResult, Parser};
use std::fmt::Debug;

#[cfg(test)]
mod tests;

/// CycleCost represents an object that can take n cycles to process.
/// typically this will be assigned to an instruction.
pub trait CycleCost {
    fn cycles(&self) -> usize {
        1
    }
}

/// ByteSized represents a type that has a byte representable size. Often this
/// will be a fixed sized type like a mnemonic, addressing mode or instruction.
pub trait ByteSized {
    fn byte_size(&self) -> usize {
        1
    }
}

pub mod addressing_mode;
pub mod mnemonic;

/// Instruction represents a single mos6502 instruction, taking a mnemonic and address mode as parameters.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Instruction<M, A>
where
    M: ByteSized + Copy + Debug + PartialEq,
    A: ByteSized + Copy + Debug + PartialEq,
{
    mnemonic: M,
    addressing_mode: A,
}

impl<M, A> Instruction<M, A>
where
    M: ByteSized + Copy + Debug + PartialEq,
    A: ByteSized + Copy + Debug + PartialEq,
{
    pub fn new(mnemonic: M, addressing_mode: A) -> Self {
        Instruction {
            mnemonic,
            addressing_mode,
        }
    }
}

impl<M, A> ByteSized for Instruction<M, A>
where
    M: ByteSized + Copy + Debug + PartialEq,
    A: ByteSized + Copy + Debug + PartialEq,
{
    fn byte_size(&self) -> usize {
        self.mnemonic.byte_size() + self.addressing_mode.byte_size()
    }
}

macro_rules! gen_instruction_cycles_and_parser {
    ($mnemonic:ty, $addressing_mode:ty, $opcode:literal, $cycles:literal) => {
        impl CycleCost for Instruction<$mnemonic, $addressing_mode> {
            fn cycles(&self) -> usize {
                $cycles
            }
        }

        impl<'a> Parser<'a, &'a [u8], Instruction<$mnemonic, $addressing_mode>>
            for Instruction<$mnemonic, $addressing_mode>
        {
            fn parse(
                &self,
                input: &'a [u8],
            ) -> ParseResult<&'a [u8], Instruction<$mnemonic, $addressing_mode>> {
                // If the expected opcode and addressing mode match, map it to a
                // corresponding Instruction.
                parcel::map(
                    parcel::and_then(expect_byte($opcode), |_| <$addressing_mode>::default()),
                    |am| Instruction::new(<$mnemonic>::default(), am),
                )
                .parse(input)
            }
        }
    };
}

// Arithmetic Operations

// ADC

gen_instruction_cycles_and_parser!(mnemonic::ADC, addressing_mode::Absolute, 0x6d, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::ADC,
    addressing_mode::AbsoluteIndexedWithX,
    0x7d,
    4
);

gen_instruction_cycles_and_parser!(
    mnemonic::ADC,
    addressing_mode::AbsoluteIndexedWithY,
    0x79,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::ADC, addressing_mode::IndirectYIndexed, 0x71, 5);

gen_instruction_cycles_and_parser!(mnemonic::ADC, addressing_mode::Immediate, 0x69, 2);

gen_instruction_cycles_and_parser!(mnemonic::ADC, addressing_mode::XIndexedIndirect, 0x61, 6);

gen_instruction_cycles_and_parser!(mnemonic::ADC, addressing_mode::ZeroPage, 0x65, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::ADC,
    addressing_mode::ZeroPageIndexedWithX,
    0x75,
    4
);

// SBC

gen_instruction_cycles_and_parser!(mnemonic::SBC, addressing_mode::Absolute, 0xed, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::SBC,
    addressing_mode::AbsoluteIndexedWithX,
    0xFD,
    4
);

gen_instruction_cycles_and_parser!(
    mnemonic::SBC,
    addressing_mode::AbsoluteIndexedWithY,
    0xF9,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::SBC, addressing_mode::IndirectYIndexed, 0xf1, 5);

gen_instruction_cycles_and_parser!(mnemonic::SBC, addressing_mode::Immediate, 0xe9, 2);

gen_instruction_cycles_and_parser!(mnemonic::SBC, addressing_mode::XIndexedIndirect, 0xe1, 6);

gen_instruction_cycles_and_parser!(mnemonic::SBC, addressing_mode::ZeroPage, 0xe5, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::SBC,
    addressing_mode::ZeroPageIndexedWithX,
    0xf5,
    4
);

// Bit-wise Operations

// AND

gen_instruction_cycles_and_parser!(mnemonic::AND, addressing_mode::Absolute, 0x2d, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::AND,
    addressing_mode::AbsoluteIndexedWithX,
    0x3d,
    4
);

gen_instruction_cycles_and_parser!(
    mnemonic::AND,
    addressing_mode::AbsoluteIndexedWithY,
    0x39,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::AND, addressing_mode::IndirectYIndexed, 0x31, 5);

gen_instruction_cycles_and_parser!(mnemonic::AND, addressing_mode::Immediate, 0x29, 2);

gen_instruction_cycles_and_parser!(mnemonic::AND, addressing_mode::XIndexedIndirect, 0x21, 6);

gen_instruction_cycles_and_parser!(mnemonic::AND, addressing_mode::ZeroPage, 0x25, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::AND,
    addressing_mode::ZeroPageIndexedWithX,
    0x35,
    4
);

// ASL

gen_instruction_cycles_and_parser!(mnemonic::ASL, addressing_mode::Absolute, 0x0e, 6);

gen_instruction_cycles_and_parser!(
    mnemonic::ASL,
    addressing_mode::AbsoluteIndexedWithX,
    0x1e,
    7
);

gen_instruction_cycles_and_parser!(mnemonic::ASL, addressing_mode::Accumulator, 0x0a, 2);

gen_instruction_cycles_and_parser!(mnemonic::ASL, addressing_mode::ZeroPage, 0x06, 5);

gen_instruction_cycles_and_parser!(
    mnemonic::ASL,
    addressing_mode::ZeroPageIndexedWithX,
    0x16,
    6
);

// BIT

gen_instruction_cycles_and_parser!(mnemonic::BIT, addressing_mode::Absolute, 0x2c, 4);

gen_instruction_cycles_and_parser!(mnemonic::BIT, addressing_mode::ZeroPage, 0x24, 3);

// EOR

gen_instruction_cycles_and_parser!(mnemonic::EOR, addressing_mode::Absolute, 0x4d, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::EOR,
    addressing_mode::AbsoluteIndexedWithX,
    0x5d,
    4
);

gen_instruction_cycles_and_parser!(
    mnemonic::EOR,
    addressing_mode::AbsoluteIndexedWithY,
    0x59,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::EOR, addressing_mode::IndirectYIndexed, 0x51, 5);

gen_instruction_cycles_and_parser!(mnemonic::EOR, addressing_mode::Immediate, 0x49, 2);

gen_instruction_cycles_and_parser!(mnemonic::EOR, addressing_mode::XIndexedIndirect, 0x41, 6);

gen_instruction_cycles_and_parser!(mnemonic::EOR, addressing_mode::ZeroPage, 0x45, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::EOR,
    addressing_mode::ZeroPageIndexedWithX,
    0x55,
    4
);

// LSR

gen_instruction_cycles_and_parser!(mnemonic::LSR, addressing_mode::Absolute, 0x4e, 6);

gen_instruction_cycles_and_parser!(
    mnemonic::LSR,
    addressing_mode::AbsoluteIndexedWithX,
    0x5e,
    7
);

gen_instruction_cycles_and_parser!(mnemonic::LSR, addressing_mode::Accumulator, 0x4a, 2);

gen_instruction_cycles_and_parser!(mnemonic::LSR, addressing_mode::ZeroPage, 0x46, 5);

gen_instruction_cycles_and_parser!(
    mnemonic::LSR,
    addressing_mode::ZeroPageIndexedWithX,
    0x56,
    6
);

// ORA

gen_instruction_cycles_and_parser!(mnemonic::ORA, addressing_mode::Absolute, 0x0d, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::ORA,
    addressing_mode::AbsoluteIndexedWithX,
    0x1d,
    4
);

gen_instruction_cycles_and_parser!(
    mnemonic::ORA,
    addressing_mode::AbsoluteIndexedWithY,
    0x19,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::ORA, addressing_mode::IndirectYIndexed, 0x11, 5);

gen_instruction_cycles_and_parser!(mnemonic::ORA, addressing_mode::Immediate, 0x09, 2);

gen_instruction_cycles_and_parser!(mnemonic::ORA, addressing_mode::XIndexedIndirect, 0x01, 6);

gen_instruction_cycles_and_parser!(mnemonic::ORA, addressing_mode::ZeroPage, 0x05, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::ORA,
    addressing_mode::ZeroPageIndexedWithX,
    0x15,
    4
);

// ROL

gen_instruction_cycles_and_parser!(mnemonic::ROL, addressing_mode::Absolute, 0x2e, 6);

gen_instruction_cycles_and_parser!(
    mnemonic::ROL,
    addressing_mode::AbsoluteIndexedWithX,
    0x3e,
    7
);

gen_instruction_cycles_and_parser!(mnemonic::ROL, addressing_mode::Accumulator, 0x2a, 2);

gen_instruction_cycles_and_parser!(mnemonic::ROL, addressing_mode::ZeroPage, 0x26, 5);

gen_instruction_cycles_and_parser!(
    mnemonic::ROL,
    addressing_mode::ZeroPageIndexedWithX,
    0x36,
    6
);

// ROR

gen_instruction_cycles_and_parser!(mnemonic::ROR, addressing_mode::Absolute, 0x6e, 6);

gen_instruction_cycles_and_parser!(
    mnemonic::ROR,
    addressing_mode::AbsoluteIndexedWithX,
    0x7e,
    7
);

gen_instruction_cycles_and_parser!(mnemonic::ROR, addressing_mode::Accumulator, 0x6a, 2);

gen_instruction_cycles_and_parser!(mnemonic::ROR, addressing_mode::ZeroPage, 0x66, 5);

gen_instruction_cycles_and_parser!(
    mnemonic::ROR,
    addressing_mode::ZeroPageIndexedWithX,
    0x76,
    6
);

// Branching

// BCC

gen_instruction_cycles_and_parser!(mnemonic::BCC, addressing_mode::Relative, 0x90, 2);

// BCS

gen_instruction_cycles_and_parser!(mnemonic::BCS, addressing_mode::Relative, 0xb0, 2);

// BEQ

gen_instruction_cycles_and_parser!(mnemonic::BEQ, addressing_mode::Relative, 0xf0, 2);

// BMI

gen_instruction_cycles_and_parser!(mnemonic::BMI, addressing_mode::Relative, 0x30, 2);

// BNE

gen_instruction_cycles_and_parser!(mnemonic::BNE, addressing_mode::Relative, 0xd0, 2);

// BPL

gen_instruction_cycles_and_parser!(mnemonic::BPL, addressing_mode::Relative, 0x10, 2);

// BVC

gen_instruction_cycles_and_parser!(mnemonic::BVC, addressing_mode::Relative, 0x50, 2);

// BVS

gen_instruction_cycles_and_parser!(mnemonic::BVS, addressing_mode::Relative, 0x70, 2);

// CLC

gen_instruction_cycles_and_parser!(mnemonic::CLC, addressing_mode::Implied, 0x18, 2);

// CLD

gen_instruction_cycles_and_parser!(mnemonic::CLD, addressing_mode::Implied, 0xd8, 2);

// CLI

gen_instruction_cycles_and_parser!(mnemonic::CLI, addressing_mode::Implied, 0x58, 2);

// CLV

gen_instruction_cycles_and_parser!(mnemonic::CLV, addressing_mode::Implied, 0xb8, 2);

// CMP

gen_instruction_cycles_and_parser!(mnemonic::CMP, addressing_mode::Absolute, 0xcd, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::CMP,
    addressing_mode::AbsoluteIndexedWithX,
    0xdd,
    4
);

gen_instruction_cycles_and_parser!(
    mnemonic::CMP,
    addressing_mode::AbsoluteIndexedWithY,
    0xd9,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::CMP, addressing_mode::IndirectYIndexed, 0xd1, 5);

gen_instruction_cycles_and_parser!(mnemonic::CMP, addressing_mode::Immediate, 0xc9, 2);

gen_instruction_cycles_and_parser!(mnemonic::CMP, addressing_mode::XIndexedIndirect, 0xc1, 6);

gen_instruction_cycles_and_parser!(mnemonic::CMP, addressing_mode::ZeroPage, 0xc5, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::CMP,
    addressing_mode::ZeroPageIndexedWithX,
    0xd5,
    4
);

// CPX

gen_instruction_cycles_and_parser!(mnemonic::CPX, addressing_mode::Absolute, 0xec, 4);

gen_instruction_cycles_and_parser!(mnemonic::CPX, addressing_mode::Immediate, 0xe0, 2);

gen_instruction_cycles_and_parser!(mnemonic::CPX, addressing_mode::ZeroPage, 0xe4, 3);

// CPY

gen_instruction_cycles_and_parser!(mnemonic::CPY, addressing_mode::Absolute, 0xcc, 4);

gen_instruction_cycles_and_parser!(mnemonic::CPY, addressing_mode::Immediate, 0xc0, 2);

gen_instruction_cycles_and_parser!(mnemonic::CPY, addressing_mode::ZeroPage, 0xc4, 3);

// DEC

gen_instruction_cycles_and_parser!(mnemonic::DEC, addressing_mode::Absolute, 0xce, 6);

gen_instruction_cycles_and_parser!(
    mnemonic::DEC,
    addressing_mode::AbsoluteIndexedWithX,
    0xde,
    7
);

gen_instruction_cycles_and_parser!(mnemonic::DEC, addressing_mode::ZeroPage, 0xc6, 5);

gen_instruction_cycles_and_parser!(
    mnemonic::DEC,
    addressing_mode::ZeroPageIndexedWithX,
    0xd6,
    6
);

// DEX

gen_instruction_cycles_and_parser!(mnemonic::DEX, addressing_mode::Implied, 0xca, 2);

// DEY

gen_instruction_cycles_and_parser!(mnemonic::DEY, addressing_mode::Implied, 0x88, 2);

// INC

gen_instruction_cycles_and_parser!(mnemonic::INC, addressing_mode::Absolute, 0xee, 6);

gen_instruction_cycles_and_parser!(
    mnemonic::INC,
    addressing_mode::AbsoluteIndexedWithX,
    0xfe,
    7
);

gen_instruction_cycles_and_parser!(mnemonic::INC, addressing_mode::ZeroPage, 0xe6, 5);

gen_instruction_cycles_and_parser!(
    mnemonic::INC,
    addressing_mode::ZeroPageIndexedWithX,
    0xf6,
    6
);

// INX

gen_instruction_cycles_and_parser!(mnemonic::INX, addressing_mode::Implied, 0xe8, 2);

// INY

gen_instruction_cycles_and_parser!(mnemonic::INY, addressing_mode::Implied, 0xc8, 2);

// JMP

gen_instruction_cycles_and_parser!(mnemonic::JMP, addressing_mode::Absolute, 0x4c, 3);

gen_instruction_cycles_and_parser!(mnemonic::JMP, addressing_mode::Indirect, 0x6c, 5);

// JSR

gen_instruction_cycles_and_parser!(mnemonic::JSR, addressing_mode::Absolute, 0x20, 6);

// LDA

gen_instruction_cycles_and_parser!(mnemonic::LDA, addressing_mode::Immediate, 0xa9, 2);

gen_instruction_cycles_and_parser!(mnemonic::LDA, addressing_mode::ZeroPage, 0xa5, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::LDA,
    addressing_mode::ZeroPageIndexedWithX,
    0xb5,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::LDA, addressing_mode::Absolute, 0xad, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::LDA,
    addressing_mode::AbsoluteIndexedWithX,
    0xbd,
    4
);

gen_instruction_cycles_and_parser!(
    mnemonic::LDA,
    addressing_mode::AbsoluteIndexedWithY,
    0xb9,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::LDA, addressing_mode::IndirectYIndexed, 0xb1, 5);

gen_instruction_cycles_and_parser!(mnemonic::LDA, addressing_mode::XIndexedIndirect, 0xa1, 6);

// LDX

gen_instruction_cycles_and_parser!(mnemonic::LDX, addressing_mode::Absolute, 0xae, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::LDX,
    addressing_mode::AbsoluteIndexedWithY,
    0xbe,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::LDX, addressing_mode::Immediate, 0xa2, 2);

gen_instruction_cycles_and_parser!(mnemonic::LDX, addressing_mode::ZeroPage, 0xa6, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::LDX,
    addressing_mode::ZeroPageIndexedWithY,
    0xb6,
    4
);

// LDY

gen_instruction_cycles_and_parser!(mnemonic::LDY, addressing_mode::Absolute, 0xac, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::LDY,
    addressing_mode::AbsoluteIndexedWithX,
    0xbc,
    4
);

gen_instruction_cycles_and_parser!(mnemonic::LDY, addressing_mode::Immediate, 0xa0, 2);

gen_instruction_cycles_and_parser!(mnemonic::LDY, addressing_mode::ZeroPage, 0xa4, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::LDY,
    addressing_mode::ZeroPageIndexedWithX,
    0xb4,
    4
);

// PHA

gen_instruction_cycles_and_parser!(mnemonic::PHA, addressing_mode::Implied, 0x48, 3);

// PHP

gen_instruction_cycles_and_parser!(mnemonic::PHP, addressing_mode::Implied, 0x08, 3);

// PLA

gen_instruction_cycles_and_parser!(mnemonic::PLA, addressing_mode::Implied, 0x68, 4);

// PLP

gen_instruction_cycles_and_parser!(mnemonic::PLP, addressing_mode::Implied, 0x28, 4);

// RTI

gen_instruction_cycles_and_parser!(mnemonic::RTI, addressing_mode::Implied, 0x40, 6);

// RTS

gen_instruction_cycles_and_parser!(mnemonic::RTS, addressing_mode::Implied, 0x60, 6);

// SEC

gen_instruction_cycles_and_parser!(mnemonic::SEC, addressing_mode::Implied, 0x38, 2);

// SED

gen_instruction_cycles_and_parser!(mnemonic::SED, addressing_mode::Implied, 0xf8, 2);

// SEI

gen_instruction_cycles_and_parser!(mnemonic::SEI, addressing_mode::Implied, 0x78, 2);

// STA

gen_instruction_cycles_and_parser!(mnemonic::STA, addressing_mode::Absolute, 0x8d, 4);

gen_instruction_cycles_and_parser!(
    mnemonic::STA,
    addressing_mode::AbsoluteIndexedWithX,
    0x9d,
    5
);

gen_instruction_cycles_and_parser!(
    mnemonic::STA,
    addressing_mode::AbsoluteIndexedWithY,
    0x99,
    5
);

gen_instruction_cycles_and_parser!(mnemonic::STA, addressing_mode::IndirectYIndexed, 0x91, 6);

gen_instruction_cycles_and_parser!(mnemonic::STA, addressing_mode::XIndexedIndirect, 0x81, 6);

gen_instruction_cycles_and_parser!(mnemonic::STA, addressing_mode::ZeroPage, 0x85, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::STA,
    addressing_mode::ZeroPageIndexedWithX,
    0x95,
    4
);

// STX

gen_instruction_cycles_and_parser!(mnemonic::STX, addressing_mode::Absolute, 0x8e, 4);

gen_instruction_cycles_and_parser!(mnemonic::STX, addressing_mode::ZeroPage, 0x86, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::STX,
    addressing_mode::ZeroPageIndexedWithY,
    0x96,
    4
);

// STY

gen_instruction_cycles_and_parser!(mnemonic::STY, addressing_mode::Absolute, 0x8c, 4);

gen_instruction_cycles_and_parser!(mnemonic::STY, addressing_mode::ZeroPage, 0x84, 3);

gen_instruction_cycles_and_parser!(
    mnemonic::STY,
    addressing_mode::ZeroPageIndexedWithX,
    0x94,
    4
);

// TAX

gen_instruction_cycles_and_parser!(mnemonic::TAX, addressing_mode::Implied, 0xaa, 2);

// TAY

gen_instruction_cycles_and_parser!(mnemonic::TAY, addressing_mode::Implied, 0xa8, 2);

// TSX

gen_instruction_cycles_and_parser!(mnemonic::TSX, addressing_mode::Implied, 0xba, 2);

// TXA

gen_instruction_cycles_and_parser!(mnemonic::TXA, addressing_mode::Implied, 0x8a, 2);

// TSX

gen_instruction_cycles_and_parser!(mnemonic::TXS, addressing_mode::Implied, 0x9a, 2);

// TYA

gen_instruction_cycles_and_parser!(mnemonic::TYA, addressing_mode::Implied, 0x98, 2);

// Misc

// BRK

gen_instruction_cycles_and_parser!(mnemonic::BRK, addressing_mode::Implied, 0x00, 7);

// NOP

gen_instruction_cycles_and_parser!(mnemonic::NOP, addressing_mode::Implied, 0xea, 2);
