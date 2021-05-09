extern crate parcel;
use crate::ByteSized;

/// Represents various conversion errors between mnemnoic types.
#[derive(Debug, Clone, PartialEq)]
pub enum MnemonicErr {
    ConversionErr(String),
}

impl std::fmt::Display for MnemonicErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConversionErr(m) => write!(f, "invalid mnemonic: {}", m),
        }
    }
}

macro_rules! generate_mnemonic_parser_and_offset {
    ($mnemonic:ty, $text:literal, $opcode:literal) => {
        impl ByteSized for $mnemonic {}

        impl<'a> parcel::Parser<'a, &'a [(usize, u8)], $mnemonic> for $mnemonic {
            fn parse(&self, input: &'a [(usize, u8)]) -> parcel::ParseResult<&'a [(usize, u8)], $mnemonic> {
                parcel::map(
                    parcel::parsers::byte::expect_byte($opcode),
                    |_| <$mnemonic>::default()
                ).parse(input)
            }
        }

        impl<'a> parcel::Parser<'a, &'a [(usize, char)], $mnemonic> for $mnemonic {
            fn parse(&self, input: &'a [(usize, char)]) -> parcel::ParseResult<&'a [(usize, char)], $mnemonic> {
                parcel::map(
                    parcel::parsers::character::expect_str($text),
                    |_| <$mnemonic>::default()
                ).parse(input)
            }
        }
    };

    ($mnemonic:ty, $text:literal, $( $opcode:literal ),* ) => {
        impl ByteSized for $mnemonic {}

        impl<'a> parcel::Parser<'a, &'a [(usize, u8)], $mnemonic> for $mnemonic {
            fn parse(&self, input: &'a [(usize, u8)]) -> parcel::ParseResult<&'a [(usize, u8)], $mnemonic> {
                parcel::one_of(vec![
                    $(
                        parcel::parsers::byte::expect_byte($opcode),
                    )*
                ])
                    .map(|_| <$mnemonic>::default())
                    .parse(input)
            }
        }

        impl<'a> parcel::Parser<'a, &'a [(usize, char)], $mnemonic> for $mnemonic {
            fn parse(&self, input: &'a [(usize, char)]) -> parcel::ParseResult<&'a [(usize, char)], $mnemonic> {
                parcel::map(
                    parcel::parsers::character::expect_str($text),
                    |_| <$mnemonic>::default()
                ).parse(input)
            }
        }

        impl std::convert::TryFrom<&str> for $mnemonic {
            type Error = MnemonicErr;

            fn try_from(src: &str) -> Result<$mnemonic, Self::Error> {
                if src == $text {
                    Ok(<$mnemonic>::default())
                } else {
                    Err(MnemonicErr::ConversionErr(src.to_string()))
                }
            }
        }

        impl std::convert::From<$mnemonic> for &str {
            fn from(_: $mnemonic) -> &'static str {
               $text
            }
        }
    };
}

/// Load operand into Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct LDA;

generate_mnemonic_parser_and_offset!(LDA, "lda", 0xa9, 0xa5, 0xb5, 0xad, 0xbd, 0xb9, 0xa1, 0xb1);

/// Load operand into X Register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct LDX;

generate_mnemonic_parser_and_offset!(LDX, "ldx", 0xa2, 0xa6, 0xb6, 0xae, 0xbe);

/// Load operand into Y Register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct LDY;

generate_mnemonic_parser_and_offset!(LDY, "ldy", 0xa0, 0xa4, 0xb4, 0xac, 0xbc);

/// Store Accumulator in memory
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct STA;

generate_mnemonic_parser_and_offset!(STA, "sta", 0x8d, 0x85, 0x95, 0x9d, 0x99, 0x81, 0x91);

/// Store X register in memory.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct STX;

generate_mnemonic_parser_and_offset!(STX, "stx", 0x8e, 0x86, 0x96);

/// Story Y register in memory.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct STY;

generate_mnemonic_parser_and_offset!(STY, "sty", 0x8c, 0x84, 0x94);

// Arithmetic

/// Add Memory to Accumulator with carry.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ADC;

generate_mnemonic_parser_and_offset!(ADC, "adc", 0x6d, 0x7d, 0x79, 0x71, 0x69, 0x61, 0x65, 0x75);

/// Subtract memory from Accumulator with borrow.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct SBC;

generate_mnemonic_parser_and_offset!(SBC, "sbc", 0xed, 0xfd, 0xf9, 0xf1, 0xe9, 0xe1, 0xe5, 0xf5);

/// Increment Memory by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct INC;

generate_mnemonic_parser_and_offset!(INC, "inc", 0xee, 0xfe, 0xe6, 0xf6);

/// Increment X register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct INX;

generate_mnemonic_parser_and_offset!(INX, "inx", 0xe8);

/// Increment Y register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct INY;

generate_mnemonic_parser_and_offset!(INY, "iny", 0xc8);

/// Decrement memory by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct DEC;

generate_mnemonic_parser_and_offset!(DEC, "dec", 0xce, 0xde, 0xc6, 0xd6);

/// Decrement X register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct DEX;

generate_mnemonic_parser_and_offset!(DEX, "dex", 0xca);

/// Decrement Y register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct DEY;

generate_mnemonic_parser_and_offset!(DEY, "dey", 0x88);

// Shift and Rotate

/// Shift one bit left (Memory or Accumulator)
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ASL;

generate_mnemonic_parser_and_offset!(ASL, "asl", 0x0e, 0x1e, 0x0a, 0x06, 0x16);

/// Shift one bit right (Memory or Accumulator).
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct LSR;

generate_mnemonic_parser_and_offset!(LSR, "lsr", 0x4e, 0x5e, 0x4a, 0x46, 0x56);

/// Rotate one bit left (Memory or Accumulator).
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ROL;

generate_mnemonic_parser_and_offset!(ROL, "rol", 0x2e, 0x3e, 0x2a, 0x26, 0x36);

/// Rotate one bit right (Memory or Accumulator)
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ROR;

generate_mnemonic_parser_and_offset!(ROR, "ror", 0x6e, 0x7e, 0x6a, 0x66, 0x76);

/// And Memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct AND;

generate_mnemonic_parser_and_offset!(AND, "and", 0x2d, 0x3d, 0x39, 0x21, 0x29, 0x31, 0x25, 0x35);

/// Or memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ORA;

generate_mnemonic_parser_and_offset!(ORA, "ora", 0x0d, 0x1d, 0x19, 0x11, 0x09, 0x01, 0x05, 0x15);

/// Exclusive-Or memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct EOR;

generate_mnemonic_parser_and_offset!(EOR, "eor", 0x4d, 0x5d, 0x59, 0x51, 0x49, 0x41, 0x45, 0x55);

// Compare and Test Bit

/// Compare memory with Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct CMP;

generate_mnemonic_parser_and_offset!(CMP, "cmp", 0xc9, 0xcd, 0xc5, 0xd5, 0xdd, 0xd9, 0xc1, 0xd1);

/// Compare memory with X register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct CPX;

generate_mnemonic_parser_and_offset!(CPX, "cpx", 0xec, 0xe0, 0xe4);

/// Compare memory with X register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct CPY;

generate_mnemonic_parser_and_offset!(CPY, "cpy", 0xcc, 0xc0, 0xc4);

/// Test Bits in Memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BIT;

generate_mnemonic_parser_and_offset!(BIT, "bit", 0x24, 0x2c);

// Branch

/// Branch on carry clear
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BCC;

generate_mnemonic_parser_and_offset!(BCC, "bcc", 0x90);

/// Branch on carry set
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BCS;

generate_mnemonic_parser_and_offset!(BCS, "bcs", 0xb0);

/// Branch on Zero. Follows branch when the Zero flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BNE;

generate_mnemonic_parser_and_offset!(BNE, "bne", 0xd0);

/// Branch on Zero. Follows branch when the Zero flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BEQ;

generate_mnemonic_parser_and_offset!(BEQ, "beq", 0xf0);

/// Branch on positive. Follows branch when the negative flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BPL;

generate_mnemonic_parser_and_offset!(BPL, "bpl", 0x10);

/// Branch on negative. Follows branch when the negative flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BMI;

generate_mnemonic_parser_and_offset!(BMI, "bmi", 0x30);

/// Branch on Overflow clear. Follows branch when overflow flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BVC;

generate_mnemonic_parser_and_offset!(BVC, "bvc", 0x50);

/// Branch on Overflow. Follows branch when the overflow flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BVS;

generate_mnemonic_parser_and_offset!(BVS, "bvs", 0x70);

// Transfer
/// Transfer Accumulator to X
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct TAX;

generate_mnemonic_parser_and_offset!(TAX, "tax", 0xaa);

/// Transfer X to Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct TXA;

generate_mnemonic_parser_and_offset!(TXA, "txa", 0x8a);

/// Transfer Accumulator to Y
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct TAY;

generate_mnemonic_parser_and_offset!(TAY, "tay", 0xa8);

/// Transfer Y to Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct TYA;

generate_mnemonic_parser_and_offset!(TYA, "tya", 0x98);

/// Transfer Stack Pointer to X
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct TSX;

generate_mnemonic_parser_and_offset!(TSX, "tsx", 0xba);

/// Transfer X to Stack Pointer
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct TXS;

generate_mnemonic_parser_and_offset!(TXS, "txs", 0x9a);

// Stack Operations

/// Push Accumulator on stack
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct PHA;

generate_mnemonic_parser_and_offset!(PHA, "pha", 0x48);

/// Pull Accumulator from stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct PLA;

generate_mnemonic_parser_and_offset!(PLA, "pla", 0x46);

/// Push Processor Status to stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct PHP;

generate_mnemonic_parser_and_offset!(PHP, "php", 0x08);

/// Pull Processor Status from stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct PLP;

generate_mnemonic_parser_and_offset!(PLP, "plp", 0x28);

// Subroutines and Jump

/// Jump
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct JMP;

generate_mnemonic_parser_and_offset!(JMP, "jmp", 0x4c, 0x6c);

/// Jump to a new location saving the return address.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct JSR;

generate_mnemonic_parser_and_offset!(JSR, "jsr", 0x20);

/// Return from subroutine.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct RTS;

generate_mnemonic_parser_and_offset!(RTS, "rts", 0x60);

/// Return from interrupt.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct RTI;

generate_mnemonic_parser_and_offset!(RTI, "rti", 0x40);

// Set and Clear

/// Clear carry
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct CLC;

generate_mnemonic_parser_and_offset!(CLC, "clc", 0xad);

/// Set carry
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct SEC;

generate_mnemonic_parser_and_offset!(SEC, "sec", 0x38);

/// Clear decimal
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct CLD;

generate_mnemonic_parser_and_offset!(CLD, "cld", 0xd8);

/// Set decimal
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct SED;

generate_mnemonic_parser_and_offset!(SED, "sed", 0xf8);

/// Clear interrupt disable
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct CLI;

generate_mnemonic_parser_and_offset!(CLI, "cli", 0x58);

/// Set interrupt disable
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct SEI;

generate_mnemonic_parser_and_offset!(SEI, "sei", 0x78);

/// Clear overflow
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct CLV;

generate_mnemonic_parser_and_offset!(CLV, "clv", 0xb8);

// Misc

/// Force Break
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct BRK;

generate_mnemonic_parser_and_offset!(BRK, "brk", 0x00);

/// No operation
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct NOP;

generate_mnemonic_parser_and_offset!(NOP, "nop", 0xea);

/// Mnemonic stores an enum representing every possible mnemonic.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Mnemonic {
    // Load-Store
    LDA,
    LDX,
    LDY,
    STA,
    STX,
    STY,

    // Arithmetic
    ADC,
    SBC,
    INC,
    INX,
    INY,
    DEC,
    DEX,
    DEY,

    // Shift and Rotate
    ASL,
    LSR,
    ROL,
    ROR,
    AND,
    ORA,
    EOR,

    // Compare and Test Bit
    CMP,
    CPX,
    CPY,
    BIT,

    // Branch
    BCC,
    BCS,
    BNE,
    BEQ,
    BPL,
    BMI,
    BVC,
    BVS,

    // Transfer
    TAX,
    TXA,
    TAY,
    TYA,
    TSX,
    TXS,

    // Stack
    PHA,
    PLA,
    PHP,
    PLP,

    // Subroutines and Jump
    JMP,
    JSR,
    RTS,
    RTI,

    // Set and Clear
    CLC,
    SEC,
    CLD,
    SED,
    CLI,
    SEI,
    CLV,

    // Misc
    BRK,
    NOP,
}

impl crate::ByteSized for Mnemonic {
    fn byte_size(&self) -> usize {
        1
    }
}

impl std::convert::TryFrom<&str> for Mnemonic {
    type Error = String;

    fn try_from(src: &str) -> Result<Mnemonic, Self::Error> {
        match src {
            "lda" => Ok(Mnemonic::LDA),
            "ldx" => Ok(Mnemonic::LDX),
            "ldy" => Ok(Mnemonic::LDY),
            "sta" => Ok(Mnemonic::STA),
            "stx" => Ok(Mnemonic::STX),
            "sty" => Ok(Mnemonic::STY),
            "adc" => Ok(Mnemonic::ADC),
            "sbc" => Ok(Mnemonic::SBC),
            "inc" => Ok(Mnemonic::INC),
            "inx" => Ok(Mnemonic::INX),
            "iny" => Ok(Mnemonic::INY),
            "dec" => Ok(Mnemonic::DEC),
            "dex" => Ok(Mnemonic::DEX),
            "dey" => Ok(Mnemonic::DEY),
            "asl" => Ok(Mnemonic::ASL),
            "lsr" => Ok(Mnemonic::LSR),
            "rol" => Ok(Mnemonic::ROL),
            "ror" => Ok(Mnemonic::ROR),
            "and" => Ok(Mnemonic::AND),
            "ora" => Ok(Mnemonic::ORA),
            "eor" => Ok(Mnemonic::EOR),
            "cmp" => Ok(Mnemonic::CMP),
            "cpx" => Ok(Mnemonic::CPX),
            "cpy" => Ok(Mnemonic::CPY),
            "bit" => Ok(Mnemonic::BIT),
            "bcc" => Ok(Mnemonic::BCC),
            "bcs" => Ok(Mnemonic::BCS),
            "bnd" => Ok(Mnemonic::BNE),
            "beq" => Ok(Mnemonic::BEQ),
            "bpl" => Ok(Mnemonic::BPL),
            "bmi" => Ok(Mnemonic::BMI),
            "bvc" => Ok(Mnemonic::BVC),
            "bvs" => Ok(Mnemonic::BVS),
            "tax" => Ok(Mnemonic::TAX),
            "txa" => Ok(Mnemonic::TXA),
            "tay" => Ok(Mnemonic::TAY),
            "tya" => Ok(Mnemonic::TYA),
            "tsx" => Ok(Mnemonic::TSX),
            "txs" => Ok(Mnemonic::TXS),
            "pha" => Ok(Mnemonic::PHA),
            "pla" => Ok(Mnemonic::PLA),
            "php" => Ok(Mnemonic::PHP),
            "plp" => Ok(Mnemonic::PLP),
            "jmp" => Ok(Mnemonic::JMP),
            "jsr" => Ok(Mnemonic::JSR),
            "rts" => Ok(Mnemonic::RTS),
            "rti" => Ok(Mnemonic::RTI),
            "clc" => Ok(Mnemonic::CLC),
            "sec" => Ok(Mnemonic::SEC),
            "cld" => Ok(Mnemonic::CLD),
            "sed" => Ok(Mnemonic::SED),
            "cli" => Ok(Mnemonic::CLI),
            "sei" => Ok(Mnemonic::SEI),
            "clv" => Ok(Mnemonic::CLV),
            "brk" => Ok(Mnemonic::BRK),
            "nop" => Ok(Mnemonic::NOP),
            _ => Err(MnemonicErr::ConversionErr(src.to_string()).to_string()),
        }
    }
}
