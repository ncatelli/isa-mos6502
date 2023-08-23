#[cfg(feature = "parcel")]
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

        #[cfg(feature = "parcel")]
        impl<'a> parcel::Parser<'a, &'a [(usize, u8)], $mnemonic> for $mnemonic {
            fn parse(&self, input: &'a [(usize, u8)]) -> parcel::ParseResult<&'a [(usize, u8)], $mnemonic> {
                parcel::map(
                    parcel::parsers::byte::expect_byte($opcode),
                    |_| <$mnemonic>::default()
                ).parse(input)
            }
        }

        #[cfg(feature = "parcel")]
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

        #[cfg(feature = "parcel")]
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

        #[cfg(feature = "parcel")]
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
pub struct Lda;

generate_mnemonic_parser_and_offset!(Lda, "lda", 0xa9, 0xa5, 0xb5, 0xad, 0xbd, 0xb9, 0xa1, 0xb1);

/// Load operand into X Register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ldx;

generate_mnemonic_parser_and_offset!(Ldx, "ldx", 0xa2, 0xa6, 0xb6, 0xae, 0xbe);

/// Load operand into Y Register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ldy;

generate_mnemonic_parser_and_offset!(Ldy, "ldy", 0xa0, 0xa4, 0xb4, 0xac, 0xbc);

/// Store Accumulator in memory
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sta;

generate_mnemonic_parser_and_offset!(Sta, "sta", 0x8d, 0x85, 0x95, 0x9d, 0x99, 0x81, 0x91);

/// Store X register in memory.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Stx;

generate_mnemonic_parser_and_offset!(Stx, "stx", 0x8e, 0x86, 0x96);

/// Story Y register in memory.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sty;

generate_mnemonic_parser_and_offset!(Sty, "sty", 0x8c, 0x84, 0x94);

// Arithmetic

/// Add Memory to Accumulator with carry.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Adc;

generate_mnemonic_parser_and_offset!(Adc, "adc", 0x6d, 0x7d, 0x79, 0x71, 0x69, 0x61, 0x65, 0x75);

/// Subtract memory from Accumulator with borrow.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sbc;

generate_mnemonic_parser_and_offset!(Sbc, "sbc", 0xed, 0xfd, 0xf9, 0xf1, 0xe9, 0xe1, 0xe5, 0xf5);

/// Increment Memory by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Inc;

generate_mnemonic_parser_and_offset!(Inc, "inc", 0xee, 0xfe, 0xe6, 0xf6);

/// Increment X register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Inx;

generate_mnemonic_parser_and_offset!(Inx, "inx", 0xe8);

/// Increment Y register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Iny;

generate_mnemonic_parser_and_offset!(Iny, "iny", 0xc8);

/// Decrement memory by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Dec;

generate_mnemonic_parser_and_offset!(Dec, "dec", 0xce, 0xde, 0xc6, 0xd6);

/// Decrement X register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Dex;

generate_mnemonic_parser_and_offset!(Dex, "dex", 0xca);

/// Decrement Y register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Dey;

generate_mnemonic_parser_and_offset!(Dey, "dey", 0x88);

// Shift and Rotate

/// Shift one bit left (Memory or Accumulator)
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Asl;

generate_mnemonic_parser_and_offset!(Asl, "asl", 0x0e, 0x1e, 0x0a, 0x06, 0x16);

/// Shift one bit right (Memory or Accumulator).
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Lsr;

generate_mnemonic_parser_and_offset!(Lsr, "lsr", 0x4e, 0x5e, 0x4a, 0x46, 0x56);

/// Rotate one bit left (Memory or Accumulator).
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Rol;

generate_mnemonic_parser_and_offset!(Rol, "rol", 0x2e, 0x3e, 0x2a, 0x26, 0x36);

/// Rotate one bit right (Memory or Accumulator)
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ror;

generate_mnemonic_parser_and_offset!(Ror, "ror", 0x6e, 0x7e, 0x6a, 0x66, 0x76);

/// And Memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct And;

generate_mnemonic_parser_and_offset!(And, "and", 0x2d, 0x3d, 0x39, 0x21, 0x29, 0x31, 0x25, 0x35);

/// Or memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ora;

generate_mnemonic_parser_and_offset!(Ora, "ora", 0x0d, 0x1d, 0x19, 0x11, 0x09, 0x01, 0x05, 0x15);

/// Exclusive-Or memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Eor;

generate_mnemonic_parser_and_offset!(Eor, "eor", 0x4d, 0x5d, 0x59, 0x51, 0x49, 0x41, 0x45, 0x55);

// Compare and Test Bit

/// Compare memory with Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cmp;

generate_mnemonic_parser_and_offset!(Cmp, "cmp", 0xc9, 0xcd, 0xc5, 0xd5, 0xdd, 0xd9, 0xc1, 0xd1);

/// Compare memory with X register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cpx;

generate_mnemonic_parser_and_offset!(Cpx, "cpx", 0xec, 0xe0, 0xe4);

/// Compare memory with X register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cpy;

generate_mnemonic_parser_and_offset!(Cpy, "cpy", 0xcc, 0xc0, 0xc4);

/// Test Bits in Memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bit;

generate_mnemonic_parser_and_offset!(Bit, "bit", 0x24, 0x2c);

// Branch

/// Branch on carry clear
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bcc;

generate_mnemonic_parser_and_offset!(Bcc, "bcc", 0x90);

/// Branch on carry set
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bcs;

generate_mnemonic_parser_and_offset!(Bcs, "bcs", 0xb0);

/// Branch on Zero. Follows branch when the Zero flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bne;

generate_mnemonic_parser_and_offset!(Bne, "bne", 0xd0);

/// Branch on Zero. Follows branch when the Zero flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Beq;

generate_mnemonic_parser_and_offset!(Beq, "beq", 0xf0);

/// Branch on positive. Follows branch when the negative flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bpl;

generate_mnemonic_parser_and_offset!(Bpl, "bpl", 0x10);

/// Branch on negative. Follows branch when the negative flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bmi;

generate_mnemonic_parser_and_offset!(Bmi, "bmi", 0x30);

/// Branch on Overflow clear. Follows branch when overflow flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bvc;

generate_mnemonic_parser_and_offset!(Bvc, "bvc", 0x50);

/// Branch on Overflow. Follows branch when the overflow flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bvs;

generate_mnemonic_parser_and_offset!(Bvs, "bvs", 0x70);

// Transfer
/// Transfer Accumulator to X
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tax;

generate_mnemonic_parser_and_offset!(Tax, "tax", 0xaa);

/// Transfer X to Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Txa;

generate_mnemonic_parser_and_offset!(Txa, "txa", 0x8a);

/// Transfer Accumulator to Y
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tay;

generate_mnemonic_parser_and_offset!(Tay, "tay", 0xa8);

/// Transfer Y to Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tya;

generate_mnemonic_parser_and_offset!(Tya, "tya", 0x98);

/// Transfer Stack Pointer to X
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tsx;

generate_mnemonic_parser_and_offset!(Tsx, "tsx", 0xba);

/// Transfer X to Stack Pointer
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Txs;

generate_mnemonic_parser_and_offset!(Txs, "txs", 0x9a);

// Stack Operations

/// Push Accumulator on stack
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Pha;

generate_mnemonic_parser_and_offset!(Pha, "pha", 0x48);

/// Pull Accumulator from stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Pla;

generate_mnemonic_parser_and_offset!(Pla, "pla", 0x46);

/// Push Processor Status to stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Php;

generate_mnemonic_parser_and_offset!(Php, "php", 0x08);

/// Pull Processor Status from stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Plp;

generate_mnemonic_parser_and_offset!(Plp, "plp", 0x28);

// Subroutines and Jump

/// Jump
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Jmp;

generate_mnemonic_parser_and_offset!(Jmp, "jmp", 0x4c, 0x6c);

/// Jump to a new location saving the return address.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Jsr;

generate_mnemonic_parser_and_offset!(Jsr, "jsr", 0x20);

/// Return from subroutine.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Rts;

generate_mnemonic_parser_and_offset!(Rts, "rts", 0x60);

/// Return from interrupt.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Rti;

generate_mnemonic_parser_and_offset!(Rti, "rti", 0x40);

// Set and Clear

/// Clear carry
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Clc;

generate_mnemonic_parser_and_offset!(Clc, "clc", 0xad);

/// Set carry
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sec;

generate_mnemonic_parser_and_offset!(Sec, "sec", 0x38);

/// Clear decimal
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cld;

generate_mnemonic_parser_and_offset!(Cld, "cld", 0xd8);

/// Set decimal
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sed;

generate_mnemonic_parser_and_offset!(Sed, "sed", 0xf8);

/// Clear interrupt disable
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cli;

generate_mnemonic_parser_and_offset!(Cli, "cli", 0x58);

/// Set interrupt disable
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sei;

generate_mnemonic_parser_and_offset!(Sei, "sei", 0x78);

/// Clear overflow
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Clv;

generate_mnemonic_parser_and_offset!(Clv, "clv", 0xb8);

// Misc

/// Force Break
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Brk;

generate_mnemonic_parser_and_offset!(Brk, "brk", 0x00);

/// No operation
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Nop;

generate_mnemonic_parser_and_offset!(Nop, "nop", 0xea);

/// Mnemonic stores an enum representing every possible mnemonic.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Mnemonic {
    // Load-Store
    Lda,
    Ldx,
    Ldy,
    Sta,
    Stx,
    Sty,

    // Arithmetic
    Adc,
    Sbc,
    Inc,
    Inx,
    Iny,
    Dec,
    Dex,
    Dey,

    // Shift and Rotate
    Asl,
    Lsr,
    Rol,
    Ror,
    And,
    Ora,
    Eor,

    // Compare and Test Bit
    Cmp,
    Cpx,
    Cpy,
    Bit,

    // Branch
    Bcc,
    Bcs,
    Bne,
    Beq,
    Bpl,
    Bmi,
    Bvc,
    Bvs,

    // Transfer
    Tax,
    Txa,
    Tay,
    Tya,
    Tsx,
    Txs,

    // Stack
    Pha,
    Pla,
    Php,
    Plp,

    // Subroutines and Jump
    Jmp,
    Jsr,
    Rts,
    Rti,

    // Set and Clear
    Clc,
    Sec,
    Cld,
    Sed,
    Cli,
    Sei,
    Clv,

    // Misc
    Brk,
    Nop,
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
            "lda" => Ok(Mnemonic::Lda),
            "ldx" => Ok(Mnemonic::Ldx),
            "ldy" => Ok(Mnemonic::Ldy),
            "sta" => Ok(Mnemonic::Sta),
            "stx" => Ok(Mnemonic::Stx),
            "sty" => Ok(Mnemonic::Sty),
            "adc" => Ok(Mnemonic::Adc),
            "sbc" => Ok(Mnemonic::Sbc),
            "inc" => Ok(Mnemonic::Inc),
            "inx" => Ok(Mnemonic::Inx),
            "iny" => Ok(Mnemonic::Iny),
            "dec" => Ok(Mnemonic::Dec),
            "dex" => Ok(Mnemonic::Dex),
            "dey" => Ok(Mnemonic::Dey),
            "asl" => Ok(Mnemonic::Asl),
            "lsr" => Ok(Mnemonic::Lsr),
            "rol" => Ok(Mnemonic::Rol),
            "ror" => Ok(Mnemonic::Ror),
            "and" => Ok(Mnemonic::And),
            "ora" => Ok(Mnemonic::Ora),
            "eor" => Ok(Mnemonic::Eor),
            "cmp" => Ok(Mnemonic::Cmp),
            "cpx" => Ok(Mnemonic::Cpx),
            "cpy" => Ok(Mnemonic::Cpy),
            "bit" => Ok(Mnemonic::Bit),
            "bcc" => Ok(Mnemonic::Bcc),
            "bcs" => Ok(Mnemonic::Bcs),
            "bnd" => Ok(Mnemonic::Bne),
            "beq" => Ok(Mnemonic::Beq),
            "bpl" => Ok(Mnemonic::Bpl),
            "bmi" => Ok(Mnemonic::Bmi),
            "bvc" => Ok(Mnemonic::Bvc),
            "bvs" => Ok(Mnemonic::Bvs),
            "tax" => Ok(Mnemonic::Tax),
            "txa" => Ok(Mnemonic::Txa),
            "tay" => Ok(Mnemonic::Tay),
            "tya" => Ok(Mnemonic::Tya),
            "tsx" => Ok(Mnemonic::Tsx),
            "txs" => Ok(Mnemonic::Txs),
            "pha" => Ok(Mnemonic::Pha),
            "pla" => Ok(Mnemonic::Pla),
            "php" => Ok(Mnemonic::Php),
            "plp" => Ok(Mnemonic::Plp),
            "jmp" => Ok(Mnemonic::Jmp),
            "jsr" => Ok(Mnemonic::Jsr),
            "rts" => Ok(Mnemonic::Rts),
            "rti" => Ok(Mnemonic::Rti),
            "clc" => Ok(Mnemonic::Clc),
            "sec" => Ok(Mnemonic::Sec),
            "cld" => Ok(Mnemonic::Cld),
            "sed" => Ok(Mnemonic::Sed),
            "cli" => Ok(Mnemonic::Cli),
            "sei" => Ok(Mnemonic::Sei),
            "clv" => Ok(Mnemonic::Clv),
            "brk" => Ok(Mnemonic::Brk),
            "nop" => Ok(Mnemonic::Nop),
            _ => Err(MnemonicErr::ConversionErr(src.to_string()).to_string()),
        }
    }
}
