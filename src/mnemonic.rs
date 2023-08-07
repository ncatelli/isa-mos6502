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
    ($mnemonic:ty, $text:literal) => {
        impl ByteSized for $mnemonic {}

        impl<'a> parcel::Parser<'a, &'a [(usize, char)], $mnemonic> for $mnemonic {
            fn parse(
                &self,
                input: &'a [(usize, char)],
            ) -> parcel::ParseResult<&'a [(usize, char)], $mnemonic> {
                parcel::map(parcel::parsers::character::expect_str($text), |_| {
                    <$mnemonic>::default()
                })
                .parse(input)
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

generate_mnemonic_parser_and_offset!(Lda, "lda");

/// Load operand into X Register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ldx;

generate_mnemonic_parser_and_offset!(Ldx, "ldx");

/// Load operand into Y Register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ldy;

generate_mnemonic_parser_and_offset!(Ldy, "ldy");

/// Store Accumulator in memory
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sta;

generate_mnemonic_parser_and_offset!(Sta, "sta");

/// Store X register in memory.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Stx;

generate_mnemonic_parser_and_offset!(Stx, "stx");

/// Story Y register in memory.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sty;

generate_mnemonic_parser_and_offset!(Sty, "sty");

// Arithmetic

/// Add Memory to Accumulator with carry.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Adc;

generate_mnemonic_parser_and_offset!(Adc, "adc");

/// Subtract memory from Accumulator with borrow.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sbc;

generate_mnemonic_parser_and_offset!(Sbc, "sbc");

/// Increment Memory by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Inc;

generate_mnemonic_parser_and_offset!(Inc, "inc");

/// Increment X register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Inx;

generate_mnemonic_parser_and_offset!(Inx, "inx");

/// Increment Y register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Iny;

generate_mnemonic_parser_and_offset!(Iny, "iny");

/// Decrement memory by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Dec;

generate_mnemonic_parser_and_offset!(Dec, "dec");

/// Decrement X register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Dex;

generate_mnemonic_parser_and_offset!(Dex, "dex");

/// Decrement Y register by one.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Dey;

generate_mnemonic_parser_and_offset!(Dey, "dey");

// Shift and Rotate

/// Shift one bit left (Memory or Accumulator)
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Asl;

generate_mnemonic_parser_and_offset!(Asl, "asl");

/// Shift one bit right (Memory or Accumulator).
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Lsr;

generate_mnemonic_parser_and_offset!(Lsr, "lsr");

/// Rotate one bit left (Memory or Accumulator).
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Rol;

generate_mnemonic_parser_and_offset!(Rol, "rol");

/// Rotate one bit right (Memory or Accumulator)
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ror;

generate_mnemonic_parser_and_offset!(Ror, "ror");

/// And Memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct And;

generate_mnemonic_parser_and_offset!(And, "and");

/// Or memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Ora;

generate_mnemonic_parser_and_offset!(Ora, "ora");

/// Exclusive-Or memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Eor;

generate_mnemonic_parser_and_offset!(Eor, "eor");

// Compare and Test Bit

/// Compare memory with Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cmp;

generate_mnemonic_parser_and_offset!(Cmp, "cmp");

/// Compare memory with X register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cpx;

generate_mnemonic_parser_and_offset!(Cpx, "cpx");

/// Compare memory with X register
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cpy;

generate_mnemonic_parser_and_offset!(Cpy, "cpy");

/// Test Bits in Memory with Accumulator.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bit;

generate_mnemonic_parser_and_offset!(Bit, "bit");

// Branch

/// Branch on carry clear
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bcc;

generate_mnemonic_parser_and_offset!(Bcc, "bcc");

/// Branch on carry set
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bcs;

generate_mnemonic_parser_and_offset!(Bcs, "bcs");

/// Branch on Zero. Follows branch when the Zero flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bne;

generate_mnemonic_parser_and_offset!(Bne, "bne");

/// Branch on Zero. Follows branch when the Zero flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Beq;

generate_mnemonic_parser_and_offset!(Beq, "beq");

/// Branch on positive. Follows branch when the negative flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bpl;

generate_mnemonic_parser_and_offset!(Bpl, "bpl");

/// Branch on negative. Follows branch when the negative flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bmi;

generate_mnemonic_parser_and_offset!(Bmi, "bmi");

/// Branch on Overflow clear. Follows branch when overflow flag is not set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bvc;

generate_mnemonic_parser_and_offset!(Bvc, "bvc");

/// Branch on Overflow. Follows branch when the overflow flag is set.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Bvs;

generate_mnemonic_parser_and_offset!(Bvs, "bvs");

// Transfer
/// Transfer Accumulator to X
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tax;

generate_mnemonic_parser_and_offset!(Tax, "tax");

/// Transfer X to Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Txa;

generate_mnemonic_parser_and_offset!(Txa, "txa");

/// Transfer Accumulator to Y
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tay;

generate_mnemonic_parser_and_offset!(Tay, "tay");

/// Transfer Y to Accumulator
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tya;

generate_mnemonic_parser_and_offset!(Tya, "tya");

/// Transfer Stack Pointer to X
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Tsx;

generate_mnemonic_parser_and_offset!(Tsx, "tsx");

/// Transfer X to Stack Pointer
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Txs;

generate_mnemonic_parser_and_offset!(Txs, "txs");

// Stack Operations

/// Push Accumulator on stack
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Pha;

generate_mnemonic_parser_and_offset!(Pha, "pha");

/// Pull Accumulator from stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Pla;

generate_mnemonic_parser_and_offset!(Pla, "pla");

/// Push Processor Status to stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Php;

generate_mnemonic_parser_and_offset!(Php, "php");

/// Pull Processor Status from stack.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Plp;

generate_mnemonic_parser_and_offset!(Plp, "plp");

// Subroutines and Jump

/// Jump
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Jmp;

generate_mnemonic_parser_and_offset!(Jmp, "jmp");

/// Jump to a new location saving the return address.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Jsr;

generate_mnemonic_parser_and_offset!(Jsr, "jsr");

/// Return from subroutine.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Rts;

generate_mnemonic_parser_and_offset!(Rts, "rts");

/// Return from interrupt.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Rti;

generate_mnemonic_parser_and_offset!(Rti, "rti");

// Set and Clear

/// Clear carry
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Clc;

generate_mnemonic_parser_and_offset!(Clc, "clc");

/// Set carry
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sec;

generate_mnemonic_parser_and_offset!(Sec, "sec");

/// Clear decimal
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cld;

generate_mnemonic_parser_and_offset!(Cld, "cld");

/// Set decimal
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sed;

generate_mnemonic_parser_and_offset!(Sed, "sed");

/// Clear interrupt disable
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Cli;

generate_mnemonic_parser_and_offset!(Cli, "cli");

/// Set interrupt disable
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Sei;

generate_mnemonic_parser_and_offset!(Sei, "sei");

/// Clear overflow
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Clv;

generate_mnemonic_parser_and_offset!(Clv, "clv");

// Misc

/// Force Break
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Brk;

generate_mnemonic_parser_and_offset!(Brk, "brk");

/// No operation
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Nop;

generate_mnemonic_parser_and_offset!(Nop, "nop");

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
