//! This crate stores helper types for all mnemonics and addressing modes for
//! the MOS6502 ISA. In addition, these types provide helpers for the
//! translation between the bytecode and an intermediate representation of the
//! instruction set.

use std::convert::TryInto;
use std::fmt::Debug;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InstructionErr {
    ConversionErr,
    InvalidInstruction(mnemonic::Mnemonic, addressing_mode::AddressingModeType),
}

impl std::fmt::Display for InstructionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConversionErr => write!(f, "invalid conversion"),
            Self::InvalidInstruction(a, m) => {
                write!(f, "invalid instruction: Instruction({:?}, {:?})", a, m)
            }
        }
    }
}

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
pub mod bit_decoder;
pub mod mnemonic;

type Bytecode = Vec<u8>;

/// Instruction represents a single mos6502 instruction, taking a mnemonic and address mode as parameters.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Instruction<M, A>
where
    M: ByteSized + Copy + Debug + PartialEq,
    A: ByteSized + Copy + Debug + PartialEq,
{
    pub mnemonic: M,
    pub addressing_mode: A,
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

#[allow(unused_variables)]
macro_rules! generate_instruction_variant_match_case_to_inst {
    ($mnemonic:tt, Implied, $variant:tt) => {
        Self::$variant
    };
    ($mnemonic:tt, Accumulator, $variant:tt) => {
        Self::$variant
    };
    ($mnemonic:tt, $am:tt, $variant:tt) => {
        Self::$variant(_)
    };
}

macro_rules! generate_instruction_variant_conversion {
    ($mnemonic:tt, Implied, $variant:tt) => {
        impl
            std::convert::From<
                $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::Implied>,
            > for $crate::InstructionVariant
        {
            fn from(
                _: $crate::Instruction<
                    $crate::mnemonic::$mnemonic,
                    $crate::addressing_mode::Implied,
                >,
            ) -> Self {
                $crate::InstructionVariant::$variant
            }
        }

        impl std::convert::TryFrom<$crate::InstructionVariant>
            for $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::Implied>
        {
            type Error = InstructionErr;

            fn try_from(src: $crate::InstructionVariant) -> Result<Self, Self::Error> {
                if src == $crate::InstructionVariant::$variant {
                    Ok($crate::Instruction::new(
                        <$crate::mnemonic::$mnemonic>::default(),
                        <$crate::addressing_mode::Implied>::default(),
                    ))
                } else {
                    Err(InstructionErr::ConversionErr)
                }
            }
        }
    };
    ($mnemonic:tt, Accumulator, $variant:tt) => {
        impl
            std::convert::From<
                $crate::Instruction<
                    $crate::mnemonic::$mnemonic,
                    $crate::addressing_mode::Accumulator,
                >,
            > for crate::InstructionVariant
        {
            fn from(
                _: $crate::Instruction<
                    $crate::mnemonic::$mnemonic,
                    $crate::addressing_mode::Accumulator,
                >,
            ) -> Self {
                $crate::InstructionVariant::$variant
            }
        }

        impl std::convert::TryFrom<$crate::InstructionVariant>
            for $crate::Instruction<
                $crate::mnemonic::$mnemonic,
                $crate::addressing_mode::Accumulator,
            >
        {
            type Error = InstructionErr;

            fn try_from(src: $crate::InstructionVariant) -> Result<Self, Self::Error> {
                if src == $crate::InstructionVariant::$variant {
                    Ok($crate::Instruction::new(
                        <$crate::mnemonic::$mnemonic>::default(),
                        <$crate::addressing_mode::Accumulator>::default(),
                    ))
                } else {
                    Err(InstructionErr::ConversionErr)
                }
            }
        }
    };
    ($mnemonic:tt, $am:tt, $variant:tt) => {
        impl
            std::convert::From<
                $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::$am>,
            > for crate::InstructionVariant
        {
            fn from(
                src: $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::$am>,
            ) -> Self {
                $crate::InstructionVariant::$variant(src.addressing_mode.unwrap())
            }
        }

        impl std::convert::TryFrom<$crate::InstructionVariant>
            for $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::$am>
        {
            type Error = InstructionErr;

            fn try_from(src: $crate::InstructionVariant) -> Result<Self, Self::Error> {
                if let $crate::InstructionVariant::$variant(val) = src {
                    Ok($crate::Instruction::new(
                        <$crate::mnemonic::$mnemonic>::default(),
                        $crate::addressing_mode::$am(val),
                    ))
                } else {
                    Err(InstructionErr::ConversionErr)
                }
            }
        }
    };
}

macro_rules! generate_instructions {
    ($($name:ident: $mnc:tt, $am:tt, $variant:tt, $opcode:expr, $cycles:expr,)*) => {

        // For each valid Instruction<Mnemonic, Addressing Mode> pairing
        $(
            impl $crate::CycleCost for $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am> {
                fn cycles(&self) -> usize {
                    $cycles
                }
            }

            #[cfg(feature = "parcel")]
            impl<'a> parcel::Parser<'a, &'a [(usize, u8)], $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>>
                for $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>
            {
                fn parse(
                    &self,
                    input: &'a [(usize, u8)],
                ) -> parcel::ParseResult<&'a [(usize, u8)], $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>> {
                    // If the expected opcode and addressing mode match, map it to a
                    // corresponding Instruction.
                    parcel::map(
                        parcel::and_then(parcel::parsers::byte::expect_byte($opcode), |_| <$crate::addressing_mode::$am>::default()),
                        |am| $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), am),
                    )
                    .parse(input)
                }
            }

            // Covert the addressing mode contests to a little-endian bytecode
            // vector and chain that to a vector containing the instructions
            // opcode.
            impl std::convert::From<$crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>> for Bytecode {
                fn from(src: $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>) -> Self {
                    let am_bytecode: Vec<u8> = src.addressing_mode.into();
                    vec![$opcode].into_iter().chain(
                        am_bytecode.into_iter()
                    ).collect()
                }
            }

            // convert instruction to variant
            generate_instruction_variant_conversion!{$mnc, $am, $variant}

            impl IntoIterator for Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am> {
                type Item = u8;
                type IntoIter = std::vec::IntoIter<Self::Item>;

                fn into_iter(self) -> Self::IntoIter {
                    let item: Vec<Self::Item> = self.into();
                    item.into_iter()
                }
            }
        )*

        // Generate Variant implementations of Instruction-specific commands.
        impl $crate::CycleCost for $crate::InstructionVariant {
            fn cycles(&self) -> usize {
                match self {
                    $(
                        generate_instruction_variant_match_case_to_inst!($mnc, $am, $variant) => $cycles,
                    )*
                }
            }
        }


        // Generate Variant implementations of Instruction-specific commands.
        impl $crate::ByteSized for $crate::InstructionVariant {
            fn byte_size(&self) -> usize {
                match self {
                    $(
                        generate_instruction_variant_match_case_to_inst!($mnc, $am, $variant) => $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <$crate::addressing_mode::$am>::default()).byte_size(),
                    )*
                }
            }
        }

        // General parser tests
        #[cfg(test)]
        mod tests {
            mod parser {
                #[cfg(feature = "parcel")]
                use parcel::prelude::v1::Parser;
                $(
                    #[test]
                    fn $name() {
                        let bytecode = [$opcode, 0x00, 0x00];
                        let expected = $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <$crate::addressing_mode::$am>::default());

                        #[cfg(feature = "parcel")]
                        let enumerated_bytes: Vec<(usize, u8)> = bytecode.iter().copied().enumerate().collect();

                        #[cfg(feature = "parcel")]
                        // assert parcel parse matches expected
                        assert_eq!(
                            expected,
                            $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <$crate::addressing_mode::$am>::default()).parse(&enumerated_bytes).unwrap().unwrap()
                        );

                        // assert decoded bytes matches parsed bytes;
                        let decoded = $crate::parse_instruction(&bytecode);
                        assert_eq!(decoded, Some(expected.into()));

                    }
                )*
            }

            mod conversion {
                #[test]
                fn conversion_from_generic_to_concrete() {
                    assert_eq!(
                        $crate::InstructionVariant::NopImplied,
                        std::convert::From::from($crate::Instruction::new(<$crate::mnemonic::Nop>::default(), <$crate::addressing_mode::Implied>::default()))
                    )
                }

                #[test]
                fn conversion_from_concrete_to_generic() {
                    assert_eq!(
                        Ok($crate::Instruction::new(<$crate::mnemonic::Nop>::default(), <$crate::addressing_mode::Implied>::default())),
                        std::convert::TryFrom::try_from($crate::InstructionVariant::NopImplied),
                    )
                }
            }

            mod bytecode {
                $(
                    #[test]
                    fn $name() {
                        let mut bytecode = $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <$crate::addressing_mode::$am>::default()).into_iter();
                        assert_eq!(
                            Some($opcode),
                            bytecode.next(),
                        )
                    }
                )*
            }
        }
    };
}

// represents each instruction in the format of:
// Parse Test Name, Mnemonic, Addressing Mode, Opcode, Instruction Cycle Count
#[rustfmt::skip]
generate_instructions!(
    adc_absolute: Adc, Absolute, AdcAbsolute, 0x6d, 4,
    adc_absolute_indexed_with_x: Adc, AbsoluteIndexedWithX, AdcAbsoluteIndexedWithX, 0x7d, 4,
    adc_absolute_indexed_with_y: Adc, AbsoluteIndexedWithY, AdcAbsoluteIndexedWithY, 0x79, 4,
    adc_indirect_y_indexed: Adc, IndirectYIndexed, AdcIndirectYIndexed, 0x71, 5,
    adc_immediate: Adc, Immediate, AdcImmediate, 0x69, 2,
    adc_x_indexed_indirect: Adc, XIndexedIndirect, AdcXIndexedIndirect, 0x61, 6,
    adc_zeropage: Adc, ZeroPage, AdcZeroPage, 0x65, 3,
    adc_zeropage_indexed_with_x: Adc, ZeroPageIndexedWithX, AdcZeroPageIndexedWithX, 0x75, 4,
    sbc_absolute: Sbc, Absolute, SbcAbsolute, 0xed, 4,
    sbc_absolute_indexed_with_x: Sbc, AbsoluteIndexedWithX, SbcAbsoluteIndexedWithX, 0xfd, 4,
    sbc_absolute_indexed_with_y: Sbc, AbsoluteIndexedWithY, SbcAbsoluteIndexedWithY, 0xf9, 4,
    sbc_indirect_y_indexed: Sbc, IndirectYIndexed, SbcIndirectYIndexed, 0xf1, 5,
    sbc_immediate: Sbc, Immediate, SbcImmediate, 0xe9, 2,
    sbc_x_indexed_indirect: Sbc, XIndexedIndirect, SbcXIndexedIndirect, 0xe1, 6,
    sbc_zeropage: Sbc, ZeroPage, SbcZeroPage, 0xe5, 3,
    sbc_zeropage_indexed_with_x: Sbc, ZeroPageIndexedWithX, SbcZeroPageIndexedWithX, 0xf5, 4,
    and_absolute: And, Absolute, AndAbsolute, 0x2d, 4,
    and_absolute_indexed_with_x: And, AbsoluteIndexedWithX, AndAbsoluteIndexedWithX, 0x3d, 4,
    and_absolute_indexed_with_y: And, AbsoluteIndexedWithY, AndAbsoluteIndexedWithY, 0x39, 4,
    and_indirect_y_indexed: And, IndirectYIndexed, AndIndirectYIndexed, 0x31, 5,
    and_immediate: And, Immediate, AndImmediate, 0x29, 2,
    and_x_indexed_indirect: And, XIndexedIndirect, AndXIndexedIndirect, 0x21, 6,
    and_zeropage: And, ZeroPage, AndZeroPage, 0x25, 3,
    and_zeropage_indxed_with_x: And, ZeroPageIndexedWithX, AndZeroPageIndexedWithX, 0x35, 4,
    asl_absolute: Asl, Absolute, AslAbsolute, 0x0e, 6,
    asl_absolute_indexed_with_x: Asl, AbsoluteIndexedWithX, AslAbsoluteIndexedWithX, 0x1e, 7,
    asl_accumulator: Asl, Accumulator, AslAccumulator, 0x0a, 2,
    asl_zeropage: Asl, ZeroPage, AslZeroPage, 0x06, 5,
    asl_zeropage_indexed_with_x: Asl, ZeroPageIndexedWithX, AslZeroPageIndexedWithX, 0x16, 6,
    bit_absolute: Bit, Absolute, BitAbsolute, 0x2c, 4,
    bit_zeropage: Bit, ZeroPage, BitZeroPage, 0x24, 3,
    eor_absolute: Eor, Absolute, EorAbsolute, 0x4d, 4,
    eor_absolute_indexed_with_x: Eor, AbsoluteIndexedWithX, EorAbsoluteIndexedWithX, 0x5d, 4,
    eor_absolute_indexed_with_y: Eor, AbsoluteIndexedWithY, EorAbsoluteIndexedWithY, 0x59, 4,
    eor_indirect_y_indexed: Eor, IndirectYIndexed, EorIndirectYIndexed, 0x51, 5,
    eor_immediate: Eor, Immediate, EorImmediate, 0x49, 2,
    eor_x_indexed_indirect: Eor, XIndexedIndirect, EorXIndexedIndirect, 0x41, 6,
    eor_zeropage: Eor, ZeroPage, EorZeroPage, 0x45, 3,
    eor_zeropage_indexed_with_x: Eor, ZeroPageIndexedWithX, EorZeroPageIndexedWithX, 0x55, 4,
    lsr_absolute: Lsr, Absolute, LsrAbsolute, 0x4e, 6,
    lsr_absolute_indexed_with_x: Lsr, AbsoluteIndexedWithX, LsrAbsoluteIndexedWithX, 0x5e, 7,
    lsr_accumulator: Lsr, Accumulator, LsrAccumulator, 0x4a, 2,
    lsr_zeropage: Lsr, ZeroPage, LsrZeroPage, 0x46, 5,
    lsr_zeropage_indexed_with_x: Lsr, ZeroPageIndexedWithX, LsrZeroPageIndexedWithX, 0x56, 6,
    ora_absolute: Ora, Absolute, OraAbsolute, 0x0d, 4,
    ora_absolute_indexed_with_x: Ora, AbsoluteIndexedWithX, OraAbsoluteIndexedWithX, 0x1d, 4,
    ora_absolute_indexed_with_y: Ora, AbsoluteIndexedWithY, OraAbsoluteIndexedWithY, 0x19, 4,
    ora_indirect_y_indexed: Ora, IndirectYIndexed, OraIndirectYIndexed, 0x11, 5,
    ora_immediate: Ora, Immediate, OraImmediate, 0x09, 2,
    ora_x_indexed_indirect: Ora, XIndexedIndirect, OraXIndexedIndirect, 0x01, 6,
    ora_zeroapage: Ora, ZeroPage, OraZeroPage, 0x05, 3,
    ora_zeropage_indexed_with_x: Ora, ZeroPageIndexedWithX, OraZeroPageIndexedWithX, 0x15, 4,
    rol_absolute: Rol, Absolute, RolAbsolute, 0x2e, 6,
    rol_absolute_indexed_with_x: Rol, AbsoluteIndexedWithX, RolAbsoluteIndexedWithX, 0x3e, 7,
    rol_accumulator: Rol, Accumulator, RolAccumulator, 0x2a, 2,
    rol_zeropage: Rol, ZeroPage, RolZeroPage, 0x26, 5,
    rol_zeropage_indexed_with_x: Rol, ZeroPageIndexedWithX, RolZeroPageIndexedWithX, 0x36, 6,
    ror_absolute: Ror, Absolute, RorAbsolute, 0x6e, 6,
    ror_absolute_indexed_with_x: Ror, AbsoluteIndexedWithX, RorAbsoluteIndexedWithX, 0x7e, 7,
    ror_acumulator: Ror, Accumulator, RorAccumulator, 0x6a, 2,
    ror_zeropage: Ror, ZeroPage, RorZeroPage, 0x66, 5,
    ror_zeropage_indexed_with_x: Ror, ZeroPageIndexedWithX, RorZeroPageIndexedWithX, 0x76, 6,
    bcc_relative: Bcc, Relative, BccRelative, 0x90, 2,
    bcs_relative: Bcs, Relative, BcsRelative, 0xb0, 2,
    beq_relative: Beq, Relative, BeqRelative, 0xf0, 2,
    bmi_relative: Bmi, Relative, BmiRelative, 0x30, 2,
    bne_relative: Bne, Relative, BneRelative, 0xd0, 2,
    bpl_relative: Bpl, Relative, BplRelative, 0x10, 2,
    bvc_relative: Bvc, Relative, BvcRelative, 0x50, 2,
    bvs_relative: Bvs, Relative, BvsRelative, 0x70, 2,
    clc_implied: Clc, Implied, ClcImplied, 0x18, 2,
    cld_implied: Cld, Implied, CldImplied, 0xd8, 2,
    cli_implied: Cli, Implied, CliImplied, 0x58, 2,
    clv_implied: Clv, Implied, ClvImplied, 0xb8, 2,
    cmp_absolute: Cmp, Absolute, CmpAbsolute, 0xcd, 4,
    cmp_absolute_indexed_with_x: Cmp, AbsoluteIndexedWithX, CmpAbsoluteIndexedWithX, 0xdd, 4,
    cmp_absolute_indexed_with_y: Cmp, AbsoluteIndexedWithY, CmpAbsoluteIndexedWithY, 0xd9, 4,
    cmp_indirect_y_indexed: Cmp, IndirectYIndexed, CmpIndirectYIndexed, 0xd1, 5,
    cmp_immediate: Cmp, Immediate, CmpImmediate, 0xc9, 2,
    cmp_x_indexed_indirect: Cmp, XIndexedIndirect, CmpXIndexedIndirect, 0xc1, 6,
    cmp_zeropage: Cmp, ZeroPage, CmpZeroPage, 0xc5, 3,
    cmp_zeropage_indexexd_with_x: Cmp, ZeroPageIndexedWithX, CmpZeroPageIndexedWithX, 0xd5, 4,
    cpx_absolute: Cpx, Absolute, CpxAbsolute, 0xec, 4,
    cpx_immediate: Cpx, Immediate, CpxImmediate, 0xe0, 2,
    cpx_zeroage: Cpx, ZeroPage, CpxZeroPage, 0xe4, 3,
    cpy_absolute: Cpy, Absolute, CpyAbsolute, 0xcc, 4,
    cpy_immediate: Cpy, Immediate, CpyImmediate, 0xc0, 2,
    cpy_zeropage: Cpy, ZeroPage, CpyZeroPage, 0xc4, 3,
    dec_absolute: Dec, Absolute, DecAbsolute, 0xce, 6,
    dec_absolute_indexed_with_x: Dec, AbsoluteIndexedWithX, DecAbsoluteIndexedWithX, 0xde, 7,
    dec_zeropage: Dec, ZeroPage, DecZeroPage, 0xc6, 5,
    dec_zeropage_indexed_with_x: Dec, ZeroPageIndexedWithX, DecZeroPageIndexedWithX, 0xd6, 6,
    dex_implied: Dex, Implied, DexImplied, 0xca, 2,
    dey_implied: Dey, Implied, DeyImplied, 0x88, 2,
    inc_absolute: Inc, Absolute, IncAbsolute, 0xee, 6,
    inc_absolute_indexed_with_x: Inc, AbsoluteIndexedWithX, IncAbsoluteIndexedWithX, 0xfe, 7,
    inc_zeropage: Inc, ZeroPage, IncZeroPage, 0xe6, 5,
    inc_zeropage_indexed_with_x: Inc, ZeroPageIndexedWithX, IncZeroPageIndexedWithX, 0xf6, 6,
    inx_implied: Inx, Implied, InxImplied, 0xe8, 2,
    iny_implied: Iny, Implied, InyImplied, 0xc8, 2,
    jmp_absolute: Jmp, Absolute, JmpAbsolute, 0x4c, 3,
    jmp_indirect: Jmp, Indirect, JmpIndirect, 0x6c, 5,
    jsr_absolute: Jsr, Absolute, JsrAbsolute, 0x20, 6,
    lda_immediate: Lda, Immediate, LdaImmediate, 0xa9, 2,
    lda_zeropage: Lda, ZeroPage, LdaZeroPage, 0xa5, 3,
    lda_zeropage_indexed_with_x: Lda, ZeroPageIndexedWithX, LdaZeroPageIndexedWithX, 0xb5, 4,
    lda_absolute: Lda, Absolute, LdaAbsolute, 0xad, 4,
    lda_absolute_indexed_with_x: Lda, AbsoluteIndexedWithX, LdaAbsoluteIndexedWithX, 0xbd, 4,
    lda_absolute_indexed_with_y: Lda, AbsoluteIndexedWithY, LdaAbsoluteIndexedWithY, 0xb9, 4,
    lda_indirect_y_indexed: Lda, IndirectYIndexed, LdaIndirectYIndexed, 0xb1, 5,
    lda_x_indexed_indirect: Lda, XIndexedIndirect, LdaXIndexedIndirect, 0xa1, 6,
    ldx_absolute: Ldx, Absolute, LdxAbsolute, 0xae, 4,
    ldx_absolute_indexed_with_y: Ldx, AbsoluteIndexedWithY, LdxAbsoluteIndexedWithY, 0xbe, 4,
    ldx_immediate: Ldx, Immediate, LdxImmediate, 0xa2, 2,
    ldx_zeropage: Ldx, ZeroPage, LdxZeroPage, 0xa6, 3,
    ldx_zeropage_indexed_with_y: Ldx, ZeroPageIndexedWithY, LdxZeroPageIndexedWithY, 0xb6, 4,
    ldy_absolute: Ldy, Absolute, LdyAbsolute, 0xac, 4,
    ldy_absolute_indexed_with_x: Ldy, AbsoluteIndexedWithX, LdyAbsoluteIndexedWithX, 0xbc, 4,
    ldy_immediate: Ldy, Immediate, LdyImmediate, 0xa0, 2,
    ldy_zeropage: Ldy, ZeroPage, LdyZeroPage, 0xa4, 3,
    ldy_zeropage_indexed_with_x: Ldy, ZeroPageIndexedWithX, LdyZeroPageIndexedWithX, 0xb4, 4,
    pha_implied: Pha, Implied, PhaImplied, 0x48, 3,
    php_implied: Php, Implied, PhpImplied, 0x08, 3,
    pla_implied: Pla, Implied, PlaImplied, 0x68, 4,
    plp_implied: Plp, Implied, PlpImplied, 0x28, 4,
    rti_implied: Rti, Implied, RtiImplied, 0x40, 6,
    rts_implied: Rts, Implied, RtsImplied, 0x60, 6,
    sec_implied: Sec, Implied, SecImplied, 0x38, 2,
    sed_implied: Sed, Implied, SedImplied, 0xf8, 2,
    sei_implied: Sei, Implied, SeiImplied, 0x78, 2,
    sta_absolute: Sta, Absolute, StaAbsolute, 0x8d, 4,
    sta_absolute_indexed_with_x: Sta, AbsoluteIndexedWithX, StaAbsoluteIndexedWithX, 0x9d, 5,
    sta_absolute_indexed_with_y: Sta, AbsoluteIndexedWithY, StaAbsoluteIndexedWithY, 0x99, 5,
    sta_indirect_y_indexed: Sta, IndirectYIndexed, StaIndirectYIndexed, 0x91, 6,
    sta_x_indexed_indirect: Sta, XIndexedIndirect, StaXIndexedIndirect, 0x81, 6,
    sta_zeropage: Sta, ZeroPage, StaZeroPage, 0x85, 3,
    sta_zeropage_indexed_with_x: Sta, ZeroPageIndexedWithX, StaZeroPageIndexedWithX, 0x95, 4,
    stx_absolute: Stx, Absolute, StxAbsolute, 0x8e, 4,
    stx_zeropage: Stx, ZeroPage, StxZeroPage, 0x86, 3,
    stx_zeropage_indexed_with_y: Stx, ZeroPageIndexedWithY, StxZeroPageIndexedWithY, 0x96, 4,
    sty_absolute: Sty, Absolute, StyAbsolute, 0x8c, 4,
    sty_zeropage: Sty, ZeroPage, StyZeroPage, 0x84, 3,
    sty_zeropage_indexed_with_x: Sty, ZeroPageIndexedWithX, StyZeroPageIndexedWithX, 0x94, 4,
    tax_implied: Tax, Implied, TaxImplied, 0xaa, 2,
    tay_implied: Tay, Implied, TayImplied, 0xa8, 2,
    tsx_implied: Tsx, Implied, TsxImplied, 0xba, 2,
    txa_implied: Txa, Implied, TxaImplied, 0x8a, 2,
    txs_implied: Txs, Implied, TxsImplied, 0x9a, 2,
    tya_implied: Tya, Implied, TyaImplied, 0x98, 2,
    brk_implied: Brk, Implied, BrkImplied, 0x00, 7,
    nop_implied: Nop, Implied, NopImplied, 0xea, 2,
);

/// InstructionVariant functions as a concrete implementations of the generic
/// instruction types for use when runtime.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InstructionVariant {
    AdcAbsolute(u16),
    AdcAbsoluteIndexedWithX(u16),
    AdcAbsoluteIndexedWithY(u16),
    AdcIndirectYIndexed(u8),
    AdcImmediate(u8),
    AdcXIndexedIndirect(u8),
    AdcZeroPage(u8),
    AdcZeroPageIndexedWithX(u8),
    AndAbsolute(u16),
    AndAbsoluteIndexedWithX(u16),
    AndAbsoluteIndexedWithY(u16),
    AndIndirectYIndexed(u8),
    AndImmediate(u8),
    AndXIndexedIndirect(u8),
    AndZeroPage(u8),
    AndZeroPageIndexedWithX(u8),
    AslAbsolute(u16),
    AslAbsoluteIndexedWithX(u16),
    AslAccumulator,
    AslZeroPage(u8),
    AslZeroPageIndexedWithX(u8),
    BccRelative(i8),
    BcsRelative(i8),
    BeqRelative(i8),
    BmiRelative(i8),
    BitAbsolute(u16),
    BitZeroPage(u8),
    BneRelative(i8),
    BplRelative(i8),
    BrkImplied,
    BvcRelative(i8),
    BvsRelative(i8),
    ClcImplied,
    CldImplied,
    CliImplied,
    ClvImplied,
    CmpAbsolute(u16),
    CmpAbsoluteIndexedWithX(u16),
    CmpAbsoluteIndexedWithY(u16),
    CmpIndirectYIndexed(u8),
    CmpImmediate(u8),
    CmpXIndexedIndirect(u8),
    CmpZeroPage(u8),
    CmpZeroPageIndexedWithX(u8),
    CpxAbsolute(u16),
    CpxImmediate(u8),
    CpxZeroPage(u8),
    CpyAbsolute(u16),
    CpyImmediate(u8),
    CpyZeroPage(u8),
    DecAbsolute(u16),
    DecAbsoluteIndexedWithX(u16),
    DecZeroPage(u8),
    DecZeroPageIndexedWithX(u8),
    DexImplied,
    DeyImplied,
    EorAbsolute(u16),
    EorAbsoluteIndexedWithX(u16),
    EorAbsoluteIndexedWithY(u16),
    EorIndirectYIndexed(u8),
    EorImmediate(u8),
    EorXIndexedIndirect(u8),
    EorZeroPage(u8),
    EorZeroPageIndexedWithX(u8),
    IncAbsolute(u16),
    IncAbsoluteIndexedWithX(u16),
    IncZeroPage(u8),
    IncZeroPageIndexedWithX(u8),
    InxImplied,
    InyImplied,
    JmpAbsolute(u16),
    JmpIndirect(u16),
    JsrAbsolute(u16),
    LdaAbsolute(u16),
    LdaAbsoluteIndexedWithX(u16),
    LdaAbsoluteIndexedWithY(u16),
    LdaIndirectYIndexed(u8),
    LdaImmediate(u8),
    LdaXIndexedIndirect(u8),
    LdaZeroPage(u8),
    LdaZeroPageIndexedWithX(u8),
    LdxAbsolute(u16),
    LdxAbsoluteIndexedWithY(u16),
    LdxImmediate(u8),
    LdxZeroPage(u8),
    LdxZeroPageIndexedWithY(u8),
    LdyAbsolute(u16),
    LdyAbsoluteIndexedWithX(u16),
    LdyImmediate(u8),
    LdyZeroPage(u8),
    LdyZeroPageIndexedWithX(u8),
    LsrAbsolute(u16),
    LsrAbsoluteIndexedWithX(u16),
    LsrAccumulator,
    LsrZeroPage(u8),
    LsrZeroPageIndexedWithX(u8),
    NopImplied,
    OraAbsolute(u16),
    OraAbsoluteIndexedWithX(u16),
    OraAbsoluteIndexedWithY(u16),
    OraIndirectYIndexed(u8),
    OraImmediate(u8),
    OraXIndexedIndirect(u8),
    OraZeroPage(u8),
    OraZeroPageIndexedWithX(u8),
    PhaImplied,
    PhpImplied,
    PlaImplied,
    PlpImplied,
    RolAbsolute(u16),
    RolAbsoluteIndexedWithX(u16),
    RolAccumulator,
    RolZeroPage(u8),
    RolZeroPageIndexedWithX(u8),
    RorAbsolute(u16),
    RorAbsoluteIndexedWithX(u16),
    RorAccumulator,
    RorZeroPage(u8),
    RorZeroPageIndexedWithX(u8),
    RtiImplied,
    RtsImplied,
    SbcAbsolute(u16),
    SbcAbsoluteIndexedWithX(u16),
    SbcAbsoluteIndexedWithY(u16),
    SbcIndirectYIndexed(u8),
    SbcImmediate(u8),
    SbcXIndexedIndirect(u8),
    SbcZeroPage(u8),
    SbcZeroPageIndexedWithX(u8),
    StaAbsolute(u16),
    StaAbsoluteIndexedWithX(u16),
    StaAbsoluteIndexedWithY(u16),
    StaIndirectYIndexed(u8),
    StaXIndexedIndirect(u8),
    StaZeroPage(u8),
    StaZeroPageIndexedWithX(u8),
    StxAbsolute(u16),
    StxZeroPage(u8),
    StxZeroPageIndexedWithY(u8),
    StyAbsolute(u16),
    StyZeroPage(u8),
    StyZeroPageIndexedWithX(u8),
    SecImplied,
    SedImplied,
    SeiImplied,
    TaxImplied,
    TayImplied,
    TsxImplied,
    TxaImplied,
    TxsImplied,
    TyaImplied,
}

impl InstructionVariant {
    /// new functions as a wrapper around TryFrom<(Mnemonic, AddressingMode)
    /// and returning a Result. This functions identically other than requiring
    /// that the TryFrom trait be imported to call this.
    pub fn new(
        m: mnemonic::Mnemonic,
        am: addressing_mode::AddressingMode,
    ) -> Result<Self, InstructionErr> {
        use std::convert::TryFrom;
        <InstructionVariant>::try_from((m, am))
    }
}

/// Implements bytecode converstion for InstructionVariant by explicitly converting to the generic type.
impl std::convert::From<InstructionVariant> for Bytecode {
    fn from(src: InstructionVariant) -> Bytecode {
        match src {
            InstructionVariant::AdcAbsolute(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::Absolute(am)).into()
            }

            InstructionVariant::AdcAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::AdcAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::AdcIndirectYIndexed(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::AdcImmediate(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::AdcXIndexedIndirect(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::AdcZeroPage(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::AdcZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Adc, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::AndAbsolute(am) => {
                Instruction::new(mnemonic::And, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::AndAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::And, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::AndAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::And, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::AndIndirectYIndexed(am) => {
                Instruction::new(mnemonic::And, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::AndImmediate(am) => {
                Instruction::new(mnemonic::And, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::AndXIndexedIndirect(am) => {
                Instruction::new(mnemonic::And, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::AndZeroPage(am) => {
                Instruction::new(mnemonic::And, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::AndZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::And, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::AslAbsolute(am) => {
                Instruction::new(mnemonic::Asl, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::AslAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Asl, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::AslAccumulator => {
                Instruction::new(mnemonic::Asl, addressing_mode::Accumulator).into()
            }
            InstructionVariant::AslZeroPage(am) => {
                Instruction::new(mnemonic::Asl, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::AslZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Asl, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::BccRelative(am) => {
                Instruction::new(mnemonic::Bcc, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BcsRelative(am) => {
                Instruction::new(mnemonic::Bcs, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BeqRelative(am) => {
                Instruction::new(mnemonic::Beq, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BmiRelative(am) => {
                Instruction::new(mnemonic::Bmi, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BitAbsolute(am) => {
                Instruction::new(mnemonic::Bit, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::BitZeroPage(am) => {
                Instruction::new(mnemonic::Bit, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::BneRelative(am) => {
                Instruction::new(mnemonic::Bne, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BplRelative(am) => {
                Instruction::new(mnemonic::Bpl, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BrkImplied => {
                Instruction::new(mnemonic::Brk, addressing_mode::Implied).into()
            }
            InstructionVariant::BvcRelative(am) => {
                Instruction::new(mnemonic::Bvc, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BvsRelative(am) => {
                Instruction::new(mnemonic::Bvs, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::ClcImplied => {
                Instruction::new(mnemonic::Clc, addressing_mode::Implied).into()
            }
            InstructionVariant::CldImplied => {
                Instruction::new(mnemonic::Cld, addressing_mode::Implied).into()
            }
            InstructionVariant::CliImplied => {
                Instruction::new(mnemonic::Cli, addressing_mode::Implied).into()
            }
            InstructionVariant::ClvImplied => {
                Instruction::new(mnemonic::Clv, addressing_mode::Implied).into()
            }
            InstructionVariant::CmpAbsolute(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::CmpAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::CmpAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::CmpIndirectYIndexed(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::CmpImmediate(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::CmpXIndexedIndirect(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::CmpZeroPage(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::CmpZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Cmp, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::CpxAbsolute(am) => {
                Instruction::new(mnemonic::Cpx, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::CpxImmediate(am) => {
                Instruction::new(mnemonic::Cpx, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::CpxZeroPage(am) => {
                Instruction::new(mnemonic::Cpx, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::CpyAbsolute(am) => {
                Instruction::new(mnemonic::Cpy, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::CpyImmediate(am) => {
                Instruction::new(mnemonic::Cpy, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::CpyZeroPage(am) => {
                Instruction::new(mnemonic::Cpy, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::DecAbsolute(am) => {
                Instruction::new(mnemonic::Dec, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::DecAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Dec, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::DecZeroPage(am) => {
                Instruction::new(mnemonic::Dec, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::DecZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Dec, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::DexImplied => {
                Instruction::new(mnemonic::Dex, addressing_mode::Implied).into()
            }
            InstructionVariant::DeyImplied => {
                Instruction::new(mnemonic::Dey, addressing_mode::Implied).into()
            }
            InstructionVariant::EorAbsolute(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::EorAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::EorAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::EorIndirectYIndexed(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::EorImmediate(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::EorXIndexedIndirect(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::EorZeroPage(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::EorZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Eor, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::IncAbsolute(am) => {
                Instruction::new(mnemonic::Inc, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::IncAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Inc, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::IncZeroPage(am) => {
                Instruction::new(mnemonic::Inc, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::IncZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Inc, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::InxImplied => {
                Instruction::new(mnemonic::Inx, addressing_mode::Implied).into()
            }
            InstructionVariant::InyImplied => {
                Instruction::new(mnemonic::Iny, addressing_mode::Implied).into()
            }
            InstructionVariant::JmpAbsolute(am) => {
                Instruction::new(mnemonic::Jmp, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::JmpIndirect(am) => {
                Instruction::new(mnemonic::Jmp, addressing_mode::Indirect(am)).into()
            }
            InstructionVariant::JsrAbsolute(am) => {
                Instruction::new(mnemonic::Jsr, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LdaAbsolute(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LdaAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::LdaAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::LdaIndirectYIndexed(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::LdaImmediate(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::LdaXIndexedIndirect(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::LdaZeroPage(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LdaZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Lda, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::LdxAbsolute(am) => {
                Instruction::new(mnemonic::Ldx, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LdxAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Ldx, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::LdxImmediate(am) => {
                Instruction::new(mnemonic::Ldx, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::LdxZeroPage(am) => {
                Instruction::new(mnemonic::Ldx, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LdxZeroPageIndexedWithY(am) => {
                Instruction::new(mnemonic::Ldx, addressing_mode::ZeroPageIndexedWithY(am)).into()
            }
            InstructionVariant::LdyAbsolute(am) => {
                Instruction::new(mnemonic::Ldy, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LdyAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Ldy, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::LdyImmediate(am) => {
                Instruction::new(mnemonic::Ldy, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::LdyZeroPage(am) => {
                Instruction::new(mnemonic::Ldy, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LdyZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Ldy, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::LsrAbsolute(am) => {
                Instruction::new(mnemonic::Lsr, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LsrAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Lsr, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::LsrAccumulator => {
                Instruction::new(mnemonic::Lsr, addressing_mode::Accumulator).into()
            }
            InstructionVariant::LsrZeroPage(am) => {
                Instruction::new(mnemonic::Lsr, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LsrZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Lsr, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::NopImplied => {
                Instruction::new(mnemonic::Nop, addressing_mode::Implied).into()
            }
            InstructionVariant::OraAbsolute(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::OraAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::OraAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::OraIndirectYIndexed(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::OraImmediate(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::OraXIndexedIndirect(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::OraZeroPage(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::OraZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Ora, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::PhaImplied => {
                Instruction::new(mnemonic::Pha, addressing_mode::Implied).into()
            }
            InstructionVariant::PhpImplied => {
                Instruction::new(mnemonic::Php, addressing_mode::Implied).into()
            }
            InstructionVariant::PlaImplied => {
                Instruction::new(mnemonic::Pla, addressing_mode::Implied).into()
            }
            InstructionVariant::PlpImplied => {
                Instruction::new(mnemonic::Plp, addressing_mode::Implied).into()
            }
            InstructionVariant::RolAbsolute(am) => {
                Instruction::new(mnemonic::Rol, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::RolAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Rol, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::RolAccumulator => {
                Instruction::new(mnemonic::Rol, addressing_mode::Accumulator).into()
            }
            InstructionVariant::RolZeroPage(am) => {
                Instruction::new(mnemonic::Rol, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::RolZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Rol, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::RorAbsolute(am) => {
                Instruction::new(mnemonic::Ror, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::RorAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Ror, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::RorAccumulator => {
                Instruction::new(mnemonic::Ror, addressing_mode::Accumulator).into()
            }
            InstructionVariant::RorZeroPage(am) => {
                Instruction::new(mnemonic::Ror, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::RorZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Ror, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::RtiImplied => {
                Instruction::new(mnemonic::Rti, addressing_mode::Implied).into()
            }
            InstructionVariant::RtsImplied => {
                Instruction::new(mnemonic::Rts, addressing_mode::Implied).into()
            }
            InstructionVariant::SbcAbsolute(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::SbcAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::SbcAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::SbcIndirectYIndexed(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::SbcImmediate(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::SbcXIndexedIndirect(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::SbcZeroPage(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::SbcZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Sbc, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::StaAbsolute(am) => {
                Instruction::new(mnemonic::Sta, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::StaAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::Sta, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::StaAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::Sta, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::StaIndirectYIndexed(am) => {
                Instruction::new(mnemonic::Sta, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::StaXIndexedIndirect(am) => {
                Instruction::new(mnemonic::Sta, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::StaZeroPage(am) => {
                Instruction::new(mnemonic::Sta, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::StaZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Sta, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::StxAbsolute(am) => {
                Instruction::new(mnemonic::Stx, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::StxZeroPage(am) => {
                Instruction::new(mnemonic::Stx, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::StxZeroPageIndexedWithY(am) => {
                Instruction::new(mnemonic::Stx, addressing_mode::ZeroPageIndexedWithY(am)).into()
            }
            InstructionVariant::StyAbsolute(am) => {
                Instruction::new(mnemonic::Sty, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::StyZeroPage(am) => {
                Instruction::new(mnemonic::Sty, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::StyZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::Sty, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::SecImplied => {
                Instruction::new(mnemonic::Sec, addressing_mode::Implied).into()
            }
            InstructionVariant::SedImplied => {
                Instruction::new(mnemonic::Sed, addressing_mode::Implied).into()
            }
            InstructionVariant::SeiImplied => {
                Instruction::new(mnemonic::Sei, addressing_mode::Implied).into()
            }
            InstructionVariant::TaxImplied => {
                Instruction::new(mnemonic::Tax, addressing_mode::Implied).into()
            }
            InstructionVariant::TayImplied => {
                Instruction::new(mnemonic::Tay, addressing_mode::Implied).into()
            }
            InstructionVariant::TsxImplied => {
                Instruction::new(mnemonic::Tsx, addressing_mode::Implied).into()
            }
            InstructionVariant::TxaImplied => {
                Instruction::new(mnemonic::Txa, addressing_mode::Implied).into()
            }
            InstructionVariant::TxsImplied => {
                Instruction::new(mnemonic::Txs, addressing_mode::Implied).into()
            }
            InstructionVariant::TyaImplied => {
                Instruction::new(mnemonic::Tya, addressing_mode::Implied).into()
            }
        }
    }
}

/// This outputs a tuple type of the mnemonic and addressing mode enums,
/// making it simpler to work with each component.
impl std::convert::From<InstructionVariant>
    for (mnemonic::Mnemonic, addressing_mode::AddressingMode)
{
    fn from(src: InstructionVariant) -> Self {
        match src {
            InstructionVariant::AdcAbsolute(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::Absolute(am),
            ),

            InstructionVariant::AdcAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::AdcAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::AdcIndirectYIndexed(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::AdcImmediate(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::AdcXIndexedIndirect(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::AdcZeroPage(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::AdcZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Adc,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::AndAbsolute(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::AndAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::AndAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::AndIndirectYIndexed(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::AndImmediate(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::AndXIndexedIndirect(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::AndZeroPage(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::AndZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::And,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::AslAbsolute(am) => (
                mnemonic::Mnemonic::Asl,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::AslAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Asl,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::AslAccumulator => (
                mnemonic::Mnemonic::Asl,
                addressing_mode::AddressingMode::Accumulator,
            ),
            InstructionVariant::AslZeroPage(am) => (
                mnemonic::Mnemonic::Asl,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::AslZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Asl,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::BccRelative(am) => (
                mnemonic::Mnemonic::Bcc,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::BcsRelative(am) => (
                mnemonic::Mnemonic::Bcs,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::BeqRelative(am) => (
                mnemonic::Mnemonic::Beq,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::BmiRelative(am) => (
                mnemonic::Mnemonic::Bmi,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::BitAbsolute(am) => (
                mnemonic::Mnemonic::Bit,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::BitZeroPage(am) => (
                mnemonic::Mnemonic::Bit,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::BneRelative(am) => (
                mnemonic::Mnemonic::Bne,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::BplRelative(am) => (
                mnemonic::Mnemonic::Bpl,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::BrkImplied => (
                mnemonic::Mnemonic::Brk,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::BvcRelative(am) => (
                mnemonic::Mnemonic::Bvc,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::BvsRelative(am) => (
                mnemonic::Mnemonic::Bvs,
                addressing_mode::AddressingMode::Relative(am),
            ),
            InstructionVariant::ClcImplied => (
                mnemonic::Mnemonic::Clc,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::CldImplied => (
                mnemonic::Mnemonic::Cld,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::CliImplied => (
                mnemonic::Mnemonic::Cli,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::ClvImplied => (
                mnemonic::Mnemonic::Clv,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::CmpAbsolute(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::CmpAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::CmpAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::CmpIndirectYIndexed(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::CmpImmediate(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::CmpXIndexedIndirect(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::CmpZeroPage(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::CmpZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Cmp,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::CpxAbsolute(am) => (
                mnemonic::Mnemonic::Cpx,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::CpxImmediate(am) => (
                mnemonic::Mnemonic::Cpx,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::CpxZeroPage(am) => (
                mnemonic::Mnemonic::Cpx,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::CpyAbsolute(am) => (
                mnemonic::Mnemonic::Cpy,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::CpyImmediate(am) => (
                mnemonic::Mnemonic::Cpy,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::CpyZeroPage(am) => (
                mnemonic::Mnemonic::Cpy,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::DecAbsolute(am) => (
                mnemonic::Mnemonic::Dec,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::DecAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Dec,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::DecZeroPage(am) => (
                mnemonic::Mnemonic::Dec,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::DecZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Dec,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::DexImplied => (
                mnemonic::Mnemonic::Dex,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::DeyImplied => (
                mnemonic::Mnemonic::Dey,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::EorAbsolute(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::EorAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::EorAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::EorIndirectYIndexed(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::EorImmediate(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::EorXIndexedIndirect(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::EorZeroPage(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::EorZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Eor,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::IncAbsolute(am) => (
                mnemonic::Mnemonic::Inc,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::IncAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Inc,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::IncZeroPage(am) => (
                mnemonic::Mnemonic::Inc,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::IncZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Inc,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::InxImplied => (
                mnemonic::Mnemonic::Inx,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::InyImplied => (
                mnemonic::Mnemonic::Iny,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::JmpAbsolute(am) => (
                mnemonic::Mnemonic::Jmp,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::JmpIndirect(am) => (
                mnemonic::Mnemonic::Jmp,
                addressing_mode::AddressingMode::Indirect(am),
            ),
            InstructionVariant::JsrAbsolute(am) => (
                mnemonic::Mnemonic::Jsr,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::LdaAbsolute(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::LdaAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::LdaAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::LdaIndirectYIndexed(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::LdaImmediate(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::LdaXIndexedIndirect(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::LdaZeroPage(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::LdaZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Lda,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::LdxAbsolute(am) => (
                mnemonic::Mnemonic::Ldx,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::LdxAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Ldx,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::LdxImmediate(am) => (
                mnemonic::Mnemonic::Ldx,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::LdxZeroPage(am) => (
                mnemonic::Mnemonic::Ldx,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::LdxZeroPageIndexedWithY(am) => (
                mnemonic::Mnemonic::Ldx,
                addressing_mode::AddressingMode::ZeroPageIndexedWithY(am),
            ),
            InstructionVariant::LdyAbsolute(am) => (
                mnemonic::Mnemonic::Ldy,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::LdyAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Ldy,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::LdyImmediate(am) => (
                mnemonic::Mnemonic::Ldy,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::LdyZeroPage(am) => (
                mnemonic::Mnemonic::Ldy,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::LdyZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Ldy,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::LsrAbsolute(am) => (
                mnemonic::Mnemonic::Lsr,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::LsrAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Lsr,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::LsrAccumulator => (
                mnemonic::Mnemonic::Lsr,
                addressing_mode::AddressingMode::Accumulator,
            ),
            InstructionVariant::LsrZeroPage(am) => (
                mnemonic::Mnemonic::Lsr,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::LsrZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Lsr,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::NopImplied => (
                mnemonic::Mnemonic::Nop,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::OraAbsolute(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::OraAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::OraAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::OraIndirectYIndexed(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::OraImmediate(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::OraXIndexedIndirect(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::OraZeroPage(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::OraZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Ora,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::PhaImplied => (
                mnemonic::Mnemonic::Pha,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::PhpImplied => (
                mnemonic::Mnemonic::Php,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::PlaImplied => (
                mnemonic::Mnemonic::Pla,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::PlpImplied => (
                mnemonic::Mnemonic::Plp,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::RolAbsolute(am) => (
                mnemonic::Mnemonic::Rol,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::RolAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Rol,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::RolAccumulator => (
                mnemonic::Mnemonic::Rol,
                addressing_mode::AddressingMode::Accumulator,
            ),
            InstructionVariant::RolZeroPage(am) => (
                mnemonic::Mnemonic::Rol,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::RolZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Rol,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::RorAbsolute(am) => (
                mnemonic::Mnemonic::Ror,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::RorAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Ror,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::RorAccumulator => (
                mnemonic::Mnemonic::Ror,
                addressing_mode::AddressingMode::Accumulator,
            ),
            InstructionVariant::RorZeroPage(am) => (
                mnemonic::Mnemonic::Ror,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::RorZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Ror,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::RtiImplied => (
                mnemonic::Mnemonic::Rti,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::RtsImplied => (
                mnemonic::Mnemonic::Rts,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::SbcAbsolute(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::SbcAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::SbcAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::SbcIndirectYIndexed(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::SbcImmediate(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::Immediate(am),
            ),
            InstructionVariant::SbcXIndexedIndirect(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::SbcZeroPage(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::SbcZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Sbc,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::StaAbsolute(am) => (
                mnemonic::Mnemonic::Sta,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::StaAbsoluteIndexedWithX(am) => (
                mnemonic::Mnemonic::Sta,
                addressing_mode::AddressingMode::AbsoluteIndexedWithX(am),
            ),
            InstructionVariant::StaAbsoluteIndexedWithY(am) => (
                mnemonic::Mnemonic::Sta,
                addressing_mode::AddressingMode::AbsoluteIndexedWithY(am),
            ),
            InstructionVariant::StaIndirectYIndexed(am) => (
                mnemonic::Mnemonic::Sta,
                addressing_mode::AddressingMode::IndirectYIndexed(am),
            ),
            InstructionVariant::StaXIndexedIndirect(am) => (
                mnemonic::Mnemonic::Sta,
                addressing_mode::AddressingMode::XIndexedIndirect(am),
            ),
            InstructionVariant::StaZeroPage(am) => (
                mnemonic::Mnemonic::Sta,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::StaZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Sta,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::StxAbsolute(am) => (
                mnemonic::Mnemonic::Stx,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::StxZeroPage(am) => (
                mnemonic::Mnemonic::Stx,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::StxZeroPageIndexedWithY(am) => (
                mnemonic::Mnemonic::Stx,
                addressing_mode::AddressingMode::ZeroPageIndexedWithY(am),
            ),
            InstructionVariant::StyAbsolute(am) => (
                mnemonic::Mnemonic::Sty,
                addressing_mode::AddressingMode::Absolute(am),
            ),
            InstructionVariant::StyZeroPage(am) => (
                mnemonic::Mnemonic::Sty,
                addressing_mode::AddressingMode::ZeroPage(am),
            ),
            InstructionVariant::StyZeroPageIndexedWithX(am) => (
                mnemonic::Mnemonic::Sty,
                addressing_mode::AddressingMode::ZeroPageIndexedWithX(am),
            ),
            InstructionVariant::SecImplied => (
                mnemonic::Mnemonic::Sec,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::SedImplied => (
                mnemonic::Mnemonic::Sed,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::SeiImplied => (
                mnemonic::Mnemonic::Sei,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::TaxImplied => (
                mnemonic::Mnemonic::Tax,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::TayImplied => (
                mnemonic::Mnemonic::Tay,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::TsxImplied => (
                mnemonic::Mnemonic::Tsx,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::TxaImplied => (
                mnemonic::Mnemonic::Txa,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::TxsImplied => (
                mnemonic::Mnemonic::Txs,
                addressing_mode::AddressingMode::Implied,
            ),
            InstructionVariant::TyaImplied => (
                mnemonic::Mnemonic::Tya,
                addressing_mode::AddressingMode::Implied,
            ),
        }
    }
}

impl std::convert::TryFrom<(mnemonic::Mnemonic, addressing_mode::AddressingMode)>
    for InstructionVariant
{
    type Error = InstructionErr;

    fn try_from(
        src: (mnemonic::Mnemonic, addressing_mode::AddressingMode),
    ) -> Result<Self, Self::Error> {
        use addressing_mode::AddressingMode;
        use mnemonic::Mnemonic;

        match src {
            (Mnemonic::Adc, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::AdcAbsolute(am))
            }
            (Mnemonic::Adc, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::AdcAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Adc, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::AdcAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Adc, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::AdcIndirectYIndexed(am))
            }
            (Mnemonic::Adc, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::AdcImmediate(am))
            }
            (Mnemonic::Adc, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::AdcXIndexedIndirect(am))
            }
            (Mnemonic::Adc, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::AdcZeroPage(am))
            }
            (Mnemonic::Adc, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::AdcZeroPageIndexedWithX(am))
            }
            (Mnemonic::And, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::AndAbsolute(am))
            }
            (Mnemonic::And, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::AndAbsoluteIndexedWithX(am))
            }
            (Mnemonic::And, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::AndAbsoluteIndexedWithY(am))
            }
            (Mnemonic::And, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::AndIndirectYIndexed(am))
            }
            (Mnemonic::And, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::AndImmediate(am))
            }
            (Mnemonic::And, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::AndXIndexedIndirect(am))
            }
            (Mnemonic::And, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::AndZeroPage(am))
            }
            (Mnemonic::And, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::AndZeroPageIndexedWithX(am))
            }
            (Mnemonic::Asl, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::AslAbsolute(am))
            }
            (Mnemonic::Asl, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::AslAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Asl, AddressingMode::Accumulator) => Ok(InstructionVariant::AslAccumulator),
            (Mnemonic::Asl, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::AslZeroPage(am))
            }
            (Mnemonic::Asl, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::AslZeroPageIndexedWithX(am))
            }
            (Mnemonic::Bcc, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BccRelative(am))
            }
            (Mnemonic::Bcs, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BcsRelative(am))
            }
            (Mnemonic::Beq, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BeqRelative(am))
            }
            (Mnemonic::Bmi, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BmiRelative(am))
            }
            (Mnemonic::Bit, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::BitAbsolute(am))
            }
            (Mnemonic::Bit, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::BitZeroPage(am))
            }
            (Mnemonic::Bne, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BneRelative(am))
            }
            (Mnemonic::Bpl, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BplRelative(am))
            }
            (Mnemonic::Brk, AddressingMode::Implied) => Ok(InstructionVariant::BrkImplied),
            (Mnemonic::Bvc, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BvcRelative(am))
            }
            (Mnemonic::Bvs, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BvsRelative(am))
            }
            (Mnemonic::Clc, AddressingMode::Implied) => Ok(InstructionVariant::ClcImplied),
            (Mnemonic::Cld, AddressingMode::Implied) => Ok(InstructionVariant::CldImplied),
            (Mnemonic::Cli, AddressingMode::Implied) => Ok(InstructionVariant::CliImplied),
            (Mnemonic::Clv, AddressingMode::Implied) => Ok(InstructionVariant::ClvImplied),
            (Mnemonic::Cmp, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::CmpAbsolute(am))
            }
            (Mnemonic::Cmp, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::CmpAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Cmp, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::CmpAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Cmp, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::CmpIndirectYIndexed(am))
            }
            (Mnemonic::Cmp, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::CmpImmediate(am))
            }
            (Mnemonic::Cmp, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::CmpXIndexedIndirect(am))
            }
            (Mnemonic::Cmp, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::CmpZeroPage(am))
            }
            (Mnemonic::Cmp, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::CmpZeroPageIndexedWithX(am))
            }
            (Mnemonic::Cpx, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::CpxAbsolute(am))
            }
            (Mnemonic::Cpx, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::CpxImmediate(am))
            }
            (Mnemonic::Cpx, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::CpxZeroPage(am))
            }
            (Mnemonic::Cpy, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::CpyAbsolute(am))
            }
            (Mnemonic::Cpy, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::CpyImmediate(am))
            }
            (Mnemonic::Cpy, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::CpyZeroPage(am))
            }
            (Mnemonic::Dec, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::DecAbsolute(am))
            }
            (Mnemonic::Dec, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::DecAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Dec, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::DecZeroPage(am))
            }
            (Mnemonic::Dec, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::DecZeroPageIndexedWithX(am))
            }
            (Mnemonic::Dex, AddressingMode::Implied) => Ok(InstructionVariant::DexImplied),
            (Mnemonic::Dey, AddressingMode::Implied) => Ok(InstructionVariant::DeyImplied),
            (Mnemonic::Eor, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::EorAbsolute(am))
            }
            (Mnemonic::Eor, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::EorAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Eor, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::EorAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Eor, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::EorIndirectYIndexed(am))
            }
            (Mnemonic::Eor, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::EorImmediate(am))
            }
            (Mnemonic::Eor, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::EorXIndexedIndirect(am))
            }
            (Mnemonic::Eor, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::EorZeroPage(am))
            }
            (Mnemonic::Eor, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::EorZeroPageIndexedWithX(am))
            }
            (Mnemonic::Inc, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::IncAbsolute(am))
            }
            (Mnemonic::Inc, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::IncAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Inc, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::IncZeroPage(am))
            }
            (Mnemonic::Inc, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::IncZeroPageIndexedWithX(am))
            }
            (Mnemonic::Inx, AddressingMode::Implied) => Ok(InstructionVariant::InxImplied),
            (Mnemonic::Iny, AddressingMode::Implied) => Ok(InstructionVariant::InyImplied),
            (Mnemonic::Jmp, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::JmpAbsolute(am))
            }
            (Mnemonic::Jmp, AddressingMode::Indirect(am)) => {
                Ok(InstructionVariant::JmpIndirect(am))
            }
            (Mnemonic::Jsr, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::JsrAbsolute(am))
            }
            (Mnemonic::Lda, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LdaAbsolute(am))
            }
            (Mnemonic::Lda, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::LdaAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Lda, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::LdaAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Lda, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::LdaIndirectYIndexed(am))
            }
            (Mnemonic::Lda, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::LdaImmediate(am))
            }
            (Mnemonic::Lda, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::LdaXIndexedIndirect(am))
            }
            (Mnemonic::Lda, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LdaZeroPage(am))
            }
            (Mnemonic::Lda, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::LdaZeroPageIndexedWithX(am))
            }
            (Mnemonic::Ldx, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LdxAbsolute(am))
            }
            (Mnemonic::Ldx, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::LdxAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Ldx, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::LdxImmediate(am))
            }
            (Mnemonic::Ldx, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LdxZeroPage(am))
            }
            (Mnemonic::Ldx, AddressingMode::ZeroPageIndexedWithY(am)) => {
                Ok(InstructionVariant::LdxZeroPageIndexedWithY(am))
            }
            (Mnemonic::Ldy, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LdyAbsolute(am))
            }
            (Mnemonic::Ldy, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::LdyAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Ldy, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::LdyImmediate(am))
            }
            (Mnemonic::Ldy, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LdyZeroPage(am))
            }
            (Mnemonic::Ldy, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::LdyZeroPageIndexedWithX(am))
            }
            (Mnemonic::Lsr, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LsrAbsolute(am))
            }
            (Mnemonic::Lsr, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::LsrAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Lsr, AddressingMode::Accumulator) => Ok(InstructionVariant::LsrAccumulator),
            (Mnemonic::Lsr, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LsrZeroPage(am))
            }
            (Mnemonic::Lsr, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::LsrZeroPageIndexedWithX(am))
            }
            (Mnemonic::Nop, AddressingMode::Implied) => Ok(InstructionVariant::NopImplied),
            (Mnemonic::Ora, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::OraAbsolute(am))
            }
            (Mnemonic::Ora, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::OraAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Ora, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::OraAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Ora, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::OraIndirectYIndexed(am))
            }
            (Mnemonic::Ora, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::OraImmediate(am))
            }
            (Mnemonic::Ora, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::OraXIndexedIndirect(am))
            }
            (Mnemonic::Ora, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::OraZeroPage(am))
            }
            (Mnemonic::Ora, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::OraZeroPageIndexedWithX(am))
            }
            (Mnemonic::Pha, AddressingMode::Implied) => Ok(InstructionVariant::PhaImplied),
            (Mnemonic::Php, AddressingMode::Implied) => Ok(InstructionVariant::PhpImplied),
            (Mnemonic::Pla, AddressingMode::Implied) => Ok(InstructionVariant::PlaImplied),
            (Mnemonic::Plp, AddressingMode::Implied) => Ok(InstructionVariant::PlpImplied),
            (Mnemonic::Rol, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::RolAbsolute(am))
            }
            (Mnemonic::Rol, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::RolAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Rol, AddressingMode::Accumulator) => Ok(InstructionVariant::RolAccumulator),
            (Mnemonic::Rol, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::RolZeroPage(am))
            }
            (Mnemonic::Rol, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::RolZeroPageIndexedWithX(am))
            }
            (Mnemonic::Ror, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::RorAbsolute(am))
            }
            (Mnemonic::Ror, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::RorAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Ror, AddressingMode::Accumulator) => Ok(InstructionVariant::RorAccumulator),
            (Mnemonic::Ror, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::RorZeroPage(am))
            }
            (Mnemonic::Ror, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::RorZeroPageIndexedWithX(am))
            }
            (Mnemonic::Rti, AddressingMode::Implied) => Ok(InstructionVariant::RtiImplied),
            (Mnemonic::Rts, AddressingMode::Implied) => Ok(InstructionVariant::RtsImplied),

            (Mnemonic::Sbc, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::SbcAbsolute(am))
            }
            (Mnemonic::Sbc, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::SbcAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Sbc, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::SbcAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Sbc, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::SbcIndirectYIndexed(am))
            }
            (Mnemonic::Sbc, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::SbcImmediate(am))
            }
            (Mnemonic::Sbc, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::SbcXIndexedIndirect(am))
            }
            (Mnemonic::Sbc, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::SbcZeroPage(am))
            }
            (Mnemonic::Sbc, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::SbcZeroPageIndexedWithX(am))
            }
            (Mnemonic::Sta, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::StaAbsolute(am))
            }
            (Mnemonic::Sta, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::StaAbsoluteIndexedWithX(am))
            }
            (Mnemonic::Sta, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::StaAbsoluteIndexedWithY(am))
            }
            (Mnemonic::Sta, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::StaIndirectYIndexed(am))
            }
            (Mnemonic::Sta, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::StaXIndexedIndirect(am))
            }
            (Mnemonic::Sta, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::StaZeroPage(am))
            }
            (Mnemonic::Sta, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::StaZeroPageIndexedWithX(am))
            }
            (Mnemonic::Stx, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::StxAbsolute(am))
            }
            (Mnemonic::Stx, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::StxZeroPage(am))
            }
            (Mnemonic::Stx, AddressingMode::ZeroPageIndexedWithY(am)) => {
                Ok(InstructionVariant::StxZeroPageIndexedWithY(am))
            }
            (Mnemonic::Sty, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::StyAbsolute(am))
            }
            (Mnemonic::Sty, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::StyZeroPage(am))
            }
            (Mnemonic::Sty, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::StyZeroPageIndexedWithX(am))
            }
            (Mnemonic::Sec, AddressingMode::Implied) => Ok(InstructionVariant::SecImplied),
            (Mnemonic::Sed, AddressingMode::Implied) => Ok(InstructionVariant::SedImplied),
            (Mnemonic::Sei, AddressingMode::Implied) => Ok(InstructionVariant::SeiImplied),
            (Mnemonic::Tax, AddressingMode::Implied) => Ok(InstructionVariant::TaxImplied),
            (Mnemonic::Tay, AddressingMode::Implied) => Ok(InstructionVariant::TayImplied),
            (Mnemonic::Tsx, AddressingMode::Implied) => Ok(InstructionVariant::TsxImplied),
            (Mnemonic::Txa, AddressingMode::Implied) => Ok(InstructionVariant::TxaImplied),
            (Mnemonic::Txs, AddressingMode::Implied) => Ok(InstructionVariant::TxsImplied),
            (Mnemonic::Tya, AddressingMode::Implied) => Ok(InstructionVariant::TyaImplied),
            _ => Err(InstructionErr::InvalidInstruction(src.0, src.1.into())),
        }
    }
}

pub fn parse_instruction(bytes: impl AsRef<[u8]>) -> Option<InstructionVariant> {
    use addressing_mode::{AddressingMode, AddressingModeType};

    // An instructions little endian lower byte will be first after the opcode.
    const LOWER_BYTE_OFFSET: usize = 1;
    // An instructions little endian upper byte will be second after the opcode.
    const UPPER_BYTE_OFFSET: usize = 2;

    let bytes = bytes.as_ref();

    let opcode = bytes.first().copied().map(bit_decoder::Opcode::from)?;
    let (mnemonic, am) = bit_decoder::decode(&opcode)?;

    let variant_components = match am {
        AddressingModeType::Accumulator => (mnemonic, AddressingMode::Accumulator),
        AddressingModeType::Implied => (mnemonic, AddressingMode::Implied),
        AddressingModeType::Immediate => {
            let data = bytes.get(LOWER_BYTE_OFFSET)?;
            (mnemonic, AddressingMode::Immediate(*data))
        }
        AddressingModeType::ZeroPage => {
            let data = bytes.get(LOWER_BYTE_OFFSET)?;
            (mnemonic, AddressingMode::ZeroPage(*data))
        }
        AddressingModeType::Relative => {
            let data = bytes.get(LOWER_BYTE_OFFSET).map(|&data| data as i8)?;
            (mnemonic, AddressingMode::Relative(data))
        }
        AddressingModeType::ZeroPageIndexedWithX => {
            let data = bytes.get(LOWER_BYTE_OFFSET)?;
            (mnemonic, AddressingMode::ZeroPageIndexedWithX(*data))
        }
        AddressingModeType::ZeroPageIndexedWithY => {
            let data = bytes.get(LOWER_BYTE_OFFSET)?;
            (mnemonic, AddressingMode::ZeroPageIndexedWithY(*data))
        }
        AddressingModeType::XIndexedIndirect => {
            let data = bytes.get(LOWER_BYTE_OFFSET)?;
            (mnemonic, AddressingMode::XIndexedIndirect(*data))
        }
        AddressingModeType::IndirectYIndexed => {
            let data = bytes.get(LOWER_BYTE_OFFSET)?;
            (mnemonic, AddressingMode::IndirectYIndexed(*data))
        }
        AddressingModeType::Indirect => {
            let lower = bytes.get(LOWER_BYTE_OFFSET)?;
            let upper = bytes.get(UPPER_BYTE_OFFSET)?;

            (
                mnemonic,
                AddressingMode::Indirect(u16::from_le_bytes([*lower, *upper])),
            )
        }
        AddressingModeType::Absolute => {
            let lower = bytes.get(LOWER_BYTE_OFFSET)?;
            let upper = bytes.get(UPPER_BYTE_OFFSET)?;

            (
                mnemonic,
                AddressingMode::Absolute(u16::from_le_bytes([*lower, *upper])),
            )
        }
        AddressingModeType::AbsoluteIndexedWithX => {
            let lower = bytes.get(LOWER_BYTE_OFFSET)?;
            let upper = bytes.get(UPPER_BYTE_OFFSET)?;

            (
                mnemonic,
                AddressingMode::AbsoluteIndexedWithX(u16::from_le_bytes([*lower, *upper])),
            )
        }
        AddressingModeType::AbsoluteIndexedWithY => {
            let lower = bytes.get(LOWER_BYTE_OFFSET)?;
            let upper = bytes.get(UPPER_BYTE_OFFSET)?;

            (
                mnemonic,
                AddressingMode::AbsoluteIndexedWithY(u16::from_le_bytes([*lower, *upper])),
            )
        }
    };

    variant_components.try_into().ok()
}
