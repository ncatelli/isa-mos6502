//! This crate stores helper types for all mnemonics and addressing modes for
//! the MOS6502 ISA. In addition, these types provide helpers for the
//! translation between the bytecode and an intermediate representation of the
//! instruction set.

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

            impl<'a> parcel::Parser<'a, &'a [u8], $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>>
                for $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>
            {
                fn parse(
                    &self,
                    input: &'a [u8],
                ) -> parcel::ParseResult<&'a [u8], $crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>> {
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
                use parcel::prelude::v1::Parser;
                $(
                    #[test]
                    fn $name() {
                        let bytecode: [u8; 3] = [$opcode, 0x00, 0x00];
                        assert_eq!(
                            $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <$crate::addressing_mode::$am>::default()),
                            $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <$crate::addressing_mode::$am>::default()).parse(&bytecode).unwrap().unwrap()
                        )
                    }
                )*
            }

            mod conversion {
                #[test]
                fn conversion_from_generic_to_concrete() {
                    assert_eq!(
                        $crate::InstructionVariant::NOPImplied,
                        std::convert::From::from($crate::Instruction::new(<$crate::mnemonic::NOP>::default(), <$crate::addressing_mode::Implied>::default()))
                    )
                }

                #[test]
                fn conversion_from_concrete_to_generic() {
                    assert_eq!(
                        Ok($crate::Instruction::new(<$crate::mnemonic::NOP>::default(), <$crate::addressing_mode::Implied>::default())),
                        std::convert::TryFrom::try_from($crate::InstructionVariant::NOPImplied),
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
    adc_absolute: ADC, Absolute, ADCAbsolute, 0x6d, 4,
    adc_absolute_indexed_with_x: ADC, AbsoluteIndexedWithX, ADCAbsoluteIndexedWithX, 0x7d, 4,
    adc_absolute_indexed_with_y: ADC, AbsoluteIndexedWithY, ADCAbsoluteIndexedWithY, 0x79, 4,
    adc_indirect_y_indexed: ADC, IndirectYIndexed, ADCIndirectYIndexed, 0x71, 5,
    adc_immediate: ADC, Immediate, ADCImmediate, 0x69, 2,
    adc_x_indexed_indirect: ADC, XIndexedIndirect, ADCXIndexedIndirect, 0x61, 6,
    adc_zeropage: ADC, ZeroPage, ADCZeroPage, 0x65, 3,
    adc_zeropage_indexed_with_x: ADC, ZeroPageIndexedWithX, ADCZeroPageIndexedWithX, 0x75, 4,
    sbc_absolute: SBC, Absolute, SBCAbsolute, 0xed, 4,
    sbc_absolute_indexed_with_x: SBC, AbsoluteIndexedWithX, SBCAbsoluteIndexedWithX, 0xfd, 4,
    sbc_absolute_indexed_with_y: SBC, AbsoluteIndexedWithY, SBCAbsoluteIndexedWithY, 0xf9, 4,
    sbc_indirect_y_indexed: SBC, IndirectYIndexed, SBCIndirectYIndexed, 0xf1, 5,
    sbc_immediate: SBC, Immediate, SBCImmediate, 0xe9, 2,
    sbc_x_indexed_indirect: SBC, XIndexedIndirect, SBCXIndexedIndirect, 0xe1, 6,
    sbc_zeropage: SBC, ZeroPage, SBCZeroPage, 0xe5, 3,
    sbc_zeropage_indexed_with_x: SBC, ZeroPageIndexedWithX, SBCZeroPageIndexedWithX, 0xf5, 4,
    and_absolute: AND, Absolute, ANDAbsolute, 0x2d, 4,
    and_absolute_indexed_with_x: AND, AbsoluteIndexedWithX, ANDAbsoluteIndexedWithX, 0x3d, 4,
    and_absolute_indexed_with_y: AND, AbsoluteIndexedWithY, ANDAbsoluteIndexedWithY, 0x39, 4,
    and_indirect_y_indexed: AND, IndirectYIndexed, ANDIndirectYIndexed, 0x31, 5,
    and_immediate: AND, Immediate, ANDImmediate, 0x29, 2,
    and_x_indexed_indirect: AND, XIndexedIndirect, ANDXIndexedIndirect, 0x21, 6,
    and_zeropage: AND, ZeroPage, ANDZeroPage, 0x25, 3,
    and_zeropage_indxed_with_x: AND, ZeroPageIndexedWithX, ANDZeroPageIndexedWithX, 0x35, 4,
    asl_absolute: ASL, Absolute, ASLAbsolute, 0x0e, 6,
    asl_absolute_indexed_with_x: ASL, AbsoluteIndexedWithX, ASLAbsoluteIndexedWithX, 0x1e, 7,
    asl_accumulator: ASL, Accumulator, ASLAccumulator, 0x0a, 2,
    asl_zeropage: ASL, ZeroPage, ASLZeroPage, 0x06, 5,
    asl_zeropage_indexed_with_x: ASL, ZeroPageIndexedWithX, ASLZeroPageIndexedWithX, 0x16, 6,
    bit_absolute: BIT, Absolute, BITAbsolute, 0x2c, 4,
    bit_zeropage: BIT, ZeroPage, BITZeroPage, 0x24, 3,
    eor_absolute: EOR, Absolute, EORAbsolute, 0x4d, 4,
    eor_absolute_indexed_with_x: EOR, AbsoluteIndexedWithX, EORAbsoluteIndexedWithX, 0x5d, 4,
    eor_absolute_indexed_with_y: EOR, AbsoluteIndexedWithY, EORAbsoluteIndexedWithY, 0x59, 4,
    eor_indirect_y_indexed: EOR, IndirectYIndexed, EORIndirectYIndexed, 0x51, 5,
    eor_immediate: EOR, Immediate, EORImmediate, 0x49, 2,
    eor_x_indexed_indirect: EOR, XIndexedIndirect, EORXIndexedIndirect, 0x41, 6,
    eor_zeropage: EOR, ZeroPage, EORZeroPage, 0x45, 3,
    eor_zeropage_indexed_with_x: EOR, ZeroPageIndexedWithX, EORZeroPageIndexedWithX, 0x55, 4,
    lsr_absolute: LSR, Absolute, LSRAbsolute, 0x4e, 6,
    lsr_absolute_indexed_with_x: LSR, AbsoluteIndexedWithX, LSRAbsoluteIndexedWithX, 0x5e, 7,
    lsr_accumulator: LSR, Accumulator, LSRAccumulator, 0x4a, 2,
    lsr_zeropage: LSR, ZeroPage, LSRZeroPage, 0x46, 5,
    lsr_zeropage_indexed_with_x: LSR, ZeroPageIndexedWithX, LSRZeroPageIndexedWithX, 0x56, 6,
    ora_absolute: ORA, Absolute, ORAAbsolute, 0x0d, 4,
    ora_absolute_indexed_with_x: ORA, AbsoluteIndexedWithX, ORAAbsoluteIndexedWithX, 0x1d, 4,
    ora_absolute_indexed_with_y: ORA, AbsoluteIndexedWithY, ORAAbsoluteIndexedWithY, 0x19, 4,
    ora_indirect_y_indexed: ORA, IndirectYIndexed, ORAIndirectYIndexed, 0x11, 5,
    ora_immediate: ORA, Immediate, ORAImmediate, 0x09, 2,
    ora_x_indexed_indirect: ORA, XIndexedIndirect, ORAXIndexedIndirect, 0x01, 6,
    ora_zeroapage: ORA, ZeroPage, ORAZeroPage, 0x05, 3,
    ora_zeropage_indexed_with_x: ORA, ZeroPageIndexedWithX, ORAZeroPageIndexedWithX, 0x15, 4,
    rol_absolute: ROL, Absolute, ROLAbsolute, 0x2e, 6,
    rol_absolute_indexed_with_x: ROL, AbsoluteIndexedWithX, ROLAbsoluteIndexedWithX, 0x3e, 7,
    rol_accumulator: ROL, Accumulator, ROLAccumulator, 0x2a, 2,
    rol_zeropage: ROL, ZeroPage, ROLZeroPage, 0x26, 5,
    rol_zeropage_indexed_with_x: ROL, ZeroPageIndexedWithX, ROLZeroPageIndexedWithX, 0x36, 6,
    ror_absolute: ROR, Absolute, RORAbsolute, 0x6e, 6,
    ror_absolute_indexed_with_x: ROR, AbsoluteIndexedWithX, RORAbsoluteIndexedWithX, 0x7e, 7,
    ror_acumulator: ROR, Accumulator, RORAccumulator, 0x6a, 2,
    ror_zeropage: ROR, ZeroPage, RORZeroPage, 0x66, 5,
    ror_zeropage_indexed_with_x: ROR, ZeroPageIndexedWithX, RORZeroPageIndexedWithX, 0x76, 6,
    bcc_relative: BCC, Relative, BCCRelative, 0x90, 2,
    bcs_relative: BCS, Relative, BCSRelative, 0xb0, 2,
    beq_relative: BEQ, Relative, BEQRelative, 0xf0, 2,
    bmi_relative: BMI, Relative, BMIRelative, 0x30, 2,
    bne_relative: BNE, Relative, BNERelative, 0xd0, 2,
    bpl_relative: BPL, Relative, BPLRelative, 0x10, 2,
    bvc_relative: BVC, Relative, BVCRelative, 0x50, 2,
    bvs_relative: BVS, Relative, BVSRelative, 0x70, 2,
    clc_implied: CLC, Implied, CLCImplied, 0x18, 2,
    cld_implied: CLD, Implied, CLDImplied, 0xd8, 2,
    cli_implied: CLI, Implied, CLIImplied, 0x58, 2,
    clv_implied: CLV, Implied, CLVImplied, 0xb8, 2,
    cmp_absolute: CMP, Absolute, CMPAbsolute, 0xcd, 4,
    cmp_absolute_indexed_with_x: CMP, AbsoluteIndexedWithX, CMPAbsoluteIndexedWithX, 0xdd, 4,
    cmp_absolute_indexed_with_y: CMP, AbsoluteIndexedWithY, CMPAbsoluteIndexedWithY, 0xd9, 4,
    cmp_indirect_y_indexed: CMP, IndirectYIndexed, CMPIndirectYIndexed, 0xd1, 5,
    cmp_immediate: CMP, Immediate, CMPImmediate, 0xc9, 2,
    cmp_x_indexed_indirect: CMP, XIndexedIndirect, CMPXIndexedIndirect, 0xc1, 6,
    cmp_zeropage: CMP, ZeroPage, CMPZeroPage, 0xc5, 3,
    cmp_zeropage_indexexd_with_x: CMP, ZeroPageIndexedWithX, CMPZeroPageIndexedWithX, 0xd5, 4,
    cpx_absolute: CPX, Absolute, CPXAbsolute, 0xec, 4,
    cpx_immediate: CPX, Immediate, CPXImmediate, 0xe0, 2,
    cpx_zeroage: CPX, ZeroPage, CPXZeroPage, 0xe4, 3,
    cpy_absolute: CPY, Absolute, CPYAbsolute, 0xcc, 4,
    cpy_immediate: CPY, Immediate, CPYImmediate, 0xc0, 2,
    cpy_zeropage: CPY, ZeroPage, CPYZeroPage, 0xc4, 3,
    dec_absolute: DEC, Absolute, DECAbsolute, 0xce, 6,
    dec_absolute_indexed_with_x: DEC, AbsoluteIndexedWithX, DECAbsoluteIndexedWithX, 0xde, 7,
    dec_zeropage: DEC, ZeroPage, DECZeroPage, 0xc6, 5,
    dec_zeropage_indexed_with_x: DEC, ZeroPageIndexedWithX, DECZeroPageIndexedWithX, 0xd6, 6,
    dex_implied: DEX, Implied, DEXImplied, 0xca, 2,
    dey_implied: DEY, Implied, DEYImplied, 0x88, 2,
    inc_absolute: INC, Absolute, INCAbsolute, 0xee, 6,
    inc_absolute_indexed_with_x: INC, AbsoluteIndexedWithX, INCAbsoluteIndexedWithX, 0xfe, 7,
    inc_zeropage: INC, ZeroPage, INCZeroPage, 0xe6, 5,
    inc_zeropage_indexed_with_x: INC, ZeroPageIndexedWithX, INCZeroPageIndexedWithX, 0xf6, 6,
    inx_implied: INX, Implied, INXImplied, 0xe8, 2,
    iny_implied: INY, Implied, INYImplied, 0xc8, 2,
    jmp_absolute: JMP, Absolute, JMPAbsolute, 0x4c, 3,
    jmp_indirect: JMP, Indirect, JMPIndirect, 0x6c, 5,
    jsr_absolute: JSR, Absolute, JSRAbsolute, 0x20, 6,
    lda_immediate: LDA, Immediate, LDAImmediate, 0xa9, 2,
    lda_zeropage: LDA, ZeroPage, LDAZeroPage, 0xa5, 3,
    lda_zeropage_indexed_with_x: LDA, ZeroPageIndexedWithX, LDAZeroPageIndexedWithX, 0xb5, 4,
    lda_absolute: LDA, Absolute, LDAAbsolute, 0xad, 4,
    lda_absolute_indexed_with_x: LDA, AbsoluteIndexedWithX, LDAAbsoluteIndexedWithX, 0xbd, 4,
    lda_absolute_indexed_with_y: LDA, AbsoluteIndexedWithY, LDAAbsoluteIndexedWithY, 0xb9, 4,
    lda_indirect_y_indexed: LDA, IndirectYIndexed, LDAIndirectYIndexed, 0xb1, 5,
    lda_x_indexed_indirect: LDA, XIndexedIndirect, LDAXIndexedIndirect, 0xa1, 6,
    ldx_absolute: LDX, Absolute, LDXAbsolute, 0xae, 4,
    ldx_absolute_indexed_with_y: LDX, AbsoluteIndexedWithY, LDXAbsoluteIndexedWithY, 0xbe, 4,
    ldx_immediate: LDX, Immediate, LDXImmediate, 0xa2, 2,
    ldx_zeropage: LDX, ZeroPage, LDXZeroPage, 0xa6, 3,
    ldx_zeropage_indexed_with_y: LDX, ZeroPageIndexedWithY, LDXZeroPageIndexedWithY, 0xb6, 4,
    ldy_absolute: LDY, Absolute, LDYAbsolute, 0xac, 4,
    ldy_absolute_indexed_with_x: LDY, AbsoluteIndexedWithX, LDYAbsoluteIndexedWithX, 0xbc, 4,
    ldy_immediate: LDY, Immediate, LDYImmediate, 0xa0, 2,
    ldy_zeropage: LDY, ZeroPage, LDYZeroPage, 0xa4, 3,
    ldy_zeropage_indexed_with_x: LDY, ZeroPageIndexedWithX, LDYZeroPageIndexedWithX, 0xb4, 4,
    pha_implied: PHA, Implied, PHAImplied, 0x48, 3,
    php_implied: PHP, Implied, PHPImplied, 0x08, 3,
    pla_implied: PLA, Implied, PLAImplied, 0x68, 4,
    plp_implied: PLP, Implied, PLPImplied, 0x28, 4,
    rti_implied: RTI, Implied, RTIImplied, 0x40, 6,
    rts_implied: RTS, Implied, RTSImplied, 0x60, 6,
    sec_implied: SEC, Implied, SECImplied, 0x38, 2,
    sed_implied: SED, Implied, SEDImplied, 0xf8, 2,
    sei_implied: SEI, Implied, SEIImplied, 0x78, 2,
    sta_absolute: STA, Absolute, STAAbsolute, 0x8d, 4,
    sta_absolute_indexed_with_x: STA, AbsoluteIndexedWithX, STAAbsoluteIndexedWithX, 0x9d, 5,
    sta_absolute_indexed_with_y: STA, AbsoluteIndexedWithY, STAAbsoluteIndexedWithY, 0x99, 5,
    sta_indirect_y_indexed: STA, IndirectYIndexed, STAIndirectYIndexed, 0x91, 6,
    sta_x_indexed_indirect: STA, XIndexedIndirect, STAXIndexedIndirect, 0x81, 6,
    sta_zeropage: STA, ZeroPage, STAZeroPage, 0x85, 3,
    sta_zeropage_indexed_with_x: STA, ZeroPageIndexedWithX, STAZeroPageIndexedWithX, 0x95, 4,
    stx_absolute: STX, Absolute, STXAbsolute, 0x8e, 4,
    stx_zeropage: STX, ZeroPage, STXZeroPage, 0x86, 3,
    stx_zeropage_indexed_with_y: STX, ZeroPageIndexedWithY, STXZeroPageIndexedWithY, 0x96, 4,
    sty_absolute: STY, Absolute, STYAbsolute, 0x8c, 4,
    sty_zeropage: STY, ZeroPage, STYZeroPage, 0x84, 3,
    sty_zeropage_indexed_with_x: STY, ZeroPageIndexedWithX, STYZeroPageIndexedWithX, 0x94, 4,
    tax_implied: TAX, Implied, TAXImplied, 0xaa, 2,
    tay_implied: TAY, Implied, TAYImplied, 0xa8, 2,
    tsx_implied: TSX, Implied, TSXImplied, 0xba, 2,
    txa_implied: TXA, Implied, TXAImplied, 0x8a, 2,
    txs_implied: TXS, Implied, TXSImplied, 0x9a, 2,
    tya_implied: TYA, Implied, TYAImplied, 0x98, 2,
    brk_implied: BRK, Implied, BRKImplied, 0x00, 7,
    nop_implied: NOP, Implied, NOPImplied, 0xea, 2,
);

/// InstructionVariant functions as a concrete implementations of the generic
/// instruction types for use when runtime.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InstructionVariant {
    ADCAbsolute(u16),
    ADCAbsoluteIndexedWithX(u16),
    ADCAbsoluteIndexedWithY(u16),
    ADCIndirectYIndexed(u8),
    ADCImmediate(u8),
    ADCXIndexedIndirect(u8),
    ADCZeroPage(u8),
    ADCZeroPageIndexedWithX(u8),
    ANDAbsolute(u16),
    ANDAbsoluteIndexedWithX(u16),
    ANDAbsoluteIndexedWithY(u16),
    ANDIndirectYIndexed(u8),
    ANDImmediate(u8),
    ANDXIndexedIndirect(u8),
    ANDZeroPage(u8),
    ANDZeroPageIndexedWithX(u8),
    ASLAbsolute(u16),
    ASLAbsoluteIndexedWithX(u16),
    ASLAccumulator,
    ASLZeroPage(u8),
    ASLZeroPageIndexedWithX(u8),
    BCCRelative(i8),
    BCSRelative(i8),
    BEQRelative(i8),
    BMIRelative(i8),
    BITAbsolute(u16),
    BITZeroPage(u8),
    BNERelative(i8),
    BPLRelative(i8),
    BRKImplied,
    BVCRelative(i8),
    BVSRelative(i8),
    CLCImplied,
    CLDImplied,
    CLIImplied,
    CLVImplied,
    CMPAbsolute(u16),
    CMPAbsoluteIndexedWithX(u16),
    CMPAbsoluteIndexedWithY(u16),
    CMPIndirectYIndexed(u8),
    CMPImmediate(u8),
    CMPXIndexedIndirect(u8),
    CMPZeroPage(u8),
    CMPZeroPageIndexedWithX(u8),
    CPXAbsolute(u16),
    CPXImmediate(u8),
    CPXZeroPage(u8),
    CPYAbsolute(u16),
    CPYImmediate(u8),
    CPYZeroPage(u8),
    DECAbsolute(u16),
    DECAbsoluteIndexedWithX(u16),
    DECZeroPage(u8),
    DECZeroPageIndexedWithX(u8),
    DEXImplied,
    DEYImplied,
    EORAbsolute(u16),
    EORAbsoluteIndexedWithX(u16),
    EORAbsoluteIndexedWithY(u16),
    EORIndirectYIndexed(u8),
    EORImmediate(u8),
    EORXIndexedIndirect(u8),
    EORZeroPage(u8),
    EORZeroPageIndexedWithX(u8),
    INCAbsolute(u16),
    INCAbsoluteIndexedWithX(u16),
    INCZeroPage(u8),
    INCZeroPageIndexedWithX(u8),
    INXImplied,
    INYImplied,
    JMPAbsolute(u16),
    JMPIndirect(u16),
    JSRAbsolute(u16),
    LDAAbsolute(u16),
    LDAAbsoluteIndexedWithX(u16),
    LDAAbsoluteIndexedWithY(u16),
    LDAIndirectYIndexed(u8),
    LDAImmediate(u8),
    LDAXIndexedIndirect(u8),
    LDAZeroPage(u8),
    LDAZeroPageIndexedWithX(u8),
    LDXAbsolute(u16),
    LDXAbsoluteIndexedWithY(u16),
    LDXImmediate(u8),
    LDXZeroPage(u8),
    LDXZeroPageIndexedWithY(u8),
    LDYAbsolute(u16),
    LDYAbsoluteIndexedWithX(u16),
    LDYImmediate(u8),
    LDYZeroPage(u8),
    LDYZeroPageIndexedWithX(u8),
    LSRAbsolute(u16),
    LSRAbsoluteIndexedWithX(u16),
    LSRAccumulator,
    LSRZeroPage(u8),
    LSRZeroPageIndexedWithX(u8),
    NOPImplied,
    ORAAbsolute(u16),
    ORAAbsoluteIndexedWithX(u16),
    ORAAbsoluteIndexedWithY(u16),
    ORAIndirectYIndexed(u8),
    ORAImmediate(u8),
    ORAXIndexedIndirect(u8),
    ORAZeroPage(u8),
    ORAZeroPageIndexedWithX(u8),
    PHAImplied,
    PHPImplied,
    PLAImplied,
    PLPImplied,
    ROLAbsolute(u16),
    ROLAbsoluteIndexedWithX(u16),
    ROLAccumulator,
    ROLZeroPage(u8),
    ROLZeroPageIndexedWithX(u8),
    RORAbsolute(u16),
    RORAbsoluteIndexedWithX(u16),
    RORAccumulator,
    RORZeroPage(u8),
    RORZeroPageIndexedWithX(u8),
    RTIImplied,
    RTSImplied,
    SBCAbsolute(u16),
    SBCAbsoluteIndexedWithX(u16),
    SBCAbsoluteIndexedWithY(u16),
    SBCIndirectYIndexed(u8),
    SBCImmediate(u8),
    SBCXIndexedIndirect(u8),
    SBCZeroPage(u8),
    SBCZeroPageIndexedWithX(u8),
    STAAbsolute(u16),
    STAAbsoluteIndexedWithX(u16),
    STAAbsoluteIndexedWithY(u16),
    STAIndirectYIndexed(u8),
    STAXIndexedIndirect(u8),
    STAZeroPage(u8),
    STAZeroPageIndexedWithX(u8),
    STXAbsolute(u16),
    STXZeroPage(u8),
    STXZeroPageIndexedWithY(u8),
    STYAbsolute(u16),
    STYZeroPage(u8),
    STYZeroPageIndexedWithX(u8),
    SECImplied,
    SEDImplied,
    SEIImplied,
    TAXImplied,
    TAYImplied,
    TSXImplied,
    TXAImplied,
    TXSImplied,
    TYAImplied,
}

/// Implements bytecode converstion for InstructionVariant by explicitly converting to the generic type.
impl std::convert::From<InstructionVariant> for Bytecode {
    fn from(src: InstructionVariant) -> Bytecode {
        match src {
            InstructionVariant::ADCAbsolute(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::Absolute(am)).into()
            }

            InstructionVariant::ADCAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::ADCAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::ADCIndirectYIndexed(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::ADCImmediate(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::ADCXIndexedIndirect(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::ADCZeroPage(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::ADCZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::ADC, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::ANDAbsolute(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::ANDAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::ANDAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::ANDIndirectYIndexed(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::ANDImmediate(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::ANDXIndexedIndirect(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::ANDZeroPage(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::ANDZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::AND, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::ASLAbsolute(am) => {
                Instruction::new(mnemonic::ASL, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::ASLAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::ASL, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::ASLAccumulator => {
                Instruction::new(mnemonic::ASL, addressing_mode::Accumulator).into()
            }
            InstructionVariant::ASLZeroPage(am) => {
                Instruction::new(mnemonic::ASL, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::ASLZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::ASL, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::BCCRelative(am) => {
                Instruction::new(mnemonic::BCC, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BCSRelative(am) => {
                Instruction::new(mnemonic::BCS, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BEQRelative(am) => {
                Instruction::new(mnemonic::BEQ, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BMIRelative(am) => {
                Instruction::new(mnemonic::BMI, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BITAbsolute(am) => {
                Instruction::new(mnemonic::BIT, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::BITZeroPage(am) => {
                Instruction::new(mnemonic::BIT, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::BNERelative(am) => {
                Instruction::new(mnemonic::BNE, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BPLRelative(am) => {
                Instruction::new(mnemonic::BPL, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BRKImplied => {
                Instruction::new(mnemonic::BRK, addressing_mode::Implied).into()
            }
            InstructionVariant::BVCRelative(am) => {
                Instruction::new(mnemonic::BVC, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::BVSRelative(am) => {
                Instruction::new(mnemonic::BVS, addressing_mode::Relative(am)).into()
            }
            InstructionVariant::CLCImplied => {
                Instruction::new(mnemonic::CLC, addressing_mode::Implied).into()
            }
            InstructionVariant::CLDImplied => {
                Instruction::new(mnemonic::CLD, addressing_mode::Implied).into()
            }
            InstructionVariant::CLIImplied => {
                Instruction::new(mnemonic::CLI, addressing_mode::Implied).into()
            }
            InstructionVariant::CLVImplied => {
                Instruction::new(mnemonic::CLV, addressing_mode::Implied).into()
            }
            InstructionVariant::CMPAbsolute(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::CMPAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::CMPAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::CMPIndirectYIndexed(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::CMPImmediate(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::CMPXIndexedIndirect(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::CMPZeroPage(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::CMPZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::CMP, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::CPXAbsolute(am) => {
                Instruction::new(mnemonic::CPX, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::CPXImmediate(am) => {
                Instruction::new(mnemonic::CPX, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::CPXZeroPage(am) => {
                Instruction::new(mnemonic::CPX, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::CPYAbsolute(am) => {
                Instruction::new(mnemonic::CPY, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::CPYImmediate(am) => {
                Instruction::new(mnemonic::CPY, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::CPYZeroPage(am) => {
                Instruction::new(mnemonic::CPY, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::DECAbsolute(am) => {
                Instruction::new(mnemonic::DEC, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::DECAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::DEC, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::DECZeroPage(am) => {
                Instruction::new(mnemonic::DEC, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::DECZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::DEC, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::DEXImplied => {
                Instruction::new(mnemonic::DEX, addressing_mode::Implied).into()
            }
            InstructionVariant::DEYImplied => {
                Instruction::new(mnemonic::DEY, addressing_mode::Implied).into()
            }
            InstructionVariant::EORAbsolute(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::EORAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::EORAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::EORIndirectYIndexed(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::EORImmediate(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::EORXIndexedIndirect(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::EORZeroPage(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::EORZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::EOR, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::INCAbsolute(am) => {
                Instruction::new(mnemonic::INC, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::INCAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::INC, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::INCZeroPage(am) => {
                Instruction::new(mnemonic::INC, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::INCZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::INC, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::INXImplied => {
                Instruction::new(mnemonic::INX, addressing_mode::Implied).into()
            }
            InstructionVariant::INYImplied => {
                Instruction::new(mnemonic::INY, addressing_mode::Implied).into()
            }
            InstructionVariant::JMPAbsolute(am) => {
                Instruction::new(mnemonic::JMP, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::JMPIndirect(am) => {
                Instruction::new(mnemonic::JMP, addressing_mode::Indirect(am)).into()
            }
            InstructionVariant::JSRAbsolute(am) => {
                Instruction::new(mnemonic::JSR, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LDAAbsolute(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LDAAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::LDAAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::LDAIndirectYIndexed(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::LDAImmediate(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::LDAXIndexedIndirect(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::LDAZeroPage(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LDAZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::LDA, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::LDXAbsolute(am) => {
                Instruction::new(mnemonic::LDX, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LDXAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::LDX, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::LDXImmediate(am) => {
                Instruction::new(mnemonic::LDX, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::LDXZeroPage(am) => {
                Instruction::new(mnemonic::LDX, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LDXZeroPageIndexedWithY(am) => {
                Instruction::new(mnemonic::LDX, addressing_mode::ZeroPageIndexedWithY(am)).into()
            }
            InstructionVariant::LDYAbsolute(am) => {
                Instruction::new(mnemonic::LDY, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LDYAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::LDY, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::LDYImmediate(am) => {
                Instruction::new(mnemonic::LDY, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::LDYZeroPage(am) => {
                Instruction::new(mnemonic::LDY, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LDYZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::LDY, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::LSRAbsolute(am) => {
                Instruction::new(mnemonic::LSR, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::LSRAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::LSR, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::LSRAccumulator => {
                Instruction::new(mnemonic::LSR, addressing_mode::Accumulator).into()
            }
            InstructionVariant::LSRZeroPage(am) => {
                Instruction::new(mnemonic::LSR, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::LSRZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::LSR, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::NOPImplied => {
                Instruction::new(mnemonic::NOP, addressing_mode::Implied).into()
            }
            InstructionVariant::ORAAbsolute(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::ORAAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::ORAAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::ORAIndirectYIndexed(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::ORAImmediate(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::ORAXIndexedIndirect(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::ORAZeroPage(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::ORAZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::ORA, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::PHAImplied => {
                Instruction::new(mnemonic::PHA, addressing_mode::Implied).into()
            }
            InstructionVariant::PHPImplied => {
                Instruction::new(mnemonic::PHP, addressing_mode::Implied).into()
            }
            InstructionVariant::PLAImplied => {
                Instruction::new(mnemonic::PLA, addressing_mode::Implied).into()
            }
            InstructionVariant::PLPImplied => {
                Instruction::new(mnemonic::PLP, addressing_mode::Implied).into()
            }
            InstructionVariant::ROLAbsolute(am) => {
                Instruction::new(mnemonic::ROL, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::ROLAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::ROL, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::ROLAccumulator => {
                Instruction::new(mnemonic::ROL, addressing_mode::Accumulator).into()
            }
            InstructionVariant::ROLZeroPage(am) => {
                Instruction::new(mnemonic::ROL, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::ROLZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::ROL, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::RORAbsolute(am) => {
                Instruction::new(mnemonic::ROR, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::RORAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::ROR, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::RORAccumulator => {
                Instruction::new(mnemonic::ROR, addressing_mode::Accumulator).into()
            }
            InstructionVariant::RORZeroPage(am) => {
                Instruction::new(mnemonic::ROR, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::RORZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::ROR, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::RTIImplied => {
                Instruction::new(mnemonic::RTI, addressing_mode::Implied).into()
            }
            InstructionVariant::RTSImplied => {
                Instruction::new(mnemonic::RTS, addressing_mode::Implied).into()
            }
            InstructionVariant::SBCAbsolute(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::SBCAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::SBCAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::SBCIndirectYIndexed(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::SBCImmediate(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::Immediate(am)).into()
            }
            InstructionVariant::SBCXIndexedIndirect(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::SBCZeroPage(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::SBCZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::SBC, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::STAAbsolute(am) => {
                Instruction::new(mnemonic::STA, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::STAAbsoluteIndexedWithX(am) => {
                Instruction::new(mnemonic::STA, addressing_mode::AbsoluteIndexedWithX(am)).into()
            }
            InstructionVariant::STAAbsoluteIndexedWithY(am) => {
                Instruction::new(mnemonic::STA, addressing_mode::AbsoluteIndexedWithY(am)).into()
            }
            InstructionVariant::STAIndirectYIndexed(am) => {
                Instruction::new(mnemonic::STA, addressing_mode::IndirectYIndexed(am)).into()
            }
            InstructionVariant::STAXIndexedIndirect(am) => {
                Instruction::new(mnemonic::STA, addressing_mode::XIndexedIndirect(am)).into()
            }
            InstructionVariant::STAZeroPage(am) => {
                Instruction::new(mnemonic::STA, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::STAZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::STA, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::STXAbsolute(am) => {
                Instruction::new(mnemonic::STX, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::STXZeroPage(am) => {
                Instruction::new(mnemonic::STX, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::STXZeroPageIndexedWithY(am) => {
                Instruction::new(mnemonic::STX, addressing_mode::ZeroPageIndexedWithY(am)).into()
            }
            InstructionVariant::STYAbsolute(am) => {
                Instruction::new(mnemonic::STY, addressing_mode::Absolute(am)).into()
            }
            InstructionVariant::STYZeroPage(am) => {
                Instruction::new(mnemonic::STY, addressing_mode::ZeroPage(am)).into()
            }
            InstructionVariant::STYZeroPageIndexedWithX(am) => {
                Instruction::new(mnemonic::STY, addressing_mode::ZeroPageIndexedWithX(am)).into()
            }
            InstructionVariant::SECImplied => {
                Instruction::new(mnemonic::SEC, addressing_mode::Implied).into()
            }
            InstructionVariant::SEDImplied => {
                Instruction::new(mnemonic::SED, addressing_mode::Implied).into()
            }
            InstructionVariant::SEIImplied => {
                Instruction::new(mnemonic::SEI, addressing_mode::Implied).into()
            }
            InstructionVariant::TAXImplied => {
                Instruction::new(mnemonic::TAX, addressing_mode::Implied).into()
            }
            InstructionVariant::TAYImplied => {
                Instruction::new(mnemonic::TAY, addressing_mode::Implied).into()
            }
            InstructionVariant::TSXImplied => {
                Instruction::new(mnemonic::TSX, addressing_mode::Implied).into()
            }
            InstructionVariant::TXAImplied => {
                Instruction::new(mnemonic::TXA, addressing_mode::Implied).into()
            }
            InstructionVariant::TXSImplied => {
                Instruction::new(mnemonic::TXS, addressing_mode::Implied).into()
            }
            InstructionVariant::TYAImplied => {
                Instruction::new(mnemonic::TYA, addressing_mode::Implied).into()
            }
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
            (Mnemonic::ADC, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::ADCAbsolute(am))
            }
            (Mnemonic::ADC, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::ADCAbsoluteIndexedWithX(am))
            }
            (Mnemonic::ADC, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::ADCAbsoluteIndexedWithY(am))
            }
            (Mnemonic::ADC, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::ADCIndirectYIndexed(am))
            }
            (Mnemonic::ADC, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::ADCImmediate(am))
            }
            (Mnemonic::ADC, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::ADCXIndexedIndirect(am))
            }
            (Mnemonic::ADC, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::ADCZeroPage(am))
            }
            (Mnemonic::ADC, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::ADCZeroPageIndexedWithX(am))
            }
            (Mnemonic::AND, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::ANDAbsolute(am))
            }
            (Mnemonic::AND, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::ANDAbsoluteIndexedWithX(am))
            }
            (Mnemonic::AND, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::ANDAbsoluteIndexedWithY(am))
            }
            (Mnemonic::AND, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::ANDIndirectYIndexed(am))
            }
            (Mnemonic::AND, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::ANDImmediate(am))
            }
            (Mnemonic::AND, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::ANDXIndexedIndirect(am))
            }
            (Mnemonic::AND, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::ANDZeroPage(am))
            }
            (Mnemonic::AND, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::ANDZeroPageIndexedWithX(am))
            }
            (Mnemonic::ASL, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::ASLAbsolute(am))
            }
            (Mnemonic::ASL, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::ASLAbsoluteIndexedWithX(am))
            }
            (Mnemonic::ASL, AddressingMode::Accumulator) => Ok(InstructionVariant::ASLAccumulator),
            (Mnemonic::ASL, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::ASLZeroPage(am))
            }
            (Mnemonic::ASL, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::ASLZeroPageIndexedWithX(am))
            }
            (Mnemonic::BCC, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BCCRelative(am))
            }
            (Mnemonic::BCS, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BCSRelative(am))
            }
            (Mnemonic::BEQ, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BEQRelative(am))
            }
            (Mnemonic::BMI, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BMIRelative(am))
            }
            (Mnemonic::BIT, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::BITAbsolute(am))
            }
            (Mnemonic::BIT, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::BITZeroPage(am))
            }
            (Mnemonic::BNE, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BNERelative(am))
            }
            (Mnemonic::BPL, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BPLRelative(am))
            }
            (Mnemonic::BRK, AddressingMode::Implied) => Ok(InstructionVariant::BRKImplied),
            (Mnemonic::BVC, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BVCRelative(am))
            }
            (Mnemonic::BVS, AddressingMode::Relative(am)) => {
                Ok(InstructionVariant::BVSRelative(am))
            }
            (Mnemonic::CLC, AddressingMode::Implied) => Ok(InstructionVariant::CLCImplied),
            (Mnemonic::CLD, AddressingMode::Implied) => Ok(InstructionVariant::CLDImplied),
            (Mnemonic::CLI, AddressingMode::Implied) => Ok(InstructionVariant::CLIImplied),
            (Mnemonic::CLV, AddressingMode::Implied) => Ok(InstructionVariant::CLVImplied),
            (Mnemonic::CMP, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::CMPAbsolute(am))
            }
            (Mnemonic::CMP, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::CMPAbsoluteIndexedWithX(am))
            }
            (Mnemonic::CMP, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::CMPAbsoluteIndexedWithY(am))
            }
            (Mnemonic::CMP, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::CMPIndirectYIndexed(am))
            }
            (Mnemonic::CMP, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::CMPImmediate(am))
            }
            (Mnemonic::CMP, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::CMPXIndexedIndirect(am))
            }
            (Mnemonic::CMP, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::CMPZeroPage(am))
            }
            (Mnemonic::CMP, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::CMPZeroPageIndexedWithX(am))
            }
            (Mnemonic::CPX, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::CPXAbsolute(am))
            }
            (Mnemonic::CPX, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::CPXImmediate(am))
            }
            (Mnemonic::CPX, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::CPXZeroPage(am))
            }
            (Mnemonic::CPY, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::CPYAbsolute(am))
            }
            (Mnemonic::CPY, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::CPYImmediate(am))
            }
            (Mnemonic::CPY, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::CPYZeroPage(am))
            }
            (Mnemonic::DEC, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::DECAbsolute(am))
            }
            (Mnemonic::DEC, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::DECAbsoluteIndexedWithX(am))
            }
            (Mnemonic::DEC, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::DECZeroPage(am))
            }
            (Mnemonic::DEC, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::DECZeroPageIndexedWithX(am))
            }
            (Mnemonic::DEX, AddressingMode::Implied) => Ok(InstructionVariant::DEXImplied),
            (Mnemonic::DEY, AddressingMode::Implied) => Ok(InstructionVariant::DEYImplied),
            (Mnemonic::EOR, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::EORAbsolute(am))
            }
            (Mnemonic::EOR, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::EORAbsoluteIndexedWithX(am))
            }
            (Mnemonic::EOR, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::EORAbsoluteIndexedWithY(am))
            }
            (Mnemonic::EOR, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::EORIndirectYIndexed(am))
            }
            (Mnemonic::EOR, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::EORImmediate(am))
            }
            (Mnemonic::EOR, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::EORXIndexedIndirect(am))
            }
            (Mnemonic::EOR, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::EORZeroPage(am))
            }
            (Mnemonic::EOR, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::EORZeroPageIndexedWithX(am))
            }
            (Mnemonic::INC, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::INCAbsolute(am))
            }
            (Mnemonic::INC, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::INCAbsoluteIndexedWithX(am))
            }
            (Mnemonic::INC, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::INCZeroPage(am))
            }
            (Mnemonic::INC, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::INCZeroPageIndexedWithX(am))
            }
            (Mnemonic::INX, AddressingMode::Implied) => Ok(InstructionVariant::INXImplied),
            (Mnemonic::INY, AddressingMode::Implied) => Ok(InstructionVariant::INYImplied),
            (Mnemonic::JMP, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::JMPAbsolute(am))
            }
            (Mnemonic::JMP, AddressingMode::Indirect(am)) => {
                Ok(InstructionVariant::JMPIndirect(am))
            }
            (Mnemonic::JSR, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::JSRAbsolute(am))
            }
            (Mnemonic::LDA, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LDAAbsolute(am))
            }
            (Mnemonic::LDA, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::LDAAbsoluteIndexedWithX(am))
            }
            (Mnemonic::LDA, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::LDAAbsoluteIndexedWithY(am))
            }
            (Mnemonic::LDA, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::LDAIndirectYIndexed(am))
            }
            (Mnemonic::LDA, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::LDAImmediate(am))
            }
            (Mnemonic::LDA, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::LDAXIndexedIndirect(am))
            }
            (Mnemonic::LDA, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LDAZeroPage(am))
            }
            (Mnemonic::LDA, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::LDAZeroPageIndexedWithX(am))
            }
            (Mnemonic::LDX, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LDXAbsolute(am))
            }
            (Mnemonic::LDX, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::LDXAbsoluteIndexedWithY(am))
            }
            (Mnemonic::LDX, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::LDXImmediate(am))
            }
            (Mnemonic::LDX, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LDXZeroPage(am))
            }
            (Mnemonic::LDX, AddressingMode::ZeroPageIndexedWithY(am)) => {
                Ok(InstructionVariant::LDXZeroPageIndexedWithY(am))
            }
            (Mnemonic::LDY, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LDYAbsolute(am))
            }
            (Mnemonic::LDY, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::LDYAbsoluteIndexedWithX(am))
            }
            (Mnemonic::LDY, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::LDYImmediate(am))
            }
            (Mnemonic::LDY, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LDYZeroPage(am))
            }
            (Mnemonic::LDY, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::LDYZeroPageIndexedWithX(am))
            }
            (Mnemonic::LSR, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::LSRAbsolute(am))
            }
            (Mnemonic::LSR, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::LSRAbsoluteIndexedWithX(am))
            }
            (Mnemonic::LSR, AddressingMode::Accumulator) => Ok(InstructionVariant::LSRAccumulator),
            (Mnemonic::LSR, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::LSRZeroPage(am))
            }
            (Mnemonic::LSR, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::LSRZeroPageIndexedWithX(am))
            }
            (Mnemonic::NOP, AddressingMode::Implied) => Ok(InstructionVariant::NOPImplied),
            (Mnemonic::ORA, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::ORAAbsolute(am))
            }
            (Mnemonic::ORA, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::ORAAbsoluteIndexedWithX(am))
            }
            (Mnemonic::ORA, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::ORAAbsoluteIndexedWithY(am))
            }
            (Mnemonic::ORA, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::ORAIndirectYIndexed(am))
            }
            (Mnemonic::ORA, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::ORAImmediate(am))
            }
            (Mnemonic::ORA, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::ORAXIndexedIndirect(am))
            }
            (Mnemonic::ORA, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::ORAZeroPage(am))
            }
            (Mnemonic::ORA, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::ORAZeroPageIndexedWithX(am))
            }
            (Mnemonic::PHA, AddressingMode::Implied) => Ok(InstructionVariant::PHAImplied),
            (Mnemonic::PHP, AddressingMode::Implied) => Ok(InstructionVariant::PHPImplied),
            (Mnemonic::PLA, AddressingMode::Implied) => Ok(InstructionVariant::PLAImplied),
            (Mnemonic::PLP, AddressingMode::Implied) => Ok(InstructionVariant::PLPImplied),
            (Mnemonic::ROL, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::ROLAbsolute(am))
            }
            (Mnemonic::ROL, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::ROLAbsoluteIndexedWithX(am))
            }
            (Mnemonic::ROL, AddressingMode::Accumulator) => Ok(InstructionVariant::ROLAccumulator),
            (Mnemonic::ROL, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::ROLZeroPage(am))
            }
            (Mnemonic::ROL, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::ROLZeroPageIndexedWithX(am))
            }
            (Mnemonic::ROR, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::RORAbsolute(am))
            }
            (Mnemonic::ROR, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::RORAbsoluteIndexedWithX(am))
            }
            (Mnemonic::ROR, AddressingMode::Accumulator) => Ok(InstructionVariant::RORAccumulator),
            (Mnemonic::ROR, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::RORZeroPage(am))
            }
            (Mnemonic::ROR, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::RORZeroPageIndexedWithX(am))
            }
            (Mnemonic::RTI, AddressingMode::Implied) => Ok(InstructionVariant::RTIImplied),
            (Mnemonic::RTS, AddressingMode::Implied) => Ok(InstructionVariant::RTSImplied),

            (Mnemonic::SBC, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::SBCAbsolute(am))
            }
            (Mnemonic::SBC, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::SBCAbsoluteIndexedWithX(am))
            }
            (Mnemonic::SBC, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::SBCAbsoluteIndexedWithY(am))
            }
            (Mnemonic::SBC, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::SBCIndirectYIndexed(am))
            }
            (Mnemonic::SBC, AddressingMode::Immediate(am)) => {
                Ok(InstructionVariant::SBCImmediate(am))
            }
            (Mnemonic::SBC, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::SBCXIndexedIndirect(am))
            }
            (Mnemonic::SBC, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::SBCZeroPage(am))
            }
            (Mnemonic::SBC, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::SBCZeroPageIndexedWithX(am))
            }
            (Mnemonic::STA, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::STAAbsolute(am))
            }
            (Mnemonic::STA, AddressingMode::AbsoluteIndexedWithX(am)) => {
                Ok(InstructionVariant::STAAbsoluteIndexedWithX(am))
            }
            (Mnemonic::STA, AddressingMode::AbsoluteIndexedWithY(am)) => {
                Ok(InstructionVariant::STAAbsoluteIndexedWithY(am))
            }
            (Mnemonic::STA, AddressingMode::IndirectYIndexed(am)) => {
                Ok(InstructionVariant::STAIndirectYIndexed(am))
            }
            (Mnemonic::STA, AddressingMode::XIndexedIndirect(am)) => {
                Ok(InstructionVariant::STAXIndexedIndirect(am))
            }
            (Mnemonic::STA, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::STAZeroPage(am))
            }
            (Mnemonic::STA, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::STAZeroPageIndexedWithX(am))
            }
            (Mnemonic::STX, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::STXAbsolute(am))
            }
            (Mnemonic::STX, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::STXZeroPage(am))
            }
            (Mnemonic::STX, AddressingMode::ZeroPageIndexedWithY(am)) => {
                Ok(InstructionVariant::STXZeroPageIndexedWithY(am))
            }
            (Mnemonic::STY, AddressingMode::Absolute(am)) => {
                Ok(InstructionVariant::STYAbsolute(am))
            }
            (Mnemonic::STY, AddressingMode::ZeroPage(am)) => {
                Ok(InstructionVariant::STYZeroPage(am))
            }
            (Mnemonic::STY, AddressingMode::ZeroPageIndexedWithX(am)) => {
                Ok(InstructionVariant::STYZeroPageIndexedWithX(am))
            }
            (Mnemonic::SEC, AddressingMode::Implied) => Ok(InstructionVariant::SECImplied),
            (Mnemonic::SED, AddressingMode::Implied) => Ok(InstructionVariant::SEDImplied),
            (Mnemonic::SEI, AddressingMode::Implied) => Ok(InstructionVariant::SEIImplied),
            (Mnemonic::TAX, AddressingMode::Implied) => Ok(InstructionVariant::TAXImplied),
            (Mnemonic::TAY, AddressingMode::Implied) => Ok(InstructionVariant::TAYImplied),
            (Mnemonic::TSX, AddressingMode::Implied) => Ok(InstructionVariant::TSXImplied),
            (Mnemonic::TXA, AddressingMode::Implied) => Ok(InstructionVariant::TXAImplied),
            (Mnemonic::TXS, AddressingMode::Implied) => Ok(InstructionVariant::TXSImplied),
            (Mnemonic::TYA, AddressingMode::Implied) => Ok(InstructionVariant::TYAImplied),
            _ => Err(InstructionErr::InvalidInstruction(src.0, src.1.into())),
        }
    }
}
