//! This crate stores helper types for all mnemonics and addressing modes for
//! the MOS6502 ISA. In addition, these types provide helpers for the
//! translation between the bytecode and an intermediate representation of the
//! instruction set.

use std::fmt::Debug;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InstructionErr {
    ConversionErr,
}

impl std::fmt::Display for InstructionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConversionErr => write!(f, "invalid conversion"),
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
                            $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <crate::addressing_mode::$am>::default()),
                            $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <crate::addressing_mode::$am>::default()).parse(&bytecode).unwrap().unwrap()
                        )
                    }
                )*
            }

            mod bytecode {
                $(
                    #[test]
                    fn $name() {
                        let mut bytecode = $crate::Instruction::new(<$crate::mnemonic::$mnc>::default(), <crate::addressing_mode::$am>::default()).into_iter();
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
