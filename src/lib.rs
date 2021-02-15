//! This crate stores helper types for all mnemonics and addressing modes for
//! the MOS6502 ISA. In addition, these types provide helpers for the
//! translation between the bytecode and an intermediate representation of the
//! instruction set.

use std::fmt::Debug;

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
            > for InstructionVariations
        {
            fn from(
                _: $crate::Instruction<
                    $crate::mnemonic::$mnemonic,
                    $crate::addressing_mode::Implied,
                >,
            ) -> Self {
                $crate::InstructionVariations::$variant
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
            > for InstructionVariations
        {
            fn from(
                _: $crate::Instruction<
                    $crate::mnemonic::$mnemonic,
                    $crate::addressing_mode::Accumulator,
                >,
            ) -> Self {
                $crate::InstructionVariations::$variant
            }
        }
    };
    ($mnemonic:tt, $am:tt, NOPImplied) => {
        impl
            std::convert::From<
                $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::$am>,
            > for InstructionVariations
        {
            fn from(
                _src: $crate::Instruction<
                    $crate::mnemonic::$mnemonic,
                    $crate::addressing_mode::$am,
                >,
            ) -> Self {
                $crate::InstructionVariations::NOPImplied
            }
        }
    };
    ($mnemonic:tt, $am:tt, $variant:tt) => {
        impl
            std::convert::From<
                $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::$am>,
            > for InstructionVariations
        {
            fn from(
                src: $crate::Instruction<$crate::mnemonic::$mnemonic, $crate::addressing_mode::$am>,
            ) -> Self {
                $crate::InstructionVariations::$variant(src.addressing_mode.unwrap())
            }
        }
    };
}

macro_rules! generate_instructions {
    ($($name:ident: $mnc:tt, $am:tt, $variant:tt, $opcode:expr, $cycles:expr,)*) => {

        // For each valid Instruction<Mnemonic, Addressing Mode> pairing
        $(
            impl $crate::CycleCost for Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am> {
                fn cycles(&self) -> usize {
                    $cycles
                }
            }

            impl<'a> parcel::Parser<'a, &'a [u8], Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>>
                for crate::Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>
            {
                fn parse(
                    &self,
                    input: &'a [u8],
                ) -> parcel::ParseResult<&'a [u8], Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>> {
                    // If the expected opcode and addressing mode match, map it to a
                    // corresponding Instruction.
                    parcel::map(
                        parcel::and_then(parcel::parsers::byte::expect_byte($opcode), |_| <$crate::addressing_mode::$am>::default()),
                        |am| Instruction::new(<$crate::mnemonic::$mnc>::default(), am),
                    )
                    .parse(input)
                }
            }

            // Covert the addressing mode contests to a little-endian bytecode
            // vector and chain that to a vector containing the instructions
            // opcode.
            impl std::convert::From<Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>> for Bytecode {
                fn from(src: Instruction<$crate::mnemonic::$mnc, $crate::addressing_mode::$am>) -> Self {
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
    adc_zeropage_indexed_with_x: ADC, ZeroPageIndexedWithX, NOPImplied, 0x75, 4,
    sbc_absolute: SBC, Absolute, NOPImplied, 0xed, 4,
    sbc_absolute_indexed_with_x: SBC, AbsoluteIndexedWithX, NOPImplied, 0xfd, 4,
    sbc_absolute_indexed_with_y: SBC, AbsoluteIndexedWithY, NOPImplied, 0xf9, 4,
    sbc_indirect_y_indexed: SBC, IndirectYIndexed, NOPImplied, 0xf1, 5,
    sbc_immediate: SBC, Immediate, NOPImplied, 0xe9, 2,
    sbc_x_indexed_indirect: SBC, XIndexedIndirect, NOPImplied, 0xe1, 6,
    sbc_zeropage: SBC, ZeroPage, NOPImplied, 0xe5, 3,
    sbc_zeropage_indexed_with_x: SBC, ZeroPageIndexedWithX, NOPImplied, 0xf5, 4,
    and_absolute: AND, Absolute, NOPImplied, 0x2d, 4,
    and_absolute_indexed_with_x: AND, AbsoluteIndexedWithX, NOPImplied, 0x3d, 4,
    and_absolute_indexed_with_y: AND, AbsoluteIndexedWithY, NOPImplied, 0x39, 4,
    and_indirect_y_indexed: AND, IndirectYIndexed, NOPImplied, 0x31, 5,
    and_immediate: AND, Immediate, NOPImplied, 0x29, 2,
    and_x_indexed_indirect: AND, XIndexedIndirect, NOPImplied, 0x21, 6,
    and_zeropage: AND, ZeroPage, NOPImplied, 0x25, 3,
    and_zeropage_indxed_with_x: AND, ZeroPageIndexedWithX, NOPImplied, 0x35, 4,
    asl_absolute: ASL, Absolute, NOPImplied, 0x0e, 6,
    asl_absolute_indexed_with_x: ASL, AbsoluteIndexedWithX, NOPImplied, 0x1e, 7,
    asl_accumulator: ASL, Accumulator, NOPImplied, 0x0a, 2,
    asl_zeropage: ASL, ZeroPage, NOPImplied, 0x06, 5,
    asl_zeropage_indexed_with_x: ASL, ZeroPageIndexedWithX, NOPImplied, 0x16, 6,
    bit_absolute: BIT, Absolute, NOPImplied, 0x2c, 4,
    bit_zeropage: BIT, ZeroPage, NOPImplied, 0x24, 3,
    eor_absolute: EOR, Absolute, NOPImplied, 0x4d, 4,
    eor_absolute_indexed_with_x: EOR, AbsoluteIndexedWithX, NOPImplied, 0x5d, 4,
    eor_absolute_indexed_with_y: EOR, AbsoluteIndexedWithY, NOPImplied, 0x59, 4,
    eor_indirect_y_indexed: EOR, IndirectYIndexed, NOPImplied, 0x51, 5,
    eor_immediate: EOR, Immediate, NOPImplied, 0x49, 2,
    eor_x_indexed_indirect: EOR, XIndexedIndirect, NOPImplied, 0x41, 6,
    eor_zeropage: EOR, ZeroPage, NOPImplied, 0x45, 3,
    eor_zeropage_indexed_with_x: EOR, ZeroPageIndexedWithX, NOPImplied, 0x55, 4,
    lsr_absolute: LSR, Absolute, NOPImplied, 0x4e, 6,
    lsr_absolute_indexed_with_x: LSR, AbsoluteIndexedWithX, NOPImplied, 0x5e, 7,
    lsr_accumulator: LSR, Accumulator, NOPImplied, 0x4a, 2,
    lsr_zeropage: LSR, ZeroPage, NOPImplied, 0x46, 5,
    lsr_zeropage_indexed_with_x: LSR, ZeroPageIndexedWithX, NOPImplied, 0x56, 6,
    ora_absolute: ORA, Absolute, NOPImplied, 0x0d, 4,
    ora_absolute_indexed_with_x: ORA, AbsoluteIndexedWithX, NOPImplied, 0x1d, 4,
    ora_absolute_indexed_with_y: ORA, AbsoluteIndexedWithY, NOPImplied, 0x19, 4,
    ora_indirect_y_indexed: ORA, IndirectYIndexed, NOPImplied, 0x11, 5,
    ora_immediate: ORA, Immediate, NOPImplied, 0x09, 2,
    ora_x_indexed_indirect: ORA, XIndexedIndirect, NOPImplied, 0x01, 6,
    ora_zeroapage: ORA, ZeroPage, NOPImplied, 0x05, 3,
    ora_zeropage_indexed_with_x: ORA, ZeroPageIndexedWithX, NOPImplied, 0x15, 4,
    rol_absolute: ROL, Absolute, NOPImplied, 0x2e, 6,
    rol_absolute_indexed_with_x: ROL, AbsoluteIndexedWithX, NOPImplied, 0x3e, 7,
    rol_accumulator: ROL, Accumulator, NOPImplied, 0x2a, 2,
    rol_zeropage: ROL, ZeroPage, NOPImplied, 0x26, 5,
    rol_zeropage_indexed_with_x: ROL, ZeroPageIndexedWithX, NOPImplied, 0x36, 6,
    ror_absolute: ROR, Absolute, NOPImplied, 0x6e, 6,
    ror_absolute_indexed_with_x: ROR, AbsoluteIndexedWithX, NOPImplied, 0x7e, 7,
    ror_acumulator: ROR, Accumulator, NOPImplied, 0x6a, 2,
    ror_zeropage: ROR, ZeroPage, NOPImplied, 0x66, 5,
    ror_zeropage_indexed_with_x: ROR, ZeroPageIndexedWithX, NOPImplied, 0x76, 6,
    bcc_relative: BCC, Relative, NOPImplied, 0x90, 2,
    bcs_relative: BCS, Relative, NOPImplied, 0xb0, 2,
    beq_relative: BEQ, Relative, NOPImplied, 0xf0, 2,
    bmi_relative: BMI, Relative, NOPImplied, 0x30, 2,
    bne_relative: BNE, Relative, NOPImplied, 0xd0, 2,
    bpl_relative: BPL, Relative, NOPImplied, 0x10, 2,
    bvc_relative: BVC, Relative, NOPImplied, 0x50, 2,
    bvs_relative: BVS, Relative, NOPImplied, 0x70, 2,
    clc_implied: CLC, Implied, NOPImplied, 0x18, 2,
    cld_implied: CLD, Implied, NOPImplied, 0xd8, 2,
    cli_implied: CLI, Implied, NOPImplied, 0x58, 2,
    clv_implied: CLV, Implied, NOPImplied, 0xb8, 2,
    cmp_absolute: CMP, Absolute, NOPImplied, 0xcd, 4,
    cmp_absolute_indexed_with_x: CMP, AbsoluteIndexedWithX, NOPImplied, 0xdd, 4,
    cmp_absolute_indexed_with_y: CMP, AbsoluteIndexedWithY, NOPImplied, 0xd9, 4,
    cmp_indirect_y_indexed: CMP, IndirectYIndexed, NOPImplied, 0xd1, 5,
    cmp_immediate: CMP, Immediate, NOPImplied, 0xc9, 2,
    cmp_x_indexed_indirect: CMP, XIndexedIndirect, NOPImplied, 0xc1, 6,
    cmp_zeropage: CMP, ZeroPage, NOPImplied, 0xc5, 3,
    cmp_zeropage_indexexd_with_x: CMP, ZeroPageIndexedWithX, NOPImplied, 0xd5, 4,
    cpx_absolute: CPX, Absolute, NOPImplied, 0xec, 4,
    cpx_immediate: CPX, Immediate, NOPImplied, 0xe0, 2,
    cpx_zeroage: CPX, ZeroPage, NOPImplied, 0xe4, 3,
    cpy_absolute: CPY, Absolute, NOPImplied, 0xcc, 4,
    cpy_immediate: CPY, Immediate, NOPImplied, 0xc0, 2,
    cpy_zeropage: CPY, ZeroPage, NOPImplied, 0xc4, 3,
    dec_absolute: DEC, Absolute, NOPImplied, 0xce, 6,
    dec_absolute_indexed_with_x: DEC, AbsoluteIndexedWithX, NOPImplied, 0xde, 7,
    dec_zeropage: DEC, ZeroPage, NOPImplied, 0xc6, 5,
    dec_zeropage_indexed_with_x: DEC, ZeroPageIndexedWithX, NOPImplied, 0xd6, 6,
    dex_implied: DEX, Implied, NOPImplied, 0xca, 2,
    dey_implied: DEY, Implied, NOPImplied, 0x88, 2,
    inc_absolute: INC, Absolute, NOPImplied, 0xee, 6,
    inc_absolute_indexed_with_x: INC, AbsoluteIndexedWithX, NOPImplied, 0xfe, 7,
    inc_zeropage: INC, ZeroPage, NOPImplied, 0xe6, 5,
    inc_zeropage_indexed_with_x: INC, ZeroPageIndexedWithX, NOPImplied, 0xf6, 6,
    inx_implied: INX, Implied, NOPImplied, 0xe8, 2,
    iny_implied: INY, Implied, NOPImplied, 0xc8, 2,
    jmp_absolute: JMP, Absolute, NOPImplied, 0x4c, 3,
    jmp_indirect: JMP, Indirect, NOPImplied, 0x6c, 5,
    jsr_absolute: JSR, Absolute, NOPImplied, 0x20, 6,
    lda_immediate: LDA, Immediate, NOPImplied, 0xa9, 2,
    lda_zeropage: LDA, ZeroPage, NOPImplied, 0xa5, 3,
    lda_zeropage_indexed_with_x: LDA, ZeroPageIndexedWithX, NOPImplied, 0xb5, 4,
    lda_absolute: LDA, Absolute, NOPImplied, 0xad, 4,
    lda_absolute_indexed_with_x: LDA, AbsoluteIndexedWithX, NOPImplied, 0xbd, 4,
    lda_absolute_indexed_with_y: LDA, AbsoluteIndexedWithY, NOPImplied, 0xb9, 4,
    lda_indirect_y_indexed: LDA, IndirectYIndexed, NOPImplied, 0xb1, 5,
    lda_x_indexed_indirect: LDA, XIndexedIndirect, NOPImplied, 0xa1, 6,
    ldx_absolute: LDX, Absolute, NOPImplied, 0xae, 4,
    ldx_absolute_indexed_with_y: LDX, AbsoluteIndexedWithY, NOPImplied, 0xbe, 4,
    ldx_immediate: LDX, Immediate, NOPImplied, 0xa2, 2,
    ldx_zeropage: LDX, ZeroPage, NOPImplied, 0xa6, 3,
    ldx_zeropage_indexed_with_y: LDX, ZeroPageIndexedWithY, NOPImplied, 0xb6, 4,
    ldy_absolute: LDY, Absolute, NOPImplied, 0xac, 4,
    ldy_absolute_indexed_with_x: LDY, AbsoluteIndexedWithX, NOPImplied, 0xbc, 4,
    ldy_immediate: LDY, Immediate, NOPImplied, 0xa0, 2,
    ldy_zeropage: LDY, ZeroPage, NOPImplied, 0xa4, 3,
    ldy_zeropage_indexed_with_x: LDY, ZeroPageIndexedWithX, NOPImplied, 0xb4, 4,
    pha_implied: PHA, Implied, NOPImplied, 0x48, 3,
    php_implied: PHP, Implied, NOPImplied, 0x08, 3,
    pla_implied: PLA, Implied, NOPImplied, 0x68, 4,
    plp_implied: PLP, Implied, NOPImplied, 0x28, 4,
    rti_implied: RTI, Implied, NOPImplied, 0x40, 6,
    rts_implied: RTS, Implied, NOPImplied, 0x60, 6,
    sec_implied: SEC, Implied, NOPImplied, 0x38, 2,
    sed_implied: SED, Implied, NOPImplied, 0xf8, 2,
    sei_implied: SEI, Implied, NOPImplied, 0x78, 2,
    sta_absolute: STA, Absolute, NOPImplied, 0x8d, 4,
    sta_absolute_indexed_with_x: STA, AbsoluteIndexedWithX, NOPImplied, 0x9d, 5,
    sta_absolute_indexed_with_y: STA, AbsoluteIndexedWithY, NOPImplied, 0x99, 5,
    sta_indirect_y_indexed: STA, IndirectYIndexed, NOPImplied, 0x91, 6,
    sta_x_indexed_indirect: STA, XIndexedIndirect, NOPImplied, 0x81, 6,
    sta_zeropage: STA, ZeroPage, NOPImplied, 0x85, 3,
    sta_zeropage_indexed_with_x: STA, ZeroPageIndexedWithX, NOPImplied, 0x95, 4,
    stx_absolute: STX, Absolute, NOPImplied, 0x8e, 4,
    stx_zeropage: STX, ZeroPage, NOPImplied, 0x86, 3,
    stx_zeropage_indexed_with_y: STX, ZeroPageIndexedWithY, NOPImplied, 0x96, 4,
    sty_absolute: STY, Absolute, NOPImplied, 0x8c, 4,
    sty_zeropage: STY, ZeroPage, NOPImplied, 0x84, 3,
    sty_zeropage_indexed_with_x: STY, ZeroPageIndexedWithX, NOPImplied, 0x94, 4,
    tax_implied: TAX, Implied, NOPImplied, 0xaa, 2,
    tay_implied: TAY, Implied, NOPImplied, 0xa8, 2,
    tsx_implied: TSX, Implied, NOPImplied, 0xba, 2,
    txa_implied: TXA, Implied, NOPImplied, 0x8a, 2,
    txs_implied: TXS, Implied, NOPImplied, 0x9a, 2,
    tya_implied: TYA, Implied, NOPImplied, 0x98, 2,
    brk_implied: BRK, Implied, NOPImplied, 0x00, 7,
    nop_implied: NOP, Implied, NOPImplied, 0xea, 2,
);

/// InstructionVariations functions as a concrete implementations of the generic
/// instruction types for use when runtime.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InstructionVariations {
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
