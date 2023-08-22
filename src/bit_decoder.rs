#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Opcode(u8);

impl Opcode {
    pub fn to_u8(self) -> u8 {
        self.0
    }

    pub const fn a_bits(&self) -> u8 {
        (self.0 >> 5) & 0x07
    }

    pub const fn b_bits(&self) -> u8 {
        (self.0 >> 2) & 0x07
    }

    pub const fn c_bits(&self) -> u8 {
        self.0 & 0x03
    }

    pub fn to_bit_types(&self) -> [u8; 3] {
        [self.a_bits(), self.b_bits(), self.c_bits()]
    }

    const fn to_a_type(self) -> AType {
        match self.a_bits() {
            0 => AType::Zero,
            1 => AType::One,
            2 => AType::Two,
            3 => AType::Three,
            4 => AType::Four,
            5 => AType::Five,
            6 => AType::Six,
            7 => AType::Seven,
            // The value returned from [to_a_bits] will never be larger than a
            // 3-bit value.
            _ => unreachable!(),
        }
    }

    const fn to_b_type(self) -> BType {
        match self.b_bits() {
            0 => BType::Zero,
            1 => BType::One,
            2 => BType::Two,
            3 => BType::Three,
            4 => BType::Four,
            5 => BType::Five,
            6 => BType::Six,
            7 => BType::Seven,
            // The value returned from [to_b_bits] will never be larger than a
            // 3-bit value.
            _ => unreachable!(),
        }
    }

    const fn to_c_type(self) -> CType {
        match self.c_bits() {
            0 => CType::Zero,
            1 => CType::One,
            2 => CType::Two,
            // The value returned from [to_c_bits] will never be larger than a
            // 2-bit value with the last value being unused.
            _ => unreachable!(),
        }
    }
}

impl From<u8> for Opcode {
    fn from(value: u8) -> Self {
        Self(value)
    }
}

#[derive(Debug, Clone, Copy)]
enum AType {
    Zero,
    One,
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
}

#[derive(Debug, Clone, Copy)]
enum BType {
    Zero,
    One,
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
}

#[derive(Debug, Clone, Copy)]
enum CType {
    Zero,
    One,
    Two,
}

const fn mnemonic_from_opcode(opcode: &Opcode) -> Option<crate::mnemonic::Mnemonic> {
    use crate::mnemonic::Mnemonic;

    // Check for exceptions to the bit patterned rules
    let exception = match opcode.0 {
        // branching
        0x10 => Some(Mnemonic::Bpl),
        0x30 => Some(Mnemonic::Bmi),
        0x50 => Some(Mnemonic::Bvc),
        0x70 => Some(Mnemonic::Bvs),
        0x90 => Some(Mnemonic::Bcc),
        0xB0 => Some(Mnemonic::Bcs),
        0xD0 => Some(Mnemonic::Bne),
        0xF0 => Some(Mnemonic::Beq),

        // interrupt
        0x00 => Some(Mnemonic::Brk),
        0x20 => Some(Mnemonic::Jsr),
        0x40 => Some(Mnemonic::Rti),
        0x60 => Some(Mnemonic::Rts),

        // other
        0x08 => Some(Mnemonic::Php),
        0x28 => Some(Mnemonic::Plp),
        0x48 => Some(Mnemonic::Pha),
        0x68 => Some(Mnemonic::Pla),
        0x88 => Some(Mnemonic::Dey),
        0xA8 => Some(Mnemonic::Tay),
        0xC8 => Some(Mnemonic::Iny),
        0xE8 => Some(Mnemonic::Inx),
        0x18 => Some(Mnemonic::Clc),
        0x38 => Some(Mnemonic::Sec),
        0x58 => Some(Mnemonic::Cli),
        0x78 => Some(Mnemonic::Sei),
        0x98 => Some(Mnemonic::Tya),
        0xB8 => Some(Mnemonic::Clv),
        0xD8 => Some(Mnemonic::Cld),
        0xF8 => Some(Mnemonic::Sed),
        0x8A => Some(Mnemonic::Txa),
        0x9A => Some(Mnemonic::Txs),
        0xAA => Some(Mnemonic::Tax),
        0xBA => Some(Mnemonic::Tsx),
        0xCA => Some(Mnemonic::Dex),
        0xEA => Some(Mnemonic::Nop),

        _ => None,
    };

    if exception.is_some() {
        return exception;
    }

    let a_type = opcode.to_a_type();
    let c_type = opcode.to_c_type();

    match c_type {
        CType::Zero => match a_type {
            AType::One => Some(Mnemonic::Bit),
            AType::Two => Some(Mnemonic::Jmp),
            AType::Three => Some(Mnemonic::Jmp),
            AType::Four => Some(Mnemonic::Sty),
            AType::Five => Some(Mnemonic::Ldy),
            AType::Six => Some(Mnemonic::Cpy),
            AType::Seven => Some(Mnemonic::Cpx),
            _ => None,
        },
        CType::One => match a_type {
            AType::Zero => Some(Mnemonic::Ora),
            AType::One => Some(Mnemonic::And),
            AType::Two => Some(Mnemonic::Eor),
            AType::Three => Some(Mnemonic::Adc),
            AType::Four => Some(Mnemonic::Sta),
            AType::Five => Some(Mnemonic::Lda),
            AType::Six => Some(Mnemonic::Cmp),
            AType::Seven => Some(Mnemonic::Sbc),
        },
        CType::Two => match a_type {
            AType::Zero => Some(Mnemonic::Asl),
            AType::One => Some(Mnemonic::Rol),
            AType::Two => Some(Mnemonic::Lsr),
            AType::Three => Some(Mnemonic::Ror),
            AType::Four => Some(Mnemonic::Stx),
            AType::Five => Some(Mnemonic::Ldx),
            AType::Six => Some(Mnemonic::Dec),
            AType::Seven => Some(Mnemonic::Inc),
        },
    }
}

const fn address_mode_from_opcode(
    opcode: &Opcode,
) -> Option<crate::addressing_mode::AddressingModeType> {
    use crate::addressing_mode::AddressingModeType;

    // Check for exceptions to the bit patterned rules
    let exception = match opcode.0 {
        // branching
        0x10 | 0x30 | 0x50 | 0x70 | 0x90 | 0xB0 | 0xD0 | 0xF0 => Some(AddressingModeType::Relative),

        // interrupt
        0x20 => Some(AddressingModeType::Absolute),
        0x00 | 0x40 | 0x60 => Some(AddressingModeType::Implied),

        // other
        0x08 | 0x28 | 0x48 | 0x68 | 0x88 | 0xA8 | 0xC8 | 0xE8 | 0x18 | 0x38 | 0x58 | 0x78
        | 0x98 | 0xB8 | 0xD8 | 0xF8 | 0x8A | 0x9A | 0xAA | 0xBA | 0xCA | 0xEA => {
            Some(AddressingModeType::Implied)
        }

        // jmp indirect
        0x6C => Some(AddressingModeType::Indirect),

        // Indexed zeropage stx/ldx
        0xB6 | 0x96 => Some(AddressingModeType::ZeroPageIndexedWithY),
        // absolute indexed ldx
        0xBE => Some(AddressingModeType::AbsoluteIndexedWithY),

        _ => None,
    };

    if exception.is_some() {
        return exception;
    }

    let b_type = opcode.to_b_type();
    let c_type = opcode.to_c_type();

    match c_type {
        CType::Zero => match b_type {
            BType::Zero => Some(AddressingModeType::Immediate),
            BType::One => Some(AddressingModeType::ZeroPage),
            BType::Three => Some(AddressingModeType::Absolute),
            BType::Five => Some(AddressingModeType::ZeroPageIndexedWithX),
            BType::Seven => Some(AddressingModeType::AbsoluteIndexedWithX),
            _ => None,
        },
        CType::One => match b_type {
            BType::Zero => Some(AddressingModeType::XIndexedIndirect),
            BType::One => Some(AddressingModeType::ZeroPage),
            BType::Two => Some(AddressingModeType::Immediate),
            BType::Three => Some(AddressingModeType::Absolute),
            BType::Four => Some(AddressingModeType::IndirectYIndexed),
            BType::Five => Some(AddressingModeType::ZeroPageIndexedWithX),
            BType::Six => Some(AddressingModeType::AbsoluteIndexedWithY),
            BType::Seven => Some(AddressingModeType::AbsoluteIndexedWithX),
        },
        CType::Two => match b_type {
            BType::Zero => Some(AddressingModeType::Immediate),
            BType::One => Some(AddressingModeType::ZeroPage),
            BType::Two => Some(AddressingModeType::Accumulator),
            BType::Three => Some(AddressingModeType::Absolute),
            BType::Five => Some(AddressingModeType::ZeroPageIndexedWithX),
            BType::Seven => Some(AddressingModeType::AbsoluteIndexedWithX),
            _ => None,
        },
    }
}

pub const fn decode(
    opcode: &Opcode,
) -> Option<(
    crate::mnemonic::Mnemonic,
    crate::addressing_mode::AddressingModeType,
)> {
    let mnemonic = mnemonic_from_opcode(opcode);
    let addressing_mode = address_mode_from_opcode(opcode);

    match (mnemonic, addressing_mode) {
        (Some(mnemonic), Some(am)) => Some((mnemonic, am)),
        _ => None,
    }
}
