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

const fn mnemonic_from_types(a_type: AType, c_type: CType) -> Option<crate::mnemonic::Mnemonic> {
    use crate::mnemonic::Mnemonic;

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

const fn address_mode_from_types(
    b_type: BType,
    c_type: CType,
) -> Option<crate::addressing_mode::AddressingModeType> {
    use crate::addressing_mode::AddressingModeType;

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
    let a_type = opcode.to_a_type();
    let b_type = opcode.to_b_type();
    let c_type = opcode.to_c_type();
    let mnemonic = mnemonic_from_types(a_type, c_type);
    let addressing_mode = address_mode_from_types(b_type, c_type);

    if let (Some(mnemonic), Some(am)) = (mnemonic, addressing_mode) {
        Some((mnemonic, am))
    } else {
        None
    }
}
