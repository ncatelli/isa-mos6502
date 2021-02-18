extern crate parcel;
use crate::{ByteSized, CycleCost};
use parcel::{parsers::byte::any_byte, MatchStatus, ParseResult, Parser};

///  Absolute addressing mode represents a u16 represented constant address to a
/// location in memory for the operand value.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Absolute(pub u16);

impl ByteSized for Absolute {
    fn byte_size(&self) -> usize {
        2
    }
}

impl<'a> Parser<'a, &'a [u8], Absolute> for Absolute {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], Absolute> {
        parcel::take_n(any_byte(), 2)
            .map(|b| Absolute(u16::from_le_bytes([b[0], b[1]])))
            .parse(input)
    }
}

impl Absolute {
    /// Unpacks the enclosed address from a Absolute into a corresponding u16
    /// address.
    pub fn unwrap(self) -> u16 {
        self.into()
    }
}

impl From<Absolute> for u16 {
    fn from(src: Absolute) -> Self {
        src.0
    }
}

impl From<Absolute> for Vec<u8> {
    fn from(src: Absolute) -> Self {
        src.0.to_le_bytes().to_vec()
    }
}

impl From<Absolute> for AddressingMode {
    fn from(src: Absolute) -> Self {
        AddressingMode::Absolute(src.0)
    }
}

/// AbsoluteIndexedWithX represents an address whose value is stored at an X
/// register offset from the operand value. Example being LLHH + X.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct AbsoluteIndexedWithX(pub u16);

impl ByteSized for AbsoluteIndexedWithX {
    fn byte_size(&self) -> usize {
        2
    }
}

impl<'a> Parser<'a, &'a [u8], AbsoluteIndexedWithX> for AbsoluteIndexedWithX {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], AbsoluteIndexedWithX> {
        parcel::take_n(any_byte(), 2)
            .map(|b| AbsoluteIndexedWithX(u16::from_le_bytes([b[0], b[1]])))
            .parse(input)
    }
}

impl AbsoluteIndexedWithX {
    /// Unpacks the enclosed address from a AbsoluteIndexedWithX addressing mode
    /// into a corresponding u16 address.
    pub fn unwrap(self) -> u16 {
        self.into()
    }
}

impl From<AbsoluteIndexedWithX> for u16 {
    fn from(src: AbsoluteIndexedWithX) -> Self {
        src.0
    }
}

impl From<AbsoluteIndexedWithX> for Vec<u8> {
    fn from(src: AbsoluteIndexedWithX) -> Self {
        src.0.to_le_bytes().to_vec()
    }
}

impl From<AbsoluteIndexedWithX> for AddressingMode {
    fn from(src: AbsoluteIndexedWithX) -> Self {
        AddressingMode::AbsoluteIndexedWithX(src.0)
    }
}

/// AbsoluteIndexedWithY represents an address whose value is stored at an Y
/// register offset from the operand value. Example being LLHH + Y.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct AbsoluteIndexedWithY(pub u16);

impl ByteSized for AbsoluteIndexedWithY {
    fn byte_size(&self) -> usize {
        2
    }
}

impl<'a> Parser<'a, &'a [u8], AbsoluteIndexedWithY> for AbsoluteIndexedWithY {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], AbsoluteIndexedWithY> {
        parcel::take_n(any_byte(), 2)
            .map(|b| AbsoluteIndexedWithY(u16::from_le_bytes([b[0], b[1]])))
            .parse(input)
    }
}

impl AbsoluteIndexedWithY {
    /// Unpacks the enclosed address from a AbsoluteIndexedWithY addressing mode
    /// into a corresponding u16 address.
    pub fn unwrap(self) -> u16 {
        self.into()
    }
}

impl From<AbsoluteIndexedWithY> for u16 {
    fn from(src: AbsoluteIndexedWithY) -> Self {
        src.0
    }
}

impl From<AbsoluteIndexedWithY> for Vec<u8> {
    fn from(src: AbsoluteIndexedWithY) -> Self {
        src.0.to_le_bytes().to_vec()
    }
}

impl From<AbsoluteIndexedWithY> for AddressingMode {
    fn from(src: AbsoluteIndexedWithY) -> Self {
        AddressingMode::AbsoluteIndexedWithY(src.0)
    }
}

/// Accumulator addressing mode represents an operand whose value is sourced
/// from the ACC register.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Accumulator;

impl ByteSized for Accumulator {
    fn byte_size(&self) -> usize {
        0
    }
}

impl<'a> Parser<'a, &'a [u8], Accumulator> for Accumulator {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], Accumulator> {
        Ok(MatchStatus::Match((input, Accumulator)))
    }
}

impl From<Accumulator> for Vec<u8> {
    fn from(_: Accumulator) -> Self {
        vec![]
    }
}

impl From<Accumulator> for AddressingMode {
    fn from(_: Accumulator) -> Self {
        AddressingMode::Accumulator
    }
}

/// Immediate represents an immediate (constant) operand represented as a
/// single byte.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Immediate(pub u8);

impl ByteSized for Immediate {}

impl<'a> Parser<'a, &'a [u8], Immediate> for Immediate {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], Immediate> {
        any_byte().map(Immediate).parse(input)
    }
}

impl Immediate {
    /// Unpacks the enclosed value from an Immediate into a corresponding u8
    /// operand.
    pub fn unwrap(self) -> u8 {
        self.into()
    }
}

impl From<Immediate> for u8 {
    fn from(src: Immediate) -> Self {
        src.0
    }
}

impl From<Immediate> for Vec<u8> {
    fn from(src: Immediate) -> Self {
        vec![src.0]
    }
}

impl From<Immediate> for AddressingMode {
    fn from(src: Immediate) -> Self {
        AddressingMode::Immediate(src.0)
    }
}

/// Implied addressing mode. This is signified by no addressing mode
/// arguments. An example instruction with an implied addressing mode would be.
/// `nop`
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Implied;

impl ByteSized for Implied {
    fn byte_size(&self) -> usize {
        0
    }
}

impl<'a> Parser<'a, &'a [u8], Implied> for Implied {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], Implied> {
        Ok(MatchStatus::Match((input, Implied)))
    }
}

impl From<Implied> for Vec<u8> {
    fn from(_: Implied) -> Self {
        vec![]
    }
}

impl From<Implied> for AddressingMode {
    fn from(_: Implied) -> Self {
        AddressingMode::Implied
    }
}

/// Indirect represents an operand whose value is the word stored at the address
/// and the address + 1.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Indirect(pub u16);

impl ByteSized for Indirect {
    fn byte_size(&self) -> usize {
        2
    }
}

impl<'a> Parser<'a, &'a [u8], Indirect> for Indirect {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], Indirect> {
        parcel::take_n(any_byte(), 2)
            .map(|b| Indirect(u16::from_le_bytes([b[0], b[1]])))
            .parse(input)
    }
}

impl Indirect {
    /// Unpacks the enclosed address from a Indirect addressing mode into a
    /// corresponding u16 address.
    pub fn unwrap(self) -> u16 {
        self.into()
    }
}

impl From<Indirect> for u16 {
    fn from(src: Indirect) -> Self {
        src.0
    }
}

impl From<Indirect> for Vec<u8> {
    fn from(src: Indirect) -> Self {
        src.0.to_le_bytes().to_vec()
    }
}

impl From<Indirect> for AddressingMode {
    fn from(src: Indirect) -> Self {
        AddressingMode::Indirect(src.0)
    }
}

/// IndirectYIndexed represents an address whose value is stored as a Y
/// register offset for an indirect address defined as the operand. Example
/// being (LL, LL + 1) + Y.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct IndirectYIndexed(pub u8);

impl ByteSized for IndirectYIndexed {}

impl<'a> Parser<'a, &'a [u8], IndirectYIndexed> for IndirectYIndexed {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], IndirectYIndexed> {
        any_byte().map(IndirectYIndexed).parse(input)
    }
}

impl IndirectYIndexed {
    /// Unpacks the enclosed address from a IndirectYIndexed addressing mode
    /// into a corresponding u8 address.
    pub fn unwrap(self) -> u8 {
        self.into()
    }
}

impl From<IndirectYIndexed> for u8 {
    fn from(src: IndirectYIndexed) -> Self {
        src.0
    }
}

impl From<IndirectYIndexed> for Vec<u8> {
    fn from(src: IndirectYIndexed) -> Self {
        src.0.to_le_bytes().to_vec()
    }
}

impl From<IndirectYIndexed> for AddressingMode {
    fn from(src: IndirectYIndexed) -> Self {
        AddressingMode::IndirectYIndexed(src.0)
    }
}

/// XIndexedIndirect represents an address whose value is stored as an X
/// register offset for sequential bytes of an address word. Example being
/// LL + X, LL + X + 1.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct XIndexedIndirect(pub u8);

impl ByteSized for XIndexedIndirect {}

impl<'a> Parser<'a, &'a [u8], XIndexedIndirect> for XIndexedIndirect {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], XIndexedIndirect> {
        any_byte().map(XIndexedIndirect).parse(input)
    }
}

impl XIndexedIndirect {
    /// Unpacks the enclosed address from a XIndexedIndirect addressing mode
    /// into a corresponding u8 address.
    pub fn unwrap(self) -> u8 {
        self.into()
    }
}

impl From<XIndexedIndirect> for u8 {
    fn from(src: XIndexedIndirect) -> Self {
        src.0
    }
}

impl From<XIndexedIndirect> for Vec<u8> {
    fn from(src: XIndexedIndirect) -> Self {
        src.0.to_le_bytes().to_vec()
    }
}

impl From<XIndexedIndirect> for AddressingMode {
    fn from(src: XIndexedIndirect) -> Self {
        AddressingMode::XIndexedIndirect(src.0)
    }
}

/// Relative wraps an i8 and signifies a relative address to the current
/// instruction. This is commonly used alongside branch instructions that may
/// cause a short jump either forward or back in memory to facilitate looping.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Relative(pub i8);

impl ByteSized for Relative {}

impl<'a> Parser<'a, &'a [u8], Relative> for Relative {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], Relative> {
        any_byte()
            .map(|b| {
                let offset = unsafe { std::mem::transmute::<u8, i8>(b) };
                Relative(offset)
            })
            .parse(input)
    }
}

impl Relative {
    /// Unpacks the enclosed address from a Relative addressing mode into a
    /// corresponding i8 address.
    pub fn unwrap(self) -> i8 {
        self.into()
    }
}

impl From<Relative> for i8 {
    fn from(src: Relative) -> Self {
        src.0
    }
}

impl From<Relative> for Vec<u8> {
    fn from(src: Relative) -> Self {
        let i_to_u = unsafe { std::mem::transmute::<i8, u8>(src.0) };
        vec![i_to_u]
    }
}

impl From<Relative> for AddressingMode {
    fn from(src: Relative) -> Self {
        AddressingMode::Relative(src.0)
    }
}

/// ZeroPage wraps a u8 and represents an address in 00LL format.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ZeroPage(pub u8);

impl CycleCost for ZeroPage {}
impl ByteSized for ZeroPage {}

impl<'a> Parser<'a, &'a [u8], ZeroPage> for ZeroPage {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], ZeroPage> {
        any_byte().map(ZeroPage).parse(input)
    }
}

impl ZeroPage {
    /// Unpacks the enclosed address from a Zeropage into a corresponding u8
    /// address.
    pub fn unwrap(self) -> u8 {
        self.into()
    }
}

impl From<ZeroPage> for u8 {
    fn from(src: ZeroPage) -> Self {
        src.0
    }
}

impl From<ZeroPage> for Vec<u8> {
    fn from(src: ZeroPage) -> Self {
        vec![src.0]
    }
}

impl From<ZeroPage> for AddressingMode {
    fn from(src: ZeroPage) -> Self {
        AddressingMode::ZeroPage(src.0)
    }
}

/// ZeroPageIndexedWithX wraps a u8 and represents an address in the zeropage +
/// the value of the X register in the format of `00LL + x`.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ZeroPageIndexedWithX(pub u8);

impl ByteSized for ZeroPageIndexedWithX {}

impl<'a> Parser<'a, &'a [u8], ZeroPageIndexedWithX> for ZeroPageIndexedWithX {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], ZeroPageIndexedWithX> {
        any_byte().map(ZeroPageIndexedWithX).parse(input)
    }
}

impl ZeroPageIndexedWithX {
    /// Unpacks the enclosed address from a ZeropageIndexedWithX into a
    /// corresponding u8 address.
    pub fn unwrap(self) -> u8 {
        self.into()
    }
}

impl From<ZeroPageIndexedWithX> for u8 {
    fn from(src: ZeroPageIndexedWithX) -> Self {
        src.0
    }
}

impl From<ZeroPageIndexedWithX> for Vec<u8> {
    fn from(src: ZeroPageIndexedWithX) -> Self {
        vec![src.0]
    }
}

impl From<ZeroPageIndexedWithX> for AddressingMode {
    fn from(src: ZeroPageIndexedWithX) -> Self {
        AddressingMode::ZeroPageIndexedWithX(src.0)
    }
}

/// ZeroPageIndexedWithY wraps a u8 and represents an address in the zeropage +
/// the value of the Y register in the format of `00LL + y`.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct ZeroPageIndexedWithY(pub u8);

impl ByteSized for ZeroPageIndexedWithY {}

impl<'a> Parser<'a, &'a [u8], ZeroPageIndexedWithY> for ZeroPageIndexedWithY {
    fn parse(&self, input: &'a [u8]) -> ParseResult<&'a [u8], ZeroPageIndexedWithY> {
        any_byte().map(ZeroPageIndexedWithY).parse(input)
    }
}

impl ZeroPageIndexedWithY {
    /// Unpacks the enclosed address from a ZeropageIndexedWithY into a
    /// corresponding u8 address.
    pub fn unwrap(self) -> u8 {
        self.into()
    }
}

impl From<ZeroPageIndexedWithY> for u8 {
    fn from(src: ZeroPageIndexedWithY) -> Self {
        src.0
    }
}

impl From<ZeroPageIndexedWithY> for Vec<u8> {
    fn from(src: ZeroPageIndexedWithY) -> Self {
        vec![src.0]
    }
}

impl From<ZeroPageIndexedWithY> for AddressingMode {
    fn from(src: ZeroPageIndexedWithY) -> Self {
        AddressingMode::ZeroPageIndexedWithY(src.0)
    }
}

/// AddressingMode captures the Addressing mode type with a corresponding
/// operand of the appropriate bit length.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AddressingMode {
    Accumulator,
    Implied,
    Immediate(u8),
    Absolute(u16),
    ZeroPage(u8),
    Relative(i8),
    Indirect(u16),
    AbsoluteIndexedWithX(u16),
    AbsoluteIndexedWithY(u16),
    ZeroPageIndexedWithX(u8),
    ZeroPageIndexedWithY(u8),
    XIndexedIndirect(u8),
    IndirectYIndexed(u8),
}

impl Into<Vec<u8>> for AddressingMode {
    fn into(self) -> Vec<u8> {
        match self {
            AddressingMode::Immediate(operand) => vec![operand],
            AddressingMode::Absolute(operand) => operand.to_le_bytes().to_vec(),
            AddressingMode::ZeroPage(operand) => vec![operand],
            AddressingMode::Relative(operand) => {
                let o_to_u8 = unsafe { std::mem::transmute::<i8, u8>(operand) };
                vec![o_to_u8]
            }
            AddressingMode::Indirect(operand) => operand.to_le_bytes().to_vec(),
            AddressingMode::AbsoluteIndexedWithX(operand) => operand.to_le_bytes().to_vec(),
            AddressingMode::AbsoluteIndexedWithY(operand) => operand.to_le_bytes().to_vec(),
            AddressingMode::ZeroPageIndexedWithX(operand) => vec![operand],
            AddressingMode::ZeroPageIndexedWithY(operand) => vec![operand],
            AddressingMode::XIndexedIndirect(operand) => vec![operand],
            AddressingMode::IndirectYIndexed(operand) => vec![operand],
            _ => vec![],
        }
    }
}

impl crate::ByteSized for AddressingMode {
    fn byte_size(&self) -> usize {
        match self {
            AddressingMode::Accumulator | AddressingMode::Implied => 0,
            AddressingMode::Absolute(_)
            | AddressingMode::Indirect(_)
            | AddressingMode::AbsoluteIndexedWithX(_)
            | AddressingMode::AbsoluteIndexedWithY(_) => 2,
            _ => 1,
        }
    }
}

/// AddressingModeType captures the addressing mode type without the operand
/// value.
#[derive(Debug, Clone, Copy, PartialEq, Hash)]
pub enum AddressingModeType {
    Accumulator,
    Implied,
    Immediate,
    Absolute,
    ZeroPage,
    Relative,
    Indirect,
    AbsoluteIndexedWithX,
    AbsoluteIndexedWithY,
    ZeroPageIndexedWithX,
    ZeroPageIndexedWithY,
    IndexedIndirect,
    IndirectIndexed,
}

impl std::fmt::Display for AddressingModeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
