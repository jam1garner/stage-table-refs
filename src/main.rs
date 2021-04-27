#![feature(array_windows)]
use binread::BinReaderExt;
use nxo_parser::NsoFile;

use std::iter::{Copied, Enumerate, StepBy};
use std::slice::ArrayWindows;
use std::convert::TryInto;
use std::io::BufReader;

const ADRP_MASK: u32 = 0b1_00_11111_0000000000000000000_00000;
const ADRP_MASKED: u32 = 0b1_00_10000_0000000000000000000_00000;

fn adrp_offset(instr: u32) -> Option<u32> {
    if instr & ADRP_MASK == ADRP_MASKED {
        let immhi = (instr >> 5) & 0x7FFFF;
        let immlo = (instr >> 29) & 0x3;

        Some((immhi << 14) + (immlo << 12))
    } else {
        None
    }
}

const ADD_MASK: u32 = 0b11111111_00_000000000000_00000_00000; // 64-bit ADD immediate
const ADD_MASKED: u32 = 0b10010001_00_000000000000_00000_00000;

fn add_offset(instr: u32) -> Option<u32> {
    if instr & ADD_MASK == ADD_MASKED {
        let rn = ((instr >> 5) & 0x1F) as u8;
        let rd = (instr & 0x1F) as u8;
        let imm = (instr >> 10) & 0xFFF;
        let shift = ((instr >> 22) & 0x3) as u8;

        if rn == rd && shift == 0 {
            Some(imm)
        } else {
            None
        }
    } else {
        None
    }
}

struct CmpImmediate {
    imm12: u16,
    reg: u8,
    is_64_bit: bool,
}

impl CmpImmediate {
    const MASK: u32 = 0b011111111_0_000000000000_00000_11111;
    const MASKED: u32 = 0b011100010_0_000000000000_00000_11111; 

    fn decode(instr: u32) -> Option<Self> {
        if instr & Self::MASK == Self::MASKED {
            let reg = ((instr >> 5) & 0b11111) as u8;
            let imm12 = ((instr >> 10) & 0b111111111111) as u16;
            let is_64_bit = (instr >> 31) == 1;

            Some(Self { reg, imm12, is_64_bit })
        } else {
            None
        }
    }

    fn encode(&self) -> u32 {
        let sh = 0;
        let sf = if self.is_64_bit { 1 } else { 0 };
        let imm12 = (self.imm12 & 0b111111111111) as u32;
        let rn = (self.reg & 0b11111) as u32;

        Self::MASKED | (imm12 << 10) | (rn << 5) | (sf << 31) | (sh << 22)
    }
}

fn extract_add_instr_register(instr: u32) -> Option<u8> {
    if instr & ADD_MASK == ADD_MASKED {
        let rn = ((instr >> 5) & 0x1F) as u8;
        let rd = (instr & 0x1F) as u8;
        let imm = (instr >> 10) & 0xFFF;
        let shift = ((instr >> 22) & 0x3) as u8;

        if rn == rd && shift == 0 {
            Some(rd)
        } else {
            None
        }
    } else {
        None
    }
}

const TABLE_START_SEARCH: &[u8] = &[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213, 246, 183, 81, 11, 0, 0, 0, 196, 43, 190,
    220, 24, 0, 0, 0, 224, 224, 240, 112, 24, 0, 0, 0, 34, 74, 84, 50, 46, 0, 0, 0,
];

fn find_table_start(rodata: &[u8], rodata_offset: usize) -> Option<usize> {
    rodata
        .windows(TABLE_START_SEARCH.len())
        .position(|window| window == TABLE_START_SEARCH)
        .map(|x| x + rodata_offset)
}

struct StageRefIter<I: Iterator<Item = [u8; 8]>> {
    table_offset: usize,
    inner: Enumerate<I>,
}

const BOTTOM_12_BITS: usize = 0b1111_1111_1111;

struct PatchLocation {
    text_offset: usize,
    offset_from_table_start: usize,
    register: u8,
}

impl<I: Iterator<Item = [u8; 8]>> Iterator for StageRefIter<I> {
    type Item = PatchLocation;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((i, bytes)) = self.inner.next() {
            let adrp = u32::from_le_bytes(bytes[..4].try_into().unwrap());
            let add = u32::from_le_bytes(bytes[4..].try_into().unwrap());

            match (adrp_offset(adrp), add_offset(add)) {
                (Some(adrp_offset), Some(add_offset)) => {
                    let instr_loc = i * 4;

                    let offset = (instr_loc & !BOTTOM_12_BITS)
                        + (adrp_offset as usize)
                        + (add_offset as usize);

                    if (self.table_offset..self.table_offset + 0x100).contains(&offset) {
                        let register = extract_add_instr_register(add).unwrap();
                        return Some(PatchLocation{
                            register,
                            text_offset: i * 4,
                            offset_from_table_start: offset - self.table_offset,
                        });
                    }
                }
                _ => continue,
            }
        }

        None
    }
}

type TextIter8<'a> = Copied<StepBy<ArrayWindows<'a, u8, 8>>>;

impl<'a> StageRefIter<TextIter8<'a>> {
    fn new(text: &'a [u8], rodata: &[u8], rodata_offset: usize) -> Self {
        Self {
            table_offset: find_table_start(&rodata, rodata_offset).unwrap(),
            inner: text.array_windows().step_by(4).copied().enumerate(),
        }
    }
}

type TextIter<'a> = Copied<StepBy<ArrayWindows<'a, u8, 4>>>;

struct StageCountRefIter<I: Iterator<Item = [u8; 4]>> {
    inner: Enumerate<I>,
}

impl<'a> StageCountRefIter<TextIter<'a>> {
    fn new(text: &'a [u8]) -> Self {
        Self {
            inner: text.array_windows().step_by(4).copied().enumerate(),
        }
    }
}

struct CmpPatchLocation {
    text_offset: usize,
    instr: CmpImmediate,
}

impl<I: Iterator<Item = [u8; 4]>> Iterator for StageCountRefIter<I> {
    type Item = CmpPatchLocation;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((i, bytes)) = self.inner.next() {
            let instr = u32::from_le_bytes(bytes);

            if let Some(instr @ CmpImmediate { imm12: 0x165, .. }) = CmpImmediate::decode(instr) {
                return Some(CmpPatchLocation { instr, text_offset: i * 4})
            }
        }

        None
    }
}

fn main() {
    let mut reader = BufReader::new(std::fs::File::open("/home/jam/re/ult/1101/main").unwrap());
    let nso: NsoFile = reader.read_le().unwrap();

    let text = nso.get_text(&mut reader).unwrap();
    let rodata = nso.get_rodata(&mut reader).unwrap();
    let rodata_offset = nso.rodata_segment_header.memory_offset as usize;

    for xref in StageRefIter::new(&text, &rodata, rodata_offset) {
        println!(".text+{:#x?} - patch register x{} to table+{:#x?}", xref.text_offset, xref.register, xref.offset_from_table_start);
    }

    for xref in StageCountRefIter::new(&text) {
        println!(".text+{:#x?} - patch `{}`", xref.text_offset, xref.instr);
    }
}

use std::fmt;

impl fmt::Display for CmpImmediate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_64_bit {
            write!(f, "cmp x{}, #{:#x?}", self.reg, self.imm12)
        } else {
            write!(f, "cmp r{}, #{:#x?}", self.reg, self.imm12)
        }
    }
}
