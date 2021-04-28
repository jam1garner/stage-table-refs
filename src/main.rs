#![feature(array_windows)]
use binread::BinReaderExt;
use nxo_parser::NsoFile;

use std::iter::{Copied, Enumerate, StepBy};
use std::slice::ArrayWindows;
use std::convert::TryInto;
use std::io::BufReader;

struct Adrp {
    imm: u32,
    rd: u8,
}

impl Adrp {
    const MASK: u32 = 0b1_00_11111_0000000000000000000_00000;
    const MASKED: u32 = 0b1_00_10000_0000000000000000000_00000;

    fn decode(instr: u32) -> Option<Self> {
        if instr & Self::MASK == Self::MASKED {
            let rd = (instr & 0b11111) as u8;
            let immhi = (instr >> 5) & 0x7FFFF;
            let immlo = (instr >> 29) & 0b11;

            let imm = (immhi << 14) + (immlo << 12);

            Some(Self { imm, rd })
        } else {
            None
        }
    }

    fn encode(&self) -> u32 {
        let immlo = (self.imm >> 12) & 0b11;
        let immhi = self.imm >> 14;

        Self::MASKED | (immlo << 29) | (immhi << 5) | (self.rd as u32)
    }
}

const ADD_MASK: u32 = 0b01111111_00_000000000000_00000_00000; // 64-bit ADD immediate
const ADD_MASKED: u32 = 0b00010001_00_000000000000_00000_00000;

struct AddImm {
    imm12: u16,
    shift: u8,
    rn: u8,
    rd: u8,
    is_64_bit: bool
}

impl AddImm {
    fn decode(instr: u32) -> Option<Self> {
        if instr & ADD_MASK == ADD_MASKED {
            let rn = ((instr >> 5) & 0x1F) as u8;
            let rd = (instr & 0x1F) as u8;
            let imm12 = ((instr >> 10) & 0xFFF) as u16;
            let shift = ((instr >> 22) & 0x3) as u8;
            let is_64_bit = (instr >> 31) == 1;

            Some(AddImm { imm12, shift, rn, rd, is_64_bit })
        } else {
            None
        }
    }
}

struct LdrImmediate {
    imm9: u16,
    rn: u8,
    rt: u8,
    is_64_bit: bool,
}

impl LdrImmediate {
    const MASK: u32 = 0b10_111_1_11_11_1_000000000_11_00000_00000;
    const MASKED: u32 = 0b10_111_0_00_01_0_000000000_01_00000_00000;

    fn encode(&self) -> u32 {
        let size = if self.is_64_bit { 1 } else { 0 };
        let imm9 = (self.imm9 as u32) << 12;
        let rn = (self.rn as u32) << 5;
        let rt = self.rt as u32;

        Self::MASKED | size | imm9 | rn | rt
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
    adrp: Adrp,
    add: AddImm,
}

impl<I: Iterator<Item = [u8; 8]>> Iterator for StageRefIter<I> {
    type Item = PatchLocation;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((i, bytes)) = self.inner.next() {
            let adrp = u32::from_le_bytes(bytes[..4].try_into().unwrap());
            let add = u32::from_le_bytes(bytes[4..].try_into().unwrap());

            match (Adrp::decode(adrp), AddImm::decode(add)) {
                (Some(adrp), Some(add)) => {
                    if add.rd != add.rn || add.rd != adrp.rd {
                        continue
                    }
                    let adrp_offset = adrp.imm;
                    let add_offset = add.imm12;
                    let instr_loc = i * 4;

                    let offset = (instr_loc & !BOTTOM_12_BITS)
                        + (adrp_offset as usize)
                        + (add_offset as usize);

                    if (self.table_offset..self.table_offset + 0x100).contains(&offset) {
                        return Some(PatchLocation{
                            add,
                            adrp,
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
    fn new(text: &'a [u8], table_offset: usize) -> Self {
        Self {
            table_offset,
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

#[repr(u32)]
enum StageKind {
    Normal,
    End,
    Battle,
}

#[repr(transparent)]
struct Hash40(u64);

#[repr(C)]
struct StageTableEntry {
    stage_id: u32,
    stage_num: u32,
    stage_kind: StageKind,
    param_name_hash: Hash40,
    stage_load_group_hash: Hash40,
    effect_load_group_hash: Hash40,
    nus3bank_path_hash: Hash40,
    sqb_path_hash: Hash40,
    nus3audio_path_hash: Hash40,
    tonelabel_path_hash: Hash40,
}

// compile-time assert that the size of the entry is correct
const _: [(); 0x48] = [(); core::mem::size_of::<StageTableEntry>()];

struct RelocatedStageTable {
    table: Vec<StageTableEntry>,
    refs: Vec<PatchLocation>,
    count_refs: Vec<CmpPatchLocation>,
}

impl RelocatedStageTable {
    fn clone_from_original() -> Self {
        let this: Self = todo!();

        this.patch_pointer();

        this
    }

    fn push(&mut self, entry: StageTableEntry) {
        self.table.push(entry);
        self.patch_pointer();
        self.patch_count(self.table.len());
    }

    fn patch_pointer(&mut self) {
        todo!()
    }

    fn patch_count(&mut self, new_count: usize) {
        todo!()
    }
}

fn main() {
    let mut reader = BufReader::new(std::fs::File::open("/home/jam/re/ult/1101/main").unwrap());
    let nso: NsoFile = reader.read_le().unwrap();

    let text = nso.get_text(&mut reader).unwrap();
    let rodata = nso.get_rodata(&mut reader).unwrap();
    let rodata_offset = nso.rodata_segment_header.memory_offset as usize;

    let table_offset = find_table_start(&rodata, rodata_offset).unwrap();

    for xref in StageRefIter::new(&text, table_offset) {
        println!(".text+{:#x?} - patch register x{} to table+{:#x?}", xref.text_offset, xref.add.rd, xref.offset_from_table_start);
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
