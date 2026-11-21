//! Generates random RV32IMC instruction sequences for the lockstep test of
//! the Lean RV32 model against Espressif's QEMU.
//!
//! Usage: `rv_cases OUT_DIR SEED CASES`. Writes two files into `OUT_DIR`:
//!
//! - `cases.S`, which `c3-rvtest` assembles. Each case loads its initial
//!   registers, runs its sequence, and stores the registers it ends with.
//! - `cases.txt`, with one line per case: `case N CODE REGS MEM`, where
//!   `CODE` is the sequence's bytes, `REGS` are `x1` through `x31` as 8 hex
//!   digits each, and `MEM` is the buffer's initial 256 bytes.
//!
//! Every load and store uses the buffer at `BUF`, through a base register
//! set just before it. Branches and jumps go forward to an instruction
//! boundary in the same sequence or to its end.

use std::fmt::Write as _;
use std::fs;

/// The buffer the sequences load and store, at the start of the
/// application RAM region, which the test firmware leaves unused.
const BUF: u32 = 0x3FC8_0000;
const BUF_LEN: u32 = 256;
const ITEMS: usize = 28;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn reg(&mut self) -> u32 {
        self.below(32) as u32
    }

    /// A register in `x8` through `x15`, as the compressed forms' 3-bit field.
    fn creg(&mut self) -> u32 {
        self.below(8) as u32
    }

    fn value(&mut self) -> u32 {
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => u32::MAX,
            3 => 0x8000_0000,
            4 => 0x7FFF_FFFF,
            _ => self.next() as u32,
        }
    }
}

/// One instruction or fixed group, before its branch target is resolved.
enum Item {
    /// Encoded bytes with no target.
    Fixed(Vec<u8>),
    /// A conditional branch or jump to the start of item `target` (or the
    /// end of the sequence when `target == ITEMS`).
    Jump { kind: JumpKind, target: usize },
}

#[derive(Clone, Copy)]
enum JumpKind {
    Branch {
        f3: u32,
        rs1: u32,
        rs2: u32,
    },
    Jal {
        rd: u32,
    },
    CJ,
    CJal,
    CBeqz {
        rs1: u32,
    },
    CBnez {
        rs1: u32,
    },
    /// `auipc rt, 0`, `addi rt, rt, delta`, then `c.jr rt` or `c.jalr rt`.
    Indirect {
        rt: u32,
        link: bool,
    },
    /// `auipc rt, 0`, then `jalr rd, delta(rt)`.
    Jalr {
        rt: u32,
        rd: u32,
    },
}

impl JumpKind {
    fn len(self) -> u32 {
        match self {
            JumpKind::Branch { .. } | JumpKind::Jal { .. } => 4,
            JumpKind::Indirect { .. } => 10,
            JumpKind::Jalr { .. } => 8,
            _ => 2,
        }
    }
}

fn w32(v: u32) -> Vec<u8> {
    v.to_le_bytes().to_vec()
}

fn w16(v: u32) -> Vec<u8> {
    (v as u16).to_le_bytes().to_vec()
}

fn r_type(f7: u32, rs2: u32, rs1: u32, f3: u32, rd: u32, op: u32) -> u32 {
    f7 << 25 | rs2 << 20 | rs1 << 15 | f3 << 12 | rd << 7 | op
}

fn i_type(imm: u32, rs1: u32, f3: u32, rd: u32, op: u32) -> u32 {
    (imm & 0xFFF) << 20 | rs1 << 15 | f3 << 12 | rd << 7 | op
}

fn s_type(imm: u32, rs2: u32, rs1: u32, f3: u32) -> u32 {
    (imm >> 5 & 0x7F) << 25 | rs2 << 20 | rs1 << 15 | f3 << 12 | (imm & 0x1F) << 7 | 0x23
}

fn b_type(off: u32, rs2: u32, rs1: u32, f3: u32) -> u32 {
    (off >> 12 & 1) << 31
        | (off >> 5 & 0x3F) << 25
        | rs2 << 20
        | rs1 << 15
        | f3 << 12
        | (off >> 1 & 0xF) << 8
        | (off >> 11 & 1) << 7
        | 0x63
}

fn j_type(off: u32, rd: u32) -> u32 {
    (off >> 20 & 1) << 31
        | (off >> 1 & 0x3FF) << 21
        | (off >> 11 & 1) << 20
        | (off >> 12 & 0xFF) << 12
        | rd << 7
        | 0x6F
}

/// The compressed jump offset field, shared by `c.j` and `c.jal`.
fn cj_bits(off: u32) -> u32 {
    (off >> 11 & 1) << 12
        | (off >> 4 & 1) << 11
        | (off >> 8 & 3) << 9
        | (off >> 10 & 1) << 8
        | (off >> 6 & 1) << 7
        | (off >> 7 & 1) << 6
        | (off >> 1 & 7) << 3
        | (off >> 5 & 1) << 2
}

fn cb_bits(off: u32) -> u32 {
    (off >> 8 & 1) << 12
        | (off >> 3 & 3) << 10
        | (off >> 6 & 3) << 5
        | (off >> 1 & 3) << 3
        | (off >> 5 & 1) << 2
}

/// `lui rb, hi(BUF)` and `addi rb, rb, lo(BUF)`, so `rb` points at the
/// buffer.
fn set_base(rb: u32) -> Vec<u8> {
    let mut v = w32(BUF & 0xFFFF_F000 | rb << 7 | 0x37);
    v.extend(w32(i_type(BUF & 0xFFF, rb, 0, rb, 0x13)));
    v
}

fn random_item(rng: &mut Rng) -> Item {
    let kind = rng.below(100);
    let bytes = match kind {
        0..=17 => {
            // OP and the M extension.
            let (f7, f3) = [
                (0, 0),
                (0x20, 0),
                (0, 1),
                (0, 2),
                (0, 3),
                (0, 4),
                (0, 5),
                (0x20, 5),
                (0, 6),
                (0, 7),
                (1, 0),
                (1, 1),
                (1, 2),
                (1, 3),
                (1, 4),
                (1, 5),
                (1, 6),
                (1, 7),
            ][rng.below(18) as usize];
            w32(r_type(f7, rng.reg(), rng.reg(), f3, rng.reg(), 0x33))
        }
        18..=29 => {
            // OP-IMM.
            let f3 = [0, 2, 3, 4, 6, 7, 1, 5][rng.below(8) as usize];
            let imm = match f3 {
                1 => rng.below(32) as u32,
                5 => rng.below(32) as u32 | if rng.below(2) == 0 { 0x400 } else { 0 },
                _ => rng.next() as u32 & 0xFFF,
            };
            w32(i_type(imm, rng.reg(), f3, rng.reg(), 0x13))
        }
        30..=33 => w32((rng.next() as u32 & 0xFFFF_F000) | rng.reg() << 7 | 0x37),
        34..=36 => w32((rng.next() as u32 & 0xFFFF_F000) | rng.reg() << 7 | 0x17),
        37..=44 => {
            // A load or store, after setting its base register.
            let rb = 1 + rng.below(31) as u32;
            let mut v = set_base(rb);
            if rng.below(2) == 0 {
                let (f3, size) = [(0, 1), (1, 2), (2, 4), (4, 1), (5, 2)][rng.below(5) as usize];
                let off = rng.below(u64::from(BUF_LEN / size)) as u32 * size;
                v.extend(w32(i_type(off, rb, f3, rng.reg(), 0x03)));
            } else {
                let (f3, size) = [(0, 1), (1, 2), (2, 4)][rng.below(3) as usize];
                let off = rng.below(u64::from(BUF_LEN / size)) as u32 * size;
                v.extend(w32(s_type(off, rng.reg(), rb, f3)));
            }
            v
        }
        45..=48 => {
            // c.lw or c.sw through a compressed base register.
            let rb = rng.creg();
            let off = rng.below(32) as u32 * 4;
            let mut v = set_base(8 + rb);
            let imm = (off >> 3 & 7) << 10 | (off >> 2 & 1) << 6 | (off >> 6 & 1) << 5;
            let f3 = if rng.below(2) == 0 { 2 } else { 6 };
            v.extend(w16(f3 << 13 | imm | rb << 7 | rng.creg() << 2));
            v
        }
        49..=51 => {
            // c.lwsp or c.swsp, after pointing sp at the buffer.
            let off = rng.below(64) as u32 * 4;
            let mut v = set_base(2);
            if rng.below(2) == 0 {
                let rd = 1 + rng.below(31) as u32;
                v.extend(w16(2 << 13
                    | (off >> 5 & 1) << 12
                    | rd << 7
                    | (off >> 2 & 7) << 4
                    | (off >> 6 & 3) << 2
                    | 2));
            } else {
                v.extend(w16(6 << 13
                    | (off >> 2 & 0xF) << 9
                    | (off >> 6 & 3) << 7
                    | rng.reg() << 2
                    | 2));
            }
            v
        }
        52..=55 => {
            let imm = rng.below(64) as u32;
            w16((imm >> 5) << 12 | rng.reg() << 7 | (imm & 0x1F) << 2 | 1)
        }
        56..=58 => {
            let imm = rng.below(64) as u32;
            w16(2 << 13 | (imm >> 5) << 12 | rng.reg() << 7 | (imm & 0x1F) << 2 | 1)
        }
        59..=60 => {
            let imm = 1 + rng.below(63) as u32;
            let rd = [1, 3, 4, 5, 6, 7, 8, 9, 10, 31][rng.below(10) as usize];
            w16(3 << 13 | (imm >> 5) << 12 | rd << 7 | (imm & 0x1F) << 2 | 1)
        }
        61..=62 => {
            // c.addi16sp, with a nonzero multiple of 16.
            let imm = (1 + rng.below(31) as u32) * 16;
            w16(3 << 13
                | (imm >> 9 & 1) << 12
                | 2 << 7
                | (imm >> 4 & 1) << 6
                | (imm >> 6 & 1) << 5
                | (imm >> 7 & 3) << 3
                | (imm >> 5 & 1) << 2
                | 1)
        }
        63..=64 => {
            // c.addi4spn, with a nonzero multiple of 4.
            let imm = (1 + rng.below(255) as u32) * 4;
            w16((imm >> 4 & 3) << 11
                | (imm >> 6 & 0xF) << 7
                | (imm >> 2 & 1) << 6
                | (imm >> 3 & 1) << 5
                | rng.creg() << 2)
        }
        65..=72 => {
            // c.srli, c.srai, c.andi, c.sub, c.xor, c.or, c.and.
            let rs = rng.creg();
            match rng.below(4) {
                0 => w16(4 << 13 | rs << 7 | (rng.below(32) as u32) << 2 | 1),
                1 => w16(4 << 13 | 1 << 10 | rs << 7 | (rng.below(32) as u32) << 2 | 1),
                2 => {
                    let imm = rng.below(64) as u32;
                    w16(4 << 13 | (imm >> 5) << 12 | 2 << 10 | rs << 7 | (imm & 0x1F) << 2 | 1)
                }
                _ => w16(4 << 13
                    | 3 << 10
                    | rs << 7
                    | (rng.below(4) as u32) << 5
                    | rng.creg() << 2
                    | 1),
            }
        }
        73..=75 => w16(rng.reg() << 7 | (rng.below(32) as u32) << 2 | 2),
        76..=81 => {
            // c.mv or c.add, with a nonzero source.
            let rs2 = 1 + rng.below(31) as u32;
            let add = if rng.below(2) == 0 { 0 } else { 1 << 12 };
            w16(4 << 13 | add | rng.reg() << 7 | rs2 << 2 | 2)
        }
        82..=86 => {
            return Item::Jump {
                kind: JumpKind::Branch {
                    f3: [0, 1, 4, 5, 6, 7][rng.below(6) as usize],
                    rs1: rng.reg(),
                    rs2: rng.reg(),
                },
                target: 0,
            };
        }
        87..=88 => {
            return Item::Jump {
                kind: JumpKind::Jal { rd: rng.reg() },
                target: 0,
            };
        }
        89 => {
            return Item::Jump {
                kind: JumpKind::CJ,
                target: 0,
            };
        }
        90 => {
            return Item::Jump {
                kind: JumpKind::CJal,
                target: 0,
            };
        }
        91..=92 => {
            return Item::Jump {
                kind: JumpKind::CBeqz { rs1: rng.creg() },
                target: 0,
            };
        }
        93..=94 => {
            return Item::Jump {
                kind: JumpKind::CBnez { rs1: rng.creg() },
                target: 0,
            };
        }
        97 => {
            let rt = 1 + rng.below(31) as u32;
            return Item::Jump {
                kind: JumpKind::Jalr { rt, rd: rng.reg() },
                target: 0,
            };
        }
        95..=96 => {
            let rt = 1 + rng.below(31) as u32;
            return Item::Jump {
                kind: JumpKind::Indirect {
                    rt,
                    link: rng.below(2) == 0,
                },
                target: 0,
            };
        }
        _ => w32(0x0000_000F),
    };
    Item::Fixed(bytes)
}

fn encode_jump(kind: JumpKind, at: u32, target: u32) -> Vec<u8> {
    let off = target.wrapping_sub(at);
    match kind {
        JumpKind::Branch { f3, rs1, rs2 } => w32(b_type(off, rs2, rs1, f3)),
        JumpKind::Jal { rd } => w32(j_type(off, rd)),
        JumpKind::CJ => w16(5 << 13 | cj_bits(off) | 1),
        JumpKind::CJal => w16(1 << 13 | cj_bits(off) | 1),
        JumpKind::CBeqz { rs1 } => w16(6 << 13 | cb_bits(off) | rs1 << 7 | 1),
        JumpKind::CBnez { rs1 } => w16(7 << 13 | cb_bits(off) | rs1 << 7 | 1),
        JumpKind::Indirect { rt, link } => {
            let mut v = w32(rt << 7 | 0x17);
            v.extend(w32(i_type(off, rt, 0, rt, 0x13)));
            let link = if link { 1 << 12 } else { 0 };
            v.extend(w16(4 << 13 | link | rt << 7 | 2));
            v
        }
        JumpKind::Jalr { rt, rd } => {
            let mut v = w32(rt << 7 | 0x17);
            v.extend(w32(i_type(off, rt, 0, rd, 0x67)));
            v
        }
    }
}

/// Lays out one sequence. Jumps go forward to a later item within reach of
/// their encoding, or to the end.
fn sequence(rng: &mut Rng) -> Vec<u8> {
    let mut items: Vec<Item> = (0..ITEMS).map(|_| random_item(rng)).collect();
    let len = |item: &Item| -> u32 {
        match item {
            Item::Fixed(b) => b.len() as u32,
            Item::Jump { kind, .. } => kind.len(),
        }
    };
    let mut starts = Vec::with_capacity(ITEMS + 1);
    let mut at = 0u32;
    for item in &items {
        starts.push(at);
        at += len(item);
    }
    starts.push(at);
    for i in 0..ITEMS {
        if let Item::Jump { kind, target } = &mut items[i] {
            let reach = match kind {
                JumpKind::CBeqz { .. } | JumpKind::CBnez { .. } => 254,
                JumpKind::Indirect { .. } | JumpKind::Jalr { .. } => 2000,
                _ => 2046,
            };
            let candidates: Vec<usize> = (i + 1..=ITEMS)
                .filter(|&t| starts[t] - starts[i] <= reach)
                .collect();
            *target = candidates[rng.below(candidates.len() as u64) as usize];
        }
    }
    let mut out = Vec::new();
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Fixed(b) => out.extend(b),
            Item::Jump { kind, target } => {
                out.extend(encode_jump(*kind, starts[i], starts[*target]))
            }
        }
    }
    out
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Callee-saved registers that `rv_call` saves and `rv_exit` restores.
const SAVED: [&str; 16] = [
    "ra", "sp", "gp", "tp", "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10",
    "s11",
];

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let [_, dir, seed, cases] = args.as_slice() else {
        panic!("usage: rv_cases OUT_DIR SEED CASES");
    };
    let seed: u64 = seed.parse().expect("SEED is a number");
    let cases: usize = cases.parse().expect("CASES is a number");
    let mut rng = Rng(0x0C3B_5EED ^ seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));

    // rv_call saves the caller's registers, points mscratch at RV_OUT, and
    // jumps to the case in a0. A case loads its registers, runs its
    // sequence, swaps t0 with mscratch, and jumps to rv_exit, which stores
    // the registers and returns to rv_call's caller.
    let mut asm = String::from(".section .text.rvcases, \"ax\"\n.option norvc\n");
    asm.push_str(".balign 4\n.globl rv_call\nrv_call:\n  la t0, RV_SAVE\n");
    for (i, r) in SAVED.iter().enumerate() {
        let _ = writeln!(asm, "  sw {r}, {}(t0)", 4 * i);
    }
    asm.push_str("  la t0, RV_OUT\n  csrw mscratch, t0\n  jr a0\nrv_exit:\n");
    for r in (1..32).filter(|&r| r != 5) {
        let _ = writeln!(asm, "  sw x{r}, {}(t0)", 4 * (r - 1));
    }
    asm.push_str("  csrr x1, mscratch\n  sw x1, 16(t0)\n  la t0, RV_SAVE\n");
    for (i, r) in SAVED.iter().enumerate() {
        let _ = writeln!(asm, "  lw {r}, {}(t0)", 4 * i);
    }
    asm.push_str("  ret\n");

    let mut listing = String::new();
    let mut data = String::from(".section .rodata.rvcases, \"a\"\n.balign 4\n");
    for n in 0..cases {
        let code = sequence(&mut rng);
        let regs: Vec<u32> = (0..31).map(|_| rng.value()).collect();
        let mem: Vec<u8> = (0..BUF_LEN).map(|_| rng.next() as u8).collect();
        let _ = writeln!(
            listing,
            "case {n} {} {} {}",
            hex(&code),
            regs.iter().map(|r| format!("{r:08x}")).collect::<String>(),
            hex(&mem)
        );
        let _ = writeln!(data, "rv_init_{n}:");
        for r in &regs {
            let _ = writeln!(data, "  .word 0x{r:08x}");
        }
        let bytes: Vec<String> = mem.iter().map(|b| format!("0x{b:02x}")).collect();
        let _ = writeln!(data, "rv_mem_{n}:\n  .byte {}", bytes.join(", "));
        let _ = writeln!(asm, ".balign 4\nrv_case_{n}:\n  la x31, rv_init_{n}");
        for r in 1..31 {
            let _ = writeln!(asm, "  lw x{r}, {}(x31)", 4 * (r - 1));
        }
        let _ = writeln!(asm, "  lw x31, 120(x31)\nrv_seq_{n}:");
        for chunk in code.chunks(2) {
            let _ = writeln!(
                asm,
                "  .half 0x{:04x}",
                u16::from_le_bytes([chunk[0], chunk[1]])
            );
        }
        asm.push_str("  csrrw t0, mscratch, t0\n  j rv_exit\n");
    }
    data.push_str(".globl rv_cases\nrv_cases:\n");
    for n in 0..cases {
        let _ = writeln!(
            data,
            "  .word rv_case_{n}, rv_seq_{n}, rv_init_{n}, rv_mem_{n}"
        );
    }
    let _ = writeln!(
        data,
        ".globl rv_case_count\nrv_case_count:\n  .word {cases}"
    );
    asm.push_str(&data);
    fs::write(format!("{dir}/cases.S"), asm).expect("writes cases.S");
    fs::write(format!("{dir}/cases.txt"), listing).expect("writes cases.txt");
}
