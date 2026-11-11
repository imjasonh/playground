"""A decoder for the RV32IMC instructions that the proof generators meet,
printing each the way the Lean model's `fetchRel` returns it. `decide`
checks every lemma a generator writes from it, so a decoding mistake fails
the build instead of slipping into a proof.
"""

import re

NAMES = {0: 'x0', 1: 'ra', 2: 'sp', 10: 'a0', 11: 'a1', 12: 'a2', 13: 'a3', 14: 'a4', 15: 'a5', 16: 'a6'}


def rname(v):
    return NAMES.get(v, f'({v} : Fin 32)')


def w(v):
    return f'0x{v & 0xFFFFFFFF:X}'


def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


ALU = {(0, 0): 'add', (0, 0x20): 'sub', (1, 0): 'sll', (2, 0): 'slt', (3, 0): 'sltu', (4, 0): 'xor',
       (5, 0): 'srl', (5, 0x20): 'sra', (6, 0): 'or', (7, 0): 'and', (0, 1): 'mul', (1, 1): 'mulh',
       (3, 1): 'mulhu'}
ALUI = {0: 'add', 2: 'slt', 3: 'sltu', 4: 'xor', 6: 'or', 7: 'and'}
BR = {0: 'beq', 1: 'bne', 4: 'blt', 5: 'bge', 6: 'bltu', 7: 'bgeu'}


def decode(code, off):
    """The instruction at `off` of `code` as a tuple of its kind, its fields,
    and its length in bytes, last. `lean` prints it for Lean.

    The kinds and their fields:
    ('alu', op, rd, rs1, rs2), ('alui', op, rd, rs1, imm), ('lw', rd, rs1, imm),
    and the same for 'lb', 'lh', 'lbu', and 'lhu', ('sw', rs1, rs2, imm) and the
    same for 'sb' and 'sh', ('lui', rd, imm), ('auipc', rd, imm),
    ('jalr', rd, rs1, imm), ('jal', rd, imm), ('br', op, rs1, rs2, imm).
    """
    lo = code[off] | (code[off + 1] << 8)
    if lo & 3 == 3:
        b = lo | (code[off + 2] << 16) | (code[off + 3] << 24)
        return _decode32(b) + (4,)
    return _decode16(lo) + (2,)


def _decode32(b):
    op = b & 0x7F
    rd, f3, rs1, rs2, f7 = (b >> 7) & 31, (b >> 12) & 7, (b >> 15) & 31, (b >> 20) & 31, b >> 25
    if op == 0x33:
        return ('alu', ALU[(f3, f7)], rd, rs1, rs2)
    if op == 0x13:
        if f3 == 1:
            return ('alui', 'sll', rd, rs1, rs2)
        if f3 == 5:
            return ('alui', 'srl' if f7 == 0 else 'sra', rd, rs1, rs2)
        return ('alui', ALUI[f3], rd, rs1, sext(b >> 20, 12))
    if op == 0x03:
        return ({0: 'lb', 1: 'lh', 2: 'lw', 4: 'lbu', 5: 'lhu'}[f3], rd, rs1, sext(b >> 20, 12))
    if op == 0x23:
        return ({0: 'sb', 1: 'sh', 2: 'sw'}[f3], rs1, rs2, sext(((b >> 25) << 5) | ((b >> 7) & 31), 12))
    if op == 0x37:
        return ('lui', rd, b & 0xFFFFF000)
    if op == 0x17:
        return ('auipc', rd, b & 0xFFFFF000)
    if op == 0x67:
        return ('jalr', rd, rs1, sext(b >> 20, 12))
    if op == 0x6F:
        imm = (((b >> 31) & 1) << 20) | (((b >> 12) & 0xFF) << 12) | (((b >> 20) & 1) << 11) | (((b >> 21) & 0x3FF) << 1)
        return ('jal', rd, sext(imm, 21))
    if op == 0x63:
        imm = (((b >> 31) & 1) << 12) | (((b >> 7) & 1) << 11) | (((b >> 25) & 0x3F) << 5) | (((b >> 8) & 0xF) << 1)
        return ('br', BR[f3], rs1, rs2, sext(imm, 13))
    raise ValueError(f'unknown instruction {b:08x}')


def _decode16(b):
    q, f3 = b & 3, (b >> 13) & 7
    rdp, rs2p = 8 + ((b >> 7) & 7), 8 + ((b >> 2) & 7)
    rd, rs2 = (b >> 7) & 31, (b >> 2) & 31
    imm6 = sext((((b >> 12) & 1) << 5) | ((b >> 2) & 31), 6)
    if q == 0:
        uimm = (((b >> 6) & 1) << 2) | (((b >> 10) & 7) << 3) | (((b >> 5) & 1) << 6)
        if f3 == 0:
            nz = (((b >> 6) & 1) << 2) | (((b >> 5) & 1) << 3) | (((b >> 11) & 3) << 4) | (((b >> 7) & 0xF) << 6)
            return ('alui', 'add', rs2p, 2, nz)
        if f3 == 2:
            return ('lw', rs2p, rdp, uimm)
        if f3 == 6:
            return ('sw', rdp, rs2p, uimm)
    if q == 1:
        if f3 == 0:
            return ('alui', 'add', rd, rd, imm6)
        if f3 == 2:
            return ('alui', 'add', rd, 0, imm6)
        if f3 == 3:
            if rd == 2:
                nz = sext((((b >> 12) & 1) << 9) | (((b >> 6) & 1) << 4) | (((b >> 5) & 1) << 6) |
                          (((b >> 3) & 3) << 7) | (((b >> 2) & 1) << 5), 10)
                return ('alui', 'add', 2, 2, nz)
            return ('lui', rd, (imm6 << 12) & 0xFFFFFFFF)
        if f3 == 4:
            f2 = (b >> 10) & 3
            sh = (((b >> 12) & 1) << 5) | ((b >> 2) & 31)
            if f2 == 0:
                return ('alui', 'srl', rdp, rdp, sh)
            if f2 == 1:
                return ('alui', 'sra', rdp, rdp, sh)
            if f2 == 2:
                return ('alui', 'and', rdp, rdp, imm6)
            return ('alu', ['sub', 'xor', 'or', 'and'][(b >> 5) & 3], rdp, rdp, rs2p)
        if f3 == 5:
            imm = (((b >> 12) & 1) << 11) | (((b >> 11) & 1) << 4) | (((b >> 9) & 3) << 8) | (((b >> 8) & 1) << 10) | \
                  (((b >> 7) & 1) << 6) | (((b >> 6) & 1) << 7) | (((b >> 3) & 7) << 1) | (((b >> 2) & 1) << 5)
            return ('jal', 0, sext(imm, 12))
        if f3 in (6, 7):
            imm = (((b >> 12) & 1) << 8) | (((b >> 10) & 3) << 3) | (((b >> 5) & 3) << 6) | (((b >> 3) & 3) << 1) | \
                  (((b >> 2) & 1) << 5)
            return ('br', 'beq' if f3 == 6 else 'bne', rdp, 0, sext(imm, 9))
    if q == 2:
        if f3 == 0:
            return ('alui', 'sll', rd, rd, (((b >> 12) & 1) << 5) | ((b >> 2) & 31))
        if f3 == 2:
            return ('lw', rd, 2, (((b >> 4) & 7) << 2) | (((b >> 12) & 1) << 5) | (((b >> 2) & 3) << 6))
        if f3 == 4:
            if (b >> 12) & 1 == 0:
                return ('jalr', 0, rd, 0) if rs2 == 0 else ('alu', 'add', rd, 0, rs2)
            return ('jalr', 1, rd, 0) if rs2 == 0 else ('alu', 'add', rd, rd, rs2)
        if f3 == 6:
            return ('sw', 2, rs2, (((b >> 9) & 0xF) << 2) | (((b >> 7) & 3) << 6))
    raise ValueError(f'unknown compressed instruction {b:04x}')


def lean(ins):
    """The `Instr` term that `fetchRel` returns for a decoded instruction."""
    k = ins[0]
    if k == 'alu':
        return f'.alu .{ins[1]} {rname(ins[2])} {rname(ins[3])} {rname(ins[4])}'
    if k == 'alui':
        return f'.aluImm .{ins[1]} {rname(ins[2])} {rname(ins[3])} {w(ins[4])}'
    if k in ('lb', 'lh', 'lw', 'lbu', 'lhu'):
        return f'.load .{k} {rname(ins[1])} {rname(ins[2])} {w(ins[3])}'
    if k in ('sb', 'sh', 'sw'):
        return f'.store .{k} {rname(ins[1])} {rname(ins[2])} {w(ins[3])}'
    if k in ('lui', 'auipc'):
        return f'.{k} {rname(ins[1])} {w(ins[2])}'
    if k == 'jalr':
        return f'.jalr {rname(ins[1])} {rname(ins[2])} {w(ins[3])}'
    if k == 'jal':
        return f'.jal {rname(ins[1])} {w(ins[2])}'
    if k == 'br':
        return f'.branch .{ins[1]} {rname(ins[2])} {rname(ins[3])} {w(ins[4])}'
    raise ValueError(ins)


def code_of(lean_src, name):
    """The bytes of `def NAMECode` (or `NAMEData`) in Bootloader.lean."""
    m = re.search(r'def %s : List Nat :=\s*\[([^\]]*)\]' % name, lean_src)
    return [int(x, 16) for x in m.group(1).replace('\n', '').split(',') if x.strip()]


def address_of(lean_src, name):
    return int(re.search(r'def %sAddress : Nat := (0x[0-9a-f]+)' % name, lean_src).group(1), 16)
