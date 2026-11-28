#!/usr/bin/env python3
"""Regenerates every fact that the proofs state about the bootloader image's
code from the extracted function bytes.

A fact about the image is a statement that `decide` checks against a
function's bytes, and its text follows from those bytes. Three kinds are
regenerated:

- Decode lemmas: `fetchRel CODE OFF = some (INSTR, LEN)` with a literal
  offset, in every proof file.
- Code chunks: the byte lists that long functions' decode lemmas fetch from,
  `def sv_cN : List Nat := [...]` with `sv_cN <+: List.drop K CODE` in
  `SvAt.lean`, and the `evcWN` windows of `EdVerifyDecode.lean`.
- Straight-line blocks: a literal `List BInstr`, by name or inline, in
  `blockEnd CODE OFF LIST = some END` with a literal offset, and the end
  offset.

The bytes come from `Image/Bootloader.lean`, which `extract-functions.py`
writes from the image, and `BootloaderReset.lean` beside it, or from
`Image/BootloaderV0.lean` for proofs that open
`C3.ImageV0`. Each fact keeps its offset, its chunk's offset and length, or
its block's instruction count, and gets its instructions or bytes from the
code there. A fact whose text already says what the code holds is left as it
is, so a fact written with `s0` or a decimal immediate keeps that spelling; a
fact that no longer holds is rewritten in the spelling `rv32dec.py` uses.
Statements with a variable offset, immediate, or code are not facts about
the image and are left alone.

`Sha256Rounds*.lean` is skipped, because `gen-sha256.py` writes it, and so
are the modules that `C3BootProofs/Pending.lean` imports, when that file
exists, which wait to be proved again against a changed function.

Usage: image-facts.py [--image BOOTLOADER_LEAN] [--check]

Run it from c3-boot-proofs/. It rewrites the files in place. A fact whose
code no longer has the instruction or the straight-line block it names
can't be regenerated: it keeps its text, and after the other facts are
rewritten, the script lists each such fact and each file that has one, and
exits 1. With `--check`, it rewrites nothing, lists the facts that differ,
and exits 1 if any do.
"""

import argparse
import glob
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
SKIP = re.compile(r'Sha256Rounds\d*\.lean$')

REGS = {'x0': 0, 'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4, 't0': 5, 't1': 6, 't2': 7,
        's0': 8, 's1': 9}
REGS.update({f'a{i}': 10 + i for i in range(8)})
REGS.update({f's{i}': 16 + i for i in range(2, 12)})
REGS.update({f't{i}': 25 + i for i in range(3, 7)})
NAMES = {0: 'x0', 1: 'ra', 2: 'sp', 10: 'a0', 11: 'a1', 12: 'a2', 13: 'a3', 14: 'a4', 15: 'a5',
         16: 'a6'}
M32 = 0xFFFFFFFF


def bits(w, hi, lo):
    return (w >> lo) % (1 << (hi + 1 - lo))


def sext(n, v):
    v &= (1 << n) - 1
    return (v - (1 << n) if v >> (n - 1) else v) & M32


def decode32(w):
    """`decode32` in Model/RV32.lean, as a tuple, or None."""
    op, rd, f3 = bits(w, 6, 0), bits(w, 11, 7), bits(w, 14, 12)
    rs1, rs2, f7 = bits(w, 19, 15), bits(w, 24, 20), bits(w, 31, 25)
    imm_i = sext(12, bits(w, 31, 20))
    imm_s = sext(12, bits(w, 31, 25) * 32 + bits(w, 11, 7))
    imm_b = sext(13, bits(w, 31, 31) * 4096 + bits(w, 7, 7) * 2048 + bits(w, 30, 25) * 32
                 + bits(w, 11, 8) * 2)
    imm_u = bits(w, 31, 12) * 4096
    imm_j = sext(21, bits(w, 31, 31) * 1048576 + bits(w, 19, 12) * 4096 + bits(w, 20, 20) * 2048
                 + bits(w, 30, 21) * 2)
    if op == 0x37:
        return ('lui', rd, imm_u)
    if op == 0x17:
        return ('auipc', rd, imm_u)
    if op == 0x6F:
        return ('jal', rd, imm_j)
    if op == 0x67:
        return ('jalr', rd, rs1, imm_i) if f3 == 0 else None
    if op == 0x63:
        o = {0: 'beq', 1: 'bne', 4: 'blt', 5: 'bge', 6: 'bltu', 7: 'bgeu'}.get(f3)
        return ('branch', o, rs1, rs2, imm_b) if o else None
    if op == 0x03:
        o = {0: 'lb', 1: 'lh', 2: 'lw', 4: 'lbu', 5: 'lhu'}.get(f3)
        return ('load', o, rd, rs1, imm_i) if o else None
    if op == 0x23:
        o = {0: 'sb', 1: 'sh', 2: 'sw'}.get(f3)
        return ('store', o, rs1, rs2, imm_s) if o else None
    if op == 0x13:
        o = {0: 'add', 2: 'slt', 3: 'sltu', 4: 'xor', 6: 'or', 7: 'and'}.get(f3)
        if o:
            return ('aluImm', o, rd, rs1, imm_i)
        if f3 == 1:
            return ('aluImm', 'sll', rd, rs1, rs2) if f7 == 0 else None
        if f3 == 5:
            o = {0: 'srl', 0x20: 'sra'}.get(f7)
            return ('aluImm', o, rd, rs1, rs2) if o else None
        return None
    if op == 0x33:
        o = {(0, 0): 'add', (0x20, 0): 'sub', (0, 1): 'sll', (0, 2): 'slt', (0, 3): 'sltu',
             (0, 4): 'xor', (0, 5): 'srl', (0x20, 5): 'sra', (0, 6): 'or', (0, 7): 'and',
             (1, 0): 'mul', (1, 1): 'mulh', (1, 2): 'mulhsu', (1, 3): 'mulhu', (1, 4): 'div',
             (1, 5): 'divu', (1, 6): 'rem', (1, 7): 'remu'}.get((f7, f3))
        return ('alu', o, rd, rs1, rs2) if o else None
    if op == 0x0F:
        if f3 == 0 and rd == 0 and rs1 == 0 and (bits(w, 31, 28) == 0 or w == 0x8330000F):
            return ('fence',)
    return None


def decode16(h):
    """`decode16` in Model/RV32.lean, as a tuple, or None."""
    op, f3, rd, rs2 = bits(h, 1, 0), bits(h, 15, 13), bits(h, 11, 7), bits(h, 6, 2)
    rdp, rs1p = 8 + bits(h, 4, 2), 8 + bits(h, 9, 7)
    ci = bits(h, 12, 12) * 32 + bits(h, 6, 2)
    cj = sext(12, bits(h, 12, 12) * 2048 + bits(h, 8, 8) * 1024 + bits(h, 10, 9) * 256
              + bits(h, 6, 6) * 128 + bits(h, 7, 7) * 64 + bits(h, 2, 2) * 32
              + bits(h, 11, 11) * 16 + bits(h, 5, 3) * 2)
    cb = sext(9, bits(h, 12, 12) * 256 + bits(h, 6, 5) * 64 + bits(h, 2, 2) * 32
              + bits(h, 11, 10) * 8 + bits(h, 4, 3) * 2)
    b12 = bits(h, 12, 12)
    if (op, f3) == (0, 0):
        imm = bits(h, 10, 7) * 64 + bits(h, 12, 11) * 16 + bits(h, 5, 5) * 8 + bits(h, 6, 6) * 4
        return ('aluImm', 'add', rdp, 2, imm) if imm else None
    if (op, f3) in ((0, 2), (0, 6)):
        off = bits(h, 5, 5) * 64 + bits(h, 12, 10) * 8 + bits(h, 6, 6) * 4
        return ('load', 'lw', rdp, rs1p, off) if f3 == 2 else ('store', 'sw', rs1p, rdp, off)
    if (op, f3) == (1, 0):
        return ('aluImm', 'add', rd, rd, sext(6, ci))
    if (op, f3) == (1, 1):
        return ('jal', 1, cj)
    if (op, f3) == (1, 2):
        return ('aluImm', 'add', rd, 0, sext(6, ci))
    if (op, f3) == (1, 3):
        if rd == 2:
            imm = (bits(h, 12, 12) * 512 + bits(h, 4, 3) * 128 + bits(h, 5, 5) * 64
                   + bits(h, 2, 2) * 32 + bits(h, 6, 6) * 16)
            return ('aluImm', 'add', 2, 2, sext(10, imm)) if imm else None
        return ('lui', rd, sext(18, ci * 4096)) if ci else None
    if (op, f3) == (1, 4):
        f2 = bits(h, 11, 10)
        if f2 in (0, 1):
            return None if b12 else ('aluImm', ('srl', 'sra')[f2], rs1p, rs1p, bits(h, 6, 2))
        if f2 == 2:
            return ('aluImm', 'and', rs1p, rs1p, sext(6, ci))
        if b12:
            return None
        return ('alu', ('sub', 'xor', 'or', 'and')[bits(h, 6, 5)], rs1p, rs1p, rdp)
    if (op, f3) == (1, 5):
        return ('jal', 0, cj)
    if (op, f3) in ((1, 6), (1, 7)):
        return ('branch', 'beq' if f3 == 6 else 'bne', rs1p, 0, cb)
    if (op, f3) == (2, 0):
        return None if b12 else ('aluImm', 'sll', rd, rd, bits(h, 6, 2))
    if (op, f3) == (2, 2):
        off = bits(h, 3, 2) * 64 + bits(h, 12, 12) * 32 + bits(h, 6, 4) * 4
        return ('load', 'lw', rd, 2, off) if rd else None
    if (op, f3) == (2, 4):
        if rs2 == 0:
            return ('jalr', b12, rd, 0) if rd else None
        return ('alu', 'add', rd, rd if b12 else 0, rs2)
    if (op, f3) == (2, 6):
        return ('store', 'sw', 2, rs2, bits(h, 8, 7) * 64 + bits(h, 12, 9) * 4)
    return None


def fetch(code, off):
    """`fetchRel code off` as (instruction, length), or None."""
    if off + 2 > len(code):
        return None
    lo = code[off] | code[off + 1] << 8
    if lo & 3 == 3:
        if off + 4 > len(code):
            return None
        ins = decode32(lo | code[off + 2] << 16 | code[off + 3] << 24)
        return (ins, 4) if ins else None
    ins = decode16(lo)
    return (ins, 2) if ins else None


def reg(r):
    return NAMES.get(r, f'({r} : Fin 32)')


def imm(v):
    return f'0x{v & M32:X}'


def render(ins):
    """The `Instr` term for a decoded instruction, as `rv32dec.lean` spells it."""
    k = ins[0]
    if k == 'fence':
        return '.fence'
    if k in ('alu', 'aluImm', 'load', 'store', 'branch'):
        last = reg(ins[4]) if k == 'alu' else imm(ins[4])
        return f'.{k} .{ins[1]} {reg(ins[2])} {reg(ins[3])} {last}'
    if k in ('lui', 'auipc', 'jal'):
        return f'.{k} {reg(ins[1])} {imm(ins[2])}'
    return f'.jalr {reg(ins[1])} {reg(ins[2])} {imm(ins[3])}'


BLOCK = {('aluImm',): 'aluImm', ('alu',): 'alu', ('lui',): 'lui', ('load', 'lw'): 'lw',
         ('load', 'lbu'): 'lbu', ('store', 'sw'): 'sw', ('store', 'sb'): 'sb'}


def to_block(ins):
    """The `BInstr` that stands for a decoded instruction, or None."""
    return BLOCK.get(ins[:1]) or BLOCK.get(ins[:2])


def render_block(ins):
    """The `BInstr` term for a decoded instruction that falls through."""
    b = to_block(ins)
    if b in ('aluImm', 'alu'):
        return render(ins)
    if b == 'lui':
        return f'.lui {reg(ins[1])} {imm(ins[2])}'
    return f'.{b} {reg(ins[2])} {reg(ins[3])} {imm(ins[4])}'


TOKEN = re.compile(r'\(\s*(\d+)\s*:\s*Fin 32\s*\)|\S+')


def tokens(text):
    return [m.group(1) and f'#{m.group(1)}' or m.group(0) for m in TOKEN.finditer(text)]


def p_reg(t):
    if t.startswith('#'):
        return int(t[1:]) % 32
    if t in REGS:
        return REGS[t]
    if t.isdigit():
        return int(t) % 32
    raise ValueError(t)


def p_imm(t):
    if re.fullmatch(r'0x[0-9A-Fa-f]+|\d+', t):
        return int(t, 0) & M32
    raise ValueError(t)


def parse(text):
    """The decoded tuple that an `Instr` term stands for, or None when the
    term isn't a literal."""
    t = tokens(text)
    try:
        k = t[0][1:]
        if k == 'fence' and len(t) == 1:
            return ('fence',)
        if k in ('alu', 'aluImm', 'load', 'store', 'branch') and len(t) == 5:
            last = p_reg(t[4]) if k == 'alu' else p_imm(t[4])
            return (k, t[1][1:], p_reg(t[2]), p_reg(t[3]), last)
        if k in ('lui', 'auipc', 'jal') and len(t) == 3:
            return (k, p_reg(t[1]), p_imm(t[2]))
        if k == 'jalr' and len(t) == 4:
            return (k, p_reg(t[1]), p_reg(t[2]), p_imm(t[3]))
    except (ValueError, IndexError):
        return None
    return None


def parse_block(text):
    """The decoded tuple that a `BInstr` term stands for, or None."""
    t = tokens(text)
    try:
        k = t[0][1:]
        if k in ('aluImm', 'alu'):
            return parse(text)
        if k == 'lui' and len(t) == 3:
            return ('lui', p_reg(t[1]), p_imm(t[2]))
        if k in ('lw', 'lbu') and len(t) == 4:
            return ('load', k, p_reg(t[1]), p_reg(t[2]), p_imm(t[3]))
        if k in ('sw', 'sb') and len(t) == 4:
            return ('store', k, p_reg(t[1]), p_reg(t[2]), p_imm(t[3]))
    except (ValueError, IndexError):
        return None
    return None


def byte_lists(src):
    return {m.group(1): [int(x, 0) for x in m.group(2).split(',') if x.strip()]
            for m in re.finditer(r'def (\w+) : List Nat :=\s*\[([^\]]*)\]', src)}


CHUNK = re.compile(r'(def (\w+) : List Nat :=\n  \[)([^\]]*)'
                   r'(\]\ntheorem \2_ok : \2 <\+: List\.drop (\w+) ([\w.]+) := by decide)')
WINDOW = re.compile(r'(def (\w+) : List Nat := \[)([^\]]*)(\]\ntheorem \2_eq : '
                    r'(?:\(([\w.]+)\.drop (\w+)\)\.take (\w+)|([\w.]+)\.drop (\w+)) = \2 )')
FETCH = re.compile(r'fetchRel ([\w.]+) (0x[0-9A-Fa-f]+|\d+) = some \(([^,\n]*), (\d+)\)')
LIST = r'\[[^\]]*\]|\((?:\(.*?\) :: )+\[\]\)'
BLOCK_DEF = re.compile(rf'def (\w+) : List BInstr :=\s*({LIST})')
BLOCK_USE = re.compile(rf'blockEnd ([\w.]+) (0x[0-9A-Fa-f]+|\d+) (\w+|{LIST}) = some '
                       r'(0x[0-9A-Fa-f]+|\d+)')
ELEM = re.compile(r'[^,\s](?:[^,]*[^,\s])?')
CONS = re.compile(r'\((.*?)\) :: ')


def chunk_rows(data):
    rows = [', '.join(f'0x{b:02x}' for b in data[i:i + 12]) for i in range(0, len(data), 12)]
    return ',\n    '.join(rows)


def spans(lst):
    """The spans of the terms in a `List BInstr` literal."""
    if lst.startswith('['):
        return [m.span() for m in ELEM.finditer(lst, 1, len(lst) - 1)]
    return [m.span(1) for m in CONS.finditer(lst, 1)]


def literal_block(lst):
    """The decoded tuples that a `List BInstr` literal stands for, or None."""
    out = [parse_block(lst[a:b]) for a, b in spans(lst)]
    return None if None in out else out


def rewrite_block(lst, want):
    out, at = [], 0
    for (a, b), ins in zip(spans(lst), want):
        out.append(lst[at:a])
        out.append(lst[a:b] if parse_block(lst[a:b]) == ins else render_block(ins))
        at = b
    return ''.join(out) + lst[at:]


def pending_paths():
    """The files of the modules that `C3BootProofs/Pending.lean` imports."""
    try:
        src = open(os.path.join(ROOT, 'C3BootProofs/Pending.lean')).read()
    except FileNotFoundError:
        return set()
    return {os.path.normpath(os.path.join(ROOT, *m.split('.')) + '.lean')
            for m in re.findall(r'^import (\S+)', src, re.M)}


class Facts:
    def __init__(self, image):
        self.cur = byte_lists(open(image).read())
        reset = os.path.join(os.path.dirname(image), 'BootloaderReset.lean')
        if os.path.exists(reset):
            self.cur.update(byte_lists(open(reset).read()))
        self.v0 = byte_lists(open(os.path.join(ROOT, 'C3BootProofs/Image/BootloaderV0.lean')).read())
        self.diffs = []
        self.errors = []
        self.stale = set()
        self.counts = {}

    def count(self, what):
        self.counts[what] = self.counts.get(what, 0) + 1

    def code(self, name, src, local):
        """The bytes that `name` denotes in a file, or None."""
        parts = name.split('.')
        base = parts[-1]
        if len(parts) == 1 and base in local:
            return local[base]
        if parts[:-1] in (['ImageV0'], ['C3', 'ImageV0']):
            return self.v0.get(base)
        if parts[:-1] in (['Image'], ['C3', 'Image']):
            return self.cur.get(base)
        if len(parts) > 1:
            return None
        if re.search(r'^open .*\bC3\.ImageV0\b', src, re.M) and base in self.v0:
            return self.v0[base]
        return self.cur.get(base)

    def fail(self, path, src, pos, msg):
        """Records a fact that can't be regenerated, which keeps its text."""
        rel = os.path.relpath(path, ROOT)
        self.errors.append(f'{rel}:{src.count(chr(10), 0, pos) + 1}: {msg}')
        self.stale.add(rel)

    def differs(self, path, src, pos, what):
        self.diffs.append(f'{os.path.relpath(path, ROOT)}:{src.count(chr(10), 0, pos) + 1}: {what}')

    def chunks(self, path, src):
        """Regenerates the code chunks of one file."""
        local = byte_lists(src)
        src = CHUNK.sub(lambda m: self.chunk(
            path, src, local, m, m.group(6), int(m.group(5), 0), len(local[m.group(2)]),
            chunk_rows), src)
        return WINDOW.sub(lambda m: self.chunk(
            path, src, local, m, m.group(5) or m.group(8), int(m.group(6) or m.group(9), 0),
            int(m.group(7), 0) if m.group(7) else None,
            lambda data: ', '.join(str(b) for b in data)), src)

    def chunk(self, path, src, local, m, name, k, n, spell):
        code = self.code(name, src, local)
        if code is None:
            self.fail(path, src, m.start(), f'no code {name}')
            return m.group(0)
        if n is None:
            n = len(code) - k
        if len(code) < k + n:
            self.fail(path, src, m.start(), f'{m.group(2)} runs past the end of {name}')
            return m.group(0)
        self.count('code chunks')
        text = spell(code[k:k + n])
        if text != m.group(3):
            self.differs(path, src, m.start(), m.group(2))
        return m.group(1) + text + m.group(4)

    def decodes(self, path, src):
        """Regenerates the decode lemmas of one file."""
        local = byte_lists(src)
        return FETCH.sub(lambda m: self.decode(path, src, local, m), src)

    def decode(self, path, src, local, m):
        code = self.code(m.group(1), src, local)
        old = parse(m.group(3))
        if code is None or old is None:
            self.count('decode statements left alone')
            return m.group(0)
        self.count('decode lemmas')
        got = fetch(code, int(m.group(2), 0))
        if got is None:
            self.fail(path, src, m.start(), f'no instruction at {m.group(2)}')
            return m.group(0)
        if got == (old, int(m.group(4))):
            return m.group(0)
        self.differs(path, src, m.start(), m.group(0))
        return f'fetchRel {m.group(1)} {m.group(2)} = some ({render(got[0])}, {got[1]})'

    def blocks(self, files):
        """Regenerates the straight-line block facts of all files. A named
        list can be defined in another file than its fact."""
        defs = {}
        for path, src in files.items():
            for m in BLOCK_DEF.finditer(src):
                defs.setdefault(m.group(1), []).append((path, m.group(2)))
        want = {}
        for path, src in files.items():
            local = byte_lists(src)
            files[path] = BLOCK_USE.sub(
                lambda m: self.block(path, src, local, defs, want, m), src)
        for (path, name), got in want.items():
            files[path] = BLOCK_DEF.sub(
                lambda d: d.group(0).replace(d.group(2), rewrite_block(d.group(2), got))
                if d.group(1) == name else d.group(0), files[path])

    def block(self, path, src, local, defs, want, m):
        lst, key = m.group(3), None
        if lst[0] not in '[(':
            where = [d for d in defs.get(lst, []) if d[0] == path] or defs.get(lst, [])
            if len(where) != 1:
                self.count('block facts left alone')
                return m.group(0)
            key, lst = (where[0][0], m.group(3)), where[0][1]
        code = self.code(m.group(1), src, local)
        old = literal_block(lst)
        if code is None or old is None:
            self.count('block facts left alone')
            return m.group(0)
        self.count('block facts')
        got, end = [], int(m.group(2), 0)
        for _ in old:
            ins = fetch(code, end)
            if ins is None or to_block(ins[0]) is None:
                self.fail(path, src, m.start(), f'{m.group(0)}: the code there is not '
                          f'{len(old)} straight-line instructions')
                return m.group(0)
            got.append(ins[0])
            end += ins[1]
        out = m.group(0)
        if got != old:
            self.differs(path, src, m.start(), m.group(0))
            if key is None:
                out = out.replace(lst, rewrite_block(lst, got), 1)
            elif want.setdefault(key, got) != got:
                self.fail(path, src, m.start(), f'{key[1]} stands for two blocks')
                return m.group(0)
        if int(m.group(4), 0) != end:
            self.differs(path, src, m.start(), f'end of {m.group(0)}')
            out = out[:out.rindex('some ') + 5] + imm(end)
        return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--image', default=os.path.join(ROOT, 'C3BootProofs/Image/Bootloader.lean'))
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    facts = Facts(args.image)
    pending = pending_paths()
    paths = sorted(p for p in glob.glob(os.path.join(ROOT, 'C3BootProofs/**/*.lean'), recursive=True)
                   if '/Image/' not in p and not SKIP.search(p)
                   and os.path.normpath(p) not in pending)
    old = {}
    for p in paths:
        with open(p) as f:
            old[p] = f.read()
    files = {p: facts.decodes(p, facts.chunks(p, s)) for p, s in old.items()}
    facts.blocks(files)
    for what, n in sorted(facts.counts.items()):
        print(f'{n:7d} {what}', file=sys.stderr)
    if pending:
        print(f'{len(pending):7d} pending files skipped', file=sys.stderr)
    for d in facts.diffs:
        print(d, file=sys.stderr)
    for e in facts.errors:
        print(e, file=sys.stderr)
    if facts.stale:
        print(f'{len(facts.stale)} files have facts that no longer hold:', file=sys.stderr)
        for s in sorted(facts.stale):
            print(f'  {s}', file=sys.stderr)
    if args.check:
        sys.exit(1 if facts.diffs or facts.errors else 0)
    for p in paths:
        if files[p] != old[p]:
            with open(p, 'w') as f:
                f.write(files[p])
    sys.exit(1 if facts.errors else 0)


if __name__ == '__main__':
    main()
