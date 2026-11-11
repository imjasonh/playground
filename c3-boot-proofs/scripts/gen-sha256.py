#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/Sha256Rounds*.lean, the proof that the rounds of
the compiled `sha2::sha256::compress256` compute FIPS 180-4's compression of
one block, from the function's bytes in C3BootProofs/Image/BootloaderV0.lean.

The rounds are 3,589 straight-line instructions. The script runs them in
Python on random inputs to name every value: a working variable after some
round, a schedule word, a round constant, a word of the result, or a stack
or table address. It cuts the instructions into chunks at points where
every live register and stack slot holds a named value, and writes one
theorem per chunk that steps through the chunk's instructions, from a short
window of the code, and proves each new named value equal to its definition
(after unfolding `Σ`, `Ch`, `Maj`, and the rotations into the forms the
compiler uses) with `ac_rfl`. The last theorem chains the chunks.
"""
import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rv32dec import decode, lean, rname, code_of, address_of  # noqa: E402

PROOFS = os.path.join(HERE, '..', 'C3BootProofs', 'Proofs')
SRC = open(os.path.join(HERE, '..', 'C3BootProofs', 'Image', 'BootloaderV0.lean')).read()
CODE = code_of(SRC, 'sha256CompressCode')
KADDR = address_of(SRC, 'shaK')
KBYTES = code_of(SRC, 'shaKData')
K = [int.from_bytes(bytes(KBYTES[i:i + 4]), 'little') for i in range(0, 256, 4)]
START, END = 0xA2, 0x2B64
O97 = 0xC09C
RLO, RLEN = 0x14, 0x58
M32 = 0xFFFFFFFF
SP, A0, A1, A2, A3, T0, T3 = 2, 10, 11, 12, 13, 5, 28
STATE_REGS = [24, 21, 25, 26, 18, 27, 22, 23]
FIELDS = 'abcdefgh'

# ---------------------------------------------------------------- instructions

def instructions():
    out, off = [], START
    while off < END:
        ins = decode(CODE, off)
        ln, ins = ins[-1], ins[:-1]
        if ins[0] == 'auipc' and ins[1] == T0:
            j = decode(CODE, off + 4)
            assert j[0] == 'jalr' and j[1] == T0 and j[2] == T0
            assert (off + ins[2] + j[3]) % 2 ** 32 == O97, hex(off)
            out.append((off, ('o97', ins[2], j[3]), 8))
            off += 8
            continue
        out.append((off, ins, ln))
        off += ln
    return out


SEQ = instructions()


def o97_semantics(r):
    a0 = (r[A0] | r[A1]) ^ (r[A2] | r[A3])
    t3 = r[T3]
    return {A0: a0, A1: ((t3 >> 17) | (t3 << 15)) & M32, A2: t3 >> 19, A3: (t3 << 13) & M32}


def alu(op, x, y):
    return {'add': x + y, 'sub': x - y, 'xor': x ^ y, 'or': x | y, 'and': x & y,
            'sll': x << (y & 31), 'srl': x >> (y & 31)}[op] & M32

# ------------------------------------------------------------------ reference

def rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & M32


def reference(H, W16):
    q = {}
    W = list(W16)
    for t in range(16, 64):
        x, y = W[t - 15], W[t - 2]
        W.append((W[t - 16] + (rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3)) + W[t - 7] +
                  (rotr(y, 17) ^ rotr(y, 19) ^ (y >> 10))) & M32)
    for t in range(64):
        q[('W', t)] = W[t]
    a, b, c, d, e, f, g, h = H
    q[('A', 0)], q[('A', -1)], q[('A', -2)], q[('A', -3)] = a, b, c, d
    q[('E', 0)], q[('E', -1)], q[('E', -2)], q[('E', -3)] = e, f, g, h
    for t in range(64):
        t1 = (h + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g & M32)) + K[t] + W[t]) & M32
        t2 = ((rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) & M32
        h, g, f, e, d, c, b, a = g, f, e, (d + t1) & M32, c, b, a, (t1 + t2) & M32
        q[('A', t + 1)] = a
        q[('E', t + 1)] = e
    for i, (x, y) in enumerate(zip(H, (a, b, c, d, e, f, g, h))):
        q[('OUT', i)] = (x + y) & M32
    return q

# ----------------------------------------------------------------- simulation

TRIALS = 6
random.seed(20261111)
FRAMES = [0x3FCD0000 + 0x100 * random.randrange(64) for _ in range(TRIALS)]
TPS = [random.getrandbits(32) for _ in range(TRIALS)]
STPS = [0x3FCC8000 + 0x40 * random.randrange(64) for _ in range(TRIALS)]
NBS = [random.getrandbits(32) for _ in range(TRIALS)]
HS = [[random.getrandbits(32) for _ in range(8)] for _ in range(TRIALS)]
WS = [[random.getrandbits(32) for _ in range(16)] for _ in range(TRIALS)]
REFS = [reference(HS[i], WS[i]) for i in range(TRIALS)]
FP = {}
for key in REFS[0]:
    FP.setdefault(tuple(r[key] for r in REFS), key)


def name_of(v):
    """The named quantity a vector of trial values is, or None."""
    if v in FP:
        return FP[v]
    d = {(v[i] - FRAMES[i]) & M32 for i in range(TRIALS)}
    if len(d) == 1:
        return ('F', d.pop())
    if v == tuple(STPS):
        return ('STP',)
    if v == tuple(NBS):
        return ('NB',)
    if v == tuple(TPS):
        return ('TP',)
    if len(set(v)) == 1:
        if v[0] == KADDR:
            return ('KA',)
        if v[0] in K:
            return ('K', K.index(v[0]))
        return ('C', v[0])
    return None


def simulate():
    """The trial values of every register before each instruction, after the
    last, and the final memory."""
    regs = [tuple([0] * TRIALS) for _ in range(32)]
    regs[SP] = tuple(FRAMES)
    regs[4] = tuple(TPS)
    for r, i in zip(STATE_REGS, range(8)):
        regs[r] = tuple(HS[t][i] for t in range(TRIALS))
    mem = [dict() for _ in range(TRIALS)]
    for t in range(TRIALS):
        F = FRAMES[t]
        for i in range(16):
            mem[t][F + 0x6C + 4 * i] = WS[t][i]
        mem[t][F + 0xC] = STPS[t]
        mem[t][F + 0x40] = NBS[t]
        for i in range(64):
            mem[t][KADDR + 4 * i] = K[i]
    before = []
    for off, ins, ln in SEQ:
        before.append(list(regs))
        k = ins[0]
        new = [list(x) for x in zip(*regs)]
        for t in range(TRIALS):
            r = new[t]
            if k == 'alu':
                r[ins[2]] = alu(ins[1], r[ins[3]], r[ins[4]])
            elif k == 'alui':
                r[ins[2]] = alu(ins[1], r[ins[3]], ins[4] & M32)
            elif k == 'lw':
                r[ins[1]] = mem[t][(r[ins[2]] + ins[3]) & M32]
            elif k == 'sw':
                mem[t][(r[ins[1]] + ins[3]) & M32] = r[ins[2]]
            elif k == 'lui':
                r[ins[1]] = ins[2]
            elif k == 'o97':
                for reg, val in o97_semantics(r).items():
                    r[reg] = val
                r[T0] = 0x1234 + t
            else:
                raise ValueError(ins)
            r[0] = 0
        regs = [tuple(new[t][j] for t in range(TRIALS)) for j in range(32)]
    final = [mem[t] for t in range(TRIALS)]
    return before, regs, final


BEFORE, AFTER_REGS, FINAL_MEM = simulate()
for i in range(8):
    assert tuple(FINAL_MEM[t][STPS[t] + 4 * i] for t in range(TRIALS)) == \
        tuple(REFS[t][('OUT', i)] for t in range(TRIALS)), 'the simulation disagrees with FIPS 180-4'

# ------------------------------------------------------------------- liveness

def uses(ins):
    """(registers read, registers written, slots read, slots written)."""
    k = ins[0]
    if k == 'alu':
        return {ins[3], ins[4]}, {ins[2]}, set(), set()
    if k == 'alui':
        return {ins[3]}, {ins[2]}, set(), set()
    if k == 'lw':
        return {ins[2]}, {ins[1]}, ({ins[3]} if ins[2] == SP else set()), set()
    if k == 'sw':
        return {ins[1], ins[2]}, set(), set(), ({ins[3]} if ins[1] == SP else set())
    if k == 'lui':
        return set(), {ins[1]}, set(), set()
    if k == 'o97':
        return {A0, A1, A2, A3, T3}, {A0, A1, A2, A3, T0}, set(), set()
    raise ValueError(ins)


def in_region(o):
    return RLO <= o < RLO + RLEN


LIVE = [None] * (len(SEQ) + 1)
live_r = {SP, 4} | set(STATE_REGS) | {19, 20, 9}
live_s = set()
LIVE[len(SEQ)] = (set(live_r), set(live_s))
for i in range(len(SEQ) - 1, -1, -1):
    rr, rw, sr, sw = uses(SEQ[i][1])
    live_r = (live_r - rw) | rr
    live_s = (live_s - sw) | {o for o in sr if in_region(o)}
    live_r.discard(0)
    LIVE[i] = (set(live_r), set(live_s))

# Slot contents before each instruction, as names.
SLOTS = []
slot_vals = {0x40: ('NB',)}
for i, (off, ins, ln) in enumerate(SEQ):
    SLOTS.append(dict(slot_vals))
    if ins[0] == 'sw' and ins[1] == SP:
        slot_vals[ins[3]] = name_of(BEFORE[i][ins[2]])


def cut_ok(i):
    regs = BEFORE[i] if i < len(SEQ) else AFTER_REGS
    lr, ls = LIVE[i]
    return all(name_of(regs[r]) is not None for r in lr) and all(SLOTS[i].get(o) is not None for o in ls)


def choose_cuts(target=110):
    cuts = [0]
    good = [i for i in range(len(SEQ)) if cut_ok(i)]
    while True:
        last = cuts[-1]
        nxt = [g for g in good if last < g <= last + target]
        if len(SEQ) - last <= target:
            break
        cuts.append(nxt[-1] if nxt else min(g for g in good if g > last))
    cuts.append(len(SEQ))
    return cuts


CUTS = choose_cuts()

# ------------------------------------------------------------------- emission

def term(q):
    """The Lean term for a named or wrapped value."""
    if not isinstance(q, tuple):
        return q
    k = q[0]
    if k in ('A', 'E'):
        s = q[1]
        if s <= 0:
            return 'hv.' + ('abcd' if k == 'A' else 'efgh')[-s]
        return f'(vsW w hv {s}).{"a" if k == "A" else "e"}'
    if k == 'W':
        return f'w {q[1]}'
    if k == 'OUT':
        f = FIELDS[q[1]]
        return f'hv.{f} + (vsW w hv 64).{f}'
    if k == 'F':
        return 'F' if q[1] == 0 else f'F + BitVec.ofNat 32 0x{q[1]:X}'
    if k == 'STP':
        return 'stp'
    if k == 'NB':
        return 'nb'
    if k == 'TP':
        return 'tp0'
    if k == 'KA':
        return 'BitVec.ofNat 32 shaKAddress'
    if k == 'K':
        return f'ktAt {q[1]}'
    if k == 'C':
        return f'(0x{q[1]:X} : Word)'
    if k == 'ROT':
        return f'rotrW ({term(q[1])}) {q[2]}'
    if k == 'SHR3':
        return f'shr3 ({term(q[1])})'
    if k == 'SHR10':
        return f'shr10 ({term(q[1])})'
    if k == 'SRL':
        return f'({term(q[1])}) >>> {q[2]}'
    if k == 'SLL':
        return f'({term(q[1])}) <<< {q[2]}'
    raise ValueError(q)


def vs_lem(kind, s):
    fn = 'vs_a' if kind == 'A' else 'vs_e'
    if s <= 4:
        return f'{fn}_{s - 1} w hv'
    return f'{fn}_ge4 w hv {s} {s - 1} {s - 2} {s - 3} {s - 4} rfl'


def sched_lem(t):
    return f'sched_step hw {t} {t - 2} {t - 7} {t - 15} {t - 16} rfl'


SEPR = 'Sep (F + BitVec.ofNat 32 0x14) 0x58'


class Chunk:
    def __init__(self, c, i0, i1):
        self.c, self.i0, self.i1 = c, i0, i1
        self.S = SEQ[i0][0]
        self.L = (SEQ[i1][0] if i1 < len(SEQ) else END) - self.S
        self.last = i1 == len(SEQ)
        self.out = []
        self.k = 0
        self.kinds = {}
        self.regs = {}      # reg -> (val_repr, step, fact)
        self.local = {}     # local var -> (children, name or None)
        self.stores = []    # (step, base, offset, memname)
        self.mem = 'M'
        self.fr = 'fr'
        self.fr2 = None

    def w(self, s):
        self.out.append(s)

    def code(self):
        return f'(cwOf {self.fr})' if self.fr2 is None else f'(cwOf2 {self.fr2})'

    def val(self, r):
        return self.regs[r][0]

    def get(self, r, k=None):
        if k is None:
            k = self.k
        v, j, f = self.regs[r]

        t = f
        for i in range(j + 1, k + 1):
            kd = self.kinds[i]
            if kd[0] == 'store':
                t = f'(reg_step_sw u{i} {t})'
            elif kd[0] == 'o97':
                t = f'((k97_{i} {rname(r)} rfl).trans {t})'
            else:
                t = f'(reg_step_ne u{i} rfl {t})'
        return t

    def refresh(self, rs, force=False):
        for r in rs:
            if r == 0 or r not in self.regs:
                continue
            v, j, f = self.regs[r]
            if (force and j < self.k) or (self.k - j >= 12):
                nm = f'g{r}_{self.k}'
                self.w(f'  have {nm} : reg n{self.k} {rname(r)} = {term(v)} := {self.get(r)}')
                self.regs[r] = (v, self.k, nm)

    def slot_read(self, o):
        t = f'm{o:x}'
        for step, base, off, _ in self.stores:
            if base == 'F' and off == o:
                t = f'(load_store_eq hM{step})'
            elif base == 'F':
                t = f'(load_store_ne hM{step} rfl {t})'
            else:
                t = f'(load_store_stp_slot env hM{step} rfl {t})'
        return t

    def state_read(self, o):
        t = None
        for step, base, off, _ in self.stores:
            assert base == 'STP'
            if off == o:
                t = f'(load_store_eq hM{step})'
            elif t is not None:
                t = f'(load_store_ne hM{step} rfl {t})'
        if t is None:
            raise ValueError(f'no store to the state at {o:#x}')
        return t

    def name_value(self, k, rd, nm, name):
        fact = f'(reg_step_eq u{k} rfl)'
        if name is not None and name[0] in ('A', 'E', 'W', 'OUT'):
            order, seen = [], set()
            queue = [nm]
            while queue:
                x = queue.pop(0)
                if x in seen:
                    continue
                seen.add(x)
                order.append(x)
                for ch in self.local[x][0]:
                    if not isinstance(ch, tuple) and self.local[ch][1] is None:
                        queue.append(ch)
            rws = [f'← hn_{x}' for x in order]
            if name[0] == 'W':
                t = name[1]
                rws += [sched_lem(t), 's0_fold', 's1_fold']
            elif name[0] == 'A':
                s = name[1]
                rws += [vs_lem('A', s), 'bigSigma1_w', 'bigSigma0_w', 'ch_mask', 'Sha256.maj_alt']
                if s == 63:
                    rws += [sched_lem(62), 's0_fold', 's1_fold']
            elif name[0] == 'E':
                s = name[1]
                rws += [vs_lem('E', s), 'bigSigma1_w', 'ch_mask']
                if s == 63:
                    rws += [sched_lem(62), 's0_fold', 's1_fold']
            elif name[0] == 'OUT':
                i = name[1]
                if i == 0:
                    rws += [vs_lem('A', 64), sched_lem(63), 's0_fold', 's1_fold', 'bigSigma1_w',
                            'bigSigma0_w', 'ch_mask', 'Sha256.maj_alt']
                elif i == 4:
                    rws += [vs_lem('E', 64), sched_lem(63), 's0_fold', 's1_fold', 'bigSigma1_w', 'ch_mask']
                else:
                    rws += [f'vs64_{FIELDS[i]}']
            self.w(f'  have eq_{nm} : {nm} = {term(name)} := by')
            self.w(f'    rw [{", ".join(rws)}]; all_goals ac_rfl')
            self.regs[rd] = (name, k, f'({fact}.trans eq_{nm})')
            self.local[nm] = (self.local[nm][0], name)
        else:
            self.regs[rd] = (nm, k, fact)

    def step(self, idx):
        off, ins, ln = SEQ[idx]
        rel = off - self.S
        nxt = rel + ln
        kd = ins[0]
        p = f's{self.c}'
        if self.k > 0 and self.k % 16 == 0:
            self.refresh(LIVE[idx][0])
        if kd == 'o97':
            self.refresh([A0, A1, A2, A3, T3], force=True)
        else:
            rr, _, _, _ = uses(ins)
            self.refresh(rr, force=True)
        self.k += 1
        k = self.k
        pv = 's' if k == 1 else f'u{k - 1}.self'
        trial = BEFORE[idx + 1] if idx + 1 < len(SEQ) else AFTER_REGS
        if kd == 'alu' and ins[1] == 'add' and ins[3] == 0:
            rd, rs = ins[2], ins[4]
            self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_mv (off\' := 0x{nxt:X}) {pv} {self.code()} {p}_at_{rel:x} rfl {self.get(rs, k - 1)}')
            self.kinds[k] = ('write', rd)
            self.regs[rd] = (self.val(rs), k, f'(reg_step_eq u{k} rfl)')
            return
        if kd == 'alu' and ins[1] == 'or':
            rd, r1, r2 = ins[2], ins[3], ins[4]
            a, b = self.val(r1), self.val(r2)
            if a[0] == 'SRL' and b[0] == 'SLL':
                assert a[1] == b[1] and a[2] + b[2] == 32
                base, r, l, fn = a[1], a[2], b[2], 'sha_or_lr'
            else:
                assert a[0] == 'SLL' and b[0] == 'SRL' and a[1] == b[1] and a[2] + b[2] == 32
                base, l, r, fn = a[1], a[2], b[2], 'sha_or_rl'
            self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := {fn} (off\' := 0x{nxt:X}) (r := {r}) (l := {l}) {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(r1, k - 1)} {self.get(r2, k - 1)}')
            self.kinds[k] = ('write', rd)
            self.regs[rd] = (('ROT', base, r), k, f'(reg_step_eq u{k} rfl)')
            return
        if kd == 'alu':
            op, rd, r1, r2 = ins[1], ins[2], ins[3], ins[4]
            a, b = self.val(r1), self.val(r2)
            nm = f'v{k}'
            self.w(f'  obtain ⟨n{k}, {nm}, d{k}, hn_{nm}, u{k}⟩ := sha_{op} (off\' := 0x{nxt:X}) {pv} {self.code()} {p}_at_{rel:x} rfl {self.get(r1, k - 1)} {self.get(r2, k - 1)}')
            self.local[nm] = ([a, b], None)
            self.kinds[k] = ('write', rd)
            self.name_value(k, rd, nm, name_of(trial[rd]))
            return
        if kd == 'alui':
            op, rd, rs, imm = ins[1], ins[2], ins[3], ins[4]
            name = name_of(trial[rd])
            if rs == 0:
                self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_li (off\' := 0x{nxt:X}) {pv} {self.code()} {p}_at_{rel:x} rfl')
                self.kinds[k] = ('write', rd)
                self.regs[rd] = (('C', imm & M32), k, f'(reg_step_eq u{k} rfl)')
                return
            if op == 'add':
                assert name is not None and name[0] in ('F', 'KA')
                self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_addi_c (off\' := 0x{nxt:X}) (c := {term(name)}) {pv} {self.code()} {p}_at_{rel:x} rfl {self.get(rs, k - 1)} rfl')
                self.kinds[k] = ('write', rd)
                self.regs[rd] = (name, k, f'(reg_step_eq u{k} rfl)')
                return
            a = self.val(rs)
            if op == 'srl' and imm == 3:
                self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_shr3 (off\' := 0x{nxt:X}) {pv} {self.code()} {p}_at_{rel:x} rfl {self.get(rs, k - 1)}')
                self.kinds[k] = ('write', rd)
                self.regs[rd] = (('SHR3', a), k, f'(reg_step_eq u{k} rfl)')
                return
            if op == 'srl' and imm == 10:
                self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_shr10 (off\' := 0x{nxt:X}) {pv} {self.code()} {p}_at_{rel:x} rfl {self.get(rs, k - 1)}')
                self.kinds[k] = ('write', rd)
                self.regs[rd] = (('SHR10', a), k, f'(reg_step_eq u{k} rfl)')
                return
            if op == 'srl':
                self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_srl (off\' := 0x{nxt:X}) (k := {imm}) {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rs, k - 1)}')
                self.kinds[k] = ('write', rd)
                self.regs[rd] = (('SRL', a, imm), k, f'(reg_step_eq u{k} rfl)')
                return
            if op == 'sll':
                self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_sll (off\' := 0x{nxt:X}) (k := {imm}) {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rs, k - 1)}')
                self.kinds[k] = ('write', rd)
                self.regs[rd] = (('SLL', a, imm), k, f'(reg_step_eq u{k} rfl)')
                return
            if op == 'xor' and imm == -1:
                nm = f'v{k}'
                self.w(f'  obtain ⟨n{k}, {nm}, d{k}, hn_{nm}, u{k}⟩ := sha_not (off\' := 0x{nxt:X}) {pv} {self.code()} {p}_at_{rel:x} rfl {self.get(rs, k - 1)}')
                self.local[nm] = ([a], None)
                self.kinds[k] = ('write', rd)
                self.name_value(k, rd, nm, name)
                return
            raise ValueError(ins)
        if kd == 'lw':
            rd, rb, o = ins[1], ins[2], ins[3]
            base = self.val(rb)
            if base == ('F', 0):
                if in_region(o):
                    content = SLOTS[idx][o]
                    self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_lw_slot (off\' := 0x{nxt:X}) (o := 0x{o:X}) env {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rb, k - 1)} {self.slot_read(o)}')
                elif o == 0xC:
                    content = ('STP',)
                    self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_lw_stp (off\' := 0x{nxt:X}) env {self.fr} {pv} {self.code()} {p}_at_{rel:x} rfl {self.get(rb, k - 1)}')
                elif 0x6C <= o < 0xAC:
                    i = (o - 0x6C) // 4
                    content = ('W', i)
                    self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_lw_w (off\' := 0x{nxt:X}) (o := 0x{o:X}) (i := {i}) env {self.fr} hWin {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rb, k - 1)}')
                else:
                    raise ValueError(hex(o))
            elif base == ('KA',):
                t = o // 4
                content = ('K', t)
                self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_lw_k (off\' := 0x{nxt:X}) (t := {t}) env {self.fr} {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rb, k - 1)}')
            else:
                raise ValueError((hex(off), base))
            self.kinds[k] = ('write', rd)
            self.regs[rd] = (content, k, f'(reg_step_eq u{k} rfl)')
            return
        if kd == 'sw':
            rb, rs, o = ins[1], ins[2], ins[3]
            base = self.val(rb)
            if base == ('F', 0):
                assert self.fr2 is None
                self.w(f'  obtain ⟨n{k}, M{k}, d{k}, hM{k}, F{k}, u{k}⟩ := sha_sw_frame (off\' := 0x{nxt:X}) (o := 0x{o:X}) env {self.fr} {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rb, k - 1)} {self.get(rs, k - 1)}')
                self.fr = f'F{k}'
                b = 'F'
            elif base == ('STP',):
                if self.fr2 is None:
                    self.w(f'  obtain ⟨n{k}, M{k}, d{k}, hM{k}, F{k}, u{k}⟩ := sha_sw_stp0 (off\' := 0x{nxt:X}) (o := 0x{o:X}) env {self.fr} {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rb, k - 1)} {self.get(rs, k - 1)}')
                else:
                    self.w(f'  obtain ⟨n{k}, M{k}, d{k}, hM{k}, F{k}, u{k}⟩ := sha_sw_stp (off\' := 0x{nxt:X}) (o := 0x{o:X}) env {self.fr2} {pv} {self.code()} {p}_at_{rel:x} rfl rfl {self.get(rb, k - 1)} {self.get(rs, k - 1)}')
                self.fr2 = f'F{k}'
                b = 'STP'
            else:
                raise ValueError((hex(off), base))
            self.stores.append((k, b, o, f'M{k}'))
            self.mem = f'M{k}'
            self.kinds[k] = ('store',)
            return
        if kd == 'o97':
            a0, a1, a2, a3, y = (self.val(r) for r in (A0, A1, A2, A3, T3))
            assert a0 == ('SRL', a0[1], 7) and a1 == ('SLL', a0[1], 25) and a2 == ('SRL', a0[1], 18) and a3 == ('SLL', a0[1], 14)
            x = a0[1]
            nm = f'v{k}'
            self.w(f'  obtain ⟨n{k}, {nm}, d{k}, hn_{nm}, u{k}, r97a0_{k}, r97a1_{k}, r97a2_{k}, r97a3_{k}, k97_{k}⟩ := sha_o97_rot {pv} {self.code()} (cw97 {self.fr}) {p}_at_{rel:x} {p}_at_{rel + 4:x} rfl env.hP rfl {self.get(A0, k - 1)} {self.get(A1, k - 1)} {self.get(A2, k - 1)} {self.get(A3, k - 1)} {self.get(T3, k - 1)}')
            self.local[nm] = ([x], None)
            self.kinds[k] = ('o97',)
            self.regs[A0] = (nm, k, f'r97a0_{k}')
            self.regs[A1] = (('ROT', y, 17), k, f'r97a1_{k}')
            self.regs[A2] = (('SRL', y, 19), k, f'r97a2_{k}')
            self.regs[A3] = (('SLL', y, 13), k, f'r97a3_{k}')
            self.regs.pop(T0, None)
            return
        if kd == 'lui':
            rd, imm = ins[1], ins[2]
            self.w(f'  obtain ⟨n{k}, d{k}, u{k}⟩ := sha_lui (off\' := 0x{nxt:X}) {pv} {self.code()} {p}_at_{rel:x} rfl')
            self.kinds[k] = ('write', rd)
            self.regs[rd] = (('C', imm), k, f'(reg_step_eq u{k} rfl)')
            return
        raise ValueError(ins)


def interface(i):
    """The live registers and stack slots before instruction i, with names."""
    regs = BEFORE[i] if i < len(SEQ) else AFTER_REGS
    lr, ls = LIVE[i]
    slots = SLOTS[i] if i < len(SEQ) else slot_vals
    return [(r, name_of(regs[r])) for r in sorted(lr)], [(o, slots[o]) for o in sorted(ls)]


BINDERS = ('{M0 M : Word → BitVec 8} {P F stp nb tp0 : Word} {w : Nat → Word} {hv : Sha256.V8} {n : Machine}\n'
           '    (env : ShaEnv M0 P F stp) (hw : ShaSched w)\n'
           '    (hWin : ∀ i, i < 16 → memLoad32 M0 (F + BitVec.ofNat 32 (0x6C + 4 * i)) = w i)\n')


def emit_chunk(c, i0, i1):
    ch = Chunk(c, i0, i1)
    rs_in, sl_in = interface(i0)
    rs_out, sl_out = interface(i1)
    for r, nm in rs_in:
        ch.regs[r] = (nm, 0, f'r{r}')
    win = CODE[ch.S:ch.S + ch.L]
    head = []
    rows = [', '.join(f'0x{b:02x}' for b in win[j:j + 16]) for j in range(0, len(win), 16)]
    head.append(f'def shaW{c} : List Nat :=\n  [' + ',\n   '.join(rows) + ']')
    head.append('')
    for idx in range(i0, i1):
        o, ins, ln = SEQ[idx]
        rel = o - ch.S
        if ins[0] == 'o97':
            head.append(f'theorem s{c}_at_{rel:x} : fetchRel shaW{c} 0x{rel:X} = some (.auipc (5 : Fin 32) 0x{ins[1] & M32:X}, 4) := by decide')
            head.append(f'theorem s{c}_at_{rel + 4:x} : fetchRel shaW{c} 0x{rel + 4:X} = some (.jalr (5 : Fin 32) (5 : Fin 32) 0x{ins[2] & M32:X}, 4) := by decide')
        else:
            head.append(f'theorem s{c}_at_{rel:x} : fetchRel shaW{c} 0x{rel:X} = some ({lean(ins)}, {ln}) := by decide')
    for idx in range(i0, i1):
        ch.step(idx)
    K = ch.k
    hyps = [f'(fr : ∀ x, {SEPR} x 1 → M x = M0 x)', f'(s : St M (P + BitVec.ofNat 32 0x{ch.S:X}) n 0 (reg n))']
    hyps += [f'(r{r} : reg n {rname(r)} = {term(nm)})' for r, nm in rs_in]
    hyps += [f'(m{o:x} : memLoad32 M (F + BitVec.ofNat 32 0x{o:X}) = {term(nm)})' for o, nm in sl_in]
    frame = f'(∀ x, {SEPR} x 1 → Sep stp 32 x 1 → M\' x = M0 x)' if ch.last else f'(∀ x, {SEPR} x 1 → M\' x = M0 x)'
    concl = ['Steps n n\'', f'St M\' (P + BitVec.ofNat 32 0x{ch.S:X}) n\' 0x{ch.L:X} (reg n\')', frame]
    concl += [f'reg n\' {rname(r)} = {term(nm)}' for r, nm in rs_out]
    concl += [f'memLoad32 M\' (F + BitVec.ofNat 32 0x{o:X}) = {term(nm)}' for o, nm in sl_out]
    proofs = []
    for r, nm in rs_out:
        v = ch.regs[r][0]
        assert v == nm, (c, r, v, nm)
        proofs.append(ch.get(r))
    for o, nm in sl_out:
        proofs.append(ch.slot_read(o))
    if ch.last:
        concl += [f'memLoad32 M\' (stp + BitVec.ofNat 32 0x{4 * i:X}) = {term(("OUT", i))}' for i in range(8)]
        proofs += [ch.state_read(4 * i) for i in range(8)]
    chain = '(.refl _)'
    for k in range(K, 0, -1):
        chain = f'(Steps.trans d{k} {chain})' if ch.kinds[k][0] == 'o97' else f'(.cons d{k} {chain})'
    final_fr = ch.fr2 if ch.last else ch.fr
    lines = list(head)
    lines.append('')
    lines.append('set_option maxHeartbeats 0 in')
    lines.append('set_option maxRecDepth 200000 in')
    lines.append(f'theorem sha_c{c} ' + BINDERS + '    ' + '\n    '.join(hyps) + ' :')
    lines.append('    ∃ n\' M\', ' + ' ∧\n      '.join(concl) + ' := by')
    lines.append(f'  have cwOf : ∀ {{M\' : Word → BitVec 8}}, (∀ x, {SEPR} x 1 → M\' x = M0 x) →')
    lines.append(f'      CodeIn M\' (P + BitVec.ofNat 32 0x{ch.S:X}) shaW{c} := fun h => env.win h rfl (by decide)')
    if ch.last:
        lines.append(f'  have cwOf2 : ∀ {{M\' : Word → BitVec 8}}, (∀ x, {SEPR} x 1 → Sep stp 32 x 1 → M\' x = M0 x) →')
        lines.append(f'      CodeIn M\' (P + BitVec.ofNat 32 0x{ch.S:X}) shaW{c} := fun h => env.win2 h rfl (by decide)')
    if any(SEQ[idx][1][0] == 'o97' for idx in range(i0, i1)):
        lines.append(f'  have cw97 : ∀ {{M\' : Word → BitVec 8}}, (∀ x, {SEPR} x 1 → M\' x = M0 x) →')
        lines.append(f'      CodeIn M\' (P + 0xC09C) shaSigma1PartCode := fun h => env.out97 h')
    lines += ch.out
    lines.append(f'  exact ⟨n{K}, {ch.mem}, {chain}, u{K}.self, {final_fr},')
    lines.append('    ' + ',\n    '.join(proofs) + '⟩')
    return '\n'.join(lines), rs_in, sl_in, rs_out, sl_out, ch


def main():
    chunks = [emit_chunk(c, CUTS[c], CUTS[c + 1]) for c in range(len(CUTS) - 1)]
    files = {}
    per = 8
    nfiles = (len(chunks) + per - 1) // per
    for f in range(nfiles):
        body = '\n\n'.join(x[0] for x in chunks[f * per:(f + 1) * per])
        files[f'Sha256Rounds{f}.lean'] = (
            f'import C3BootProofs.Proofs.ShaSupport\n\n/-! # SHA-256 rounds, part {f}\n\n'
            'Generated by `scripts/gen-sha256.py`; do not edit.\n-/\n\n'
            'namespace C3.RV32\n\nopen C3.ImageV0\n\nset_option maxRecDepth 20000\nset_option linter.unusedVariables false\n\n' + body + '\n\nend C3.RV32\n')
    L = []
    w = L.append
    rs0, sl0 = interface(0)
    rsE, slE = interface(len(SEQ))
    w('set_option maxHeartbeats 0 in')
    w('set_option maxRecDepth 200000 in')
    w('/-- **The rounds of the compiled SHA-256 compression function.** From 0xA2,')
    w('with the working variables in `s8`, `s5`, `s9`, `s10`, `s2`, `s11`, `s6`, and `s7`,')
    w('the schedule\'s first 16 words in the frame, and the next block\'s address at')
    w('`sp + 0x40`, they reach 0x2B64 with each register and each word at `stp`')
    w('holding a word of the result. -/')
    w('theorem sha_rounds ' + BINDERS + f'    (fr : ∀ x, {SEPR} x 1 → M x = M0 x) (s : St M P n 0xA2 (reg n))')
    for r, nm in rs0:
        w(f'    (r{r} : reg n {rname(r)} = {term(nm)})')
    for o, nm in sl0:
        w(f'    (m{o:x} : memLoad32 M (F + BitVec.ofNat 32 0x{o:X}) = {term(nm)})')
    concl = ['Steps n n\'', 'St M\' P n\' 0x2B64 (reg n\')', f'(∀ x, {SEPR} x 1 → Sep stp 32 x 1 → M\' x = M0 x)']
    concl += [f'reg n\' {rname(r)} = {term(nm)}' for r, nm in rsE]
    concl += [f'memLoad32 M\' (stp + BitVec.ofNat 32 0x{4 * i:X}) = {term(("OUT", i))}' for i in range(8)]
    w('    : ∃ n\' M\', ' + ' ∧\n      '.join(concl) + ' := by')
    prev_s = '(St.rebase0 s)'
    prev_r = {r: f'r{r}' for r, _ in rs0}
    prev_m = {o: f'm{o:x}' for o, _ in sl0}
    steps = []
    fr = 'fr'
    for c, (text, rs_in, sl_in, rs_out, sl_out, ch) in enumerate(chunks):
        args = ' '.join([prev_r[r] for r, _ in rs_in] + [prev_m[o] for o, _ in sl_in])
        outs = [f'q{c}_{r}' for r, _ in rs_out] + [f'p{c}_{o:x}' for o, _ in sl_out]
        extra = [f'st{c}_{i}' for i in range(8)] if ch.last else []
        pat = ', '.join([f'n{c}', f'M{c}', f'c{c}', f's{c}', f'fr{c}'] + outs + extra)
        w(f'  obtain ⟨{pat}⟩ := sha_c{c} env hw hWin {fr} {prev_s} {args}')
        nxt = ch.S + ch.L
        prev_s = f'(St.shift s{c} (s := 0x{ch.S:X}) (s\' := 0x{nxt:X}) (by decide))'
        prev_r = {r: f'q{c}_{r}' for r, _ in rs_out}
        prev_m = {o: f'p{c}_{o:x}' for o, _ in sl_out}
        fr = f'fr{c}'
        steps.append(f'c{c}')
    last = len(chunks) - 1
    chain = steps[-1]
    for s_ in reversed(steps[:-1]):
        chain = f'{s_}.trans ({chain})'
    facts = [f'q{last}_{r}' for r, _ in rsE] + [f'st{last}_{i}' for i in range(8)]
    w(f'  exact ⟨n{last}, M{last}, {chain}, St.unbase s{last}, fr{last}, ' + ', '.join(facts) + '⟩')
    files['Sha256Rounds.lean'] = (
        '\n'.join(f'import C3BootProofs.Proofs.Sha256Rounds{f}' for f in range(nfiles)) +
        '\n\n/-! # The rounds of the compiled SHA-256 compression function\n\n'
        'Generated by `scripts/gen-sha256.py`; do not edit.\n-/\n\nnamespace C3.RV32\n\nopen C3.ImageV0\n\n' +
        '\n'.join(L) + '\n\nend C3.RV32\n')
    for name, text in files.items():
        with open(os.path.join(PROOFS, name), 'w') as fh:
            fh.write(text)


if __name__ == '__main__':
    main()
