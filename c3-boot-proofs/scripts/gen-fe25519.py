#!/usr/bin/env python3
"""Writes the straight-line proofs of curve25519_dalek's 32-bit field
arithmetic: C3BootProofs/Proofs/FeReduceBody.lean.

For a block of a decoded function, it steps every instruction with a fresh
name for its result, turns each result into a natural-number fact, and runs
the block and the Rust source side by side on random inputs to find which
words hold each value the Rust code computes (its low word, and its high
word when the code keeps one). For each Rust value it writes one `omega`
step from the facts of the instructions between that value and the values
it is computed from. Run it from c3-boot-proofs/ after Fe25519Decode.lean
changes; CI checks that the committed file matches.
"""
import os, random, re, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
NAMES = {'x0': 0, 'ra': 1, 'sp': 2, 'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17}
LEAN = {v: k for k, v in NAMES.items()}


def addr(key):
    """The Lean address of a slot (base, offset)."""
    return f'{key[0]} + 0x{key[1]:X}'


def kname(key):
    """A slot's suffix in hypothesis names: the offset, after the base unless it is `F`."""
    return f'{key[1]:X}' if key[0] == 'F' else f'{key[0]}{key[1]:X}'


def rv(cur, r):
    """The Lean value of register `r` in `cur`: x0 reads as 0."""
    return '0' if r == 0 else cur.get(r)


def lreg(r):
    return LEAN.get(r, f'({r} : Fin 32)')


def reg(s):
    s = s.strip()
    m = re.match(r'\((\d+) : Fin 32\)', s)
    return int(m.group(1)) if m else NAMES[s]


def toks(s):
    out, d, cur = [], 0, ''
    for ch in s:
        if ch == '(':
            d += 1
        if ch == ')':
            d -= 1
        if ch == ' ' and d == 0:
            if cur:
                out.append(cur)
                cur = ''
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def decode(prefix, code):
    src = open(os.path.join(ROOT, 'C3BootProofs/Proofs/Fe25519Decode.lean')).read()
    ins = []
    for m in re.finditer(rf'theorem ({prefix}_at_\w+) : fetchRel {code} (0x[0-9A-Fa-f]+) = some \((.*), (\d)\) := by decide',
                         src):
        ins.append((int(m.group(2), 16), m.group(1), m.group(3), int(m.group(4))))
    ins.sort()
    return ins


class Ins:
    def __init__(self, off, lemma, text, ln):
        self.off, self.lemma, self.text, self.ln = off, lemma, text, ln
        t = toks(text.lstrip('.'))
        self.kind = t[0]
        if self.kind == 'load':
            self.rd, self.rs1, self.imm = reg(t[2]), reg(t[3]), int(t[4], 16)
            self.op = 'lw'
        elif self.kind == 'alu':
            self.op, self.rd, self.rs1, self.rs2 = t[1].lstrip('.'), reg(t[2]), reg(t[3]), reg(t[4])
        elif self.kind == 'aluImm':
            self.op, self.rd, self.rs1, self.imm = t[1].lstrip('.'), reg(t[2]), reg(t[3]), int(t[4], 16)
        elif self.kind == 'lui':
            self.rd, self.imm = reg(t[1]), int(t[2], 16)
            self.op = 'lui'
        elif self.kind == 'store':
            self.op, self.rs1, self.rs2, self.imm, self.rd = 'sw', reg(t[2]), reg(t[3]), int(t[4], 16), None
        elif self.kind in ('jalr', 'auipc', 'branch'):
            self.op, self.rd = self.kind, None
        else:
            raise Exception(text)


def alu(op, a, b):
    return {'add': (a + b) & M32, 'sltu': int(a < b), 'or': a | b, 'and': a & b, 'mul': (a * b) & M32,
            'mulhu': (a * b) >> 32, 'sll': (a << (b & 31)) & M32, 'srl': a >> (b & 31)}[op]


def simulate(block, regs0, mem):
    """Runs the block; returns, per instruction, the value it writes."""
    R = list(regs0)
    mem = dict(mem)
    vals = []
    for i in block:
        if i.kind == 'store':
            mem[(R[i.rs1] + i.imm) & M32] = R[i.rs2]
            vals.append(None)
            continue
        if i.kind == 'load':
            v = mem[(R[i.rs1] + i.imm) & M32]
        elif i.kind == 'alu':
            v = alu(i.op, R[i.rs1], R[i.rs2])
        elif i.kind == 'aluImm':
            v = alu(i.op, R[i.rs1], i.imm)
        else:
            v = i.imm
        if i.rd:
            R[i.rd] = v
        vals.append(v)
    return vals, R


class Gen:
    """Writes one block's proof."""

    def __init__(self, block, prefix, code, start, end, init_names):
        self.block, self.prefix, self.code, self.start, self.end = block, prefix, code, start, end
        self.init = dict(init_names)  # register -> Lean expression at the block's start
        self.lines = []
        self.combine = False

    def emit(self, s):
        self.lines.append(s)

    def step(self, hyps):
        """Steps each instruction. `self.src[k]` names instruction k's operands."""
        cur = dict(self.init)  # register -> var name or initial expr
        self.src = []
        self.var = []
        self.const = {}
        prev = 's'
        for k, i in enumerate(self.block):
            nxt = self.block[k + 1].off if k + 1 < len(self.block) else self.end
            v = f'v{k}'
            u = f'u{k}'
            ops = []
            if i.kind == 'load':
                ops = [cur.get(i.rs1)]
                self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.lwG hc {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                self.emit(f'    (by simp +decide only [upd, ↓reduceIte, {hyps}]; exact aligned_add hz (k := {i.imm}) (by decide))')
            elif i.kind == 'alu':
                ops = [cur.get(i.rs1), cur.get(i.rs2)]
                self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluG hc {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
            elif i.kind == 'aluImm':
                ops = [cur.get(i.rs1)]
                self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluImmG hc {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
            else:
                self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.luiG hc {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
            if i.kind != 'lui':
                self.emit(f'  simp +decide only [upd, ↓reduceIte, {hyps}] at hv{k}')
            self.src.append(ops)
            self.var.append(v)
            if i.rd:
                cur[i.rd] = v
            prev = u
        self.final = cur
        self.last = len(self.block) - 1

    def step_mem(self, hyps0, bases, sz, seg=40):
        """Steps a block that also loads from inputs and spills to the stack
        frame at `F`. `bases` maps each input base's Lean name to its
        alignment and separation hypotheses. Every `seg` instructions it
        restates each register's value, so the register terms stay short."""
        cur = dict(self.init)
        self.src, self.var = [], []
        prev, mem, hc, fr = 's', 'M', 'hc', 'fr0'
        hyps = 'hz0, ' + hyps0
        self.emit('  have hz0 : reg n 0 = 0 := s.zero')
        self.emit('  have fr0 : ∀ x, Sep F 0x%X x 1 → M x = M x := fun _ _ => rfl' % sz)
        self.stores = []  # (k, offset, value, memory name)
        self.slots = {}
        self.inputs = {}
        for k, i in enumerate(self.block):
            nxt = self.block[k + 1].off if k + 1 < len(self.block) else self.end
            v, u = f'v{k}', f'u{k}'
            simp = f'simp +decide only [upd, ↓reduceIte, {hyps}]'
            ops = []
            head = f'  obtain ⟨n{k}, '
            alias = None
            if i.kind == 'store':
                base, val = cur[i.rs1], cur[i.rs2]
                if base != 'F':
                    raise Exception(i.text)
                self.emit(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.swG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                self.emit(f'    (by {simp}; exact aligned_add hF (k := {i.imm}) (by decide)) (a := F + 0x{i.imm:X}) (v := {val})')
                self.emit(f'    (by {simp}) (by {simp})')
                self.emit(f'  obtain ⟨M{k}, hM{k}⟩ : ∃ M\', memStore32 {mem} (F + 0x{i.imm:X}) {val} = M\' := ⟨_, rfl⟩')
                self.emit(f'  rw [hM{k}] at {u}')
                self.emit(f'  have hc{k} : CodeIn M{k} B {self.code} := by rw [← hM{k}]; exact {hc}.store32 (frm_sep\' sFC (by decide))')
                self.emit(f'  have fr{k} : ∀ x, Sep F 0x{sz:X} x 1 → M{k} x = M x := fun x hx => by')
                self.emit(f'    rw [← hM{k}, memStore32_get_sep (frm_sep\' hx (by decide)), {fr} x hx]')
                mem, hc, fr = f'M{k}', f'hc{k}', f'fr{k}'
                self.stores.append((k, i.imm, val, mem))
                self.slots[i.imm] = len(self.stores) - 1
                self.src.append([val])
                self.var.append(None)
            elif i.kind == 'load':
                base = cur.get(i.rs1)
                if base == 'F':
                    si = self.slots[i.imm]
                    alias = self.stores[si][2]
                    self.emit(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.lwE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                    self.emit(f'    (by {simp}; exact aligned_add hF (k := {i.imm}) (by decide)) (v := {alias})')
                    self.emit(f'    (by {simp}; rw [{self.chain(si, i.imm)}])')
                else:
                    al, sep = bases[base]
                    load = (f'load_frame {fr} (show Sep F 0x{sz:X} ({base} + 0x{i.imm:X}) 4 from '
                            f'{sep}.symm.subR (c := {i.imm}) (l := 4) (by decide))')
                    key = (base, i.imm)
                    if key in self.inputs:
                        alias = self.inputs[key]
                        self.emit(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.lwE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        self.emit(f'    (by {simp}; exact aligned_add {al} (k := {i.imm}) (by decide)) (v := {alias})')
                        self.emit(f'    (by {simp}; rw [{load}]; exact hv{alias[1:]})')
                    else:
                        self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.lwG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        self.emit(f'    (by {simp}; exact aligned_add {al} (k := {i.imm}) (by decide))')
                        self.emit(f'  {simp} at hv{k}')
                        self.emit(f'  rw [{load}] at hv{k}')
                        self.inputs[key] = v
                        ops = [base]
            elif i.kind == 'alu' and i.op == 'add' and 0 in (i.rs1, i.rs2):
                alias = cur[i.rs2 if i.rs1 == 0 else i.rs1]
                self.emit(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.aluE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide) (v := {alias})')
                self.emit(f'    (by {simp}; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)')
            elif i.kind == 'alu':
                ops = [cur.get(i.rs1), cur.get(i.rs2)]
                self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                self.emit(f'  {simp} at hv{k}')
            elif i.kind == 'aluImm':
                ops = [cur.get(i.rs1)]
                self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluImmG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                self.emit(f'  {simp} at hv{k}')
            else:
                self.emit(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.luiG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
            if i.kind != 'store':
                if alias is not None:
                    self.src.append([])
                    self.var.append(None)
                    if i.rd:
                        cur[i.rd] = alias
                else:
                    self.src.append(ops)
                    self.var.append(v)
                    if i.rd:
                        cur[i.rd] = v
            prev = u
            if (k + 1) % seg == 0 and k + 1 < len(self.block):
                qs = []
                for r in sorted(cur):
                    if r == 0 or cur[r] is None:
                        continue
                    self.emit(f'  have q{k}_{r} : reg n{k} {lreg(r)} = {cur[r]} := by rw [{u}.regs]; {simp}')
                    qs.append(f'q{k}_{r}')
                self.emit(f'  have z{k} : reg n{k} 0 = 0 := {u}.self.zero')
                hyps = ', '.join([f'z{k}'] + qs + [h for h in ('hF',) if False])
                prev = f'{u}.self'
        self.final, self.last, self.mem, self.hc, self.fr = cur, len(self.block) - 1, mem, hc, fr
        self.hyps = hyps

    def step_seg(self, name, bases, seg, keep_slots, out_slots):
        """Like `step_mem`, but each `seg` instructions are a theorem of their
        own, so no single proof grows long; `self.lines` chains them.
        `self.regions` lists the memory the block writes, as (base, size,
        frame hypothesis, code separation, alignment): the stack frame `F`
        and any output. A slot is a (base, offset) pair. `keep_slots` are
        slots the block doesn't write and must report; `out_slots` are
        slots whose last value it must report."""
        n = len(self.block)
        rbase = {r[0]: r for r in self.regions}
        # a dry run for the bookkeeping: operands, stores, and which store each slot load reads
        cur = dict(self.init)
        self.src, self.var = [], [None] * n
        self.stores, slots, inputs = [], {}, {}
        reads = {}
        for k, i in enumerate(self.block):
            if i.kind == 'store':
                key = (cur[i.rs1], i.imm)
                self.stores.append((k, key, cur[i.rs2], f'M{k}'))
                slots[key] = len(self.stores) - 1
                self.src.append([cur[i.rs2]])
                continue
            v = f'v{k}'
            if i.kind == 'load' and cur.get(i.rs1) in rbase:
                si = slots[(cur[i.rs1], i.imm)]
                reads[k] = si
                cur[i.rd] = self.stores[si][2]
                self.src.append([])
                continue
            if i.kind == 'load':
                key = (cur[i.rs1], i.imm)
                if key in inputs:
                    cur[i.rd] = inputs[key]
                    self.src.append([])
                    continue
                inputs[key] = v
                self.src.append([cur[i.rs1]])
            elif i.kind == 'alu' and i.op == 'add' and 0 in (i.rs1, i.rs2):
                cur[i.rd] = cur[i.rs2 if i.rs1 == 0 else i.rs1]
                self.src.append([])
                continue
            elif i.kind == 'alu':
                self.src.append([cur.get(i.rs1), cur.get(i.rs2)])
            elif i.kind == 'aluImm':
                self.src.append([cur.get(i.rs1)])
            else:
                self.src.append([])
            self.var[k] = v
            if i.rd:
                cur[i.rd] = v
        self.final, self.last, self.inputs = cur, n - 1, inputs
        store_at = {st[0]: si for si, st in enumerate(self.stores)}
        live_until = {}
        for k, si in reads.items():
            live_until[si] = max(live_until.get(si, -1), k)
        self.final_slot = {key: si for si, (k, key, _, _) in enumerate(self.stores)}
        self.live_until, self.out_slots = live_until, out_slots
        ftype = ' → '.join(f'Sep {b} 0x{sz:X} x 1' for b, sz, *_ in self.regions)
        flam = ' '.join(r[2] for r in self.regions)
        fus = ' '.join('_' for _ in self.regions)

        # the segments
        cur = dict(self.init)
        slotval = {key: f'memLoad32 M0 ({addr(key)})' for key in keep_slots}
        slotsrc = {key: None for key in keep_slots}
        seen_inputs = {}
        bounds = self.seg_bounds(n, seg)
        self.seg_thms = []
        self.emit(f'  have fr0 : ∀ x, {ftype} → M x = M x := fun _ {fus} => rfl')
        for key in keep_slots:
            self.emit(f'  have sg0_{kname(key)} : memLoad32 M ({addr(key)}) = memLoad32 M ({addr(key)}) := rfl')
        mq = {r: self.init_hyp[r] for r in self.init}
        ms = {key: f'sg0_{kname(key)}' for key in keep_slots}
        mstate = ('s', 'hc', 'fr0')
        csteps = []
        for j in range(len(bounds) - 1):
            k0, k1 = bounds[j], bounds[j + 1]
            off_a = self.block[k0].off
            off_b = self.block[k1].off if k1 < n else self.end
            qin = sorted(r for r in cur if r != 0 and cur[r] is not None)
            qinval = {r: cur[r] for r in qin}
            sin = sorted((key for key, si in slotsrc.items() if self.carried(key, si, k0)), key=lambda t: (t[0] != 'F', t))
            sinval = {key: slotval[key] for key in sin}
            L = ['  have hz0 : reg n 0 = 0 := s.zero']
            mem, hc, fr, prev = 'Mi', 'hc', 'fr', 's'
            hyps = 'hz0' + ''.join(f', q{r}' for r in qin)
            seg_stores, new_vars, hv_refs = [], [], []
            for k in range(k0, k1):
                i = self.block[k]
                nxt = self.block[k + 1].off if k + 1 < n else self.end
                v, u = f'v{k}', f'u{k}'
                simp = f'simp +decide only [upd, ↓reduceIte, {hyps}]'
                if i.kind == 'store':
                    val = cur[i.rs2]
                    key = (cur[i.rs1], i.imm)
                    b_, bsz, blam, bcode, bal = rbase[key[0]]
                    L.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.swG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                    L.append(f'    (by {simp}; exact aligned_add {bal} (k := {i.imm}) (by decide)) (a := {addr(key)}) (v := {val})')
                    L.append(f'    (by {simp}) (by {simp})')
                    L.append(f'  obtain ⟨M{k}, hM{k}⟩ : ∃ M\', memStore32 {mem} ({addr(key)}) {val} = M\' := ⟨_, rfl⟩')
                    L.append(f'  rw [hM{k}] at {u}')
                    L.append(f'  have hc{k} : CodeIn M{k} B {self.code} := by rw [← hM{k}]; exact {hc}.store32 (frm_sep\' {bcode} (by decide))')
                    L.append(f'  have fr{k} : ∀ x, {ftype} → M{k} x = M0 x := fun x {flam} => by')
                    L.append(f'    rw [← hM{k}, memStore32_get_sep (frm_sep\' {blam} (by decide)), {fr} x {flam}]')
                    mem, hc, fr = f'M{k}', f'hc{k}', f'fr{k}'
                    seg_stores.append((k, key, val, mem))
                    slotsrc[key] = store_at[k]
                    slotval[key] = val
                elif i.kind == 'load' and cur.get(i.rs1) in rbase:
                    key = (cur[i.rs1], i.imm)
                    alias = slotval[key]
                    bal = rbase[key[0]][4]
                    L.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.lwE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                    L.append(f'    (by {simp}; exact aligned_add {bal} (k := {i.imm}) (by decide)) (v := {alias})')
                    L.append(f'    (by {simp}; rw [{self.seg_chain(seg_stores, key)}])')
                    cur[i.rd] = alias
                elif i.kind == 'load':
                    base = cur[i.rs1]
                    al, seps = bases[base]
                    shows = [f'(show Sep {rb} 0x{rsz:X} ({base} + 0x{i.imm:X}) 4 from {sp_}.symm.subR (c := {i.imm}) (l := 4) (by decide))'
                             for (rb, rsz, *_), sp_ in zip(self.regions, seps)]
                    load = (f'load_frame {fr} ' if len(shows) == 1 else f'load_frame2 {fr} ') + ' '.join(shows)
                    key = (base, i.imm)
                    if key in seen_inputs:
                        alias = seen_inputs[key]
                        L.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.lwE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        L.append(f'    (by {simp}; exact aligned_add {al} (k := {i.imm}) (by decide)) (v := {alias})')
                        L.append(f'    (by {simp}; rw [{load}]; exact hv{alias[1:]})')
                        if int(alias[1:]) < k0 and alias not in [h for h, _ in hv_refs]:
                            hv_refs.append((alias, f'memLoad32 M0 ({base} + 0x{i.imm:X}) = {alias}'))
                        cur[i.rd] = alias
                    else:
                        L.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.lwG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        L.append(f'    (by {simp}; exact aligned_add {al} (k := {i.imm}) (by decide))')
                        L.append(f'  {simp} at hv{k}')
                        L.append(f'  rw [{load}] at hv{k}')
                        seen_inputs[key] = v
                        new_vars.append((v, f'memLoad32 M0 ({base} + 0x{i.imm:X}) = {v}'))
                        cur[i.rd] = v
                elif i.kind == 'alu' and i.op == 'add' and 0 in (i.rs1, i.rs2):
                    alias = cur[i.rs2 if i.rs1 == 0 else i.rs1]
                    L.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.aluE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide) (v := {alias})')
                    L.append(f'    (by {simp}; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)')
                    cur[i.rd] = alias
                else:
                    if i.kind == 'alu':
                        L.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        stmt = f'aluEval .{i.op} {rv(cur, i.rs1)} {rv(cur, i.rs2)} = {v}'
                    elif i.kind == 'aluImm':
                        L.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluImmG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        stmt = f'aluEval .{i.op} {rv(cur, i.rs1)} 0x{i.imm:X} = {v}'
                    else:
                        L.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.luiG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        stmt = f'(0x{i.imm:X} : Word) = {v}'
                    if i.kind != 'lui':
                        L.append(f'  {simp} at hv{k}')
                    new_vars.append((v, stmt))
                    if i.rd:
                        cur[i.rd] = v
                prev = u
            last_k = k1 - 1
            qout = sorted(r for r in cur if r != 0 and cur[r] is not None)
            sout = sorted((key for key, si in slotsrc.items() if self.carried(key, si, k1)), key=lambda t: (t[0] != 'F', t))
            for r in qout:
                L.append(f'  have qo{r} : reg n{last_k} {lreg(r)} = {cur[r]} := by rw [u{last_k}.regs]; simp +decide only [upd, ↓reduceIte, {hyps}]')
            for key in sout:
                L.append(f'  have so{kname(key)} : memLoad32 {mem} ({addr(key)}) = {slotval[key]} := by')
                L.append(f'    rw [{self.seg_chain(seg_stores, key)}]')
            steps = ''.join(f'(.cons d{k} ' for k in range(k0, last_k)) + f'(.single d{last_k})' + ')' * (last_k - k0)
            parts = [v for v, _ in new_vars] + [steps, f'u{last_k}.self', hc, fr] + [f'qo{r}' for r in qout] + \
                [f'so{kname(key)}' for key in sout] + [f'hv{v[1:]}' for v, _ in new_vars]
            L.append(f'  exact ⟨n{last_k}, {mem}, {", ".join(parts)}⟩')
            concl = ['Steps n n\'', f'St M\' B n\' 0x{off_b:X} (reg n\')', f'CodeIn M\' B {self.code}',
                     f'(∀ x, {ftype} → M\' x = M0 x)']
            concl += [f'reg n\' {lreg(r)} = {cur[r]}' for r in qout]
            concl += [f'memLoad32 M\' ({addr(key)}) = {slotval[key]}' for key in sout]
            concl += [st for _, st in new_vars]
            hyps_in = [f'(q{r} : reg n {lreg(r)} = {qinval[r]})' for r in qin]
            hyps_in += [f'(sl{kname(key)} : memLoad32 Mi ({addr(key)}) = {sinval[key]})' for key in sin]
            hyps_in += [f'(hv{h[1:]} : {t})' for h, t in hv_refs]
            text = ' '.join(hyps_in)
            words = sorted(set(WORD_RE.findall(text)), key=lambda w: int(w[1:]))
            nv = ' '.join(v for v, _ in new_vars)
            thm = [f'set_option linter.unusedSimpArgs false in', 'set_option linter.unusedVariables false in',
                   f'set_option maxHeartbeats 40000000 in', f'set_option maxRecDepth 100000 in',
                   f'theorem {name}_g{j} {{M0 Mi : Word → BitVec 8}} {{B F {" ".join(self.basenames)} : Word}} {{n : Machine}}'
                   + (f' {{{" ".join(words)} : Word}}' if words else ''),
                   f'    (s : St Mi B n 0x{off_a:X} (reg n)) (hc : CodeIn Mi B {self.code})',
                   f'    (fr : ∀ x, {ftype} → Mi x = M0 x) {self.global_hyps}']
            for h in hyps_in:
                thm.append(f'    {h}')
            thm.append(f'    : ∃ (n\' : Machine) (M\' : Word → BitVec 8)' + (f' ({nv} : Word)' if nv else '') + ',')
            thm.append('      ' + ' ∧\n      '.join(concl) + ' := by')
            self.seg_thms.append('\n'.join(thm + L))
            s_, hc_, fr_ = mstate
            args = [s_, hc_, fr_, self.global_args] + [mq[r] for r in qin] + [ms[key] for key in sin] + \
                [f'hv{h[1:]}' for h, _ in hv_refs]
            ex = [f'ng{j}', f'Mg{j}'] + [v for v, _ in new_vars]
            conj = [f'cg{j}', f'ug{j}', f'hcg{j}', f'frg{j}'] + \
                [f'qg{j}_{r}' for r in qout] + [f'sg{j + 1}_{kname(key)}' for key in sout] + [f'hv{v[1:]}' for v, _ in new_vars]
            # `obtain` on a long conjunction is slow; projections are not
            self.emit(f'  obtain ⟨{", ".join(ex)}, hg{j}⟩ := {name}_g{j} {" ".join(args)}')
            for idx, c_ in enumerate(conj):
                path = f'hg{j}' + '.2' * idx + ('.1' if idx < len(conj) - 1 else '')
                self.emit(f'  have {c_} := {path}')
            mq = {r: f'qg{j}_{r}' for r in qout}
            ms = {key: f'sg{j + 1}_{kname(key)}' for key in sout}
            mstate = (f'ug{j}', f'hcg{j}', f'frg{j}')
            csteps.append(f'cg{j}')
        self.mem_final = f'Mg{len(bounds) - 2}'
        self.slot_facts = ms
        self.reg_facts = mq
        self.steps_final = csteps
        self.n_final = f'ng{len(bounds) - 2}'

    def seg_bounds(self, n, seg):
        """Where each segment theorem starts, and the end."""
        return list(range(0, n, seg)) + [n]

    def carried(self, key, si, at):
        """Whether `key`, last written by store `si`, is still read at or after `at`."""
        return si is None or self.live_until.get(si, -1) >= at or (key in self.out_slots and self.final_slot.get(key) == si)

    def seg_chain(self, seg_stores, key):
        """Rewrites that read slot `key` back through this segment's stores to
        its value: the store that wrote it, or the slot fact at the start."""
        b, o = key
        rws = []
        for k, (b2, os), _, m in reversed(seg_stores):
            if (b2, os) == key:
                rws.append(f'← hM{k}, memLoad32_store32_same')
                return ', '.join(rws)
            if b2 == b:
                sep = f'sep_offsets {b} (c := {os}) (n := 4) (d := {o}) (k := 4) (by decide) (by decide) (by decide)'
            else:
                sep = f'({self.region_sep[(b2, b)]}.sub (c := {os}) (l := 4) (by decide)).subR (c := {o}) (l := 4) (by decide)'
            rws.append(f'← hM{k}, memLoad32_store32_sep (show Sep ({b2} + 0x{os:X}) 4 ({b} + 0x{o:X}) 4 from {sep})')
        rws.append(f'sl{o:X}' if b == 'F' else f'sl{b}{o:X}')
        return ', '.join(rws)

    def chain(self, si, o):
        """Rewrites that read slot `o` of the current memory back to store `si`."""
        rws = []
        for k, os, _, m in reversed(self.stores[si + 1:]):
            rws.append(f'← hM{k}, memLoad32_store32_sep (show Sep (F + 0x{os:X}) 4 (F + 0x{o:X}) 4 from '
                       f'sep_offsets F (c := {os}) (n := 4) (d := {o}) (k := 4) (by decide) (by decide) (by decide))')
        rws.append(f'← hM{self.stores[si][0]}, memLoad32_store32_same')
        return ', '.join(rws)

    def facts(self):
        """One natural-number fact per instruction result: `self.stmt[k]` and
        the term or tactic that proves it."""
        self.const = {}
        self.stmt = {}
        for k, i in enumerate(self.block):
            if self.var[k] is None:
                continue
            v = f'v{k}'
            ops = self.src[k]
            if i.kind == 'lui':
                self.const[v] = i.imm
            elif i.kind == 'aluImm' and i.op == 'add' and (i.rs1 == 0 or ops[0] in self.const):
                self.const[v] = ((0 if i.rs1 == 0 else self.const[ops[0]]) + i.imm) & M32
            if v in self.const:
                prevs = [o for o in ops if o in self.const]
                rw = ', '.join(['← hv%d' % k] + ['c' + o[1:] for o in prevs])
                self.emit(f'  have c{k} : {v} = 0x{self.const[v]:X} := by rw [{rw}]; try rfl')
                self.stmt[k] = f'{v}.toNat = {self.const[v]}'
                self.emit(f'  have t{k} : {self.stmt[k]} := by rw [c{k}]; rfl')
                continue
            if i.kind == 'load':
                continue
            a = ops[0]
            pf = None
            if i.kind == 'aluImm':
                sh = i.imm & 31
                if i.op == 'sll':
                    st, pf = f'{v}.toNat = {a}.toNat * 2 ^ {sh} % 2 ^ 32', f'tn_sll hv{k}'
                elif i.op == 'srl':
                    st, pf = f'{v}.toNat = {a}.toNat / 2 ^ {sh}', f'tn_srl hv{k}'
                elif i.op == 'add':
                    st, pf = f'{v}.toNat = ({a}.toNat + {i.imm}) % 2 ^ 32', f'tn_add hv{k}'
                else:
                    raise Exception(i.text)
            else:
                b = ops[1]
                if i.op == 'add':
                    st, pf = f'{v}.toNat = ({a}.toNat + {b}.toNat) % 2 ^ 32', f'tn_add hv{k}'
                elif i.op == 'sltu':
                    st = (f'({a}.toNat < {b}.toNat ∧ {v}.toNat = 1) ∨ ({b}.toNat ≤ {a}.toNat ∧ {v}.toNat = 0)')
                    pf = f'tn_sltu hv{k}'
                    if a in self.var and self.combine:
                        ka = self.var.index(a)
                        ia = self.block[ka]
                        if ia.kind == 'alu' and ia.op == 'add' and b in self.src[ka]:
                            p0, p1 = self.src[ka]
                            st = f'{a}.toNat + 2 ^ 32 * {v}.toNat = {p0}.toNat + {p1}.toNat'
                            pf = f'fmP1 hv{ka} (.{"inl" if b == p0 else "inr"} hv{k})'
                elif i.op in ('mul', 'mulhu'):
                    tail = '% 2 ^ 32' if i.op == 'mul' else '/ 2 ^ 32'
                    lem = 'tn_mul' if i.op == 'mul' else 'tn_mulhu'
                    if b in self.const or a in self.const:
                        x, c = (a, b) if b in self.const else (b, a)
                        comm = '' if c == b else ', Nat.mul_comm'
                        st = f'{v}.toNat = {x}.toNat * {self.const[c]} {tail}'
                        pf = f'by rw [{lem} hv{k}, t{c[1:]}{comm}]'
                    else:
                        st, pf = f'{v}.toNat = {a}.toNat * {b}.toNat {tail}', f'{lem} hv{k}'
                elif i.op == 'and':
                    c = b if b in self.const else a
                    if c not in self.const:
                        raise Exception(i.text)
                    x = a if c == b else b
                    w = {0x3FFFFFF: 26, 0x1FFFFFF: 25}[self.const[c]]
                    st = f'{v}.toNat = {x}.toNat % 2 ^ {w}'
                    pf = f'tn_and{w}' + ('' if c == b else "'") + f' hv{k} c{c[1:]}'
                elif i.op == 'or':
                    ia, ib = self.block[self.var.index(a)], self.block[self.var.index(b)]
                    if ia.op == 'srl' and ib.op == 'sll':
                        x, y, ix, iy, lem = a, b, ia, ib, 'tn_orS'
                    elif ia.op == 'sll' and ib.op == 'srl':
                        x, y, ix, iy, lem = b, a, ib, ia, "tn_orS'"
                    else:
                        raise Exception(i.text)
                    sh = ix.imm & 31
                    if (iy.imm & 31) != 32 - sh:
                        raise Exception(i.text)
                    st = f'{v}.toNat = {x}.toNat + {y}.toNat'
                    pf = f'{lem} {sh} (by decide) hv{k} t{x[1:]} t{y[1:]}'
                else:
                    raise Exception(i.text)
            self.stmt[k] = st
            self.emit(f'  have t{k} : {st} := {pf}')

    def walk(self, v, top, known, acc):
        """Collects into `acc` (instructions, stops, seen) the cone below `v`."""
        ks, stops, seen = acc
        if v in seen:
            return
        seen.add(v)
        if v not in self.var:
            return
        if v in known and not top:
            stops.add(v)
            return
        k = self.var.index(v)
        if k in self.stmt:
            ks.add(k)
        if v in self.const:
            return
        for o in self.src[k]:
            self.walk(o, False, known, acc)

    def cone(self, targets, known):
        """The instructions between `targets` and the known words."""
        ks, stops, seen = set(), set(), set()
        for t in targets:
            self.walk(t, True, known, (ks, stops, seen))
        used = ' '.join(self.stmt[k] for k in ks if self.var[k] not in self.const)
        ks = {k for k in ks if self.var[k] not in self.const or re.search(rf'\b{self.var[k]}\b', used)}
        return sorted(ks), stops


class Spec:
    """A Rust function's values in order: each is a natural number given by a
    Lean expression over earlier ones, and a Python function for its value."""

    def __init__(self):
        self.vals = []  # (name, lean expr, fn(env)->int, deps, full_needed)

    def add(self, name, expr, fn, deps, full=False):
        self.vals.append([name, expr, fn, deps, full])
        return name

    def run(self, inputs):
        env = dict(inputs)
        for name, expr, fn, deps, _ in self.vals:
            env[name] = fn(env)
        return env


def reduce_spec():
    sp = Spec()
    z = [f'Z{i}' for i in range(10)]
    divs = set()
    cnt = [0]

    def new(expr, fn, deps, full=False):
        cnt[0] += 1
        return sp.add(f'X{cnt[0]}', expr, fn, deps, full)

    def carry(i):
        s = 26 if i % 2 == 0 else 25
        a, b = z[i + 1], z[i]
        divs.add(b)
        z[i + 1] = new(f'({a} + {b} / 2 ^ {s}) % 2 ^ 64', lambda e, a=a, b=b, s=s: (e[a] + (e[b] >> s)) & M64, [a, b])
        z[i] = new(f'{b} % 2 ^ {s}', lambda e, b=b, s=s: e[b] & ((1 << s) - 1), [b])

    for i in [0, 4, 1, 5, 2, 6, 3, 7, 4, 8]:
        carry(i)
    a, b = z[0], z[9]
    divs.add(b)
    sh = new(f'{b} / 2 ^ 25', lambda e, b=b: e[b] >> 25, [b], True)
    t = new(f'19 * {sh} % 2 ^ 64', lambda e, sh=sh: (19 * e[sh]) & M64, [sh], True)
    z[0] = new(f'({a} + {t}) % 2 ^ 64', lambda e, a=a, t=t: (e[a] + e[t]) & M64, [a, t])
    z[9] = new(f'{b} % 2 ^ 25', lambda e, b=b: e[b] & ((1 << 25) - 1), [b])
    carry(0)
    for v in sp.vals:
        v[4] = v[4] or v[0] in divs
    return sp, z, divs


def match(gen, sp, divs, inputs_of_run, runs):
    """For each spec value, the earliest instruction results that hold its
    low word and, when it is divided later, its high word, in every run."""
    lo, hi = {}, {}
    traces = []
    for regs0, mem, ins in runs:
        vals, _ = simulate(gen.block, regs0, mem)
        env = sp.run(ins)
        traces.append((vals, env))
    names = [v[0] for v in sp.vals]
    for name in list(inputs_of_run) + names:
        for part, f, tab in (('lo', lambda x: x & M32, lo), ('hi', lambda x: x >> 32, hi)):
            for k in range(len(gen.block)):
                if gen.var[k] in gen.const:
                    continue
                if all(vals[k] == f(env[name]) for vals, env in traces):
                    tab[name] = gen.var[k]
                    break
    return lo, hi


def nat_eval(expr, env):
    """The value of a Lean natural-number expression made of `vN.toNat`,
    numerals, `+`, `*`, `^`, `%`, `/`, and parentheses."""
    toks = re.findall(r'v\d+\.toNat|\d+|[-+*/%^()]', expr)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def take():
        pos[0] += 1
        return toks[pos[0] - 1]

    def atom():
        t = take()
        if t == '(':
            v = add()
            take()
            return v
        if t.endswith('.toNat'):
            return env[t[:-6]]
        return int(t)

    def power():
        b = atom()
        if peek() == '^':
            take()
            return b ** power()
        return b

    def mul():
        v = power()
        while peek() in ('*', '/', '%'):
            op = take()
            r = power()
            v = v * r if op == '*' else v // r if op == '/' else v % r
        return v

    def add():
        v = mul()
        while peek() == '+':
            take()
            v += mul()
        return v

    return add()


def lemma(name, stmt, words, nats, hyps, extra='', bounds=True):
    """A standalone step lemma, so each `omega` sees only its own facts."""
    ws = ' '.join(sorted(words, key=lambda w: int(w[1:])))
    ns = ' '.join(nats)
    hs = '\n    '.join(f'({h} : {t})' for h, t in hyps)
    lts = '; '.join(f'have := {w}.isLt' for w in sorted(words, key=lambda w: int(w[1:])))
    out = [f'theorem {name} {{{ws} : Word}}' + (f' {{{ns} : Nat}}' if ns else '')]
    out.append(f'    {hs} :')
    out.append(f'    {stmt} := by')
    ws = sorted(words, key=lambda w: int(w[1:]))
    gen = ''.join(f'\n  generalize {w}.toNat = n{w[1:]} at *' for w in ws)
    if bounds:
        out.append(f'  {lts}{extra}{gen}')
        out.append('  omega')
    else:
        out.append('  ' + extra.strip())
    return '\n'.join(out)


WORD_RE = re.compile(r'\bv\d+\b')
NAT_RE = re.compile(r'\b[XZ]\d+\b')


def gen_reduce():
    ins = [Ins(*t) for t in decode('fr', 'feReduceCode')]
    block = [i for i in ins if 0xC <= i.off < 0x1A4]
    g = Gen(block, 'fr', 'feReduceCode', 0xC, 0x1A4, {11: 'zp'})
    g.step('ha1')
    g.facts()
    sp, outs, divs = reduce_spec()
    rnd = random.Random(710)
    runs = []
    for _ in range(400):
        z = [rnd.getrandbits(64) for _ in range(10)]
        regs0 = [0] * 32
        regs0[11] = 0x2000
        mem = {}
        for k in range(10):
            mem[0x2000 + 8 * k] = z[k] & M32
            mem[0x2000 + 8 * k + 4] = z[k] >> 32
        runs.append((regs0, mem, {f'Z{k}': z[k] for k in range(10)}))
    inputs = [f'Z{k}' for k in range(10)]
    lo, hi = match(g, sp, divs, inputs, runs)
    body = []
    lemmas = []
    known = {}
    hfact = {}  # spec name -> (hyp name, stmt)
    efact = {}
    small = set()
    for zi in inputs:
        l, h = lo[zi], hi[zi]
        st = f'{l}.toNat + 2 ^ 32 * {h}.toNat = {zi}'
        k = int(zi[1:])
        body.append(f'  obtain ⟨{zi}, e{zi}⟩ : ∃ Z, u64At M zp {k} = Z := ⟨_, rfl⟩')
        body.append(f'  have h{zi} : {st} := by')
        body.append(f'    rw [← e{zi}, ← hv{l[1:]}, ← hv{h[1:]}]; rfl')
        hfact[zi] = (f'h{zi}', st)
        known[l] = zi
        known[h] = zi
    for n, (name, expr, fn, deps, full) in enumerate(sp.vals):
        l = lo.get(name)
        if l is None:
            raise Exception(f'no low word for {name} = {expr}')
        targets = [l]
        if full:
            h = hi.get(name)
            if h is None:
                raise Exception(f'no high word for {name} = {expr}')
            targets.append(h)
            st = f'{l}.toNat + 2 ^ 32 * {h}.toNat = {name}'
        elif re.fullmatch(r'[XZ]\d+ % 2 \^ 2[56]', expr):
            st = f'{l}.toNat = {name}'
            small.add(name)
        else:
            st = f'{l}.toNat = {name} % 2 ^ 32'
        ks, stops = g.cone(targets, known)
        hyps = [(f't{k}', g.stmt[k]) for k in ks]
        specs = sorted({known[v] for v in stops}, key=lambda x: (x[0], int(x[1:])))
        for sname in specs:
            hyps.append(hfact[sname])
        efact[name] = (f'e{name}', f'{expr} = {name}')
        hyps.append(efact[name])
        words = set()
        nats = []
        for _, t in hyps:
            words |= set(WORD_RE.findall(t))
        words |= set(WORD_RE.findall(st))
        for _, t in hyps + [('', st)]:
            for x in NAT_RE.findall(t):
                if x not in nats:
                    nats.append(x)
        lname = f'fr_s{n}'
        lemmas.append(lemma(lname, st, words, nats, hyps))
        body.append(f'  obtain ⟨{name}, e{name}⟩ : ∃ X, {expr} = X := ⟨_, rfl⟩')
        body.append(f'  have h{name} : {st} := {lname} ' + ' '.join(h for h, _ in hyps))
        hfact[name] = (f'h{name}', st)
        known[l] = name
        if full:
            known[hi[name]] = name
    return g, sp, outs, lo, body, lemmas, small


MUL_KEEP_SLOTS = [0x58] + [0xEC + 4 * i for i in range(13)]
MUL_Z_SLOTS = [0x98 + 4 * i for i in range(20)]


def mul_terms():
    """For each sum `z[k]`, its ten products as (x index, doubled, y index, times 19)."""
    out = []
    for k in range(10):
        t = []
        for i in range(10):
            j = k - i
            wrap = j < 0
            if wrap:
                j += 10
            t.append((i, bool(i % 2 and j % 2), j, wrap))
        out.append(t)
    return out


def gen_mul():
    ins = [Ins(*t) for t in decode('fmu', 'feMulCode')]
    block = [i for i in ins if 0x2C <= i.off < 0x8A8]
    g = Gen(block, 'fmu', 'feMulCode', 0x2C, 0x8A8, {11: 'xp', 12: 'yp', 2: 'F', 3: 'G3', 4: 'G4'})
    g.combine = True
    g.init_hyp = {2: 'hsp', 11: 'ha1', 12: 'ha2', 3: 'hG3', 4: 'hG4'}
    g.basenames = ['xp', 'yp', 'G3', 'G4']
    g.global_hyps = ('(hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)\n'
                     '    (sFC : Sep F 0x120 B feMulCode.length) (sXF : Sep xp 40 F 0x120) (sYF : Sep yp 40 F 0x120)')
    g.global_args = 'hF hx hy sFC sXF sYF'
    g.regions = [('F', 0x120, 'hx', 'sFC', 'hF')]
    g.region_sep = {}
    g.step_seg('fmu', {'xp': ('hx', ['sXF']), 'yp': ('hy', ['sYF'])}, 40,
               [('F', o) for o in MUL_KEEP_SLOTS], [('F', o) for o in MUL_Z_SLOTS])
    g.facts()
    rnd = random.Random(710)
    runs = []
    for _ in range(64):
        x = [rnd.getrandbits(32) for _ in range(10)]
        y = [rnd.getrandbits(32) for _ in range(10)]
        regs0 = [0] * 32
        regs0[2], regs0[11], regs0[12] = 0x10000, 0x2000, 0x2800
        mem = {}
        for k in range(10):
            mem[0x2000 + 4 * k] = x[k]
            mem[0x2800 + 4 * k] = y[k]
        vals, _ = simulate(block, regs0, mem)
        runs.append((x, y, vals))
    n = len(block)

    def find(f, ks=None):
        for k in (ks if ks is not None else range(n)):
            if g.var[k] is None or g.var[k] in g.const:
                continue
            if all(vals[k] == f(x, y) for x, y, vals in runs):
                return k
        return None

    terms = mul_terms()

    def xval(i, dbl):
        return (lambda inp: (2 * inp[0][i]) & M32) if dbl else (lambda inp: inp[0][i])

    def yval(j, w19):
        return (lambda inp: (19 * inp[1][j]) & M32) if w19 else (lambda inp: inp[1][j])

    pterms = [[(xval(i, dbl), yval(j, w19), False) for (i, dbl, j, w19) in ts] for ts in terms]
    pruns = [((x, y), vals) for x, y, vals in runs]
    prods, lemmas, body, zfacts = prodsum(g, pruns, pterms, 'fmu')
    return g, runs, prods, terms, lemmas, body, zfacts


def prodsum(g, runs, terms, prefix):
    """The facts for each product and each sum the block keeps whole.
    `terms[k]` lists sum `k`'s products as (left value, right value,
    doubled), each value a function of a run's input; the doubled ones are
    the Rust source's `(...) * 2` group, which comes last."""
    block = g.block
    n = len(block)

    def pval(kz, t, inp):
        a, b_, _ = terms[kz][t]
        return a(inp) * b_(inp)

    prods = {}
    for kz, ts in enumerate(terms):
        for t in range(len(ts)):
            klo = khi = None
            for k in range(n):
                bk = block[k]
                if g.var[k] and bk.kind == 'alu' and bk.op == 'mul' and all(
                        vals[k] == pval(kz, t, inp) & M32 for inp, vals in runs):
                    klo = k
                    break
            for k in range(n):
                bk = block[k]
                if g.var[k] and bk.kind == 'alu' and bk.op == 'mulhu' and all(
                        vals[k] == pval(kz, t, inp) >> 32 for inp, vals in runs):
                    khi = k
                    break
            if klo is None or khi is None:
                raise Exception(f'no product z{kz}[{t}]')
            o0, o1 = g.src[klo]

            def val_of(o):
                kk = g.var.index(o)
                return [vals[kk] for _, vals in runs]
            xs = [terms[kz][t][0](inp) for inp, _ in runs]
            xa, yb = (o0, o1) if val_of(o0) == xs else (o1, o0)
            prods[(kz, t)] = (g.var[klo], g.var[khi], xa, yb, klo, khi)
    known = {}
    hfact = {}
    lemmas, body = [], []
    order = sorted(prods.items(), key=lambda kv: max(kv[1][4], kv[1][5]))
    for (kz, t), (lo, hi, xa, yb, klo, khi) in order:
        st = f'{lo}.toNat + 2 ^ 32 * {hi}.toNat = {xa}.toNat * {yb}.toNat'
        hyps = [(f't{klo}', g.stmt[klo]), (f't{khi}', g.stmt[khi])]
        extra = ''
        for kk in (klo, khi):
            o0, o1 = g.src[kk]
            if o0 != xa:
                extra += f'\n  rw [Nat.mul_comm {o0}.toNat {o1}.toNat] at t{kk}'
        name = f'{prefix}_p{kz}_{t}'
        lemmas.append(lemma(name, st, {lo, hi, xa, yb}, [], hyps, extra))
        body.append(f'  have hp{kz}_{t} : {st} := {name} t{klo} t{khi}')
        hfact[lo] = hfact[hi] = (f'hp{kz}_{t}', st)
        known[lo] = known[hi] = (kz, frozenset([t]))
    # partial sums: words whose cone's products all belong to one sum
    pset = {}
    for (kz, t), (lo, hi, *_r) in prods.items():
        pset[lo] = pset[hi] = (kz, t)
    cone = {}
    for k in range(n):
        sset = set()
        v = g.var[k]
        if v in pset:
            sset.add(pset[v])
        for o in g.src[k]:
            if o in cone:
                sset |= cone[o]
        if v is not None:
            cone[v] = sset
    sums = {}
    for k in range(n):
        v = g.var[k]
        if v is None or v in pset or v in g.const:
            continue
        sset = cone[v]
        kzs = {a for a, _ in sset}
        if len(sset) < 2 and not any(terms[a][b_][2] for a, b_ in sset):
            continue
        if len(kzs) != 1:
            continue
        kz = kzs.pop()
        ts = tuple(sorted(b_ for _, b_ in sset))
        kinds = [False] + ([True] if any(terms[kz][tt][2] for tt in ts) else [])
        for w in kinds:
            def tot(inp, kz=kz, ts=ts, w=w):
                return sum(pval(kz, tt, inp) * (2 if w and terms[kz][tt][2] else 1) for tt in ts) & M64
            key = (kz, ts, w)
            if all(vals[k] == tot(inp) & M32 for inp, vals in runs):
                sums.setdefault(key, {}).setdefault('lo', v)
            elif all(vals[k] == tot(inp) >> 32 for inp, vals in runs):
                sums.setdefault(key, {}).setdefault('hi', v)
    full = [(key, d['lo'], d['hi']) for key, d in sums.items() if 'lo' in d and 'hi' in d and
            (len(key[1]) > 1 or key[2])]
    full.sort(key=lambda e: max(g.var.index(e[1]), g.var.index(e[2])))

    def ptxt(kz, tt):
        return f'{prods[(kz, tt)][2]}.toNat * {prods[(kz, tt)][3]}.toNat'

    def sum_expr(kz, ts, w):
        plain = [tt for tt in ts if not (w and terms[kz][tt][2])]
        grp = [tt for tt in ts if w and terms[kz][tt][2]]
        parts = [ptxt(kz, tt) for tt in plain]
        if grp:
            inner = ' + '.join(ptxt(kz, tt) for tt in grp)
            parts.append(f'({inner}) * 2' if len(grp) > 1 or plain else f'{inner} * 2')
        return ' + '.join(parts)

    zfacts = {}
    for (kz, ts, w), lo, hi in full:
        expr = sum_expr(kz, ts, w)
        st = f'{lo}.toNat + 2 ^ 32 * {hi}.toNat = ({expr}) % 2 ^ 64'
        ks, stops = g.cone([lo, hi], known)
        hyps = [(f't{k}', g.stmt[k]) for k in ks]
        seen = set()
        for sv in sorted(stops, key=lambda x_: int(x_[1:])):
            h = hfact[sv]
            if h[0] not in seen:
                seen.add(h[0])
                hyps.append(h)
        words = set(WORD_RE.findall(st))
        for _, tt in hyps:
            words |= set(WORD_RE.findall(tt))
        tag = 'w' if w else 's'
        name = f'{prefix}_{tag}{kz}_{"_".join(str(tt) for tt in ts)}'
        hn = f'h{tag}{kz}_{"_".join(str(tt) for tt in ts)}'
        if w and all(terms[kz][tt][2] for tt in ts):
            # a doubled group: a few shifts from the group's sum, by `omega` over its bounds
            lemmas.append(lemma(name, st, words, [], hyps))
        else:
            # the low words' adds come with their carries (fmP1); drop their remainders
            combined = set()
            for h, tt in hyps:
                m = re.match(r'(v\d+)\.toNat \+ 2 \^ 32 \* v\d+\.toNat = v\d+\.toNat \+ v\d+\.toNat$', tt)
                if m and h.startswith('t'):
                    combined.add(m.group(1))
            hyps = [(h, tt) for h, tt in hyps
                    if not (h.startswith('t') and re.match(r'(v\d+)\.toNat = \(', tt) and tt.split('.')[0] in combined)]
            qs, extra = [], ''
            for h, tt in hyps:
                if re.search(r'% 2 \^ (32|64)$', tt):
                    extra += f'\n  obtain ⟨q_{h}, e_{h}⟩ := mod_q {h}; clear {h}'
                    qs.append((h, tt))
            # check the identity the proof states on the runs
            for inp, vals in runs:
                env = {f'v{k}': vals[k] for k in range(len(vals)) if vals[k] is not None}
                S = nat_eval(expr, env)
                Q = 0
                for h, tt in qs:
                    rhs = tt.split(' = ', 1)[1]
                    mod = 2 ** 32 if rhs.endswith('2 ^ 32') else 2 ** 64
                    Q += nat_eval(rhs[:rhs.rindex(' % ')], env) // mod
                if env[lo] + 2 ** 32 * env[hi] + 2 ** 64 * Q != S:
                    raise Exception(f'identity fails for {name}')
            qsum = ' + '.join(f'q_{h}' for h, _ in qs) or '0'
            gen = ''.join(f'\n    generalize {x_}.toNat = n{x_[1:]} at *' for x_ in sorted(words, key=lambda x_: int(x_[1:])))
            extra += (f'\n  have key : {lo}.toNat + 2 ^ 32 * {hi}.toNat + 2 ^ 64 * ({qsum}) = {expr} := by{gen}'
                      f'\n    omega\n  exact mod64_of key')
            lemmas.append(lemma(name, st, words, [], hyps, extra, bounds=False))
        body.append(f'  have {hn} : {st} := {name} ' + ' '.join(h for h, _ in hyps))
        hfact[lo] = hfact[hi] = (hn, st)
        known[lo] = known[hi] = (kz, frozenset(ts))
        if len(ts) == len(terms[kz]) and (w or not any(t_[2] for t_ in terms[kz])):
            zfacts[kz] = (lo, hi, hn)
    if len(zfacts) != len(terms):
        raise Exception(f'sums found for {sorted(zfacts)}')
    return prods, lemmas, body, zfacts


SQ_TERMS = {
    0: ([('x', 0, 'x', 0), ('x2', 2, 'x19', 8), ('x2', 4, 'x19', 6)],
        [('x2', 1, 'x19', 9), ('x2', 3, 'x19', 7), ('x', 5, 'x19', 5)]),
    1: ([('x2', 0, 'x', 1), ('x2', 3, 'x19', 8), ('x2', 5, 'x19', 6)], [('x', 2, 'x19', 9), ('x', 4, 'x19', 7)]),
    2: ([('x2', 0, 'x', 2), ('x2', 1, 'x', 1), ('x2', 4, 'x19', 8), ('x', 6, 'x19', 6)],
        [('x2', 3, 'x19', 9), ('x2', 5, 'x19', 7)]),
    3: ([('x2', 0, 'x', 3), ('x2', 1, 'x', 2), ('x2', 5, 'x19', 8)], [('x', 4, 'x19', 9), ('x', 6, 'x19', 7)]),
    4: ([('x2', 0, 'x', 4), ('x2', 1, 'x2', 3), ('x', 2, 'x', 2), ('x2', 6, 'x19', 8)],
        [('x2', 5, 'x19', 9), ('x', 7, 'x19', 7)]),
    5: ([('x2', 0, 'x', 5), ('x2', 1, 'x', 4), ('x2', 2, 'x', 3), ('x2', 7, 'x19', 8)], [('x', 6, 'x19', 9)]),
    6: ([('x2', 0, 'x', 6), ('x2', 1, 'x2', 5), ('x2', 2, 'x', 4), ('x2', 3, 'x', 3), ('x', 8, 'x19', 8)],
        [('x2', 7, 'x19', 9)]),
    7: ([('x2', 0, 'x', 7), ('x2', 1, 'x', 6), ('x2', 2, 'x', 5), ('x2', 3, 'x', 4)], [('x', 8, 'x19', 9)]),
    8: ([('x2', 0, 'x', 8), ('x2', 1, 'x2', 7), ('x2', 2, 'x', 6), ('x2', 3, 'x2', 5), ('x', 4, 'x', 4)],
        [('x', 9, 'x19', 9)]),
    9: ([('x2', 0, 'x', 9), ('x2', 1, 'x', 8), ('x2', 2, 'x', 7), ('x2', 3, 'x', 6), ('x2', 4, 'x', 5)], []),
}
SQ_KEEP_SLOTS = [0x1C + 4 * i for i in range(13)]


def sq_val(kind, i):
    if kind == 'x':
        return lambda inp: inp[i]
    if kind == 'x2':
        return lambda inp: (2 * inp[i]) & M32
    return lambda inp: (19 * inp[i]) & M32


def gen_sq():
    ins = [Ins(*t) for t in decode('fsq', 'feSquareInnerCode')]
    block = [i for i in ins if 0x1C <= i.off < 0x4CC]
    g = Gen(block, 'fsq', 'feSquareInnerCode', 0x1C, 0x4CC, {10: 'zo', 11: 'xp', 2: 'F', 3: 'G3', 4: 'G4'})
    g.combine = True
    g.init_hyp = {2: 'hsp', 10: 'ha0', 11: 'ha1', 3: 'hG3', 4: 'hG4'}
    g.basenames = ['zo', 'xp', 'G3', 'G4']
    g.global_hyps = ('(hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)\n'
                     '    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)\n'
                     '    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)')
    g.global_args = 'hF hZ hx sFC sZC sXF sXZ sFZ'
    g.regions = [('F', 0x50, 'hxF', 'sFC', 'hF'), ('zo', 0x50, 'hxZ', 'sZC', 'hZ')]
    g.region_sep = {('F', 'zo'): 'sFZ', ('zo', 'F'): 'sFZ.symm'}
    g.step_seg('fsq', {'xp': ('hx', ['sXF', 'sXZ'])}, 40,
               [('F', o) for o in SQ_KEEP_SLOTS], [('zo', 4 * i) for i in range(20)])
    g.facts()
    rnd = random.Random(710)
    runs = []
    for _ in range(64):
        x = [rnd.getrandbits(32) for _ in range(10)]
        regs0 = [0] * 32
        regs0[2], regs0[10], regs0[11] = 0x10000, 0x3000, 0x2000
        mem = {0x2000 + 4 * k: x[k] for k in range(10)}
        vals, _ = simulate(block, regs0, mem)
        runs.append((x, vals))
    terms = []
    for k in range(10):
        plain, grp = SQ_TERMS[k]
        terms.append([(sq_val(a, i), sq_val(b, j), False) for a, i, b, j in plain] +
                     [(sq_val(a, i), sq_val(b, j), True) for a, i, b, j in grp])
    prods, lemmas, body, zfacts = prodsum(g, runs, terms, 'fsq')
    return g, runs, prods, lemmas, body, zfacts


def write_sq():
    g, runs, prods, lemmas, body, zfacts = gen_sq()
    o = ['import C3BootProofs.Proofs.Fe25519Decode', '',
         '/-! # The straight-line body of `FieldElement2625::square_inner`, as compiled', '',
         '`scripts/gen-fe25519.py` writes this file from the decoded instructions: a',
         'theorem for each 40 instructions, the facts for each product and sum, and',
         '`fsq_body`, which chains them. -/', '',
         'namespace C3.RV32', '', 'open C3.Image', '']
    for t in g.seg_thms:
        o += [t, '']
    for lm in lemmas:
        o += [lm, '']
    keep = ' ∧\n      '.join(f'memLoad32 M\' (F + 0x{s_:X}) = memLoad32 M (F + 0x{s_:X})' for s_ in SQ_KEEP_SLOTS)
    o += ['set_option maxHeartbeats 40000000 in', 'set_option maxRecDepth 100000 in',
          '/-- **The body of `square_inner`**, from 0x1C to the restores at 0x4CC: the',
          'ten `u64` sums it stores at `zo` are `feSqZ` of the operand\'s limbs, it',
          'writes nothing outside its frame and the sums, and it leaves the frame',
          'slots that hold the saved registers alone. -/',
          'theorem fsq_body {M : Word → BitVec 8} {B F zo xp : Word} {n : Machine} (s : St M B n 0x1C (reg n))',
          '    (hc : CodeIn M B feSquareInnerCode) (hsp : reg n sp = F) (ha0 : reg n a0 = zo) (ha1 : reg n a1 = xp)',
          '    (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)',
          '    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)',
          '    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50) :',
          '    ∃ n\' M\', Steps n n\' ∧ St M\' B n\' 0x4CC (reg n\') ∧',
          '      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M\' x = M x) ∧',
          f'      {keep} ∧',
          '      [u64At M\' zo 0, u64At M\' zo 1, u64At M\' zo 2, u64At M\' zo 3, u64At M\' zo 4, u64At M\' zo 5,',
          '        u64At M\' zo 6, u64At M\' zo 7, u64At M\' zo 8, u64At M\' zo 9] =',
          '        feSqZ (limbAt M xp 0) (limbAt M xp 1) (limbAt M xp 2) (limbAt M xp 3) (limbAt M xp 4)',
          '          (limbAt M xp 5) (limbAt M xp 6) (limbAt M xp 7) (limbAt M xp 8) (limbAt M xp 9) ∧',
          '      reg n\' sp = F ∧ reg n\' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n\' (4 : Fin 32) = reg n (4 : Fin 32) := by',
          '  obtain ⟨G3, hG3⟩ : ∃ g, reg n (3 : Fin 32) = g := ⟨_, rfl⟩',
          '  obtain ⟨G4, hG4⟩ : ∃ g, reg n (4 : Fin 32) = g := ⟨_, rfl⟩']
    o += g.lines
    o += body
    xs = [g.inputs[('xp', 4 * i)] for i in range(10)]
    for i, w in enumerate(xs):
        o.append(f'  obtain ⟨X{i}, eX{i}⟩ : ∃ X, limbAt M xp {i} = X := ⟨_, rfl⟩')
        o.append(f'  have hX{i} : {w}.toNat = X{i} := by rw [← eX{i}, ← hv{w[1:]}]; rfl')
    w2, w19 = {}, {}
    for (kz, t), (lo, hi, xa, yb, klo, khi) in prods.items():
        plain, grp = SQ_TERMS[kz]
        a, i, b, j = (plain + grp)[t]
        for kind, idx, word in ((a, i, xa), (b, j, yb)):
            if kind == 'x2':
                w2.setdefault(idx, set()).add(word)
            elif kind == 'x19':
                w19.setdefault(idx, set()).add(word)
    eqs = []
    for i, wsx in sorted(w2.items()):
        if len(wsx) != 1:
            raise Exception(f'x{i}*2 in several words {wsx}')
        w = wsx.pop()
        o.append(f'  have g2_{i} : 2 * {xs[i]}.toNat % 2 ^ 32 = {w}.toNat := by rw [t{w[1:]}, Nat.pow_one, Nat.mul_comm]')
        eqs.append(f'g2_{i}')
    for i, wsx in sorted(w19.items()):
        if len(wsx) != 1:
            raise Exception(f'x{i}*19 in several words {wsx}')
        w = wsx.pop()
        o.append(f'  have g19_{i} : 19 * {xs[i]}.toNat % 2 ^ 32 = {w}.toNat := by rw [t{w[1:]}, Nat.mul_comm]')
        eqs.append(f'g19_{i}')
    mlast = g.mem_final
    for kz in range(10):
        lo, hi, hn = zfacts[kz]
        for off, w in ((8 * kz, lo), (8 * kz + 4, hi)):
            si = g.final_slot[('zo', off)]
            if g.stores[si][2] != w:
                raise Exception(f'slot zo+{off:#x} holds {g.stores[si][2]}, not {w}')
        o.append(f'  have uz{kz} : u64At {mlast} zo {kz} = {lo}.toNat + 2 ^ 32 * {hi}.toNat := by')
        o.append(f'    unfold u64At')
        o.append(f'    rw [show zo + BitVec.ofNat 32 (8 * {kz}) = zo + 0x{8 * kz:X} from rfl,')
        o.append(f'      show zo + BitVec.ofNat 32 (8 * {kz} + 4) = zo + 0x{8 * kz + 4:X} from rfl,')
        o.append(f'      {g.slot_facts[("zo", 8 * kz)]}, {g.slot_facts[("zo", 8 * kz + 4)]}]')
    steps = g.steps_final
    chain = steps[-1]
    for c in reversed(steps[:-1]):
        chain = f'{c}.trans ({chain})'
    last = len(steps) - 1
    o.append(f'  refine ⟨{g.n_final}, {mlast}, {chain}, ug{last}, frg{last}, ' +
             ', '.join(g.slot_facts[('F', s_)] for s_ in SQ_KEEP_SLOTS) + ', ?_, ' +
             f'{g.reg_facts[2]}, {g.reg_facts[3]}.trans hG3.symm, {g.reg_facts[4]}.trans hG4.symm⟩')
    o.append('  rw [' + ', '.join(f'uz{k}' for k in range(10)) + ', ' + ', '.join(f'eX{i}' for i in range(10)) + ']')
    o.append('  simp only [feSqZ]')
    o.append('  rw [' + ', '.join(f'← hX{i}' for i in range(10)) + ']')
    o.append('  rw [' + ', '.join(eqs) + ']')
    o.append('  rw [' + ', '.join(zfacts[k][2] for k in range(10)) + ']')
    o += ['', 'end C3.RV32']
    open(os.path.join(ROOT, 'C3BootProofs/Proofs/FeSqBody.lean'), 'w').write('\n'.join(o) + '\n')


OUT_REGS = ['a2', 'a3', 'a4', '(8 : Fin 32)', 'a5', '(5 : Fin 32)', 'a1', 'a6', '(6 : Fin 32)', '(9 : Fin 32)']
OUT_NUMS = [12, 13, 14, 8, 15, 5, 11, 16, 6, 9]


def write_mul():
    g, runs, prods, terms, lemmas, body, zfacts = gen_mul()
    o = ['import C3BootProofs.Proofs.Fe25519Decode', '',
         '/-! # The straight-line body of `<&FieldElement2625 as Mul>::mul`, as compiled', '',
         '`scripts/gen-fe25519.py` writes this file from the decoded instructions: a',
         'theorem for each 40 instructions, the facts for each product and sum, and',
         '`fmu_body`, which chains them. -/', '',
         'namespace C3.RV32', '', 'open C3.Image', '']
    for t in g.seg_thms:
        o += [t, '']
    for lm in lemmas:
        o += [lm, '']
    keep = ' ∧\n      '.join(f'memLoad32 M\' (F + 0x{s_:X}) = memLoad32 M (F + 0x{s_:X})' for s_ in MUL_KEEP_SLOTS)
    o += ['set_option maxHeartbeats 40000000 in', 'set_option maxRecDepth 100000 in',
          '/-- **The body of `mul`**, from the first load at 0x2C to the call to `reduce`',
          'at 0x8A8: the ten `u64` sums it stores at `F + 0x98` are `feMulZ` of the',
          'operands\' limbs, it writes nothing outside its frame, and it leaves the',
          'frame slots that hold `out` and the saved registers alone. -/',
          'theorem fmu_body {M : Word → BitVec 8} {B F xp yp : Word} {n : Machine} (s : St M B n 0x2C (reg n))',
          '    (hc : CodeIn M B feMulCode) (hsp : reg n sp = F) (ha1 : reg n a1 = xp) (ha2 : reg n a2 = yp)',
          '    (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)',
          '    (sFC : Sep F 0x120 B feMulCode.length) (sXF : Sep xp 40 F 0x120) (sYF : Sep yp 40 F 0x120) :',
          '    ∃ n\' M\', Steps n n\' ∧ St M\' B n\' 0x8A8 (reg n\') ∧ (∀ x, Sep F 0x120 x 1 → M\' x = M x) ∧',
          f'      {keep} ∧',
          '      [u64At M\' (F + 0x98) 0, u64At M\' (F + 0x98) 1, u64At M\' (F + 0x98) 2, u64At M\' (F + 0x98) 3,',
          '        u64At M\' (F + 0x98) 4, u64At M\' (F + 0x98) 5, u64At M\' (F + 0x98) 6, u64At M\' (F + 0x98) 7,',
          '        u64At M\' (F + 0x98) 8, u64At M\' (F + 0x98) 9] =',
          '        feMulZ (limbAt M xp 0) (limbAt M xp 1) (limbAt M xp 2) (limbAt M xp 3) (limbAt M xp 4)',
          '          (limbAt M xp 5) (limbAt M xp 6) (limbAt M xp 7) (limbAt M xp 8) (limbAt M xp 9)',
          '          (limbAt M yp 0) (limbAt M yp 1) (limbAt M yp 2) (limbAt M yp 3) (limbAt M yp 4)',
          '          (limbAt M yp 5) (limbAt M yp 6) (limbAt M yp 7) (limbAt M yp 8) (limbAt M yp 9) ∧',
          '      reg n\' sp = F ∧ reg n\' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n\' (4 : Fin 32) = reg n (4 : Fin 32) := by',
          '  obtain ⟨G3, hG3⟩ : ∃ g, reg n (3 : Fin 32) = g := ⟨_, rfl⟩',
          '  obtain ⟨G4, hG4⟩ : ∃ g, reg n (4 : Fin 32) = g := ⟨_, rfl⟩']
    o += g.lines
    o += [l for l in body]
    xs = [g.inputs[('xp', 4 * i)] for i in range(10)]
    ys = [g.inputs[('yp', 4 * j)] for j in range(10)]
    for nm, ws, base in (('X', xs, 'xp'), ('Y', ys, 'yp')):
        for i, w in enumerate(ws):
            o.append(f'  obtain ⟨{nm}{i}, e{nm}{i}⟩ : ∃ X, limbAt M {base} {i} = X := ⟨_, rfl⟩')
            o.append(f'  have h{nm}{i} : {w}.toNat = {nm}{i} := by rw [← e{nm}{i}, ← hv{w[1:]}]; rfl')
    g19, g2 = {}, {}
    for (kz, t), (lo, hi, xa, yb, klo, khi) in prods.items():
        i, dbl, j, w19 = terms[kz][t]
        if w19:
            g19.setdefault(j, set()).add(yb)
        if dbl:
            g2.setdefault(i, set()).add(xa)
    eqs = []
    for j, wsx in sorted(g19.items()):
        if len(wsx) != 1:
            raise Exception(f'y{j}*19 in several words {wsx}')
        w = wsx.pop()
        o.append(f'  have g19_{j} : 19 * {ys[j]}.toNat % 2 ^ 32 = {w}.toNat := by rw [t{w[1:]}, Nat.mul_comm]')
        eqs.append(f'g19_{j}')
    for i, wsx in sorted(g2.items()):
        if len(wsx) != 1:
            raise Exception(f'x{i}*2 in several words {wsx}')
        w = wsx.pop()
        o.append(f'  have g2_{i} : 2 * {xs[i]}.toNat % 2 ^ 32 = {w}.toNat := by rw [t{w[1:]}, Nat.pow_one, Nat.mul_comm]')
        eqs.append(f'g2_{i}')
    mlast = g.mem_final
    for kz in range(10):
        lo, hi, hn = zfacts[kz]
        for part, off, w in (('l', 0x98 + 8 * kz, lo), ('h', 0x9C + 8 * kz, hi)):
            si = g.final_slot[('F', off)]
            if g.stores[si][2] != w:
                raise Exception(f'slot {off:#x} holds {g.stores[si][2]}, not {w}')
        o.append(f'  have uz{kz} : u64At {mlast} (F + 0x98) {kz} = {lo}.toNat + 2 ^ 32 * {hi}.toNat := by')
        o.append(f'    unfold u64At')
        o.append(f'    rw [show F + 0x98 + BitVec.ofNat 32 (8 * {kz}) = F + 0x{0x98 + 8 * kz:X} by rw [BitVec.add_assoc]; rfl,')
        o.append(f'      show F + 0x98 + BitVec.ofNat 32 (8 * {kz} + 4) = F + 0x{0x9C + 8 * kz:X} by rw [BitVec.add_assoc]; rfl,')
        o.append(f'      {g.slot_facts[("F", 0x98 + 8 * kz)]}, {g.slot_facts[("F", 0x9C + 8 * kz)]}]')
    steps = g.steps_final
    chain = steps[-1]
    for c in reversed(steps[:-1]):
        chain = f'{c}.trans ({chain})'
    last = len(steps) - 1
    o.append(f'  refine ⟨{g.n_final}, {mlast}, {chain}, ug{last}, frg{last}, ' +
             ', '.join(g.slot_facts[('F', s_)] for s_ in MUL_KEEP_SLOTS) + ', ?_, ' +
             f'{g.reg_facts[2]}, {g.reg_facts[3]}.trans hG3.symm, {g.reg_facts[4]}.trans hG4.symm⟩')
    o.append('  rw [' + ', '.join(f'uz{k}' for k in range(10)) + ', ' + ', '.join(f'eX{i}' for i in range(10)) + ', ' +
             ', '.join(f'eY{i}' for i in range(10)) + ']')
    o.append('  simp only [feMulZ]')
    o.append('  rw [' + ', '.join(f'← hX{i}' for i in range(10)) + ', ' + ', '.join(f'← hY{i}' for i in range(10)) + ']')
    o.append('  rw [' + ', '.join(eqs) + ']')
    o.append('  rw [' + ', '.join(zfacts[k][2] for k in range(10)) + ']')
    o += ['', 'end C3.RV32']
    open(os.path.join(ROOT, 'C3BootProofs/Proofs/FeMulBody.lean'), 'w').write('\n'.join(o) + '\n')


def main():
    write_mul()
    write_sq()
    g, sp, outs, lo, body, lemmas, small = gen_reduce()
    last = g.last
    rds = sorted({i.rd for i in g.block if i.rd})
    keep = sorted(set(range(32)) - set(rds) - {0})
    o = []
    o.append('import C3BootProofs.Proofs.Fe25519Decode')
    o.append('')
    o.append('/-! # The straight-line body of `FieldElement2625::reduce`, as compiled')
    o.append('')
    o.append('`scripts/gen-fe25519.py` writes this file from the decoded instructions. -/')
    o.append('')
    o.append('namespace C3.RV32')
    o.append('')
    o.append('open C3.Image')
    o.append('')
    for lm in lemmas:
        o.append(lm)
        o.append('')
    o.append('/-- The registers `reduce`\'s body leaves alone. -/')
    o.append(f'def frBodyKeep (q : Fin 32) : Bool := q.val ∉ [{", ".join(str(r) for r in rds)}]')
    o.append('')
    o.append('set_option linter.unusedSimpArgs false in')
    o.append('set_option maxHeartbeats 40000000 in')
    o.append('set_option maxRecDepth 100000 in')
    o.append('/-- **The body of `reduce`**, from the first load at 0xC to the first store at')
    o.append('0x1A4: the ten words it leaves for the stores are `feReduceSpec` of the ten')
    o.append('`u64` limbs at `zp`. -/')
    o.append('theorem fr_body {M : Word → BitVec 8} {B zp : Word} {n : Machine} (s : St M B n 0xC (reg n))')
    o.append('    (hc : CodeIn M B feReduceCode) (ha1 : reg n a1 = zp) (hz : zp.toNat % 4 = 0) :')
    o.append('    ∃ n\', Steps n n\' ∧ St M B n\' 0x1A4 (reg n\') ∧')
    regs = ', '.join(f"reg n' {r}" for r in OUT_REGS)
    o.append(f'      [{regs}].map BitVec.toNat =')
    o.append('        feReduceSpec (u64At M zp 0) (u64At M zp 1) (u64At M zp 2) (u64At M zp 3) (u64At M zp 4)')
    o.append('          (u64At M zp 5) (u64At M zp 6) (u64At M zp 7) (u64At M zp 8) (u64At M zp 9) ∧')
    o.append('      ∀ q, frBodyKeep q = true → reg n\' q = reg n q := by')
    o.extend(g.lines)
    o.extend(body)
    outv = []
    for r, num, zname in zip(OUT_REGS, OUT_NUMS, outs):
        v = g.final[num]
        if lo[zname] != v:
            raise Exception(f'output {r} holds {v}, not the low word {lo[zname]} of {zname}')
        outv.append((r, v, zname))
        o.append(f'  have o{num} : reg n{last} {r} = {v} := by rw [u{last}.regs]; simp +decide only [upd, ↓reduceIte]')
    chain = ''.join(f'(.cons d{k} ' for k in range(last)) + f'(.single d{last})' + ')' * last
    o.append(f'  refine ⟨n{last}, {chain}, u{last}.self, ?_, ?_⟩')
    o.append('  · rw [' + ', '.join(f'o{num}' for num in OUT_NUMS) + ', ' +
             ', '.join(f'eZ{k}' for k in range(10)) + ']')
    o.append('    simp only [List.map_cons, List.map_nil, feReduceSpec]')
    o.append('    rw [' + ', '.join(f'e{v[0]}' for v in sp.vals) + ']')
    o.append('    rw [' + ', '.join(f'h{z}' for _, _, z in outv) + ']')
    sm = [z for _, _, z in outv if z in small]
    if sm:
        o.append('    rw [' + ', '.join(f'small_mod (by decide) e{z}' for z in sm) + ']')
    o.append('  · intro q hq')
    o.append(f'    rw [u{last}.regs]')
    ne = ', '.join(f'bkeep_ne hq (r := {lreg(r)}) rfl' for r in rds)
    names = ', '.join(f'q{r}' for r in rds)
    typ = ' ∧ '.join(f'q ≠ {lreg(r)}' for r in rds)
    o.append(f'    have ⟨{names}⟩ : {typ} :=')
    o.append(f'      ⟨{ne}⟩')
    o.append('    by_cases h0 : q.val = 0')
    o.append('    · have : q = 0 := Fin.ext h0')
    o.append('      subst this; simp [upd]; exact s.zero.symm')
    o.append(f'    · simp [upd, h0, {names}]')
    o.append('')
    o.append('end C3.RV32')
    open(os.path.join(ROOT, 'C3BootProofs/Proofs/FeReduceBody.lean'), 'w').write('\n'.join(o) + '\n')


if __name__ == '__main__':
    main()
