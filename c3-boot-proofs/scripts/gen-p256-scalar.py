#!/usr/bin/env python3
"""Writes the generated proof of P-256's `Scalar::mul` body, as compiled:
everything from the return of its `widening_mul_fixed::<8, 8>` call to the
stores of the result, in `P256ScalarBody.lean` and the `P256ScalarSeg*` and
`P256ScalarVal*` files it imports.

The body is `barrett_reduce` from `p256`'s `scalar32.rs`, inlined: the
schoolbook products `q1 · mu` and `q3 · n`, then `sub_inner_nine` and
`subtract_n_if_necessary`, whose 18 `borrowing_sub` calls the compiler kept.
Like gen-scalar-mont.py, it steps each instruction with a fresh name for
its result, in theorems of 40 instructions each, and proves each value the
Rust source computes with one `omega` lemma over the words that hold it.
Two things are new here: the product's limbs are inputs read from the
function's own frame, and a call to `borrowing_sub` is one step, through
`St.bsubCall`, that writes the word below the frame.

Run it from c3-boot-proofs/ after P256ScalarDecode.lean changes; CI checks
that the committed files match.
"""
import importlib.util
import os
import random
import re
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
_spec = importlib.util.spec_from_file_location('smm', os.path.join(HERE, 'gen-scalar-mont.py'))
smm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(smm)
gfe = smm.gfe
addr, kname, lreg, rv = gfe.addr, gfe.kname, gfe.lreg, gfe.rv

M32 = (1 << 32) - 1
MASK = 4294967295
CODE = 'p256ScalarMulCode'
START, END = 0x28, 0xB6A
# `psmBsub B`: borrowing_sub, from the function's start
BSUB = 0x403A2320 - 0x403B2152
MU = [0xEEDF9BFE, 0x012FFD85, 0xDF1A6C21, 0x43190552, 0xFFFFFFFF, 0xFFFFFFFE, 0xFFFFFFFF, 0, 1]
N = [0xFC632551, 0xF3B9CAC2, 0xA7179E84, 0xBCE6FAAD, 0xFFFFFFFF, 0xFFFFFFFF, 0, 0xFFFFFFFF]
IN_SLOTS = [0x2C + 4 * i for i in range(16)]
SAVE_SLOTS = [0x6C + 4 * i for i in range(13)]
OUT_SLOTS = [4 * i for i in range(8)]
SEG = 40
SEG_CHARS_PER_FILE = 160000
LEMMAS_PER_FILE = 70
RUNS = 3000
# LLVM rewrites the products by `0xFFFFFFFF` and `0xFFFFFFFE` (`mu[4..6]`,
# `n[4]`, `n[5]`, `n[7]`) as shifts and subtractions, so some of their words
# hold a value on every input only because of an invariant of the Rust
# arithmetic (`P5h` is `A7 - 1` because `P4h < A7`). Their lemmas would need
# the invariant, so these products and their high words are not taken as
# held: their expressions are inlined into the values computed from them.
NOT_HELD_MULT = ()


def decode():
    src = open(os.path.join(ROOT, 'C3BootProofs/Proofs/P256ScalarDecode.lean')).read()
    ins = []
    for m in re.finditer(rf'theorem (psm_at_\w+) : fetchRel {CODE} (0x[0-9A-Fa-f]+) = '
                         r'some \((.*), (\d)\) := by decide', src):
        ins.append((int(m.group(2), 16), m.group(1), m.group(3), int(m.group(4))))
    ins.sort()
    return [gfe.Ins(*t) for t in ins]


def bsub(l, r, b):
    d = ((MASK if b >> 31 else 0) + l - r) & M32
    nl = l ^ M32
    w = (0 - ((((r & nl) | ((r | nl) & d)) >> 31))) & M32
    return d, w


def simulate(block, calls, regs0, mem, rnd):
    """Runs the block; returns, per instruction, the value it writes. A call
    to `borrowing_sub` sets `a0` and `a1` and leaves junk in `a2`..`a4`, `ra`,
    and the word below `sp`."""
    R = list(regs0)
    mem = dict(mem)
    vals = [None] * len(block)
    k = 0
    while k < len(block):
        i = block[k]
        if k in calls:
            d, w = bsub(R[10], R[11], R[12])
            R[10], R[11] = d, w
            for r in (1, 12, 13, 14):
                R[r] = rnd.getrandbits(32)
            mem[(R[2] - 4) & M32] = rnd.getrandbits(32)
            vals[k], vals[k + 1] = d, w
            k += 2
            continue
        if i.kind == 'store':
            mem[(R[i.rs1] + i.imm) & M32] = R[i.rs2]
            k += 1
            continue
        if i.kind == 'load':
            v = mem[(R[i.rs1] + i.imm) & M32]
        elif i.kind == 'alu':
            v = smm.alu(i.op, R[i.rs1], R[i.rs2])
        elif i.kind == 'aluImm':
            v = smm.alu(i.op, R[i.rs1], i.imm)
        else:
            v = i.imm
        if i.rd:
            R[i.rd] = v
        vals[k] = v
        k += 1
    return vals, R, mem


class Gen(smm.Gen):
    """gen-scalar-mont's stepper, with inputs in frame slots, a slot whose
    first value a hypothesis names, and calls to `borrowing_sub`."""

    def call_ops(self, cur):
        return [rv(cur, 10), rv(cur, 11), rv(cur, 12)]

    def step_seg(self, name, bases, seg, keep_slots, out_slots):
        n = len(self.block)
        calls = self.calls
        rbase = {r[0]: r for r in self.regions}
        cur = dict(self.init)
        self.src, self.var = [None] * n, [None] * n
        self.stores, slots, inputs = [], {}, {}
        reads = {}
        self.masks = set()
        k = 0
        while k < n:
            i = self.block[k]
            if k in calls:
                ops = self.call_ops(cur)
                self.src[k], self.src[k + 1] = ops, ops
                self.var[k], self.var[k + 1] = f'v{k}', f'v{k + 1}'
                self.masks.add(f'v{k + 1}')
                cur[10], cur[11] = f'v{k}', f'v{k + 1}'
                for r in (1, 12, 13, 14):
                    cur[r] = None
                k += 2
                continue
            if i.kind == 'store':
                key = (cur[i.rs1], i.imm)
                self.stores.append((k, key, cur[i.rs2], f'M{k}'))
                slots[key] = len(self.stores) - 1
                self.src[k] = [cur[i.rs2]]
                k += 1
                continue
            v = f'v{k}'
            if i.kind == 'load' and cur.get(i.rs1) in rbase:
                key = (cur[i.rs1], i.imm)
                if key in slots:
                    si = slots[key]
                    reads[k] = si
                    cur[i.rd] = self.stores[si][2]
                    self.src[k] = []
                    k += 1
                    continue
                if key in self.slot_init:
                    cur[i.rd] = self.slot_init[key][0]
                    self.src[k] = []
                    k += 1
                    continue
                if key in inputs:
                    cur[i.rd] = inputs[key]
                    self.src[k] = []
                    k += 1
                    continue
                inputs[key] = v
                self.src[k] = [cur[i.rs1]]
            elif i.kind == 'load':
                raise Exception(i.text)
            elif i.kind == 'alu' and i.op == 'add' and 0 in (i.rs1, i.rs2):
                cur[i.rd] = cur[i.rs2 if i.rs1 == 0 else i.rs1]
                self.src[k] = []
                k += 1
                continue
            elif i.kind == 'alu':
                self.src[k] = [cur.get(i.rs1), cur.get(i.rs2)]
            elif i.kind == 'aluImm':
                self.src[k] = [cur.get(i.rs1)]
            else:
                self.src[k] = []
            self.var[k] = v
            if i.rd:
                cur[i.rd] = v
            k += 1
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

        cur = dict(self.init)
        slotval = {key: f'memLoad32 M0 ({addr(key)})' for key in keep_slots}
        for key, (val, _) in self.slot_init.items():
            slotval[key] = val
        slotsrc = {key: None for key in keep_slots}
        seen_inputs = {}
        bounds = sorted(set(b + 1 if b - 1 in calls else b for b in self.seg_bounds(n, seg)))
        self.seg_thms = []
        self.emit(f'  have fr0 : ∀ x, {ftype} → M x = M x := fun _ {fus} => rfl')
        for key in keep_slots:
            if key not in self.slot_init:
                self.emit(f'  have sg0_{kname(key)} : memLoad32 M ({addr(key)}) = memLoad32 M ({addr(key)}) := rfl')
        mq = {r: self.init_hyp[r] for r in self.init}
        ms = {key: (self.slot_init[key][1] if key in self.slot_init else f'sg0_{kname(key)}') for key in keep_slots}
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
            seg_stores, new_vars, hv_refs, chain = [], [], [], []
            last = None
            k = k0
            while k < k1:
                i = self.block[k]
                nxt = self.block[k + 1].off if k + 1 < n else self.end
                v, u = f'v{k}', f'u{k}'
                simp = f'simp +decide only [upd, ↓reduceIte, {hyps}]'
                if k in calls:
                    l_, r_, b_ = self.call_ops(cur)
                    j2 = self.block[k + 1]
                    nxt = self.block[k + 2].off if k + 2 < n else self.end
                    L.append(f'  obtain ⟨n{k}, d{k}, {u}, ca{k}, cb{k}, cs{k}, ck{k}, cm{k}⟩ := {prev}.bsubCall {hc}')
                    L.append(f'    (psm_code3 hbs sFB sF4B sOB {fr}) (by rw [psmBsub]; exact even_at B hB 0x{BSUB & M32:X} (by decide))')
                    L.append(f'    {i.lemma} {j2.lemma} (by rw [psmBsub, BitVec.add_assoc, BitVec.add_assoc]; rfl)')
                    L.append(f'    (even_at B hB (0x{i.off:X} + 8) (by decide)) (by {simp}) hF sF4B')
                    L.append(f'  {simp} at ca{k} cb{k}')
                    L.append(f'  obtain ⟨{v}, hv{k}⟩ : ∃ v, bsubD {l_} {r_} {b_} = v := ⟨_, rfl⟩')
                    L.append(f'  obtain ⟨v{k + 1}, hv{k + 1}⟩ : ∃ v, bsubB {l_} {r_} {v} = v := ⟨_, rfl⟩')
                    L.append(f'  rw [hv{k}] at ca{k} cb{k}; rw [hv{k + 1}] at cb{k}')
                    L.append(f'  obtain ⟨M{k}, hM{k}⟩ : ∃ M\', n{k}.mem = M\' := ⟨_, rfl⟩')
                    L.append(f'  rw [hM{k}] at {u} cm{k}')
                    L.append(f'  have hc{k} : CodeIn M{k} B {self.code} := psm_code {hc} sF4C cm{k}')
                    L.append(f'  have fr{k} : ∀ x, {ftype} → M{k} x = M0 x := fun x {flam} => by')
                    L.append(f'    rw [cm{k} x {self.regions[1][2]}, {fr} x {flam}]')
                    L.append(f'  have z{k} : reg n{k} 0 = 0 := {u}.zero')
                    new_vars.append((v, f'bsubD {l_} {r_} {b_} = {v}'))
                    new_vars.append((f'v{k + 1}', f'bsubB {l_} {r_} {v} = v{k + 1}'))
                    cur[10], cur[11] = v, f'v{k + 1}'
                    for r in (1, 12, 13, 14):
                        cur[r] = None
                    qs = []
                    for r in sorted(cur):
                        if r == 0 or cur[r] is None or r in (10, 11):
                            continue
                        dec = ' '.join(['(by decide)'] * 6)
                        L.append(f'  have qc{k}_{r} : reg n{k} {lreg(r)} = {cur[r]} := by rw [ck{k} _ {dec}]; {simp}')
                        qs.append(f'qc{k}_{r}')
                    hyps = ', '.join([f'z{k}', f'ca{k}', f'cb{k}'] + qs)
                    mem, hc, fr = f'M{k}', f'hc{k}', f'fr{k}'
                    seg_stores.append((k, ('CALL', 0), None, mem))
                    chain.append(('call', k))
                    prev, last = u, k
                    k += 2
                    continue
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
                    bal = rbase[key[0]][4]
                    stored = slotsrc.get(key) is not None
                    if stored or key in self.slot_init or key in seen_inputs:
                        alias = slotval[key] if (stored or key in self.slot_init) else seen_inputs[key]
                        L.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.lwE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        L.append(f'    (by {simp}; exact aligned_add {bal} (k := {i.imm}) (by decide)) (v := {alias})')
                        tail = '' if (stored or key in self.slot_init) else f'; exact hv{alias[1:]}'
                        L.append(f'    (by {simp}; rw [{self.seg_chain(seg_stores, key)}]{tail})')
                        if not (stored or key in self.slot_init) and int(alias[1:]) < k0 and \
                                alias not in [h for h, _ in hv_refs]:
                            hv_refs.append((alias, f'memLoad32 M0 ({addr(key)}) = {alias}'))
                        cur[i.rd] = alias
                    else:
                        L.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.lwG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        L.append(f'    (by {simp}; exact aligned_add {bal} (k := {i.imm}) (by decide))')
                        L.append(f'  {simp} at hv{k}')
                        L.append(f'  rw [{self.seg_chain(seg_stores, key)}] at hv{k}')
                        seen_inputs[key] = v
                        new_vars.append((v, f'memLoad32 M0 ({addr(key)}) = {v}'))
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
                chain.append(('step', k))
                prev, last = u, k
                k += 1
            qout = sorted(r for r in cur if r != 0 and cur[r] is not None)
            sout = sorted((key for key, si in slotsrc.items() if self.carried(key, si, k1)), key=lambda t: (t[0] != 'F', t))
            for r in qout:
                L.append(f'  have qo{r} : reg n{last} {lreg(r)} = {cur[r]} := by rw [u{last}.regs]; simp +decide only [upd, ↓reduceIte, {hyps}]')
            for key in sout:
                L.append(f'  have so{kname(key)} : memLoad32 {mem} ({addr(key)}) = {slotval[key]} := by')
                L.append(f'    rw [{self.seg_chain(seg_stores, key)}]')
            steps = None
            for kind, kk in reversed(chain):
                if steps is None:
                    steps = f'd{kk}' if kind == 'call' else f'(.single d{kk})'
                else:
                    steps = f'(Steps.trans d{kk} {steps})' if kind == 'call' else f'(.cons d{kk} {steps})'
            parts = [v for v, _ in new_vars] + [steps, f'u{last}.self', hc, fr] + [f'qo{r}' for r in qout] + \
                [f'so{kname(key)}' for key in sout] + [f'hv{v[1:]}' for v, _ in new_vars]
            L.append(f'  exact ⟨n{last}, {mem}, {", ".join(parts)}⟩')
            concl = ['Steps n n\'', f'St M\' B n\' 0x{off_b:X} (reg n\')', f'CodeIn M\' B {self.code}',
                     f'(∀ x, {ftype} → M\' x = M0 x)']
            concl += [f'reg n\' {lreg(r)} = {cur[r]}' for r in qout]
            concl += [f'memLoad32 M\' ({addr(key)}) = {slotval[key]}' for key in sout]
            concl += [st for _, st in new_vars]
            hyps_in = [f'(q{r} : reg n {lreg(r)} = {qinval[r]})' for r in qin]
            hyps_in += [f'(sl{kname(key)} : memLoad32 Mi ({addr(key)}) = {sinval[key]})' for key in sin]
            hyps_in += [f'(hv{h[1:]} : {t})' for h, t in hv_refs]
            text = ' '.join(hyps_in)
            words = sorted(set(gfe.WORD_RE.findall(text)), key=lambda w: int(w[1:]))
            nv = ' '.join(v for v, _ in new_vars)
            thm = ['set_option linter.unusedSimpArgs false in', 'set_option linter.unusedVariables false in',
                   'set_option maxHeartbeats 40000000 in', 'set_option maxRecDepth 100000 in',
                   f'theorem {name}_g{j} {{M0 Mi : Word → BitVec 8}} {{B F {" ".join(self.basenames)} : Word}} {{n : Machine}}'
                   + (f' {{{" ".join(words)} : Word}}' if words else ''),
                   f'    (s : St Mi B n 0x{off_a:X} (reg n)) (hc : CodeIn Mi B {self.code})',
                   f'    (fr : ∀ x, {ftype} → Mi x = M0 x) {self.global_hyps}']
            for h in hyps_in:
                thm.append(f'    {h}')
            thm.append('    : ∃ (n\' : Machine) (M\' : Word → BitVec 8)' + (f' ({nv} : Word)' if nv else '') + ',')
            thm.append('      ' + ' ∧\n      '.join(concl) + ' := by')
            self.seg_thms.append('\n'.join(thm + L))
            s_, hc_, fr_ = mstate
            args = [s_, hc_, fr_, self.global_args] + [mq[r] for r in qin] + [ms[key] for key in sin] + \
                [f'hv{h[1:]}' for h, _ in hv_refs]
            ex = [f'ng{j}', f'Mg{j}'] + [v for v, _ in new_vars]
            conj = [f'cg{j}', f'ug{j}', f'hcg{j}', f'frg{j}'] + \
                [f'qg{j}_{r}' for r in qout] + [f'sg{j + 1}_{kname(key)}' for key in sout] + [f'hv{v[1:]}' for v, _ in new_vars]
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

    def seg_chain(self, seg_stores, key):
        b, o = key
        rws = []
        for k, (b2, os), _, m in reversed(seg_stores):
            if b2 == 'CALL':
                if b == 'F':
                    hs = (f'sep_offsets F (c := {o}) (n := 4) (d := 0xFFFFFFFC) (k := 4) (.inl (by decide)) '
                          f'(by decide) (by decide)')
                else:
                    hs = f'{self.call_sep[b]}.sub (c := {o}) (l := 4) (by decide)'
                rws.append(f'psm_slotS (show Sep ({b} + 0x{o:X}) 4 (F + 0xFFFFFFFC) 4 from {hs}) cm{k}')
                continue
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

    def cone(self, targets, known):
        """The base cone, with a call's two facts together: the mask's fact
        alone doesn't relate it to the call's operands."""
        ks, stops = super().cone(targets, known)
        ks = set(ks)
        for k in list(ks):
            for k2 in ((k + 1,) if k in self.calls else ()) + ((k - 1,) if k - 1 in self.calls else ()):
                ks.add(k2)
                for o in self.src[k2]:
                    if o in self.const:
                        ks.add(self.var.index(o))
        return sorted(ks), stops

    def facts(self):
        """gen-scalar-mont's facts, plus `borrowing_sub` calls and masking
        with a borrow."""
        held = {}
        for k in sorted(self.calls):
            held[k], held[k + 1] = self.var[k], self.var[k + 1]
            self.var[k] = self.var[k + 1] = None
        ands, clears = {}, {}
        for k, i in enumerate(self.block):
            if self.var[k] and i.kind == 'alu' and i.op == 'and' and set(self.src[k]) & self.masks:
                ands[k] = self.var[k]
                self.var[k] = None
            elif self.var[k] and i.kind == 'aluImm' and i.op == 'and' and i.imm == 0xFFFFFFFE:
                clears[k] = self.var[k]
                self.var[k] = None
        super().facts()
        for k, v in held.items():
            self.var[k] = v
        for k, v in list(ands.items()) + list(clears.items()):
            self.var[k] = v
        for k, v in clears.items():
            self.stmt[k] = f'{v}.toNat = {self.src[k][0]}.toNat / 2 * 2'
            self.emit(f'  have t{k} : {self.stmt[k]} := tn_andFE hv{k}')
        # products by 0xFFFFFFFF and 0xFFFFFFFE: add the small-quotient form
        for k, st in list(self.stmt.items()):
            m = re.fullmatch(r'(v\d+)\.toNat = (v\d+)\.toNat \* (4294967295|4294967294) (% 2 \^ 32|/ 2 \^ 32)', st)
            if not m or self.block[k].kind != 'alu':
                continue
            v, a, c, tail = m.groups()
            lem = {('4294967295', '/'): 'psm_hiFF', ('4294967294', '/'): 'psm_hiFE',
                   ('4294967295', '%'): 'psm_loFF', ('4294967294', '%'): 'psm_loFE'}[(c, tail[0])]
            two = '' if c == '4294967295' else '2 * '
            extra = (f'{v}.toNat + ({two}{a}.toNat + 4294967295) / 4294967296 = {a}.toNat' if tail[0] == '/' else
                     f'{v}.toNat + {two}{a}.toNat = 4294967296 * (({two}{a}.toNat + 4294967295) / 4294967296)')
            self.stmt[k] = f'{st} ∧ {extra}'
            self.emit(f'  replace t{k} : {self.stmt[k]} := {lem} t{k}')
        mproof = {}
        for k in sorted(self.calls):
            l_, r_, b_ = self.src[k]
            if b_ == '0':
                hb = '(.inl rfl)'
            elif b_ in self.const and self.const[b_] == 0:
                hb = f'(.inl c{b_[1:]})'
            else:
                hb = mproof[b_]
            d, w = self.var[k], self.var[k + 1]
            self.emit(f'  have pb{k} := psm_bsub hv{k} hv{k + 1} {hb}')
            st = re.sub(r'(?<![\w.])0\.toNat', '0',
                        f'{d}.toNat + {r_}.toNat + {b_}.toNat / {MASK} = {l_}.toNat + 2 ^ 32 * ({w}.toNat / {MASK})')
            self.stmt[k] = st
            self.emit(f'  have t{k} : {st} := pb{k}.1')
            mproof[w] = f'pb{k}.2'
            self.stmt[k + 1] = f'{w}.toNat = 0 ∨ {w}.toNat = {MASK}'
            self.emit(f'  have t{k + 1} : {self.stmt[k + 1]} := psm_mask pb{k}.2')
        for k, v in ands.items():
            a, b = self.src[k]
            m, c = (a, b) if a in self.masks else (b, a)
            lem = 'tn_andM' if m == a else "tn_andM'"
            if c in self.const:
                st = f'{v}.toNat = {self.const[c]} * ({m}.toNat / {MASK})'
                pf = f'by rw [{lem} hv{k} {mproof[m]}, t{c[1:]}]'
            else:
                st = f'{v}.toNat = {c}.toNat * ({m}.toNat / {MASK})'
                pf = f'{lem} hv{k} {mproof[m]}'
            self.stmt[k] = st
            self.emit(f'  have t{k} : {st} := {pf}')


class Spec(smm.Spec):
    def __init__(self):
        super().__init__()
        self.mult = {}


def structured32(name, st, hyps):
    """The proof of a word's value `v = (R) % 2 ^ 32` as an exact identity, as
    gen-scalar-mont's `structured_lemma` does for word pairs: each `% 2 ^ 32`
    fact and each `% 2 ^ 32` inside `R` becomes an equation with a quotient,
    and the identity's quotient coefficients come from expanding the words.
    `omega` then solves equations only."""
    Lin, NonLinear = smm.Lin, smm.NonLinear
    m = re.fullmatch(r'(v\d+)\.toNat = (\(.*\)) % 2 \^ 32', st)
    if not m:
        raise NonLinear()
    v, r0 = m.group(1), m.group(2)
    depth = 0
    for j, ch in enumerate(r0):
        depth += ch == '('
        depth -= ch == ')'
        if depth == 0 and j < len(r0) - 1:
            raise NonLinear()
    defs, keep, qs = {}, [], []
    for h, t_ in hyps:
        mm = re.fullmatch(r'(v\d+)\.toNat = \((.*)\) % 2 \^ 32', t_) or \
            re.fullmatch(r'(v\d+)\.toNat = (v\d+\.toNat \* \d+) % 2 \^ 32', t_)
        if mm and mm.group(1) not in defs:
            defs[mm.group(1)] = (mm.group(2), f'q{h}')
            qs.append(h)
            continue
        mm = re.fullmatch(r'(v\d+)\.toNat \+ 2 \^ 32 \* (v\d+)\.toNat = (v\d+)\.toNat \+ (v\d+)\.toNat', t_)
        if mm and mm.group(1) not in defs:
            defs[mm.group(1)] = (f'{mm.group(3)}.toNat + {mm.group(4)}.toNat - 2 ^ 32 * {mm.group(2)}.toNat', None)
            keep.append(h)
            continue
        mm = re.fullmatch(r'(v\d+)\.toNat = (\d+)', t_)
        if mm and mm.group(1) not in defs:
            defs[mm.group(1)] = (mm.group(2), None)
            keep.append(h)
    cache = {}

    def lin_word(w):
        if w in cache:
            return cache[w]
        if w not in defs:
            res = Lin({w: 1}, 0)
        else:
            e, q = defs[w]
            res = smm.lin_eval(e, [], 2 ** 32)
            res = sum((Lin({k: c}, 0) if k not in defs else lin_word(k) * c for k, c in res.d.items()), Lin({}, res.c))
            if q:
                res = res - Lin({q: 2 ** 32}, 0)
        cache[w] = res
        return res

    mods = []
    for j, (inner, whole) in enumerate(smm.inner_mods(r0, 32)):
        mods.append((f'm{j}', smm.lin_eval(inner, [(nm, l) for nm, l, _, _ in mods], 2 ** 32), inner, whole))
    rl = smm.lin_eval(r0, [(nm, l) for nm, l, _, _ in mods], 2 ** 32)
    for nm, l, _, _ in reversed(mods):
        c = rl.d.pop(nm, 0)
        if c:
            rl = rl + l * c - Lin({'k' + nm[1:]: 2 ** 32 * c}, 0)
    diff = lin_word(v) - rl
    coef = {}
    for k, c in diff.d.items():
        if c % 2 ** 32:
            raise NonLinear()
        coef[k if not gfe.WORD_RE.fullmatch(k) else f'{k}.toNat'] = c // 2 ** 32
    if diff.c % 2 ** 32:
        raise NonLinear()
    c0 = diff.c // 2 ** 32
    pos = [f'{c} * {k}' if c != 1 else k for k, c in coef.items() if c > 0] + ([str(c0)] if c0 > 0 else [])
    neg = [f'{-c} * {k}' if c != -1 else k for k, c in coef.items() if c < 0] + ([str(-c0)] if c0 < 0 else [])
    hs = [(h, t_) for h, t_ in hyps if h in keep or h in qs]
    wset = set(gfe.WORD_RE.findall(st))
    for _, t_ in hs:
        wset |= set(gfe.WORD_RE.findall(t_))
    words = sorted(wset, key=lambda w: int(w[1:]))
    out = [f'theorem {name} {{{" ".join(words)} : Word}}']
    out.append('    ' + '\n    '.join(f'({h} : {t_})' for h, t_ in hs) + ' :')
    out.append(f'    {st} := by')
    for h in qs:
        out.append(f'  obtain ⟨q{h}, eq{h}⟩ := mod_q {h}; clear {h}')
    for j, (nm, _, inner, whole) in enumerate(mods):
        out.append(f'  obtain ⟨k{j}, ek{j}⟩ : ∃ k, {whole} + 2 ^ 32 * k = {inner} := ⟨_, Nat.mod_add_div _ _⟩')
    def sub(s, below):
        for i in reversed(range(below)):
            s = s.replace(mods[i][3], f'm{i}')
        return s

    ms = ' '.join([f'm{j}' for j in range(len(mods))] + [f'k{j}' for j in range(len(mods))])
    binders = f'∀ {ms} : Nat, ' if mods else ''
    prem = ''.join(f'm{j} + 2 ^ 32 * k{j} = {sub(inner, j)} → ' for j, (_, _, inner, _) in enumerate(mods))
    intro = ms + ' ' + ' '.join(f'e{j}' for j in range(len(mods)))
    subd = sorted({w for _, t_ in hs for w in re.findall(r'- (v\d+)\.toNat', t_)}, key=lambda w: int(w[1:]))
    gen = ''.join(f'\n    have := {w}.isLt' for w in subd)
    gen += ''.join(f'\n    generalize {w}.toNat = n{w[1:]} at *' for w in words)
    out.append(f'  have key : {binders}{prem}{v}.toNat + 2 ^ 32 * ({" + ".join(neg) or "0"}) = '
               f'{sub(r0, len(mods))} + 2 ^ 32 * ({" + ".join(pos) or "0"}) := by')
    out.append(f'    {"intro " + intro if mods else "skip"}{gen}')
    out.append('    omega')
    args = ' '.join(['_'] * (2 * len(mods)) + [f'ek{j}' for j in range(len(mods))])
    out.append(f'  exact psm_key32 (key {args}) {v}.isLt')
    return '\n'.join(out), hs


def strategies(text):
    """A fallback lemma's `omega`, tried several ways: `omega` doesn't search
    the dark shadow, so whether it closes a goal depends on the form of the
    facts. The other forms are each `x = E % 2 ^ 32` fact as the equation
    `x + 2 ^ 32 q = E` with a quotient `q`, and case splits on the range of
    each word multiplied by 0xFFFFFFFF or 0xFFFFFFFE and on the `sltu` and mask
    disjunctions, while the cases stay few."""
    if not text.endswith('\n  omega'):
        return text
    quot, conj = [], []
    for h in re.findall(r'\((t\d+) : v\d+\.toNat = v\d+\.toNat \* 429496729[45] [/%] 2 \^ 32 ∧ ', text):
        conj.append(f'obtain ⟨{h}a, {h}b⟩ := {h}')
        if re.search(rf'\({h} : v\d+\.toNat = v\d+\.toNat \* 429496729[45] % ', text):
            quot.append(f'obtain ⟨q{h[1:]}a, e{h[1:]}a⟩ := mod_q {h}a; clear {h}a')
    for h in re.findall(r'\(([tw]\w+) : v\d+\.toNat = [^\n]* % 2 \^ 32\)\n', text):
        quot.append(f'obtain ⟨q{h}, e{h}⟩ := mod_q {h}; clear {h}')
    splits, cases = [], 1
    for w in sorted(set(re.findall(r'\((v\d+)\.toNat \+ 4294967295\) / 4294967296', text)), key=lambda w: int(w[1:])):
        splits.append(f'rcases Nat.eq_zero_or_pos n{w[1:]} with _ | _')
        cases *= 2
    for w in sorted(set(re.findall(r'\(2 \* (v\d+)\.toNat \+ 4294967295\) / 4294967296', text)), key=lambda w: int(w[1:])):
        n = f'n{w[1:]}'
        splits.append(f'rcases (by omega : {n} = 0 ∨ (0 < {n} ∧ {n} ≤ 2147483648) ∨ 2147483648 < {n}) with _ | _ | _')
        cases *= 3
    for h in re.findall(r'\((t\d+) : \(v\d+\.toNat < v\d+\.toNat ∧ v\d+\.toNat = 1\) ∨', text):
        if cases * 2 > 32:
            break
        splits.append(f'rcases {h} with ⟨_, _⟩ | ⟨_, _⟩')
        cases *= 2
    for h in re.findall(r'\((t\d+) : v\d+\.toNat = 0 ∨ v\d+\.toNat = 4294967295\)', text):
        if cases * 2 > 32:
            break
        splits.append(f'rcases {h} with _ | _')
        cases *= 2
    alts = ['omega']
    if splits:
        alts.append('(' + '; '.join(conj + [' <;> '.join(splits + ['omega'])]) + ')')
    if quot:
        alts.append('(' + '; '.join(conj + quot + ['omega']) + ')')
    if quot and splits:
        alts.append('(' + '; '.join(conj + quot + [' <;> '.join(splits + ['omega'])]) + ')')
    if len(alts) == 1:
        return text
    return text[:-len('omega')] + 'first\n' + ''.join(f'    | {a}\n' for a in alts).rstrip('\n')


def build_spec():
    sp = Spec()
    A = [sp.add(f'A{i}', 32, f'a {i}', None, []) for i in range(16)]
    cnt = [0]

    def fresh(p):
        cnt[0] += 1
        return f'{p}{cnt[0]}'

    def term(x):
        return f'{{{x}}}' if isinstance(x, str) else str(x)

    def val(e, x):
        return e[x] if isinstance(x, str) else x

    def split(P):
        lo = sp.add(P + 'l', 32, f'{{{P}}} % 2 ^ 32', lambda e, P=P: e[P] & M32, [P])
        hi = sp.add(P + 'h', 32, f'{{{P}}} / 2 ^ 32', lambda e, P=P: e[P] >> 32, [P])
        return lo, hi

    def cma(x, y, add, carry):
        """`x.carrying_mul_add(y, add, carry)`: the low and high words of
        `x y + add + carry`. `y` is a constant."""
        ts = [] if y == 0 else ([f'{{{x}}}'] if y == 1 else [f'{{{x}}} * {y}'])
        deps = [x] if y else []
        for t in (add, carry):
            if isinstance(t, str):
                ts.append(f'{{{t}}}')
                deps.append(t)
        P = sp.add(fresh('P'), 64, ' + '.join(ts) or '0',
                   lambda e, x=x, y=y, add=add, carry=carry: e[x] * y + val(e, add) + val(e, carry), deps)
        sp.mult[P] = y
        return split(P)

    def cadd(a, b, carry):
        ts, deps = [], []
        for t in (a, b, carry):
            if isinstance(t, str):
                ts.append(f'{{{t}}}')
                deps.append(t)
        if len(ts) == 1:
            return deps[0], 0
        P = sp.add(fresh('S'), 64, ' + '.join(ts),
                   lambda e, a=a, b=b, carry=carry: val(e, a) + val(e, b) + val(e, carry), deps)
        return split(P)

    # q1_times_mu_shift_nine
    q1 = A[7:16]
    w = [0] * 18
    _, c = cma(q1[0], MU[0], 0, 0)
    for j in range(1, 7):
        w[j], c = cma(q1[0], MU[j], 0, c)
    w[7], w[8], w[9] = c, q1[0], 0
    for i in range(1, 9):
        _, c = cma(q1[i], MU[0], w[i], 0)
        for j in range(1, 7):
            w[i + j], c = cma(q1[i], MU[j], w[i + j], c)
        w[i + 7], c = cadd(w[i + 7], 0, c)
        w[i + 8], w[i + 9] = cadd(w[i + 8], q1[i], c)
    q3 = w[9:18]

    # q3_times_n_keep_nine
    r2 = [0] * 9
    r2[0], c = cma(q3[0], N[0], 0, 0)
    for j in range(1, 6):
        r2[j], c = cma(q3[0], N[j], 0, c)
    r2[6], c = c, 0
    r2[7], c = cma(q3[0], N[7], 0, c)
    r2[8] = c
    for i in range(1, 9):
        r2[i], c = cma(q3[i], N[0], r2[i], 0)
        for j in range(i + 1, 9):
            nj = N[j - i]
            if j == 8:
                if nj == 0:
                    r2[8], _ = cadd(r2[8], 0, c)
                else:
                    r2[8], _ = cma(q3[i], nj, r2[8], c)
            elif nj == 0:
                r2[j], c = cadd(r2[j], 0, c)
            else:
                r2[j], c = cma(q3[i], nj, r2[j], c)

    # sub_inner_nine and subtract_n_if_necessary
    def bsub_chain(ls, rs, tag):
        out, b = [], 0
        for i, (l, r) in enumerate(zip(ls, rs)):
            bit = '' if b == 0 else f' - {{{b}}} / {MASK}'
            base = f'{term(l)} + 2 ^ 32 - {term(r)}{bit}'
            deps = [x for x in (l, r, b) if isinstance(x, str)]
            fd = (lambda e, l=l, r=r, b=b: (val(e, l) - val(e, r) - (1 if val(e, b) else 0)) & M32)
            fm = (lambda e, l=l, r=r, b=b: MASK if val(e, l) < val(e, r) + (1 if val(e, b) else 0) else 0)
            d = sp.add(f'{tag}D{i}', 32, f'({base}) % 2 ^ 32', fd, deps)
            m = sp.add(f'{tag}M{i}', 32, f'{MASK} * (1 - ({base}) / 2 ^ 32)', fm, deps)
            out.append(d)
            b = m
        return out, b

    r, _ = bsub_chain(A[0:9], r2, 'U')
    s, m = bsub_chain(r, N + [0], 'V')
    R, c = [], 0
    for i in range(8):
        add = m if N[i] == MASK else (0 if N[i] == 0 else None)
        if add is None:
            t = sp.add(f'K{i}', 32, f'{N[i]} * ({{{m}}} / {MASK})',
                       lambda e, i=i: N[i] if e[m] else 0, [m])
            add = t
        lo, c = cadd(s[i], add, c)
        R.append(lo)
    return sp, A, R


def main():
    ins = decode()
    block = [i for i in ins if START <= i.off < END]
    calls = {k for k in range(len(block) - 1) if block[k].kind == 'auipc' and block[k + 1].kind == 'jalr'}
    g = Gen(block, 'psm', CODE, START, END, {2: 'F', 3: 'G3', 4: 'G4'})
    g.calls = calls
    g.init_hyp = {2: 'hsp', 3: 'hG3', 4: 'hG4'}
    g.slot_init = {('F', 0x28): ('outp', 'hout')}
    g.basenames = ['outp', 'G3', 'G4']
    g.global_hyps = ('(hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)\n'
                     f'    (sFC : Sep F 0xA0 B {CODE}.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B {CODE}.length)\n'
                     f'    (sOC : Sep outp 32 B {CODE}.length) (sOF : Sep outp 32 F 0xA0)\n'
                     '    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)\n'
                     '    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)\n'
                     '    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)\n'
                     '    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)')
    g.global_args = 'hF hO hB sFC sF4C sOC sOF sOF4 hbs sFB sF4B sOB'
    g.regions = [('F', 0xA0, 'hx1', 'sFC', 'hF'), ('(F + 0xFFFFFFFC)', 4, 'hx2', 'sF4C', 'hF'),
                 ('outp', 32, 'hx3', 'sOC', 'hO')]
    g.region_sep = {('outp', 'F'): 'sOF', ('F', 'outp'): 'sOF.symm'}
    g.call_sep = {'outp': 'sOF4'}
    keep = [('F', o) for o in SAVE_SLOTS] + [('F', 0x28)] + [('F', o) for o in IN_SLOTS]
    g.step_seg('psm', {}, SEG, keep, [('outp', o) for o in OUT_SLOTS])
    g.facts()

    sp, A, R = build_spec()
    not_held = set()
    for P, y in sp.mult.items():
        if y in NOT_HELD_MULT:
            not_held |= {P, P + 'h'}
    rnd = random.Random(710)
    runs = []
    n = len(block)
    # Some carries are rare (`mu[1]` is below 2^25), so it takes many runs to
    # tell a word that holds a value from one that holds it but for a carry.
    for t in range(RUNS):
        a = [rnd.getrandbits(32) for _ in range(16)]
        if t % 3 == 0:
            a = [rnd.choice([0, M32, M32 - rnd.getrandbits(8), rnd.getrandbits(32)]) for _ in range(16)]
        regs0 = [rnd.getrandbits(32) for _ in range(32)]
        regs0[0] = 0
        regs0[2] = 0x10000
        mem = {0x10000 + 0x28: 0x3000}
        for k in range(16):
            mem[0x10000 + 0x2C + 4 * k] = a[k]
        vals, regs, mem2 = simulate(block, calls, regs0, mem, rnd)
        env = sp.run({f'A{i}': a[i] for i in range(16)})
        for i, nm in enumerate(R):
            if mem2[0x3000 + 4 * i] != env[nm]:
                raise Exception(f'out[{i}] does not hold {nm}')
        runs.append((vals, env))

    vindex = {v: k for k, v in enumerate(g.var) if v}
    observed = {}

    def obs(name):
        if name not in observed:
            observed[name] = sorted({env[name] for _, env in runs})
        return observed[name]

    def held_closure(name, acc):
        """The held values `name`'s definition reaches, through values no word holds."""
        for d in sp.vals[sp.by[name]][4]:
            if d in words:
                acc.add(d)
            else:
                held_closure(d, acc)
        return acc

    def local_value(name, env):
        """`name`'s value from the held values in `env`, computing the rest."""
        if name in env:
            return env[name]
        _, _, _, fn, deps = sp.vals[sp.by[name]]
        for d in deps:
            local_value(d, env)
        env[name] = fn(env)
        return env[name]

    def sample(d, rnd):
        """A value for operand `d`: one from another run, or an edge value of
        its kind (a bit, a mask, or any word), so rare carries happen."""
        seen = obs(d)
        if rnd.random() < 0.5 or seen[-1] > M32:
            return rnd.choice(runs)[1][d]
        if set(seen) <= {0, 1}:
            return rnd.choice([0, 1])
        if set(seen) <= {0, MASK}:
            return rnd.choice([0, MASK])
        return rnd.choice([0, 1, 2, M32, M32 - 1, 1 << 31, (1 << 31) - 1, rnd.getrandbits(32)])

    def structural(name, cand, part):
        """Whether word `cand` holds `name` (its low or high word, by `part`)
        for any operand values, not only the correlated values of real runs:
        the instructions between the operands' words and `cand`, run on mixed
        and edge operand values, must agree with the Rust value."""
        held = held_closure(name, set())
        known = {}
        for d in held:
            for j, w in enumerate(words[d]):
                known[w] = (d, j)
        # the instructions between the operands' words and `cand`
        cone, stack, seen = set(), [cand], set()
        while stack:
            v = stack.pop()
            if v in seen or v in known or v in g.const or v in (None, '0'):
                continue
            seen.add(v)
            k = vindex.get(v)
            if k is None:
                return False
            if g.block[k].kind == 'load':
                return False
            cone.add(k)
            stack.extend(g.src[k])
        lrnd = random.Random(zlib.crc32(name.encode()))
        for _ in range(200):
            env = {}
            for d in held:
                env[d] = sample(d, lrnd)
            val = {}
            for w, (d, j) in known.items():
                val[w] = env[d] & M32 if j == 0 else env[d] >> 32
            for v, c in g.const.items():
                val[v] = c
            for k in sorted(cone):
                i = g.block[k]
                if k in calls or k - 1 in calls:
                    kc = k if k in calls else k - 1
                    a, b, c = (0 if o == '0' else val[o] for o in g.src[kc])
                    dd, ww = bsub(a, b, c)
                    val[g.var[kc]], val[g.var[kc + 1]] = dd, ww
                    continue
                ops = [0 if o == '0' else val[o] for o in g.src[k]]
                if i.kind == 'alu':
                    val[g.var[k]] = smm.alu(i.op, ops[0], ops[1])
                elif i.kind == 'aluImm':
                    val[g.var[k]] = smm.alu(i.op, ops[0], i.imm)
                else:
                    val[g.var[k]] = i.imm
            want = local_value(name, env)
            if val[cand] != (want & M32 if part == 0 else want >> 32):
                return False
        return True

    def find(f, after=0, name=None, part=0):
        """The first word at or after instruction `after` that holds a value on
        every run and for any operand values: a word before its operands' holds
        it only because of an invariant, and a later one is a recomputation."""
        for k in range(after, n):
            v = g.var[k]
            if v is None or v in g.const:
                continue
            if all(vals[k] == f(env) for vals, env in runs) and (name is None or structural(name, v, part)):
                return v
        return None

    def operand_pos(name):
        """The last instruction that forms a word of the value's operands."""
        pos = 0
        for d in sp.vals[sp.by[name]][4]:
            if d in words:
                pos = max([pos] + [int(w[1:]) for w in words[d]])
            else:
                pos = max(pos, operand_pos(d))
        return pos

    # the words holding each value
    words = {}
    for i in range(16):
        words[A[i]] = (g.inputs[('F', 0x2C + 4 * i)],)
    # the two `borrowing_sub` chains, in call order
    ck = sorted(calls)
    for j, k in enumerate(ck):
        tag, i = ('U', j) if j < 9 else ('V', j - 9)
        words[f'{tag}D{i}'] = (g.var[k],)
        words[f'{tag}M{i}'] = (g.var[k + 1],)
        for vals, env in runs:
            if vals[k] != env[f'{tag}D{i}'] or vals[k + 1] != env[f'{tag}M{i}']:
                raise Exception(f'call {j} does not compute {tag}D{i}')
    final_store = {}
    for k, key, val, _ in g.stores:
        final_store[key] = val
    for i, nm in enumerate(R):
        words[nm] = (final_store[('outp', 4 * i)],)
    for name, bits, _, _, _ in sp.vals:
        if name in words or name in not_held:
            continue
        # the low and high words of a held 64-bit value are its words
        if name[-1] in 'lh' and len(words.get(name[:-1], ())) == 2:
            words[name] = (words[name[:-1]]['lh'.index(name[-1])],)
            continue
        at = operand_pos(name)
        lo = find(lambda e, name=name: e[name] & M32, at, name, 0)
        if bits == 32:
            if lo is not None:
                words[name] = (lo,)
        else:
            hi = find(lambda e, name=name: e[name] >> 32, at, name, 1)
            if lo is not None and hi is not None:
                words[name] = (lo, hi)

    def we(name):
        if name in words:
            w = words[name]
            return f'{w[0]}.toNat' if len(w) == 1 else f'({w[0]}.toNat + 2 ^ 32 * {w[1]}.toNat)'
        _, _, expr, _, deps = sp.vals[sp.by[name]]
        return '(' + re.sub(r'\{(\w+)\}', lambda m: we(m.group(1)), expr) + ')'

    def stmt_of(name):
        _, bits, expr, _, _ = sp.vals[sp.by[name]]
        rhs = re.sub(r'\{(\w+)\}', lambda m: we(m.group(1)), expr)
        w = words[name]
        lhs = f'{w[0]}.toNat' if len(w) == 1 else f'{w[0]}.toNat + 2 ^ 32 * {w[1]}.toNat'
        return f'{lhs} = {rhs}'

    mask_fact = {g.var[k + 1]: (f't{k + 1}', g.stmt[k + 1]) for k in calls}
    lemmas, body = [], []
    earlier = {words[a][0] for a in A}
    wstmt = {}
    for name, bits, expr, _, deps in sp.vals:
        if name in A or name not in words:
            continue
        st = stmt_of(name)
        used = set(gfe.WORD_RE.findall(st.split(' = ', 1)[1]))
        targets = list(words[name])
        ks, stops = g.cone(targets, (earlier | used) - set(targets))
        hyps = [(f't{k}', g.stmt[k]) for k in ks]
        extra = sorted((s_ for s_ in stops if s_ not in used), key=lambda w: int(w[1:]))
        if extra:
            held = []

            def collect(d):
                if d in words:
                    held.append(d)
                else:
                    for dd in sp.vals[sp.by[d]][4]:
                        collect(dd)
            for d in deps:
                collect(d)
            # the 64-bit values that split words come from, then any earlier statement
            cands = held + [d[:-1] for d in held if d[-1] in 'lh' and d[:-1] in sp.by] + list(reversed(wstmt))
            for e_ in extra:
                if any(re.search(rf'\b{e_}\b', t_) for h_, t_ in hyps if h_.startswith('w')):
                    continue
                for d in cands:
                    if d in wstmt and re.search(rf'\b{e_}\b', wstmt[d]):
                        if (f'w{d}', wstmt[d]) not in hyps:
                            hyps.append((f'w{d}', wstmt[d]))
                        break
                else:
                    raise Exception(f'{name}: the cone stops at {e_}, which no operand names')
        text = st + ' '.join(t_ for _, t_ in hyps)
        for w_, fact in mask_fact.items():
            if re.search(rf'\b{w_}\.toNat / {MASK}', text) and fact not in hyps:
                hyps.append(fact)
        wset = set(gfe.WORD_RE.findall(st))
        for _, t_ in hyps:
            wset |= set(gfe.WORD_RE.findall(t_))
        lnm = f'psm_v_{name}'
        try:
            text, hyps = smm.structured_lemma(lnm, st, hyps, wset)
            lemmas.append(smm.comm_products(text))
        except smm.NonLinear:
            try:
                text, hyps = structured32(lnm, st, hyps)
                lemmas.append(text)
            except smm.NonLinear:
                lemmas.append(strategies(smm.comm_products(gfe.lemma(lnm, st, wset, [], hyps))))
        body.append(f'  have w{name} : {st} := {lnm} ' + ' '.join(h for h, _ in hyps))
        wstmt[name] = st
        earlier |= set(targets)

    def lname(name):
        return f'psv{name}'

    defs = []
    for name, bits, expr, _, deps in sp.vals:
        if name in A:
            continue
        rhs = re.sub(r'\{(\w+)\}', lambda m: (f'a {m.group(1)[1:]}' if m.group(1) in A
                                               else f'{lname(m.group(1))} a'), expr)
        defs.append(f'def {lname(name)} (a : Nat → Nat) : Nat := {rhs}')

    names_body = []
    for i in range(16):
        w = words[A[i]][0]
        names_body.append(f'  have h{A[i]} : {w}.toNat = psmIn M F {i} := by')
        names_body.append(f'    rw [psmIn, ite_eq_left (by decide), ← hv{w[1:]}] <;> rfl')
    for name, bits, expr, _, deps in sp.vals:
        if name in A or name not in words:
            continue
        w = words[name]
        lhs = f'{w[0]}.toNat' if len(w) == 1 else f'{w[0]}.toNat + 2 ^ 32 * {w[1]}.toNat'
        held = []

        def collect(d):
            if d in words:
                held.append(d)
            else:
                for dd in sp.vals[sp.by[d]][4]:
                    collect(dd)
        for d in deps:
            collect(d)
        held.sort(key=lambda d: -len(words[d]))
        rw = f'rw [w{name}' + ''.join(f', h{d}' for d in dict.fromkeys(held)) + ']'
        names_body.append(f'  have h{name} : {lhs} = {lname(name)} (psmIn M F) := by')
        names_body.append(f'    {rw} <;> rfl')

    parts = []

    def part(pname, doc, items):
        parts.append(pname)
        p = ['import C3BootProofs.Proofs.P256ScalarDecode', '', f'/-! {doc} -/', '',
             'namespace C3.RV32', '', 'open C3.Image', '']
        for t in items:
            p += [t, '']
        p += ['end C3.RV32']
        open(os.path.join(ROOT, f'C3BootProofs/Proofs/{pname}.lean'), 'w').write('\n'.join(p) + '\n')

    gen = '`scripts/gen-p256-scalar.py` writes this file.'
    groups, cur = [], []
    for i, t in enumerate(g.seg_thms):
        if cur and sum(len(g.seg_thms[j]) for j in cur) + len(t) > SEG_CHARS_PER_FILE:
            groups.append(cur)
            cur = []
        cur.append(i)
    groups.append(cur)
    for k, grp in enumerate(groups):
        lo, hi = grp[0], grp[-1]
        span = f'segment {lo}' if lo == hi else f'segments {lo} to {hi}'
        part(f'P256ScalarSeg{k}', f'# P-256\'s `Scalar::mul`, {span}\n\n'
             f'Each theorem steps 40 instructions. {gen}', [g.seg_thms[j] for j in grp])
    for k, lo in enumerate(range(0, len(lemmas), LEMMAS_PER_FILE)):
        part(f'P256ScalarVal{k}', f'# P-256\'s `Scalar::mul`, values, part {k}\n\n'
             f'Each lemma proves one value the code holds in words from its instructions\' facts. {gen}',
             lemmas[lo:lo + LEMMAS_PER_FILE])
    pdir = os.path.join(ROOT, 'C3BootProofs/Proofs')
    for f in os.listdir(pdir):
        if re.fullmatch(r'P256Scalar(Seg|Val)\d+\.lean', f) and f[:-5] not in parts:
            os.remove(os.path.join(pdir, f))

    o = [f'import C3BootProofs.Proofs.{p}' for p in parts] + ['',
         '/-! # The body of P-256\'s `Scalar::mul`, as compiled', '',
         '`scripts/gen-p256-scalar.py` writes this file from the decoded instructions:',
         'a definition for each value `barrett_reduce` computes, and `psm_body`,',
         'which chains the segment theorems (`P256ScalarSeg*`) and the value lemmas',
         '(`P256ScalarVal*`). -/', '',
         'namespace C3.RV32', '', 'open C3.Image', '']
    o += defs + ['']
    o += ['/-- `barrett_reduce`\'s result limb `j` for the 16 limbs `a`. It is written',
          'with `Nat.rec` rather than `match` so that the kernel reduces `psmOut a 7`',
          'without unfolding the definitions under it. -/',
          'def psmOut (a : Nat → Nat) (j : Nat) : Nat :=']
    o += [f'  Nat.rec (motive := fun _ => Nat) ({lname(nm)} a) (fun j _ =>' for nm in R[:-2]]
    o += [f'  Nat.rec (motive := fun _ => Nat) ({lname(R[-2])} a) (fun _ _ => {lname(R[-1])} a) j' + ') j' * (len(R) - 2), '']
    keep = ' ∧\n      '.join(f'memLoad32 M\' (F + 0x{s_:X}) = memLoad32 M (F + 0x{s_:X})' for s_ in SAVE_SLOTS)
    outs_l = ', '.join(f'memLoad32 M\' (outp + 0x{o_:X})' for o_ in OUT_SLOTS)
    outs_r = ', '.join(f'{lname(nm)} (psmIn M F)' for nm in R)
    gh = g.global_hyps.replace('M0', 'M')
    o += ['set_option maxHeartbeats 40000000 in', 'set_option maxRecDepth 100000 in',
          '/-- **The body of `Scalar::mul`**, from the return of `widening_mul_fixed`',
          'at 0x28 to the epilogue at 0xB6A: it stores `barrett_reduce` of the product\'s',
          'limbs in the frame to `outp`, writes nothing outside the frame, the word below',
          'it, and the result, and leaves the slots that hold the saved registers alone. -/',
          'theorem psm_body {M : Word → BitVec 8} {B F outp : Word} {n : Machine}',
          f'    (s : St M B n 0x{START:X} (reg n)) (hc : CodeIn M B {CODE}) (hsp : reg n sp = F)',
          '    (hout : memLoad32 M (F + 0x28) = outp)',
          f'    {gh} :',
          f'    ∃ n\' M\', Steps n n\' ∧ St M\' B n\' 0x{END:X} (reg n\') ∧',
          '      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 4 x 1 → Sep outp 32 x 1 → M\' x = M x) ∧',
          f'      {keep} ∧',
          f'      [{outs_l}].map BitVec.toNat =',
          f'        [{outs_r}] ∧',
          '      reg n\' sp = F ∧ reg n\' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n\' (4 : Fin 32) = reg n (4 : Fin 32) := by',
          '  obtain ⟨G3, hG3⟩ : ∃ g, reg n (3 : Fin 32) = g := ⟨_, rfl⟩',
          '  obtain ⟨G4, hG4⟩ : ∃ g, reg n (4 : Fin 32) = g := ⟨_, rfl⟩']
    o += g.lines
    o += body
    o += names_body
    steps = g.steps_final
    chain = steps[-1]
    for c in reversed(steps[:-1]):
        chain = f'{c}.trans ({chain})'
    last = len(steps) - 1
    o.append(f'  refine ⟨{g.n_final}, {g.mem_final}, {chain}, ug{last}, frg{last}, ' +
             ', '.join(g.slot_facts[('F', s_)] for s_ in SAVE_SLOTS) + ', ?_, ' +
             f'{g.reg_facts[2]}, {g.reg_facts[3]}.trans hG3.symm, {g.reg_facts[4]}.trans hG4.symm⟩')
    o.append('  rw [' + ', '.join(g.slot_facts[('outp', o_)] for o_ in OUT_SLOTS) + ']')
    o.append('  simp only [List.map_cons, List.map_nil]')
    o.append('  rw [' + ', '.join(f'h{nm}' for nm in R) + ']')
    o += ['', 'end C3.RV32']
    open(os.path.join(ROOT, 'C3BootProofs/Proofs/P256ScalarBody.lean'), 'w').write('\n'.join(o) + '\n')
    print(f'{len(lemmas)} value lemmas, {len(g.seg_thms)} segments, '
          f'{sum(1 for v in sp.vals if v[0] not in words)} values inlined')


if __name__ == '__main__':
    main()
