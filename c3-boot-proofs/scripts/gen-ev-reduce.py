#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/EdvReduceBody.lean and the EdvReduceSeg and
EdvReduceVal files it imports: the straight-line `Scalar::reduce` that
`ed25519_verify` inlines into its check that `S` is canonical.

From 0x17C to 0xEE4 the compiled code splits the eight words at
`sp + 0x9F0` into nine 29-bit limbs (`Scalar29::from_bytes`), multiplies them
by `constants::R` (`mul_internal`, with `R`'s limbs and their Karatsuba sums
folded into constants), and runs `montgomery_reduce` up to the limbs' low
words, which the next instructions mask and store. The proof is written the
way gen-scalar-mont.py writes `montgomery_mul`'s: each instruction's result
gets a name and a natural-number fact, random runs find the words that hold
each value of the Rust source, and one lemma proves each such value from
the facts between it and its operands. This block also addresses the stack
through registers that hold `sp` plus a constant, so the stepper tracks
those as offsets from `F`, and it reads its inputs from the frame above the
slots it spills to.

Run it from c3-boot-proofs/ after EdVerifyDecode.lean changes; CI checks
that the committed files match.
"""
import importlib.util
import os
import random
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
_spec = importlib.util.spec_from_file_location('gsm', os.path.join(HERE, 'gen-scalar-mont.py'))
gsm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gsm)
gfe = gsm.gfe

M32, M64 = gsm.M32, gsm.M64
MASK = (1 << 29) - 1
LFACTOR, L = gsm.LFACTOR, gsm.L
RL = [0x114DF9ED, 0x1A617303, 0x0F7C098C, 0x16793167, 0x1FFD656E, 0x1FFFFFFF, 0x1FFFFFFF, 0x1FFFFFFF, 0x000FFFFF]
START, END = 0x17C, 0xEE4
FSZ = 0x128
WOFF = 0x9F0
KEEP_SLOTS = [0x10, 0xD0]
OUT_SLOT = 0xC
OUT_REGS = [16, 7, 6, 5, 28, 9, 8, 11, 10]
SEG_CHARS_PER_FILE = 160000
LEMMAS_PER_FILE = 70
ALIAS = re.compile(r'^F \+ 0x([0-9A-F]+)$')


def fofs(val):
    """The offset from `F` that a register holding `val` points at, or None."""
    if val == 'F':
        return 0
    m = ALIAS.match(val or '')
    return int(m.group(1), 16) if m else None


def norm(c, imm):
    """A rewrite of `F + c + imm` to `F + (c + imm)`, or nothing when c is 0."""
    if c == 0:
        return None
    return (f'show F + 0x{c:X} + 0x{imm:X} = F + 0x{c + imm:X} from by rw [BitVec.add_assoc]; rfl')


def decode():
    src = open(os.path.join(ROOT, 'C3BootProofs/Proofs/EdVerifyDecode.lean')).read()
    ins = []
    for m in re.finditer(r'theorem (ev_at_\w+) : fetchRel ed25519VerifyCode (0x[0-9A-Fa-f]+) = '
                         r'some \((.*), (\d)\) := by ', src):
        ins.append((int(m.group(2), 16), m.group(1), m.group(3), int(m.group(4))))
    ins.sort()
    return [gfe.Ins(*t) for t in ins if START <= t[0] < END]


class Gen(gsm.Gen):
    """gen-scalar-mont's stepper, with registers that point into the frame."""

    def step_seg(self, name, seg, keep_slots, out_slots):
        n = len(self.block)
        # a dry run for the bookkeeping: operands, stores, and which store each slot load reads
        cur = dict(self.init)
        self.src, self.var = [], [None] * n
        self.stores, slots, inputs = [], {}, {}
        reads = {}
        for k, i in enumerate(self.block):
            if i.kind == 'store':
                c = fofs(cur[i.rs1])
                if c is None or c + i.imm + 4 > FSZ:
                    raise Exception(i.text)
                key = ('F', c + i.imm)
                self.stores.append((k, key, cur[i.rs2], f'M{k}'))
                slots[key] = len(self.stores) - 1
                self.src.append([cur[i.rs2]])
                continue
            v = f'v{k}'
            if i.kind == 'aluImm' and i.op == 'add' and fofs(cur.get(i.rs1)) is not None:
                cur[i.rd] = f'F + 0x{fofs(cur[i.rs1]) + i.imm:X}'
                self.src.append([])
                continue
            if i.kind == 'load':
                c = fofs(cur.get(i.rs1))
                if c is None:
                    raise Exception(i.text)
                key = ('F', c + i.imm)
                if key[1] < FSZ:
                    si = slots[key]
                    reads[k] = si
                    cur[i.rd] = self.stores[si][2]
                    self.src.append([])
                    continue
                if key in inputs:
                    cur[i.rd] = inputs[key]
                    self.src.append([])
                    continue
                inputs[key] = v
                self.src.append([])
            elif i.kind == 'alu' and i.op == 'add' and 0 in (i.rs1, i.rs2):
                cur[i.rd] = cur[i.rs2 if i.rs1 == 0 else i.rs1]
                self.src.append([])
                continue
            elif i.kind == 'alu':
                for r in (i.rs1, i.rs2):
                    if fofs(cur.get(r)) is not None:
                        raise Exception(i.text)
                self.src.append([cur.get(i.rs1), cur.get(i.rs2)])
            elif i.kind == 'aluImm':
                if fofs(cur.get(i.rs1)) is not None:
                    raise Exception(i.text)
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
        ftype = f'Sep F 0x{FSZ:X} x 1'

        cur = dict(self.init)
        slotval = {key: f'memLoad32 M0 ({gfe.addr(key)})' for key in keep_slots}
        slotsrc = {key: None for key in keep_slots}
        seen_inputs = {}
        bounds = self.seg_bounds(n, seg)
        self.seg_thms = []
        self.emit('  have fr0 : ∀ x, Sep F 0x%X x 1 → M x = M x := fun _ _ => rfl' % FSZ)
        for key in keep_slots:
            self.emit(f'  have sg0_{gfe.kname(key)} : memLoad32 M ({gfe.addr(key)}) = memLoad32 M ({gfe.addr(key)}) := rfl')
        mq = {r: self.init_hyp[r] for r in self.init}
        ms = {key: f'sg0_{gfe.kname(key)}' for key in keep_slots}
        mstate = ('s', 'hc', 'fr0')
        csteps = []
        for j in range(len(bounds) - 1):
            k0, k1 = bounds[j], bounds[j + 1]
            off_a = self.block[k0].off
            off_b = self.block[k1].off if k1 < n else self.end
            qin = sorted(r for r in cur if r != 0 and cur[r] is not None)
            qinval = {r: cur[r] for r in qin}
            sin = sorted((key for key, si in slotsrc.items() if self.carried(key, si, k0)), key=lambda t: t)
            sinval = {key: slotval[key] for key in sin}
            Ls = ['  have hz0 : reg n 0 = 0 := s.zero']
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
                    c = fofs(cur[i.rs1])
                    key = ('F', c + i.imm)
                    nr = norm(c, i.imm)
                    pre = f'rw [{nr}]; ' if nr else ''
                    Ls.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.swG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                    Ls.append(f'    (by {simp}; {pre}exact aligned_add hF (k := {key[1]}) (by decide)) (a := {gfe.addr(key)}) (v := {val})')
                    Ls.append(f'    (by {simp}{"; " + pre[:-2] if pre else ""}) (by {simp})')
                    Ls.append(f'  obtain ⟨Mm{k}, hM{k}⟩ : ∃ M\', memStore32 {mem} ({gfe.addr(key)}) {val} = M\' := ⟨_, rfl⟩')
                    Ls.append(f'  rw [hM{k}] at {u}')
                    Ls.append(f'  have hc{k} : CodeIn Mm{k} B ed25519VerifyCode := by rw [← hM{k}]; exact {hc}.store32 (frm_sep\' sFC (by decide))')
                    Ls.append(f'  have fr{k} : ∀ x, {ftype} → Mm{k} x = M0 x := fun x hx => by')
                    Ls.append(f'    rw [← hM{k}, memStore32_get_sep (frm_sep\' hx (by decide)), {fr} x hx]')
                    mem, hc, fr = f'Mm{k}', f'hc{k}', f'fr{k}'
                    seg_stores.append((k, key, val, mem))
                    slotsrc[key] = store_at[k]
                    slotval[key] = val
                elif i.kind == 'aluImm' and i.op == 'add' and fofs(cur.get(i.rs1)) is not None:
                    c = fofs(cur[i.rs1])
                    a = f'F + 0x{c + i.imm:X}'
                    pf = 'rfl' if c == 0 else f'show F + 0x{c:X} + 0x{i.imm:X} = _; rw [BitVec.add_assoc]; rfl'
                    Ls.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.aluImmE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide) (v := {a})')
                    Ls.append(f'    (by {simp}; {pf})')
                    cur[i.rd] = a
                elif i.kind == 'load':
                    c = fofs(cur[i.rs1])
                    key = ('F', c + i.imm)
                    nr = norm(c, i.imm)
                    pre = f'rw [{nr}]; ' if nr else ''
                    al = f'(by {simp}; {pre}exact aligned_add hF (k := {key[1]}) (by decide))'
                    if key[1] < FSZ:
                        alias = slotval[key]
                        Ls.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.lwE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        Ls.append(f'    {al} (v := {alias})')
                        Ls.append(f'    (by {simp}; {pre}rw [{self.seg_chain(seg_stores, key)}])')
                        cur[i.rd] = alias
                        continue_load = True
                    else:
                        load = (f'load_frame {fr} (show Sep F 0x{FSZ:X} ({gfe.addr(key)}) 4 from '
                                f'ev_sepIn F {key[1]} (by decide) (by decide))')
                        if key in seen_inputs:
                            alias = seen_inputs[key]
                            Ls.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.lwE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                            Ls.append(f'    {al} (v := {alias})')
                            Ls.append(f'    (by {simp}; {pre}rw [{load}]; exact hv{alias[1:]})')
                            if int(alias[1:]) < k0 and alias not in [h for h, _ in hv_refs]:
                                hv_refs.append((alias, f'memLoad32 M0 ({gfe.addr(key)}) = {alias}'))
                            cur[i.rd] = alias
                        else:
                            Ls.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.lwG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                            Ls.append(f'    {al}')
                            Ls.append(f'  {simp} at hv{k}')
                            if nr:
                                Ls.append(f'  rw [{nr}] at hv{k}')
                            Ls.append(f'  rw [{load}] at hv{k}')
                            seen_inputs[key] = v
                            new_vars.append((v, f'memLoad32 M0 ({gfe.addr(key)}) = {v}'))
                            cur[i.rd] = v
                elif i.kind == 'alu' and i.op == 'add' and 0 in (i.rs1, i.rs2):
                    alias = cur[i.rs2 if i.rs1 == 0 else i.rs1]
                    Ls.append(f'  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.aluE {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide) (v := {alias})')
                    Ls.append(f'    (by {simp}; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)')
                    cur[i.rd] = alias
                else:
                    if i.kind == 'alu':
                        Ls.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        stmt = f'aluEval .{i.op} {gfe.rv(cur, i.rs1)} {gfe.rv(cur, i.rs2)} = {v}'
                    elif i.kind == 'aluImm':
                        Ls.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluImmG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        stmt = f'aluEval .{i.op} {gfe.rv(cur, i.rs1)} 0x{i.imm:X} = {v}'
                    else:
                        Ls.append(f'  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.luiG {hc} {i.lemma} (off\' := 0x{nxt:X}) (by decide)')
                        stmt = f'(0x{i.imm:X} : Word) = {v}'
                    if i.kind != 'lui':
                        Ls.append(f'  {simp} at hv{k}')
                    new_vars.append((v, stmt))
                    if i.rd:
                        cur[i.rd] = v
                prev = u
            last_k = k1 - 1
            qout = sorted(r for r in cur if r != 0 and cur[r] is not None)
            sout = sorted((key for key, si in slotsrc.items() if self.carried(key, si, k1)), key=lambda t: t)
            for r in qout:
                Ls.append(f'  have qo{r} : reg n{last_k} {gfe.lreg(r)} = {cur[r]} := by rw [u{last_k}.regs]; simp +decide only [upd, ↓reduceIte, {hyps}]')
            for key in sout:
                Ls.append(f'  have so{gfe.kname(key)} : memLoad32 {mem} ({gfe.addr(key)}) = {slotval[key]} := by')
                Ls.append(f'    rw [{self.seg_chain(seg_stores, key)}]')
            steps = ''.join(f'(.cons d{k} ' for k in range(k0, last_k)) + f'(.single d{last_k})' + ')' * (last_k - k0)
            parts = [v for v, _ in new_vars] + [steps, f'u{last_k}.self', hc, fr] + [f'qo{r}' for r in qout] + \
                [f'so{gfe.kname(key)}' for key in sout] + [f'hv{v[1:]}' for v, _ in new_vars]
            Ls.append(f'  exact ⟨n{last_k}, {mem}, {", ".join(parts)}⟩')
            concl = ['Steps n n\'', f'St M\' B n\' 0x{off_b:X} (reg n\')', 'CodeIn M\' B ed25519VerifyCode',
                     f'(∀ x, {ftype} → M\' x = M0 x)']
            concl += [f'reg n\' {gfe.lreg(r)} = {cur[r]}' for r in qout]
            concl += [f'memLoad32 M\' ({gfe.addr(key)}) = {slotval[key]}' for key in sout]
            concl += [st for _, st in new_vars]
            hyps_in = [f'(q{r} : reg n {gfe.lreg(r)} = {qinval[r]})' for r in qin]
            hyps_in += [f'(sl{gfe.kname(key)} : memLoad32 Mi ({gfe.addr(key)}) = {sinval[key]})' for key in sin]
            hyps_in += [f'(hv{h[1:]} : {t})' for h, t in hv_refs]
            text = ' '.join(hyps_in)
            words = sorted(set(gfe.WORD_RE.findall(text)), key=lambda w: int(w[1:]))
            nv = ' '.join(v for v, _ in new_vars)
            thm = ['set_option linter.unusedSimpArgs false in', 'set_option linter.unusedVariables false in',
                   'set_option maxHeartbeats 40000000 in', 'set_option maxRecDepth 100000 in',
                   f'theorem {name}_g{j} {{M0 Mi : Word → BitVec 8}} {{B F {" ".join(self.basenames)} : Word}} {{n : Machine}}'
                   + (f' {{{" ".join(words)} : Word}}' if words else ''),
                   f'    (s : St Mi B n 0x{off_a:X} (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)',
                   f'    (fr : ∀ x, {ftype} → Mi x = M0 x) {self.global_hyps}']
            for h in hyps_in:
                thm.append(f'    {h}')
            thm.append('    : ∃ (n\' : Machine) (M\' : Word → BitVec 8)' + (f' ({nv} : Word)' if nv else '') + ',')
            thm.append('      ' + ' ∧\n      '.join(concl) + ' := by')
            self.seg_thms.append('\n'.join(thm + Ls))
            s_, hc_, fr_ = mstate
            args = [s_, hc_, fr_, self.global_args] + [mq[r] for r in qin] + [ms[key] for key in sin] + \
                [f'hv{h[1:]}' for h, _ in hv_refs]
            ex = [f'ng{j}', f'Mg{j}'] + [v for v, _ in new_vars]
            conj = [f'cg{j}', f'ug{j}', f'hcg{j}', f'frg{j}'] + \
                [f'qg{j}_{r}' for r in qout] + [f'sg{j + 1}_{gfe.kname(key)}' for key in sout] + \
                [f'hv{v[1:]}' for v, _ in new_vars]
            self.emit(f'  obtain ⟨{", ".join(ex)}, hg{j}⟩ := {name}_g{j} {" ".join(args)}')
            for idx, c_ in enumerate(conj):
                path = f'hg{j}' + '.2' * idx + ('.1' if idx < len(conj) - 1 else '')
                self.emit(f'  have {c_} := {path}')
            mq = {r: f'qg{j}_{r}' for r in qout}
            ms = {key: f'sg{j + 1}_{gfe.kname(key)}' for key in sout}
            mstate = (f'ug{j}', f'hcg{j}', f'frg{j}')
            csteps.append(f'cg{j}')
        self.mem_final = f'Mg{len(bounds) - 2}'
        self.slot_facts = ms
        self.reg_facts = mq
        self.steps_final = csteps
        self.n_final = f'ng{len(bounds) - 2}'


def build_spec():
    sp = gsm.Spec()
    W = [sp.add(f'W{i}', 32, f'w {i}', None, []) for i in range(8)]
    A = [sp.add('A0', 32, '{W0} % 2 ^ 29', lambda e: e['W0'] & MASK, ['W0'])]
    for i, (r, lsh) in enumerate([(29, 3), (26, 6), (23, 9), (20, 12), (17, 15), (14, 18), (11, 21)]):
        h = sp.add(f'SR{i + 1}', 32, f'{{W{i}}} / 2 ^ {r}', lambda e, i=i, r=r: e[f'W{i}'] >> r, [f'W{i}'])
        gg = sp.add(f'SL{i + 1}', 32, f'{{W{i + 1}}} * 2 ^ {lsh} % 2 ^ 32',
                    lambda e, i=i, lsh=lsh: (e[f'W{i + 1}'] << lsh) & M32, [f'W{i + 1}'])
        o = sp.add(f'O{i + 1}', 32, f'{{{h}}} + {{{gg}}}', lambda e, h=h, gg=gg: e[h] + e[gg], [h, gg])
        A.append(sp.add(f'A{i + 1}', 32, f'{{{o}}} % 2 ^ 29', lambda e, o=o: e[o] & MASK, [o]))
    A.append(sp.add('A8', 32, '{W7} / 2 ^ 8', lambda e: e['W7'] >> 8, ['W7']))
    B = [sp.add(f'B{i}', 32, f'{RL[i]}', lambda e, c=RL[i]: c, []) for i in range(9)]

    def prod(x, y):
        return sp.add(f'P{x}{y}', 64, f'{{{x}}} * {{{y}}}', lambda e: e[x] * e[y], [x, y])

    def cprod(x, c, j):
        return sp.add(f'P{x}L{j}', 64, f'{{{x}}} * {c}', lambda e: e[x] * c, [x])

    def wsum(name, terms):
        return sp.add(name, 64, '(' + ' + '.join(f'{{{t}}}' for t in terms) + ') % 2 ^ 64',
                      lambda e: sum(e[t] for t in terms) & M64, list(terms))

    def wsub(name, x, y):
        return sp.add(name, 64, f'({{{x}}} + (2 ^ 64 - {{{y}}})) % 2 ^ 64',
                      lambda e: (e[x] - e[y]) & M64, [x, y])

    def add32(name, x, y):
        return sp.add(name, 32, f'({{{x}}} + {{{y}}}) % 2 ^ 32', lambda e: (e[x] + e[y]) & M32, [x, y])

    def pa(i, j):
        return prod(A[i], B[j])

    Z0 = pa(0, 0)
    Z1 = wsum('Z1', [pa(0, 1), pa(1, 0)])
    Z2 = wsum('Z2', [pa(0, 2), pa(1, 1), pa(2, 0)])
    Z3 = wsum('Z3', [pa(0, 3), pa(1, 2), pa(2, 1), pa(3, 0)])
    Z4 = wsum('Z4', [pa(0, 4), pa(1, 3), pa(2, 2), pa(3, 1), pa(4, 0)])
    Z5a = wsum('Z5a', [pa(1, 4), pa(2, 3), pa(3, 2), pa(4, 1)])
    Z6a = wsum('Z6a', [pa(2, 4), pa(3, 3), pa(4, 2)])
    Z7a = wsum('Z7a', [pa(3, 4), pa(4, 3)])
    Z8a = wsub('Z8a', pa(4, 4), Z3)
    Z10a = wsub('Z10a', Z5a, pa(5, 5))
    # R's limbs 5 to 7 are equal, so the compiled code forms Q12 as Q11 plus one product
    Q11 = wsum('Q11', [pa(5, 6), pa(6, 5)])
    Z11a = wsub('Z11a', Z6a, Q11)
    Z12a = wsub('Z12a', Z7a, wsum('Q12', [Q11, pa(7, 5)]))
    Z13 = wsum('Z13', [pa(5, 8), pa(6, 7), pa(7, 6), pa(8, 5)])
    Z14 = wsum('Z14', [pa(6, 8), pa(7, 7), pa(8, 6)])
    Z15 = wsum('Z15', [pa(7, 8), pa(8, 7)])
    Z16 = pa(8, 8)
    Z5b = wsub('Z5b', Z10a, Z0)
    Z6b = wsub('Z6b', Z11a, Z1)
    Z7b = wsub('Z7b', Z12a, Z2)
    Z8b = wsub('Z8b', Z8a, Z13)
    Z9a = wsum('Z9a', [Z14, Z4])
    Z10b = wsum('Z10b', [Z15, Z10a])
    Z11b = wsum('Z11b', [Z16, Z11a])
    AA = [add32(f'AA{k}', A[k], A[k + 5]) for k in range(4)]
    BB = [add32(f'BB{k}', B[k], B[k + 5]) for k in range(4)]
    Z5 = wsum('Z5', [prod(AA[0], BB[0]), Z5b])
    Z6 = wsum('Z6', [wsum('K6', [prod(AA[0], BB[1]), prod(AA[1], BB[0])]), Z6b])
    Z7 = wsum('Z7', [wsum('K7', [prod(AA[0], BB[2]), prod(AA[1], BB[1]), prod(AA[2], BB[0])]), Z7b])
    Z8 = wsum('Z8', [wsum('K8', [prod(AA[0], BB[3]), prod(AA[1], BB[2]), prod(AA[2], BB[1]),
                                 prod(AA[3], BB[0])]), Z8b])
    Z9 = wsub('Z9', wsum('K9', [prod(AA[0], B[4]), prod(AA[1], BB[3]), prod(AA[2], BB[2]), prod(AA[3], BB[1]),
                                prod(A[4], BB[0])]), Z9a)
    Z10 = wsub('Z10', wsum('K10', [prod(AA[1], B[4]), prod(AA[2], BB[3]), prod(AA[3], BB[2]),
                                   prod(A[4], BB[1])]), Z10b)
    Z11 = wsub('Z11', wsum('K11', [prod(AA[2], B[4]), prod(AA[3], BB[3]), prod(A[4], BB[2])]), Z11b)
    Z12 = wsub('Z12', wsum('K12', [prod(AA[3], B[4]), prod(A[4], BB[3])]), Z12a)
    Z = [Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16]

    N, C, R = [], [], []
    S = Z[0]
    for i in range(17):
        if i > 0:
            terms = [C[i - 1], Z[i]]
            for j in range(9):
                k = i - j
                if 0 <= j < len(N) and 1 <= k <= 8 and L[k]:
                    terms.append(cprod(N[j], L[k], k))
            S = wsum(f'S{i}', terms)
        if i < 9:
            nn = sp.add(f'N{i}', 32, f'({{{S}}} % 2 ^ 32 * {LFACTOR} % 2 ^ 32) % 2 ^ 29',
                        lambda e, S=S: ((e[S] & M32) * LFACTOR & M32) & MASK, [S])
            N.append(nn)
            t = wsum(f'T{i}', [S, cprod(nn, L[0], 0)])
            C.append(sp.add(f'C{i}', 64, f'{{{t}}} / 2 ^ 29', lambda e, t=t: e[t] >> 29, [t]))
        else:
            R.append(sp.add(f'R{i - 9}', 32, f'{{{S}}} % 2 ^ 32', lambda e, S=S: e[S] & M32, [S]))
            if i < 16:
                C.append(sp.add(f'C{i}', 64, f'{{{S}}} / 2 ^ 29', lambda e, S=S: e[S] >> 29, [S]))
    # the code forms the top limb, `carry as u32`, from the last sum's two words
    sh = sp.add('S16h', 32, f'{{{S}}} / 2 ^ 32', lambda e, S=S: e[S] >> 32, [S])
    R.append(sp.add('R8', 32, f'({{{R[7]}}} / 2 ^ 29 + {{{sh}}} * 2 ^ 3) % 2 ^ 32',
                    lambda e: ((e[R[7]] >> 29) + (e[sh] << 3)) & M32, [R[7], sh]))
    return sp, W, B, R


class Iv:
    """An interval of natural numbers, for the bounds a narrow value's lemma needs."""

    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi

    def __add__(self, o):
        o = iv_of(o)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __sub__(self, o):
        o = iv_of(o)
        return Iv(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return iv_of(o) - self

    def __mul__(self, o):
        o = iv_of(o)
        c = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return Iv(min(c), max(c))

    __rmul__ = __mul__

    def __floordiv__(self, o):
        return Iv(self.lo // o, self.hi // o)

    def __mod__(self, o):
        return self if 0 <= self.lo and self.hi < o else Iv(0, o - 1)


def iv_of(x):
    return x if isinstance(x, Iv) else Iv(x, x)


def iv_eval(expr, I):
    """The interval of a spec expression (`{Name}`, numerals, `+ - * / % ^`,
    parentheses, with Lean's precedence) over the intervals `I` of its names."""
    toks = re.findall(r'\{\w+\}|\d+|[-+*/%^()]', expr)
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
        if t.startswith('{'):
            return I[t[1:-1]]
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
            v = iv_of(v) * r if op == '*' else iv_of(v) // r if op == '/' else iv_of(v) % r
        return v

    def add():
        v = mul()
        while peek() in ('+', '-'):
            op = take()
            r = mul()
            v = iv_of(v) + r if op == '+' else iv_of(v) - r
        return v

    return iv_of(add())


def lname(name):
    return f'evr{name}'


def main():
    ins = decode()
    block = [i for i in ins if START <= i.off < END]
    g = Gen(block, 'evr', 'ed25519VerifyCode', START, END,
            {2: 'F', 20: f'F + 0x{0x90F:X}', 21: 'G21', 3: 'G3', 4: 'G4'})
    g.init_hyp = {2: 'hsp', 20: 'hs4', 21: 'hs5', 3: 'hG3', 4: 'hG4'}
    g.basenames = ['G21', 'G3', 'G4']
    g.global_hyps = f'(hF : F.toNat % 4 = 0) (sFC : Sep F 0x{FSZ:X} B ed25519VerifyCode.length)'
    g.global_args = 'hF sFC'
    keep = [('F', o) for o in KEEP_SLOTS]
    g.step_seg('evr', 40, keep, [('F', OUT_SLOT)])
    g.facts()

    sp, W, B, R = build_spec()
    rnd = random.Random(710)
    runs = []
    SP0 = 0x10000
    for t in range(160):
        if t % 4 == 0:
            w = [M32 ^ (rnd.getrandbits(32) & rnd.getrandbits(32) & rnd.getrandbits(32)) for _ in range(8)]
        elif t % 4 == 1:
            w = [rnd.getrandbits(32) & rnd.getrandbits(32) & rnd.getrandbits(32) for _ in range(8)]
        else:
            w = [rnd.getrandbits(32) for _ in range(8)]
        regs0 = [0] * 32
        regs0[2], regs0[20], regs0[21] = SP0, SP0 + 0x90F, 0x4444
        mem = {}
        for k in range(8):
            mem[SP0 + WOFF + 4 * k] = w[k]
        vals, regs = gfe.simulate(block, regs0, mem)
        env = sp.run({f'W{i}': w[i] for i in range(8)})
        for r_, nm in zip(OUT_REGS, R):
            if regs[r_] != env[nm]:
                raise Exception(f'register {r_} does not hold {nm}')
        runs.append((vals, env))
    n = len(block)
    consts = {v[0] for v in sp.vals if v[0] in B}

    pos = {g.var[k]: k for k in range(n) if g.var[k] is not None}
    words = {}
    for i in range(8):
        words[W[i]] = (g.inputs[('F', WOFF + 4 * i)],)

    def lower(name):
        """The last instruction that writes a word one of `name`'s operands is held in."""
        best = -1
        for d in sp.vals[sp.by[name]][4]:
            if d in consts:
                continue
            if d in words:
                best = max(best, min(pos[w_] for w_ in words[d]))
            else:
                best = max(best, lower(d))
        return best

    def cands(f, lb):
        """The words after `lb` that hold `f` of the runs' values, in order."""
        out = []
        for k in range(lb + 1, n):
            v = g.var[k]
            if v is None or v in g.const:
                continue
            if all(vals[k] == f(env) for vals, env in runs):
                out.append(v)
        return out

    def we(name):
        if name in words:
            w_ = words[name]
            return f'{w_[0]}.toNat' if len(w_) == 1 else f'({w_[0]}.toNat + 2 ^ 32 * {w_[1]}.toNat)'
        _, _, expr, _, deps = sp.vals[sp.by[name]]
        return '(' + re.sub(r'\{(\w+)\}', lambda m: we(m.group(1)), expr) + ')'

    def stmt_of(name):
        _, bits, expr, _, _ = sp.vals[sp.by[name]]
        rhs = re.sub(r'\{(\w+)\}', lambda m: we(m.group(1)), expr)
        w_ = words[name]
        lhs = f'{w_[0]}.toNat' if len(w_) == 1 else f'{w_[0]}.toNat + 2 ^ 32 * {w_[1]}.toNat'
        return f'{lhs} = {rhs}'

    forced = {nm: (g.final[r_],) for r_, nm in zip(OUT_REGS, R)}
    word_of = {words[x][0]: x for x in W}
    earlier = set(words[x][0] for x in W)
    wstmt = {}

    def bounds_for(deps, depth=4):
        """The statements of the held values under `deps`, which bound them."""
        out, seen = [], set()

        def go(d, k):
            if d in seen or d in consts or d in W or k == 0:
                return
            seen.add(d)
            if d in wstmt:
                out.append((f'w{d}', wstmt[d]))
            for dd in sp.vals[sp.by[d]][4]:
                go(dd, k - 1)
        for d in deps:
            go(d, depth)
        return out

    def hyps_for(name, deps, st, targets):
        """The facts a value's lemma needs, or None when its words' cone stops at
        a word that no operand's statement reaches."""
        used = set(gfe.WORD_RE.findall(st.split(' = ', 1)[1]))
        if set(targets) <= used:
            # the value is a part of an operand's words: the statement is arithmetic
            return []
        ks, stops = g.cone(targets, (earlier | used) - set(targets))
        hyps = [(f't{k}', g.stmt[k]) for k in ks]
        extra = sorted((s_ for s_ in stops if s_ not in used), key=lambda w_: int(w_[1:]))
        for e_ in extra:
            if any(re.search(rf'\b{e_}\b', t_) for h_, t_ in hyps if h_.startswith('w')):
                continue
            found = []

            def dfs(d, path):
                if found or d in consts or d in W:
                    return
                if d in wstmt:
                    path = path + [d]
                    if re.search(rf'\b{e_}\b', wstmt[d]):
                        found.append(path)
                        return
                for dd in sp.vals[sp.by[d]][4]:
                    dfs(dd, path)
            for d in deps:
                dfs(d, [])
            if not found:
                return None
            for d in found[0]:
                if (f'w{d}', wstmt[d]) not in hyps:
                    hyps.append((f'w{d}', wstmt[d]))
        # the statements of the other held words those statements name
        for _ in range(3):
            more = []
            for h_, t_ in hyps:
                if not h_.startswith('w'):
                    continue
                for w_ in gfe.WORD_RE.findall(t_):
                    V = word_of.get(w_)
                    if (V and V in wstmt and w_ not in used and w_ not in targets
                            and (f'w{V}', wstmt[V]) not in hyps and (f'w{V}', wstmt[V]) not in more):
                        more.append((f'w{V}', wstmt[V]))
            if not more:
                break
            hyps += more
        return hyps

    lemmas, body = [], []
    ivs = {}

    def ival(name):
        if name in ivs:
            return ivs[name]
        if name in W:
            r = Iv(0, M32)
        elif name in consts:
            r = iv_of(RL[int(name[1:])])
        else:
            I = {d: ival(d) for d in sp.vals[sp.by[name]][4]}
            r = iv_eval(sp.vals[sp.by[name]][2], I)
        ivs[name] = r
        return r

    blem = {}

    def bound(name):
        """A lemma bounding the value `name` holds in words, from its statement and
        its operands' bounds."""
        if name in blem:
            return blem[name]
        w_ = words[name]
        lhs = f'{w_[0]}.toNat' if len(w_) == 1 else f'{w_[0]}.toNat + 2 ^ 32 * {w_[1]}.toNat'
        stb = f'{lhs} ≤ {ival(name).hi}'
        hy = [(f'w{name}', wstmt[name])]
        for w2 in sorted(set(gfe.WORD_RE.findall(wstmt[name].split(' = ', 1)[1])), key=lambda x: int(x[1:])):
            V = word_of.get(w2)
            if V and V != name and V not in W and V in wstmt:
                bh = bound(V)
                if bh not in hy:
                    hy.append(bh)
        ws = set(gfe.WORD_RE.findall(stb))
        for _, t_ in hy:
            ws |= set(gfe.WORD_RE.findall(t_))
        lemmas.append('set_option maxHeartbeats 10000000 in\n' + gfe.lemma(f'evr_b_{name}', stb, ws, [], hy))
        body.append(f'  have b{name} : {stb} := evr_b_{name} ' + ' '.join(h for h, _ in hy))
        blem[name] = (f'b{name}', stb)
        return blem[name]

    for name, bits, expr, _, deps in sp.vals:
        if name in W or name in consts:
            continue
        lb = lower(name)
        if name in forced:
            options = [forced[name]]
        else:
            los = cands(lambda e, name=name: e[name] & M32, lb)
            if bits == 32:
                options = [(lo,) for lo in los]
            elif any(env[name] >> 32 for _, env in runs):
                his = cands(lambda e, name=name: e[name] >> 32, lb)
                options = [(lo, hi) for lo in los for hi in his]
            else:
                # the high word is always 0: a word the code computes for it, or, if
                # the code keeps only the low word, the low word alone
                his = cands(lambda e: 0, lb)
                options = [(lo, hi) for lo in los for hi in his][:80] + [(lo,) for lo in los]
        chosen = None
        for opt in options[:120]:
            words[name] = opt
            st = stmt_of(name)
            hy = hyps_for(name, deps, st, list(opt))
            if hy is not None and bits == 64 and len(opt) == 1:
                for w2 in sorted(set(gfe.WORD_RE.findall(st.split(' = ', 1)[1])), key=lambda w_: int(w_[1:])):
                    V = word_of.get(w2)
                    if V and V not in W and V in wstmt:
                        bh = bound(V)
                        if bh not in hy:
                            hy.append(bh)
            if hy is not None:
                chosen = (opt, st, hy)
                break
            del words[name]
        if chosen is None:
            if name in forced:
                raise Exception(f'{name}: no word set whose cone its operands reach')
            continue
        opt, st, hyps = chosen
        wset = set(gfe.WORD_RE.findall(st))
        for _, t_ in hyps:
            wset |= set(gfe.WORD_RE.findall(t_))
        lnm = f"evr_v_{name}"
        try:
            text, hyps = gsm.structured_lemma(lnm, st, hyps, wset)
        except gsm.NonLinear:
            text = gfe.lemma(lnm, st, wset, [], hyps)
        lemmas.append('set_option maxHeartbeats 10000000 in\n' + gsm.comm_products(text))
        body.append(f'  have w{name} : {st} := {lnm} ' + ' '.join(h for h, _ in hyps))
        wstmt[name] = st
        earlier |= set(opt)
        for w_ in opt:
            word_of.setdefault(w_, name)

    defs = []
    for name, bits, expr, _, deps in sp.vals:
        if name in W or name in consts:
            continue
        rhs = re.sub(r'\{(\w+)\}', lambda m: (f'w {m.group(1)[1:]}' if m.group(1) in W
                                               else (str(RL[int(m.group(1)[1:])]) if m.group(1) in consts
                                                     else f'{lname(m.group(1))} w')), expr)
        pw = 'w' if re.search(r'\bw\b', rhs) else '_w'
        defs.append(f'def {lname(name)} ({pw} : Nat → Nat) : Nat := {rhs}')

    names_body = []
    for i in range(8):
        w_ = words[W[i]][0]
        names_body.append(f'  have h{W[i]} : {w_}.toNat = evIn M F {i} := by')
        names_body.append(f'    rw [evIn, ite_eq_left (by decide), ← hv{w_[1:]}] <;> rfl')
    for name, bits, expr, _, deps in sp.vals:
        if name in W or name in consts or name not in words:
            continue
        w_ = words[name]
        lhs = f'{w_[0]}.toNat' if len(w_) == 1 else f'{w_[0]}.toNat + 2 ^ 32 * {w_[1]}.toNat'
        held = []

        def collect(d):
            if d in words:
                held.append(d)
            elif d not in consts:
                for dd in sp.vals[sp.by[d]][4]:
                    collect(dd)
        for d in deps:
            collect(d)
        held.sort(key=lambda d: -len(words[d]))
        rw = f'rw [w{name}' + ''.join(f', h{d}' for d in dict.fromkeys(held)) + ']'
        names_body.append(f'  have h{name} : {lhs} = {lname(name)} (evIn M F) := by')
        names_body.append(f'    {rw} <;> rfl')

    parts = []

    def part(pname, doc, items):
        parts.append(pname)
        p = ['import C3BootProofs.Proofs.EdvReduceFacts', '', f'/-! {doc} -/', '',
             'namespace C3.RV32', '', 'open C3.Image', '']
        for t in items:
            p += [t, '']
        p += ['end C3.RV32']
        open(os.path.join(ROOT, f'C3BootProofs/Proofs/{pname}.lean'), 'w').write('\n'.join(p) + '\n')

    gen = '`scripts/gen-ev-reduce.py` writes this file.'
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
        part(f'EdvReduceSeg{k}', f'# The inlined `Scalar::reduce` in `ed25519_verify`, {span}\n\n'
             f'Each theorem steps 40 instructions. {gen}', [g.seg_thms[j] for j in grp])
    for k, lo in enumerate(range(0, len(lemmas), LEMMAS_PER_FILE)):
        part(f'EdvReduceVal{k}',
             f'# The inlined `Scalar::reduce`\'s values, part {k}\n\n'
             f'Each lemma proves one value the code holds in words from its instructions\' facts. {gen}',
             lemmas[lo:lo + LEMMAS_PER_FILE])
    pdir = os.path.join(ROOT, 'C3BootProofs/Proofs')
    for f in os.listdir(pdir):
        if re.fullmatch(r'EdvReduce(Seg|Val)\d+\.lean', f) and f[:-5] not in parts:
            os.remove(os.path.join(pdir, f))

    o = [f'import C3BootProofs.Proofs.{p}' for p in parts] + ['',
         '/-! # The inlined `Scalar::reduce` in `ed25519_verify`, as compiled', '',
         '`scripts/gen-ev-reduce.py` writes this file from the decoded instructions:',
         'a definition for each value the Rust source computes, and `evr_body`, which',
         'chains the segment theorems (`EdvReduceSeg*`) and the value lemmas',
         '(`EdvReduceVal*`). -/', '',
         'namespace C3.RV32', '', 'open C3.Image', '']
    o += defs + ['']
    regs = ', '.join(f"reg n' {gfe.lreg(r_)}" for r_ in OUT_REGS)
    outs = ', '.join(f'{lname(nm)} (evIn M F)' for nm in R)
    keepst = ' ∧\n      '.join(f'memLoad32 M\' (F + 0x{s_:X}) = memLoad32 M (F + 0x{s_:X})' for s_ in KEEP_SLOTS)
    mask_k = next(k for k in range(n) if g.var[k] == g.final[18])
    o += ['set_option maxHeartbeats 40000000 in', 'set_option maxRecDepth 100000 in',
          '/-- **The inlined `Scalar::reduce`**, from 0x17C to the masks at 0xEE4: the',
          'nine registers it leaves hold the low words of `montgomery_reduce`\'s limbs of',
          '`mul_internal` of the limbs of the eight words at `F + 0x9F0` and `R`; it writes',
          'nothing outside the frame\'s first 0x128 bytes, keeps the words at `F + 0x10` and',
          '`F + 0xD0`, and saves `s5` at `F + 0xC`. -/',
          'theorem evr_body {M : Word → BitVec 8} {B F G21 : Word} {n : Machine}',
          '    (s : St M B n 0x17C (reg n)) (hc : CodeIn M B ed25519VerifyCode) (hsp : reg n sp = F)',
          f'    (hs4 : reg n (20 : Fin 32) = F + 0x90F) (hs5 : reg n (21 : Fin 32) = G21)',
          f'    (hF : F.toNat % 4 = 0) (sFC : Sep F 0x{FSZ:X} B ed25519VerifyCode.length) :',
          f'    ∃ n\' M\', Steps n n\' ∧ St M\' B n\' 0x{END:X} (reg n\') ∧ (∀ x, Sep F 0x{FSZ:X} x 1 → M\' x = M x) ∧',
          f'      {keepst} ∧',
          f'      memLoad32 M\' (F + 0x{OUT_SLOT:X}) = G21 ∧',
          f'      [{regs}].map BitVec.toNat =',
          f'        [{outs}] ∧',
          '      reg n\' sp = F ∧ reg n\' (19 : Fin 32) = F + 0x90F ∧ reg n\' (18 : Fin 32) = 0x1FFFFFFF ∧',
          '      reg n\' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n\' (4 : Fin 32) = reg n (4 : Fin 32) := by',
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
    outw = [f'{g.reg_facts[r_]}' for r_ in OUT_REGS]
    o.append(f'  refine ⟨{g.n_final}, {g.mem_final}, {chain}, ug{last}, frg{last}, ' +
             ', '.join(g.slot_facts[('F', s_)] for s_ in KEEP_SLOTS) + f', {g.slot_facts[("F", OUT_SLOT)]}, ?_, ' +
             f'{g.reg_facts[2]}, {g.reg_facts[19]}, {g.reg_facts[18]}.trans c{mask_k}, '
             f'{g.reg_facts[3]}.trans hG3.symm, {g.reg_facts[4]}.trans hG4.symm⟩')
    o.append('  rw [' + ', '.join(outw) + ']')
    o.append('  simp only [List.map_cons, List.map_nil]')
    o.append('  rw [' + ', '.join(f'h{nm}' for nm in R) + ']')
    o += ['', 'end C3.RV32']
    open(os.path.join(ROOT, 'C3BootProofs/Proofs/EdvReduceBody.lean'), 'w').write('\n'.join(o) + '\n')
    print(f'{len(lemmas)} value lemmas, {len(g.seg_thms)} segments, '
          f'{sum(1 for v in sp.vals if v[0] not in words and v[0] not in consts)} values inlined')


if __name__ == '__main__':
    main()
