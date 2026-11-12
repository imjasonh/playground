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
        elif self.kind == 'jalr':
            self.op, self.rd = 'jalr', None
        else:
            raise Exception(text)


def alu(op, a, b):
    return {'add': (a + b) & M32, 'sltu': int(a < b), 'or': a | b, 'and': a & b, 'mul': (a * b) & M32,
            'mulhu': (a * b) >> 32, 'sll': (a << (b & 31)) & M32, 'srl': a >> (b & 31)}[op]


def simulate(block, regs0, mem):
    """Runs the block; returns, per instruction, the value it writes."""
    R = list(regs0)
    vals = []
    for i in block:
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

    def facts(self):
        """One natural-number fact per instruction result: `self.stmt[k]` and
        the term or tactic that proves it."""
        self.const = {}
        self.stmt = {}
        for k, i in enumerate(self.block):
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


def lemma(name, stmt, words, nats, hyps, extra=''):
    """A standalone step lemma, so each `omega` sees only its own facts."""
    ws = ' '.join(sorted(words, key=lambda w: int(w[1:])))
    ns = ' '.join(nats)
    hs = '\n    '.join(f'({h} : {t})' for h, t in hyps)
    lts = '; '.join(f'have := {w}.isLt' for w in sorted(words, key=lambda w: int(w[1:])))
    out = [f'theorem {name} {{{ws} : Word}}' + (f' {{{ns} : Nat}}' if ns else '')]
    out.append(f'    {hs} :')
    out.append(f'    {stmt} := by')
    out.append(f'  {lts}{extra}')
    out.append('  omega')
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


OUT_REGS = ['a2', 'a3', 'a4', '(8 : Fin 32)', 'a5', '(5 : Fin 32)', 'a1', 'a6', '(6 : Fin 32)', '(9 : Fin 32)']
OUT_NUMS = [12, 13, 14, 8, 15, 5, 11, 16, 6, 9]


def main():
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
