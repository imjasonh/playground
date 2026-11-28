#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/FeToBytesBody.lean: the straight-line tail of
curve25519_dalek's FieldElement2625::to_bytes, from its first load of
reduce's limbs at 0x5C to the epilogue at 0x204.

It steps every instruction with a fresh name for its result and turns each
result into a natural-number fact. It runs the block and the Rust source side
by side on random limbs to find which words hold the quotient's steps and the
carried limbs. Then it proves each of those values, and each of the 32 stored
bytes, with one `omega` lemma over the facts between it and the values it is
computed from. Run it from c3-boot-proofs/ after FeToBytesDecode.lean
changes.
"""
import os, random, re

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
M32 = (1 << 32) - 1
NAMES = {'x0': 0, 'ra': 1, 'sp': 2, 'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17}
LEAN = {v: k for k, v in NAMES.items()}
START, END = 0x5C, 0x204
W = [26, 25] * 5


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


class Ins:
    def __init__(self, off, lemma, text):
        self.off, self.lemma, self.text = off, lemma, text
        t = toks(text.lstrip('.'))
        self.kind = t[0]
        self.rd = self.rs1 = self.rs2 = 0
        self.imm = 0
        self.op = None
        if self.kind == 'load':
            self.rd, self.rs1, self.imm = reg(t[2]), reg(t[3]), int(t[4], 16)
        elif self.kind == 'store':
            self.op = t[1].lstrip('.')
            self.rs1, self.rs2, self.imm = reg(t[2]), reg(t[3]), int(t[4], 16)
        elif self.kind == 'alu':
            self.op = t[1].lstrip('.')
            self.rd, self.rs1, self.rs2 = reg(t[2]), reg(t[3]), reg(t[4])
        elif self.kind == 'aluImm':
            self.op = t[1].lstrip('.')
            self.rd, self.rs1, self.imm = reg(t[2]), reg(t[3]), int(t[4], 16)
        else:
            raise Exception(text)


def decode():
    src = open(os.path.join(ROOT, 'C3BootProofs/Proofs/FeToBytesDecode.lean')).read()
    ins = []
    for m in re.finditer(r'theorem (tb_at_\w+) : fetchRel feToBytesCode (0x[0-9A-Fa-f]+) = some \((.*), \d\) := by decide',
                         src):
        off = int(m.group(2), 16)
        if START <= off < END:
            ins.append(Ins(off, m.group(1), m.group(3)))
    ins.sort(key=lambda i: i.off)
    return ins


def alu(op, a, b):
    return {'add': (a + b) & M32, 'or': a | b, 'mul': (a * b) & M32, 'sll': (a << (b & 31)) & M32,
            'srl': a >> (b & 31)}[op]


def spec_vals(h):
    """The Rust source's intermediate values: Q1..Q10 and C0..C9."""
    out = {}
    q = ((h[0] + 19) & M32) >> 26
    out['Q1'] = q
    for i in range(1, 10):
        q = ((h[i] + q) & M32) >> W[i]
        out[f'Q{i + 1}'] = q
    c = (h[0] + ((19 * q) & M32)) & M32
    out['C0'] = c
    for i in range(1, 10):
        c = (h[i] + (out[f'C{i - 1}'] >> W[i - 1])) & M32
        out[f'C{i}'] = c
    return out


def main():
    block = decode()
    # symbolic names and a dry run
    cur = {2: 'F', 8: 'out'}
    src, var, stores, words = [], [], [], {}
    const = {}
    for k, i in enumerate(block):
        v = f'v{k}'
        if i.kind == 'load':
            if cur.get(i.rs1) != 'F':
                raise Exception(i.text)
            words[(i.imm - 8) // 4] = v
            src.append([])
            var.append(v)
            cur[i.rd] = v
        elif i.kind == 'store':
            if cur.get(i.rs1) != 'out' or i.op != 'sb':
                raise Exception(i.text)
            stores.append((k, i.imm, cur[i.rs2]))
            src.append([cur[i.rs2]])
            var.append(None)
        elif i.kind == 'alu':
            src.append([cur.get(i.rs1), cur.get(i.rs2)])
            var.append(v)
            cur[i.rd] = v
        else:
            if i.op == 'add' and i.rs1 == 0:
                const[v] = i.imm & M32
                src.append([])
            else:
                src.append([cur.get(i.rs1)])
            var.append(v)
            cur[i.rd] = v
    final = dict(cur)

    def simulate(h):
        vals = {}
        R = {}
        for k, i in enumerate(block):
            if i.kind == 'load':
                vals[var[k]] = h[(i.imm - 8) // 4]
            elif i.kind == 'store':
                continue
            elif i.kind == 'alu':
                vals[var[k]] = alu(i.op, vals[src[k][0]], vals[src[k][1]])
            elif var[k] in const:
                vals[var[k]] = const[var[k]]
            else:
                vals[var[k]] = alu(i.op, vals[src[k][0]], i.imm)
        return vals

    runs = []
    rnd = random.Random(25519)
    for t in range(400):
        if t % 2:
            # limbs at the edges of their widths, so the carries differ from the quotient's steps
            h = [rnd.choice([(1 << W[j]) - rnd.randint(1, 40), (1 << W[j]) + rnd.randint(0, 40), rnd.getrandbits(W[j])])
                 for j in range(10)]
        else:
            h = [rnd.getrandbits(rnd.choice([25, 26, 27, 32])) for _ in range(10)]
        runs.append((simulate(h), spec_vals(h)))
    # which word holds each spec value: the quotient's steps before the `mul`, the carries after it
    kmul = next(k for k, i in enumerate(block) if i.op == 'mul')
    hold = {}
    for name in ['Q%d' % i for i in range(1, 11)] + ['C%d' % i for i in range(10)]:
        rng = range(kmul) if name[0] == 'Q' else range(kmul + 1, len(block))
        for k in rng:
            v = var[k]
            if v is None or v in const:
                continue
            if all(r[0][v] == r[1][name] for r in runs):
                hold[name] = v
                break
        else:
            raise Exception(f'no word holds {name}')

    # Lean facts per instruction
    stmt, pf = {}, {}
    for k, i in enumerate(block):
        v = var[k]
        if v is None or i.kind == 'load':
            continue
        if v in const:
            continue
        a = src[k][0]
        if i.kind == 'aluImm':
            sh = i.imm & 31
            if i.op == 'sll':
                stmt[k], pf[k] = f'{v}.toNat = {a}.toNat * 2 ^ {sh} % 2 ^ 32', f'tn_sll hv{k}'
            elif i.op == 'srl':
                stmt[k], pf[k] = f'{v}.toNat = {a}.toNat / 2 ^ {sh}', f'tn_srl hv{k}'
            elif i.op == 'add':
                stmt[k], pf[k] = f'{v}.toNat = ({a}.toNat + {i.imm}) % 2 ^ 32', f'tn_add hv{k}'
            else:
                raise Exception(i.text)
        else:
            b = src[k][1]
            if i.op == 'add':
                stmt[k], pf[k] = f'{v}.toNat = ({a}.toNat + {b}.toNat) % 2 ^ 32', f'tn_add hv{k}'
            elif i.op == 'mul':
                if b in const:
                    stmt[k] = f'{v}.toNat = {a}.toNat * {const[b]} % 2 ^ 32'
                    pf[k] = f'by rw [tn_mul hv{k}, c{b[1:]}]; rfl'
                elif a in const:
                    stmt[k] = f'{v}.toNat = {b}.toNat * {const[a]} % 2 ^ 32'
                    pf[k] = f'by rw [tn_mul hv{k}, c{a[1:]}, Nat.mul_comm]; rfl'
                else:
                    raise Exception(i.text)
            elif i.op == 'or':
                ka, kb = var.index(a), var.index(b)
                ia, ib = block[ka], block[kb]
                if ia.op == 'srl' and ib.op == 'sll':
                    x, y, ix, iy, lem = a, b, ia, ib, 'tn_orS'
                elif ia.op == 'sll' and ib.op == 'srl':
                    x, y, ix, iy, lem = b, a, ib, ia, "tn_orS'"
                else:
                    raise Exception(i.text)
                sh = ix.imm & 31
                if (iy.imm & 31) != 32 - sh:
                    raise Exception(i.text)
                stmt[k] = f'{v}.toNat = {x}.toNat + {y}.toNat'
                pf[k] = f'{lem} {sh} (by decide) hv{k} t{var.index(x)} t{var.index(y)}'
            else:
                raise Exception(i.text)

    def cone(target, known):
        ks, seen, stops = set(), set(), set()

        def walk(v, top):
            if v in seen:
                return
            seen.add(v)
            if v in const or v not in var:
                return
            if v in known and not top:
                stops.add(v)
                return
            k = var.index(v)
            if k in stmt:
                ks.add(k)
            for o in src[k]:
                walk(o, False)
        walk(target, True)
        return sorted(ks), stops

    lemmas, uses = [], []

    def nat_lemma(name, concl, target, known):
        ks, stops = cone(target, known)
        vs = sorted({target} | stops | {var[k] for k in ks} |
                    {o for k in ks for o in src[k] if o and o not in const}, key=lambda s: int(s[1:]))
        # every word named in the conclusion
        for w in re.findall(r'\bv\d+\b', concl):
            if w not in vs:
                vs.append(w)
        vs = sorted(set(vs), key=lambda s: int(s[1:]))
        ren = lambda s: re.sub(r'\b(v\d+)\.toNat\b', lambda m: 'x' + m.group(1)[1:], s)
        hyps = [f'(_h{k} : {ren(stmt[k])})' for k in ks]
        bnds = [f'(_b{w[1:]} : x{w[1:]} < 2 ^ 32)' for w in vs]
        params = ' '.join('x' + w[1:] for w in vs)
        lemmas.append(f'theorem {name} {{{params} : Nat}} {" ".join(bnds)}\n    {" ".join(hyps)} :\n'
                      f'    {ren(concl)} := by omega')
        args = ' '.join(f'{w}.isLt' for w in vs) + ' ' + ' '.join(f't{k}' for k in ks)
        return f'{name} {args}'

    known = set(words.values()) | set(hold.values())
    # the spec's values
    hspec = []
    q_expr = {1: f'({words[0]}.toNat + 19) % 2 ^ 32 / 2 ^ 26 = {hold["Q1"]}.toNat'}
    for i in range(1, 10):
        q_expr[i + 1] = f'({words[i]}.toNat + {hold["Q%d" % i]}.toNat) % 2 ^ 32 / 2 ^ {W[i]} = {hold["Q%d" % (i + 1)]}.toNat'
    c_expr = {0: f'({words[0]}.toNat + 19 * {hold["Q10"]}.toNat % 2 ^ 32) % 2 ^ 32 = {hold["C0"]}.toNat'}
    for i in range(1, 10):
        c_expr[i] = f'({words[i]}.toNat + {hold["C%d" % (i - 1)]}.toNat / 2 ^ {W[i - 1]}) % 2 ^ 32 = {hold["C%d" % i]}.toNat'
    for i in range(1, 11):
        kn = known - {hold['Q%d' % i]}
        hspec.append(('hQ%d' % i, nat_lemma(f'tb_q{i}', q_expr[i], hold['Q%d' % i], kn)))
    for i in range(10):
        kn = known - {hold['C%d' % i]}
        hspec.append(('hC%d' % i, nat_lemma(f'tb_c{i}', c_expr[i], hold['C%d' % i], kn)))
    # the bytes
    specb = []
    for line in open(os.path.join(ROOT, 'C3BootProofs/Proofs/FeToBytesSpec.lean')).read().split(
            '      [', 1)[1].split('] := by', 1)[0].split(',\n'):
        specb.append(line.strip())
    if len(specb) != 32:
        raise Exception(len(specb))
    by_off = {o: (k, val) for k, o, val in stores}
    blems = []
    for o in range(32):
        k, val = by_off[o]
        concl = f'{val}.toNat % 2 ^ 8 = ' + re.sub(r'\bC(\d)\b', lambda m: hold['C' + m.group(1)] + '.toNat', specb[o])
        blems.append(nat_lemma(f'tb_b{o}', concl, val, known))

    o = []
    o.append('import C3BootProofs.Proofs.FeToBytesDecode')
    o.append('')
    o.append('/-! # The straight-line tail of `FieldElement2625::to_bytes`, as compiled')
    o.append('')
    o.append('`scripts/gen-tobytes.py` writes this file from the decoded instructions. -/')
    o.append('')
    o.append('namespace C3.RV32')
    o.append('')
    o.append('open C3.Image')
    o.append('')
    for lm in lemmas:
        o.append(lm)
        o.append('')
    rds = sorted({i.rd for i in block if i.kind != 'store' and i.rd})
    o.append("/-- The registers `to_bytes`'s tail leaves alone. -/")
    o.append(f'def tbBodyKeep (q : Fin 32) : Bool := q.val ∉ [{", ".join(str(r) for r in rds)}]')
    o.append('')
    o.append('theorem tbkeep_ne {q r : Fin 32} (hq : tbBodyKeep q = true) (hr : tbBodyKeep r = false) : q ≠ r := by')
    o.append('  rintro rfl; rw [hq] at hr; exact Bool.noConfusion hr')
    o.append('')
    o.append('set_option linter.unusedSimpArgs false in')
    o.append('set_option maxHeartbeats 40000000 in')
    o.append('set_option maxRecDepth 100000 in')
    o.append("/-- **The tail of `to_bytes`**, from the first load of `reduce`'s limbs at")
    o.append('0x5C to the epilogue at 0x204: the 32 bytes it stores at `out` are')
    o.append('`feToBytesSpec` of the ten words at `F + 8`. -/')
    o.append('theorem tb_body {M : Word → BitVec 8} {B F out : Word} {n : Machine} (s : St M B n 0x5C (reg n))')
    o.append('    (hc : CodeIn M B feToBytesCode) (hsp : reg n sp = F) (hs0 : reg n 8 = out) (hF : F.toNat % 4 = 0)')
    o.append('    (sOC : Sep out 32 B feToBytesCode.length) :')
    o.append("    ∃ n' M', Steps n n' ∧ St M' B n' 0x204 (reg n') ∧ CodeIn M' B feToBytesCode ∧")
    o.append("      (∀ x, Sep out 32 x 1 → M' x = M x) ∧")
    ws = ' '.join(f'(memLoad32 M (F + 0x{8 + 4 * j:X})).toNat' for j in range(10))
    o.append(f"      memBytes M' out 32 = feToBytesSpec {ws} ∧")
    o.append("      ∀ q, tbBodyKeep q = true → reg n' q = reg n q := by")
    o.append('  have hz0 : reg n 0 = 0 := s.zero')
    hyps = 'hz0, hsp, hs0'
    cur = {2: 'F', 8: 'out'}
    prev, mem, hc = 's', 'M', 'hc'
    seg = 10 ** 6
    for k, i in enumerate(block):
        nxt = block[k + 1].off if k + 1 < len(block) else END
        v, u = f'v{k}', f'u{k}'
        simp = f'simp +decide only [upd, ↓reduceIte, {hyps}]'
        if i.kind == 'load':
            o.append(f"  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.lwG {hc} {i.lemma} (off' := 0x{nxt:X}) (by decide)")
            o.append(f'    (by {simp}; exact aligned_add hF (k := 0x{i.imm:X}) (by decide))')
            o.append(f'  {simp} at hv{k}')
            cur[i.rd] = v
        elif i.kind == 'store':
            val = cur[i.rs2]
            o.append(f"  obtain ⟨n{k}, d{k}, {u}⟩ := {prev}.sbG {hc} {i.lemma} (off' := 0x{nxt:X}) (by decide)")
            o.append(f'    (a := out + 0x{i.imm:X}) (v := {val}) (by {simp}) (by {simp})')
            o.append(f"  obtain ⟨M{k}, hM{k}⟩ : ∃ M', memStore8 {mem} (out + 0x{i.imm:X}) ({val}.extractLsb' 0 8) = M' :=")
            o.append('    ⟨_, rfl⟩')
            o.append(f'  rw [hM{k}] at {u}')
            o.append(f'  have hc{k} : CodeIn M{k} B feToBytesCode := by')
            o.append(f'    rw [← hM{k}]; exact {hc}.store8 (sOC.sub (c := {i.imm}) (l := 1) (by decide))')
            mem, hc = f'M{k}', f'hc{k}'
        elif i.kind == 'alu':
            o.append(f"  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluG {hc} {i.lemma} (off' := 0x{nxt:X}) (by decide)")
            o.append(f'  {simp} at hv{k}')
            cur[i.rd] = v
        else:
            o.append(f"  obtain ⟨n{k}, {v}, d{k}, hv{k}, {u}⟩ := {prev}.aluImmG {hc} {i.lemma} (off' := 0x{nxt:X}) (by decide)")
            o.append(f'  {simp} at hv{k}')
            if v in const:
                o.append(f'  have c{k} : {v} = 0x{const[v]:X} := by rw [← hv{k}]; rfl')
            cur[i.rd] = v
        prev = u
        if (k + 1) % seg == 0 and k + 1 < len(block):
            qs = []
            for r in sorted(cur):
                o.append(f'  have q{k}_{r} : reg n{k} {lreg(r)} = {cur[r]} := by rw [{u}.regs]; {simp}')
                qs.append(f'q{k}_{r}')
            o.append(f'  have z{k} : reg n{k} 0 = 0 := {u}.self.zero')
            hyps = ', '.join([f'z{k}'] + qs)
            prev = f'{u}.self'
    last = len(block) - 1
    for k in sorted(stmt):
        o.append(f'  have t{k} : {stmt[k]} := {pf[k]}')
    for j in range(10):
        kw = var.index(words[j])
        o.append(f'  have eW{j} : (memLoad32 M (F + 0x{8 + 4 * j:X})).toNat = {words[j]}.toNat := by rw [hv{kw}]')
    for name, term in hspec:
        o.append(f'  have {name} := {term}')
    # the memory outside `out`
    o.append(f'  have frO : ∀ x, Sep out 32 x 1 → {mem} x = M x := fun x hx => by')
    rw = []
    for k, off, val in reversed(stores):
        rw.append(f'← hM{k}, memStore8_ne fun e => hx {off} (by decide) 0 (by decide) (by rw [e]; bv_omega)')
    o.append('    rw [' + ',\n      '.join(rw) + ']')
    # each byte
    for off in range(32):
        k, val = by_off[off]
        later = [(k2, o2) for k2, o2, _ in stores if k2 > k]
        rws = []
        for k2, o2 in reversed(later):
            rws.append(f'← hM{k2}, memStore8_ne (show out + 0x{off:X} ≠ out + 0x{o2:X} from\n'
                       f'        tb_off_ne (by decide) (by decide) (by decide))')
        rws.append(f'← hM{k}, memStore8_same')
        o.append(f"  have m{off} : {mem} (out + 0x{off:X}) = {val}.extractLsb' 0 8 := by")
        o.append('    rw [' + ',\n      '.join(rws) + ']')
    chain = ''.join(f'(.cons d{k} ' for k in range(last)) + f'(.single d{last})' + ')' * last
    o.append(f'  refine ⟨n{last}, {mem}, {chain}, {prev}.self, {hc}, frO, ?_, ?_⟩')
    o.append('  · rw [' + ', '.join(f'eW{j}' for j in range(10)) + ',')
    o.append('      feToBytesSpec_of ' + ' '.join(n for n, _ in hspec) + ']')
    o.append("    show [" + ', '.join(f'({mem} (out + 0x{i:X})).toNat' for i in range(32)) + '] = _')
    o.append('    rw [' + ', '.join(f'm{i}' for i in range(32)) + ']')
    o.append('    simp only [tb_byte]')
    o.append('    rw [' + ',\n      '.join(blems) + ']')
    o.append('  · intro q hq')
    o.append(f'    rw [{prev}.regs]')
    ne = ', '.join(f'tbkeep_ne hq (r := {lreg(r)}) rfl' for r in rds)
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
    open(os.path.join(ROOT, 'C3BootProofs/Proofs/FeToBytesBody.lean'), 'w').write('\n'.join(o) + '\n')


if __name__ == '__main__':
    main()
