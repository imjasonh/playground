#!/usr/bin/env python3
"""Writes C3BootProofs/Models/P256BarrettChain.lean, the carry-chain
identities of P-256's compiled `barrett_reduce`.

It parses the `psv*` definitions in P256ScalarBody.lean and sorts them into
five stages: the product `q1 * mu`, the product `q3 * n` modulo `2^288`, the
subtraction `r1 - r2`, the subtraction of `n`, and the conditional addition
of `n`. Each definition gives one equation: a sum split into its low word
and carry, or a borrowing subtraction. For each stage, the script finds the
power of `2^32` to scale each equation by so that every carry and borrow
cancels, checks the remaining identity on random values, and writes one
theorem that `ring_eq` proves from the scaled equations. Run it from
c3-boot-proofs/ after P256ScalarBody.lean changes.
"""
import os, random, re
from fractions import Fraction

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
random.seed(710)

B = 1 << 32
MASK = B - 1
N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
MU = B ** 16 // N

src = open(os.path.join(ROOT, 'C3BootProofs/Proofs/P256ScalarBody.lean')).read()
defs, order = {}, []
for m in re.finditer(r'^def (psv\w+) \(a : Nat → Nat\) : Nat := (.*)$', src, re.M):
    defs[m.group(1)] = m.group(2)
    order.append(m.group(1))


def tokenize(s):
    return re.findall(r'\d+|psv\w+|\ba\b|[()+\-*/%^]', s)


PREC = {'+': 65, '-': 65, '*': 70, '/': 70, '%': 70, '^': 75}


def parse(s):
    ts = tokenize(s)
    pos = [0]

    def peek():
        return ts[pos[0]] if pos[0] < len(ts) else None

    def take():
        pos[0] += 1
        return ts[pos[0] - 1]

    def primary():
        t = take()
        if t == '(':
            e = expr(0)
            assert take() == ')'
            return e
        if t.isdigit():
            return ('num', int(t))
        if t == 'a':
            return ('a', int(take()))
        assert t.startswith('psv') and take() == 'a', t
        return ('ref', t)

    def expr(minp):
        lhs = primary()
        while peek() in PREC and PREC[peek()] >= minp:
            op = take()
            p = PREC[op]
            rhs = expr(p if op == '^' else p + 1)
            lhs = ('bin', op, lhs, rhs)
        return lhs

    e = expr(0)
    assert pos[0] == len(ts), s
    return e


def const(e):
    if e[0] == 'num':
        return e[1]
    if e[0] == 'bin' and e[1] == '^':
        return const(e[2]) ** const(e[3])
    return None


def add(*fs):
    out = {}
    for f in fs:
        for k, v in f.items():
            out[k] = out.get(k, 0) + v
            if out[k] == 0:
                del out[k]
    return out


def scale(f, c):
    return {k: v * c for k, v in f.items()} if c else {}


def lin(e):
    """The linear form of e over atoms: limbs, words, and borrows."""
    c = const(e)
    if c is not None:
        return {'1': c} if c else {}
    if e[0] == 'a':
        return {('a', e[1]): 1}
    if e[0] == 'ref':
        return {('ref', e[1]): 1}
    op, l, r = e[1], e[2], e[3]
    if op == '+':
        return add(lin(l), lin(r))
    if op == '*':
        if const(r) is not None:
            return scale(lin(l), const(r))
        return scale(lin(r), const(l))
    if op == '/' and l[0] == 'ref' and const(r) == MASK:
        return {('div', l[1]): 1}
    raise ValueError(e)


def atom_txt(k):
    if k[0] == 'a':
        return 'a %d' % k[1]
    if k[0] == 'ref':
        return '%s a' % k[1]
    return '(%s a / 4294967295)' % k[1]


def lin_txt(f):
    parts = []
    for k, v in sorted(f.items(), key=lambda kv: str(kv[0])):
        if k == '1':
            parts.append(str(v))
        elif v == 1:
            parts.append(atom_txt(k))
        else:
            parts.append('%d * %s' % (v, atom_txt(k)))
    return ' + '.join(parts) if parts else '0'


def render(e):
    if e[0] == 'num':
        return str(e[1])
    if e[0] == 'a':
        return 'a %d' % e[1]
    if e[0] == 'ref':
        return '%s a' % e[1]
    s = '%s %s %s' % (render(e[2]), e[1], render(e[3]))
    return '(%s)' % s


# Evaluation, for the numeric checks.
def ev(e, a, env):
    if e[0] == 'num':
        return e[1]
    if e[0] == 'a':
        return a[e[1]] if e[1] < 16 else 0
    if e[0] == 'ref':
        return value(e[1], a, env)
    op, l, r = e[1], ev(e[2], a, env), ev(e[3], a, env)
    return {'+': lambda: l + r, '-': lambda: max(l - r, 0), '*': lambda: l * r,
            '/': lambda: l // r, '%': lambda: l % r, '^': lambda: l ** r}[op]()


asts = {n: parse(b) for n, b in defs.items()}


def value(n, a, env):
    if n not in env:
        env[n] = ev(asts[n], a, env)
    return env[n]


def atom_val(k, a, env):
    if k == '1':
        return 1
    if k[0] == 'a':
        return a[k[1]]
    if k[0] == 'ref':
        return value(k[1], a, env)
    return value(k[1], a, env) // MASK


# Equations: lhs = rhs, each a linear form, with Lean text and a proof.
class Eq:
    def __init__(self, lhs, rhs, ltxt, rtxt, proof):
        self.lhs, self.rhs, self.ltxt, self.rtxt, self.proof = lhs, rhs, ltxt, rtxt, proof


def carry_eq(x):
    assert defs[x + 'l'] == '%s a %% 2 ^ 32' % x and defs[x + 'h'] == '%s a / 2 ^ 32' % x
    rtxt = '%sl a + 2 ^ 32 * %sh a' % (x, x)
    return Eq(lin(asts[x]), {('ref', x + 'l'): 1, ('ref', x + 'h'): B},
              defs[x], rtxt, '(Nat.mod_add_div (%s a) (2 ^ 32)).symm' % x)


def borrow_parts(d):
    e = asts[d]
    assert e[0] == 'bin' and e[1] == '%' and const(e[3]) == B
    e = e[2]
    c = None
    if e[2][0] == 'bin' and e[2][1] == '-':
        c, e = e[3], e[2]
    assert e[1] == '-'
    y, e = e[3], e[2]
    assert e[1] == '+' and const(e[3]) == B
    return e[2], y, c


def borrow_eq(p, i, xbound):
    """Step i of a borrowing subtraction with digits psv{p}D and masks psv{p}M."""
    d, m = 'psv%sD%d' % (p, i), 'psv%sM%d' % (p, i)
    x, y, c = borrow_parts(d)
    lhs = add(lin(x), {('div', m): B})
    rhs = add({('ref', d): 1}, lin(y), lin(c) if c else {})
    ltxt = '%s + 2 ^ 32 * (%s a / 4294967295)' % (render(x), m)
    rtxt = '%s a + %s' % (d, render(y)) + (' + %s' % render(c) if c else '')
    hy = 'lt32 _' if y[0] == 'ref' else 'by decide'
    if c:
        px, py, pc = borrow_parts('psv%sD%d' % (p, i - 1))
        le = ('bstep_le (%s) (%s) (%s)' % (render(px), render(py), render(pc)) if pc else
              'bstep0_le (%s) (%s)' % (render(px), render(py)))
        proof = 'bstep_eq (%s) (%s) (%s) %s (%s) (%s)' % (
            render(x), render(y), render(c), xbound(x), hy, le)
    else:
        proof = 'bstep0_eq (%s) (%s) %s (%s)' % (render(x), render(y), xbound(x), hy)
    return Eq(lhs, rhs, ltxt, rtxt, proof)


def xbound(x):
    return '(ha %d)' % x[1] if x[0] == 'a' else '(lt32 _)'


def stage_coeffs(eqs, seed):
    """Scales that cancel every atom an equation of the stage produces."""
    produced = {}
    for i, q in enumerate(eqs):
        for k in q.rhs:
            if k != '1':
                produced.setdefault(k, []).append(i)
    consumed = {}
    for i, q in enumerate(eqs):
        for k in q.lhs:
            if k in produced:
                consumed.setdefault(k, []).append(i)
    cons = []
    for k in consumed:
        terms = [(i, Fraction(eqs[i].lhs.get(k, 0)) - eqs[i].rhs.get(k, 0)) for i in
                 set(produced[k]) | set(consumed[k])]
        cons.append([(i, v) for i, v in terms if v])
    c = {seed: Fraction(1)}
    changed = True
    while changed:
        changed = False
        for t in cons:
            unk = [(i, v) for i, v in t if i not in c]
            if len(unk) == 1:
                i, v = unk[0]
                c[i] = -sum(c[j] * w for j, w in t if j in c) / v
                changed = True
    assert len(c) == len(eqs), (len(c), len(eqs))
    for t in cons:
        assert sum(c[i] * v for i, v in t) == 0
    for v in c.values():
        assert v > 0 and v.denominator == 1
    return [int(c[i]) for i in range(len(eqs))]


def leftover(eqs, cs):
    """Σ c (lhs - rhs) over the atoms that don't cancel."""
    return add(*[add(scale(q.lhs, c), scale(q.rhs, -c)) for q, c in zip(eqs, cs)])


def names_between(lo, hi):
    i, j = order.index(lo), order.index(hi)
    return [n for n in order[i:j + 1] if re.fullmatch(r'psv[PS]\d+', n)]


out = []
emit = out.append


def check(f, g, label):
    """f = g as forms, at random values of the definitions."""
    for _ in range(200):
        a = [random.randrange(B) if random.random() < 0.8 else MASK for _ in range(16)]
        env = {}
        fv = sum(v * atom_val(k, a, env) for k, v in f.items())
        gv = sum(v * atom_val(k, a, env) for k, v in g.items())
        assert fv == gv, label


def emit_stage(name, doc, args, eqs, cs, P, Q, ptxt, qtxt, unfold):
    D = leftover(eqs, cs)
    assert add(P, scale(Q, -1), scale(D, -1)) == {}, name
    check(P, Q, name)
    S = ''.join('%d * (%s) + (\n      ' % (c, q.ltxt) for q, c in zip(eqs, cs)) + '0' + ')' * len(eqs)
    T = ''.join('%d * (%s) + (\n      ' % (c, q.rtxt) for q, c in zip(eqs, cs)) + '0' + ')' * len(eqs)
    chain = ''.join('\n    (lcs (c := %d) (show %s = %s from %s)' % (c, q.ltxt, q.rtxt, q.proof)
                    for q, c in zip(eqs, cs)) + ' rfl' + ')' * len(eqs)
    emit('set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 100000 in')
    emit('/-- %s -/' % doc)
    emit('theorem %s (a : Nat → Nat)%s :\n    %s = %s := by' % (name, args, ptxt, qtxt))
    emit('  unfold %s' % ' '.join(unfold))
    emit('  refine lcN (S := %s)\n    (T := %s) ?_ (by ring_eq)' % (S, T))
    emit('  exact' + chain)
    emit('')


def sum_txt(atoms, base=0):
    return ' + '.join((atom_txt(k) if i + base == 0 else '%d * %s' % (B ** (i + base), atom_txt(k)))
                      for i, k in enumerate(atoms))


def emit_def(name, doc, f):
    emit('/-- %s -/' % doc)
    emit('def %s (a : Nat → Nat) : Nat :=\n  %s\n' % (name, f))


def emit_lt(name, atoms, bound, proofs):
    emit('theorem %s_lt (a : Nat → Nat)%s : %s a < %d := by' % (
        name, ' (ha : ∀ i, a i < 2 ^ 32)' if any(k[0] == 'a' for k in atoms) else '', name, bound))
    emit('  unfold %s' % name)
    for i, k in enumerate(atoms):
        pf = '(ha %d)' % k[1] if k[0] == 'a' else 'lt32 _'
        emit('  have h%d : %s < 2 ^ 32 := %s' % (i, atom_txt(k), pf))
    emit('  omega\n')


def limb_sum(atoms, base=0):
    return {k: B ** (i + base) for i, k in enumerate(atoms)}


# Stage A: q1 * mu, every partial product, with its carries.
eqsA = [carry_eq(x) for x in names_between('psvP1', 'psvS79')]
csA = stage_coeffs(eqsA, 0)
q3 = [('ref', 'psvP%dl' % i) for i in range(72, 78)] + [('ref', 'psvS78l'), ('ref', 'psvS79l'),
                                                       ('ref', 'psvS79h')]
q1 = [('a', i) for i in range(7, 16)]
DA = leftover(eqsA, csA)
lowA = {k: v for k, v in DA.items() if v < 0 and k not in q3}
assert all(-v < B ** 9 for v in lowA.values())
PA = scale(limb_sum(q1), MU)
QA = add(scale(lowA, -1), limb_sum(q3, 9))

# Stage B: q3 * n modulo 2^288.
eqsB = [carry_eq(x) for x in names_between('psvP80', 'psvP122')]
csB = stage_coeffs(eqsB, 0)
DB = leftover(eqsB, csB)
r2 = [('ref', n) for n in ['psvP80l', 'psvP87l', 'psvP95l', 'psvP102l', 'psvP108l', 'psvP113l',
                           'psvP117l', 'psvP120l', 'psvP122l']]
for i, k in enumerate(r2):
    assert DB[k] == -B ** i
PB = scale(limb_sum(q3), N)
hiB = add(PB, scale(limb_sum(r2), -1), scale(DB, -1))
assert all(v > 0 and v % B ** 9 == 0 for v in hiB.values())
hiB = {k: v // B ** 9 for k, v in hiB.items()}
QB = add(limb_sum(r2), scale(hiB, B ** 9))

# Stage U: r1 - r2 with borrows.
eqsU = [borrow_eq('U', i, xbound) for i in range(9)]
csU = stage_coeffs(eqsU, 0)
r1 = [('a', i) for i in range(9)]
ud = [('ref', 'psvUD%d' % i) for i in range(9)]
cU8 = ('div', 'psvUM8')
PU = add(limb_sum(r1), {cU8: B ** 9})
QU = add(limb_sum(ud), limb_sum(r2))

# Stage V: u - n with borrows.
eqsV = [borrow_eq('V', i, xbound) for i in range(9)]
csV = stage_coeffs(eqsV, 0)
vd = [('ref', 'psvVD%d' % i) for i in range(9)]
cV8 = ('div', 'psvVM8')
PV = add(limb_sum(ud), {cV8: B ** 9})
QV = add(limb_sum(vd), {'1': N})

# Stage S: v + n when the subtraction borrowed, in eight words.
eqsS = [carry_eq(x) for x in names_between('psvS123', 'psvS130')]
for j in range(4):
    k = 'psvK%d' % j
    assert defs[k] == '%d * (psvVM8 a / 4294967295)' % ((N >> (32 * j)) & MASK)
    eqsS.append(Eq({cV8: (N >> (32 * j)) & MASK}, {('ref', k): 1}, defs[k], '%s a' % k, 'rfl'))
eqsS.append(Eq({cV8: MASK}, {('ref', 'psvVM8'): 1}, '4294967295 * (psvVM8 a / 4294967295)',
               'psvVM8 a', '(mask_eq _).symm'))
csS = stage_coeffs(eqsS, 0)
outs = [('ref', 'psvS%dl' % j) for j in range(123, 131)]
PS = add(limb_sum(vd[:8]), {cV8: N})
QS = add(limb_sum(outs), {('ref', 'psvS130h'): B ** 8})

emit('''import C3BootProofs.Proofs.P256ScalarBody
import C3BootProofs.Ring.Tactic

/-!
# The carry chains of P-256's `barrett_reduce`

`scripts/gen-p256-barrett.py` writes this file from the definitions in
`P256ScalarBody`. Each theorem is one stage of the compiled reduction, as an
identity over its input limbs `a`, the words it stores, and its borrows:
`barrettA` is `q1 * mu`, `barrettB` is `q3 * n` modulo `2 ^ 288`, `barrettU`
and `barrettV` are the two borrowing subtractions, and `barrettS` is the
conditional addition of `n`. `ring_eq` proves each from the stage's carry
equations, each scaled by the power of `2 ^ 32` at which it acts.
-/

namespace C3.Models

open C3.RV32

theorem lcN {P Q S T : Nat} (h : S = T) (k : P + T = Q + S) : P = Q := by
  rw [h] at k; exact Nat.add_right_cancel k

theorem lcs {c l r s t : Nat} (h : l = r) (hs : s = t) : c * l + s = c * r + t := by
  rw [h, hs]

theorem lt32 (x : Nat) : x % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem bstep_eq (x y c : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hc : c ≤ 1) :
    x + 2 ^ 32 * (4294967295 * (1 - (x + 2 ^ 32 - y - c) / 2 ^ 32) / 4294967295) =
      (x + 2 ^ 32 - y - c) % 2 ^ 32 + y + c := by omega

theorem bstep0_eq (x y : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    x + 2 ^ 32 * (4294967295 * (1 - (x + 2 ^ 32 - y) / 2 ^ 32) / 4294967295) =
      (x + 2 ^ 32 - y) % 2 ^ 32 + y := by omega

theorem bstep_le (x y c : Nat) :
    4294967295 * (1 - (x + 2 ^ 32 - y - c) / 2 ^ 32) / 4294967295 ≤ 1 := by omega

theorem bstep0_le (x y : Nat) :
    4294967295 * (1 - (x + 2 ^ 32 - y) / 2 ^ 32) / 4294967295 ≤ 1 := by omega

theorem mask_eq (w : Nat) : 4294967295 * w = 4294967295 * (4294967295 * w / 4294967295) := by
  rw [Nat.mul_div_cancel_left w (by decide)]
''')

lowAk = sorted(lowA, key=lambda k: -lowA[k])
assert [-lowA[k] for k in lowAk] == [B ** i for i in range(9)]
hiBt = lin_txt(hiB)
emit_def('bQ1', 'Limbs 7 to 15 of the input: `q1`.', sum_txt(q1))
emit_def('bQ3', 'The nine words of `q1 * ⌊2 ^ 512 / n⌋` above its low nine: `q3`.', sum_txt(q3))
emit_def('bLowA', 'The low nine words of `q1 * ⌊2 ^ 512 / n⌋`.', sum_txt(lowAk))
emit_def('bR1', 'The input\'s low nine limbs.', sum_txt(r1))
emit_def('bR2', 'The low nine words of `q3 * n`.', sum_txt(r2))
emit_def('bHiB', 'The rest of `q3 * n`, over `2 ^ 288`.', hiBt)
emit_def('bU', 'The first difference, `r1 - r2` modulo `2 ^ 288`.', sum_txt(ud))
emit_def('bV8', 'The low eight words of the second difference.', sum_txt(vd[:8]))
emit_def('bOut', 'The result\'s eight words.', sum_txt(outs))
emit_lt('bLowA', lowAk, B ** 9, None)
emit_lt('bR2', r2, B ** 9, None)
emit_lt('bU', ud, B ** 9, None)
emit_lt('bV8', vd[:8], B ** 8, None)
emit_lt('bOut', outs, B ** 8, None)

LIMBS = ' (ha : ∀ i, a i < 2 ^ 32)'
emit_stage('barrettA', 'The product of `q1` and `⌊2 ^ 512 / n⌋`.', '', eqsA, csA, PA, QA,
           'bQ1 a * %d' % MU, 'bLowA a + %d * bQ3 a' % B ** 9, ['bQ1', 'bLowA', 'bQ3'])
emit_stage('barrettB', 'The product of `q3` and `n`.', '', eqsB, csB, PB, QB,
           'bQ3 a * %d' % N, 'bR2 a + %d * bHiB a' % B ** 9, ['bQ3', 'bR2', 'bHiB'])
emit_stage('barrettU', 'The first subtraction, with its final borrow.', LIMBS, eqsU, csU, PU, QU,
           'bR1 a + %d * (psvUM8 a / 4294967295)' % B ** 9, 'bU a + bR2 a', ['bR1', 'bU', 'bR2'])
emit_stage('barrettV', 'The subtraction of `n`, with its final borrow.', '', eqsV, csV, PV, QV,
           'bU a + %d * (psvVM8 a / 4294967295)' % B ** 9,
           'bV8 a + %d * psvVD8 a + %d' % (B ** 8, N), ['bU', 'bV8'])
emit_stage('barrettS', 'The addition of `n` when the subtraction borrowed.', '', eqsS, csS, PS,
           QS, 'bV8 a + %d * (psvVM8 a / 4294967295)' % N,
           'bOut a + %d * psvS130h a' % B ** 8, ['bV8', 'bOut'])

emit('end C3.Models')
path = os.path.join(ROOT, 'C3BootProofs/Models/P256BarrettChain.lean')
open(path, 'w').write('\n'.join(out) + '\n')
print('wrote', path, len(out))
