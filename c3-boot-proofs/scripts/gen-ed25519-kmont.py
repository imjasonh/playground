#!/usr/bin/env python3
"""Writes C3BootProofs/Models/Ed25519KMont.lean: the value of
`Scalar29::montgomery_mul`'s body, `smmRed`, from its definitions in
ScalarMontBody.lean.

For limbs below 2^29, each Karatsuba coefficient the body forms is the
schoolbook one (`kz*`), each Montgomery step clears 29 low bits (`kt*`), and
the sums do not wrap (`ks*`). `smm_val` combines them: the nine output limbs
are below 2^29, their value `r` is below `2 L` when `b`'s value is below `L`,
and `2^261 r = a b + N L` for some `N`.

Run it from c3-boot-proofs/ after ScalarMontBody.lean changes.
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
BODY = os.path.join(ROOT, 'C3BootProofs', 'Proofs', 'ScalarMontBody.lean')
OUT = os.path.join(ROOT, 'C3BootProofs', 'Models', 'Ed25519KMont.lean')

L = [0x1CF5D3ED, 0x009318D2, 0x1DE73596, 0x1DF3BD45, 0x0000014D, 0, 0, 0, 0x00100000]
LNUM = sum(l << (29 * i) for i, l in enumerate(L))
assert LNUM == 2 ** 252 + 27742317777372353535851937790883648493
LFACTOR = 307527195
assert (LFACTOR * L[0] + 1) % 2 ** 29 == 0
PB = '(2 ^ 29 - 1) * (2 ^ 29 - 1)'
HAB = '(ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29)'


def parse_defs():
    defs = {}
    pat = re.compile(r'^def (smv\w+) \((\w+) (\w+) : Nat → Nat\) : Nat := (.*)$')
    with open(BODY) as f:
        for line in f:
            m = pat.match(line.rstrip('\n'))
            if m:
                defs[m.group(1)] = m.group(4)
    return defs


DEFS = parse_defs()


def refs(name):
    return re.findall(r'\b(smv\w+) a b\b', DEFS[name])


def zname(k):
    if k == 0:
        return 'smvPA0B0'
    if k == 16:
        return 'smvPA8B8'
    return 'smvZ%d' % k


def closure(name):
    """The definitions to unfold under `name`, stopping at `smvAA*` and `smvBB*`."""
    seen, stack = [], [name]
    while stack:
        n = stack.pop()
        if n in seen or re.match(r'smv(AA|BB)\d$', n):
            continue
        seen.append(n)
        stack.extend(refs(n))
    return seen


def pairs_of(names):
    """The products `a i * b j` that the unfolded definitions mention."""
    ps = set()
    for n in names:
        m = re.match(r'smvPA(\d)B(\d)$', n)
        if m:
            ps.add((int(m.group(1)), int(m.group(2))))
            continue
        m = re.match(r'smvPAA(\d)BB(\d)$', n)
        if m:
            x, y = int(m.group(1)), int(m.group(2))
            ps |= {(x, y), (x, y + 5), (x + 5, y), (x + 5, y + 5)}
            continue
        m = re.match(r'smvPAA(\d)B4$', n)
        if m:
            x = int(m.group(1))
            ps |= {(x, 4), (x + 5, 4)}
            continue
        m = re.match(r'smvPA4BB(\d)$', n)
        if m:
            y = int(m.group(1))
            ps |= {(4, y), (4, y + 5)}
    return sorted(ps)


def coeff(k):
    return [(i, k - i) for i in range(9) if 0 <= k - i < 9]


def csum(k):
    return ' + '.join('a %d * b %d' % p for p in coeff(k))


def pbound(i, j):
    return ('  have p%d%d : a %d * b %d ≤ %s :=\n'
            '    Nat.mul_le_mul (Nat.le_pred_of_lt (ha %d (by decide))) (Nat.le_pred_of_lt (hb %d (by decide)))\n'
            % (i, j, i, j, PB, i, j))


def pns(k):
    """The `N_i * L_j` terms of `S_k`, in the order the body adds them."""
    m = re.match(r'\(smvC\d+ a b \+ \w+ a b((?: \+ smvPN\d+L\d+ a b)*)\) % 2 \^ 64$', DEFS['smvS%d' % k])
    assert m, k
    return [(int(x), int(y)) for x, y in re.findall(r'smvPN(\d+)L(\d+)', m.group(1))]


def main():
    o = []
    w = o.append
    w('import C3BootProofs.Proofs.ScalarMont\n')
    w('import C3BootProofs.Spec.Ed25519\n')
    w('import C3BootProofs.Ring.Tactic\n\n')
    w('/-! # The value of `Scalar29::montgomery_mul`\'s body\n\n')
    w('`scripts/gen-ed25519-kmont.py` writes this file from the definitions in\n')
    w('`ScalarMontBody.lean`. For limbs below 2^29, `smm_val` gives the value of\n')
    w('`smmRed a b`, the nine limbs `montgomery_reduce(mul_internal(a, b))`\n')
    w('returns before the final `sub`. -/\n\n')
    w('namespace C3.RV32.EdK\n\n')
    w('open C3.RV32\n\n')
    w('/-- Nine 29-bit limbs\' value. -/\n')
    w('def sv9 (f : Nat → Nat) : Nat :=\n  ' +
      ' + '.join(('f 0' if i == 0 else '2 ^ %d * f %d' % (29 * i, i)) for i in range(9)) + '\n\n')
    w('theorem mont0 (S : Nat) : (S + (S % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 * 485872621) % 2 ^ 29 = 0 := by\n')
    w('  omega\n\n')
    for x in range(4):
        w('theorem aa%d {a : Nat → Nat} (b : Nat → Nat) (ha : ∀ i, i < 9 → a i < 2 ^ 29) : smvAA%d a b = a %d + a %d :=\n'
          % (x, x, x, x + 5))
        w('  Nat.mod_eq_of_lt (by have := ha %d (by decide); have := ha %d (by decide); omega)\n\n' % (x, x + 5))
        w('theorem bb%d (a : Nat → Nat) {b : Nat → Nat} (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvBB%d a b = b %d + b %d :=\n'
          % (x, x, x, x + 5))
        w('  Nat.mod_eq_of_lt (by have := hb %d (by decide); have := hb %d (by decide); omega)\n\n' % (x, x + 5))
    w('section\n\nvariable {a b : Nat → Nat}\n\n')
    for k in range(17):
        z = zname(k)
        if k in (0, 16):
            w('theorem kz%d : %s a b = %s := rfl\n\n' % (k, z, csum(k)))
            continue
        names = closure(z)
        used_aa = sorted({n for n in sum((refs(n) for n in names), []) if re.match(r'smv(AA|BB)\d$', n)})
        w('theorem kz%d %s : %s a b = %s := by\n' % (k, HAB, z, csum(k)))
        for (i, j) in pairs_of(names):
            w(pbound(i, j))
        rw = ', '.join(names)
        for n in used_aa:
            kind, x = n[3:5], n[5:]
            rw += ', %s%s %s' % (kind.lower(), x, 'b ha' if kind == 'AA' else 'a hb')
        if any(re.match(r'smvPAA\d+(BB|B4)', n) for n in names):
            rw += ', Nat.add_mul'
        if any(re.match(r'smvP(AA\d+|A4)BB', n) for n in names):
            rw += ', Nat.mul_add'
        w('  simp only [%s]\n' % rw)
        w('  omega\n\n')
    for k in range(17):
        n = len(coeff(k))
        args = '' if k in (0, 16) else ' ha hb'
        w('theorem kzb%d %s : %s a b ≤ %d * (%s) := by\n' % (k, HAB, zname(k), n, PB))
        w('  rw [kz%d%s]\n' % (k, args))
        for (i, j) in coeff(k):
            w(pbound(i, j))
        w('  omega\n\n')
    for i in range(9):
        w('theorem kn%d (a b : Nat → Nat) : smvN%d a b < 2 ^ 29 := by\n  unfold smvN%d; omega\n\n' % (i, i, i))
    for k in range(17):
        inner = 'smvT%d' % k if k <= 8 else 'smvS%d' % k
        w('theorem kc%d (a b : Nat → Nat) : smvC%d a b < 2 ^ 35 := by\n  unfold smvC%d %s; omega\n\n' % (k, k, k, inner))

    def sbounds(k):
        s = '  have := kc%d a b\n  have := kzb%d ha hb\n' % (k - 1, k)
        for (i, _) in pns(k):
            s += '  have := kn%d a b\n' % i
        return s

    for k in range(1, 17):
        rhs = 'smvC%d a b + %s a b' % (k - 1, zname(k))
        for (i, j) in pns(k):
            rhs += ' + smvN%d a b * %d' % (i, L[j])
        w('theorem ks%d %s : smvS%d a b = %s := by\n' % (k, HAB, k, rhs))
        w(sbounds(k))
        w('  unfold smvS%d %s\n' % (k, ' '.join('smvPN%dL%d' % p for p in pns(k))))
        w('  omega\n\n')
    for k in range(9):
        s = 'smvPA0B0 a b' if k == 0 else 'smvS%d a b' % k
        w('theorem kt%d %s : 2 ^ 29 * smvC%d a b = %s + smvN%d a b * 485872621 := by\n' % (k, HAB, k, s, k))
        if k == 0:
            w('  have hs : %s < 2 ^ 63 := by have := kzb0 ha hb; omega\n' % s)
        else:
            w('  have hs : %s < 2 ^ 63 := by\n    rw [ks%d ha hb]\n' % (s, k))
            w('\n'.join('  ' + ln for ln in sbounds(k).rstrip('\n').split('\n')) + '\n')
            w('    omega\n')
        w('  have hn := kn%d a b\n' % k)
        w('  have hm := mont0 (%s)\n' % s)
        w('  have e : smvN%d a b = %s %% 2 ^ 32 * 307527195 %% 2 ^ 32 %% 2 ^ 29 := rfl\n' % (k, s))
        w('  rw [← e] at hm\n')
        w('  unfold smvC%d smvT%d smvPN%dL0\n' % (k, k, k))
        w('  omega\n\n')
    rsum = ' + '.join(('smvR0 a b' if i == 0 else '2 ^ %d * smvR%d a b' % (29 * i, i)) for i in range(8))
    rsum += ' + 2 ^ 232 * smvC16 a b'
    zsum = ' + '.join(('%s a b' % zname(k) if k == 0 else '2 ^ %d * %s a b' % (29 * k, zname(k))) for k in range(17))
    nsum = ' + '.join(('smvN0 a b' if i == 0 else '2 ^ %d * smvN%d a b' % (29 * i, i)) for i in range(9))
    w('theorem kmont_id %s :\n    2 ^ 261 * (%s) =\n      %s + (%s) * %d := by\n' % (HAB, rsum, zsum, nsum, LNUM))
    for k in range(9):
        w('  have := kt%d ha hb\n' % k)
    for k in range(1, 17):
        w('  have := ks%d ha hb\n' % k)
    for i in range(8):
        w('  have : smvR%d a b = smvS%d a b %% 2 ^ 29 := rfl\n' % (i, i + 9))
    for k in range(9, 17):
        w('  have : smvC%d a b = smvS%d a b / 2 ^ 29 := rfl\n' % (k, k))
    w('  omega\n\n')
    expand = ' + '.join(('(%s)' % csum(k) if k == 0 else '2 ^ %d * (%s)' % (29 * k, csum(k))) for k in range(17))
    w('set_option exponentiation.threshold 600 in\ntheorem kab (a b : Nat → Nat) : sv9 a * sv9 b = %s := by\n  unfold sv9; ring_eq\n\n' % expand)
    w('theorem kmont_val %s :\n    2 ^ 261 * (%s) = sv9 a * sv9 b + (%s) * %d := by\n' % (HAB, rsum, nsum, LNUM))
    w('  have := kmont_id ha hb\n  have := kab a b\n')
    for k in range(17):
        w('  have := kz%d%s\n' % (k, ' (a := a) (b := b)' if k in (0, 16) else ' ha hb'))
    w('  omega\n\n')
    w('set_option exponentiation.threshold 600 in\ntheorem smm_val %s (hbL : sv9 b < Ed25519.L) :\n' % HAB)
    w('    (∀ i, i < 9 → smmRed a b i < 2 ^ 29) ∧ sv9 (smmRed a b) < 2 * Ed25519.L ∧\n')
    w('      ∃ N, 2 ^ 261 * sv9 (smmRed a b) = sv9 a * sv9 b + N * Ed25519.L := by\n')
    w('  have hv := kmont_val ha hb\n')
    w('  have hA : sv9 a ≤ 2 ^ 261 - 1 := by\n    unfold sv9\n')
    for i in range(9):
        w('    have := ha %d (by decide)\n' % i)
    w('    omega\n')
    w('  have hB : sv9 b ≤ Ed25519.L - 1 := by omega\n')
    w('  have hAB : sv9 a * sv9 b ≤ (2 ^ 261 - 1) * (Ed25519.L - 1) := Nat.mul_le_mul hA hB\n')
    for i in range(9):
        w('  have := kn%d a b\n' % i)
    w('  have e : sv9 (smmRed a b) = %s := rfl\n' % rsum.replace('smvC16 a b', 'smvR8 a b'))
    w('  have e8 : smvR8 a b = smvC16 a b % 2 ^ 32 := rfl\n')
    w('  have hr : %s < 2 * Ed25519.L := by\n    unfold Ed25519.L at hAB ⊢\n    omega\n' % rsum)
    w('  have h16 : smvC16 a b < 2 ^ 32 := by unfold Ed25519.L at hr; omega\n')
    w('  rw [Nat.mod_eq_of_lt h16] at e8\n')
    w('  refine ⟨fun i hi => ?_, by rw [e, e8]; exact hr, ⟨%s, ?_⟩⟩\n' % nsum)
    w('  · match i, hi with\n')
    for i in range(8):
        w('    | %d, _ => show smvS%d a b %% 2 ^ 29 < 2 ^ 29; omega\n' % (i, i + 9))
    w('    | 8, _ => show smvR8 a b < 2 ^ 29; unfold Ed25519.L at hr; omega\n')
    w('    | _ + 9, h => exact absurd h (by omega)\n')
    w('  · rw [e, e8, hv]; rfl\n\n')
    w('end\n\nend C3.RV32.EdK\n')
    with open(OUT, 'w') as f:
        f.write(''.join(o))


if __name__ == '__main__':
    main()
