#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/SvP256A.lean: the P-256 check in
`sigstore::verify` from 0xFBA to the inversion of `s` at 0x1328, composed
from the generated stages `sv_eca1`, `sv_eca2`, and `sv_eca3`.

The stages take about a hundred hypotheses each, so this reads their
statements and writes the arguments and the names of their conclusions.

Usage: python3 scripts/gen-sv-p256a.py   (from c3-boot-proofs/)
"""

import re

BASE = 'C3BootProofs/Proofs/'


def stmt(fn, name):
    s = open(BASE + fn + '.lean').read()
    i = s.index(f'theorem {name} ')
    j = s.index('\n  have t0', i)
    return s[i:j]


def sig(fn, name):
    st = stmt(fn, name)
    k = st.index('\n    (¬')
    ph = re.sub(r'\{[^}]*\}', '', st[:k])
    pn = [p for p in re.findall(r'\(([A-Za-z0-9_]+) :', ph) if not p.isdigit()]
    c2 = st[k:][st[k:].index("∃ n', "):]
    lines = [l.strip().rstrip('∧').strip() for l in c2.split('\n') if l.strip()]
    return pn, [cname(l) for l in lines]


def sc(fn, name):
    """The stage's success condition, as written in its statement."""
    st = stmt(fn, name)
    k = st.index('\n    (¬ (')
    e = st.index(') ∧ SvErrRet', k)
    return st[k + len('\n    (¬ ('):e]


def nsc(fn, name):
    """How many conjuncts of the success condition come before the stage's `∃ n'`."""
    st = stmt(fn, name)
    k = st.index('\n    (¬')
    rest = st[k:].split('\n')[2:]
    return next(i for i, l in enumerate(rest) if "∃ n', Steps" in l)


def cname(l):
    if l.startswith("∃ n', Steps"):
        return 'STEPS'
    if re.match(r"St n'\.mem SV n' 0x", l):
        return 'ST'
    for pre, nm in (("SvCode", 'E'), ("SvSaves", 'V'), ("(∀ x, SvR", 'FR'), ("reg n' sp", 'r2')):
        if l.startswith(pre):
            return nm
    m = re.match(r"reg n' \((\d+) : Fin 32\)", l) or re.match(r"reg n' (a\d)", l)
    if m:
        return 'r' + m.group(1)
    for pre, nm in (("memLoad32 n'\\.mem", 'w'), ("n'\\.mem", 'b'), ("accV n'\\.mem", 'a')):
        m = re.match(pre + r" \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x([0-9A-F]+)\)", l)
        if m:
            return nm + m.group(1).lower()
    m = re.match(r"\(∀ j, j < \d+ → n'\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 \(0x([0-9A-F]+) \+ j\)\)", l)
    if m:
        return 'q' + m.group(1).lower()
    raise ValueError(l)


def pat(cs, k):
    names = []
    for c in cs:
        if c == 'STEPS':
            names += [f"n{k}", f"c{k}"]
        elif c in ('ST', 'E', 'V', 'FR'):
            names.append({'ST': 's', 'E': 'E', 'V': 'V', 'FR': 'fR'}[c] + str(k))
        else:
            names.append(f"{c[0]}{k}_{c[1:]}")
    return names


def fa(e):
    return f"B + 0x21A0 + BitVec.ofNat 32 0x{e:X}"


IVW = list(range(0x24, 0x5C, 4)) + [0x64, 0x68, 0x6C] + list(range(0x7C, 0x134, 4))
W0 = "(fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))"
N = "accV M0 (BitVec.ofNat 32 0x3FCC4268) 8"
ONE = "accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8"
QV = ["gsVal M0 x21 1 * 2 ^ 256 % p256", "gsVal M0 x21 0x21 * 2 ^ 256 % p256", "accV M0 (BitVec.ofNat 32 0x3FCC43A8) 8",
      "beNat (b32 er)", "beNat (b32 es)", f"beNat (memBytes M0 (memLoad32 n0.mem ({fa(0x84)})) 32) % C3.p256.n"]
ST0 = f"⟨1, ({N} : Int), (beNat (b32 es) : Int), 0, ({ONE} : Int), 0x24F⟩"

p1, c1 = sig('SvEcA1', 'sv_eca1')
p2, c2 = sig('SvEcA2', 'sv_eca2')
p3, c3 = sig('SvEcA3', 'sv_eca3')
SC1 = sc('SvEcA1', 'sv_eca1')
SC2 = sc('SvEcA2', 'sv_eca2')

# The hypotheses of `sv_eca1` other than its frame words, which this ties to `n0`.
st1 = stmt('SvEcA1', 'sv_eca1')
hyps = [l for l in st1[st1.index('\n') + 1:st1.index('\n    (¬')].split('\n') if not l.lstrip().startswith('(w0_')]
hyps = [l for l in hyps if not l.lstrip().startswith('(k_in')]
hyps[-1] = hyps[-1].rstrip()
if hyps[-1].endswith(' :'):
    hyps[-1] = hyps[-1][:-2]

out = []
O = out.append
O("import C3BootProofs.Proofs.SvIvLoop")
O("import C3BootProofs.Proofs.SvSeg")
O("import C3BootProofs.Proofs.SvEcA1")
O("import C3BootProofs.Proofs.SvEcA2")
O("import C3BootProofs.Proofs.SvEcA3\n")
O("/-!\n# `sigstore::verify`: the P-256 check up to the inversion of `s`\n")
O("From 0xFBA to the inversion's head at 0x1328: `sv_eca1`, `sv_eca2`, and `sv_eca3` check `r` and `s`, decode")
O("the key, and set up the inversion, whose state is then `IvInv` for the starting `ivLoop8` state `p256Iv0`.")
O("The frame words the inversion keeps are those at the start.\n-/\n")
O("namespace C3.RV32.Sv\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2\n\nset_option maxRecDepth 100000\n")
O("/-- The inversion of `s`'s starting state: `f` is the order `n`, `g` is `s`, `d` is 0, `e` is 1, and")
O("591 divsteps are left. -/")
O("def p256Iv0 (M0 : Word → BitVec 8) (es : Bytes) : Iv :=")
O(f"  {ST0}\n")
O("set_option maxHeartbeats 64000000 in")
O("/-- **The P-256 check up to the inversion of `s`**: from 0xFBA to 0x1328, or an error return when `r` or")
O("`s` is out of range or the key isn't a point on the curve. -/")
O("theorem sv_p256_inv {B out bp x21 x26 : Word} {er es : Bytes} {v : Nat → Word} {n0 : Machine}")
for l in hyps:
    O(l)
O("    (IC0 : SvIvCode M0) (UC0 : SvUpCode M0) (D0 : P2Data M0) (BG0 : BGEnv M0) (RS : SvRoSep B) (BY0 : BYEnv M0)")
O(f"    (k1 : SvIn B x21 1) (k41 : SvIn B x21 0x41) (dg_in : SvIn B (memLoad32 n0.mem ({fa(0x84)})) 32) :")
O(f"    (¬ (({SC1}) ∧ ({SC2})) ∧ SvErrRet B out v n0) ∨")
O(f"    (({SC1}) ∧ ({SC2}) ∧")
O("      ∃ m, Steps n0 m ∧ (∀ x, SvR B x → m.mem x = M0 x) ∧ St m.mem SV m 0x1328 (reg m) ∧")
O(f"        IvInv B m v (reg n0 (3 : Fin 32)) (reg n0 (4 : Fin 32)) out bp (BitVec.ofNat 32 0x1) x26")
O(f"          ({QV[0]}) ({QV[1]})")
O(f"          ({QV[2]}) ({QV[3]}) ({QV[4]})")
O(f"          ({QV[5]}) ({N})")
O(f"          {W0} (p256Iv0 M0 es)) := by")


def arg1(p):
    if p.startswith('w0_'):
        return 'rfl'
    if p == 'k_in':
        return 'k1'
    return p


def argk(p, k, extra):
    if p in ('F', 'hret', 'hO', 'M0', 'EC0', 'D0', 'BG0', 'RS', 'BY0', 'dg_in'):
        return p
    m = {'E0': f'E{k}', 'V0': f'V{k}', 's0': f's{k}', 'fM': f'fR{k}'}
    m.update(extra)
    if p in m:
        return m[p]
    for pre in ('g0_', 'w0_', 'a0_', 'b0_', 'q0_'):
        if p.startswith(pre):
            return f"{'r' if pre == 'g0_' else pre[0]}{k}_{p[3:]}"
    raise ValueError(p)


n1, n2, n3 = nsc('SvEcA1', 'sv_eca1'), nsc('SvEcA2', 'sv_eca2'), nsc('SvEcA3', 'sv_eca3')
x1 = [f"x1_{i}" for i in range(n1)]
x2 = [f"x2_{i}" for i in range(n2)]
assert n3 == 0 and n2 == 5
O("  rcases sv_eca1 " + " ".join(arg1(p) for p in p1) + " with ⟨hn, e⟩ | ⟨" + ", ".join(x1 + pat(c1, 1)) + "⟩")
O("  · exact .inl ⟨fun h => hn h.1, e⟩")
O("  have h1 : " + SC1 + " := ⟨" + ", ".join(x1) + ", trivial⟩")
O("  have CH1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x hx => (fR1 x hx).trans (fM x hx).symm")
O("  rcases sv_eca2 " + " ".join(argk(p, 1, {'k_in': 'k41'}) for p in p2) + " with ⟨hn, e⟩ | ⟨" + ", ".join(x2 + pat(c2, 2)) + "⟩")
O("  · exact .inl ⟨fun h => hn h.2, SvErrRet.pre c1 r1_3 r1_4 CH1 e⟩")
O("  have h2 : " + SC2 + " := ⟨" + ", ".join(x2) + ", trivial⟩")
O("  rcases sv_eca3 " + " ".join(argk(p, 2, {'hrz': 'x2_3', 'hsz': 'x2_4'}) for p in p3)
  + " with ⟨hn, -⟩ | ⟨" + ", ".join(pat(c3, 3)) + "⟩")
O("  · exact absurd trivial hn")
t = ["E3", "IC0.sv F fR3", "EC0.sv F fR3", "UC0.sv F fR3", "V3", "r3_2", "by rw [r3_3, r2_3, r1_3]",
     "by rw [r3_4, r2_4, r1_4]", "r3_18", "r3_19", "r3_21", "r3_24", "r3_26", "r3_27", "by rw [r3_23, r3_25]; rfl",
     "w3_78", "by show 0x24F < 2 ^ 32; decide", "w3_60", "w3_70", "accV_dataR F fR3 (by decide) (by decide)"]
t += [f"a3_{a:x}" for a in (0x240, 0x260, 0x280, 0x2A0, 0x2C0, 0x2E0)]
for a, b in ((0x1380, 0x13A0), (0x1480, 0x14A0), (0x1020, 0x1040), (0x420, 0x440)):
    t += [f"by rw [b3_{b:x}, a3_{a:x}]; rfl", f"by rw [b3_{b:x}]; decide"]
t.append("fun e he => ?_")
O("  refine .inr ⟨h1, h2, n3, c1.trans (c2.trans c3), fR3, s3, " + ", ".join(t) + "⟩")
O("  simp only [ivWords, List.mem_cons, List.not_mem_nil, or_false] at he")
O("  rcases he with " + " | ".join(["rfl"] * len(IVW)))
for e in IVW:
    O(f"  · exact w3_{e:x}")
O("")
O("end C3.RV32.Sv")
open(BASE + 'SvP256A.lean', 'w').write("\n".join(out) + "\n")
