#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/SvP256B.lean: the P-256 check in
`sigstore::verify` from the end of the inversion of `s` at 0x1556 to the
main loop at 0x18F8, composed from the generated stages `sv_ive` through
`sv_ecw3` with `svchain.Chain`.

Usage: python3 scripts/gen-sv-p256b.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import BASE, Chain, Stage, strip_parens, top_split  # noqa: E402


def fa(e):
    return f"B + 0x21A0 + BitVec.ofNat 32 0x{e:X}"


IVW = list(range(0x24, 0x5C, 4)) + [0x64, 0x68, 0x6C] + list(range(0x7C, 0x134, 4))
SEQ = [('SvIvE', 'sv_ive'), ('SvEcD', 'sv_ecd'), ('SvEcT0a', 'sv_ect0a'), ('SvEcT0c', 'sv_ect0c'),
       ('SvEcT0b', 'sv_ect0b'), ('SvEcT1a', 'sv_ect1a'), ('SvEcT1c', 'sv_ect1c'), ('SvEcT1b', 'sv_ect1b'),
       ('SvEcW2', 'sv_ecw'), ('SvEcW3', 'sv_ecw3')]
GLOBAL = ['IC0', 'EC0', 'UC0', 'UE0', 'N80', 'RS', 'PM0', 'WM0', 'PT0', 'WN0']
stages = [Stage(*x) for x in SEQ]
gty = {}
for st in stages:
    for p, ty in st.params:
        if p in GLOBAL and p not in gty:
            gty[p] = ty

proof = []
P = proof.append
ch = Chain(P)

# sv_ive, from the invariant at the inversion's exit.
ive = stages[0]
ov = {p: p for p, _ in ive.params if p in GLOBAL or p in ('F', 'hret', 'hO', 'M0', 'fM')}
ov.update({'E0': 'I.E', 'V0': 'I.V', 's0': 's', 'g0_2': 'I.sp', 'g0_18': 'I.g18', 'g0_19': 'I.g19',
           'g0_21': 'I.g21', 'g0_23': 'rfl', 'g0_24': 'I.g24', 'g0_25': 'rfl', 'g0_26': 'I.g26', 'g0_27': 'I.g27',
           'w0_5c': 'rfl', 'w0_60': 'I.w60', 'w0_70': 'I.w70', 'w0_78': 'I.wr', 'hfs': 'I.lf', 'hds': 'I.ld'})
fixed = {'out': 'out', 'bp': 'bp', 'x26': 'x26', 's8v': 'BitVec.ofNat 32 0x3FCC4268',
         'w60': 'BitVec.ofNat 32 0x332E3755', 'w70': 'BitVec.ofNat 32 0x11FF43B1', 'rem': 'BitVec.ofNat 32 st.rem'}
for e in IVW:
    ov[f'w0_{e:x}'] = f"(I.ww 0x{e:X} (by decide))"
    fixed[f'w{e:x}'] = f"W 0x{e:X}"
for a, q in zip((0x240, 0x260, 0x280, 0x2A0, 0x2C0, 0x2E0), ('qx', 'qy', 'qz', 'rv', 'sv', 'zv')):
    ov[f'a0_{a:x}'] = f"I.a{a:x}"
    fixed[q] = q
for p, _ in ive.params:
    if p.startswith('a0_') and p not in ov or p.startswith('b0_'):
        ov[p] = 'rfl'
args, names, pats, sc_ive = ch.call(ive, ov, fixed)
SC = " ∧ ".join(f"({x})" for x in sc_ive) + " ∧ True"
P("  rcases @sv_ive " + " ".join(args) + " with ⟨hn, e⟩ | ⟨" + ", ".join(names + pats) + "⟩")
P("  · exact .inl ⟨hn, e⟩")

P0 = P1 = None
for st in stages[1:]:
    k = ch.k
    ov = {p: p for p, _ in st.params if p in GLOBAL or p in ('F', 'hret', 'hO', 'M0')}
    ov.update({'E0': f'E{k}', 'V0': f'V{k}', 's0': f's{k}', 'fM': f'fR{k}'})
    fixed = {}
    if st.name == 'sv_ect0a':
        pv = ch.prev
        P0 = f"({strip_parens(pv['a320'].rhs)}, {strip_parens(pv['a340'].rhs)}, {strip_parens(pv['a360'].rhs)})"
        P1 = f"({strip_parens(pv['a3a0'].rhs)}, {strip_parens(pv['a3c0'].rhs)}, {strip_parens(pv['a3e0'].rhs)})"
        fixed = {'P0': P0, 'P1': P1}
        ov.update({'b0_440': 'rfl', 'b0_14a0': 'rfl',
                   'p0_320': f"(ptF_of a{k}_320 a{k}_340 a{k}_360)", 'p0_3a0': f"(ptF_of a{k}_3a0 a{k}_3c0 a{k}_3e0)",
                   'p0_1480': f"(ptF_of a{k}_1480 a{k}_14a0 a{k}_14c0)",
                   'p0_1500': f"(ptF_of a{k}_1500 a{k}_1520 a{k}_1540)"})
    if 'hP0' in [p for p, _ in st.params]:
        ov.update({'hP0': 'hG', 'hP1': 'hQ'})
    args, names, pats, _ = ch.call(st, ov, fixed)
    assert not names
    P(f"  rcases @{st.name} " + " ".join(args) + " with ⟨hn, -⟩ | ⟨" + ", ".join(pats) + "⟩")
    P("  · exact absurd trivial hn")

K = ch.k
fin = ch.prev
T0 = [0x420 + 0x60 * j for j in range(8)]
T1 = [0x720 + 0x60 * j for j in range(8)]
D0 = strip_parens(fin['mb1024'].rhs)
D1 = strip_parens(fin['mb112c'].rhs)
keep = []
for key, f in fin.items():
    if key in ('STEPS', 'ST', 'E', 'V', 'FR', 'r3', 'r4') or key[0] in 'pqm':
        continue
    t = f.text.replace(f"n{K}", "m'")
    if re.search(r"(?<![\w.'])n\d+(?![\w'])", t.replace("n0", "")):
        continue
    keep.append((key, t))


def pname(key):
    return f"{key[0] if key[0] != 'm' else 'mb'}{K}_{key[1:] if key[0] != 'm' else key[2:]}"


chain3 = ", ".join(f"r{k}_3" for k in range(K, 0, -1))
chain4 = ", ".join(f"r{k}_4" for k in range(K, 0, -1))
steps = f"c{K}"
for k in range(K - 1, 0, -1):
    steps = f"c{k}.trans ({steps})"
P(f"  refine .inr ⟨⟨x1_0, trivial⟩, n{K}, {steps}, fR{K}, s{K}, ME.fr F fR{K}, V{K},")
P(f"    by rw [{chain3}]; exact I.g3, by rw [{chain4}]; exact I.g4,")
P("    " + ", ".join(pname(k) for k, _ in keep) + ",")
P(f"    ⟨fun j hj => ?_, fun j hj => ?_, fun j _ => ⟨tbl2_lt hG j, tbl2_lt hQ j⟩, mb{K}_1024, mb{K}_112c⟩⟩")
for tab in (T0, T1):
    P("  · rcases j with " + " | ".join(["_"] * 8) + " | j")
    for d in tab:
        P(f"    · exact p{K}_{d:x}")
    P("    · omega")

out = []
O = out.append
O("import C3BootProofs.Proofs.SvP256A")
for fn, _ in SEQ[1:]:
    O(f"import C3BootProofs.Proofs.{fn}")
O("import C3BootProofs.Proofs.SvIvE\n")
O("/-!\n# `sigstore::verify`: the P-256 check from the inverse to the main loop\n")
O("From 0x1556, where the inversion of `s` ends, to the main loop at 0x18F8: `sv_ive` normalizes the inverse,")
O("`sv_ecd` computes `u₁` and `u₂`, the `sv_ect*` stages build the tables of odd multiples, and `sv_ecw` and")
O("`sv_ecw3` write the wNAF digits, which leaves what `ml2_main` takes.\n-/\n")
O("namespace C3.RV32.Sv\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2\n\nset_option maxRecDepth 100000\n")
O("theorem ptF_of {M : Word → BitVec 8} {B : Word} {c x y z : Nat}")
O("    (hx : accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8 = x) (hy : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8 = y)")
O("    (hz : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8 = z) : ptF M B c = (x, y, z) := by")
O("  unfold ptF; rw [hx, hy, hz]\n")
O("set_option maxHeartbeats 64000000 in")
O("/-- **The P-256 check from the inverse to the main loop**: from 0x1556 to 0x18F8, or a panic when the")
O("inversion's `f` isn't 1. -/")
O("theorem sv_p256_tab {B r3 r4 out bp x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word} {n0 : Machine}")
O("    {st : Iv} (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (s : St n0.mem SV n0 0x1556 (reg n0))")
O("    (I : IvInv B n0 v r3 r4 out bp (BitVec.ofNat 32 0x1) x26 qx qy qz rv sv zv N W st)")
O("    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)")
O("    " + " ".join(f"({p} : {gty[p]})" for p in GLOBAL) + " (ME : MlEnv M0)")
O(f"    (hG : Pt2Lt {P0})")
O(f"    (hQ : Pt2Lt {P1}) :")
O(f"    (¬ ({SC}) ∧ Panics n0) ∨")
O(f"    (({SC}) ∧ ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x18F8 (reg m') ∧")
O("      MlEnv m'.mem ∧ SvSaves B m'.mem v ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧")
for _, t in keep:
    O(f"      {t} ∧")
O(f"      GM2 B m'.mem (tbl2 {P0}) (tbl2 {P1})")
O(f"        ({D0})")
O(f"        ({D1})) := by")
out += proof
O("")
O("end C3.RV32.Sv")
open(BASE + 'SvP256B.lean', 'w').write("\n".join(out) + "\n")
