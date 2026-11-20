#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/SvP256D.lean: the end of the P-256 check in
`sigstore::verify`, from the inversion of `Z` at 0x1B54 with no divsteps
left to 0x2034, through the stage `sv_ze`.

Usage: python3 scripts/gen-sv-p256d.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import BASE, Chain, Stage, subst, top_split  # noqa: E402

ZIW = [0x4C, 0x50, 0x54, 0x58, 0x64, 0x68, 0x6C] + list(range(0x7C, 0x134, 4))
GLOBAL = ['IC0', 'EC0', 'UC0', 'UE0', 'N80', 'P2C0', 'GDC0', 'P2D0', 'SC0', 'BY0', 'WN0']
EXTRA = ['hnz', 'hX', 'hY', 'hid', 'hzi']

ze = Stage('SvZE', 'sv_ze')
pty = dict(ze.params)
proof = []
P = proof.append
ch = Chain(P)
ov = {p: p for p in GLOBAL + EXTRA + ['F', 'hret', 'hO', 'M0', 'fM']}
ov.update({'E0': 'I.E', 'V0': 'I.V', 's0': 's', 'g0_2': 'I.sp', 'g0_18': 'I.g18', 'g0_19': 'I.g19',
           'g0_26': 'I.g26', 'g0_27': 'I.g27', 'w0_20': 'I.w20', 'w0_34': 'rfl', 'w0_38': 'rfl', 'w0_78': 'I.wr',
           'w0_460': 'I.w460', 'w0_464': 'I.w464', 'a0_2a0': 'I.a2a0', 'a0_2c0': 'I.a2c0', 'a0_2e0': 'I.a2e0',
           'a0_15a8': 'I.a15a8', 'a0_15c8': 'I.a15c8', 'a0_420': '(I.a420.trans (I.aP.symm.trans (accV_dataR F fM (by decide) (by decide))))',
           'a0_440': '(I.a440.trans (I.aR.symm.trans (accV_dataR F fM (by decide) (by decide))))', 'hrem': "hrem'", 'hfs': 'I.lf', 'hds': 'I.ld'})
fixed = {'out': 'out', 'bp': 'bp', 'x26': 'x26', 'nzw': 'nzw', 'rv': 'rv', 'sv': 'sv', 'zv': 'zv', 'X': 'X', 'Y': 'Y',
         'rem': 'BitVec.ofNat 32 st.rem'}
for e in ZIW:
    ov[f'w0_{e:x}'] = f"(I.ww 0x{e:X} (by decide))"
    fixed[f'w{e:x}'] = f"W 0x{e:X}"
for p, _ in ze.params:
    if p not in ov and p[:3] in ('a0_', 'b0_'):
        ov[p] = 'rfl'
missing = [p for p, _ in ze.params if p not in ov]
assert not missing, missing
args, names, pats, sc = ch.call(ze, ov, fixed)
SC = " ∧ ".join(f"({x})" for x in sc) + " ∧ True"
env = ch.env


def inst(t):
    return subst(t, env)


P("  have hrem' : BitVec.ofNat 32 st.rem = 0 := by rw [h0]; rfl")
P("  rcases @sv_ze " + " ".join(args) + " with ⟨hn, e⟩ | ⟨" + ", ".join(names + pats) + "⟩")
P("  · exact .inl ⟨hn, e⟩")
keep = []
for key, f in ch.prev.items():
    if key in ('STEPS', 'ST', 'E', 'V', 'FR', 'r3', 'r4'):
        continue
    t = re.sub(r"(?<![\w.'])n1(?![\w'])", "m'", f.text)
    keep.append((key, t))


def pname(key):
    return f"{key[0] if key[0] != 'm' else 'mb'}1_{key[1:] if key[0] != 'm' else key[2:]}"


P("  exact .inr ⟨⟨" + ", ".join(names) + ", trivial⟩, n1, c1, fR1, s1, E1, V1, by rw [r1_3]; exact I.g3,")
P("    by rw [r1_4]; exact I.g4, " + ", ".join(pname(k) for k, _ in keep) + "⟩")

out = []
O = out.append
O("import C3BootProofs.Proofs.SvP256C")
O("import C3BootProofs.Proofs.SvZE\n")
O("/-!\n# `sigstore::verify`: the end of the P-256 check\n")
O("From the inversion of the sum's `Z` at 0x1B54, with no divsteps left, to 0x2034: `sv_ze` takes the affine")
O("`x` of the sum and compares it with `r`.\n-/\n")
O("namespace C3.RV32.Sv\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd\n")
O("set_option maxRecDepth 100000\n")
O("set_option maxHeartbeats 64000000 in")
O("/-- **The end of the P-256 check**: from 0x1B54 to 0x2034 when the affine `x` of the sum matches `r`,")
O("and an error return otherwise. -/")
O("theorem sv_p256_end {B r3 r4 out bp x26 nzw : Word} {rv sv zv X Y P R2 : Nat} {W v : Nat → Word} {n0 : Machine}")
O("    {st : Iv} (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (s : St n0.mem SV n0 0x1B54 (reg n0))")
O("    (I : ZvInv B n0 v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W st) (h0 : st.rem = 0)")
O("    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)")
O("    " + " ".join(f"({p} : {pty[p]})" for p in GLOBAL))
for p in EXTRA:
    O(f"    ({p} : {inst(pty[p])})")
O(f"    :")
O(f"    (¬ ({SC}) ∧ SvErrRet B out v n0) ∨")
O(f"    (({SC}) ∧ ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x2034 (reg m') ∧")
O("      SvCode m'.mem ∧ SvSaves B m'.mem v ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧")
for i, (_, t) in enumerate(keep):
    O(f"      {t}" + (" ∧" if i + 1 < len(keep) else ") := by"))
out += proof
O("")
O("end C3.RV32.Sv")
open(BASE + 'SvP256D.lean', 'w').write("\n".join(out) + "\n")
