#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/SvP256C.lean: the P-256 check in
`sigstore::verify` from the end of the inversion of `s` at 0x1556 to the
inversion of `Z` at 0x1B54: `sv_p256_tab`, the main loop `ml2_main`, and
the stage `sv_zs`.

Usage: python3 scripts/gen-sv-p256c.py   (from c3-boot-proofs/)
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import BASE, Chain, Stage, fact_key, strip_parens, top_split  # noqa: E402


def fa(e):
    return f"B + 0x21A0 + BitVec.ofNat 32 0x{e:X}"


ZIW = [0x4C, 0x50, 0x54, 0x58, 0x64, 0x68, 0x6C] + list(range(0x7C, 0x134, 4))

src = open(BASE + 'SvP256B.lean').read()
i = src.index('theorem sv_p256_tab ')
j = src.index(' := by\n', i)
tab = src[i:j]
hyp_text = tab[tab.index('\n') + 1:tab.index(' :\n    (¬')]
binders = tab[len('theorem sv_p256_tab '):tab.index('\n')]
body = tab[tab.index(' :\n    (¬') + 3:]
SC = body[len('    (¬ ('):body.index(') ∧ Panics n0) ∨')]
lines = body.split('\n')
k0 = next(n for n, l in enumerate(lines) if l.strip().startswith('MlEnv m\'.mem'))
facts = []
n = k0 + 1
while not lines[n].strip().startswith('GM2 '):
    t = lines[n].strip().rstrip('∧').strip()
    facts.append((fact_key(t.replace("m'", "n'")), t))
    n += 1
gm2 = " ".join(l.strip() for l in lines[n:]).strip()
assert gm2.endswith(')')
gm2 = gm2[:-1]
gm2_args = gm2[len("GM2 B m'.mem "):]
T0, T1, D0, D1 = [g for g in top_split(gm2_args, ' ') if g]
keys = {k: t for k, t in facts}


def rhs(key):
    return strip_parens(top_split(keys[key], ' = ')[-1])


L0 = rhs('r9')
L1 = rhs('ra0')
assert L0.startswith('BitVec.ofNat 32 ') and L1.startswith('BitVec.ofNat 32 ')
L0, L1 = strip_parens(L0[len('BitVec.ofNat 32 '):]), strip_parens(L1[len('BitVec.ofNat 32 '):])
U1 = rhs('a380')
U2 = rhs('a400')


def fname(key):
    return f"{key[0] if key[0] != 'm' else 'mb'}1_{key[1:] if key[0] != 'm' else key[2:]}"


hyp_names = [g.split(' : ', 1)[0] for g in __import__('svchain').groups(hyp_text)]

ML = f"mlMain2 {T0} {T1} {D0} {D1} (max {L0} {L1})"
P = "accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8"
R2 = "accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8"
NZW = "(((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF)"

out = []
O = out.append
O("import C3BootProofs.Proofs.SvP256B")
O("import C3BootProofs.Proofs.SvZS")
O("import C3BootProofs.Proofs.SvZLoop2\n")
O("/-!\n# `sigstore::verify`: the P-256 check from the inverse to the inversion of `Z`\n")
O("From 0x1556 to the inversion of the sum's `Z` at 0x1B54: `sv_p256_tab`, then the main loop `ml2_main`,")
O("then `sv_zs`, which leaves `ZvInv` for the starting `zvLoop` state `p256Zv0`.\n-/\n")
O("namespace C3.RV32.Sv\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2\n\nset_option maxRecDepth 100000\n")
O("/-- The inversion of `Z`'s starting state: `f` is the prime `p`, `g` is `Z`, `d` is 0, `e` is `R²`, and")
O("591 divsteps are left. -/")
O("def p256Zv0 (M0 : Word → BitVec 8) (Z : Nat) : Iv :=")
O(f"  ⟨1, ({P} : Int), (Z : Int), 0, ({R2} : Int), 0x24F⟩\n")
O("set_option maxHeartbeats 64000000 in")
O("/-- **The P-256 check from the inverse to the inversion of `Z`**: from 0x1556 to 0x1B54, or a panic. -/")
O("theorem sv_p256_z " + binders)
O(hyp_text)
O("    (hid : CodeIn M0 (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData) :")
O("    Panics n0 ∨")
O(f"    (({SC}) ∧ ∃ stm, {ML} = some stm ∧ Pt2Lt stm.1 ∧")
O("      ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x1B54 (reg m') ∧")
O(f"        ZvInv B m' v r3 r4 out bp x26 {NZW} rv sv zv stm.1.1 stm.1.2.1")
O(f"          ({P}) ({R2}) W (p256Zv0 M0 stm.1.2.2)) := by")
pat = ["x1", "n1", "c1", "fR1", "s1", "ME1", "g1_3", "g1_4"] + [fname(k) for k, _ in facts] + ["G1"]
O("  rcases sv_p256_tab " + " ".join(hyp_names) + " with ⟨-, e⟩ | ⟨x1, n1, c1, fR1, s1, ME1, V1, g1_3, g1_4,")
O("      " + ", ".join(fname(k) for k, _ in facts) + ", G1⟩")
O("  · exact .inl e")
O(f"  have hL0 : {L0} ≤ 0x101 :=")
O(f"    wnafGo_len (by have := accV_lt n1.mem ({fa(0x380)}) 8; rw [a1_380] at this; exact this) _ _ _ (by decide) (by decide)")
O(f"  have hL1 : {L1} ≤ 0x101 :=")
O(f"    wnafGo_len (by have := accV_lt n1.mem ({fa(0x400)}) 8; rw [a1_400] at this; exact this) _ _ _ (by decide) (by decide)")
O("  rcases ml2_main F ME1 RS (F.dataIn fR1 hid (by decide) (by decide)) s1 r1_2 r1_9 r1_a0 r1_27 hL0 hL1 G1 with")
O("    ⟨-, hp⟩ | ⟨stm, hst, n2, c2, E2, fr2, K2, s2, X2, r2_22, -, -, A2, l2⟩")
O("  · exact .inl (Panics.of_steps c1 hp)")
O("  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)")

zs = Stage('SvZS', 'sv_zs')
ch = Chain(O)
ov = {p: p for p, _ in zs.params if p in ('F', 'hret', 'hO', 'M0', 'RS', 'EC0')}
ov.update({'E0': 'E2.C', 'V0': '(V1.keepL K2 (by decide))', 's0': 's2', 'fM': 'fR2', 'g0_2': 'X2.sp',
           'g0_18': '(X2.s2.trans r1_18)', 'g0_19': '(X2.s3.trans r1_19)', 'g0_20': 'X2.s4', 'g0_21': 'X2.s5',
           'g0_22': 'r2_22', 'g0_24': 'X2.s8', 'g0_26': '(X2.s10.trans r1_26)', 'g0_27': 'X2.s11',
           'a0_1480': '(congrArg Prod.fst A2)', 'a0_14a0': '(congrArg (fun p => p.2.1) A2)',
           'a0_14c0': '(congrArg (fun p => p.2.2) A2)'})
for p, _ in zs.params:
    if p not in ov:
        kind = {'w0_': 'w32', 'a0_': 'acc', 'b0_': 'b8'}[p[:3]]
        ov[p] = f"((K2.{kind} (by decide) (by decide)).trans {p[0] if p[0] != 'g' else 'r'}1_{p[3:]})"
for p, _ in zs.params:
    if p.startswith('w0_'):
        assert f"w{p[3:]}" in keys, p
ch.k = 2
args, names, pats, _ = ch.call(zs, ov, {'out': 'out', 'bp': 'bp', 'x26': 'x26', 'rv': 'rv', 'sv': 'sv', 'zv': 'zv',
                                       'X': 'stm.1.1', 'Y': 'stm.1.2.1', 'Z': 'stm.1.2.2'})
O("  rcases @sv_zs " + " ".join(args) + " with ⟨hn, -⟩ | ⟨" + ", ".join(pats) + "⟩")
O("  · exact absurd trivial hn")
t = ["E3", "IC0.sv F fR3", "EC0.sv F fR3", "UC0.sv F fR3", "V3", "r3_2", "by rw [r3_3, X2.g3]; exact g1_3",
     "by rw [r3_4, X2.g4]; exact g1_4", "r3_18", "r3_19", "r3_26", "r3_27", "w3_20", "by rw [w3_34, w3_38]; rfl",
     "w3_78", "by show 0x24F < 2 ^ 32; decide", "w3_460", "w3_464", "a3_420",
     "accV_dataR F fR3 (by decide) (by decide)", "a3_440", "accV_dataR F fR3 (by decide) (by decide)",
     "a3_2a0", "a3_2c0", "a3_2e0", "a3_15a8", "a3_15c8"]
for a, b in ((0x320, 0x340), (0x1380, 0x13A0), (0x1480, 0x14A0), (0x1020, 0x1040)):
    t += [f"by rw [b3_{b:x}, a3_{a:x}]; rfl", f"by rw [b3_{b:x}]; decide"]
t.append("fun e he => ?_")
O(f"  refine .inr ⟨x1, stm, hst, l2, n3, c1.trans (c2.trans c3), fR3, s3, " + ", ".join(t) + "⟩")
O("  simp only [ziWords, List.mem_cons, List.not_mem_nil, or_false] at he")
O("  rcases he with " + " | ".join(["rfl"] * len(ZIW)))
for e in ZIW:
    O(f"  · exact w3_{e:x}")
O("")
O("end C3.RV32.Sv")
open(BASE + 'SvP256C.lean', 'w').write("\n".join(out) + "\n")
