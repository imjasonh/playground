#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/SvP256All.lean: the whole P-256 check in
`sigstore::verify`, from 0xFBA to 0x2034, joined from the segments
`sv_p256_inv`, `sv_p256_z`, and `sv_p256_end` and the loops `iv_loop`,
`iv_exit`, and `zv_loop`.

The segments describe the inverses that leave the two inversions by their
sign bytes and limbs in the frame. This theorem names those as witnesses
that `sgnVal` ties to the model's state, so its statement doesn't mention
any intermediate machine.

Usage: python3 scripts/gen-sv-p256.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import BASE, groups, subst, top_split  # noqa: E402


def fa(e):
    return f"B + 0x21A0 + BitVec.ofNat 32 0x{e:X}"


def theorem(fn, name):
    s = open(BASE + fn + '.lean').read()
    i = s.index(f'theorem {name} ')
    return s[i:s.index(' := by\n', i)]


def hyps(st):
    """The explicit hypotheses' names and the text of the hypothesis list."""
    end = st.index(' :\n    ') if ' :\n    ' in st else st.index('\n    :\n')
    text = st[st.index('\n') + 1:end]
    return [g.split(' : ', 1)[0].strip() for g in groups(text)], text


def witnesses(text, d, f, dv, fv, names):
    """Replaces the inversion's frame reads in `text` with witness names."""
    sd, sf, D, F = names
    reps = [(f"((n0.mem ({fa(d)}))).toNat", sd), (f"(((n0.mem ({fa(f)}))).zeroExtend 32).toNat", sf),
            (f"((accV n0.mem ({fa(dv)}) 8))", D), (f"(accV n0.mem ({fa(fv)}) 8)", F)]
    for a, b in reps:
        text = text.replace(a, b)
    return text


A = theorem('SvP256A', 'sv_p256_inv')
C = theorem('SvP256C', 'sv_p256_z')
D = theorem('SvP256D', 'sv_p256_end')
a_names, a_text = hyps(A)
a_binders = A[len('theorem sv_p256_inv '):A.index('\n')]
a_body = A[A.index(' :\n    (¬') + 3:]
SC12 = a_body[len('    (¬ ('):a_body.index(') ∧ SvErrRet B out v n0) ∨')]

N = "accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8"
PP = "accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8"
R2 = "accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8"
QV = {'qx': "gsVal M0 x21 1 * 2 ^ 256 % p256", 'qy': "gsVal M0 x21 0x21 * 2 ^ 256 % p256",
      'qz': "accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8", 'rv': "beNat (b32 er)", 'sv': "beNat (b32 es)",
      'zv': f"beNat (memBytes M0 (memLoad32 n0.mem ({fa(0x84)})) 32) % C3.p256.n", 'N': N,
      'W': "(fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))",
      'r3': "reg n0 (3 : Fin 32)", 'r4': "reg n0 (4 : Fin 32)"}

# sv_p256_z's success condition and main-loop result, at the inversion of s's exit.
c_body = C[C.index(' :\n    Panics n0 ∨') + len(' :\n    Panics n0 ∨\n'):]
SCI = c_body[len('    (('):c_body.index(') ∧ ∃ stm, ')]
ML = c_body[c_body.index('∃ stm, ') + len('∃ stm, '):c_body.index(' = some stm ∧')]
WS = ('σd', 'σf', 'Dv', 'Fv')
SCI = subst(witnesses(SCI, 0x1040, 0x13A0, 0x1020, 0x1380, WS), QV)
ML = subst(witnesses(ML, 0x1040, 0x13A0, 0x1020, 0x1380, WS), QV)
assert 'n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1' not in SCI + ML

# sv_p256_end's hypotheses, success condition, and conclusion, at the inversion of Z's end.
DEV = dict(QV)
DEV.update({'nzw': "(((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF)", 'X': 'stm.1.1',
            'Y': 'stm.1.2.1', 'P': PP, 'R2': R2, 'st': 'p256Sz M0 stm.1.2.2'})
WZ = ('τd', 'τf', 'Dz', 'Fz')
d_names, d_text = hyps(D)
hzi = [g for g in groups(d_text) if g.startswith('hzi : ')][0][len('hzi : '):]
hidR = [g for g in groups(d_text) if g.startswith('hid : ')][0][len('hid : '):]
hzi = subst(witnesses(hzi, 0x14A0, 0x340, 0x1480, 0x320, WZ), DEV)
d_body = D[D.index('\n    :\n') + len('\n    :\n'):]
SCZ = d_body[len('    (¬ ('):d_body.index(') ∧ SvErrRet B out v n0) ∨')]
SCZ = subst(witnesses(SCZ, 0x14A0, 0x340, 0x1480, 0x320, WZ), DEV)
lines = d_body.split('\n')
k0 = next(i for i, l in enumerate(lines) if l.strip().startswith("SvCode m'.mem ∧ SvSaves"))
dfacts = [l.strip().rstrip('∧').strip() for l in lines[k0 + 1:]]
dfacts[-1] = dfacts[-1][:-1].rstrip() if dfacts[-1].endswith(')') else dfacts[-1]
keep = [(i, subst(t, DEV)) for i, t in enumerate(dfacts) if 'n0.mem' not in t]
for _, t in keep:
    assert not re.search(r"(?<![\w.'])(σd|σf|Dv|Fv|τd|τf|Dz|Fz)(?![\w'])", t)
HZI = (f"∀ Z τd τf Dz Fz, τd ≤ 1 → τf ≤ 1 → sgnVal τf Fz = (p256Sz M0 Z).f → sgnVal τd Dz = (p256Sz M0 Z).d →\n"
       f"        {hzi.replace('stm.1.2.2', 'Z')}")

c_names, _ = hyps(C)
GLOB_C = [n for n in c_names if n not in ('F', 'hret', 'hO', 's', 'I', 'M0', 'fM', 'hid', 'hG', 'hQ')]
GLOB_D = [n for n in d_names if n not in ('F', 'hret', 'hO', 's', 'I', 'h0', 'M0', 'fM', 'hnz', 'hX', 'hY', 'hid', 'hzi')]
c_hyps = {g.split(' : ', 1)[0].strip(): g.split(' : ', 1)[1] for g in groups(C[C.index('\n') + 1:C.index(' :\n    Panics')])}
d_hyps = {g.split(' : ', 1)[0].strip(): g.split(' : ', 1)[1] for g in groups(d_text)}
extra = []
for n in GLOB_C + GLOB_D:
    if n in a_names or n in [e[0] for e in extra]:
        continue
    ty = c_hyps.get(n) or d_hyps.get(n)
    extra.append((n, subst(ty, QV)))

out = []
O = out.append
O("import C3BootProofs.Proofs.SvP256D")
O("import C3BootProofs.Image.BootloaderData5\n")
O("/-!\n# `sigstore::verify`: the whole P-256 check\n")
O("From 0xFBA to 0x2034: the range checks and key decode, the inversion of `s` (`ivLoop8`), the tables and")
O("wNAF digits, the main loop (`mlMain2`), the inversion of the sum's `Z` (`zvLoop`), and the comparison with")
O("`r`. The inverses that leave the two inversions are named by witnesses that `sgnVal` ties to the models'")
O("states.\n-/\n")
O("namespace C3.RV32.Sv\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd\n")
O("set_option maxRecDepth 100000\n")
O("/-- The inversion of `s`'s state after its 10 batches. -/")
O("def p256Sf (M0 : Word → BitVec 8) (es : Bytes) : Iv :=")
O(f"  ivLoop8 ({N}) 10 (p256Iv0 M0 es)\n")
O("/-- The inversion of `Z`'s state after its 10 batches. -/")
O("def p256Sz (M0 : Word → BitVec 8) (Z : Nat) : Iv :=")
O(f"  zvLoop ({PP}) 10 (p256Zv0 M0 Z)\n")
O("theorem p256_zx (b : BitVec 8) : (b.zeroExtend 32).toNat = b.toNat := by")
O("  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]\n")
O("theorem p256_nzw (Z : Nat) : (((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) = 0 ∨")
O("    (((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) = 1 := by")
O("  by_cases h : Z = 0")
O("  · rw [ite_eq_left h]; exact .inl (by decide)")
O("  · rw [ite_eq_right h]; exact .inr (by decide)\n")
O("set_option maxHeartbeats 64000000 in")
O("/-- **The P-256 check in `sigstore::verify`**: from 0xFBA to 0x2034 when the signature is valid by the")
O("check's arithmetic, an error return when it isn't, or a panic when the inversion of `s` doesn't end with")
O("`f = ±1` or the main loop meets an invalid wNAF digit. -/")
O("theorem sv_p256 " + a_binders)
O(a_text)
O("    " + " ".join(f"({n} : {t})" for n, t in extra))
O(f"    (hidC : {subst(c_hyps['hid'], QV)})")
O("    (GD : CodeIn M0 (BitVec.ofNat 32 p256GMontAddress) p256GMontData)")
O("    (OD : CodeIn M0 (BitVec.ofNat 32 p256MontOneAddress) p256MontOneData)")
O("    (AD : CodeIn M0 (BitVec.ofNat 32 p256AffineIdXAddress) p256AffineIdXData)")
O(f"    (hzi : {HZI}) :")
O(f"    (¬ ({SC12}) ∧ SvErrRet B out v n0) ∨ Panics n0 ∨")
O(f"    (({SC12}) ∧")
O("      ∃ σd σf Dv Fv, σd ≤ 1 ∧ σf ≤ 1 ∧ sgnVal σf Fv = (p256Sf M0 es).f ∧ sgnVal σd Dv = (p256Sf M0 es).d ∧")
O(f"      ({SCI}) ∧ ∃ stm, {ML} = some stm ∧")
O("      ∃ τd τf Dz Fz, τd ≤ 1 ∧ τf ≤ 1 ∧ sgnVal τf Fz = (p256Sz M0 stm.1.2.2).f ∧ sgnVal τd Dz = (p256Sz M0 stm.1.2.2).d ∧")
O(f"      ((¬ ({SCZ}) ∧ SvErrRet B out v n0) ∨")
O(f"       (({SCZ}) ∧ ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x2034 (reg m') ∧")
O("        SvCode m'.mem ∧ SvSaves B m'.mem v ∧ reg m' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧")
O("        reg m' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
for i, (_, t) in enumerate(keep):
    O(f"        {t}" + (" ∧" if i + 1 < len(keep) else "))) := by"))
O(f"  have hN : 0 < {N} := by")
O("    show 0 < accV M0 BYO 8; rw [BY0.ord]; decide")
O(f"  have hP : 0 < {PP} := by")
O("    have h := code_accV D0.params 0 8 (by decide)")
O("    rw [add_ofNat_zero] at h")
O("    show 0 < accV M0 P2N 8; rw [h]; decide")
O(f"  have hG : {subst(c_hyps['hG'], QV)} := by")
O("    have g0 : accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 = dataVal p256GMontData 0 8 :=")
O("      code_accV GD 0 8 (by decide)")
O("    have g1 : accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 = dataVal p256GMontData 0x20 8 :=")
O("      code_accV GD 0x20 8 (by decide)")
O("    have g2 : accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 = dataVal p256GMontData 0x40 8 :=")
O("      code_accV GD 0x40 8 (by decide)")
O("    rw [g0, g1, g2]; exact ⟨by decide, by decide, by decide⟩")
O(f"  have hQ : {subst(c_hyps['hQ'], QV)} := by")
O("    have z : accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress) + BitVec.ofNat 32 0) 8 = dataVal p256MontOneData 0 8 :=")
O("      code_accV OD 0 8 (by decide)")
O("    rw [add_ofNat_zero] at z")
O("    exact ⟨Nat.mod_lt _ p256_pos, Nat.mod_lt _ p256_pos, by show accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 < p256; rw [z]; decide⟩")
O(f"  have hidR : {hidR} := by")
O("    have z : accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress) + BitVec.ofNat 32 0) 8 = dataVal p256AffineIdXData 0 8 :=")
O("      code_accV AD 0 8 (by decide)")
O("    rw [add_ofNat_zero] at z")
O("    rw [z]; decide")
O("  rcases sv_p256_inv " + " ".join(a_names) + " with ⟨hn, e⟩ | ⟨h1, h2, m1, c1, fr1, s1, I1⟩")
O("  · exact .inl ⟨hn, e⟩")
O("  obtain ⟨m2, c2, fr2, s2, I2⟩ := iv_loop F hret hO hN 10 s1 I1")
O("  obtain ⟨m3, c3, fr3, s3, I3⟩ := iv_exit F hret hO hN s2 I2")
O("    (ivLoop8_stop _ 10 _ (by show 0x24F ≤ 62 * 10; decide))")
O("  have fM3 : ∀ x, SvR B x → m3.mem x = M0 x := fun x hx => by rw [fr3 x hx, fr2 x hx, fr1 x hx]")
c_args = []
for n in c_names:
    c_args.append({'s': 's3', 'I': 'I3', 'fM': 'fM3', 'hid': 'hidC'}.get(n, n))
O("  rcases sv_p256_z " + " ".join(c_args) + " with e | ⟨x3, stm, hst, l3, m4, c4, fr4, s4, I4⟩")
O("  · exact .inr (.inl (Panics.of_steps (c1.trans (c2.trans c3)) e))")
O("  obtain ⟨m5, c5, fr5, s5, I5⟩ := zv_loop F hret hO hP 10 s4 I4")
O("  have fM5 : ∀ x, SvR B x → m5.mem x = M0 x := fun x hx => by rw [fr5 x hx, fr4 x hx]")
O("  have W3 : ((m3.mem (" + fa(0x13A0) + ")).zeroExtend 32).toNat ≤ 1 := by rw [p256_zx]; exact I3.lf")
O("  have V3 : sgnVal ((m3.mem (" + fa(0x13A0) + ")).zeroExtend 32).toNat (accV m3.mem (" + fa(0x1380)
  + ") 8) = (p256Sf M0 es).f := by rw [p256_zx]; exact I3.vf")
O("  have W5 : ((m5.mem (" + fa(0x340) + ")).zeroExtend 32).toNat ≤ 1 := by rw [p256_zx]; exact I5.lf")
O("  have V5 : sgnVal ((m5.mem (" + fa(0x340) + ")).zeroExtend 32).toNat (accV m5.mem (" + fa(0x320)
  + ") 8) = (p256Sz M0 stm.1.2.2).f := by rw [p256_zx]; exact I5.vf")
d_args = []
for n in d_names:
    d_args.append({'s': 's5', 'I': 'I5', 'fM': 'fM5', 'h0': '(zvLoop_rem _ 10 _ (by show 0x24F ≤ 62 * 10; decide))',
                   'hnz': '(p256_nzw _)', 'hX': 'l3.1', 'hY': 'l3.2.1', 'hid': 'hidR',
                   'hzi': '(hzi _ _ _ _ _ I5.ld W5 V5 I5.vd)'}.get(n, n))
pat = ", ".join(f"d6_{i}" for i in range(len(dfacts)))
O("  rcases sv_p256_end " + " ".join(d_args) + " with ⟨hn, e⟩ | ⟨h6, m6, c6, fr6, s6, E6, V6, g6_3, g6_4,")
O(f"      {pat}⟩")
WIT = "_, _, _, _, I3.ld, W3, V3, I3.vd, x3, stm, hst, _, _, _, _, I5.ld, W5, V5, I5.vd"
O(f"  · exact .inr (.inr ⟨⟨h1, h2⟩, {WIT}, .inl ⟨hn, SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans c5))))")
O("      I5.g3 I5.g4 (fun x hx => (fM5 x hx).trans (fM x hx).symm) e⟩⟩)")
O(f"  · exact .inr (.inr ⟨⟨h1, h2⟩, {WIT}, .inr ⟨h6, m6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))),")
O("      fr6, s6, E6, V6, g6_3, g6_4,")
O("      " + ", ".join(f"d6_{i}" for i, _ in keep) + "⟩⟩)")
O("")
O("end C3.RV32.Sv")
open(BASE + 'SvP256All.lean', 'w').write("\n".join(out) + "\n")
