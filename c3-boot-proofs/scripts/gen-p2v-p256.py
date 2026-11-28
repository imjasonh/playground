#!/usr/bin/env python3
"""Writes the compositions of the generated `p256VerifyPrehash` stages:

- C3BootProofs/Proofs/P2vP256B.lean: from the end of the inversion of `s` at
  0x610 to the main loop at 0x998, `p2v_ive` through `p2v_ecw3`, composed
  with `svchain.Chain`.
- C3BootProofs/Proofs/P2vP256C.lean: from 0x610 to the inversion of `Z` at
  0xBEE: `p2v_p256_tab`, the main loop `ml2_main`, and `p2v_zs`.

Usage: python3 scripts/gen-p2v-p256.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import BASE, Chain, Stage, fact_key, groups, strip_parens, top_split  # noqa: E402

HDR = ("namespace C3.RV32.P2v\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv\n\n"
       "set_option maxRecDepth 100000\n")


def gen_tab():
    seq = [('P2vIvE', 'p2v_ive'), ('P2vEcD', 'p2v_ecd'), ('P2vEcT0a', 'p2v_ect0a'), ('P2vEcT0c', 'p2v_ect0c'),
           ('P2vEcT0b', 'p2v_ect0b'), ('P2vEcT1a', 'p2v_ect1a'), ('P2vEcT1c', 'p2v_ect1c'), ('P2vEcT1b', 'p2v_ect1b'),
           ('P2vEcW2', 'p2v_ecw2'), ('P2vEcW3', 'p2v_ecw3')]
    glob = ['EC0', 'UC0', 'UE0', 'N80', 'RS', 'PM0', 'WM0', 'PT0', 'WN0']
    stages = [Stage(*x) for x in seq]
    gty = {}
    for st in stages:
        for p, ty in st.params:
            if p in glob and p not in gty:
                gty[p] = ty

    proof = []
    P = proof.append
    ch = Chain(P)

    ive = stages[0]
    ov = {p: p for p, _ in ive.params if p in glob or p in ('F', 'hret', 'M0', 'fM')}
    ov.update({'E0': 'I.E', 'V0': 'I.V', 's0': 's', 'g0_2': 'I.sp', 'g0_8': 'I.g8', 'g0_9': 'I.g9',
               'g0_19': 'rfl', 'g0_21': 'rfl', 'g0_22': 'I.g22', 'g0_23': 'I.g23', 'g0_24': 'rfl',
               'g0_26': 'I.g26', 'g0_27': 'I.g27', 'hfs': 'I.lf', 'hds': 'I.ld'})
    fixed = {}
    for a, q in zip((0x120, 0x140, 0x160, 0x180, 0x1A0, 0x1C0), ('qx', 'qy', 'qz', 'rv', 'sv', 'zv')):
        ov[f'a0_{a:x}'] = f"I.a{a:x}"
        fixed[q] = q
    for p, _ in ive.params:
        if p.startswith('a0_') and p not in ov or p.startswith('b0_'):
            ov[p] = 'rfl'
    args, names, pats, sc_ive = ch.call(ive, ov, fixed)
    sc = " ∧ ".join(f"({x})" for x in sc_ive) + " ∧ True"
    P(f"  rcases {'@' if ch.at else ''}p2v_ive " + " ".join(args) + " with ⟨hn, e⟩ | ⟨" + ", ".join(names + pats) + "⟩")
    P("  · exact .inl ⟨hn, e⟩")

    p0 = p1 = None
    for st in stages[1:]:
        k = ch.k
        ov = {p: p for p, _ in st.params if p in glob or p in ('F', 'hret', 'M0')}
        ov.update({'E0': f'E{k}', 'V0': f'V{k}', 's0': f's{k}', 'fM': f'fR{k}'})
        fixed = {}
        if st.name == 'p2v_ect0a':
            pv = ch.prev
            p0 = f"({strip_parens(pv['a200'].rhs)}, {strip_parens(pv['a220'].rhs)}, {strip_parens(pv['a240'].rhs)})"
            p1 = f"({strip_parens(pv['a280'].rhs)}, {strip_parens(pv['a2a0'].rhs)}, {strip_parens(pv['a2c0'].rhs)})"
            fixed = {'P0': p0, 'P1': p1}
            for c in (0x200, 0x280, 0xFE4, 0x1064):
                ov[f'p0_{c:x}'] = f"(p2v_ptF_of a{k}_{c:x} a{k}_{c + 0x20:x} a{k}_{c + 0x40:x})"
        if 'hP0' in [p for p, _ in st.params]:
            ov.update({'hP0': 'hG', 'hP1': 'hQ'})
        args, names, pats, _ = ch.call(st, ov, fixed)
        assert not names
        P(f"  rcases {'@' if ch.at else ''}{st.name} " + " ".join(args) + " with ⟨hn, -⟩ | ⟨" + ", ".join(pats) + "⟩")
        P("  · exact absurd trivial hn")

    K = ch.k
    fin = ch.prev
    t0 = [0x300 + 0x60 * j for j in range(8)]
    t1 = [0x600 + 0x60 * j for j in range(8)]
    d0 = strip_parens(fin['mb10e8'].rhs)
    d1 = strip_parens(fin['mb11f0'].rhs)
    keep = []
    for key, f in fin.items():
        if key in ('STEPS', 'ST', 'E', 'V', 'FR', 'r3', 'r4', 'KL') or key[0] in 'pqml':
            continue
        t = f.text.replace(f"n{K}", "m'")
        if re.search(r"(?<![\w.'])n\d+(?![\w'])", t.replace("n0", "")):
            continue
        keep.append((key, t))

    def pname(key):
        return f"{key[0]}{K}_{key[1:]}"

    chain3 = ", ".join(f"r{k}_3" for k in range(K, 0, -1))
    chain4 = ", ".join(f"r{k}_4" for k in range(K, 0, -1))
    steps = f"c{K}"
    for k in range(K - 1, 0, -1):
        steps = f"c{k}.trans ({steps})"
    P(f"  refine .inr ⟨⟨x1_0, trivial⟩, n{K}, {steps}, fR{K}, s{K}, ME.fr F fR{K}, V{K},")
    P(f"    by rw [{chain3}]; exact I.g3, by rw [{chain4}]; exact I.g4,")
    P("    " + ", ".join(pname(k) for k, _ in keep) + ",")
    P(f"    ⟨fun j hj => ?_, fun j hj => ?_, fun j _ => ⟨tbl2_lt hG j, tbl2_lt hQ j⟩, mb{K}_10e8, mb{K}_11f0⟩⟩")
    for tab in (t0, t1):
        P("  · rcases j with " + " | ".join(["_"] * 8) + " | j")
        for d in tab:
            P(f"    · exact p{K}_{d:x}")
        P("    · omega")

    out = []
    O = out.append
    O("import C3BootProofs.Proofs.P2vIvLoop")
    O("import C3BootProofs.Proofs.P2vEcMl")
    for fn, _ in seq:
        O(f"import C3BootProofs.Proofs.{fn}")
    O("\n/-!\n# `p256VerifyPrehash`: the check from the inverse to the main loop\n")
    O("From 0x610, where the inversion of `s` ends, to the main loop at 0x998: `p2v_ive` normalizes the")
    O("inverse, `p2v_ecd` computes `u₁` and `u₂`, the `p2v_ect*` stages build the tables of odd multiples, and")
    O("`p2v_ecw2` and `p2v_ecw3` write the wNAF digits, which leaves what `ml2_main` takes.\n-/\n")
    O(HDR)
    O("theorem p2v_ptF_of {M : Word → BitVec 8} {B : Word} {c x y z : Nat}")
    O("    (hx : accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8 = x) (hy : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8 = y)")
    O("    (hz : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8 = z) : ptF M B c = (x, y, z) := by")
    O("  unfold ptF; rw [hx, hy, hz]\n")
    O("set_option maxHeartbeats 64000000 in")
    O("/-- **The check from the inverse to the main loop**: from 0x610 to 0x998, or a panic when the")
    O("inversion's `f` isn't 1. -/")
    O("theorem p2v_p256_tab {B r3 r4 : Word} {qx qy qz rv sv zv N : Nat} {v : Nat → Word} {n0 : Machine}")
    O("    {st : Iv} (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (s : St n0.mem P2V n0 0x610 (reg n0))")
    O("    (I : IvInv B n0 v r3 r4 qx qy qz rv sv zv N st)")
    O("    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)")
    O("    " + " ".join(f"({p} : {gty[p]})" for p in glob) + " (ME : MlEnv M0)")
    O(f"    (hG : Pt2Lt {p0})")
    O(f"    (hQ : Pt2Lt {p1}) :")
    O(f"    (¬ ({sc}) ∧ Panics n0) ∨")
    O(f"    (({sc}) ∧ ∃ m', Steps n0 m' ∧ (∀ x, P2vR B x → m'.mem x = M0 x) ∧ St m'.mem P2V m' 0x998 (reg m') ∧")
    O("      MlEnv m'.mem ∧ P2vSaves B m'.mem v ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧")
    for _, t in keep:
        O(f"      {t} ∧")
    O(f"      GM2 B m'.mem (tbl2 {p0}) (tbl2 {p1})")
    O(f"        ({d0})")
    O(f"        ({d1})) := by")
    out += proof
    O("")
    O("end C3.RV32.P2v")
    open(BASE + 'P2vP256B.lean', 'w').write("\n".join(out) + "\n")


def gen_z():
    src = open(BASE + 'P2vP256B.lean').read()
    i = src.index('theorem p2v_p256_tab ')
    tab = src[i:src.index(' := by\n', i)]
    hyp_text = tab[tab.index('\n') + 1:tab.index(' :\n    (¬')]
    binders = tab[len('theorem p2v_p256_tab '):tab.index('\n')]
    body = tab[tab.index(' :\n    (¬') + 3:]
    sc = body[len('    (¬ ('):body.index(') ∧ Panics n0) ∨')]
    lines = body.split('\n')
    k0 = next(n for n, l in enumerate(lines) if l.strip().startswith("MlEnv m'.mem"))
    facts = []
    n = k0 + 1
    while not lines[n].strip().startswith('GM2 '):
        t = lines[n].strip().rstrip('∧').strip()
        facts.append((fact_key(t.replace("m'", "n'")), t))
        n += 1
    gm2 = " ".join(l.strip() for l in lines[n:]).strip()
    assert gm2.endswith(')')
    gm2 = gm2[:-1]
    t0, t1, d0, d1 = [g for g in top_split(gm2[len("GM2 B m'.mem "):], ' ') if g]
    keys = {k: t for k, t in facts}

    def rhs(key):
        return strip_parens(top_split(keys[key], ' = ')[-1])

    l0, l1 = rhs('r9'), rhs('ra0')
    assert l0.startswith('BitVec.ofNat 32 ') and l1.startswith('BitVec.ofNat 32 ')
    l0, l1 = strip_parens(l0[len('BitVec.ofNat 32 '):]), strip_parens(l1[len('BitVec.ofNat 32 '):])

    def fname(key):
        return f"{key[0]}1_{key[1:]}"

    hyp_names = [g.split(' : ', 1)[0] for g in groups(hyp_text)]
    ml = f"mlMain2 {t0} {t1} {d0} {d1} (max {l0} {l1})"
    pp = "accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8"
    nzw = "(((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF)"

    out = []
    O = out.append
    O("import C3BootProofs.Proofs.P2vP256B")
    O("import C3BootProofs.Proofs.P2vEcMl3")
    O("import C3BootProofs.Proofs.P2vZS")
    O("import C3BootProofs.Proofs.P2vZLoop\n")
    O("/-!\n# `p256VerifyPrehash`: the check from the inverse to the inversion of `Z`\n")
    O("From 0x610 to the inversion of the sum's `Z` at 0xBEE: `p2v_p256_tab`, then the main loop `ml2_main`,")
    O("then `p2v_zs`, which leaves `ZvInv` for the starting `zvLoop` state `p256Zv0`.\n-/\n")
    O(HDR)
    O("set_option maxHeartbeats 64000000 in")
    O("/-- **The check from the inverse to the inversion of `Z`**: from 0x610 to 0xBEE, or a panic. -/")
    O("theorem p2v_p256_z " + binders)
    O(hyp_text)
    O("    (IC0 : P2vIvCode M0) (hid : CodeIn M0 (BitVec.ofNat 32 (img% p256IdentityAddress)) p256IdentityData) :")
    O("    Panics n0 ∨")
    O(f"    (({sc}) ∧ ∃ stm, {ml} = some stm ∧ Pt2Lt stm.1 ∧")
    O("      ∃ m', Steps n0 m' ∧ (∀ x, P2vR B x → m'.mem x = M0 x) ∧ St m'.mem P2V m' 0xBEE (reg m') ∧")
    O(f"        ZvInv B m' v r3 r4 {nzw} rv stm.1.1 stm.1.2.1")
    O(f"          ({pp}) (p256Zv0 M0 stm.1.2.2)) := by")
    O("  rcases p2v_p256_tab " + " ".join(hyp_names) + " with ⟨-, e⟩ | ⟨x1, n1, c1, fR1, s1, ME1, V1, g1_3, g1_4,")
    O("      " + ", ".join(fname(k) for k, _ in facts) + ", G1⟩")
    O("  · exact .inl e")
    O(f"  have hL0 : {l0} ≤ 0x101 :=")
    O(f"    wnafGo_len (by have := accV_lt n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8; rw [a1_260] at this; exact this) _ _ _ (by decide) (by decide)")
    O(f"  have hL1 : {l1} ≤ 0x101 :=")
    O(f"    wnafGo_len (by have := accV_lt n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8; rw [a1_2e0] at this; exact this) _ _ _ (by decide) (by decide)")
    O("  rcases ml2_main F ME1 RS (F.dataIn fR1 hid (by decide) (by decide)) s1 r1_2 r1_9 r1_a0 hL0 hL1 G1 with")
    O("    ⟨-, hp⟩ | ⟨stm, hst, n2, c2, ME2, fr2, K2, s2, r2_2, r2_3, r2_4, -, -, A2, l2⟩")
    O("  · exact .inl (Panics.of_steps c1 hp)")
    O("  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)")
    O("  rcases p2v_zs (rv := rv) F ME2.C (V1.keepL K2 (by decide)) hret s2 M0 fR2 r2_2")
    O("      ((K2.acc (by decide) (by decide)).trans a1_180) (congrArg Prod.fst A2) (congrArg (fun p => p.2.1) A2)")
    O("      (congrArg (fun p => p.2.2) A2) RS EC0 with")
    O("    ⟨hn, -⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_a0, r3_a4, r3_24, w3_10, w3_40, b3_220, b3_920, b3_fa0,")
    O("      b3_1004, -, -, -, -, a3_180, a3_200, a3_900, a3_980, -, a3_f80, a3_fe4, a3_1338, a3_1358, -, -⟩")
    O("  · exact absurd trivial hn")
    O("  refine .inr ⟨x1, stm, hst, l2, n3, c1.trans (c2.trans c3), fR3, s3, E3, IC0.p2v F fR3, UC0.p2v F fR3, V3, r3_2,")
    O("    by rw [r3_3, r2_3, g1_3], by rw [r3_4, r2_4, g1_4], r3_a0, r3_a4, by rw [w3_40, r3_24]; rfl,")
    O("    by show 0x24F < 2 ^ 32; decide, w3_10, accV_dataR F fR3 (by decide) (by decide), a3_980, a3_180,")
    O("    a3_1338, a3_1358, by rw [b3_fa0, a3_f80]; rfl, by rw [b3_fa0]; decide, by rw [b3_920, a3_900]; rfl,")
    O("    by rw [b3_920]; decide, by rw [b3_220, a3_200]; rfl, by rw [b3_220]; decide,")
    O("    by rw [b3_1004, a3_fe4]; rfl, by rw [b3_1004]; decide⟩")
    O("")
    O("end C3.RV32.P2v")
    open(BASE + 'P2vP256C.lean', 'w').write("\n".join(out) + "\n")


gen_tab()
gen_z()
