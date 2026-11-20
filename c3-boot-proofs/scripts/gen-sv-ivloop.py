#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/SvIvLoop.lean: the batches of the inversion of
`s` in `sigstore::verify`, composed from the generated stages `sv_ivhc`,
`sv_iva`, `sv_ivb`, and `sv_ivhx`, the scan `ec_scan`, and the divstep loop
`ec_loop`.

The stages take about a hundred hypotheses each, so this reads their
statements and writes the arguments and the names of their conclusions.

Usage: python3 scripts/gen-sv-ivloop.py   (from c3-boot-proofs/)
"""

import re

BASE = 'C3BootProofs/Proofs/'


def sig(fn, name):
    s = open(BASE + fn + '.lean').read()
    i = s.index(f'theorem {name} ')
    j = s.index(':= by', i)
    st = s[i:j]
    k = st.index('(¬')
    ph = re.sub(r'\{[^}]*\}', '', st[:k])
    pn = [p for p in re.findall(r'\(([A-Za-z0-9_]+) :', ph) if not p.isdigit()]
    c2 = st[k:][st[k:].index("∃ n', "):]
    lines = [l.strip().rstrip('∧').strip() for l in c2.split('\n') if l.strip()]
    return pn, [cname(l) for l in lines]


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
IVWS = set(IVW)
QA = [0x240, 0x260, 0x280, 0x2A0, 0x2C0, 0x2E0]
QN = ['qx', 'qy', 'qz', 'rv', 'sv', 'zv']
SG = [("f", 0x1380, 0x13A0), ("g", 0x1480, 0x14A0), ("d", 0x1020, 0x1040), ("e", 0x420, 0x440)]
PARAMS = "B v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W"
INV = "IvInv B {m} v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W"
IMPL = ("{B r3 r4 out bp s5v x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word}")

out = []
E = out.append
E("import C3BootProofs.Proofs.SvZLoop2")
E("import C3BootProofs.Proofs.SvIvHc")
E("import C3BootProofs.Proofs.SvIvHx")
E("import C3BootProofs.Proofs.SvIvA")
E("import C3BootProofs.Proofs.SvIvB")
E("import C3BootProofs.Proofs.SvEcDs\n")
E("/-!\n# `sigstore::verify`: the batches of the inversion of `s`\n")
E("From the inversion's head at 0x1328 back to it: `sv_ivhc` starts a batch, `ec_scan` looks for a nonzero limb")
E("of `g`, `sv_iva` loads the low words, `ec_loop` runs the divsteps, and `sv_ivb` applies their matrix, which")
E("is one `ivStep8`. `iv_loop` runs batches as `ivLoop8` does, and `iv_exit` leaves for 0x1556 when no steps")
E("are left or `g` is zero.\n-/\n")
E("namespace C3.RV32.Sv\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv\n\nset_option maxRecDepth 100000\n")
E("/-- `-n⁻¹ mod 2⁶⁴` for the order `n` of P-256, which the inversion of `s` keeps at 0x70 and 0x60. -/")
E("def ivMI : Nat := 0x332E375511FF43B1\n")
E("/-- One batch of the inversion of `s` modulo `N`. -/")
E("def ivStep8 (N : Nat) (s : Iv) : Iv :=")
E("  let n := min s.rem 62")
E("  let t := dsIter n ⟨s.δ, lowestI s.f, lowestI s.g, 1, 0, 0, 1⟩")
E("  ⟨t.δ, fgUpd8 s.f s.g (i64Val t.u) (i64Val t.v) n, fgUpd8 s.f s.g (i64Val t.q) (i64Val t.r) n,")
E("    deUpd8 s.d s.e (i64Val t.u) (i64Val t.v) ivMI n N, deUpd8 s.d s.e (i64Val t.q) (i64Val t.r) ivMI n N, s.rem - n⟩\n")
E("/-- Batches until no steps are left or `g` is zero, with `k` batches at most. -/")
E("def ivLoop8 (N : Nat) : Nat → Iv → Iv")
E("  | 0, s => s")
E("  | k + 1, s => if s.rem = 0 ∨ s.g = 0 then s else ivLoop8 N k (ivStep8 N s)\n")
E("theorem ivLoop8_done (N : Nat) : ∀ k (s : Iv), s.rem = 0 ∨ s.g = 0 → ivLoop8 N k s = s")
E("  | 0, _, _ => rfl")
E("  | _ + 1, s, h => by rw [ivLoop8, ite_eq_left h]\n")
E("theorem ivLoop8_stop (N : Nat) : ∀ k (s : Iv), s.rem ≤ 62 * k →")
E("    (ivLoop8 N k s).rem = 0 ∨ (ivLoop8 N k s).g = 0")
E("  | 0, s, h => by rw [ivLoop8]; omega")
E("  | k + 1, s, h => by")
E("    rw [ivLoop8]")
E("    by_cases h0 : s.rem = 0 ∨ s.g = 0")
E("    · rw [ite_eq_left h0]; exact h0")
E("    · rw [ite_eq_right h0]")
E("      exact ivLoop8_stop N k _ (by simp only [ivStep8]; omega)\n")
E("/-- The frame words that the inversion of `s` leaves alone. -/")
E("def ivWords : List Nat := [" + ", ".join(f"0x{e:X}" for e in IVW) + "]\n")
E("/-- What holds at the inversion's head 0x1328 for the state `st`. -/")
E("structure IvInv (B : Word) (m : Machine) (v : Nat → Word) (r3 r4 out bp s5v x26 : Word) (qx qy qz rv sv zv N : Nat)")
E("    (W : Nat → Word) (st : Iv) : Prop where")
inv = [("E", "SvCode m.mem"), ("IC", "SvIvCode m.mem"), ("EC", "SvEcCode m.mem"), ("UC", "SvUpCode m.mem"),
       ("V", "SvSaves B m.mem v"), ("sp", "reg m sp = B + 0x21A0"), ("g3", "reg m (3 : Fin 32) = r3"),
       ("g4", "reg m (4 : Fin 32) = r4"), ("g18", "reg m (18 : Fin 32) = out"), ("g19", "reg m (19 : Fin 32) = bp"),
       ("g21", "reg m (21 : Fin 32) = s5v"), ("g24", "reg m (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268"),
       ("g26", "reg m (26 : Fin 32) = x26"), ("g27", f"reg m (27 : Fin 32) = {fa(0xA20)}"),
       ("wd", "W64 (reg m (23 : Fin 32)) (reg m (25 : Fin 32)) = st.δ"),
       ("wr", f"memLoad32 m.mem ({fa(0x78)}) = BitVec.ofNat 32 st.rem"), ("rem", "st.rem < 2 ^ 32"),
       ("w60", f"memLoad32 m.mem ({fa(0x60)}) = BitVec.ofNat 32 0x332E3755"),
       ("w70", f"memLoad32 m.mem ({fa(0x70)}) = BitVec.ofNat 32 0x11FF43B1"),
       ("aN", "accV m.mem (BitVec.ofNat 32 0x3FCC4268) 8 = N")]
for a, q in zip(QA, QN):
    inv.append((f"a{a:x}", f"accV m.mem ({fa(a)}) 8 = {q}"))
for nm, a, b in SG:
    inv.append((f"v{nm}", f"sgnVal (m.mem ({fa(b)})).toNat (accV m.mem ({fa(a)}) 8) = st.{nm}"))
    inv.append((f"l{nm}", f"(m.mem ({fa(b)})).toNat ≤ 1"))
inv.append(("ww", "∀ e, e ∈ ivWords → memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 e) = W e"))
for n, t in inv:
    E(f"  {n} : {t}")
E("")
REGS = {"sp": 2, "g3": 3, "g4": 4, "g18": 18, "g19": 19, "g21": 21, "g24": 24, "g26": 26, "g27": 27}
E("theorem IvInv.of " + IMPL + " {m m' : Machine} {st : Iv}")
E(f"    (I : {INV.format(m='m')} st) (hm : m'.mem = m.mem)")
E("    (hr : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 23, 24, 25, 26, 27] → reg m' q = reg m q) :")
E(f"    {INV.format(m=chr(109) + chr(39))} st := by")
terms = []
for n, t in inv:
    if n in REGS:
        terms.append(f"by rw [hr {REGS[n]} (by decide)]; exact I.{n}")
    elif n == "wd":
        terms.append("by rw [hr 23 (by decide), hr 25 (by decide)]; exact I.wd")
    elif n == "rem":
        terms.append("I.rem")
    elif n == "ww":
        terms.append("fun e he => by rw [hm]; exact I.ww e he")
    else:
        terms.append(f"by rw [hm]; exact I.{n}")
E("  exact ⟨" + ",\n    ".join(terms) + "⟩\n")
E("theorem iv_keep74 {B : Word} {M M' : Word → BitVec 8} (F : Fr B 0x3830)")
E(f"    (h : ∀ x, Sep ({fa(0x74)}) 4 x 1 → M' x = M x) : SvKeepL B M M' [(0x74, 4)] :=")
E("  fun e he hL => h _ (by")
E("    have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)")
E("    have h1 := hL _ (List.mem_singleton_self _)")
E("    dsimp only at h1")
E("    have hS : (B + 0x21A0).toNat + 0x1690 ≤ 2 ^ 32 := by have := FS.hi; omega")
E("    exact zfr_sep (a := BitVec.ofNat 32 0x74) (b := BitVec.ofNat 32 e) hS (by decide) (by decide) (by decide)")
E("      (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega))\n")
E("theorem iv_s0 {B : Word} {M : Word → BitVec 8} {f : Fin 32 → Word} {δ : Nat} {F G : Int} {fs gs : BitVec 8}")
E("    {fv gv : Nat} (hfs : fs.toNat ≤ 1) (hgs : gs.toNat ≤ 1) (vf : sgnVal fs.toNat fv = F)")
E("    (vg : sgnVal gs.toNat gv = G) (wd : W64 (f 23) (f 25) = δ) (r2 : f 2 = B + 0x21A0)")
E("    (r22 : f 22 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32))")
E(f"    (w74 : memLoad32 M ({fa(0x74)}) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32))")
E("    (r10 : f 10 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32))")
E("    (r11 : f 11 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32))")
E("    (r14 : f 14 = BitVec.ofNat 32 0x1) (r5 : f 5 = BitVec.ofNat 32 0x0) (r31 : f 31 = BitVec.ofNat 32 0x0)")
E("    (r17 : f 17 = BitVec.ofNat 32 0x0) (r8 : f 8 = BitVec.ofNat 32 0x0) (r29 : f 29 = BitVec.ofNat 32 0x0)")
E("    (r12 : f 12 = BitVec.ofNat 32 0x1) (r6 : f 6 = BitVec.ofNat 32 0x0) :")
E("    EcDsRegs M f ⟨δ, lowestI F, lowestI G, 1, 0, 0, 1⟩ := by")
E("  refine ⟨wd, ?_, ?_, ?_, ?_, ?_, ?_⟩")
E(f"  · rw [r22, r2]; show W64 _ (memLoad32 M ({fa(0x74)})) = _")
E("    rw [w74, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hfs vf]")
E("  · rw [r10, r11, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hgs vg]")
E("  · rw [r14, r5]; rfl")
E("  · rw [r31, r17]; rfl")
E("  · rw [r8, r29]; rfl")
E("  · rw [r12, r6]; rfl\n")
HEAD = "\n".join(out)


def head_arg(p, I, s, extra):
    """An argument of `sv_ivhc`, `sv_ivhx`, or `sv_iva` at a head state with the invariant `I`."""
    if p in ('F', 'hret', 'hO'):
        return p
    m = {'E0': f'{I}.E', 'V0': f'{I}.V', 's0': s, 'fM': '(fun _ _ => rfl)', 'g0_2': f'{I}.sp',
         'g0_18': f'{I}.g18', 'g0_19': f'{I}.g19', 'g0_21': f'{I}.g21', 'g0_23': 'rfl', 'g0_24': f'{I}.g24',
         'g0_25': 'rfl', 'g0_26': f'{I}.g26', 'g0_27': f'{I}.g27', 'w0_5c': 'rfl', 'w0_60': f'{I}.w60',
         'w0_70': f'{I}.w70', 'w0_78': f'{I}.wr', 'IC0': f'{I}.IC', 'EC0': f'{I}.EC', 'hfs': f'{I}.lf',
         'hgs': f'{I}.lg'}
    m.update(extra)
    if p in m:
        return m[p]
    if p.startswith('w0_') and int(p[3:], 16) in IVWS:
        return f"({I}.ww 0x{int(p[3:], 16):X} (by decide))"
    if p.startswith('a0_'):
        a = int(p[3:], 16)
        return f"{I}.a{a:x}" if a in QA else 'rfl'
    if p.startswith('b0_'):
        return 'rfl'
    raise ValueError(p)


def ww_cases(k):
    o = ["  simp only [ivWords, List.mem_cons, List.not_mem_nil, or_false] at he",
         "  rcases he with " + " | ".join(["rfl"] * len(IVW))]
    o += [f"  · exact w{k}_{e:x}" for e in IVW]
    return o


def head_inv(k, I, M):
    """The invariant at the end of `sv_ivhc` or `sv_ivhx` (stage `k`), from the invariant `I` at its start."""
    t = [f"E{k}", f"{I}.IC.sv F fR{k}", f"{I}.EC.sv F fR{k}", f"{I}.UC.sv F fR{k}", f"V{k}", f"r{k}_2",
         f"by rw [r{k}_3]; exact {I}.g3", f"by rw [r{k}_4]; exact {I}.g4", f"r{k}_18", f"r{k}_19", f"r{k}_21",
         f"r{k}_24", f"r{k}_26", f"r{k}_27", f"by rw [r{k}_23, r{k}_25]; exact {I}.wd", f"w{k}_78", f"{I}.rem",
         f"w{k}_60", f"w{k}_70", f"by rw [accV_dataR F fR{k} (by decide) (by decide)]; exact {I}.aN"]
    t += [f"a{k}_{a:x}" for a in QA]
    for nm, a, b in SG:
        t += [f"by rw [b{k}_{b:x}, a{k}_{a:x}]; exact {I}.v{nm}", f"by rw [b{k}_{b:x}]; exact {I}.l{nm}"]
    t.append("fun e he => ?_")
    return "⟨" + ", ".join(t) + "⟩"


phc, chc = sig('SvIvHc', 'sv_ivhc')
phx, chx = sig('SvIvHx', 'sv_ivhx')
pa, ca = sig('SvIvA', 'sv_iva')
pb, cb = sig('SvIvB', 'sv_ivb')

o = []
O = o.append
O("set_option maxHeartbeats 64000000 in")
O("/-- **One batch** of the inversion of `s`, from its head at 0x1328: to 0x1556 when `g` is zero, and")
O("otherwise back to the head after one `ivStep8`. -/")
O("theorem iv_iter " + IMPL + " {m : Machine} {st : Iv}")
O("    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hN : 0 < N)")
O(f"    (s : St m.mem SV m 0x1328 (reg m)) (I : {INV.format(m='m')} st) (h0 : st.rem ≠ 0) :")
O("    ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧")
O(f"      ((st.g = 0 ∧ St m'.mem SV m' 0x1556 (reg m') ∧ {INV.format(m=chr(109) + chr(39))} st) ∨")
O(f"       (st.g ≠ 0 ∧ St m'.mem SV m' 0x1328 (reg m') ∧ {INV.format(m=chr(109) + chr(39))} (ivStep8 N st))) := by")
O("  have hrem' : BitVec.ofNat 32 st.rem ≠ 0 := Pv.ofNat_ne0 (by omega) I.rem")
O("  rcases sv_ivhc (x21 := 0) (er := []) (es := []) " + " ".join(head_arg(p, 'I', 's', {'M0': 'm.mem', 'hrem': "hrem'"}) for p in phc)
  + " with ⟨h, _⟩ | ⟨" + ", ".join(pat(chc, 1)) + "⟩")
O("  · exact absurd trivial h")
O(f"  have I1 : {INV.format(m='n1')} st := by")
O("    refine " + head_inv(1, 'I', 'm'))
for l in ww_cases(1):
    O("  " + l)
O("  obtain ⟨m2, c2, k2, h2⟩ := ec_scan F E1.self 8 0 rfl s1 (by rw [r1_a0]; rfl)")
O("    (by rw [r1_a1]; exact (add_ofNat_zero _).symm) (fun k hk => absurd hk (Nat.not_lt_zero _))")
O("  have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 23, 24, 25, 26, 27] → reg m2 q = reg n1 q := fun q hq =>")
O("    k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)")
O("  rcases h2 with ⟨hzr, s2⟩ | ⟨hnz, s2⟩")
O("  · have m2m : m2.mem = n1.mem := s2.mem")
O("    have hg : st.g = 0 := by")
O("      rw [← I1.vg, sv_zero.2]")
O("      exact (accV_zero_iff 8).2 hzr")
O("    exact ⟨m2, c1.trans c2, fun x hx => by rw [m2m, fR1 x hx], .inl ⟨hg, ⟨s2.pc, rfl, fun _ => rfl⟩,")
O("      I1.of m2m kk⟩⟩")
O("  have m2m : m2.mem = n1.mem := s2.mem")
O("  have hg : st.g ≠ 0 := by")
O("    rw [← I1.vg]; intro h")
O("    exact hnz ((accV_zero_iff 8).1 (sv_zero.1 h))")
O("  have s2' : St m2.mem SV m2 0x134C (reg m2) := ⟨s2.pc, rfl, fun _ => rfl⟩")
O("  have I2 := I1.of m2m kk")
O("  have hns := umin_ofNat I.rem")
O("  have hn : min st.rem 62 - 1 + 1 = min st.rem 62 := by omega")
O("  rcases sv_iva (x21 := 0) (er := []) (es := []) " + " ".join(head_arg(p, 'I2', "s2'", {'M0': 'm2.mem', 'hrem': "hrem'"}) for p in pa)
  + " with ⟨h, _⟩ | ⟨" + ", ".join(pat(ca, 3)) + "⟩")
O("  · exact absurd trivial h")
O("  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)")
O("  obtain ⟨n4, M4, c4, s4, h4, k4, f4, -⟩ := ec_loop (min st.rem 62 - 1) E3.self s3")
O("    (iv_s0 (δ := st.δ) I2.lf I2.lg I2.vf I2.vg (by rw [r3_23, r3_25]; exact I2.wd) r3_2 r3_22 w3_74 r3_a0 r3_a1 r3_a4 r3_5")
O("      r3_31 r3_a7 r3_8 r3_29 r3_a2 r3_6)")
O("    (by rw [hn]; exact r3_a6.trans hns) (by omega)")
O("    (by rw [r3_2]; exact zfr_al FS (c := 0x74) (by decide) (by decide))")
O("    (by rw [r3_2]; exact zfr_code FS (c := 0x74) (by decide))")
O("  have hm4 : n4.mem = M4 := s4.mem")
O("  subst hm4")
O("  rw [hn] at h4")
O(f"  have f4' : ∀ x, Sep ({fa(0x74)}) 4 x 1 → n4.mem x = n3.mem x := fun x hx => f4 x (by rw [r3_2]; exact hx)")
O("  have K4 := iv_keep74 F f4'")
O("  have R4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x hx => f4' x (svR_hi (c := 0x74) (l := 4) hx (by decide))")
O("  have CH3 : ∀ x, SvR B x → n3.mem x = m.mem x := fun x hx => by rw [fR3 x hx, m2m, fR1 x hx]")
O("  have CH4 : ∀ x, SvR B x → n4.mem x = m.mem x := fun x hx => by rw [R4 x hx, CH3 x hx]")


def ivb_arg(p):
    if p in ('F', 'hret', 'hO'):
        return p
    m = {'E0': '(E3.fr F R4)', 'V0': '(V3.keepL K4 (by decide))', 's0': 's4', 'M0': 'n4.mem',
         'fM': '(fun _ _ => rfl)', 'g0_2': '((k4 2 (by decide)).trans r3_2)',
         'g0_18': '((k4 18 (by decide)).trans r3_18)', 'g0_19': '((k4 19 (by decide)).trans r3_19)',
         'g0_21': '((k4 21 (by decide)).trans r3_21)', 'g0_23': 'rfl', 'g0_25': 'rfl',
         'g0_26': '((k4 26 (by decide)).trans r3_26)', 'g0_27': '((k4 27 (by decide)).trans r3_27)',
         'IC0': '(I.IC.sv F CH4)', 'EC0': '(I.EC.sv F CH4)', 'g0_24': '((k4 24 (by decide)).trans r3_24)',
         'g0_14': 'rfl', 'g0_5': 'rfl', 'g0_31': 'rfl', 'g0_17': 'rfl', 'g0_8': 'rfl', 'g0_29': 'rfl',
         'g0_12': 'rfl', 'g0_6': 'rfl', 'w0_5c': '((K4.w32 (by decide) (by decide)).trans (w3_5c.trans hns))',
         'hns1': '(by omega)', 'hns2': '(Nat.min_le_right _ _)', 'UC0': '(I.UC.sv F CH4)',
         'hfs': 'I2.lf', 'hgs': 'I2.lg', 'hds': 'I2.ld', 'hes': 'I2.le'}
    if p in m:
        return m[p]
    for pre, acc in (('w0_', 'w32'), ('a0_', 'acc'), ('b0_', 'b8')):
        if p.startswith(pre):
            return f"((K4.{acc} (by decide) (by decide)).trans {pre[0]}3_{p[3:]})"
    raise ValueError(p)


O("  rcases sv_ivb (x21 := 0) (er := []) (es := []) (w5c := 0) (s8v := 0) " + " ".join(ivb_arg(p) for p in pb)
  + " with ⟨h, _⟩ | ⟨σa, Aa, ea, la, σb, Ab, eb, lb, σc, Ac, ec, lc,")
O("      σd, Ad, ed, ld, " + ", ".join(pat(cb, 5)) + "⟩")
O("  · exact absurd (sc4 _ _ _ _) h")
O("  have CH5 : ∀ x, SvR B x → n5.mem x = m.mem x := fun x hx => by rw [fR5 x hx, CH4 x hx]")
O("  have hNv : accV n4.mem (BitVec.ofNat 32 0x3FCC4268) 8 = N := by")
O("    rw [accV_dataR F CH4 (by decide) (by decide), I.aN]")
O("  have hMI : (BitVec.ofNat 32 0x11FF43B1 : Word).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755 : Word).toNat = ivMI :=")
O("    rfl")
O("  obtain ⟨Zd, -, -, Zu, Zv, Zq, Zr⟩ := h4")
O("  have eu : i64Val ((reg n4 a4).toNat + 2 ^ 32 * (reg n4 (5 : Fin 32)).toNat) =")
O("      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).u := by rw [← Zu]")
O("  have ev : i64Val ((reg n4 (31 : Fin 32)).toNat + 2 ^ 32 * (reg n4 a7).toNat) =")
O("      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).v := by rw [← Zv]")
O("  have eq : i64Val ((reg n4 (8 : Fin 32)).toNat + 2 ^ 32 * (reg n4 (29 : Fin 32)).toNat) =")
O("      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).q := by rw [← Zq]")
O("  have er : i64Val ((reg n4 a2).toNat + 2 ^ 32 * (reg n4 (6 : Fin 32)).toNat) =")
O("      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).r := by rw [← Zr]")
O("  rw [I2.vf, I2.vg, eu, ev] at ea")
O("  rw [I2.vf, I2.vg, eq, er] at eb")
O("  rw [I2.vd, I2.ve, eu, ev] at ec")
O("  rw [I2.vd, I2.ve, eq, er] at ed")
O("  obtain ⟨vf', lf'⟩ := fgUpd8_of la ea (tn8 (by omega)) rfl")
O("  obtain ⟨vg', lg'⟩ := fgUpd8_of lb eb (tn8 (by omega)) rfl")
O("  rw [hNv, hMI] at b5_440 a5_420 b5_1040 a5_1020")
O("  obtain ⟨vd', ld'⟩ := deUpd8_of lc hN ec (tn8 (Nat.lt_of_le_of_lt (lrsm8_le lc) (by decide))) rfl")
O("  obtain ⟨ve', le'⟩ := deUpd8_of ld hN ed (tn8 (Nat.lt_of_le_of_lt (lrsm8_le ld) (by decide))) rfl")
t = ["E5", "I.IC.sv F CH5", "I.EC.sv F CH5", "I.UC.sv F CH5", "V5", "r5_2",
     "by rw [r5_3, k4 3 (by decide), r3_3]; exact I2.g3", "by rw [r5_4, k4 4 (by decide), r3_4]; exact I2.g4",
     "r5_18", "r5_19", "r5_21", "r5_24", "r5_26", "r5_27", "by rw [r5_23, r5_25]; exact Zd",
     "by rw [w5_78, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl",
     "by simp only [ivStep8]; have := I.rem; omega", "w5_60", "w5_70",
     "by rw [accV_dataR F CH5 (by decide) (by decide)]; exact I.aN"]
t += [f"a5_{a:x}" for a in QA]
for nm, a, b in SG:
    t += [f"by rw [b5_{b:x}, a5_{a:x}]; exact v{nm}'", f"by rw [b5_{b:x}]; exact l{nm}'"]
t.append("fun e he => ?_")
O("  refine ⟨n5, c1.trans (c2.trans (c3.trans (c4.trans c5))), CH5, .inr ⟨hg, s5, " + ", ".join(t) + "⟩⟩")
for l in ww_cases(5):
    O(l)
O("")
O("/-- **The batches** of the inversion of `s`, from its head at 0x1328 back to it, as many as `ivLoop8` runs. -/")
O("theorem iv_loop " + IMPL + " (F : Fr B 0x3830)")
O("    (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hN : 0 < N) :")
O("    ∀ k {m : Machine} {st : Iv}, St m.mem SV m 0x1328 (reg m) →")
O(f"      {INV.format(m='m')} st →")
O("      ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1328 (reg m') ∧")
O(f"        {INV.format(m=chr(109) + chr(39))} (ivLoop8 N k st)")
O("  | 0, m, st, s, I => ⟨m, .refl m, fun _ _ => rfl, s, I⟩")
O("  | k + 1, m, st, s, I => by")
O("    by_cases h0 : st.rem = 0 ∨ st.g = 0")
O("    · rw [ivLoop8, ite_eq_left h0]; exact ⟨m, .refl m, fun _ _ => rfl, s, I⟩")
O("    rw [ivLoop8, ite_eq_right h0]")
O("    obtain ⟨n1, c1, fr1, h1⟩ := iv_iter F hret hO hN s I (fun h => h0 (.inl h))")
O("    rcases h1 with ⟨hg, -, -⟩ | ⟨-, s1, I1⟩")
O("    · exact absurd (.inr hg) h0")
O("    obtain ⟨n2, c2, fr2, s2, I2⟩ := iv_loop F hret hO hN k s1 I1")
O("    exact ⟨n2, c1.trans c2, fun x hx => by rw [fr2 x hx, fr1 x hx], s2, I2⟩")
O("")
O("set_option maxHeartbeats 16000000 in")
O("/-- **The exit** of the inversion of `s`: from its head at 0x1328 to 0x1556 once no steps are left or")
O("`g` is zero. -/")
O("theorem iv_exit " + IMPL + " {m : Machine} {st : Iv}")
O("    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hN : 0 < N)")
O(f"    (s : St m.mem SV m 0x1328 (reg m)) (I : {INV.format(m='m')} st) (h0 : st.rem = 0 ∨ st.g = 0) :")
O("    ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1556 (reg m') ∧")
O(f"      {INV.format(m=chr(109) + chr(39))} st := by")
O("  by_cases hr : st.rem = 0")
O("  · have hrem' : BitVec.ofNat 32 st.rem = 0 := by rw [hr]; rfl")
O("    rcases sv_ivhx (x21 := 0) (er := []) (es := []) " + " ".join(head_arg(p, 'I', 's', {'M0': 'm.mem', 'hrem': "hrem'"}) for p in phx)
  + " with ⟨h, _⟩ | ⟨" + ", ".join(pat(chx, 1)) + "⟩")
O("    · exact absurd trivial h")
O("    refine ⟨n1, c1, fR1, s1, " + head_inv(1, 'I', 'm')[1:-1] + "⟩")
for l in ww_cases(1):
    O("  " + l)
O("  obtain ⟨n1, c1, fr1, h1⟩ := iv_iter F hret hO hN s I hr")
O("  rcases h1 with ⟨-, s1, I1⟩ | ⟨hg, -, -⟩")
O("  · exact ⟨n1, c1, fr1, s1, I1⟩")
O("  · exact absurd (h0.resolve_left hr) hg")
O("")
O("end C3.RV32.Sv")
open(BASE + 'SvIvLoop.lean', 'w').write(HEAD + "\n" + "\n".join(o) + "\n")
