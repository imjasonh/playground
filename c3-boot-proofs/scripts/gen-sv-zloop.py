#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/SvZLoop2.lean: the batches of the inversion of
`Z` in `sigstore::verify`, composed from the generated stages `sv_za` and
`sv_zb` and the divstep loop `zt_loop`.

The stages take about a hundred hypotheses each, so this reads their
statements and writes the arguments and the names of their conclusions.

Usage: python3 scripts/gen-sv-zloop.py   (from c3-boot-proofs/)
"""

import re
import sys
BASE = 'C3BootProofs/Proofs/'
def sig(fn, name):
    s=open(BASE+fn+'.lean').read()
    i=s.index(f'theorem {name} '); j=s.index(':= by', i); st=s[i:j]
    k=st.index('(¬'); ph=st[:k]; concl=st[k:]
    pn=re.findall(r'\(([A-Za-z0-9_]+) :', ph)
    # drop implicit binder group names (inside {...})
    ph2=re.sub(r'\{[^}]*\}','',ph)
    pn=re.findall(r'\(([A-Za-z0-9_]+) :', ph2)
    c2=concl[concl.index("∃ n', "):]
    lines=[l.strip().rstrip('∧').strip() for l in c2.split('\n') if l.strip()]
    return pn, lines
def cname(l):
    if l.startswith("∃ n', Steps"): return 'STEPS'
    m=re.match(r"St n'\.mem SV n' 0x([0-9A-F]+)",l)
    if m: return 'ST'
    if l.startswith("SvCode"): return 'E'
    if l.startswith("SvSaves"): return 'V'
    if l.startswith("(∀ x, SvR"): return 'FR'
    if l.startswith("SvKeepL B n0.mem n'.mem"): return 'KL'
    if l.startswith("reg n' sp"): return 'r2'
    m=re.match(r"reg n' \((\d+) : Fin 32\)",l)
    if m: return 'r'+m.group(1)
    m=re.match(r"reg n' (a\d)",l)
    if m: return 'r'+m.group(1)
    m=re.match(r"memLoad32 n'\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x([0-9A-F]+)\)",l)
    if m: return 'w'+m.group(1).lower()
    m=re.match(r"n'\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x([0-9A-F]+)\)",l)
    if m: return 'b'+m.group(1).lower()
    m=re.match(r"accV n'\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x([0-9A-F]+)\)",l)
    if m: return 'a'+m.group(1).lower()
    raise ValueError(l)

ZIW=[0x4C,0x50,0x54,0x58,0x64,0x68,0x6C]+list(range(0x7C,0x134,4))
def fa(e): return f"B + 0x21A0 + BitVec.ofNat 32 0x{e:X}"
out=[]
E=out.append
E("import C3BootProofs.Proofs.SvZLoop\n")
E("/-!\n# `sigstore::verify`: the batches of the inversion of `Z`\n")
E("From the inversion's head at 0x1B54 back to it: `sv_za` starts a batch, `zt_loop` runs its divsteps, and")
E("`sv_zb` applies its matrix, which is one `zvStep`. `zv_loop` runs batches until no steps are left. It")
E("follows `Pv384HLoop.lean`.\n-/\n")
E("namespace C3.RV32.Sv\n\nopen C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv\n\nset_option maxRecDepth 100000\n")
E("/-- The frame words that the inversion of `Z` leaves alone. -/")
E("def ziWords : List Nat := [" + ", ".join(f"0x{e:X}" for e in ZIW) + "]\n")
E("theorem w64_ofNat_split {L : Nat} (hL : L < 2 ^ 64) :")
E("    W64 (BitVec.ofNat 32 (L % 2 ^ 32)) (BitVec.ofNat 32 (L / 2 ^ 32)) = L := by")
E("  simp only [W64, BitVec.toNat_ofNat]; omega\n")
E("theorem lowestVal_lt (σ v : Nat) : lowestVal σ v < 2 ^ 64 := by")
E("  unfold lowestVal; split <;> omega\n")
E("theorem sc4 (X1 X2 X3 X4 : Int) : ∃ σ1 A1, sgnVal σ1 A1 = X1 ∧ σ1 ≤ 1 ∧ ∃ σ2 A2, sgnVal σ2 A2 = X2 ∧ σ2 ≤ 1 ∧")
E("    ∃ σ3 A3, sgnVal σ3 A3 = X3 ∧ σ3 ≤ 1 ∧ ∃ σ4 A4, sgnVal σ4 A4 = X4 ∧ σ4 ≤ 1 ∧ True := by")
E("  obtain ⟨a1, b1, e1, l1⟩ := sgn_ex X1; obtain ⟨a2, b2, e2, l2⟩ := sgn_ex X2")
E("  obtain ⟨a3, b3, e3, l3⟩ := sgn_ex X3; obtain ⟨a4, b4, e4, l4⟩ := sgn_ex X4")
E("  exact ⟨a1, b1, e1, l1, a2, b2, e2, l2, a3, b3, e3, l3, a4, b4, e4, l4, trivial⟩\n")
E("/-- What holds at the inversion's head 0x1B54 for the state `st`. -/")
E("structure ZvInv (B : Word) (m : Machine) (v : Nat → Word) (r3 r4 out bp x26 nzw : Word) (rv sv zv X Y P R2 : Nat)")
E("    (W : Nat → Word) (st : Iv) : Prop where")
inv=[("E","SvCode m.mem"),("IC","SvIvCode m.mem"),("EC","SvEcCode m.mem"),("UC","SvUpCode m.mem"),("V","SvSaves B m.mem v"),
("sp","reg m sp = B + 0x21A0"),("g3","reg m (3 : Fin 32) = r3"),("g4","reg m (4 : Fin 32) = r4"),
("g18","reg m (18 : Fin 32) = out"),("g19","reg m (19 : Fin 32) = bp"),("g26","reg m (26 : Fin 32) = x26"),
("g27",f"reg m (27 : Fin 32) = {fa(0xA20)}"),("w20",f"memLoad32 m.mem ({fa(0x20)}) = nzw"),
("wd",f"W64 (memLoad32 m.mem ({fa(0x34)})) (memLoad32 m.mem ({fa(0x38)})) = st.δ"),
("wr",f"memLoad32 m.mem ({fa(0x78)}) = BitVec.ofNat 32 st.rem"),("rem","st.rem < 2 ^ 32"),
("w460",f"memLoad32 m.mem ({fa(0x460)}) = BitVec.ofNat 32 0xFFFFFFFF"),("w464",f"memLoad32 m.mem ({fa(0x464)}) = BitVec.ofNat 32 0xFFFFFFFF"),
("a420",f"accV m.mem ({fa(0x420)}) 8 = P"),("aP","accV m.mem (BitVec.ofNat 32 0x3FCC4B38) 8 = P"),
("a440",f"accV m.mem ({fa(0x440)}) 8 = R2"),("aR","accV m.mem (BitVec.ofNat 32 0x3FCC4B78) 8 = R2"),
("a2a0",f"accV m.mem ({fa(0x2A0)}) 8 = rv"),("a2c0",f"accV m.mem ({fa(0x2C0)}) 8 = sv"),("a2e0",f"accV m.mem ({fa(0x2E0)}) 8 = zv"),
("a15a8",f"accV m.mem ({fa(0x15A8)}) 8 = X"),("a15c8",f"accV m.mem ({fa(0x15C8)}) 8 = Y")]
SG=[("f",0x320,0x340),("g",0x1380,0x13A0),("d",0x1480,0x14A0),("e",0x1020,0x1040)]
for nm,a,b in SG:
    inv.append((f"v{nm}",f"sgnVal (m.mem ({fa(b)})).toNat (accV m.mem ({fa(a)}) 8) = st.{nm}"))
    inv.append((f"l{nm}",f"(m.mem ({fa(b)})).toNat ≤ 1"))
inv.append(("ww",f"∀ e, e ∈ ziWords → memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 e) = W e"))
for n,t in inv: E(f"  {n} : {t}")
E("")
HEAD = "\n".join(out)

pa,la=sig('SvZA','sv_za'); pa=[p for p in pa if not p.isdigit()]
pb,lb=sig('SvZB','sv_zb'); pb=[p for p in pb if not p.isdigit()]
ca=[cname(l) for l in la]; cb=[cname(l) for l in lb]
def pat(cs, k):
    names=[]
    for c in cs:
        if c=='STEPS': names += [f"n{k}", f"c{k}"]
        elif c=='ST': names.append(f"s{k}")
        elif c=='E': names.append(f"E{k}")
        elif c=='V': names.append(f"V{k}")
        elif c=='FR': names.append(f"fR{k}")
        else: names.append(f"{c[0]}{k}_{c[1:]}")
    return names
def hexw(n): return int(n,16)
ZIWS=set(ZIW)
# ZA args
def za_arg(p):
    if p in ('F','hret','hO'): return p
    m={'E0':'I.E','V0':'I.V','s0':'s','M0':'m.mem','fM':'(fun _ _ => rfl)','g0_2':'I.sp','g0_18':'I.g18','g0_19':'I.g19',
       'g0_26':'I.g26','g0_27':'I.g27','w0_20':'I.w20','w0_34':'rfl','w0_38':'rfl','w0_78':'I.wr','w0_460':'I.w460','w0_464':'I.w464',
       'a0_2a0':'I.a2a0','a0_2c0':'I.a2c0','a0_2e0':'I.a2e0','a0_320':'rfl','a0_420':'(I.a420.trans I.aP.symm)',
       'a0_440':'(I.a440.trans I.aR.symm)','a0_1020':'rfl','a0_1380':'rfl','a0_1480':'rfl','a0_15a8':'I.a15a8','a0_15c8':'I.a15c8',
       'b0_340':'rfl','b0_1040':'rfl','b0_13a0':'rfl','b0_14a0':'rfl','IC0':'I.IC','EC0':'I.EC','hrem':'hrem\'','hfs':'I.lf','hgs':'I.lg'}
    if p in m: return m[p]
    if p.startswith('w0_') and hexw(p[3:]) in ZIWS: return f"(I.ww 0x{hexw(p[3:]):X} (by decide))"
    raise ValueError(p)
CH="(fun x hx => (fr2 x hx).trans (fR1 x hx))"
def zb_arg(p):
    if p in ('F','hret','hO'): return p
    m={'E0':'E2','V0':'(V1.keepL K2 (by decide))','s0':'s2','M0':'n2.mem','fM':'(fun _ _ => rfl)','g0_2':'sp2',
       'g0_18':'(by rw [r2_k _ (by decide), r1_18])','g0_19':'(by rw [r2_k _ (by decide), r1_19])',
       'g0_26':'(by rw [r2_k _ (by decide), r1_26])','g0_27':'(by rw [r2_27]; rfl)',
       'w0_34':'rfl','w0_38':'rfl','g0_24':'rfl','w0_3c':'rfl','w0_44':'rfl','w0_40':'rfl','w0_70':'rfl','w0_60':'rfl',
       'w0_5c':'rfl','w0_74':'rfl','w0_1c':'((K2.w32 (by decide) (by decide)).trans (w1_1c.trans hns))',
       'a0_420':f'(by rw [K2.acc (by decide) (by decide), a1_420, accV_dataR F {CH} (by decide) (by decide)])',
       'a0_440':f'(by rw [K2.acc (by decide) (by decide), a1_440, accV_dataR F {CH} (by decide) (by decide)])',
       'IC0':'IC2','EC0':f'(I.EC.sv F {CH})','hns1':'hn1','hns2':'hn2','UC0':f'(I.UC.sv F {CH})',
       'hfs':'I.lf','hgs':'I.lg','hds':'I.ld','hes':'I.le'}
    if p in m: return m[p]
    if p.startswith('w0_'): return f"((K2.w32 (by decide) (by decide)).trans w1_{p[3:]})"
    if p.startswith('a0_'): return f"((K2.acc (by decide) (by decide)).trans a1_{p[3:]})"
    if p.startswith('b0_'): return f"((K2.b8 (by decide) (by decide)).trans b1_{p[3:]})"
    raise ValueError(p)
o=[]
O=o.append
O("theorem tn8 {σ : Nat} (h : σ < 256) : (BitVec.ofNat 8 σ).toNat = σ := by")
O("  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h")
O("")
O("theorem zv_s0 {B : Word} {m : Machine} {st : Iv} {fs gs : BitVec 8} {fv gv : Nat}")
O("    (hfs : fs.toNat ≤ 1) (hgs : gs.toNat ≤ 1) (vf : sgnVal fs.toNat fv = st.f) (vg : sgnVal gs.toNat gv = st.g)")
O(f"    (w24 : memLoad32 m.mem ({fa(0x24)}) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32))")
O(f"    (w28 : memLoad32 m.mem ({fa(0x28)}) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32))")
O(f"    (w2c : memLoad32 m.mem ({fa(0x2C)}) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32))")
O(f"    (w30 : memLoad32 m.mem ({fa(0x30)}) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32))")
O(f"    (wd : W64 (memLoad32 m.mem ({fa(0x34)})) (memLoad32 m.mem ({fa(0x38)})) = st.δ)")
O("    (r24 : reg m (24 : Fin 32) = BitVec.ofNat 32 0x1)")
for e,v in ((0x3C,0),(0x40,0),(0x44,0),(0x5C,1),(0x60,0),(0x70,0),(0x74,0)):
    O(f"    (w{e:x} : memLoad32 m.mem ({fa(e)}) = BitVec.ofNat 32 0x{v:X})")
O("    : ZtRegs B m.mem (reg m) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩ := by")
O("  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩")
O(f"  · show W64 (memLoad32 m.mem ({fa(0x34)})) (memLoad32 m.mem ({fa(0x38)})) = _; exact wd")
O(f"  · show W64 (memLoad32 m.mem ({fa(0x30)})) (memLoad32 m.mem ({fa(0x2C)})) = _")
O("    rw [w30, w2c, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hfs vf]")
O(f"  · show W64 (memLoad32 m.mem ({fa(0x24)})) (memLoad32 m.mem ({fa(0x28)})) = _")
O("    rw [w24, w28, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hgs vg]")
O(f"  · show W64 (reg m (24 : Fin 32)) (memLoad32 m.mem ({fa(0x3C)})) = _; rw [r24, w3c]; rfl")
O(f"  · show W64 (memLoad32 m.mem ({fa(0x44)})) (memLoad32 m.mem ({fa(0x40)})) = _; rw [w44, w40]; rfl")
O(f"  · show W64 (memLoad32 m.mem ({fa(0x70)})) (memLoad32 m.mem ({fa(0x60)})) = _; rw [w70, w60]; rfl")
O(f"  · show W64 (memLoad32 m.mem ({fa(0x5C)})) (memLoad32 m.mem ({fa(0x74)})) = _; rw [w5c, w74]; rfl")
O("")
O("set_option maxHeartbeats 64000000 in")
O("/-- **One batch** of the inversion of `Z`, from its head at 0x1B54 back to it: `zvStep`. -/")
O("theorem zv_iter {B r3 r4 out bp x26 nzw : Word} {rv sv zv X Y P R2 : Nat} {W v : Nat → Word} {m : Machine} {st : Iv}")
O("    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hP : 0 < P)")
O("    (s : St m.mem SV m 0x1B54 (reg m)) (I : ZvInv B m v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W st)")
O("    (h0 : st.rem ≠ 0) :")
O("    ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1B54 (reg m') ∧")
O("      ZvInv B m' v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W (zvStep P st) := by")
O("  have hn1 : 1 ≤ min st.rem 62 := by omega")
O("  have hn2 : min st.rem 62 ≤ 62 := Nat.min_le_right _ _")
O("  have hrem' : BitVec.ofNat 32 st.rem ≠ 0 := Pv.ofNat_ne0 (by omega) I.rem")
O("  have hns := umin_ofNat I.rem")
O("  rcases sv_za " + " ".join(za_arg(p) for p in pa) + " with ⟨h, _⟩ | ⟨" + ", ".join(pat(ca,1)) + "⟩")
O("  · exact absurd trivial h")
O("  have IC1 : SvIvCode n1.mem := I.IC.sv F fR1")
O("  obtain ⟨n2, c2, E2, IC2, fr2, K2, s2, sp2, r2_3, r2_4, r2_k, r2_27, w2_48, Z2⟩ :=")
O("    zt_loop F (min st.rem 62) E1 IC1 s1 r1_2 (by rw [r1_27]; rfl)")
O(f"      (by show memLoad32 n1.mem ({fa(0x48)}) = _; rw [w1_48, hns]) (by omega)")
O("      (zv_s0 I.lf I.lg I.vf I.vg w1_24 w1_28 w1_2c w1_30 (by rw [w1_34, w1_38]; exact I.wd) r1_24 w1_3c w1_40 w1_44 w1_5c")
O("        w1_60 w1_70 w1_74)")
O("  rcases sv_zb " + " ".join(zb_arg(p) for p in pb) + " with ⟨h, _⟩ | ⟨σa, Aa, ea, la, σb, Ab, eb, lb, σc, Ac, ec, lc,")
O("      σd, Ad, ed, ld, " + ", ".join(pat(cb,3)) + "⟩")
O("  · exact absurd (sc4 _ _ _ _) h")
O("  obtain ⟨Zd, -, -, Zu, Zv, Zq, Zr⟩ := Z2")
O(f"  have CH3 : ∀ x, SvR B x → n3.mem x = m.mem x := fun x hx => by rw [fR3 x hx, fr2 x hx, fR1 x hx]")
O(f"  have CH2 : ∀ x, SvR B x → n2.mem x = m.mem x := {CH}")
O("  have hM : accV n2.mem (BitVec.ofNat 32 0x3FCC4B38) 8 = P := by rw [accV_dataR F CH2 (by decide) (by decide), I.aP]")
O("  have eu : i64Val ((reg n2 (24 : Fin 32)).toNat + 2 ^ 32 *")
O(f"      (memLoad32 n2.mem ({fa(0x3C)})).toNat) = i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).u := by")
O("    rw [← Zu]; rfl")
for nm,(lo,hi),fld in (("ev",(0x44,0x40),"v"),("eq",(0x70,0x60),"q"),("er",(0x5C,0x74),"r")):
    O(f"  have {nm} : i64Val ((memLoad32 n2.mem ({fa(lo)})).toNat + 2 ^ 32 *")
    O(f"      (memLoad32 n2.mem ({fa(hi)})).toNat) = i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).{fld} := by")
    O(f"    rw [← Z{fld}]; rfl")
O("  rw [I.vf, I.vg, eu, ev] at ea")
O("  rw [I.vf, I.vg, eq, er] at eb")
O("  rw [I.vd, I.ve, eu, ev] at ec")
O("  rw [I.vd, I.ve, eq, er] at ed")
O("  obtain ⟨vf', lf'⟩ := fgUpd8_of la ea (tn8 (by omega)) rfl")
O("  obtain ⟨vg', lg'⟩ := fgUpd8_of lb eb (tn8 (by omega)) rfl")
O("  rw [hM] at b3_14a0 a3_1480 b3_1040 a3_1020")
O("  obtain ⟨vd', ld'⟩ := deUpd8_of lc hP ec (tn8 (Nat.lt_of_le_of_lt (lrsm8_le lc) (by decide))) rfl")
O("  obtain ⟨ve', le'⟩ := deUpd8_of ld hP ed (tn8 (Nat.lt_of_le_of_lt (lrsm8_le ld) (by decide))) rfl")
O("  refine ⟨n3, c1.trans (c2.trans c3), CH3, s3, E3, I.IC.sv F CH3, I.EC.sv F CH3, I.UC.sv F CH3, V3, r3_2,")
O("    by rw [r3_3, r2_3, r1_3]; exact I.g3, by rw [r3_4, r2_4, r1_4]; exact I.g4, r3_18, r3_19, r3_26, r3_27, w3_20,")
O("    by rw [w3_34, w3_38]; exact Zd, by rw [w3_78, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl,")
O("    by simp only [zvStep]; have := I.rem; omega, w3_460, w3_464,")
O("    by rw [a3_420, hM], by rw [accV_dataR F CH3 (by decide) (by decide)]; exact I.aP,")
O("    by rw [a3_440, accV_dataR F CH2 (by decide) (by decide)]; exact I.aR,")
O("    by rw [accV_dataR F CH3 (by decide) (by decide)]; exact I.aR, a3_2a0, a3_2c0, a3_2e0, a3_15a8, a3_15c8,")
O("    by rw [b3_340, a3_320]; exact vf', by rw [b3_340]; exact lf',")
O("    by rw [b3_13a0, a3_1380]; exact vg', by rw [b3_13a0]; exact lg',")
O("    by rw [b3_14a0, a3_1480]; exact vd', by rw [b3_14a0]; exact ld',")
O("    by rw [b3_1040, a3_1020]; exact ve', by rw [b3_1040]; exact le', fun e he => ?_⟩")
O("  simp only [ziWords, List.mem_cons, List.not_mem_nil, or_false] at he")
O("  rcases he with " + " | ".join(["rfl"]*len(ZIW)))
for e in ZIW:
    O(f"  · exact w3_{e:x}")
O("")
O("/-- **The batches** of the inversion of `Z`, from its head at 0x1B54 back to it, as many as `zvLoop` runs. -/")
O("theorem zv_loop {B r3 r4 out bp x26 nzw : Word} {rv sv zv X Y P R2 : Nat} {W v : Nat → Word} (F : Fr B 0x3830)")
O("    (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hP : 0 < P) :")
O("    ∀ k {m : Machine} {st : Iv}, St m.mem SV m 0x1B54 (reg m) →")
O("      ZvInv B m v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W st →")
O("      ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1B54 (reg m') ∧")
O("        ZvInv B m' v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W (zvLoop P k st)")
O("  | 0, m, st, s, I => ⟨m, .refl m, fun _ _ => rfl, s, I⟩")
O("  | k + 1, m, st, s, I => by")
O("    by_cases h0 : st.rem = 0")
O("    · rw [zvLoop, ite_eq_left h0]; exact ⟨m, .refl m, fun _ _ => rfl, s, I⟩")
O("    rw [zvLoop, ite_eq_right h0]")
O("    obtain ⟨n1, c1, fr1, s1, I1⟩ := zv_iter F hret hO hP s I h0")
O("    obtain ⟨n2, c2, fr2, s2, I2⟩ := zv_loop F hret hO hP k s1 I1")
O("    exact ⟨n2, c1.trans c2, fun x hx => by rw [fr2 x hx, fr1 x hx], s2, I2⟩")
O("")
O("end C3.RV32.Sv")
open(BASE + 'SvZLoop2.lean', 'w').write(HEAD + "\n".join(o) + "\n")
