import C3BootProofs.Proofs.DerNested

/-!
# Calls to `Der::element`

`Der::octet_string`, `Der::bit_string`, and `Der::integer` compile to the
same frame: they save `ra` and `s0` in a 0x20-byte frame, keep `out` in
`s0`, load the tag into `a2`, and call `Der::element` with its result in the
frame at `sp + 4`. Then each reads that result and stores its own at `out`,
and all three return through the same epilogue. These lemmas prove the
prologue and call, and the epilogue, for any code with those instructions.
-/

namespace C3.RV32

open C3.Image

/-- The registers the prologue saves, and where in the frame. -/
abbrev dcPs : List (Fin 32 × Word) := [(ra, 0x1C), ((8 : Fin 32), 0x18)]

/-- From 0x6 to the call at 0xC: `out` to `s0`, the result's address to
`a0`, and the tag to `a2`. -/
def dcMov (tag : Word) : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x4, .aluImm .add a2 x0 tag]

/-- Where a reader that calls `Der::element` at `P + e` runs: its code and
its callees', its 0x20-byte frame below `sp0`, `ol` bytes of result at
`out`, and the reader at `d`, apart from what each must not touch. -/
structure DerCallEnv (M : Word → BitVec 8) (code : List Nat) (P e sp0 out d : Word) (ol : Nat) : Prop where
  hP : P.toNat % 2 = 0
  hE : (P + e).toNat % 2 = 0
  cod : CodeIn M P code
  elem : CodeIn M (P + e) derElementCode
  tlv : CodeIn M (P + e + 0x26) derTlvCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x20 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hd : d.toNat % 4 = 0
  sFC : Sep (sp0 + 0xFFFFFFE0) 0x20 P code.length
  sFE : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + e) derElementCode.length
  sFT : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + e + 0x26) derTlvCode.length
  sOC : Sep out ol P code.length
  sDC : Sep (d + 8) 8 P code.length
  sDT : Sep (d + 8) 8 (P + e + 0x26) derTlvCode.length
  sOF : Sep out ol (sp0 + 0xFFFFFFE0) 0x20
  sDF : Sep (d + 8) 8 (sp0 + 0xFFFFFFE0) 0x20
  sRF : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (sp0 + 0xFFFFFFE0) 0x20
  hrp : 0 < (memLoad32 M (d + 8)).toNat
  hrw : (memLoad32 M (d + 8)).toNat + (memLoad32 M (d + 0xC)).toNat < 2 ^ 32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The prologue and the call**: from the entry to the instruction after
the call at 0x14, with the frame at `F = sp0 - 0x20`. The result of
`Der::element` sits at `F + 4` over `Msv`, which is the entry memory with
`ra` and `s0` saved in the frame. -/
theorem derCall_pro (m : Machine) {code : List Nat} {P e sp0 out d hi lo : Word} {ol tag : Nat}
    (env : DerCallEnv m.mem code P e sp0 out d ol)
    (h0 : fetchRel code 0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2))
    (hsv : blockEnd code 2 (saveBlock dcPs) = some 6)
    (hmv : blockEnd code 6 (dcMov (BitVec.ofNat 32 tag)) = some 0xC)
    (hc1 : fetchRel code 0xC = some (.auipc ra hi, 4)) (hc2 : fetchRel code (0xC + 4) = some (.jalr ra ra lo, 4))
    (hb : P + BitVec.ofNat 32 0xC + hi + lo = P + e) (htag : tag < 256)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d) :
    ∃ m5 Msv, Steps m m5 ∧
      St (derTlvMem Msv (sp0 + 0xFFFFFFE0 + 4) d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
        (derElement tag (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)))
        P m5 0x14 (reg m5) ∧
      reg m5 sp = sp0 + 0xFFFFFFE0 ∧ reg m5 8 = out ∧
      (∀ q, tlvClob q = false → q ≠ ra → q ≠ sp → q ≠ 8 → q ≠ a0 → reg m5 q = reg m q) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Msv x = m.mem x) ∧
      memLoad32 Msv (sp0 + 0xFFFFFFE0 + 0x1C) = reg m ra ∧ memLoad32 Msv (sp0 + 0xFFFFFFE0 + 0x18) = reg m 8 := by
  obtain ⟨rp, hrp⟩ : ∃ rp, memLoad32 m.mem (d + 8) = rp := ⟨_, rfl⟩
  obtain ⟨rl, hrl⟩ : ∃ rl, memLoad32 m.mem (d + 0xC) = rl := ⟨_, rfl⟩
  have sRF := env.sRF
  rw [hrp, hrl] at sRF ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sFE := env.sFE; have sFT := env.sFT; have sDF := env.sDF
  rw [hF] at sFC sFE sFT sDF sRF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep F 0x20 b code'.length → (∀ x, Sep F 0x20 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod h0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock dcPs) u1 env.cod hsv (saveBlock_ok _ dcPs _ fun p hp => by
    rw [sp1]
    simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) dcPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x20 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside dcPs fun p hp => by
      simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact frm_sep' hx (by decide)
      · exact frm_sep' hx (by decide)
  have hslv : ∀ r o, (r, o) ∈ dcPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) r := u2.regs
  obtain ⟨m3, c3, u3⟩ := St.block (dcMov (BitVec.ofNat 32 tag)) u2.self (cIn env.cod sFC frSv) hmv
    (by simp [BlockOk, BInstr.ok, dcMov])
  simp only [runBlock, BInstr.run, dcMov] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have v3 : reg m3 sp = F ∧ reg m3 8 = out ∧ reg m3 a0 = F + 4 ∧ reg m3 a2 = BitVec.ofNat 32 tag ∧
      reg m3 a1 = d := by
    simp +decide only [g3, upd_app, ↓reduceIte, r2]
    simp only [ev_add, hsp, hF, ha0, ha1, zw]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  obtain ⟨v3sp, v38, v3a0, v3a2, v3a1⟩ := v3
  have k3 : ∀ q : Fin 32, q ≠ sp → q ≠ 8 → q ≠ a0 → q ≠ a2 → reg m3 q = reg m q := fun q h1 h2 h3 h4 => by
    rw [g3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h3, h4, ite_false]; rw [r2]; simp only [upd_app, h0, h1, ite_false]
  have hcS := cIn env.cod sFC frSv
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS hc1 hc2 hb env.hE
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have hF4 : F + 4 = F + BitVec.ofNat 32 4 := rfl
  obtain ⟨m5, c5, pc5, mem5, k5⟩ := derElement_correct m4 (tag := tag) env.hE
    (by rw [mem4]; exact cIn env.elem sFE frSv) (by rw [mem4]; exact cIn env.tlv sFT frSv) pc4
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [r4 a2 (by decide), v3a2]) htag
    (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0xC + 8) (by decide)))
    (by rw [hF4]; exact aligned_add hFa (by decide)) env.hd
    (by rw [hF4]; exact sFE.sub (by decide)) (by rw [hF4]; exact sFT.sub (by decide)) env.sDT
  rw [mem4] at mem5
  have eD8 : memLoad32 Msv (d + 8) = rp := by
    rw [← hrp]; exact memLoad32_congr fun j hj => frSv _ (sDF.symm.subR (c := j) (l := 1) (by omega))
  have eDC : memLoad32 Msv (d + 0xC) = rl := by
    rw [← hrl]; exact memLoad32_congr fun j hj => frSv _ (by
      rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact sDF.symm.subR (by omega))
  rw [eD8, eDC] at mem5
  have eL : memBytes Msv rp rl.toNat = memBytes m.mem rp rl.toNat :=
    memBytes_congr fun i hi => frSv _ (sRF.symm.subR (c := i) (l := 1) (by omega))
  rw [eL] at mem5
  refine ⟨m5, Msv, .cons d1 (c2.trans (c3.trans (c4.trans c5))), ⟨by rw [pc5], mem5, fun _ => rfl⟩, ?_, ?_,
    fun q hq h1 h2 h3 h4 => ?_, frSv, hslv ra 0x1C (by decide), hslv 8 0x18 (by decide)⟩
  · rw [k5 sp (by decide), r4 sp (by decide), v3sp]
  · rw [k5 8 (by decide), r4 8 (by decide), v38]
  · have ha2 : q ≠ a2 := fun e => by subst e; exact absurd hq (by decide)
    rw [k5 q hq, r4 q h1, k3 q h2 h3 h4 ha2]

/-- Outside the frame, the memory after the call is the entry memory with
the reader moved past the element. -/
theorem derCall_outside {Msv M : Word → BitVec 8} {F d rp rl x : Word} (r : Except DerError DerTlv)
    (hM : ∀ x, Sep F 0x20 x 1 → Msv x = M x) (hx : Sep F 0x20 x 1) :
    derTlvMem Msv (F + 4) d rp rl r x = derAdvance M d rp rl r x := by
  rw [derTlvMem_outside r (by rw [show F + 4 = F + BitVec.ofNat 32 4 from rfl]; exact hx.sub (by decide)),
    derAdvance_pt r (hM x hx)]

/-- The saved registers' slots, at `F + 0x18` and `F + 0x1C`, survive the
call and any stores to the result. -/
theorem derCall_slot {Msv Mx : Word → BitVec 8} {F out d rp rl : Word} {ol : Nat} {o : Word}
    (r : Except DerError DerTlv) (sOF : Sep out ol F 0x20) (sDF : Sep (d + 8) 8 F 0x20)
    (ho : 0x18 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x20)
    (hMx : ∀ x, Sep out ol x 1 → Mx x = derTlvMem Msv (F + 4) d rp rl r x) :
    memLoad32 Mx (F + o) = memLoad32 Msv (F + o) := by
  apply memLoad32_congr; intro j hj
  have e : F + o + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (o.toNat + j) := by
    conv => lhs; rw [← ofNat_toNat_self o]
    rw [add_ofNat_assoc]
  rw [hMx _ (by rw [e]; exact sOF.subR (c := o.toNat + j) (l := 1) (by omega)), e,
    derTlvMem_outside r (by
      rw [show F + 4 = F + BitVec.ofNat 32 4 from rfl]
      exact sep_offsets F (c := 4) (n := 17) (d := o.toNat + j) (k := 1) (.inl (by omega)) (by omega) (by omega)),
    derAdvance_outside r (sDF.subR (by omega))]

set_option maxRecDepth 20000 in
/-- **The epilogue** at `E`: it reloads `ra` and `s0` from the frame at
`F`, frees it, and returns. -/
theorem derCall_epi {code : List Nat} {Mx : Word → BitVec 8} {P F retAddr : Word} {E : Nat} {n : Machine}
    (s : St Mx P n E (reg n)) (hc : CodeIn Mx P code)
    (hr : blockEnd code E (restoreBlock dcPs) = some (E + 4))
    (ha : fetchRel code (E + 4) = some (.aluImm .add sp sp 0x20, 2))
    (hj : fetchRel code (E + 6) = some (.jalr x0 ra 0x0, 2))
    (hFa : F.toNat % 4 = 0) (rsp : reg n sp = F) (hra : memLoad32 Mx (F + 0x1C) = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = F + 0x20 ∧ reg n' ra = retAddr ∧
      reg n' 8 = memLoad32 Mx (F + 0x18) ∧ ∀ q, q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock dcPs) s hc hr
    (restoreBlock_ok Mx _ dcPs (reg n) rsp (by decide) fun p hp => by
      simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> exact fr_al' hFa (by decide))
  simp only [restoreBlock_run Mx _ dcPs (reg n) rsp (by decide)] at u1
  obtain ⟨n2, d2, u2⟩ := u1.aluImm hc ha (off' := E + 6) (ofNat_add_ofNat (E + 4) 2)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc hj
  have rsp1 : restoreRegs Mx F (reg n) dcPs sp = F := by rw [restoreRegs_sp _ _ _ _ (by decide)]; exact rsp
  refine ⟨n3, c1.trans (.cons d2 (.single d3)), ?_, mem3, ?_, ?_, ?_, fun q h1 h8 hs => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp1, ev_add]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact hra
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
  · rw [regs3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s.zero.symm
    simp only [upd_app, h0, hs, ite_false, restoreRegs, h1, h8]

/-- A reader keeps every register outside `t0` to `t2` and `a0` to `a7`
when the call kept them and the code after it wrote only those. -/
theorem derCall_keep {m m5 n' : Machine} {sp0 : Word} (hsp : reg m sp = sp0)
    (k5 : ∀ q, tlvClob q = false → q ≠ ra → q ≠ sp → q ≠ 8 → q ≠ a0 → reg m5 q = reg m q)
    (kn : ∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg m5 q)
    (sp' : reg n' sp = sp0) (ra' : reg n' ra = reg m ra) (s8' : reg n' 8 = reg m 8) :
    ∀ q, oidKeep q = true → reg n' q = reg m q := fun q hq => by
  by_cases hr : q = ra
  · subst hr; exact ra'
  by_cases h8 : q = 8
  · subst h8; exact s8'
  by_cases hs : q = sp
  · subst hs; rw [sp', hsp]
  have hkc : ∀ q : Fin 32, oidKeep q = true → tlvClob q = false := by decide
  have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
  rw [kn q hq hr h8 hs, k5 q (hkc q hq) hr hs h8 h0]

end C3.RV32
