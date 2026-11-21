import C3BootProofs.Proofs.DerOid

/-!
# `Der::nested`, as compiled

`Der::nested` reads an element with the tag in `a2` through `Der::element`
and returns a reader over its contents: `Der::new(content)`, whose input and
unread bytes are both the contents.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem sqn_at_0 : fetchRel derSequenceCode 0x0 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem sqn_at_4 : fetchRel derSequenceCode 0x4 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem sqn_at_8 : fetchRel derSequenceCode 0x8 = some (.jalr x0 (6 : Fin 32) 0x274, 4) := by decide
end

section
set_option maxRecDepth 20000
theorem nst_at_0 : fetchRel derNestedCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem nst_at_2 : fetchRel derNestedCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem nst_at_4 : fetchRel derNestedCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem nst_at_6 : fetchRel derNestedCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem nst_at_8 : fetchRel derNestedCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem nst_at_a : fetchRel derNestedCode 0xA = some (.auipc ra 0x0, 4) := by decide
theorem nst_at_e : fetchRel derNestedCode 0xE = some (.jalr ra ra 0xFFFFFF16, 4) := by decide
theorem nst_at_12 : fetchRel derNestedCode 0x12 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem nst_at_14 : fetchRel derNestedCode 0x14 = some (.branch .beq a0 x0 0xC, 2) := by decide
theorem nst_at_16 : fetchRel derNestedCode 0x16 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem nst_at_18 : fetchRel derNestedCode 0x18 = some (.store .sw (8 : Fin 32) a0 0x8, 2) := by decide
theorem nst_at_1a : fetchRel derNestedCode 0x1A = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem nst_at_1c : fetchRel derNestedCode 0x1C = some (.store .sw (8 : Fin 32) a1 0xC, 2) := by decide
theorem nst_at_1e : fetchRel derNestedCode 0x1E = some (.jal x0 0xA, 2) := by decide
theorem nst_at_20 : fetchRel derNestedCode 0x20 = some (.load .lbu a1 sp 0x8, 4) := by decide
theorem nst_at_24 : fetchRel derNestedCode 0x24 = some (.store .sb (8 : Fin 32) a1 0x4, 4) := by decide
theorem nst_at_28 : fetchRel derNestedCode 0x28 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem nst_at_2a : fetchRel derNestedCode 0x2A = some (.load .lw ra sp 0x1C, 2) := by decide
theorem nst_at_2c : fetchRel derNestedCode 0x2C = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem nst_at_2e : fetchRel derNestedCode 0x2E = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem nst_at_30 : fetchRel derNestedCode 0x30 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- What `Der::nested` stores at `out`: on success a reader whose input and
unread bytes are both the element's contents. -/
def derNestedMem (M : Word → BitVec 8) (out rp : Word) : Except DerError DerTlv → Word → BitVec 8
  | .error e => memStore32 (memStore8 M (out + 4) (derErrByte e)) out 0
  | .ok t => memStore32 (memStore32 (memStore32 (memStore32 M (out + 8) (rp + BitVec.ofNat 32 t.header))
      (out + 4) (BitVec.ofNat 32 t.len)) (out + 0xC) (BitVec.ofNat 32 t.len)) out (rp + BitVec.ofNat 32 t.header)

/-- Where `Der::nested` runs: its code and its callees', its 0x20-byte frame
below `sp0`, the result `out`, and the reader at `d`, apart from what each
must not touch. -/
structure NestEnv (M : Word → BitVec 8) (P sp0 out d : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P derNestedCode
  elem : CodeIn M (P + 0xFFFFFF20) derElementCode
  tlv : CodeIn M (P + 0xFFFFFF46) derTlvCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x20 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hd : d.toNat % 4 = 0
  sFC : Sep (sp0 + 0xFFFFFFE0) 0x20 P derNestedCode.length
  sFE : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + 0xFFFFFF20) derElementCode.length
  sFT : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + 0xFFFFFF46) derTlvCode.length
  sOC : Sep out 16 P derNestedCode.length
  sDC : Sep (d + 8) 8 P derNestedCode.length
  sDT : Sep (d + 8) 8 (P + 0xFFFFFF46) derTlvCode.length
  sOF : Sep out 16 (sp0 + 0xFFFFFFE0) 0x20
  sDF : Sep (d + 8) 8 (sp0 + 0xFFFFFFE0) 0x20
  sRF : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (sp0 + 0xFFFFFFE0) 0x20
  hrp : 0 < (memLoad32 M (d + 8)).toNat
  hrw : (memLoad32 M (d + 8)).toNat + (memLoad32 M (d + 0xC)).toNat < 2 ^ 32

abbrev nstPs : List (Fin 32 × Word) := [(ra, 0x1C), ((8 : Fin 32), 0x18)]

def nstMov : List BInstr := [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x4]

section
set_option maxRecDepth 20000
theorem nstSave_end : blockEnd derNestedCode 2 (saveBlock nstPs) = some 0x6 := by decide
theorem nstMov_end : blockEnd derNestedCode 0x6 nstMov = some 0xA := by decide
theorem nstRestore_end : blockEnd derNestedCode 0x2A (restoreBlock nstPs) = some 0x2E := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Der::nested`**: with the reader at `d`, whose unread
bytes start at `rp` and number `rl`, and the tag in `a2`, it stores a reader
over the contents of `derElement` of those bytes at `out`, or its error, and
moves the reader at `d` past the element. Outside its frame, nothing else
changes. -/
theorem derNested_correct (m : Machine) {P sp0 out d retAddr : Word} {tag : Nat} (env : NestEnv m.mem P sp0 out d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (ha2 : reg m a2 = BitVec.ofNat 32 tag) (htag : tag < 256)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derNestedMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement tag (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)))
          out (memLoad32 m.mem (d + 8))
          (derElement tag (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  obtain ⟨rp, hrp⟩ : ∃ rp, memLoad32 m.mem (d + 8) = rp := ⟨_, rfl⟩
  obtain ⟨rl, hrl⟩ : ∃ rl, memLoad32 m.mem (d + 0xC) = rl := ⟨_, rfl⟩
  have hrp0 := env.hrp; have hrw := env.hrw; have sRF := env.sRF
  rw [hrp, hrl] at hrw sRF ⊢
  rw [hrp] at hrp0
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sFE := env.sFE; have sFT := env.sFT; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at sFC sFE sFT sOF sDF sRF ⊢
  have hFw : F.toNat + 0x20 = sp0.toNat := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep F 0x20 b code.length → (∀ x, Sep F 0x20 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code nst_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock nstPs) u1 env.code nstSave_end (saveBlock_ok _ nstPs _ fun p hp => by
    rw [sp1]
    simp only [nstPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) nstPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x20 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside nstPs fun p hp => by
      simp only [nstPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact frm_sep' hx (by decide)
      · exact frm_sep' hx (by decide)
  have hslv : ∀ r o, (r, o) ∈ nstPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [nstPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) r := u2.regs
  obtain ⟨m3, c3, u3⟩ := St.block nstMov u2.self (cIn env.code sFC frSv) nstMov_end
    (by simp [BlockOk, BInstr.ok, nstMov])
  simp only [runBlock, BInstr.run, nstMov] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have v3 : reg m3 sp = F ∧ reg m3 8 = out ∧ reg m3 a0 = F + 4 ∧ reg m3 a2 = BitVec.ofNat 32 tag ∧ reg m3 a1 = d := by
    simp +decide only [g3, upd_app, ↓reduceIte, r2]
    simp only [ev_add, hsp, hF, ha0, ha1, ha2, zw]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  obtain ⟨v3sp, v38, v3a0, v3a2, v3a1⟩ := v3
  have k3 : ∀ q : Fin 32, q ≠ sp → q ≠ 8 → q ≠ a0 → reg m3 q = reg m q := fun q h1 h2 h3 => by
    rw [g3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h3, ite_false]; rw [r2]; simp only [upd_app, h0, h1, ite_false]
  have hcS := cIn env.code sFC frSv
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS nst_at_a nst_at_e
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFF20 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have eT : P + BitVec.ofNat 32 0xFFFFFF20 + 0x26 = P + 0xFFFFFF46 := by rw [BitVec.add_assoc]; rfl
  have hF4 : F + 4 = F + BitVec.ofNat 32 4 := rfl
  obtain ⟨m5, c5, pc5, mem5, k5⟩ := derElement_correct m4 (tag := tag) (even_at P env.hP 0xFFFFFF20 (by decide))
    (by rw [mem4]; exact cIn env.elem sFE frSv) (by rw [mem4, eT]; exact cIn env.tlv sFT frSv) pc4
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [r4 a2 (by decide), v3a2]) htag
    (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0xA + 8) (by decide)))
    (by rw [hF4]; exact aligned_add hFa (by decide)) env.hd
    (by rw [hF4]; exact sFE.sub (by decide)) (by rw [eT, hF4]; exact sFT.sub (by decide))
    (by rw [eT]; exact env.sDT)
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
  obtain ⟨r, hr⟩ : ∃ r, derElement tag (memBytes m.mem rp rl.toNat) = r := ⟨_, rfl⟩
  rw [hr] at mem5 ⊢
  have u5 : St m5.mem P m5 0x12 (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have K5 : ∀ q, tlvClob q = false → q ≠ ra → reg m5 q = reg m3 q := fun q hq hr => by rw [k5 q hq, r4 q hr]
  have sp5 : reg m5 sp = F := by rw [K5 sp (by decide) (by decide), v3sp]
  have s85 : reg m5 8 = out := by rw [K5 8 (by decide) (by decide), v38]
  have fr5' : ∀ x, Sep F 0x20 x 1 → m5.mem x = derAdvance m.mem d rp rl r x := fun x hx => by
    rw [mem5, derTlvMem_outside r (by rw [hF4]; exact hx.sub (by decide)), derAdvance_pt r (frSv x hx)]
  have fr5 : ∀ x, Sep F 0x20 x 1 → Sep (d + 8) 8 x 1 → m5.mem x = m.mem x := fun x hx hd' => by
    rw [fr5' x hx, derAdvance_outside r hd']
  have hc5 : CodeIn m5.mem P derNestedCode := fun i hi => by
    rw [fr5 _ (sFC.subR (c := i) (l := 1) (by omega)) (env.sDC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  -- the slots survive any memory that agrees with `m5.mem` outside `out`
  have slots : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep out 16 x 1 → Mx x = m5.mem x) →
      ∀ q o, (q, o) ∈ nstPs → memLoad32 Mx (F + o) = reg m q := fun {Mx} hMx q o h => by
    have ho : o.toNat + 4 ≤ 0x20 ∧ 0x18 ≤ o.toNat := by
      simp only [nstPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [← hslv q o h]
    apply memLoad32_congr; intro j hj
    have e : F + o + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (o.toNat + j) := by
      conv => lhs; rw [← ofNat_toNat_self o]
      rw [add_ofNat_assoc]
    rw [hMx _ (by rw [e]; exact sOF.subR (c := o.toNat + j) (l := 1) (by omega)), mem5, e,
      derTlvMem_outside r (by
        rw [hF4]; exact sep_offsets F (c := 4) (n := 17) (d := o.toNat + j) (k := 1) (.inl (by omega)) (by omega)
          (by omega)),
      derAdvance_outside r (sDF.subR (by omega))]
  -- the epilogue, from 0x2A
  have epi : ∀ {Mx : Word → BitVec 8} {n : Machine}, St Mx P n 0x2A (reg n) → CodeIn Mx P derNestedCode →
      reg n sp = F → (∀ q o, (q, o) ∈ nstPs → memLoad32 Mx (F + o) = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧ reg n' ra = reg m ra ∧
        reg n' 8 = reg m 8 ∧ ∀ q, q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg n q := by
    intro Mx n s hc rsp hsl
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock nstPs) s hc nstRestore_end
      (restoreBlock_ok Mx _ nstPs (reg n) rsp (by decide) fun p hp => by
        simp only [nstPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl <;> exact fr_al' hFa (by decide))
    simp only [restoreBlock_run Mx _ nstPs (reg n) rsp (by decide)] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc nst_at_2e (off' := 0x30) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc nst_at_30
    have rsp1 : restoreRegs Mx F (reg n) nstPs sp = F := by rw [restoreRegs_sp _ _ _ _ (by decide)]; exact rsp
    have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
    refine ⟨n3, c1.trans (.cons d2 (.single d3)), ?_, mem3, ?_, ?_, ?_, fun q h1 h8 hs => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      rw [hsl ra 0x1C (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp1, ev_add, eS]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact hsl ra 0x1C (by decide)
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact hsl 8 0x18 (by decide)
    · rw [regs3]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact s.zero.symm
      simp only [upd_app, h0, hs, ite_false, restoreRegs, h1, h8]
  have finish : ∀ {n' : Machine}, Steps m n' → n'.pc = retAddr →
      (∀ x, Sep F 0x20 x 1 → n'.mem x = derNestedMem (derAdvance m.mem d rp rl r) out rp r x) →
      reg n' sp = sp0 → reg n' ra = reg m ra → reg n' 8 = reg m 8 →
      (∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg m5 q) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
        ∀ x, Sep F 0x20 x 1 → m'.mem x = derNestedMem (derAdvance m.mem d rp rl r) out rp r x := by
    intro n' st pc' hmo sp' ra' s8' kq
    refine ⟨n', st, pc', sp', fun q hq => ?_, hmo⟩
    by_cases hr' : q = ra
    · subst hr'; exact ra'
    by_cases h8 : q = 8
    · subst h8; exact s8'
    by_cases hs : q = sp
    · subst hs; rw [sp', hsp]
    have hkc : ∀ q : Fin 32, oidKeep q = true → tlvClob q = false := by decide
    have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    rw [kq q hq hr' h8 hs, K5 q (hkc q hq) hr', k3 q hs h8 h0]
  have hspa : (reg m5 sp + 4).toNat % 4 = 0 := by rw [sp5]; exact aligned_add hFa (k := 4) (by decide)
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 nst_at_12 (off' := 0x14) (by decide) hspa
  rw [sp5] at u6
  have S6 : Steps m n6 := .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d6)))))
  cases r with
  | error e =>
    have h0 : memLoad32 m5.mem (F + 4) = 0 := by rw [mem5]; exact derTlvMem_err0 e
    obtain ⟨n7, d7, u7⟩ := u6.taken hc5 0x20 nst_at_14 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.lbu hc5 nst_at_20 (off' := 0x24) (by decide)
    have eb : m5.mem (upd (reg m5) a0 (memLoad32 m5.mem (F + 4)) sp + 8) = derErrByte e := by
      rw [upd_ne (by decide) (by decide), sp5, hF8, mem5]; exact derTlvMem_err4 e
    rw [eb] at u8
    obtain ⟨n9, d9, u9⟩ := u8.sb hc5 nst_at_24 (off' := 0x28) (by decide)
    simp only [upd_app] at u9; simp +decide only [↓reduceIte] at u9
    rw [s85, tlv_zext] at u9
    have hc9 := CodeIn.store8 (v := derErrByte e) hc5 (env.sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n10, d10, u10⟩ := u9.sw hc9 nst_at_28 (off' := 0x2A) (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [s85, add_lit_zero]; exact env.hout)
    simp only [upd_app] at u10; simp +decide only [↓reduceIte] at u10
    rw [s85, add_lit_zero, h0] at u10
    have hc10 := CodeIn.store32 (v := 0) hc9 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    have hMx : ∀ x, Sep out 16 x 1 → memStore32 (memStore8 m5.mem (out + 4) (derErrByte e)) out 0 x = m5.mem x :=
      fun x hx => by
        rw [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
          memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm)]
    obtain ⟨n11, c11, pc11, mem11, sp11, ra11, s811, k11⟩ := epi u10.self hc10
      (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]) (slots hMx)
    refine finish (S6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10 c11))))) pc11 (fun x hx => ?_) sp11 ra11 s811
      (fun q hq h1 h8 hs => ?_)
    · rw [mem11]; simp only [derNestedMem]; exact memStore32_pt (memStore8_pt (fr5' x hx))
    · have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
      have h1' : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
      rw [k11 q h1 h8 hs, u10.regs]
      simp only [upd_app]
      by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext hq0
        subst this; simp; exact u5.zero.symm
      simp only [hq0, h0, h1', ite_false]
  | ok t =>
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have h0 : memLoad32 m5.mem (F + 4) = rp + BitVec.ofNat 32 t.header := by rw [mem5]; exact derTlvMem_ok0 t
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x16 nst_at_14 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]
      show (rp + BitVec.ofNat 32 t.header == 0) = false
      exact beq_false_of_ne fun h => by have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega)
    obtain ⟨n8, d8, u8⟩ := u7.lw hc5 nst_at_16 (off' := 0x18) (by decide)
      (by rw [upd_ne (by decide) (by decide), sp5]; exact aligned_add hFa (k := 8) (by decide))
    have elen : memLoad32 m5.mem (upd (reg m5) a0 (memLoad32 m5.mem (F + 4)) sp + 8) = BitVec.ofNat 32 t.len := by
      rw [upd_ne (by decide) (by decide), sp5, hF8, mem5]; exact derTlvMem_ok4 t
    rw [elen, h0] at u8
    have r8 : ∀ q, q ≠ a0 → q ≠ a1 → upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1
        (BitVec.ofNat 32 t.len) q = reg m5 q := fun q h0 h1 => by
      rw [upd_ne' h1 (by simp [upd]), upd_ne' h0 u5.zero]
    have v8 : upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1 (BitVec.ofNat 32 t.len) a0 =
        rp + BitVec.ofNat 32 t.header := by simp +decide only [upd_app, ↓reduceIte]
    have v8' : upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1 (BitVec.ofNat 32 t.len) a1 =
        BitVec.ofNat 32 t.len := by simp +decide only [upd_app, ↓reduceIte]
    obtain ⟨n9, d9, u9⟩ := u8.sw hc5 nst_at_18 (off' := 0x1A) (by decide)
      (by rw [r8 8 (by decide) (by decide), s85]; exact aligned_add env.hout (k := 8) (by decide))
    rw [r8 8 (by decide) (by decide), s85, v8] at u9
    have hc9 := CodeIn.store32 (v := rp + BitVec.ofNat 32 t.header) hc5 (env.sOC.sub (c := 8) (l := 4) (by decide))
    obtain ⟨n10, d10, u10⟩ := u9.sw hc9 nst_at_1a (off' := 0x1C) (by decide)
      (by rw [r8 8 (by decide) (by decide), s85]; exact aligned_add env.hout (k := 4) (by decide))
    rw [r8 8 (by decide) (by decide), s85, v8'] at u10
    have hc10 := CodeIn.store32 (v := BitVec.ofNat 32 t.len) hc9 (env.sOC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨n11, d11, u11⟩ := u10.sw hc10 nst_at_1c (off' := 0x1E) (by decide)
      (by rw [r8 8 (by decide) (by decide), s85]; exact aligned_add env.hout (k := 0xC) (by decide))
    rw [r8 8 (by decide) (by decide), s85, v8'] at u11
    have hc11 := CodeIn.store32 (v := BitVec.ofNat 32 t.len) hc10 (env.sOC.sub (c := 0xC) (l := 4) (by decide))
    obtain ⟨n12, d12, u12⟩ := u11.jump hc11 nst_at_1e (off' := 0x28) (by decide) (by
      rw [u11.pc, show P + BitVec.ofNat 32 0x1E + 0xA = P + BitVec.ofNat 32 0x28 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x28 (by decide)))
    obtain ⟨n13, d13, u13⟩ := u12.sw hc11 nst_at_28 (off' := 0x2A) (by decide)
      (by rw [r8 8 (by decide) (by decide), s85, add_lit_zero]; exact env.hout)
    rw [r8 8 (by decide) (by decide), s85, v8, add_lit_zero] at u13
    have hc13 := CodeIn.store32 (v := rp + BitVec.ofNat 32 t.header) hc11
      (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    have hMx : ∀ x, Sep out 16 x 1 → memStore32 (memStore32 (memStore32 (memStore32 m5.mem (out + 8)
        (rp + BitVec.ofNat 32 t.header)) (out + 4) (BitVec.ofNat 32 t.len)) (out + 0xC) (BitVec.ofNat 32 t.len)) out
        (rp + BitVec.ofNat 32 t.header) x = m5.mem x := fun x hx => by
      rw [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
        memStore32_get_sep (a := out + 0xC) (hx.sub (c := 0xC) (l := 4) (by decide)),
        memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
        memStore32_get_sep (a := out + 8) (hx.sub (c := 8) (l := 4) (by decide))]
    obtain ⟨n14, c14, pc14, mem14, sp14, ra14, s814, k14⟩ := epi u13.self hc13
      (by rw [u13.regs, r8 sp (by decide) (by decide), sp5]) (slots hMx)
    refine finish (S6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 c14))))))))
      pc14 (fun x hx => ?_) sp14 ra14 s814 (fun q hq h1 h8 hs => ?_)
    · rw [mem14]; simp only [derNestedMem]
      exact memStore32_pt (memStore32_pt (memStore32_pt (memStore32_pt (fr5' x hx))))
    · have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
      have h1' : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
      rw [k14 q h1 h8 hs, u13.regs, r8 q h0 h1']

/-- **The compiled `Der::sequence`** is `Der::nested` for tag 0x30, which it
tail-calls at `Q + 0x278`. -/
theorem derSequence_correct (m : Machine) {Q sp0 out d retAddr : Word} (hQ : Q.toNat % 2 = 0)
    (hc : CodeIn m.mem Q derSequenceCode) (env : NestEnv m.mem (Q + 0x278) sp0 out d)
    (hpc : m.pc = Q) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derNestedMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 0x30 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)))
          out (memLoad32 m.mem (d + 8))
          (derElement 0x30 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  have s0 : St m.mem Q m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc sqn_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.auipc hc sqn_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc sqn_at_8
  have k3 : ∀ q, q ≠ a2 → q ≠ t1 → reg n3 q = reg m q := fun q h2 ht => by
    rw [regs3, updz (upd_zero _ _ _) ht, updz hz h2]
  have pcN : n3.pc = Q + 0x278 := by
    rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
    rw [show Q + BitVec.ofNat 32 4 + 0x0 + 0x274 = Q + 0x278 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at Q hQ 0x278 (by decide))
  obtain ⟨m4, c4, pc4, sp4, k4, f4⟩ := derNested_correct n3 (tag := 0x30) (by rw [mem3]; exact env) pcN
    (by rw [k3 sp (by decide) (by decide), hsp]) (by rw [k3 a0 (by decide) (by decide), ha0])
    (by rw [k3 a1 (by decide) (by decide), ha1])
    (by rw [regs3, updz (upd_zero _ _ _) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl)
    (by decide) (by rw [k3 ra (by decide) (by decide), hra]) hret
  rw [mem3] at f4
  exact ⟨m4, .cons d1 (.cons d2 (.cons d3 c4)), pc4, sp4, fun q hq => by
    rw [k4 q hq, k3 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))],
    f4⟩

end C3.RV32
