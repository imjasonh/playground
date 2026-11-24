import C3BootProofs.Proofs.DerReaders

/-!
# `Der::optional`, as compiled

`Der::optional` reads the next element through `Der::tlv` when the next tag
is the one it expects, and copies the element's `Tlv` into its
`Result<Option<Tlv>, Error>` with `memcpy`. Otherwise it returns
`Ok(None)` and leaves the reader where it was. `memcpy`'s 16 bytes of
scratch lie below the 0x20-byte frame, so the stack region is 0x30 bytes.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem dopt_at_0 : fetchRel derOptionalCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem dopt_at_2 : fetchRel derOptionalCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem dopt_at_4 : fetchRel derOptionalCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem dopt_at_6 : fetchRel derOptionalCode 0x6 = some (.load .lw a3 a1 0xC, 2) := by decide
theorem dopt_at_8 : fetchRel derOptionalCode 0x8 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dopt_at_a : fetchRel derOptionalCode 0xA = some (.branch .beq a3 x0 0x2E, 2) := by decide
theorem dopt_at_c : fetchRel derOptionalCode 0xC = some (.load .lw a0 a1 0x8, 2) := by decide
theorem dopt_at_e : fetchRel derOptionalCode 0xE = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem dopt_at_12 : fetchRel derOptionalCode 0x12 = some (.branch .bne a0 a2 0x26, 4) := by decide
theorem dopt_at_16 : fetchRel derOptionalCode 0x16 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem dopt_at_18 : fetchRel derOptionalCode 0x18 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dopt_at_1c : fetchRel derOptionalCode 0x1C = some (.jalr ra ra 0x36A, 4) := by decide
theorem dopt_at_20 : fetchRel derOptionalCode 0x20 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem dopt_at_22 : fetchRel derOptionalCode 0x22 = some (.branch .beq a0 x0 0x20, 2) := by decide
theorem dopt_at_24 : fetchRel derOptionalCode 0x24 = some (.aluImm .add a0 (8 : Fin 32) 0x4, 4) := by decide
theorem dopt_at_28 : fetchRel derOptionalCode 0x28 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem dopt_at_2a : fetchRel derOptionalCode 0x2A = some (.aluImm .add a2 x0 0x14, 2) := by decide
theorem dopt_at_2c : fetchRel derOptionalCode 0x2C = some (.auipc ra 0xA000, 4) := by decide
theorem dopt_at_30 : fetchRel derOptionalCode 0x30 = some (.jalr ra ra 0x48E, 4) := by decide
theorem dopt_at_34 : fetchRel derOptionalCode 0x34 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem dopt_at_36 : fetchRel derOptionalCode 0x36 = some (.jal x0 0x16, 2) := by decide
theorem dopt_at_38 : fetchRel derOptionalCode 0x38 = some (.store .sb (8 : Fin 32) x0 0x0, 4) := by decide
theorem dopt_at_3c : fetchRel derOptionalCode 0x3C = some (.store .sw (8 : Fin 32) x0 0x4, 4) := by decide
theorem dopt_at_40 : fetchRel derOptionalCode 0x40 = some (.jal x0 0x10, 2) := by decide
theorem dopt_at_42 : fetchRel derOptionalCode 0x42 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dopt_at_46 : fetchRel derOptionalCode 0x46 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem dopt_at_4a : fetchRel derOptionalCode 0x4A = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem dopt_at_4c : fetchRel derOptionalCode 0x4C = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem dopt_at_50 : fetchRel derOptionalCode 0x50 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem dopt_at_52 : fetchRel derOptionalCode 0x52 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem dopt_at_54 : fetchRel derOptionalCode 0x54 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem dopt_at_56 : fetchRel derOptionalCode 0x56 = some (.jalr x0 ra 0x0, 2) := by decide
theorem doptSave_end : blockEnd derOptionalCode 2 (saveBlock dcPs) = some 6 := by decide
theorem doptRestore_end : blockEnd derOptionalCode 0x50 (restoreBlock dcPs) = some (0x50 + 4) := by decide
end

/-- `Der::optional`'s choice for the unread bytes `L`: `none` when the next
tag isn't `tag`, else `Der::tlv`'s result. -/
def derOptRes (tag : Nat) : Bytes → Option (Except DerError DerTlv)
  | [] => none
  | b :: rest => if b = tag then some (derTlv (b :: rest)) else none

/-- What `Der::optional` stores at `out`, a `Result<Option<Tlv>, Error>`,
and how it moves the reader at `d`. A `Tlv` is copied from the frame at
`F + 4`, so its three padding bytes are the frame's. -/
def derOptMem (M : Word → BitVec 8) (out F d rp rl : Word) : Option (Except DerError DerTlv) → Word → BitVec 8
  | none => memStore32 (memStore8 M out 0) (out + 4) 0
  | some (.error e) => memStore8 (memStore8 M (out + 1) (derErrByte e)) out 1
  | some (.ok t) => memStore8 (copyBytes (derTlvMem M (F + 4) d rp rl (.ok t)) (out + 4) (F + 4) 0x14) out 0

theorem derTlvMem_pt {M M' : Word → BitVec 8} {o d rp rl x : Word} (r : Except DerError DerTlv)
    (h : M x = M' x) : derTlvMem M o d rp rl r x = derTlvMem M' o d rp rl r x := by
  cases r <;> simp only [derTlvMem]
  · exact memStore8_pt (memStore32_pt h)
  · exact memStore8_pt (memStore32_pt (memStore32_pt (memStore32_pt (memStore32_pt (memStore32_pt
      (memStore32_pt h))))))

theorem copyBytes_pt {M M' : Word → BitVec 8} {dst src x : Word} {k : Nat} (h1 : M x = M' x)
    (h2 : (x - dst).toNat < k → M (src + (x - dst)) = M' (src + (x - dst))) :
    copyBytes M dst src k x = copyBytes M' dst src k x := by
  unfold copyBytes; split
  · exact h2 ‹_›
  · exact h1

/-- Where `Der::optional` runs: its code and its callees', its stack region
of 0x30 bytes below `sp0`, the 0x18-byte result at `out`, and the reader at
`d`, apart from what each must not touch. -/
structure OptEnv (M : Word → BitVec 8) (P sp0 out d : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P derOptionalCode
  tlv : CodeIn M (P + 0xFFFFF810) derTlvCode
  mcs : CodeIn M (P + 0xBFD6) memcpyStubCode
  mcb : CodeIn M (P + 0xBFDE) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x30 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hd : d.toNat % 4 = 0
  how : out.toNat + 0x18 < 2 ^ 32
  sFC : Sep (sp0 + 0xFFFFFFD0) 0x30 P derOptionalCode.length
  sFT : Sep (sp0 + 0xFFFFFFD0) 0x30 (P + 0xFFFFF810) derTlvCode.length
  sFS : Sep (sp0 + 0xFFFFFFD0) 0x30 (P + 0xBFD6) memcpyStubCode.length
  sFB : Sep (sp0 + 0xFFFFFFD0) 0x30 (P + 0xBFDE) memcpyBodyCode.length
  sOC : Sep out 0x18 P derOptionalCode.length
  sOB : Sep out 0x18 (P + 0xBFDE) memcpyBodyCode.length
  sDC : Sep (d + 8) 8 P derOptionalCode.length
  sDT : Sep (d + 8) 8 (P + 0xFFFFF810) derTlvCode.length
  sDS : Sep (d + 8) 8 (P + 0xBFD6) memcpyStubCode.length
  sDB : Sep (d + 8) 8 (P + 0xBFDE) memcpyBodyCode.length
  sOF : Sep out 0x18 (sp0 + 0xFFFFFFD0) 0x30
  sDF : Sep (d + 8) 8 (sp0 + 0xFFFFFFD0) 0x30
  sOD : Sep out 0x18 (d + 8) 8
  sRF : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (sp0 + 0xFFFFFFD0) 0x30
  hrp : 0 < (memLoad32 M (d + 8)).toNat
  hrw : (memLoad32 M (d + 8)).toNat + (memLoad32 M (d + 0xC)).toNat < 2 ^ 32

/-- The registers `Der::optional` may change: `t0` to `t6` and `a0` to
`a7`. It restores `ra`, `sp`, and `s0`. -/
def optKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Der::optional`**: with the reader at `d`, whose unread
bytes start at `rp` and number `rl`, and the tag in `a2`, it stores
`derOptMem` of `derOptRes` of those bytes, and moves the reader past an
element it reads. -/
theorem derOptional_correct (m : Machine) {P sp0 out d retAddr : Word} {tag : Nat}
    (env : OptEnv m.mem P sp0 out d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (ha2 : reg m a2 = BitVec.ofNat 32 tag) (htag : tag < 256)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, optKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFD0) 0x30 x 1 →
        m'.mem x = derOptMem m.mem out (sp0 + 0xFFFFFFE0) d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derOptRes tag (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  have hrp0 := env.hrp; have hrw := env.hrw; have sRF := env.sRF
  generalize hRP : memLoad32 m.mem (d + 8) = rp at hrp0 hrw sRF ⊢
  generalize hRL : memLoad32 m.mem (d + 0xC) = rl at hrw sRF ⊢
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFD0 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sFT := env.sFT; have sFS := env.sFS; have sFB := env.sFB
  have sOF := env.sOF; have sDF := env.sDF
  rw [hG] at sFC sFT sFS sFB sOF sDF sRF ⊢
  rw [hF]
  have hGF : G + 0x10 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFFD0) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x10) (by decide)
  have hGw : G.toNat + 0x30 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 4294967248 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x10 := by
    rw [← hGF, BitVec.toNat_add, show (0x10 : Word).toNat = 0x10 from rfl]; omega
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  -- the frame is the region's top 0x20 bytes
  have inF : ∀ {x : Word}, Sep G 0x30 x 1 → Sep F 0x20 x 1 := fun hx => by
    rw [← hGF]; exact hx.sub (c := 0x10) (l := 0x20) (by decide)
  have sFC' : Sep F 0x20 P derOptionalCode.length := by rw [← hGF]; exact sFC.sub (c := 0x10) (l := 0x20) (by decide)
  have sFT' : Sep F 0x20 (P + 0xFFFFF810) derTlvCode.length := by
    rw [← hGF]; exact sFT.sub (c := 0x10) (l := 0x20) (by decide)
  have sDF' : Sep (d + 8) 8 F 0x20 := by rw [← hGF]; exact sDF.subR (c := 0x10) (l := 0x20) (by decide)
  have sOF' : Sep out 0x18 F 0x20 := by rw [← hGF]; exact sOF.subR (c := 0x10) (l := 0x20) (by decide)
  have sRF' : Sep rp rl.toNat F 0x20 := by rw [← hGF]; exact sRF.subR (c := 0x10) (l := 0x20) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep F 0x20 b code'.length → (∀ x, Sep F 0x20 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod dopt_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock dcPs) u1 env.cod doptSave_end (saveBlock_ok _ dcPs _ fun p hp => by
    rw [sp1]
    simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC' (by decide)⟩
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC' (by decide)⟩)
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
  -- the bytes below the slots, `F` to `F + 0x18`, keep their entry values
  have frLo : ∀ k, k < 0x18 → Msv (F + BitVec.ofNat 32 k) = m.mem (F + BitVec.ofNat 32 k) := fun k hk => by
    rw [← hMsv]
    exact saveMem_outside dcPs fun p hp => by
      simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact sep_offsets F (c := 0x1C) (n := 4) (d := k) (k := 1) (.inr (by omega)) (by omega) (by omega)
      · exact sep_offsets F (c := 0x18) (n := 4) (d := k) (k := 1) (.inr (by omega)) (by omega) (by omega)
  have hslv : ∀ r o, (r, o) ∈ dcPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have hcS : CodeIn Msv P derOptionalCode := cIn env.cod sFC' frSv
  have eD8 : memLoad32 Msv (d + 8) = rp := by
    rw [← hRP]; exact memLoad32_congr fun j hj => frSv _ (sDF'.symm.subR (c := j) (l := 1) (by omega))
  have eDC : memLoad32 Msv (d + 0xC) = rl := by
    rw [← hRL]; exact memLoad32_congr fun j hj => frSv _ (by
      rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact sDF'.symm.subR (by omega))
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by
    rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  obtain ⟨m3, d3, u3⟩ := u2.self.lw hcS dopt_at_6 (off' := 8) (by decide)
    (by rw [r2 a1 (by decide), ha1]; exact aligned_add env.hd (k := 0xC) (by decide))
  rw [r2 a1 (by decide), ha1, eDC] at u3
  obtain ⟨m4, d4, u4⟩ := u3.self.alu hcS dopt_at_8 (off' := 0xA) (by decide)
  have r4 : ∀ q, q ≠ a3 → q ≠ 8 → reg m4 q = reg m2 q := fun q h3 h8 => by
    rw [u4.regs, upd_ne' h8 u3.self.zero, u3.regs, upd_ne' h3 u2.self.zero]
  have v4a3 : reg m4 a3 = rl := by
    rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
  have v48 : reg m4 8 = out := by
    rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]
    simp only [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [r2 a0 (by decide), ha0]; exact zw out
  have sp4 : reg m4 sp = F := by rw [r4 sp (by decide) (by decide), sp2]
  have K4 : ∀ q, optKeep q = true → q ≠ sp → q ≠ 8 → reg m4 q = reg m q := fun q hq hs h8 => by
    rw [r4 q (fun e => by subst e; exact absurd hq (by decide)) h8, r2 q hs]
  have S4 : Steps m m4 := .cons d1 (c2.trans (.cons d3 (.single d4)))
  -- the epilogue, from 0x50
  have slotR : ∀ {Mx : Word → BitVec 8}, (∀ k, 0x18 ≤ k → k < 0x20 → Mx (F + BitVec.ofNat 32 k) =
      Msv (F + BitVec.ofNat 32 k)) → memLoad32 Mx (F + 0x1C) = reg m ra ∧ memLoad32 Mx (F + 0x18) = reg m 8 := by
    intro Mx h
    refine ⟨?_, ?_⟩
    · rw [← hslv ra 0x1C (by decide)]
      apply memLoad32_congr; intro j hj
      rw [show F + 0x1C + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x1C + j) by
        rw [show (0x1C : Word) = BitVec.ofNat 32 0x1C from rfl, add_ofNat_assoc]]
      exact h _ (by omega) (by omega)
    · rw [← hslv 8 0x18 (by decide)]
      apply memLoad32_congr; intro j hj
      rw [show F + 0x18 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x18 + j) by
        rw [show (0x18 : Word) = BitVec.ofNat 32 0x18 from rfl, add_ofNat_assoc]]
      exact h _ (by omega) (by omega)
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m4 n → St Mx P n 0x50 (reg n) →
      CodeIn Mx P derOptionalCode → (∀ k, 0x18 ≤ k → k < 0x20 → Mx (F + BitVec.ofNat 32 k) =
        Msv (F + BitVec.ofNat 32 k)) → reg n sp = F → (∀ q, optKeep q = true → q ≠ sp → q ≠ 8 → q ≠ ra →
        reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, optKeep q = true → reg n' q = reg m q := by
    intro Mx n S s hc hsl rsp kq
    obtain ⟨sR, s8⟩ := slotR hsl
    obtain ⟨n', c', pc', mem', sp', ra', s8', k'⟩ := derCall_epi s hc doptRestore_end dopt_at_54 dopt_at_56 hFa rsp
      (by rw [sR, hra]) hret
    refine ⟨n', S4.trans (S.trans c'), pc', mem', by rw [sp', eS], fun q hq => ?_⟩
    by_cases hr : q = ra
    · subst hr; rw [ra', hra]
    by_cases h8 : q = 8
    · subst h8; rw [s8', s8]
    by_cases hs : q = sp
    · subst hs; rw [sp', eS, hsp]
    rw [k' q hr h8 hs, kq q hq hs h8 hr]
  -- `Ok(None)` at 0x38
  have none_ : ∀ {n : Machine}, Steps m4 n → St Msv P n 0x38 (reg n) → reg n 8 = out → reg n sp = F →
      (∀ q, optKeep q = true → q ≠ sp → q ≠ 8 → q ≠ ra → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧ (∀ q, optKeep q = true → reg n' q = reg m q) ∧
        ∀ x, Sep G 0x30 x 1 → n'.mem x = derOptMem m.mem out F d rp rl none x := by
    intro n S s r8 rsp kq
    obtain ⟨n1, e1, w1⟩ := s.sb hcS dopt_at_38 (off' := 0x3C) (by decide)
    rw [r8, add_lit_zero, s.zero] at w1
    have hc1 := CodeIn.store8 (v := (0 : Word).extractLsb' 0 8) hcS
      (env.sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨n2, e2, w2⟩ := w1.sw hc1 dopt_at_3c (off' := 0x40) (by decide)
      (by rw [r8]; exact aligned_add env.hout (k := 4) (by decide))
    rw [r8, s.zero] at w2
    have hc2 := CodeIn.store32 (v := 0) hc1 (env.sOC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨n3, e3, w3⟩ := w2.jump hc2 dopt_at_40 (off' := 0x50) (by decide) (by
      rw [w2.pc, show P + BitVec.ofNat 32 0x40 + 0x10 = P + BitVec.ofNat 32 0x50 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x50 (by decide)))
    have hout8 : ∀ k, 0x18 ≤ k → k < 0x20 → Sep out 0x18 (F + BitVec.ofNat 32 k) 1 := fun k h1 h2 =>
      sOF'.subR (c := k) (l := 1) (by omega)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons e1 (.cons e2 (.single e3)))) w3.self hc2
      (fun k h1 h2 => by
        rw [memStore32_get_sep (a := out + 4) ((hout8 k h1 h2).sub (c := 4) (l := 4) (by decide)),
          memStore8_ne fun e' => hout8 k h1 h2 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm)])
      (by rw [w3.regs]; exact rsp) (fun q hq hs h8 hr => by rw [w3.regs]; exact kq q hq hs h8 hr)
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem']; simp only [derOptMem]
    exact memStore32_pt (memStore8_pt (frSv x (inF hx)))
  have r4' : ∀ q, q ≠ a3 → q ≠ 8 → q ≠ sp → reg m4 q = reg m q := fun q h3 h8 hs => by rw [r4 q h3 h8, r2 q hs]
  by_cases hl0 : rl = 0
  · obtain ⟨n5, d5, u5⟩ := u4.self.taken hcS 0x38 dopt_at_a (by decide) (by rw [v4a3, u4.self.zero, hl0]; rfl)
    obtain ⟨n', S', pc', sp', k', mem'⟩ := none_ (.single d5) u5.self (by rw [u5.regs, v48]) (by rw [u5.regs, sp4])
      (fun q hq hs h8 _ => by rw [u5.regs]; exact K4 q hq hs h8)
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem' x hx, hl0]; rfl
  obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hcS 0xC dopt_at_a (by decide) (by
    rw [v4a3, u4.self.zero]; exact beq_false_of_ne hl0)
  have hA1 : reg n5 a1 = d := by rw [u5.regs, r4' a1 (by decide) (by decide) (by decide), ha1]
  obtain ⟨n6, d6, u6⟩ := u5.self.lw hcS dopt_at_c (off' := 0xE) (by decide)
    (by rw [hA1]; exact aligned_add env.hd (k := 8) (by decide))
  rw [hA1, eD8] at u6
  obtain ⟨n7, d7, u7⟩ := u6.self.lbu hcS dopt_at_e (off' := 0x12) (by decide)
  obtain ⟨j, hj⟩ : ∃ j, rl.toNat = j + 1 := ⟨rl.toNat - 1, by
    have : rl.toNat ≠ 0 := fun h => hl0 (BitVec.eq_of_toNat_eq h); omega⟩
  have eRP : Msv rp = m.mem rp := frSv rp (by
    have := sRF'.symm.subR (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
  have v7a0 : reg n7 a0 = (m.mem rp).zeroExtend 32 := by
    rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, eRP]
  have r7 : ∀ q, q ≠ a0 → q ≠ a3 → q ≠ 8 → q ≠ sp → reg n7 q = reg m q := fun q h0 h3 h8 hs => by
    rw [u7.regs, upd_ne' h0 u6.self.zero, u6.regs, upd_ne' h0 u5.self.zero, u5.regs, r4' q h3 h8 hs]
  have v78 : reg n7 8 = out := by
    rw [u7.regs, upd_ne' (by decide) u6.self.zero, u6.regs, upd_ne' (by decide) u5.self.zero, u5.regs, v48]
  have sp7 : reg n7 sp = F := by
    rw [u7.regs, upd_ne' (by decide) u6.self.zero, u6.regs, upd_ne' (by decide) u5.self.zero, u5.regs, sp4]
  have K7 : ∀ q, optKeep q = true → q ≠ sp → q ≠ 8 → reg n7 q = reg m q := fun q hq hs h8 =>
    r7 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide)) h8 hs
  have S7 : Steps m4 n7 := .cons d5 (.cons d6 (.single d7))
  have hL : memBytes m.mem rp rl.toNat = (m.mem rp).toNat :: memBytes m.mem (rp + 1) j := by
    rw [hj, memBytes_succ]
  by_cases htn : (m.mem rp).toNat ≠ tag
  · obtain ⟨n8, d8, u8⟩ := u7.self.taken hcS 0x38 dopt_at_12 (by decide) (by
      rw [v7a0, r7 a2 (by decide) (by decide) (by decide) (by decide), ha2]
      simp only [branchTaken, bne_iff_ne, ne_eq]
      intro h; apply htn
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.mem rp).isLt; omega), ofNat_tn (by omega)] at this)
    obtain ⟨n', S', pc', sp', k', mem'⟩ := none_ (S7.trans (.single d8)) u8.self (by rw [u8.regs, v78])
      (by rw [u8.regs, sp7]) (fun q hq hs h8 _ => by rw [u8.regs]; exact K7 q hq hs h8)
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem' x hx, hL]; simp only [derOptRes, htn, ↓reduceIte]
  have ht : (m.mem rp).toNat = tag := Decidable.of_not_not htn
  clear htn
  obtain ⟨n8, d8, u8⟩ := u7.self.notTaken hcS 0x16 dopt_at_12 (by decide) (by
    rw [v7a0, r7 a2 (by decide) (by decide) (by decide) (by decide), ha2]
    show ((m.mem rp).zeroExtend 32 != BitVec.ofNat 32 tag) = false
    have heq : ((m.mem rp).zeroExtend 32 : Word) = BitVec.ofNat 32 tag := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.mem rp).isLt; omega), ofNat_tn (by omega), ht]
    rw [heq]; exact bne_self_eq_false _)
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hcS dopt_at_16 (off' := 0x18) (by decide)
  obtain ⟨n10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hcS dopt_at_18 dopt_at_1c (cb := P + 0xFFFFF810)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF810 (by decide))
  have r10 := PEnv.reg1 regs10 u9.self.zero
  have hF4 : F + 4 = F + BitVec.ofNat 32 4 := rfl
  have v9 : ∀ q, q ≠ a0 → reg n9 q = reg n7 q := fun q h => by
    rw [u9.regs, upd_ne' h u8.self.zero, u8.regs]
  obtain ⟨n11, c11, pc11, mem11, k11⟩ := derTlv_correct n10 (out := F + 4) (d := d)
    (even_at P env.hP 0xFFFFF810 (by decide))
    (by rw [mem10]; exact cIn env.tlv sFT' frSv) pc10
    (by rw [r10 a0 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, u8.regs, sp7])
    (by rw [r10 a1 (by decide), v9 a1 (by decide), r7 a1 (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [regs10]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x18 + 8) (by decide)))
    (by rw [hF4]; exact aligned_add hFa (by decide)) env.hd
    (by rw [hF4]; exact sFT'.sub (by decide)) env.sDT
  rw [mem10, eD8, eDC] at mem11
  have eL : memBytes Msv rp rl.toNat = memBytes m.mem rp rl.toNat :=
    memBytes_congr fun i hi => frSv _ (sRF'.symm.subR (c := i) (l := 1) (by omega))
  rw [eL] at mem11
  have hspec : derOptRes tag (memBytes m.mem rp rl.toNat) = some (derTlv (memBytes m.mem rp rl.toNat)) := by
    rw [hL]; simp only [derOptRes, ht, ↓reduceIte]
  rw [hspec]
  generalize hr : derTlv (memBytes m.mem rp rl.toNat) = r at mem11
  have K11 : ∀ q, optKeep q = true → q ≠ sp → q ≠ 8 → q ≠ ra → reg n11 q = reg m q := fun q hq hs h8 hra' => by
    have hc : tlvClob q = false := by
      revert hq; revert q; decide
    have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    rw [k11 q hc, r10 q hra', v9 q h0]; exact K7 q hq hs h8
  have r11 : ∀ q, tlvClob q = false → q ≠ ra → q ≠ a0 → reg n11 q = reg n7 q := fun q hc hra' h0 => by
    rw [k11 q hc, r10 q hra', v9 q h0]
  have sp11 : reg n11 sp = F := by rw [r11 sp (by decide) (by decide) (by decide), sp7]
  have s811 : reg n11 8 = out := by rw [r11 8 (by decide) (by decide) (by decide), v78]
  have hc11 : CodeIn (derTlvMem Msv (F + 4) d rp rl r) P derOptionalCode := fun i hi => by
    rw [derCall_outside r frSv (sFC'.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have u11 : St (derTlvMem Msv (F + 4) d rp rl r) P n11 0x20 (reg n11) := ⟨by rw [pc11], mem11, fun _ => rfl⟩
  have S11 : Steps m4 n11 := S7.trans (.cons d8 (.cons d9 (c10.trans c11)))
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  -- the frame's slots after the call
  have slot11 : ∀ k, 0x18 ≤ k → k < 0x20 →
      derTlvMem Msv (F + 4) d rp rl r (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) := fun k h1 h2 => by
    rw [derTlvMem_outside r (by
        rw [hF4]; exact sep_offsets F (c := 4) (n := 17) (d := k) (k := 1) (.inl (by omega)) (by omega) (by omega)),
      derAdvance_outside r (sDF'.subR (c := k) (l := 1) (by omega))]
  have outF : ∀ k, 0x18 ≤ k → k < 0x20 → Sep out 0x18 (F + BitVec.ofNat 32 k) 1 := fun k h1 h2 =>
    sOF'.subR (c := k) (l := 1) (by omega)
  obtain ⟨n12, d12, u12⟩ := u11.lw hc11 dopt_at_20 (off' := 0x22) (by decide)
    (by rw [sp11]; exact aligned_add hFa (k := 4) (by decide))
  rw [sp11] at u12
  cases r with
  | error e =>
    obtain ⟨n13, d13, u13⟩ := u12.taken hc11 0x42 dopt_at_22 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [derTlvMem_err0]; rfl)
    obtain ⟨n14, d14, u14⟩ := u13.lbu hc11 dopt_at_42 (off' := 0x46) (by decide)
    rw [upd_ne (by decide) (by decide), sp11, hF8, derTlvMem_err4] at u14
    obtain ⟨n15, d15, u15⟩ := u14.sb hc11 dopt_at_46 (off' := 0x4A) (by decide)
    simp only [upd_app] at u15; simp +decide only [↓reduceIte] at u15
    rw [s811, tlv_zext] at u15
    have hc15 := CodeIn.store8 (v := derErrByte e) hc11 (env.sOC.sub (c := 1) (l := 1) (by decide))
    obtain ⟨n16, d16, u16⟩ := u15.aluImm hc15 dopt_at_4a (off' := 0x4C) (by decide)
    obtain ⟨n17, d17, u17⟩ := u16.sb hc15 dopt_at_4c (off' := 0x50) (by decide)
    simp only [upd_app] at u17; simp +decide only [↓reduceIte] at u17
    rw [s811, add_lit_zero] at u17
    have hc17 := CodeIn.store8 (v := (aluEval .add 0 1 : Word).extractLsb' 0 8) hc15
      (env.sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S11.trans (.cons d12 (.cons d13 (.cons d14 (.cons d15
      (.cons d16 (.single d17))))))) u17.self hc17
      (fun k h1 h2 => by
        rw [memStore8_ne fun e' => outF k h1 h2 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm),
          memStore8_ne fun e' => outF k h1 h2 1 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
          slot11 k h1 h2])
      (by rw [u17.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp11)
      (fun q hq hs h8 hr' => by
        rw [u17.regs]
        have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp [upd]; exact hz.symm
        simp only [upd_app, hq0, h0, ite_false]; exact K11 q hq hs h8 hr')
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem']; simp only [derOptMem]
    exact memStore8_pt (memStore8_pt (by rw [derCall_outside _ frSv (inF hx)]; rfl))
  | ok t =>
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derTlv_bound hr; rwa [memBytes_length] at this
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hnz : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega
    obtain ⟨n13, d13, u13⟩ := u12.notTaken hc11 0x24 dopt_at_22 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [derTlvMem_ok0]
      exact beq_false_of_ne hnz)
    obtain ⟨n14, d14, u14⟩ := u13.self.aluImm hc11 dopt_at_24 (off' := 0x28) (by decide)
    obtain ⟨n15, d15, u15⟩ := u14.self.aluImm hc11 dopt_at_28 (off' := 0x2A) (by decide)
    obtain ⟨n16, d16, u16⟩ := u15.self.aluImm hc11 dopt_at_2a (off' := 0x2C) (by decide)
    have r16 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n16 q = reg n11 q := fun q h0 h1 h2 => by
      rw [u16.regs, upd_ne' h2 u15.self.zero, u15.regs, upd_ne' h1 u14.self.zero, u14.regs,
        upd_ne' h0 u13.self.zero, u13.regs, upd_ne' h0 u11.zero]
    have v16 : reg n16 a0 = out + 4 ∧ reg n16 a1 = F + 4 ∧ reg n16 a2 = BitVec.ofNat 32 0x14 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [u16.regs, upd_ne' (by decide) u15.self.zero, u15.regs, upd_ne' (by decide) u14.self.zero, u14.regs]
        simp +decide only [upd_app, ↓reduceIte]; rw [u13.regs, upd_ne' (by decide) u11.zero, s811]; rfl
      · rw [u16.regs, upd_ne' (by decide) u15.self.zero, u15.regs]
        simp +decide only [upd_app, ↓reduceIte]; rw [u14.regs, upd_ne' (by decide) u13.self.zero, u13.regs,
          upd_ne' (by decide) u11.zero, sp11]; rfl
      · rw [u16.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u15.self.zero]; rfl
    obtain ⟨v16a0, v16a1, v16a2⟩ := v16
    obtain ⟨n17, c17, pc17, mem17, regs17⟩ := u16.self.callRa hc11 dopt_at_2c dopt_at_30 (cb := P + 0xBFD6)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xBFD6 (by decide))
    have r17 := PEnv.reg1 regs17 u16.self.zero
    have sp17 : reg n17 sp = F := by
      rw [r17 sp (by decide), r16 sp (by decide) (by decide) (by decide), sp11]
    have eGF : F + 0xFFFFFFF0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
    have hF4G : F + 4 = G + BitVec.ofNat 32 0x14 := by rw [← hGF, BitVec.add_assoc]; rfl
    have sDst : Sep (out + 4) 0x14 G 16 := by
      have := (sOF.sub (c := 4) (l := 0x14) (by decide)).subR (c := 0) (l := 16) (by decide)
      rwa [add_ofNat_zero] at this
    have sSrc : Sep (F + 4) 0x14 G 16 := by
      rw [hF4G]
      have := sep_offsets G (c := 0x14) (n := 0x14) (d := 0) (k := 16) (.inr (by decide)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have sDS : Sep (out + 4) 0x14 (F + 4) 0x14 := by
      rw [hF4G]; exact (sOF.sub (c := 4) (l := 0x14) (by decide)).subR (c := 0x14) (l := 0x14) (by decide)
    have hcB : CodeIn (derTlvMem Msv (F + 4) d rp rl (.ok t)) (P + 0xBFDE) memcpyBodyCode := fun i hi => by
      rw [derCall_outside (.ok t) frSv (inF (sFB.subR (c := i) (l := 1) (by omega))),
        derAdvance_outside (.ok t) (env.sDB.subR (c := i) (l := 1) (by omega))]
      exact env.mcb i hi
    have hcS' : CodeIn (derTlvMem Msv (F + 4) d rp rl (.ok t)) (P + 0xBFD6) memcpyStubCode := fun i hi => by
      rw [derCall_outside (.ok t) frSv (inF (sFS.subR (c := i) (l := 1) (by omega))),
        derAdvance_outside (.ok t) (env.sDS.subR (c := i) (l := 1) (by omega))]
      exact env.mcs i hi
    obtain ⟨n18, c18, pc18, sp18, a018, mem18, k18⟩ := memcpy_correct n17 (P + 0xBFD6)
      (P + BitVec.ofNat 32 (0x2C + 8)) (out + 4) (F + 4) 0x14
      (fun i hi => by show n17.mem _ = _; rw [mem17]; exact hcS' i hi)
      (even_at P env.hP 0xBFD6 (by decide)) pc17
      (by rw [r17 a0 (by decide), v16a0]) (by rw [r17 a1 (by decide), v16a1]) (by rw [r17 a2 (by decide), v16a2])
      (by rw [regs17]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x2C + 8) (by decide)))
      (by
        rw [mem17, sp17, eGF, show P + 0xBFD6 + 8 = P + 0xBFDE by rw [BitVec.add_assoc]; rfl]
        exact ⟨hcB, env.sOB.sub (c := 4) (l := 0x14) (by decide),
          by have := sFB.sub (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this,
          sDst, sSrc, sDS, hGa, by omega,
          by rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; have := env.how; omega,
          by rw [hF4G, BitVec.toNat_add, ofNat_tn (by decide)]; omega⟩)
    rw [mem17, sp17, eGF] at mem18
    -- after `memcpy`, memory outside its scratch is the copy
    have cpOut : ∀ y, Sep G 16 y 1 → n18.mem y =
        copyBytes (derTlvMem Msv (F + 4) d rp rl (.ok t)) (out + 4) (F + 4) 0x14 y := mem18
    have hc18 : CodeIn n18.mem P derOptionalCode := fun i hi => by
      have hs := (sFC.sub (c := 0) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega)
      rw [add_ofNat_zero] at hs
      rw [cpOut _ hs, copyBytes_sep (dst := out + 4) ((env.sOC.sub (c := 4) (l := 0x14) (by decide)).subR (c := i) (l := 1) (by omega))
        (Nat.le_refl _)]
      exact hc11 i hi
    have u18 : St n18.mem P n18 0x34 (reg n18) := ⟨by rw [pc18], rfl, fun _ => rfl⟩
    obtain ⟨n19, d19, u19⟩ := u18.aluImm hc18 dopt_at_34 (off' := 0x36) (by decide)
    obtain ⟨n20, d20, u20⟩ := u19.jump hc18 dopt_at_36 (off' := 0x4C) (by decide) (by
      rw [u19.pc, show P + BitVec.ofNat 32 0x36 + 0x16 = P + BitVec.ofNat 32 0x4C by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x4C (by decide)))
    have K18 : ∀ q, optKeep q = true → q ≠ sp → q ≠ 8 → q ≠ ra → reg n18 q = reg m q := fun q hq hs h8 hr' => by
      have nq : ∀ r : Fin 32, r.val ∈ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] → q ≠ r :=
        fun r hr e => by subst e; simp only [optKeep, hr, not_true_eq_false, decide_false] at hq; exact Bool.noConfusion hq
      have h0 : q ≠ a0 := nq a0 (by decide)
      rw [k18 q (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq a4 (by decide)) (nq a5 (by decide))
        (nq a6 (by decide)) (nq a7 (by decide)) (nq t0 (by decide)) (nq t1 (by decide)) (nq 7 (by decide))
        (nq 28 (by decide)) (nq 29 (by decide)) (nq 30 (by decide)) hs, r17 q hr',
        r16 q h0 (nq a1 (by decide)) (nq a2 (by decide))]
      exact K11 q hq hs h8 hr'
    have s818 : reg n18 8 = out := by
      rw [k18 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r17 8 (by decide),
        r16 8 (by decide) (by decide) (by decide), s811]
    have sp18' : reg n18 sp = F := by rw [sp18, sp17]
    obtain ⟨n21, d21, u21⟩ := u20.sb hc18 dopt_at_4c (off' := 0x50) (by decide)
    simp only [upd_app] at u21; simp +decide only [↓reduceIte] at u21
    rw [s818, add_lit_zero] at u21
    have hc21 := CodeIn.store8 (v := (aluEval .add 0 0 : Word).extractLsb' 0 8) hc18
      (env.sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S11.trans (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16
      (c17.trans (c18.trans (.cons d19 (.cons d20 (.single d21))))))))))) u21.self hc21
      (fun k h1 h2 => by
        have hFk : Sep G 16 (F + BitVec.ofNat 32 k) 1 := by
          rw [← hGF, show G + 0x10 + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x10 + k) by
            rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, add_ofNat_assoc]]
          have := sep_offsets G (c := 0) (n := 16) (d := 0x10 + k) (k := 1) (.inl (by omega)) (by omega) (by omega)
          rwa [add_ofNat_zero] at this
        rw [memStore8_ne fun e' => outF k h1 h2 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm),
          cpOut _ hFk, copyBytes_sep (dst := out + 4) ((outF k h1 h2).sub (c := 4) (l := 0x14) (by decide)) (Nat.le_refl _), slot11 k h1 h2])
      (by rw [u21.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp18')
      (fun q hq hs h8 hr' => by
        rw [u21.regs]
        have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp [upd]; exact hz.symm
        simp only [upd_app, hq0, h0, ite_false]; exact K18 q hq hs h8 hr')
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    have hxG : Sep G 16 x 1 := hx.sub (c := 0) (l := 16) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    rw [mem']; simp only [derOptMem]
    refine memStore8_pt ?_
    rw [cpOut x hxG]
    refine copyBytes_pt (derTlvMem_pt _ (frSv x (inF hx))) fun hk => derTlvMem_pt _ ?_
    have e : F + 4 + (x - (out + 4)) = F + BitVec.ofNat 32 (4 + (x - (out + 4)).toNat) := by
      conv => lhs; rw [← ofNat_toNat_self (x - (out + 4))]
      rw [hF4, add_ofNat_assoc]
    rw [e]; exact frLo _ (by omega)

end C3.RV32
