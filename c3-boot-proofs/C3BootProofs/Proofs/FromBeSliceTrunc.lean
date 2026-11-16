import C3BootProofs.Proofs.FillLimbs

/-!
# `<Uint<12> as Encoding>::from_be_slice_truncated`, as compiled

The wrapper zeroes 12 limbs on its stack, has
`fill_limbs_from_be_slice_truncated` fill them from the input's last bytes,
checks that it returned `Ok`, and copies the limbs to the output. The
P-256 instance, `Uint<8>`, is the same code with 8 limbs and a smaller
frame.
-/

namespace C3.RV32

open C3.Image

/-- **The limbs add up to the input.** When limb `q` below `⌈mm / 4⌉` holds
the big-endian value of the up to four bytes that end `4 q` bytes before
`E`, and the limbs above are zero, the `Lw` limbs are the big-endian value
of the `mm` bytes that end at `E`. -/
theorem fl_accV {M L : Word → BitVec 8} {X E : Word} {mm Lw : Nat} (hmm : mm < 2 ^ 30) (hKL : (mm + 3) / 4 ≤ Lw)
    (hl : ∀ q, q < (mm + 3) / 4 → (memLoad32 L (X + BitVec.ofNat 32 (4 * q))).toNat =
      beNat (memBytes M (E - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen mm q)) (flLen mm q)))
    (hz : ∀ q, (mm + 3) / 4 ≤ q → q < Lw → memLoad32 L (X + BitVec.ofNat 32 (4 * q)) = 0) :
    accV L X Lw = beNat (memBytes M (E - BitVec.ofNat 32 mm) mm) := by
  have lo : ∀ j, j ≤ (mm + 3) / 4 →
      accV L X j = beNat (memBytes M (E - BitVec.ofNat 32 (min mm (4 * j))) (min mm (4 * j))) := by
    intro j
    induction j with
    | zero => intro _; rw [show min mm (4 * 0) = 0 by omega]; rfl
    | succ j ih =>
      intro hj
      have hjm : 4 * j < mm := by omega
      have e1 : min mm (4 * (j + 1)) = 4 * j + flLen mm j := by simp only [flLen]; omega
      have e0 : min mm (4 * j) = 4 * j := by omega
      have hf4 : flLen mm j ≤ 4 := Nat.min_le_left _ _
      rw [accV, ih (by omega), hl j (by omega), e1, e0, ← fl_subsub E (a := 4 * j) (b := flLen mm j) (by omega),
        show 4 * j + flLen mm j = flLen mm j + 4 * j by omega, memBytes_split, beNat_append, memBytes_length,
        BitVec.sub_add_cancel, show 2 ^ (32 * j) = 256 ^ (4 * j) by rw [show 32 * j = 8 * (4 * j) by omega, Nat.pow_mul]]
      exact Nat.add_comm _ _
  have hi : ∀ j, (mm + 3) / 4 ≤ j → j ≤ Lw → accV L X j = accV L X ((mm + 3) / 4) := by
    intro j h1 h2
    induction j with
    | zero => rw [show (mm + 3) / 4 = 0 by omega]
    | succ j ih =>
      by_cases hj : (mm + 3) / 4 = j + 1
      · rw [hj]
      · rw [accV, hz j (by omega) (by omega), ih (by omega) (by omega), show (0 : Word).toNat = 0 from rfl,
          Nat.zero_mul, Nat.add_zero]
  rw [hi Lw hKL (Nat.le_refl _), lo _ (Nat.le_refl _), show min mm (4 * ((mm + 3) / 4)) = mm by omega]

section
set_option maxRecDepth 20000
theorem fb_at_0 : fetchRel fromBeSliceTrunc12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem fb_at_2 : fetchRel fromBeSliceTrunc12Code 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem fb_at_4 : fetchRel fromBeSliceTrunc12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem fb_at_6 : fetchRel fromBeSliceTrunc12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem fb_at_8 : fetchRel fromBeSliceTrunc12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem fb_at_a : fetchRel fromBeSliceTrunc12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem fb_at_c : fetchRel fromBeSliceTrunc12Code 0xC = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem fb_at_e : fetchRel fromBeSliceTrunc12Code 0xE = some (.alu .add (8 : Fin 32) x0 a2, 2) := by decide
theorem fb_at_10 : fetchRel fromBeSliceTrunc12Code 0x10 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem fb_at_12 : fetchRel fromBeSliceTrunc12Code 0x12 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem fb_at_14 : fetchRel fromBeSliceTrunc12Code 0x14 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem fb_at_16 : fetchRel fromBeSliceTrunc12Code 0x16 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fb_at_1a : fetchRel fromBeSliceTrunc12Code 0x1A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem fb_at_1c : fetchRel fromBeSliceTrunc12Code 0x1C = some (.auipc ra 0x12000, 4) := by decide
theorem fb_at_20 : fetchRel fromBeSliceTrunc12Code 0x20 = some (.jalr ra ra 0xFFFFFB40, 4) := by decide
theorem fb_at_24 : fetchRel fromBeSliceTrunc12Code 0x24 = some (.aluImm .add a2 sp 0xC, 2) := by decide
theorem fb_at_26 : fetchRel fromBeSliceTrunc12Code 0x26 = some (.aluImm .add a3 x0 0xC, 2) := by decide
theorem fb_at_28 : fetchRel fromBeSliceTrunc12Code 0x28 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem fb_at_2a : fetchRel fromBeSliceTrunc12Code 0x2A = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem fb_at_2c : fetchRel fromBeSliceTrunc12Code 0x2C = some (.alu .add a4 x0 (19 : Fin 32), 2) := by decide
theorem fb_at_2e : fetchRel fromBeSliceTrunc12Code 0x2E = some (.auipc ra 0xB000, 4) := by decide
theorem fb_at_32 : fetchRel fromBeSliceTrunc12Code 0x32 = some (.jalr ra ra 0xFFFFF86C, 4) := by decide
theorem fb_at_36 : fetchRel fromBeSliceTrunc12Code 0x36 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem fb_at_3a : fetchRel fromBeSliceTrunc12Code 0x3A = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem fb_at_3e : fetchRel fromBeSliceTrunc12Code 0x3E = some (.branch .bne a0 x0 0x20, 2) := by decide
theorem fb_at_40 : fetchRel fromBeSliceTrunc12Code 0x40 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem fb_at_42 : fetchRel fromBeSliceTrunc12Code 0x42 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fb_at_46 : fetchRel fromBeSliceTrunc12Code 0x46 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem fb_at_48 : fetchRel fromBeSliceTrunc12Code 0x48 = some (.auipc ra 0x12000, 4) := by decide
theorem fb_at_4c : fetchRel fromBeSliceTrunc12Code 0x4C = some (.jalr ra ra 0xFFFFFB7C, 4) := by decide
theorem fb_at_50 : fetchRel fromBeSliceTrunc12Code 0x50 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem fb_at_52 : fetchRel fromBeSliceTrunc12Code 0x52 = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem fb_at_54 : fetchRel fromBeSliceTrunc12Code 0x54 = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem fb_at_56 : fetchRel fromBeSliceTrunc12Code 0x56 = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem fb_at_58 : fetchRel fromBeSliceTrunc12Code 0x58 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem fb_at_5a : fetchRel fromBeSliceTrunc12Code 0x5A = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem fb_at_5c : fetchRel fromBeSliceTrunc12Code 0x5C = some (.jalr x0 ra 0x0, 2) := by decide
theorem fb_at_5e : fetchRel fromBeSliceTrunc12Code 0x5E = some (.auipc ra 0xA000, 4) := by decide
theorem fb_at_62 : fetchRel fromBeSliceTrunc12Code 0x62 = some (.jalr ra ra 0x576, 4) := by decide
end

abbrev FB : Word := BitVec.ofNat 32 fromBeSliceTrunc12Address

/-- The code `from_be_slice_truncated` for `Uint<12>` runs: its own and its
callees'. -/
structure FBEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M FB fromBeSliceTrunc12Code
  ms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  fl : CodeIn M FL fillLimbsBeTruncCode
  cs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode

abbrev fbPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), ((8 : Fin 32), 0x48), ((9 : Fin 32), 0x44), ((18 : Fin 32), 0x40), ((19 : Fin 32), 0x3C)]

def fbB3 : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a3, .alu .add (8 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1,
   .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]
def fbB5 : List BInstr :=
  [.aluImm .add a2 sp 0xC, .aluImm .add a3 x0 0xC, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (8 : Fin 32),
   .alu .add a4 x0 (19 : Fin 32)]
def fbB10 : List BInstr :=
  [.aluImm .add a1 sp 0xC, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem fbSave_end : blockEnd fromBeSliceTrunc12Code 2 (saveBlock fbPs) = some 0xC := by decide
theorem fbB3_end : blockEnd fromBeSliceTrunc12Code 0xC fbB3 = some 0x1C := by decide
theorem fbB5_end : blockEnd fromBeSliceTrunc12Code 0x24 fbB5 = some 0x2E := by decide
theorem fbB10_end : blockEnd fromBeSliceTrunc12Code 0x40 fbB10 = some 0x48 := by decide
theorem fbRestore_end : blockEnd fromBeSliceTrunc12Code 0x50 (restoreBlock fbPs) = some 0x5A := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `<Uint<12> as Encoding>::from_be_slice_truncated`**, for a
precision `bits` that is a multiple of 32 and at most 384: the 12 limbs it
writes to `out` are the big-endian value of the last `min n (bits / 8)` of
the `n` bytes at `b`. It returns with `sp` and the callee-saved registers
restored and writes only `out` and the 0x70 bytes of stack below `sp`. -/
theorem fromBeSliceTrunc12_correct (m : Machine) {sp0 out b retAddr : Word} {n bits : Nat} (E : FBEnv m.mem)
    (hpc : m.pc = FB) (ha0 : reg m a0 = out) (ha1 : reg m a1 = b) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (ha3 : reg m a3 = BitVec.ofNat 32 bits) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hbits : bits % 32 = 0) (hb384 : bits ≤ 384) (hbn : b.toNat + n < 2 ^ 32)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x70 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 48 ≤ 0x40000000) (hoa : out.toNat % 4 = 0)
    (sBG : Sep b n (sp0 + 0xFFFFFF90) 0x70) (sOG : Sep out 48 (sp0 + 0xFFFFFF90) 0x70) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      accV m'.mem out 12 = beNat (memBytes m.mem (b + BitVec.ofNat 32 n - BitVec.ofNat 32 (min n (bits / 8)))
        (min n (bits / 8))) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF90) 0x70 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF90 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFB0 = F := ⟨_, rfl⟩
  rw [hG] at sBG sOG ⊢
  have hGF : G + 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGn : G.toNat = sp0.toNat - 0x70 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF90 : Word).toNat = 2 ^ 32 - 0x70 from rfl]; have := sp0.isLt; omega
  have hGa : G.toNat % 4 = 0 := by omega
  have hGc : ∀ c, c ≤ 0x70 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFn : F.toNat = G.toNat + 0x20 := by rw [← hGF]; exact hGc 0x20 (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have eFG : F + 0xFFFFFFE0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eFS : F + 0x50 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by
    rw [← hGF, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
  obtain ⟨T, hT⟩ : ∃ T, G + BitVec.ofNat 32 0x2C = T := ⟨_, rfl⟩
  have hFT : F + 0xC = T := by rw [← hT, ← hGF, BitVec.add_assoc]; rfl
  have hTn : T.toNat = G.toNat + 0x2C := by rw [← hT]; exact hGc _ (by decide)
  have hTa : T.toNat % 4 = 0 := by omega
  have sTG : ∀ {c l : Nat} {x : Word}, Sep G 0x70 x 1 → 0x2C + c + l ≤ 0x70 → Sep (T + BitVec.ofNat 32 c) l x 1 :=
    fun {c l _} hx h => by rw [← hT, add_ofNat_assoc]; exact (hx.symm.subR (c := 0x2C + c) (l := l) h).symm
  have offs0 : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x70 → d + k ≤ 0x70 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have sFG : ∀ {x : Word}, Sep G 0x70 x 1 → Sep F 0x50 x 1 := fun hx => by
    have := hx.symm.subR (c := 0x20) (l := 0x50) (by decide); rw [← hGF]; exact this.symm
  have hiG : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep G 0x70 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep G 0x70 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by rw [hM _ (hiG _ (code_hi h1 h2 hi'))]; exact hc i hi'
  have hFBn : FB.toNat = 0x403a2c8a := by decide
  have hc := E.cod
  have st0 : St m.mem FB m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc fb_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hF
  have slotO : ∀ o : Word, F + o = F + BitVec.ofNat 32 o.toNat := fun o => by rw [ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x4C → Sep (F + o) 4 FB fromBeSliceTrunc12Code.length := fun o ho =>
    sep_of_le (by rw [BitVec.toNat_add, hFBn]; have := Nat.mod_le (F.toNat + o.toNat) (2 ^ 32); omega)
      (by rw [hFBn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock fbPs) u1 hc fbSave_end (saveBlock_ok _ fbPs _ fun q hq => by
      rw [sp1]
      simp only [fbPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hFa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) fbPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep F 0x50 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside fbPs fun q hq => by
      simp only [fbPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> (rw [slotO]; exact hx.sub (by decide))
  have slots : ∀ r o, (r, o) ∈ fbPs → memLoad32 Ms (F + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [fbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot fbPs _ hm (by
      simp only [fbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [fbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have IMsG : ∀ x, Sep G 0x70 x 1 → Ms x = m.mem x := fun x hx => IMs x (sFG hx)
  have hc2 : CodeIn Ms FB fromBeSliceTrunc12Code := cd hc (by rw [hFBn]; decide) (by rw [hFBn]; decide) IMsG
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block fbB3 u2.self hc2 fbB3_end (by
    simp only [BlockOk, BInstr.ok, fbB3, and_self])
  have R3 : ∀ q, reg m3 q = (runBlock fbB3 (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms FB m3 0x1C (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have K3 : ∀ q, q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a2 →
      q ≠ a1 → reg m3 q = reg m2 q := fun q h19 h8 h9 h18 h0 h2 h1 => by
    rw [R3]; refine runBlock_reg _ _ _ q u2.self.zero ?_
    simp only [fbB3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h19, h8, h9, h18, h0, h2, h1]
  have v3 : reg m3 (19 : Fin 32) = BitVec.ofNat 32 bits ∧ reg m3 (8 : Fin 32) = BitVec.ofNat 32 n ∧
      reg m3 (9 : Fin 32) = b ∧ reg m3 (18 : Fin 32) = out ∧ reg m3 a0 = T ∧ reg m3 a1 = 0 ∧
      reg m3 a2 = BitVec.ofNat 32 (4 * 12) := by
    simp +decide only [R3, runBlock, BInstr.run, fbB3, upd_app, ↓reduceIte]
    rw [u2.self.zero, r2 a3 (by decide), r2 a2 (by decide), r2 a1 (by decide), r2 a0 (by decide), ha0, ha1, ha2, ha3,
      sp2]
    simp only [ev_add, hFT, and_true]
    exact ⟨zw _, zw _, zw _, zw _⟩
  obtain ⟨v319, v38, v39, v318, v3a0, v3a1, v3a2⟩ := v3
  have hMSn : (BitVec.ofNat 32 memsetAddress : Word).toNat = memsetAddress := by decide
  obtain ⟨m4, c4, u4, _, k4⟩ := u3'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 12) (dst := T) (by decide)
    hc2 (cd E.ms (by rw [hMSn]; decide) (by rw [hMSn]; decide) IMsG) fb_at_1c fb_at_20 (by decide) (by decide)
    (by decide) (by omega) (by decide) hTa (sep_of_le (by rw [hMSn]; unfold memsetAddress; omega) (by decide))
    v3a0 v3a1 v3a2
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Ms T 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have IMz : ∀ x, Sep G 0x70 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside 12 (by have := sTG (c := 0) (l := 48) hx (by decide); rwa [add_ofNat_zero] at this)]
    exact IMsG x hx
  have hc4 : CodeIn Mz FB fromBeSliceTrunc12Code := cd hc (by rw [hFBn]; decide) (by rw [hFBn]; decide) IMz
  obtain ⟨m5, c5, u5⟩ := St.block fbB5 u4 hc4 fbB5_end (by simp only [BlockOk, BInstr.ok, fbB5, and_self])
  have R5 : ∀ q, reg m5 q = (runBlock fbB5 (Mz, reg m4)).2 q := u5.regs
  have u5' : St Mz FB m5 0x2E (reg m5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  have K5 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a0 → q ≠ a1 → q ≠ a4 → reg m5 q = reg m4 q := fun q h2 h3 h0 h1 h4 => by
    rw [R5]; refine runBlock_reg _ _ _ q u4.zero ?_
    simp only [fbB5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h2, h3, h0, h1, h4]
  have K4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) →
      q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ sp → reg m4 q = reg m q :=
    fun q h2 h3 h4 h5 h6 hr h19 h8 h9 h18 h0 h1 hs => by
      rw [k4 q h2 h3 h4 h5 h6 hr, K3 q h19 h8 h9 h18 h0 h2 h1, r2 q hs]
  have sp4 : reg m4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  have s4 : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19] → reg m4 q = reg m3 q := fun q hq => by
    obtain ⟨h2, h3, h4, h5, h6, hr⟩ : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra := by
      revert hq; revert q; decide
    exact k4 q h2 h3 h4 h5 h6 hr
  have v5 : reg m5 a2 = T ∧ reg m5 a3 = BitVec.ofNat 32 12 ∧ reg m5 a0 = b ∧ reg m5 a1 = BitVec.ofNat 32 n ∧
      reg m5 a4 = BitVec.ofNat 32 bits := by
    simp +decide only [R5, runBlock, BInstr.run, fbB5, upd_app, ↓reduceIte]
    rw [sp4, s4 19 (by decide), s4 8 (by decide), s4 9 (by decide), v319, v38, v39]
    simp only [ev_add, hFT, true_and]
    exact ⟨zw _, zw _, zw _⟩
  obtain ⟨v5a2, v5a3, v5a0, v5a1, v5a4⟩ := v5
  have hFLn : FL.toNat = 0x403ad524 := by decide
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5'.callRa hc4 fb_at_2e fb_at_32 (cb := FL) (by decide) (by decide)
  have r6 := PEnv.reg1 regs6 u5'.zero
  have sp6 : reg m6 sp = F := by
    rw [r6 sp (by decide), K5 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp4]
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = min n (bits / 8) := ⟨_, rfl⟩
  rw [← hmm]
  have hmmB : mm ≤ bits / 8 := by rw [hmm]; exact Nat.min_le_right _ _
  have hmmn : mm ≤ n := by rw [hmm]; exact Nat.min_le_left _ _
  have hm30 : mm < 2 ^ 30 := by omega
  have sGT : Sep (F + 0xFFFFFFE0) 0x20 T (4 * 12) := by
    rw [eFG, ← hT]; have := offs0 (c := 0) (n := 0x20) (d := 0x2C) (k := 48) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have sBT : Sep b n T (4 * 12) := by rw [← hT]; exact sBG.subR (c := 0x2C) (l := 48) (by decide)
  have sBF : Sep b n (F + 0xFFFFFFE0) 0x20 := by
    rw [eFG]; have := sBG.subR (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨m7, c7, pc7, sp7, a07, K7, hl7, fr7⟩ := fillLimbs_correct m6 (sp0 := F) (b := b) (Lp := T)
    (retAddr := FB + BitVec.ofNat 32 (0x2E + 8)) (n := n) (L := 12) (bits := bits) (mm := mm)
    (by rw [mem6]; exact cd E.fl (by rw [hFLn]; decide) (by rw [hFLn]; decide) IMz) pc6
    (by rw [r6 a0 (by decide), v5a0]) (by rw [r6 a1 (by decide), v5a1]) (by rw [r6 a2 (by decide), v5a2])
    (by rw [r6 a3 (by decide), v5a3]) (by rw [r6 a4 (by decide), v5a4])
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at FB (by decide) _ (by decide)))
    sp6 hbits (by omega) (by decide) hmm hbn hFa (by omega) (by omega) (by omega) hTa sBF sBT sGT
  have sK : ∀ {x : Word}, Sep G 0x70 x 1 → Sep (F + 0xFFFFFFE0) 0x20 x 1 ∧ Sep T (4 * ((mm + 3) / 4)) x 1 :=
    fun hx => ⟨by rw [eFG]; have := hx.symm.subR (c := 0) (l := 0x20) (by decide); rw [add_ofNat_zero] at this
                  exact this.symm,
               by have := sTG (c := 0) (l := 4 * ((mm + 3) / 4)) hx (by omega); rwa [add_ofNat_zero] at this⟩
  have M7G : ∀ x, Sep G 0x70 x 1 → m7.mem x = m.mem x := fun x hx => by
    rw [fr7 x (sK hx).1 (sK hx).2, mem6, IMz x hx]
  have hc7 : CodeIn m7.mem FB fromBeSliceTrunc12Code := cd hc (by rw [hFBn]; decide) (by rw [hFBn]; decide) M7G
  have u7 : St m7.mem FB m7 0x36 (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc7 fb_at_36 (off' := 0x3A) (by decide)
  obtain ⟨m9, d9, u9⟩ := u8.self.aluImm hc7 fb_at_3a (off' := 0x3E) (by decide)
  have a09 : reg m9 a0 = 0 := by
    rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [a07]; decide
  have K9 : ∀ q, q ≠ a0 → reg m9 q = reg m7 q := fun q h0 => by
    rw [u9.regs, updz u8.self.zero h0, u8.regs, updz u7.zero h0]
  obtain ⟨m10, d10, u10⟩ := u9.self.notTaken hc7 0x40 fb_at_3e (by decide) (by
    simp only [branchTaken]; rw [a09, u9.self.zero]; decide)
  obtain ⟨m11, c11, u11⟩ := St.block fbB10 u10 hc7 fbB10_end (by simp only [BlockOk, BInstr.ok, fbB10, and_self])
  have R11 : ∀ q, reg m11 q = (runBlock fbB10 (m7.mem, reg m9)).2 q := u11.regs
  have u11' : St m7.mem FB m11 0x48 (reg m11) := ⟨u11.pc, by rw [u11.mem]; rfl, fun _ => rfl⟩
  have K11 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a0 → reg m11 q = reg m9 q := fun q h1 h2 h0 => by
    rw [R11]; refine runBlock_reg _ _ _ q u10.zero ?_
    simp only [fbB10, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h1, h2, h0]
  have K7' : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ ra → reg m7 q = reg m5 q :=
    fun q hq hr => by rw [K7 q hq, r6 q hr]
  have o7 : reg m7 (18 : Fin 32) = out := by
    rw [K7' 18 (by decide) (by decide), K5 18 (by decide) (by decide) (by decide) (by decide) (by decide),
      s4 18 (by decide), v318]
  have sp9 : reg m9 sp = F := by rw [K9 sp (by decide), sp7]
  have v11 : reg m11 a0 = out ∧ reg m11 a1 = T ∧ reg m11 a2 = BitVec.ofNat 32 (4 * 12) := by
    simp +decide only [R11, runBlock, BInstr.run, fbB10, upd_app, ↓reduceIte]
    rw [sp9, K9 18 (by decide), o7]
    simp only [ev_add, hFT, and_true]
    exact zw _
  obtain ⟨v11a0, v11a1, v11a2⟩ := v11
  have hMCn : (BitVec.ofNat 32 memcpyStubAddress : Word).toNat = memcpyStubAddress := by decide
  have hMCb : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = memcpyStubAddress + 8 := by decide
  have sOT : Sep out (4 * 12) T (4 * 12) := by rw [← hT]; exact sOG.subR (c := 0x2C) (l := 48) (by decide)
  obtain ⟨m12, c12, u12, _, k12⟩ := u11'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 12) (dst := out)
    (src := T) (by decide) hc7 (cd E.cs (by rw [hMCn]; decide) (by rw [hMCn]; decide) M7G)
    (cd E.cb (by decide) (by decide) M7G) fb_at_48 fb_at_4c (by decide) (by decide) (by decide) (by omega) (by decide)
    hoa hTa sOT (sep_of_le (by rw [hMCb]; unfold memcpyStubAddress; omega) (by decide)) v11a0 v11a1 v11a2
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords m7.mem out T 12 = Mc := ⟨_, rfl⟩
  rw [hMc] at u12
  have FrC : ∀ x, Sep G 0x70 x 1 → Sep out 48 x 1 → Mc x = m.mem x := fun x hx ho => by
    rw [← hMc, copyWords_outside 12 ho, M7G x hx]
  have hiO : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep out 48 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hc12 : CodeIn Mc FB fromBeSliceTrunc12Code := fun i hi => by
    have hx := code_hi (b := FB) (by rw [hFBn]; decide) (by rw [hFBn]; decide) hi
    rw [FrC _ (hiG _ hx) (hiO _ hx)]; exact hc i hi
  have sp12 : reg m12 sp = F := by
    rw [k12 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), K11 sp (by decide) (by decide) (by decide), sp9]
  have hpsp : ∀ p ∈ fbPs, p.1 ≠ sp := by decide
  obtain ⟨n1, c13, u13⟩ := St.block (restoreBlock fbPs) u12.self hc12 fbRestore_end
    (restoreBlock_ok Mc F fbPs (reg m12) sp12 hpsp fun q hq => by
      simp only [fbPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run Mc F fbPs (reg m12) sp12 hpsp] at u13
  have rsp : restoreRegs Mc F (reg m12) fbPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp12
  obtain ⟨n2, d14, u14⟩ := u13.aluImm hc12 fb_at_5a (off' := 0x5C) (by decide)
  obtain ⟨n3, d15, pc15, mem15, regs15⟩ := u14.jalr hc12 fb_at_5c
  have slotM : ∀ c, 0x5C ≤ c → c < 0x70 → Mc (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
    have hx1 : Sep (F + 0xFFFFFFE0) 0x20 (G + BitVec.ofNat 32 c) 1 := by
      rw [eFG]; have := offs0 (c := 0) (n := 0x20) (d := c) (k := 1) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have hx2 : Sep T (4 * ((mm + 3) / 4)) (G + BitVec.ofNat 32 c) 1 := by
      rw [← hT]; exact offs0 (by omega) (by omega) (by omega)
    have hT48 : Sep T 48 (G + BitVec.ofNat 32 c) 1 := by
      rw [← hT]; exact offs0 (by omega) (by omega) (by omega)
    rw [← hMc, copyWords_outside 12 (sOG.subR (c := c) (l := 1) (by omega)), fr7 _ hx1 hx2, mem6, ← hMz,
      fillWords_outside 12 hT48]
  have slot : ∀ o : Word, 0x3C ≤ o.toNat → o.toNat + 4 ≤ 0x50 → memLoad32 Mc (F + o) = memLoad32 Ms (F + o) :=
    fun o h1 h2 => by
      rw [slotO]
      apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, eFk]; exact slotM _ (by omega) (by omega)
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs Mc F f ps q = f q := by
    intro f ps q hq0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
  have hslot : ∀ r o, (r, o) ∈ fbPs → reg n3 r = reg m r := fun r o hm => by
    rw [regs15]
    simp only [fbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      rw [slot _ (by decide) (by decide)]; exact slots _ _ (by decide)
  have eIn : b + BitVec.ofNat 32 n - BitVec.ofNat 32 mm = b + BitVec.ofNat 32 (n - mm) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    have := b.isLt; omega
  have hIn : ∀ q, q < (mm + 3) / 4 → ∀ i, i < flLen mm q →
      Sep G 0x70 (b + BitVec.ofNat 32 n - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen mm q) +
        BitVec.ofNat 32 i) 1 := fun q hq i hi => by
    rw [fl_srcE (b + BitVec.ofNat 32 n) (by omega) hm30 hi, eIn, add_ofNat_assoc]
    exact (sBG.sub (by unfold flLen at hi; omega)).symm
  have val : accV Mc out 12 = beNat (memBytes m.mem (b + BitVec.ofNat 32 n - BitVec.ofNat 32 mm) mm) := by
    rw [accV_congr2 (M := m7.mem) (b := T) 12 fun i hi => by rw [← hMc]; exact copyWords_load 12 i hi (by omega)]
    refine fl_accV hm30 (by omega) (fun q hq => ?_) (fun q h1 h2 => ?_)
    · rw [hl7 q hq]
      exact congrArg beNat (memBytes_congr fun i hi => by rw [mem6]; exact IMz _ (hIn q hq i hi))
    · rw [← fillWords_load (M := Ms) (dst := T) (v := 0) 12 q h2 (by omega), hMz]
      apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc]
      have hx : Sep (F + 0xFFFFFFE0) 0x20 (T + BitVec.ofNat 32 (4 * q + j)) 1 := by
        rw [eFG, ← hT, add_ofNat_assoc]
        have := offs0 (c := 0) (n := 0x20) (d := 0x2C + (4 * q + j)) (k := 1) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have hTK : Sep T (4 * ((mm + 3) / 4)) (T + BitVec.ofNat 32 (4 * q + j)) 1 := by
        have := sep_offsets T (c := 0) (n := 4 * ((mm + 3) / 4)) (d := 4 * q + j) (k := 1) (by omega) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at this
      rw [fr7 _ hx hTK, mem6]
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (.cons d9 (.cons d10
    (c11.trans (c12.trans (c13.trans (.cons d14 (.single d15)))))))))))))), ?_, ?_, fun q hq => ?_, ?_,
    fun x hx hl => ?_⟩
  · rw [pc15, ← regs15, hslot ra 0x4C (by decide), hra, add_lit_zero, hret]
  · rw [regs15]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp, eFS]
  · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27]) q hq with rfl | rfl | rfl | rfl | rfl | hL
    · exact hslot _ 0x4C (by decide)
    · exact hslot _ 0x48 (by decide)
    · exact hslot _ 0x44 (by decide)
    · exact hslot _ 0x40 (by decide)
    · exact hslot _ 0x3C (by decide)
    · obtain ⟨hv, hs, hps, h1, h2, h3, h4, h5, h6, h7, ht0, ht1, hr, h0, h19, h8, h9, h18⟩ :
          q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ fbPs, p.1 ≠ q) ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧
          q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ (19 : Fin 32) ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧
          q ≠ (18 : Fin 32) := by revert hL; revert q; decide
      rw [regs15, upd_ne hv hs, rr _ _ q hv hps, k12 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 hr, K11 q h1 h2 h0, K9 q h0,
        K7' q hq hr, K5 q h2 h3 h0 h1 h4, K4 q h2 h3 h4 h5 h6 hr h19 h8 h9 h18 h0 h1 hs]
  · rw [mem15]; exact val
  · rw [mem15]; exact FrC x hx hl


section
set_option maxRecDepth 20000
theorem fc_at_0 : fetchRel fromBeSliceTrunc8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem fc_at_2 : fetchRel fromBeSliceTrunc8Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem fc_at_4 : fetchRel fromBeSliceTrunc8Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem fc_at_6 : fetchRel fromBeSliceTrunc8Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem fc_at_8 : fetchRel fromBeSliceTrunc8Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem fc_at_a : fetchRel fromBeSliceTrunc8Code 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem fc_at_c : fetchRel fromBeSliceTrunc8Code 0xC = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem fc_at_e : fetchRel fromBeSliceTrunc8Code 0xE = some (.alu .add (8 : Fin 32) x0 a2, 2) := by decide
theorem fc_at_10 : fetchRel fromBeSliceTrunc8Code 0x10 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem fc_at_12 : fetchRel fromBeSliceTrunc8Code 0x12 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem fc_at_14 : fetchRel fromBeSliceTrunc8Code 0x14 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem fc_at_16 : fetchRel fromBeSliceTrunc8Code 0x16 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem fc_at_1a : fetchRel fromBeSliceTrunc8Code 0x1A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem fc_at_1c : fetchRel fromBeSliceTrunc8Code 0x1C = some (.auipc ra 0x12000, 4) := by decide
theorem fc_at_20 : fetchRel fromBeSliceTrunc8Code 0x20 = some (.jalr ra ra 0xFFFFF996, 4) := by decide
theorem fc_at_24 : fetchRel fromBeSliceTrunc8Code 0x24 = some (.aluImm .add a2 sp 0xC, 2) := by decide
theorem fc_at_26 : fetchRel fromBeSliceTrunc8Code 0x26 = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem fc_at_28 : fetchRel fromBeSliceTrunc8Code 0x28 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem fc_at_2a : fetchRel fromBeSliceTrunc8Code 0x2A = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem fc_at_2c : fetchRel fromBeSliceTrunc8Code 0x2C = some (.alu .add a4 x0 (19 : Fin 32), 2) := by decide
theorem fc_at_2e : fetchRel fromBeSliceTrunc8Code 0x2E = some (.auipc ra 0xA000, 4) := by decide
theorem fc_at_32 : fetchRel fromBeSliceTrunc8Code 0x32 = some (.jalr ra ra 0x6C2, 4) := by decide
theorem fc_at_36 : fetchRel fromBeSliceTrunc8Code 0x36 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem fc_at_3a : fetchRel fromBeSliceTrunc8Code 0x3A = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem fc_at_3e : fetchRel fromBeSliceTrunc8Code 0x3E = some (.branch .bne a0 x0 0x20, 2) := by decide
theorem fc_at_40 : fetchRel fromBeSliceTrunc8Code 0x40 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem fc_at_42 : fetchRel fromBeSliceTrunc8Code 0x42 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem fc_at_46 : fetchRel fromBeSliceTrunc8Code 0x46 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem fc_at_48 : fetchRel fromBeSliceTrunc8Code 0x48 = some (.auipc ra 0x12000, 4) := by decide
theorem fc_at_4c : fetchRel fromBeSliceTrunc8Code 0x4C = some (.jalr ra ra 0xFFFFF9D2, 4) := by decide
theorem fc_at_50 : fetchRel fromBeSliceTrunc8Code 0x50 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem fc_at_52 : fetchRel fromBeSliceTrunc8Code 0x52 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem fc_at_54 : fetchRel fromBeSliceTrunc8Code 0x54 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem fc_at_56 : fetchRel fromBeSliceTrunc8Code 0x56 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem fc_at_58 : fetchRel fromBeSliceTrunc8Code 0x58 = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem fc_at_5a : fetchRel fromBeSliceTrunc8Code 0x5A = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem fc_at_5c : fetchRel fromBeSliceTrunc8Code 0x5C = some (.jalr x0 ra 0x0, 2) := by decide
theorem fc_at_5e : fetchRel fromBeSliceTrunc8Code 0x5E = some (.auipc ra 0xA000, 4) := by decide
theorem fc_at_62 : fetchRel fromBeSliceTrunc8Code 0x62 = some (.jalr ra ra 0x3CC, 4) := by decide
end

abbrev FC : Word := BitVec.ofNat 32 fromBeSliceTrunc8Address

/-- The code `from_be_slice_truncated` for `Uint<8>` runs: its own and its
callees'. -/
structure FCEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M FC fromBeSliceTrunc8Code
  ms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  fl : CodeIn M FL fillLimbsBeTruncCode
  cs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode

abbrev fcPs : List (Fin 32 × Word) :=
  [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30), ((19 : Fin 32), 0x2C)]

def fcB3 : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a3, .alu .add (8 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1,
   .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
def fcB5 : List BInstr :=
  [.aluImm .add a2 sp 0xC, .aluImm .add a3 x0 0x8, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (8 : Fin 32),
   .alu .add a4 x0 (19 : Fin 32)]
def fcB10 : List BInstr :=
  [.aluImm .add a1 sp 0xC, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem fcSave_end : blockEnd fromBeSliceTrunc8Code 2 (saveBlock fcPs) = some 0xC := by decide
theorem fcB3_end : blockEnd fromBeSliceTrunc8Code 0xC fcB3 = some 0x1C := by decide
theorem fcB5_end : blockEnd fromBeSliceTrunc8Code 0x24 fcB5 = some 0x2E := by decide
theorem fcB10_end : blockEnd fromBeSliceTrunc8Code 0x40 fcB10 = some 0x48 := by decide
theorem fcRestore_end : blockEnd fromBeSliceTrunc8Code 0x50 (restoreBlock fcPs) = some 0x5A := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `<Uint<8> as Encoding>::from_be_slice_truncated`**, for a
precision `bits` that is a multiple of 32 and at most 256: the 8 limbs it
writes to `out` are the big-endian value of the last `min n (bits / 8)` of
the `n` bytes at `b`. It returns with `sp` and the callee-saved registers
restored and writes only `out` and the 0x60 bytes of stack below `sp`. -/
theorem fromBeSliceTrunc8_correct (m : Machine) {sp0 out b retAddr : Word} {n bits : Nat} (E : FCEnv m.mem)
    (hpc : m.pc = FC) (ha0 : reg m a0 = out) (ha1 : reg m a1 = b) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (ha3 : reg m a3 = BitVec.ofNat 32 bits) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hbits : bits % 32 = 0) (hb256 : bits ≤ 256) (hbn : b.toNat + n < 2 ^ 32)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x60 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 32 ≤ 0x40000000) (hoa : out.toNat % 4 = 0)
    (sBG : Sep b n (sp0 + 0xFFFFFFA0) 0x60) (sOG : Sep out 32 (sp0 + 0xFFFFFFA0) 0x60) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      accV m'.mem out 8 = beNat (memBytes m.mem (b + BitVec.ofNat 32 n - BitVec.ofNat 32 (min n (bits / 8)))
        (min n (bits / 8))) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFA0 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFC0 = F := ⟨_, rfl⟩
  rw [hG] at sBG sOG ⊢
  have hGF : G + 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGn : G.toNat = sp0.toNat - 0x60 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFA0 : Word).toNat = 2 ^ 32 - 0x60 from rfl]; have := sp0.isLt; omega
  have hGa : G.toNat % 4 = 0 := by omega
  have hGc : ∀ c, c ≤ 0x60 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFn : F.toNat = G.toNat + 0x20 := by rw [← hGF]; exact hGc 0x20 (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have eFG : F + 0xFFFFFFE0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eFS : F + 0x40 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by
    rw [← hGF, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
  obtain ⟨T, hT⟩ : ∃ T, G + BitVec.ofNat 32 0x2C = T := ⟨_, rfl⟩
  have hFT : F + 0xC = T := by rw [← hT, ← hGF, BitVec.add_assoc]; rfl
  have hTn : T.toNat = G.toNat + 0x2C := by rw [← hT]; exact hGc _ (by decide)
  have hTa : T.toNat % 4 = 0 := by omega
  have sTG : ∀ {c l : Nat} {x : Word}, Sep G 0x60 x 1 → 0x2C + c + l ≤ 0x60 → Sep (T + BitVec.ofNat 32 c) l x 1 :=
    fun {c l _} hx h => by rw [← hT, add_ofNat_assoc]; exact (hx.symm.subR (c := 0x2C + c) (l := l) h).symm
  have offs0 : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x60 → d + k ≤ 0x60 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have sFG : ∀ {x : Word}, Sep G 0x60 x 1 → Sep F 0x40 x 1 := fun hx => by
    have := hx.symm.subR (c := 0x20) (l := 0x40) (by decide); rw [← hGF]; exact this.symm
  have hiG : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep G 0x60 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep G 0x60 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by rw [hM _ (hiG _ (code_hi h1 h2 hi'))]; exact hc i hi'
  have hFCn : FC.toNat = 0x403a2e34 := by decide
  have hc := E.cod
  have st0 : St m.mem FC m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc fc_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hF
  have slotO : ∀ o : Word, F + o = F + BitVec.ofNat 32 o.toNat := fun o => by rw [ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x3C → Sep (F + o) 4 FC fromBeSliceTrunc8Code.length := fun o ho =>
    sep_of_le (by rw [BitVec.toNat_add, hFCn]; have := Nat.mod_le (F.toNat + o.toNat) (2 ^ 32); omega)
      (by rw [hFCn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock fcPs) u1 hc fcSave_end (saveBlock_ok _ fcPs _ fun q hq => by
      rw [sp1]
      simp only [fcPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hFa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0)) fcPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep F 0x40 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside fcPs fun q hq => by
      simp only [fcPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> (rw [slotO]; exact hx.sub (by decide))
  have slots : ∀ r o, (r, o) ∈ fcPs → memLoad32 Ms (F + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [fcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot fcPs _ hm (by
      simp only [fcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [fcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have IMsG : ∀ x, Sep G 0x60 x 1 → Ms x = m.mem x := fun x hx => IMs x (sFG hx)
  have hc2 : CodeIn Ms FC fromBeSliceTrunc8Code := cd hc (by rw [hFCn]; decide) (by rw [hFCn]; decide) IMsG
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block fcB3 u2.self hc2 fcB3_end (by
    simp only [BlockOk, BInstr.ok, fcB3, and_self])
  have R3 : ∀ q, reg m3 q = (runBlock fcB3 (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms FC m3 0x1C (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have K3 : ∀ q, q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a2 →
      q ≠ a1 → reg m3 q = reg m2 q := fun q h19 h8 h9 h18 h0 h2 h1 => by
    rw [R3]; refine runBlock_reg _ _ _ q u2.self.zero ?_
    simp only [fcB3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h19, h8, h9, h18, h0, h2, h1]
  have v3 : reg m3 (19 : Fin 32) = BitVec.ofNat 32 bits ∧ reg m3 (8 : Fin 32) = BitVec.ofNat 32 n ∧
      reg m3 (9 : Fin 32) = b ∧ reg m3 (18 : Fin 32) = out ∧ reg m3 a0 = T ∧ reg m3 a1 = 0 ∧
      reg m3 a2 = BitVec.ofNat 32 (4 * 8) := by
    simp +decide only [R3, runBlock, BInstr.run, fcB3, upd_app, ↓reduceIte]
    rw [u2.self.zero, r2 a3 (by decide), r2 a2 (by decide), r2 a1 (by decide), r2 a0 (by decide), ha0, ha1, ha2, ha3,
      sp2]
    simp only [ev_add, hFT, and_true]
    exact ⟨zw _, zw _, zw _, zw _⟩
  obtain ⟨v319, v38, v39, v318, v3a0, v3a1, v3a2⟩ := v3
  have hMSn : (BitVec.ofNat 32 memsetAddress : Word).toNat = memsetAddress := by decide
  obtain ⟨m4, c4, u4, _, k4⟩ := u3'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 8) (dst := T) (by decide)
    hc2 (cd E.ms (by rw [hMSn]; decide) (by rw [hMSn]; decide) IMsG) fc_at_1c fc_at_20 (by decide) (by decide)
    (by decide) (by omega) (by decide) hTa (sep_of_le (by rw [hMSn]; unfold memsetAddress; omega) (by decide))
    v3a0 v3a1 v3a2
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Ms T 0 8 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have IMz : ∀ x, Sep G 0x60 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside 8 (by have := sTG (c := 0) (l := 32) hx (by decide); rwa [add_ofNat_zero] at this)]
    exact IMsG x hx
  have hc4 : CodeIn Mz FC fromBeSliceTrunc8Code := cd hc (by rw [hFCn]; decide) (by rw [hFCn]; decide) IMz
  obtain ⟨m5, c5, u5⟩ := St.block fcB5 u4 hc4 fcB5_end (by simp only [BlockOk, BInstr.ok, fcB5, and_self])
  have R5 : ∀ q, reg m5 q = (runBlock fcB5 (Mz, reg m4)).2 q := u5.regs
  have u5' : St Mz FC m5 0x2E (reg m5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  have K5 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a0 → q ≠ a1 → q ≠ a4 → reg m5 q = reg m4 q := fun q h2 h3 h0 h1 h4 => by
    rw [R5]; refine runBlock_reg _ _ _ q u4.zero ?_
    simp only [fcB5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h2, h3, h0, h1, h4]
  have K4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) →
      q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ sp → reg m4 q = reg m q :=
    fun q h2 h3 h4 h5 h6 hr h19 h8 h9 h18 h0 h1 hs => by
      rw [k4 q h2 h3 h4 h5 h6 hr, K3 q h19 h8 h9 h18 h0 h2 h1, r2 q hs]
  have sp4 : reg m4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  have s4 : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19] → reg m4 q = reg m3 q := fun q hq => by
    obtain ⟨h2, h3, h4, h5, h6, hr⟩ : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra := by
      revert hq; revert q; decide
    exact k4 q h2 h3 h4 h5 h6 hr
  have v5 : reg m5 a2 = T ∧ reg m5 a3 = BitVec.ofNat 32 8 ∧ reg m5 a0 = b ∧ reg m5 a1 = BitVec.ofNat 32 n ∧
      reg m5 a4 = BitVec.ofNat 32 bits := by
    simp +decide only [R5, runBlock, BInstr.run, fcB5, upd_app, ↓reduceIte]
    rw [sp4, s4 19 (by decide), s4 8 (by decide), s4 9 (by decide), v319, v38, v39]
    simp only [ev_add, hFT, true_and]
    exact ⟨zw _, zw _, zw _⟩
  obtain ⟨v5a2, v5a3, v5a0, v5a1, v5a4⟩ := v5
  have hFLn : FL.toNat = 0x403ad524 := by decide
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5'.callRa hc4 fc_at_2e fc_at_32 (cb := FL) (by decide) (by decide)
  have r6 := PEnv.reg1 regs6 u5'.zero
  have sp6 : reg m6 sp = F := by
    rw [r6 sp (by decide), K5 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp4]
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = min n (bits / 8) := ⟨_, rfl⟩
  rw [← hmm]
  have hmmB : mm ≤ bits / 8 := by rw [hmm]; exact Nat.min_le_right _ _
  have hmmn : mm ≤ n := by rw [hmm]; exact Nat.min_le_left _ _
  have hm30 : mm < 2 ^ 30 := by omega
  have sGT : Sep (F + 0xFFFFFFE0) 0x20 T (4 * 8) := by
    rw [eFG, ← hT]; have := offs0 (c := 0) (n := 0x20) (d := 0x2C) (k := 32) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have sBT : Sep b n T (4 * 8) := by rw [← hT]; exact sBG.subR (c := 0x2C) (l := 32) (by decide)
  have sBF : Sep b n (F + 0xFFFFFFE0) 0x20 := by
    rw [eFG]; have := sBG.subR (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨m7, c7, pc7, sp7, a07, K7, hl7, fr7⟩ := fillLimbs_correct m6 (sp0 := F) (b := b) (Lp := T)
    (retAddr := FC + BitVec.ofNat 32 (0x2E + 8)) (n := n) (L := 8) (bits := bits) (mm := mm)
    (by rw [mem6]; exact cd E.fl (by rw [hFLn]; decide) (by rw [hFLn]; decide) IMz) pc6
    (by rw [r6 a0 (by decide), v5a0]) (by rw [r6 a1 (by decide), v5a1]) (by rw [r6 a2 (by decide), v5a2])
    (by rw [r6 a3 (by decide), v5a3]) (by rw [r6 a4 (by decide), v5a4])
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at FC (by decide) _ (by decide)))
    sp6 hbits (by omega) (by decide) hmm hbn hFa (by omega) (by omega) (by omega) hTa sBF sBT sGT
  have sK : ∀ {x : Word}, Sep G 0x60 x 1 → Sep (F + 0xFFFFFFE0) 0x20 x 1 ∧ Sep T (4 * ((mm + 3) / 4)) x 1 :=
    fun hx => ⟨by rw [eFG]; have := hx.symm.subR (c := 0) (l := 0x20) (by decide); rw [add_ofNat_zero] at this
                  exact this.symm,
               by have := sTG (c := 0) (l := 4 * ((mm + 3) / 4)) hx (by omega); rwa [add_ofNat_zero] at this⟩
  have M7G : ∀ x, Sep G 0x60 x 1 → m7.mem x = m.mem x := fun x hx => by
    rw [fr7 x (sK hx).1 (sK hx).2, mem6, IMz x hx]
  have hc7 : CodeIn m7.mem FC fromBeSliceTrunc8Code := cd hc (by rw [hFCn]; decide) (by rw [hFCn]; decide) M7G
  have u7 : St m7.mem FC m7 0x36 (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc7 fc_at_36 (off' := 0x3A) (by decide)
  obtain ⟨m9, d9, u9⟩ := u8.self.aluImm hc7 fc_at_3a (off' := 0x3E) (by decide)
  have a09 : reg m9 a0 = 0 := by
    rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [a07]; decide
  have K9 : ∀ q, q ≠ a0 → reg m9 q = reg m7 q := fun q h0 => by
    rw [u9.regs, updz u8.self.zero h0, u8.regs, updz u7.zero h0]
  obtain ⟨m10, d10, u10⟩ := u9.self.notTaken hc7 0x40 fc_at_3e (by decide) (by
    simp only [branchTaken]; rw [a09, u9.self.zero]; decide)
  obtain ⟨m11, c11, u11⟩ := St.block fcB10 u10 hc7 fcB10_end (by simp only [BlockOk, BInstr.ok, fcB10, and_self])
  have R11 : ∀ q, reg m11 q = (runBlock fcB10 (m7.mem, reg m9)).2 q := u11.regs
  have u11' : St m7.mem FC m11 0x48 (reg m11) := ⟨u11.pc, by rw [u11.mem]; rfl, fun _ => rfl⟩
  have K11 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a0 → reg m11 q = reg m9 q := fun q h1 h2 h0 => by
    rw [R11]; refine runBlock_reg _ _ _ q u10.zero ?_
    simp only [fcB10, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h1, h2, h0]
  have K7' : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ ra → reg m7 q = reg m5 q :=
    fun q hq hr => by rw [K7 q hq, r6 q hr]
  have o7 : reg m7 (18 : Fin 32) = out := by
    rw [K7' 18 (by decide) (by decide), K5 18 (by decide) (by decide) (by decide) (by decide) (by decide),
      s4 18 (by decide), v318]
  have sp9 : reg m9 sp = F := by rw [K9 sp (by decide), sp7]
  have v11 : reg m11 a0 = out ∧ reg m11 a1 = T ∧ reg m11 a2 = BitVec.ofNat 32 (4 * 8) := by
    simp +decide only [R11, runBlock, BInstr.run, fcB10, upd_app, ↓reduceIte]
    rw [sp9, K9 18 (by decide), o7]
    simp only [ev_add, hFT, and_true]
    exact zw _
  obtain ⟨v11a0, v11a1, v11a2⟩ := v11
  have hMCn : (BitVec.ofNat 32 memcpyStubAddress : Word).toNat = memcpyStubAddress := by decide
  have hMCb : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = memcpyStubAddress + 8 := by decide
  have sOT : Sep out (4 * 8) T (4 * 8) := by rw [← hT]; exact sOG.subR (c := 0x2C) (l := 32) (by decide)
  obtain ⟨m12, c12, u12, _, k12⟩ := u11'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 8) (dst := out)
    (src := T) (by decide) hc7 (cd E.cs (by rw [hMCn]; decide) (by rw [hMCn]; decide) M7G)
    (cd E.cb (by decide) (by decide) M7G) fc_at_48 fc_at_4c (by decide) (by decide) (by decide) (by omega) (by decide)
    hoa hTa sOT (sep_of_le (by rw [hMCb]; unfold memcpyStubAddress; omega) (by decide)) v11a0 v11a1 v11a2
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords m7.mem out T 8 = Mc := ⟨_, rfl⟩
  rw [hMc] at u12
  have FrC : ∀ x, Sep G 0x60 x 1 → Sep out 32 x 1 → Mc x = m.mem x := fun x hx ho => by
    rw [← hMc, copyWords_outside 8 ho, M7G x hx]
  have hiO : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep out 32 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hc12 : CodeIn Mc FC fromBeSliceTrunc8Code := fun i hi => by
    have hx := code_hi (b := FC) (by rw [hFCn]; decide) (by rw [hFCn]; decide) hi
    rw [FrC _ (hiG _ hx) (hiO _ hx)]; exact hc i hi
  have sp12 : reg m12 sp = F := by
    rw [k12 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), K11 sp (by decide) (by decide) (by decide), sp9]
  have hpsp : ∀ p ∈ fcPs, p.1 ≠ sp := by decide
  obtain ⟨n1, c13, u13⟩ := St.block (restoreBlock fcPs) u12.self hc12 fcRestore_end
    (restoreBlock_ok Mc F fcPs (reg m12) sp12 hpsp fun q hq => by
      simp only [fcPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run Mc F fcPs (reg m12) sp12 hpsp] at u13
  have rsp : restoreRegs Mc F (reg m12) fcPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp12
  obtain ⟨n2, d14, u14⟩ := u13.aluImm hc12 fc_at_5a (off' := 0x5C) (by decide)
  obtain ⟨n3, d15, pc15, mem15, regs15⟩ := u14.jalr hc12 fc_at_5c
  have slotM : ∀ c, 0x4C ≤ c → c < 0x60 → Mc (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
    have hx1 : Sep (F + 0xFFFFFFE0) 0x20 (G + BitVec.ofNat 32 c) 1 := by
      rw [eFG]; have := offs0 (c := 0) (n := 0x20) (d := c) (k := 1) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have hx2 : Sep T (4 * ((mm + 3) / 4)) (G + BitVec.ofNat 32 c) 1 := by
      rw [← hT]; exact offs0 (by omega) (by omega) (by omega)
    have hT48 : Sep T 32 (G + BitVec.ofNat 32 c) 1 := by
      rw [← hT]; exact offs0 (by omega) (by omega) (by omega)
    rw [← hMc, copyWords_outside 8 (sOG.subR (c := c) (l := 1) (by omega)), fr7 _ hx1 hx2, mem6, ← hMz,
      fillWords_outside 8 hT48]
  have slot : ∀ o : Word, 0x2C ≤ o.toNat → o.toNat + 4 ≤ 0x40 → memLoad32 Mc (F + o) = memLoad32 Ms (F + o) :=
    fun o h1 h2 => by
      rw [slotO]
      apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, eFk]; exact slotM _ (by omega) (by omega)
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs Mc F f ps q = f q := by
    intro f ps q hq0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
  have hslot : ∀ r o, (r, o) ∈ fcPs → reg n3 r = reg m r := fun r o hm => by
    rw [regs15]
    simp only [fcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      rw [slot _ (by decide) (by decide)]; exact slots _ _ (by decide)
  have eIn : b + BitVec.ofNat 32 n - BitVec.ofNat 32 mm = b + BitVec.ofNat 32 (n - mm) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    have := b.isLt; omega
  have hIn : ∀ q, q < (mm + 3) / 4 → ∀ i, i < flLen mm q →
      Sep G 0x60 (b + BitVec.ofNat 32 n - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen mm q) +
        BitVec.ofNat 32 i) 1 := fun q hq i hi => by
    rw [fl_srcE (b + BitVec.ofNat 32 n) (by omega) hm30 hi, eIn, add_ofNat_assoc]
    exact (sBG.sub (by unfold flLen at hi; omega)).symm
  have val : accV Mc out 8 = beNat (memBytes m.mem (b + BitVec.ofNat 32 n - BitVec.ofNat 32 mm) mm) := by
    rw [accV_congr2 (M := m7.mem) (b := T) 8 fun i hi => by rw [← hMc]; exact copyWords_load 8 i hi (by omega)]
    refine fl_accV hm30 (by omega) (fun q hq => ?_) (fun q h1 h2 => ?_)
    · rw [hl7 q hq]
      exact congrArg beNat (memBytes_congr fun i hi => by rw [mem6]; exact IMz _ (hIn q hq i hi))
    · rw [← fillWords_load (M := Ms) (dst := T) (v := 0) 8 q h2 (by omega), hMz]
      apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc]
      have hx : Sep (F + 0xFFFFFFE0) 0x20 (T + BitVec.ofNat 32 (4 * q + j)) 1 := by
        rw [eFG, ← hT, add_ofNat_assoc]
        have := offs0 (c := 0) (n := 0x20) (d := 0x2C + (4 * q + j)) (k := 1) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have hTK : Sep T (4 * ((mm + 3) / 4)) (T + BitVec.ofNat 32 (4 * q + j)) 1 := by
        have := sep_offsets T (c := 0) (n := 4 * ((mm + 3) / 4)) (d := 4 * q + j) (k := 1) (by omega) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at this
      rw [fr7 _ hx hTK, mem6]
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (.cons d9 (.cons d10
    (c11.trans (c12.trans (c13.trans (.cons d14 (.single d15)))))))))))))), ?_, ?_, fun q hq => ?_, ?_,
    fun x hx hl => ?_⟩
  · rw [pc15, ← regs15, hslot ra 0x3C (by decide), hra, add_lit_zero, hret]
  · rw [regs15]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp, eFS]
  · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27]) q hq with rfl | rfl | rfl | rfl | rfl | hL
    · exact hslot _ 0x3C (by decide)
    · exact hslot _ 0x38 (by decide)
    · exact hslot _ 0x34 (by decide)
    · exact hslot _ 0x30 (by decide)
    · exact hslot _ 0x2C (by decide)
    · obtain ⟨hv, hs, hps, h1, h2, h3, h4, h5, h6, h7, ht0, ht1, hr, h0, h19, h8, h9, h18⟩ :
          q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ fcPs, p.1 ≠ q) ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧
          q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ (19 : Fin 32) ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧
          q ≠ (18 : Fin 32) := by revert hL; revert q; decide
      rw [regs15, upd_ne hv hs, rr _ _ q hv hps, k12 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 hr, K11 q h1 h2 h0, K9 q h0,
        K7' q hq hr, K5 q h2 h3 h0 h1 h4, K4 q h2 h3 h4 h5 h6 hr h19 h8 h9 h18 h0 h1 hs]
  · rw [mem15]; exact val
  · rw [mem15]; exact FrC x hx hl

end C3.RV32
