import C3BootProofs.Proofs.Ed25519VerifyP3

/-!
# `ed25519_verify`, offsets 0xF70 to 0x104C: `R` decoded

The function copies `R ‖ s` to `F + 0x228` and `F + 0x1E8`, decompresses
`R`, and rejects the signature unless `R` is a point, and neither `R` nor
the key's point `A` is of small order. `R`'s coordinates end at
`F + 0x268`.
-/

namespace C3.RV32

open C3.Image

/-- Whether `R` decodes to a point and neither it nor `A = (AX, AY, AZ)` is
of small order. -/
def evRok (o : Option (List Nat × List Nat × List Nat × List Nat)) (AX AY AZ : List Nat) : Bool :=
  match o with
  | none => false
  | some (X, Y, Z, _) => !isoSpec X Y Z && !isoSpec AX AY AZ

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

theorem flag_iso : ∀ b : Bool, branchTaken .bne (if b then (1 : Word) else 0) 0 = b := by decide
theorem flag_iso0 : ∀ b : Bool, branchTaken .beq (if b then (1 : Word) else 0) 0 = !b := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xF70: `R ‖ s` to `F + 0x228` and `F + 0x1E8`, and `R`
decompressed into `F + 0xEF0`. -/
theorem ev_rcp (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0xF70)
    (h8 : reg n 8 = F + BitVec.ofNat 32 0x330)
    (hR : ∀ j, j < 64 → M (F + BitVec.ofNat 32 (0x310 + j)) = M0 (sig + BitVec.ofNat 32 j)) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0xFD4 ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      DecOut M' (F + BitVec.ofNat 32 0xEF0) (evDec M0 (memBytes M0 sig 32)) ∧
      (∀ j, j < 64 → M' (F + BitVec.ofNat 32 (0x1E8 + j)) = M0 (sig + BitVec.ofNat 32 j)) ∧
      (∀ j, j < 64 → M' (F + BitVec.ofNat 32 (0x228 + j)) = M0 (sig + BitVec.ofNat 32 j)) ∧
      ∀ c, c < 0x16A0 → (c < 0x1E8 ∨ (0x268 ≤ c ∧ c < 0xEF0) ∨ 0xF94 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have ev : ∀ {M' : Word → BitVec 8} {f : Fin 32 → Word} {blk : List BInstr} (q : Fin 32), f 0 = 0 →
      q ∉ blk.filterMap BInstr.dst → (runBlock blk (M', f)).2 q = f q := fun q h0 h => runBlock_reg _ _ _ q h0 h
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0xF7E)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x711, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (8 : Fin 32)]
    (blockEnd_cons' ev_at_f70 rfl (blockEnd_cons' ev_at_f74 rfl (blockEnd_cons' ev_at_f78 rfl
      (blockEnd_cons' ev_at_f7c rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, k2, fz2⟩ := D1.memcpy C (d := 0xF10) (s := F + BitVec.ofNat 32 0x330) (N := 32)
    ev_at_f7e ev_at_f82 (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h8]; exact BitVec.zero_add _)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0xF94)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x6F1, .aluImm .add a1 sp 0x310, .aluImm .add a2 x0 0x20]
    (blockEnd_cons' ev_at_f86 rfl (blockEnd_cons' ev_at_f8a rfl (blockEnd_cons' ev_at_f8e rfl
      (blockEnd_cons' ev_at_f90 rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, fz4⟩ := D3.memcpy C (d := 0xEF0) (s := F + BitVec.ofNat 32 0x310) (N := 32)
    ev_at_f94 ev_at_f98 (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0xFAA)
    [.aluImm .add a0 sp 0x228, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F1, .aluImm .add a2 x0 0x40]
    (blockEnd_cons' ev_at_f9c rfl (blockEnd_cons' ev_at_f9e rfl (blockEnd_cons' ev_at_fa2 rfl
      (blockEnd_cons' ev_at_fa6 rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, fz6⟩ := D5.memcpy C (d := 0x228) (s := F + BitVec.ofNat 32 0xEF0) (N := 0x40)
    ev_at_faa ev_at_fae (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0xFBA)
    [.aluImm .add a0 sp 0x1E8, .aluImm .add a1 sp 0x228, .aluImm .add a2 x0 0x40]
    (blockEnd_cons' ev_at_fb2 rfl (blockEnd_cons' ev_at_fb4 rfl (blockEnd_cons' ev_at_fb6 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n8, c8, D8, k8, fz8⟩ := D7.memcpy C (d := 0x1E8) (s := F + BitVec.ofNat 32 0x228) (N := 0x40)
    ev_at_fba ev_at_fbe (by decide) (by decide)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; rfl)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; rfl)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0xFCC)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x6F1, .aluImm .add a1 sp 0x228]
    (blockEnd_cons' ev_at_fc2 rfl (blockEnd_cons' ev_at_fc6 rfl (blockEnd_cons' ev_at_fca rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  -- The bytes after the four copies.
  have B2 : ∀ j, j < 32 → n2.mem (F + BitVec.ofNat 32 (0xF10 + j)) = M0 (sig + BitVec.ofNat 32 (32 + j)) := fun j hj => by
    rw [cp_at C fz2 (by decide) hj, add_ofNat_assoc, show 0x330 + j = 0x310 + (32 + j) by omega, hR _ (by omega)]
  have B4 : ∀ j, j < 64 → n4.mem (F + BitVec.ofNat 32 (0xEF0 + j)) = M0 (sig + BitVec.ofNat 32 j) := fun j hj => by
    by_cases h : j < 32
    · rw [cp_at C fz4 (by decide) h, add_ofNat_assoc, cp_out C fz2 (by decide) (by omega) (by omega), hR _ (by omega)]
    · rw [cp_out C fz4 (by decide) (by omega) (by omega), show 0xEF0 + j = 0xF10 + (j - 32) by omega, B2 _ (by omega),
        show 32 + (j - 32) = j by omega]
  have B6 : ∀ j, j < 64 → n6.mem (F + BitVec.ofNat 32 (0x228 + j)) = M0 (sig + BitVec.ofNat 32 j) := fun j hj => by
    rw [cp_at C fz6 (by decide) hj, add_ofNat_assoc, B4 j hj]
  have B8 : ∀ j, j < 64 → n8.mem (F + BitVec.ofNat 32 (0x1E8 + j)) = M0 (sig + BitVec.ofNat 32 j) := fun j hj => by
    rw [cp_at C fz8 (by decide) hj, add_ofNat_assoc, B6 j hj]
  have B8' : ∀ j, j < 64 → n8.mem (F + BitVec.ofNat 32 (0x228 + j)) = M0 (sig + BitVec.ofNat 32 j) := fun j hj => by
    rw [cp_out C fz8 (by decide) (by omega) (by omega), B6 j hj]
  have bR : memBytes n8.mem (F + BitVec.ofNat 32 0x228) 32 = memBytes M0 sig 32 := by
    unfold memBytes; refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    rw [add_ofNat_assoc, B8' j (by omega)]
  obtain ⟨n10, c10, D10, k10, o10, fz10⟩ := D9.decompress C (d := 0xEF0) (e := 0x228) ev_at_fcc ev_at_fd0 (by decide)
    (by decide)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; rfl)
    (by decide) (by decide) (by decide)
  rw [bR] at o10
  have fr10 : ∀ c, c < 0x16A0 → (c < 0xEF0 ∨ 0xF94 ≤ c) → n10.mem (F + BitVec.ofNat 32 c) = n8.mem (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => fz10 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))
  refine ⟨n10, n10.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
    (c9.trans c10)))))))), D10, fun q hq => ?_, o10, fun j hj => ?_, fun j hj => ?_, fun c h1 h2 => ?_⟩
  · rw [k10 q hq, hr9, ev q D8.st.zero (by revert hq; revert q; decide), k8 q hq, hr7,
      ev q D6.st.zero (by revert hq; revert q; decide), k6 q hq, hr5, ev q D4.st.zero (by revert hq; revert q; decide),
      k4 q hq, hr3, ev q D2.st.zero (by revert hq; revert q; decide), k2 q hq, hr1,
      ev q D.st.zero (by revert hq; revert q; decide)]
  · rw [fr10 _ (by omega) (Or.inl (by omega)), B8 j hj]
  · rw [fr10 _ (by omega) (Or.inl (by omega)), B8' j hj]
  · rw [fr10 c h1 (by omega), cp_out C fz8 (by decide) h1 (by omega), cp_out C fz6 (by decide) h1 (by omega),
      cp_out C fz4 (by decide) h1 (by omega), cp_out C fz2 (by decide) h1 (by omega)]

theorem feW_bytes {M M' : Word → BitVec 8} {F : Word} {a b : Nat}
    (h : ∀ j, j < 40 → M' (F + BitVec.ofNat 32 (a + j)) = M (F + BitVec.ofNat 32 (b + j))) :
    feW M' (F + BitVec.ofNat 32 a) = feW M (F + BitVec.ofNat 32 b) :=
  feW_eq2 fun i hi => vk_ld2 fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
    exact h _ (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xFD4: rejects unless `R` decompressed, then copies its
coordinates to `F + 0x268` and rejects if `R` or `A` is of small order. -/
theorem ev_rchk (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0xFD4)
    (h19 : reg n 19 = F + 0x90F) {o : Option (List Nat × List Nat × List Nat × List Nat)}
    (hD : DecOut M (F + BitVec.ofNat 32 0xEF0) o) {AX AY AZ : List Nat} (hAX : feW M (F + BitVec.ofNat 32 0x148) = AX)
    (hAY : feW M (F + BitVec.ofNat 32 0x170) = AY) (hAZ : feW M (F + BitVec.ofNat 32 0x198) = AZ) :
    ∃ n' M', Steps n n' ∧ (evRok o AX AY AZ = false → EvSt M0 Ms F r0 M' n' 0x100A ∧ reg n' a0 = 0) ∧
      (evRok o AX AY AZ = true → EvSt M0 Ms F r0 M' n' 0x104C ∧
        (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
        (∃ X Y Z T, o = some (X, Y, Z, T) ∧ feW M' (F + BitVec.ofNat 32 0x268) = X ∧
          feW M' (F + BitVec.ofNat 32 0x290) = Y ∧ feW M' (F + BitVec.ofNat 32 0x2B8) = Z ∧
          feW M' (F + BitVec.ofNat 32 0x2E0) = T) ∧
        ∀ c, c < 0x16A0 → (c < 0x268 ∨ 0x308 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) := by
  have ev : ∀ {M' : Word → BitVec 8} {f : Fin 32 → Word} {blk : List BInstr} (q : Fin 32), f 0 = 0 →
      q ∉ blk.filterMap BInstr.dst → (runBlock blk (M', f)).2 q = f q := fun q h0 h => runBlock_reg _ _ _ q h0 h
  have eT : reg n 19 + 0x5E1 = F + BitVec.ofNat 32 0xEF0 := by rw [h19, BitVec.add_assoc]; rfl
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0xFD8) [.lw a0 (19 : Fin 32) 0x5E1] (bEnd1 ev_at_fd4 rfl)
    ⟨by show (reg n 19 + 0x5E1).toNat % 4 = 0
        rw [eT]; exact C.al (by decide), trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have va1 : reg n1 a0 = memLoad32 M (F + BitVec.ofNat 32 0xEF0) := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [eT]
  have hc1 := D1.code C
  have k1 : ∀ q : Fin 32, q.val ∈ evKeep → reg n1 q = reg n q := fun q hq => by
    rw [hr1, ev q D.st.zero (by revert hq; revert q; decide)]
  cases o with
  | none =>
    obtain ⟨n2, d2, u2⟩ := D1.st.taken hc1 0x1008 ev_at_fd8 (by decide)
      (by rw [va1, show memLoad32 M (F + BitVec.ofNat 32 0xEF0) = 0 from hD, D1.st.zero]; decide)
    obtain ⟨n3, c3, D3, hr3⟩ := (D1.jmp u2).block C (off' := 0x100A) [.aluImm .add a0 x0 0] (bEnd1 ev_at_1008 rfl)
      ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    refine ⟨n3, M, c1.trans (.cons d2 c3), fun _ => ⟨D3, ?_⟩, fun h => by cases h⟩
    rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u2.regs, D1.st.zero]; rfl
  | some P =>
    obtain ⟨X, Y, Z, T⟩ := P
    obtain ⟨tag, hX, hY, hZ, hT⟩ := hD
    obtain ⟨n2, d2, u2⟩ := D1.st.notTaken hc1 0xFDA ev_at_fd8 (by decide)
      (by rw [va1, tag, D1.st.zero]; decide)
    have D2 := D1.jmp u2
    obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0xFE8)
      [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F5, .aluImm .add a0 sp 0x268, .aluImm .add a2 x0 0xA0]
      (blockEnd_cons' ev_at_fda rfl (blockEnd_cons' ev_at_fde rfl (blockEnd_cons' ev_at_fe2 rfl
        (blockEnd_cons' ev_at_fe4 rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n4, c4, D4, k4, fz4⟩ := D3.memcpy C (d := 0x268) (s := F + BitVec.ofNat 32 0xEF4) (N := 0xA0)
      ev_at_fe8 ev_at_fec (by decide) (by decide)
      (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u2.regs, D1.hsp]; rfl)
      (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u2.regs, D1.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]
          exact add_sp F rfl)
      (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
      (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
      (by rw [C.fN (by decide)]; have := C.hhi; omega)
    -- `R`'s coordinates at `F + 0x268`.
    have cp : ∀ e, e + 40 ≤ 0xA0 → feW n4.mem (F + BitVec.ofNat 32 (0x268 + e)) = feW M (F + BitVec.ofNat 32 (0xEF4 + e)) :=
      fun e he => feW_bytes fun j hj => by
        rw [Nat.add_assoc, cp_at C fz4 (by decide) (by omega), add_ofNat_assoc, Nat.add_assoc]
    have eX : feW n4.mem (F + BitVec.ofNat 32 0x268) = X := by
      rw [cp 0 (by decide)]; rw [← hX, add_ofNat_assoc]
    have eY : feW n4.mem (F + BitVec.ofNat 32 0x290) = Y := by
      rw [cp 0x28 (by decide)]; rw [← hY, add_ofNat_assoc, add_ofNat_assoc]
    have eZ : feW n4.mem (F + BitVec.ofNat 32 0x2B8) = Z := by
      rw [cp 0x50 (by decide)]; rw [← hZ, add_ofNat_assoc, add_ofNat_assoc]
    have eT' : feW n4.mem (F + BitVec.ofNat 32 0x2E0) = T := by
      rw [cp 0x78 (by decide)]; rw [← hT, add_ofNat_assoc, add_ofNat_assoc]
    have fA : ∀ c, c < 0x16A0 → (c < 0x268 ∨ 0x308 ≤ c) → n4.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
      fun c h1 h2 => cp_out C fz4 (by decide) h1 (by omega)
    obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0xFF2) [.aluImm .add a0 sp 0x268] (bEnd1 ev_at_ff0 rfl)
      ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n6, c6, D6, k6, a06, f6⟩ := D5.iso C (d := 0x268) ev_at_ff2 ev_at_ff6 (by decide) (by decide)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl) (by decide) (by decide)
    rw [show F + BitVec.ofNat 32 0x268 + (0x28 : Word) = F + BitVec.ofNat 32 0x290 from add_ofNat_assoc F 0x268 0x28,
      show F + BitVec.ofNat 32 0x268 + (0x50 : Word) = F + BitVec.ofNat 32 0x2B8 from add_ofNat_assoc F 0x268 0x50,
      eX, eY, eZ] at a06
    have keep6 : ∀ q : Fin 32, q.val ∈ evKeep → reg n6 q = reg n q := fun q hq => by
      rw [k6 q hq, hr5, ev q D4.st.zero (by revert hq; revert q; decide), k4 q hq, hr3,
        ev q D2.st.zero (by revert hq; revert q; decide), u2.regs, k1 q hq]
    have hc6 := D6.code C
    cases hR : isoSpec X Y Z with
    | true =>
      rw [hR] at a06
      obtain ⟨n7, d7, u7⟩ := D6.st.taken hc6 0x1008 ev_at_ffa (by decide) (by rw [a06, D6.st.zero]; rfl)
      obtain ⟨n8, c8, D8, hr8⟩ := (D6.jmp u7).block C (off' := 0x100A) [.aluImm .add a0 x0 0] (bEnd1 ev_at_1008 rfl)
        ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
      refine ⟨n8, n6.mem, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 c8)))))),
        fun _ => ⟨D8, ?_⟩, fun h => by simp only [evRok, hR] at h; cases h⟩
      rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u7.regs, D6.st.zero]; rfl
    | false =>
      rw [hR] at a06
      obtain ⟨n7, d7, u7⟩ := D6.st.notTaken hc6 0xFFC ev_at_ffa (by decide) (by rw [a06, D6.st.zero]; rfl)
      have D7 := D6.jmp u7
      obtain ⟨n8, c8, D8, hr8⟩ := D7.block C (off' := 0xFFE) [.aluImm .add a0 sp 0x148] (bEnd1 ev_at_ffc rfl)
        ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
      obtain ⟨n9, c9, D9, k9, a09, f9⟩ := D8.iso C (d := 0x148) ev_at_ffe ev_at_1002 (by decide) (by decide)
        (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u7.regs, D6.hsp]; rfl)
        (by decide) (by decide)
      have mA : ∀ e, e + 40 ≤ 0x120 → feW n6.mem (F + BitVec.ofNat 32 (0x148 + e)) = feW M (F + BitVec.ofNat 32 (0x148 + e)) :=
        fun e he => feW_bytes fun j hj => by
          rw [Nat.add_assoc, f6 _ (C.zF (by omega)), fA _ (by omega) (by omega)]
      rw [show F + BitVec.ofNat 32 0x148 + (0x28 : Word) = F + BitVec.ofNat 32 (0x148 + 0x28) from add_ofNat_assoc F 0x148 0x28,
        show F + BitVec.ofNat 32 0x148 + (0x50 : Word) = F + BitVec.ofNat 32 (0x148 + 0x50) from add_ofNat_assoc F 0x148 0x50,
        show F + BitVec.ofNat 32 0x148 = F + BitVec.ofNat 32 (0x148 + 0) from rfl,
        mA 0 (by decide), mA 0x28 (by decide), mA 0x50 (by decide)] at a09
      rw [show (0x148 + 0 : Nat) = 0x148 from rfl, show (0x148 + 0x28 : Nat) = 0x170 from rfl,
        show (0x148 + 0x50 : Nat) = 0x198 from rfl, hAX, hAY, hAZ] at a09
      have hc9 := D9.code C
      have keep9 : ∀ q : Fin 32, q.val ∈ evKeep → reg n9 q = reg n q := fun q hq => by
        rw [k9 q hq, hr8, ev q (by rw [u7.regs]; exact D6.st.zero) (by revert hq; revert q; decide), u7.regs, keep6 q hq]
      have fR : ∀ c, c < 0x16A0 → n9.mem (F + BitVec.ofNat 32 c) = n4.mem (F + BitVec.ofNat 32 c) := fun c h1 => by
        rw [f9 _ (C.zF (by omega)), f6 _ (C.zF (by omega))]
      cases hA : isoSpec AX AY AZ with
      | true =>
        rw [hA] at a09
        obtain ⟨n10, d10, u10⟩ := D9.st.notTaken hc9 0x1008 ev_at_1006 (by decide) (by rw [a09, D9.st.zero]; rfl)
        obtain ⟨n11, c11, D11, hr11⟩ := (D9.jmp u10).block C (off' := 0x100A) [.aluImm .add a0 x0 0]
          (bEnd1 ev_at_1008 rfl) ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
        refine ⟨n11, n9.mem, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 (c8.trans
          (c9.trans (.cons d10 c11))))))))), fun _ => ⟨D11, ?_⟩, fun h => by simp only [evRok, hR, hA] at h; cases h⟩
        rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u10.regs, D9.st.zero]; rfl
      | false =>
        rw [hA] at a09
        obtain ⟨n10, d10, u10⟩ := D9.st.taken hc9 0x104C ev_at_1006 (by decide) (by rw [a09, D9.st.zero]; rfl)
        refine ⟨n10, n9.mem, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 (c8.trans
          (c9.trans (.single d10))))))))), fun h => (by simp only [evRok, hR, hA] at h; cases h),
          fun _ => ⟨D9.jmp u10, fun q hq => by rw [u10.regs, keep9 q hq], ⟨X, Y, Z, T, rfl, ?_, ?_, ?_, ?_⟩,
            fun c h1 h2 => by rw [fR c h1, fA c h1 h2]⟩⟩
        · rw [← eX]; exact feW_frame fun i hi => memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc, add_ofNat_assoc]; exact fR _ (by omega)
        · rw [← eY]; exact feW_frame fun i hi => memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc, add_ofNat_assoc]; exact fR _ (by omega)
        · rw [← eZ]; exact feW_frame fun i hi => memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc, add_ofNat_assoc]; exact fR _ (by omega)
        · rw [← eT']; exact feW_frame fun i hi => memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc, add_ofNat_assoc]; exact fR _ (by omega)

end

end C3.RV32
