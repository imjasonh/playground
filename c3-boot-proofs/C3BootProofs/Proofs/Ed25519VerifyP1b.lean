import C3BootProofs.Proofs.Ed25519VerifyP1

/-!
# `ed25519_verify`, offsets 0x7E to 0x17C: decoding and copies

The function decodes the key with `VerifyingKey::from_bytes` into
`F + 0xEF0`, rejects it when that fails, copies the key to `F + 0x128` and
the signature to `F + 0x310` and its `s` to `F + 0x8F0`, keeps whether
the top bit of `s` is clear at `F + 0xD0`, and loads `s` as eight
little-endian words at `F + 0x9F0`.
-/

namespace C3.RV32

open C3.Image

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

/-- The address moves at offsets 0x7E to 0x90. -/
def evB7E : List BInstr :=
  [.aluImm .add (20 : Fin 32) sp 0x7FF, .aluImm .add (20 : Fin 32) (20 : Fin 32) 0x110, .aluImm .add a0 sp 0x7FF,
   .aluImm .add a0 a0 0x6F1, .alu .add a1 x0 (9 : Fin 32)]

theorem evB7E_end : blockEnd ed25519VerifyCode 0x7E evB7E = some 0x90 :=
  blockEnd_cons' ev_at_7e rfl (blockEnd_cons' ev_at_82 rfl (blockEnd_cons' ev_at_86 rfl (blockEnd_cons' ev_at_8a rfl
    (blockEnd_cons' ev_at_8e rfl rfl))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0x7E: `VerifyingKey::from_bytes` on the key into
`F + 0xEF0`, to the epilogue with `a0 = 0` when the key names no point and
to offset 0xA0 when it does. -/
theorem ev_vk (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x7E)
    (h9 : reg n 9 = pk) :
    ∃ n' M', Steps n n' ∧ (∀ q : Fin 32, q.val ∈ [8, 18, 19, 21] → reg n' q = reg n q) ∧
      reg n' 20 = F + BitVec.ofNat 32 0x90F ∧
      (evDec M0 (memBytes M0 pk 32) = none → EvSt M0 Ms F r0 M' n' 0x100A ∧ reg n' a0 = 0) ∧
      (∀ P, evDec M0 (memBytes M0 pk 32) = some P → EvSt M0 Ms F r0 M' n' 0xA0 ∧
        VkOut M' (F + BitVec.ofNat 32 0xEF0) (memBytes M0 pk 32) (some P) ∧
        ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 0xEF0) 0xC4 x 1 → M' x = M x) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C evB7E evB7E_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB7E, runBlock, BInstr.run, upd, ↓reduceIte])
  have v20 : reg n1 20 = F + BitVec.ofNat 32 0x90F := by
    rw [hr1]; simp +decide only [evB7E, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  have va0 : reg n1 a0 = F + BitVec.ofNat 32 0xEF0 := by
    rw [hr1]; simp +decide only [evB7E, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  have va1 : reg n1 a1 = pk := by
    rw [hr1]; simp +decide only [evB7E, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [h9]; exact BitVec.zero_add _
  have r1 : ∀ q : Fin 32, q.val ∈ [8, 18, 19, 21] → reg n1 q = reg n q := fun q hq => by
    have h0 : q.val ≠ 0 := by revert hq; revert q; decide
    have h1 : q ≠ 20 := by revert hq; revert q; decide
    have h2 : q ≠ a0 := by revert hq; revert q; decide
    have h3 : q ≠ a1 := by revert hq; revert q; decide
    rw [hr1]; simp only [evB7E, runBlock, BInstr.run, upd, h0, h1, h2, h3, ↓reduceIte]
  obtain ⟨n2, c2, D2, k2, vk2, fr2⟩ := D1.vkFromBytes C ev_at_90 ev_at_94 (by decide) (by decide) va0 va1 (by decide)
    (by decide) C.sPk C.hpk
  have M2 := D2
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x9C) [.lw a0 (20 : Fin 32) 0x5E1] (bEnd1 ev_at_98 rfl)
    ⟨by show (reg n2 20 + 0x5E1).toNat % 4 = 0
        rw [k2 20 (by decide), v20, show F + BitVec.ofNat 32 0x90F + 0x5E1 = F + BitVec.ofNat 32 0xEF0 from
          add_ofNat_assoc F 0x90F 0x5E1]; exact C.al (by decide), trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have va3 : reg n3 a0 = memLoad32 n2.mem (F + BitVec.ofNat 32 0xEF0) := by
    rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [k2 20 (by decide), v20]; exact congrArg _ (add_ofNat_assoc F 0x90F 0x5E1)
  have r3 : ∀ q : Fin 32, q ≠ a0 → reg n3 q = reg n2 q := fun q hq => by
    rw [hr3]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D2.st.zero
  have q3 : ∀ q : Fin 32, q.val ∈ [8, 18, 19, 21] → reg n3 q = reg n q := fun q hq => by
    rw [r3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), r1 q hq]
  have v20' : reg n3 20 = F + BitVec.ofNat 32 0x90F := by rw [r3 _ (by decide), k2 20 (by decide), v20]
  unfold evDec
  generalize decSpec (feW M0 (BitVec.ofNat 32 edOneAddress)) (feW M0 (BitVec.ofNat 32 edDAddress))
    (feW M0 (BitVec.ofNat 32 edSqrtM1Address)) (memBytes M0 pk 32) = Dv at vk2 ⊢
  cases Dv with
  | none =>
    have hc := D3.code C
    obtain ⟨n4, d4, u4⟩ := D3.st.taken hc 0x1008 ev_at_9c (by decide)
      (by rw [va3, show memLoad32 n2.mem (F + BitVec.ofNat 32 0xEF0) = 1 from vk2, D3.st.zero]; decide)
    obtain ⟨n5, c5, D5, hr5⟩ := (D3.jmp u4).block C (off' := 0x100A) [.aluImm .add a0 x0 0] (bEnd1 ev_at_1008 rfl)
      ⟨trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have r5 : ∀ q : Fin 32, q ≠ a0 → reg n5 q = reg n3 q := fun q hq => by
      rw [hr5]; simp only [runBlock, BInstr.run]; rw [upd_ne' hq (by rw [u4.regs]; exact D3.st.zero), u4.regs]
    refine ⟨n5, n2.mem, c1.trans (c2.trans (c3.trans (.cons d4 c5))), fun q hq => by
      rw [r5 q (by revert hq; revert q; decide), q3 q hq], by rw [r5 _ (by decide), v20'],
      fun _ => ⟨D5, ?_⟩, fun P h => by cases h⟩
    rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [u4.regs, D3.st.zero]; rfl
  | some P =>
    have hc := D3.code C
    obtain ⟨X, Y, Z, T⟩ := P
    obtain ⟨n4, d4, u4⟩ := D3.st.notTaken hc 0xA0 ev_at_9c (by decide)
      (by rw [va3, show memLoad32 n2.mem (F + BitVec.ofNat 32 0xEF0) = 0 from vk2.1, D3.st.zero]; decide)
    exact ⟨n4, n2.mem, c1.trans (c2.trans (c3.trans (.single d4))), fun q hq => by rw [u4.regs, q3 q hq],
      by rw [u4.regs, v20'], fun h => (by cases h), fun P h => by cases h; exact ⟨D3.jmp u4, vk2, fr2⟩⟩

/-- A byte a copy into `F + d` wrote. -/
theorem cp_at (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {s : Word} {d N : Nat}
    (fz : ∀ x, Sep (evG F) 0xA10 x 1 → M' x = copyBytes M (F + BitVec.ofNat 32 d) s N x) (hd : d + N ≤ 0x16A0)
    {j : Nat} (hj : j < N) : M' (F + BitVec.ofNat 32 (d + j)) = M (s + BitVec.ofNat 32 j) := by
  rw [← add_ofNat_assoc, fz _ (by rw [add_ofNat_assoc]; exact C.zF (by omega)), cb_in hj (by omega)]

/-- A frame byte a copy into `F + d` did not write. -/
theorem cp_out (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {s : Word} {d N : Nat}
    (fz : ∀ x, Sep (evG F) 0xA10 x 1 → M' x = copyBytes M (F + BitVec.ofNat 32 d) s N x) (hd : d + N ≤ 0x16A0)
    {c : Nat} (hc : c < 0x16A0) (hs : c < d ∨ d + N ≤ c) : M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  rw [fz _ (C.zF (by omega)), copyBytes_sep (C.offs (c := d) (n := N) (d := c) (k := 1) (by omega) hd (by omega))
    (Nat.le_refl _)]

theorem EvCtx.zS (C : EvCtx M0 F pk sig msg len) {p : Word} {k : Nat} (h : Sep p k (evG F) 0x20B0) :
    Sep p k (evG F) 0xA10 := by
  have := h.subR (c := 0) (l := 0xA10) (by omega); rwa [add_ofNat_zero] at this

theorem EvCtx.fS (C : EvCtx M0 F pk sig msg len) {p : Word} {k c l : Nat} (h : Sep p k (evG F) 0x20B0)
    (hc : c + l ≤ 0x16A0) : Sep (F + BitVec.ofNat 32 c) l p k := by
  rw [evF_G]; exact (h.subR (by omega)).symm

/-- The moves at offsets 0xA2 to 0xB0. -/
def evBA2 : List BInstr :=
  [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F5, .aluImm .add a0 sp 0x128, .aluImm .add a2 x0 0xC0]

theorem evBA2_end : blockEnd ed25519VerifyCode 0xA2 evBA2 = some 0xB0 :=
  blockEnd_cons' ev_at_a2 rfl (blockEnd_cons' ev_at_a6 rfl (blockEnd_cons' ev_at_aa rfl
    (blockEnd_cons' ev_at_ac rfl rfl)))

/-- The moves at offsets 0xB8 to 0xCE. -/
def evBB8 : List BInstr :=
  [.aluImm .add (9 : Fin 32) sp 0x7FF, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x711, .aluImm .add a0 sp 0x7FF,
   .aluImm .add a0 a0 0x6F1, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (8 : Fin 32)]

theorem evBB8_end : blockEnd ed25519VerifyCode 0xB8 evBB8 = some 0xCE :=
  blockEnd_cons' ev_at_b8 rfl (blockEnd_cons' ev_at_bc rfl (blockEnd_cons' ev_at_c0 rfl
    (blockEnd_cons' ev_at_c4 rfl (blockEnd_cons' ev_at_c8 rfl (blockEnd_cons' ev_at_cc rfl rfl)))))

theorem keepB {blk : List BInstr} {M : Word → BitVec 8} {f : Fin 32 → Word} {q : Fin 32}
    (h : (runBlock blk (M, f)).2 q = f q) : (runBlock blk (M, f)).2 q = f q := h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0xA0: the message length to `F + 0x10`, the decoded key's
0xC0 bytes from `F + 0xEF4` to `F + 0x128`, and `R` to `F + 0xEF0`. -/
theorem ev_cp1 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0xA0)
    (h8 : reg n 8 = sig) (h18 : reg n 18 = BitVec.ofNat 32 len) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0xD6 ∧
      (∀ q : Fin 32, q.val ∈ [19, 20, 21] → reg n' q = reg n q) ∧ reg n' 9 = F + BitVec.ofNat 32 0xF10 ∧
      memLoad32 M' (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 len ∧
      (∀ j, j < 0xC0 → M' (F + BitVec.ofNat 32 (0x128 + j)) = M (F + BitVec.ofNat 32 (0xEF4 + j))) ∧
      (∀ j, j < 32 → M' (F + BitVec.ofNat 32 (0xEF0 + j)) = M0 (sig + BitVec.ofNat 32 j)) ∧
      ∀ c, c < 0x16A0 → (c < 0x10 ∨ (0x14 ≤ c ∧ c < 0x128) ∨ (0x1E8 ≤ c ∧ c < 0xEF0) ∨ 0xF10 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have hc := D.code C
  obtain ⟨n1, d1, u1⟩ := D.st.sw hc ev_at_a0 (off' := 0xA2) (by decide) (by rw [D.hsp]; exact C.al (by decide))
  rw [D.hsp, h18, show F + (0x10 : Word) = F + BitVec.ofNat 32 0x10 from rfl] at u1
  have D1 := D.store C (d := 0x10) (k := 4) u1.self (by rw [u1.regs, D.hsp]) (by rw [u1.regs]) (by rw [u1.regs])
    (by decide) (fun x hx => st32_frame hx)
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C evBA2 evBA2_end ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evBA2, runBlock, BInstr.run, upd, ↓reduceIte])
  have r2 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n2 q = reg n q := fun q h0 h1 h2 => by
    by_cases hz : q.val = 0
    · rw [show q = 0 from Fin.ext hz, D2.st.zero, D.st.zero]
    · rw [hr2, ← u1.regs q]; simp only [evBA2, runBlock, BInstr.run, upd, hz, h0, h1, h2, ↓reduceIte]
  obtain ⟨n3, c3, D3, k3, fz3⟩ := D2.memcpy C (d := 0x128) (s := F + BitVec.ofNat 32 0xEF4) (N := 0xC0)
    ev_at_b0 ev_at_b4 (by decide) (by decide)
    (by rw [hr2]; simp +decide only [evBA2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [u1.regs, D.hsp]; rfl)
    (by rw [hr2]; simp +decide only [evBA2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [u1.regs, D.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr2]; simp +decide only [evBA2, runBlock, BInstr.run, upd, ↓reduceIte])
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n4, c4, D4, hr4⟩ := D3.block C evBB8 evBB8_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evBB8, runBlock, BInstr.run, upd, ↓reduceIte])
  have r4 : ∀ q : Fin 32, q.val ∈ [19, 20, 21] → reg n4 q = reg n q := fun q hq => by
    have h0 : q.val ≠ 0 := by revert hq; revert q; decide
    rw [hr4]; simp only [evBB8, runBlock, BInstr.run, upd, h0, show q ≠ 9 by revert hq; revert q; decide,
      show q ≠ a0 by revert hq; revert q; decide, show q ≠ a1 by revert hq; revert q; decide,
      show q ≠ a2 by revert hq; revert q; decide, ↓reduceIte]
    rw [k3 q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]
  obtain ⟨n5, c5, D5, k5, fz5⟩ := D4.memcpy C (d := 0xEF0) (s := sig) (N := 32) ev_at_ce ev_at_d2 (by decide) (by decide)
    (by rw [hr4]; simp +decide only [evBB8, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D3.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr4]; simp +decide only [evBB8, runBlock, BInstr.run, upd, ↓reduceIte]; rw [k3 8 (by decide),
      r2 8 (by decide) (by decide) (by decide), h8]; exact BitVec.zero_add _)
    (by rw [hr4]; simp +decide only [evBB8, runBlock, BInstr.run, upd, ↓reduceIte])
    (by decide) (C.zS C.sig0) (C.fS C.sig0 (by decide)) (by have := C.hsig; omega)
  have v9 : reg n5 9 = F + BitVec.ofNat 32 0xF10 := by
    rw [k5 9 (by decide), hr4]; simp +decide only [evBB8, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D3.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  have M3e : ∀ c, c < 0x16A0 → (c < 0x10 ∨ 0x14 ≤ c) →
      memStore32 M (F + BitVec.ofNat 32 0x10) (BitVec.ofNat 32 len) (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => st32_frame (C.offs (by omega) (by decide) (by omega))
  refine ⟨n5, n5.mem, c2 |> fun c => .cons d1 (c.trans (c3.trans (c4.trans c5))), D5, fun q hq => by
    rw [k5 q (by revert hq; revert q; decide), r4 q hq], v9, ?_, fun j hj => ?_, fun j hj => ?_, fun c h1 h2 => ?_⟩
  · rw [memLoad32_congr (M := memStore32 M (F + BitVec.ofNat 32 0x10) (BitVec.ofNat 32 len)) fun j hj => by
      rw [add_ofNat_assoc, cp_out C fz5 (by decide) (by omega) (by omega), cp_out C fz3 (by decide) (by omega) (by omega)],
      memLoad32_store32_same]
  · rw [cp_out C fz5 (by decide) (by omega) (by omega), cp_at C fz3 (by decide) hj, add_ofNat_assoc, M3e _ (by omega)
      (by omega)]
  · rw [cp_at C fz5 (by decide) hj]; exact D4.agree _ (C.sig0.sub (c := j) (l := 1) (by omega)).symm
  · rw [cp_out C fz5 (by decide) h1 (by omega), cp_out C fz3 (by decide) h1 (by omega), M3e c h1 (by omega)]

def evBD6 : List BInstr := [.aluImm .add a2 x0 0x20, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (19 : Fin 32)]

theorem evBD6_end : blockEnd ed25519VerifyCode 0xD6 evBD6 = some 0xDE :=
  blockEnd_cons' ev_at_d6 rfl (blockEnd_cons' ev_at_da rfl (blockEnd_cons' ev_at_dc rfl rfl))

def evBE6 : List BInstr :=
  [.aluImm .add a0 sp 0x310, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F1, .aluImm .add a2 x0 0x40]

theorem evBE6_end : blockEnd ed25519VerifyCode 0xE6 evBE6 = some 0xF4 :=
  blockEnd_cons' ev_at_e6 rfl (blockEnd_cons' ev_at_e8 rfl (blockEnd_cons' ev_at_ec rfl
    (blockEnd_cons' ev_at_f0 rfl rfl)))

def evBFC : List BInstr :=
  [.aluImm .add a1 sp 0x330, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0xF1, .aluImm .add a2 x0 0x20,
   .aluImm .add (8 : Fin 32) sp 0x7FF, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xF1]

theorem evBFC_end : blockEnd ed25519VerifyCode 0xFC evBFC = some 0x112 :=
  blockEnd_cons' ev_at_fc rfl (blockEnd_cons' ev_at_fe rfl (blockEnd_cons' ev_at_102 rfl
    (blockEnd_cons' ev_at_106 rfl (blockEnd_cons' ev_at_10a rfl (blockEnd_cons' ev_at_10e rfl rfl)))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0xD6: `s` to `F + 0xF10`, the 64 signature bytes from
`F + 0xEF0` to `F + 0x310`, and `s` from there to `F + 0x8F0`. -/
theorem ev_cp2 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0xD6)
    (h9 : reg n 9 = F + BitVec.ofNat 32 0xF10) (h19 : reg n 19 = sig + BitVec.ofNat 32 32)
    (hE : ∀ j, j < 32 → M (F + BitVec.ofNat 32 (0xEF0 + j)) = M0 (sig + BitVec.ofNat 32 j)) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x11A ∧
      (∀ q : Fin 32, q.val ∈ [20, 21] → reg n' q = reg n q) ∧ reg n' 8 = F + BitVec.ofNat 32 0x8F0 ∧
      (∀ j, j < 64 → M' (F + BitVec.ofNat 32 (0x310 + j)) = M0 (sig + BitVec.ofNat 32 j)) ∧
      (∀ j, j < 32 → M' (F + BitVec.ofNat 32 (0x8F0 + j)) = M0 (sig + BitVec.ofNat 32 (32 + j))) ∧
      ∀ c, c < 0x16A0 → (c < 0x310 ∨ (0x350 ≤ c ∧ c < 0x8F0) ∨ (0x910 ≤ c ∧ c < 0xF10) ∨ 0xF30 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C evBD6 evBD6_end ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evBD6, runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, k2, fz2⟩ := D1.memcpy C (d := 0xF10) (s := sig + BitVec.ofNat 32 32) (N := 32)
    ev_at_de ev_at_e2 (by decide) (by decide)
    (by rw [hr1]; simp +decide only [evBD6, runBlock, BInstr.run, upd, ↓reduceIte]; rw [h9]; exact BitVec.zero_add _)
    (by rw [hr1]; simp +decide only [evBD6, runBlock, BInstr.run, upd, ↓reduceIte]; rw [h19]; exact BitVec.zero_add _)
    (by rw [hr1]; simp +decide only [evBD6, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.st.zero]; rfl)
    (by decide) (C.zS C.sig32) (C.fS C.sig32 (by decide))
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := C.hsig; omega)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C evBE6 evBE6_end ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evBE6, runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, fz4⟩ := D3.memcpy C (d := 0x310) (s := F + BitVec.ofNat 32 0xEF0) (N := 0x40)
    ev_at_f4 ev_at_f8 (by decide) (by decide)
    (by rw [hr3]; simp +decide only [evBE6, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [evBE6, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr3]; simp +decide only [evBE6, runBlock, BInstr.run, upd, ↓reduceIte])
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C evBFC evBFC_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evBFC, runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, fz6⟩ := D5.memcpy C (d := 0x8F0) (s := F + BitVec.ofNat 32 0x330) (N := 32)
    ev_at_112 ev_at_116 (by decide) (by decide)
    (by rw [hr5]; simp +decide only [evBFC, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr5]; simp +decide only [evBFC, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by rw [hr5]; simp +decide only [evBFC, runBlock, BInstr.run, upd, ↓reduceIte])
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  have kq : ∀ q : Fin 32, q.val ∈ [20, 21] → reg n6 q = reg n q := fun q hq => by
    have h0 : q.val ≠ 0 := by revert hq; revert q; decide
    rw [k6 q (by revert hq; revert q; decide), hr5]
    simp only [evBFC, runBlock, BInstr.run, upd, h0, show q ≠ 8 by revert hq; revert q; decide,
      show q ≠ a0 by revert hq; revert q; decide, show q ≠ a1 by revert hq; revert q; decide,
      show q ≠ a2 by revert hq; revert q; decide, ↓reduceIte]
    rw [k4 q (by revert hq; revert q; decide), hr3]
    simp only [evBE6, runBlock, BInstr.run, upd, h0, show q ≠ a0 by revert hq; revert q; decide,
      show q ≠ a1 by revert hq; revert q; decide, show q ≠ a2 by revert hq; revert q; decide, ↓reduceIte]
    rw [k2 q (by revert hq; revert q; decide), hr1]
    simp only [evBD6, runBlock, BInstr.run, upd, h0, show q ≠ a0 by revert hq; revert q; decide,
      show q ≠ a1 by revert hq; revert q; decide, show q ≠ a2 by revert hq; revert q; decide, ↓reduceIte]
  refine ⟨n6, n6.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), D6, kq, ?_, fun j hj => ?_,
    fun j hj => ?_, fun c h1 h2 => ?_⟩
  · rw [k6 8 (by decide), hr5]; simp +decide only [evBFC, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D4.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  · rw [cp_out C fz6 (by decide) (by omega) (by omega), cp_at C fz4 (by decide) hj, add_ofNat_assoc]
    by_cases hj32 : j < 32
    · rw [cp_out C fz2 (by decide) (by omega) (by omega), hE j hj32]
    · rw [show 0xEF0 + j = 0xF10 + (j - 32) by omega, cp_at C fz2 (by decide) (by omega), add_ofNat_assoc,
        show 32 + (j - 32) = j by omega]
      exact D1.agree _ (C.sSig.sub (c := j) (l := 1) (by omega)).symm
  · rw [cp_at C fz6 (by decide) hj, add_ofNat_assoc, show 0x330 + j = 0x310 + (0x20 + j) by omega,
      cp_at C fz4 (by decide) (by omega), add_ofNat_assoc,
      show 0xEF0 + (0x20 + j) = 0xF10 + j by omega, cp_at C fz2 (by decide) hj, add_ofNat_assoc]
    exact D1.agree _ (C.sSig.sub (c := 32 + j) (l := 1) (by omega)).symm
  · rw [cp_out C fz6 (by decide) h1 (by omega), cp_out C fz4 (by decide) h1 (by omega),
      cp_out C fz2 (by decide) h1 (by omega)]

theorem srl7_lt : ∀ b : BitVec 8, (aluEval .srl (b.zeroExtend 32) 7).toNat < 256 := by decide

theorem srl7_eq : ∀ b : BitVec 8,
    (if aluEval .srl (b.zeroExtend 32) 7 = 0 then (1 : Word) else 0) = if b.toNat < 128 then 1 else 0 := by decide

def evB11A : List BInstr := [.lbu a0 (20 : Fin 32) 0, .aluImm .srl a0 a0 0x7, .aluImm .add a1 x0 0]

theorem evB11A_end : blockEnd ed25519VerifyCode 0x11A evB11A = some 0x122 :=
  blockEnd_cons' ev_at_11a rfl (blockEnd_cons' ev_at_11e rfl (blockEnd_cons' ev_at_120 rfl rfl))

def evB12C : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1F1, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0,
   .aluImm .add (18 : Fin 32) sp 0x7FF, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1F1]

theorem evB12C_end : blockEnd ed25519VerifyCode 0x12C evB12C = some 0x142 :=
  blockEnd_cons' ev_at_12c rfl (blockEnd_cons' ev_at_130 rfl (blockEnd_cons' ev_at_134 rfl
    (blockEnd_cons' ev_at_138 rfl (blockEnd_cons' ev_at_13a rfl (blockEnd_cons' ev_at_13e rfl rfl)))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0x11A: whether the top bit of `s` is clear, through
`ct_eq`, to `F + 0xD0`, and the 32 bytes at `F + 0x9F0` cleared. -/
theorem ev_cp3 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x11A)
    (h20 : reg n 20 = F + BitVec.ofNat 32 0x90F) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x14A ∧
      (∀ q : Fin 32, q.val ∈ [8, 20, 21] → reg n' q = reg n q) ∧ reg n' 18 = F + BitVec.ofNat 32 0x9F0 ∧
      memLoad32 M' (F + BitVec.ofNat 32 0xD0) = (if (M (F + BitVec.ofNat 32 0x90F)).toNat < 128 then 1 else 0) ∧
      (∀ j, j < 32 → M' (F + BitVec.ofNat 32 (0x9F0 + j)) = 0) ∧
      ∀ c, c < 0x16A0 → (c < 0xD0 ∨ (0xD4 ≤ c ∧ c < 0x9F0) ∨ 0xA10 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C evB11A evB11A_end ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB11A, runBlock, BInstr.run, upd, ↓reduceIte])
  have va0 : reg n1 a0 = aluEval .srl ((M (F + BitVec.ofNat 32 0x90F)).zeroExtend 32) 7 := by
    rw [hr1]; simp +decide only [evB11A, runBlock, BInstr.run, upd, ↓reduceIte]; rw [h20, add_lit_zero]; try rfl
  obtain ⟨n2, c2, D2, k2, a02, fz2⟩ := D1.ctEqU8 C (y := 0) ev_at_122 ev_at_126 (by decide) (by decide) va0
    (by rw [hr1]; simp +decide only [evB11A, runBlock, BInstr.run, upd, ↓reduceIte]; try rfl) (srl7_lt _) (by decide)
  rw [srl7_eq] at a02
  have hc := D2.code C
  obtain ⟨n3, d3, u3⟩ := D2.st.sw hc ev_at_12a (off' := 0x12C) (by decide) (by rw [D2.hsp]; exact C.al (by decide))
  rw [D2.hsp, a02, show F + (0xD0 : Word) = F + BitVec.ofNat 32 0xD0 from rfl] at u3
  have D3 := D2.store C (d := 0xD0) (k := 4) u3.self (by rw [u3.regs, D2.hsp]) (by rw [u3.regs]) (by rw [u3.regs])
    (by decide) (fun x hx => st32_frame hx)
  obtain ⟨n4, c4, D4, hr4⟩ := D3.block C evB12C evB12C_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB12C, runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n5, c5, D5, k5⟩ := D4.memset C (d := 0x9F0) (b := 0) (N := 32) ev_at_142 ev_at_146 (by decide) (by decide)
    (by rw [hr4]; simp +decide only [evB12C, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D3.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr4]; simp +decide only [evB12C, runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by rw [hr4]; simp +decide only [evB12C, runBlock, BInstr.run, upd, ↓reduceIte]; try rfl) (by decide)
  have M3 : ∀ c, c < 0x16A0 → (c < 0xD0 ∨ 0xD4 ≤ c) →
      memStore32 n2.mem (F + BitVec.ofNat 32 0xD0) (if (M (F + BitVec.ofNat 32 0x90F)).toNat < 128 then 1 else 0)
        (F + BitVec.ofNat 32 c) = n2.mem (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => st32_frame (C.offs (by omega) (by decide) (by omega))
  have fs : ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA10 ≤ c) → ∀ M' : Word → BitVec 8,
      fillBytes M' (F + BitVec.ofNat 32 0x9F0) (BitVec.extractLsb' 0 8 (0 : Word)) 32 (F + BitVec.ofNat 32 c) =
        M' (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 M' => fillBytes_sep (C.offs (by omega) (by decide) (by omega)) (Nat.le_refl _)
  refine ⟨n5, _, c1.trans (c2.trans (.cons d3 (c4.trans c5))), D5, fun q hq => ?_, ?_, ?_, fun j hj => ?_,
    fun c h1 h2 => ?_⟩
  · have h0 : q.val ≠ 0 := by revert hq; revert q; decide
    rw [k5 q (by revert hq; revert q; decide), hr4]
    simp only [evB12C, runBlock, BInstr.run, upd, h0, show q ≠ 18 by revert hq; revert q; decide,
      show q ≠ a0 by revert hq; revert q; decide, show q ≠ a1 by revert hq; revert q; decide,
      show q ≠ a2 by revert hq; revert q; decide, ↓reduceIte]
    rw [u3.regs, k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), hr1]
    simp only [evB11A, runBlock, BInstr.run, upd, h0, show q ≠ a0 by revert hq; revert q; decide,
      show q ≠ a1 by revert hq; revert q; decide, ↓reduceIte]
  · rw [k5 18 (by decide), hr4]; simp +decide only [evB12C, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D3.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  · rw [memLoad32_congr (M := memStore32 n2.mem (F + BitVec.ofNat 32 0xD0)
      (if (M (F + BitVec.ofNat 32 0x90F)).toNat < 128 then 1 else 0)) fun j hj => by
        rw [add_ofNat_assoc, fs _ (by omega) (by omega)], memLoad32_store32_same]
  · rw [← add_ofNat_assoc]; unfold fillBytes
    rw [add_sub_toNat _ (by omega), ite_eq_left hj]; rfl
  · rw [fs c h1 (by omega), M3 c h1 (by omega), fz2 _ (C.zF (by omega))]

/-- The first `j` bytes at `b`, little-endian. -/
def leAcc (M : Word → BitVec 8) (b : Word) : Nat → Nat
  | 0 => 0
  | j + 1 => leAcc M b j + (M (b + BitVec.ofNat 32 j)).toNat * 256 ^ j

theorem leAcc_lt (M : Word → BitVec 8) (b : Word) : ∀ j, leAcc M b j < 256 ^ j
  | 0 => by show 0 < 1; decide
  | j + 1 => by
    have := leAcc_lt M b j
    have hb := (M (b + BitVec.ofNat 32 j)).isLt
    simp only [leAcc, Nat.pow_succ]
    have : (M (b + BitVec.ofNat 32 j)).toNat * 256 ^ j ≤ 255 * 256 ^ j := Nat.mul_le_mul_right _ (by omega)
    omega

theorem or_shl (x a : Word) {k : Nat} (hx : x.toNat < 2 ^ k) (ha : a.toNat * 2 ^ k < 2 ^ 32) :
    (x ||| a <<< k).toNat = x.toNat + a.toNat * 2 ^ k := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha, Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]

theorem beq_inner : ∀ j, j < 4 → branchTaken .beq (aluEval .add (BitVec.ofNat 32 (8 * j)) 0xFFFFFFE0) 0 = false := by
  decide

def evB162 : List BInstr :=
  [.lbu a3 a5 0, .aluImm .add a5 a5 1, .alu .sll a3 a3 (9 : Fin 32), .aluImm .add (9 : Fin 32) (9 : Fin 32) 8,
   .alu .or a4 a4 a3]

theorem evB162_end : blockEnd ed25519VerifyCode 0x162 evB162 = some 0x170 :=
  blockEnd_cons' ev_at_162 rfl (blockEnd_cons' ev_at_166 rfl (blockEnd_cons' ev_at_168 rfl
    (blockEnd_cons' ev_at_16c rfl (blockEnd_cons' ev_at_16e rfl rfl))))

theorem inner_keep {q : Fin 32} (h : q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ (9 : Fin 32)) : q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ 9 := h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The inner loop at offset 0x15C: `a4` gains the bytes at `b` from `j`
to 4, little-endian. -/
theorem ev_inner (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {b : Word} :
    ∀ k j {n : Machine}, j + k = 4 → EvSt M0 Ms F r0 M n 0x15C → reg n 9 = BitVec.ofNat 32 (8 * j) →
      reg n a5 = b + BitVec.ofNat 32 j → (reg n a4).toNat = leAcc M b j →
      ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' 0x172 ∧ (reg n' a4).toNat = leAcc M b 4 ∧
        ∀ q : Fin 32, q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (9 : Fin 32) → reg n' q = reg n q
  | 0, j, n, hk, D, h9, ha5, ha4 => by
    obtain rfl : j = 4 := by omega
    obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x160) [.aluImm .add a3 (9 : Fin 32) 0xFFFFFFE0]
      (bEnd1 ev_at_15c rfl) ⟨trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n2, d2, u2⟩ := D1.st.taken (D1.code C) 0x172 ev_at_160 (by decide)
      (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h9, D1.st.zero]; decide)
    refine ⟨n2, c1.trans (.single d2), D1.jmp u2, by rw [u2.regs, hr1]; simpa +decide only [runBlock, BInstr.run, upd,
      ↓reduceIte] using ha4, fun q h3 h4 h5 h9' => ?_⟩
    by_cases h0 : q.val = 0
    · rw [show q = 0 from Fin.ext h0, u2.regs, D1.st.zero, D.st.zero]
    · rw [u2.regs, hr1]; simp only [runBlock, BInstr.run, upd, h0, h3, ↓reduceIte]
  | k + 1, j, n, hk, D, h9, ha5, ha4 => by
    have hj : j < 4 := by omega
    obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x160) [.aluImm .add a3 (9 : Fin 32) 0xFFFFFFE0]
      (bEnd1 ev_at_15c rfl) ⟨trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x162 ev_at_160 (by decide)
      (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h9, D1.st.zero]; exact beq_inner j hj)
    have D2 := D1.jmp u2
    obtain ⟨n3, c3, D3, hr3⟩ := D2.block C evB162 evB162_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB162, runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n4, d4, u4⟩ := D3.st.jump (D3.code C) ev_at_170 (off' := 0x15C) (by decide) (by rw [D3.st.pc]; decide)
    have D4 := D3.jmp u4
    have R1 : ∀ q : Fin 32, q ≠ a3 → reg n2 q = reg n q := fun q h => by
      by_cases h0 : q.val = 0
      · rw [show q = 0 from Fin.ext h0, D2.st.zero, D.st.zero]
      · rw [u2.regs, hr1]; simp only [runBlock, BInstr.run, upd, h0, h, ↓reduceIte]
    have hsh : (BitVec.ofNat 32 (8 * j)).toNat % 32 = 8 * j := by
      rw [BitVec.toNat_ofNat]; omega
    obtain ⟨n', c', D', ha4', kp'⟩ := ev_inner C k (j + 1) (by omega) D4
      (by rw [u4.regs, hr3]; simp +decide only [evB162, runBlock, BInstr.run, upd, ↓reduceIte]
          rw [R1 _ (by decide), h9, show (8 : Word) = BitVec.ofNat 32 8 from rfl]
          exact (BitVec.ofNat_add_ofNat ..).trans (congrArg _ (by omega)))
      (by rw [u4.regs, hr3]; simp +decide only [evB162, runBlock, BInstr.run, upd, ↓reduceIte]
          rw [R1 _ (by decide), ha5, show (1 : Word) = BitVec.ofNat 32 1 from rfl]; exact add_ofNat_assoc ..)
      (by
        rw [u4.regs, hr3]; simp +decide only [evB162, runBlock, BInstr.run, upd, ↓reduceIte]
        rw [R1 _ (by decide), R1 _ (by decide), R1 _ (by decide), ha5, h9, add_lit_zero, leAcc]
        have hb := (M (b + BitVec.ofNat 32 j)).isLt
        have hl := leAcc_lt M b j
        have e : aluEval .or (reg n a4) (aluEval .sll ((M (b + BitVec.ofNat 32 j)).zeroExtend 32)
            (BitVec.ofNat 32 (8 * j))) = reg n a4 ||| (M (b + BitVec.ofNat 32 j)).zeroExtend 32 <<< (8 * j) := by
          simp only [aluEval]; rw [hsh]
        rw [e, or_shl _ _ (by rw [ha4, Nat.pow_mul]; exact hl) (by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.pow_mul]
            have : (M (b + BitVec.ofNat 32 j)).toNat * 256 ^ j ≤ 255 * 256 ^ 3 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
            show (M (b + BitVec.ofNat 32 j)).toNat * 256 ^ j < 2 ^ 32; omega),
          ha4, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.pow_mul])
    refine ⟨n', c1.trans (.cons d2 (c3.trans (.cons d4 c'))), D', ha4', fun q h3 h4 h5 h9' => ?_⟩
    rw [kp' q h3 h4 h5 h9', u4.regs, hr3]
    by_cases h0 : q.val = 0
    · rw [show q = 0 from Fin.ext h0]; simp +decide only [evB162, runBlock, BInstr.run, upd, ↓reduceIte]
      exact D.st.zero.symm
    · simp only [evB162, runBlock, BInstr.run, upd, h0, h3, h4, h5, h9', ↓reduceIte]; exact R1 q h3

theorem leAcc_congr {M M' : Word → BitVec 8} {b : Word} :
    ∀ j, (∀ u, u < j → M (b + BitVec.ofNat 32 u) = M' (b + BitVec.ofNat 32 u)) → leAcc M b j = leAcc M' b j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [leAcc]; rw [leAcc_congr j fun u hu => h u (by omega), h j (by omega)]

/-- What the words loop keeps at the head of iteration `i`, from the memory
`Mb` before it. -/
structure WordsInv (F : Word) (Mb M : Word → BitVec 8) (i : Nat) : Prop where
  hW : ∀ t, t < i → memLoad32 M (F + BitVec.ofNat 32 (0x9F0 + 4 * t)) =
    BitVec.ofNat 32 (leAcc Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * t)) 4)
  hZ : ∀ j, 4 * i ≤ j → j < 32 → M (F + BitVec.ofNat 32 (0x9F0 + j)) = 0
  hK : ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA10 ≤ c) → M (F + BitVec.ofNat 32 c) = Mb (F + BitVec.ofNat 32 c)

theorem ld_zero {M : Word → BitVec 8} {a : Word} (h : ∀ j, j < 4 → M (a + BitVec.ofNat 32 j) = 0) :
    memLoad32 M a = 0 := by
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero] at h0
  unfold memLoad32
  rw [show a + 3 = a + BitVec.ofNat 32 3 from rfl, show a + 2 = a + BitVec.ofNat 32 2 from rfl,
    show a + 1 = a + BitVec.ofNat 32 1 from rfl, h 3 (by decide), h 2 (by decide), h 1 (by decide), h0]
  rfl

def evB150 : List BInstr :=
  [.aluImm .add (9 : Fin 32) x0 0, .aluImm .sll a2 a0 2, .alu .add a2 a2 (18 : Fin 32), .lw a4 a2 0,
   .alu .add a5 x0 (8 : Fin 32)]

theorem evB150_end : blockEnd ed25519VerifyCode 0x150 evB150 = some 0x15C :=
  blockEnd_cons' ev_at_150 rfl (blockEnd_cons' ev_at_152 rfl (blockEnd_cons' ev_at_156 rfl
    (blockEnd_cons' ev_at_158 rfl (blockEnd_cons' ev_at_15a rfl rfl))))

theorem evSll2 {i : Nat} (hi : i < 8) (G : Word) :
    aluEval .add (aluEval .sll (BitVec.ofNat 32 i) 2) G = G + BitVec.ofNat 32 (4 * i) := by
  have e : aluEval .sll (BitVec.ofNat 32 i) 2 = BitVec.ofNat 32 (4 * i) := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 i <<< ((2 : Word).toNat % 32)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 : Word).toNat % 32 = 2 from rfl,
      Nat.shiftLeft_eq]; omega
  rw [e]; exact BitVec.add_comm _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- One iteration of the words loop from offset 0x150: word `i` from the
four bytes at `F + 0x8F0 + 4i`. -/
theorem ev_outer (C : EvCtx M0 F pk sig msg len) {Mb M : Word → BitVec 8} {n : Machine} {i : Nat} (hi : i < 8)
    (D : EvSt M0 Ms F r0 M n 0x150) (W : WordsInv F Mb M i) (ha0 : reg n a0 = BitVec.ofNat 32 i)
    (ha1 : reg n a1 = 8) (h8 : reg n 8 = F + BitVec.ofNat 32 (0x8F0 + 4 * i)) (h18 : reg n 18 = F + BitVec.ofNat 32 0x9F0) :
    ∃ n' M', Steps n n' ∧ WordsInv F Mb M' (i + 1) ∧ reg n' a0 = BitVec.ofNat 32 (i + 1) ∧ reg n' a1 = 8 ∧
      reg n' 8 = F + BitVec.ofNat 32 (0x8F0 + 4 * (i + 1)) ∧ reg n' 18 = F + BitVec.ofNat 32 0x9F0 ∧
      (∀ q : Fin 32, q.val ∈ [20, 21] → reg n' q = reg n q) ∧
      (i + 1 < 8 → EvSt M0 Ms F r0 M' n' 0x150) ∧ (i + 1 = 8 → EvSt M0 Ms F r0 M' n' 0x17C) := by
  have ea2 : aluEval .add (aluEval .sll (reg n a0) 2) (reg n 18) = F + BitVec.ofNat 32 (0x9F0 + 4 * i) := by
    rw [ha0, h18, evSll2 hi, add_ofNat_assoc]
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C evB150 evB150_end
    ⟨trivial, trivial, trivial, by
      show (aluEval .add (aluEval .sll (reg n a0) 2) (reg n 18) + 0).toNat % 4 = 0
      rw [ea2, add_lit_zero]; exact C.al (by omega), trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB150, runBlock, BInstr.run, upd, ↓reduceIte])
  have va2 : reg n1 a2 = F + BitVec.ofNat 32 (0x9F0 + 4 * i) := by
    rw [hr1]; simp +decide only [evB150, runBlock, BInstr.run, upd, ↓reduceIte]; exact ea2
  have va4 : reg n1 a4 = 0 := by
    rw [hr1]; simp +decide only [evB150, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [ea2, add_lit_zero]
    exact ld_zero fun j hj => by
      rw [add_ofNat_assoc, show 0x9F0 + 4 * i + j = 0x9F0 + (4 * i + j) by omega]; exact W.hZ _ (by omega) (by omega)
  obtain ⟨n2, c2, D2, ha42, kp2⟩ := ev_inner C (b := F + BitVec.ofNat 32 (0x8F0 + 4 * i)) 4 0 rfl D1
    (by rw [hr1]; simp +decide only [evB150, runBlock, BInstr.run, upd, ↓reduceIte]; rfl)
    (by rw [hr1]; simp +decide only [evB150, runBlock, BInstr.run, upd, ↓reduceIte]
        rw [h8, add_ofNat_zero]; exact BitVec.zero_add _)
    (by rw [va4]; rfl)
  have k2 : ∀ q : Fin 32, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (9 : Fin 32) → reg n2 q = reg n q := by
    intro q h2 h3 h4 h5 h9
    rw [kp2 q h3 h4 h5 h9, hr1]
    by_cases h0 : q.val = 0
    · rw [show q = 0 from Fin.ext h0]; simp +decide only [evB150, runBlock, BInstr.run, upd, ↓reduceIte]
      exact D.st.zero.symm
    · simp only [evB150, runBlock, BInstr.run, upd, h0, h2, h4, h5, h9, ↓reduceIte]
  have va2' : reg n2 a2 = F + BitVec.ofNat 32 (0x9F0 + 4 * i) := by
    rw [kp2 _ (by decide) (by decide) (by decide) (by decide), va2]
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x174) [.aluImm .add a0 a0 1] (bEnd1 ev_at_172 rfl)
    ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r3 : ∀ q : Fin 32, q ≠ a0 → reg n3 q = reg n2 q := fun q hq => by
    rw [hr3]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D2.st.zero
  have hc := D3.code C
  obtain ⟨n4, d4, u4⟩ := D3.st.sw hc ev_at_174 (off' := 0x176) (by decide)
    (by rw [r3 _ (by decide), va2', add_lit_zero]; exact C.al (by omega))
  rw [r3 _ (by decide), va2', add_lit_zero, r3 _ (by decide)] at u4
  have D4 := D3.store C (d := 0x9F0 + 4 * i) (k := 4) u4.self (by rw [u4.regs, D3.hsp]) (by rw [u4.regs])
    (by rw [u4.regs]) (by omega) (fun x hx => st32_frame hx)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x178) [.aluImm .add (8 : Fin 32) (8 : Fin 32) 4] (bEnd1 ev_at_176 rfl)
    ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r5 : ∀ q : Fin 32, q ≠ (8 : Fin 32) → reg n5 q = reg n3 q := fun q hq => by
    rw [hr5, ← u4.regs q]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D4.st.zero
  have va0 : reg n5 a0 = BitVec.ofNat 32 (i + 1) := by
    rw [r5 _ (by decide), hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
    show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1); rw [BitVec.ofNat_add_ofNat]
  have va1 : reg n5 a1 = 8 := by
    rw [r5 _ (by decide), r3 _ (by decide), k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), ha1]
  have hb : ∀ u, u < 4 → M (F + BitVec.ofNat 32 (0x8F0 + 4 * i) + BitVec.ofNat 32 u) =
      Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * i) + BitVec.ofNat 32 u) := fun u hu => by
    rw [add_ofNat_assoc]; exact W.hK _ (by omega) (by omega)
  have hv : reg n2 a4 = BitVec.ofNat 32 (leAcc Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * i)) 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [ha42, BitVec.toNat_ofNat, leAcc_congr 4 hb, Nat.mod_eq_of_lt (leAcc_lt _ _ 4)]
  rw [hv] at D4 D5
  have W' : WordsInv F Mb (memStore32 M (F + BitVec.ofNat 32 (0x9F0 + 4 * i))
      (BitVec.ofNat 32 (leAcc Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * i)) 4))) (i + 1) :=
    ⟨fun t ht => by
      by_cases e : t = i
      · subst e; exact memLoad32_store32_same _ _ _
      · rw [memLoad32_store32_sep (C.offs (by omega) (by omega) (by omega))]; exact W.hW t (by omega),
     fun j h1 h2 => by rw [st32_frame (C.offs (by omega) (by omega) (by omega))]; exact W.hZ j (by omega) h2,
     fun c h1 h2 => by rw [st32_frame (C.offs (by omega) (by omega) (by omega))]; exact W.hK c h1 h2⟩
  have v8 : reg n5 8 = F + BitVec.ofNat 32 (0x8F0 + 4 * (i + 1)) := by
    rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [u4.regs, r3 _ (by decide), k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), h8]
    exact add_sp F (a := 0x8F0 + 4 * i) (b := 4) (c := 0x8F0 + 4 * (i + 1)) (by omega)
  have v18 : reg n5 18 = F + BitVec.ofNat 32 0x9F0 := by
    rw [r5 _ (by decide), r3 _ (by decide), k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), h18]
  have kq : ∀ q : Fin 32, q.val ∈ [20, 21] → reg n5 q = reg n q := fun q hq => by
    rw [r5 q (by revert hq; revert q; decide), r3 q (by revert hq; revert q; decide),
      k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have hc5 := D5.code C
  have hne : (BitVec.ofNat 32 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases Nat.lt_or_ge (i + 1) 8 with hl | hl
  · obtain ⟨n6, d6, u6⟩ := D5.st.taken hc5 0x150 ev_at_178 (by decide) (by
      rw [va0, va1]
      show (BitVec.ofNat 32 (i + 1) != 8) = true
      exact bne_iff_ne.mpr fun e => by have := congrArg BitVec.toNat e; rw [hne] at this; exact absurd this (by
        show i + 1 ≠ 8; omega))
    exact ⟨n6, _, c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (.single d6))))), W',
      by rw [u6.regs, va0], by rw [u6.regs, va1], by rw [u6.regs, v8], by rw [u6.regs, v18],
      fun q hq => by rw [u6.regs, kq q hq], fun _ => D5.jmp u6, fun h => absurd h (by omega)⟩
  · have e8 : i + 1 = 8 := by omega
    obtain ⟨n6, d6, u6⟩ := D5.st.notTaken hc5 0x17C ev_at_178 (by decide) (by
      rw [va0, va1, e8]; rfl)
    exact ⟨n6, _, c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (.single d6))))), W',
      by rw [u6.regs, va0], by rw [u6.regs, va1], by rw [u6.regs, v8], by rw [u6.regs, v18],
      fun q hq => by rw [u6.regs, kq q hq], fun h => absurd h (by omega), fun _ => D5.jmp u6⟩

/-- The words loop from the head of iteration `i` to offset 0x17C. -/
theorem ev_loop (C : EvCtx M0 F pk sig msg len) {Mb : Word → BitVec 8} :
    ∀ k i {M : Word → BitVec 8} {n : Machine}, i + k = 8 → i < 8 → EvSt M0 Ms F r0 M n 0x150 → WordsInv F Mb M i →
      reg n a0 = BitVec.ofNat 32 i → reg n a1 = 8 → reg n 8 = F + BitVec.ofNat 32 (0x8F0 + 4 * i) →
      reg n 18 = F + BitVec.ofNat 32 0x9F0 →
      ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x17C ∧ WordsInv F Mb M' 8 ∧
        ∀ q : Fin 32, q.val ∈ [20, 21] → reg n' q = reg n q
  | 0, i, _, _, hk, hi, _, _, _, _, _, _ => absurd hk (by omega)
  | k + 1, i, M, n, hk, hi, D, W, ha0, ha1, h8, h18 => by
    obtain ⟨n1, M1, c1, W1, ha01, ha11, h81, h181, kq1, T1, F1⟩ := ev_outer C hi D W ha0 ha1 h8 h18
    rcases Nat.lt_or_ge (i + 1) 8 with hl | hl
    · obtain ⟨n', M', c', D', W', kq'⟩ := ev_loop C k (i + 1) (by omega) hl (T1 hl) W1 ha01 ha11 h81 h181
      exact ⟨n', M', c1.trans c', D', W', fun q hq => by rw [kq' q hq, kq1 q hq]⟩
    · obtain e8 : i + 1 = 8 := by omega
      exact ⟨n1, M1, c1, F1 e8, by rw [← e8]; exact W1, kq1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0x14A: the 32 bytes at `F + 0x8F0` as eight little-endian
words at `F + 0x9F0`. -/
theorem ev_words (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x14A)
    (h8 : reg n 8 = F + BitVec.ofNat 32 0x8F0) (h18 : reg n 18 = F + BitVec.ofNat 32 0x9F0)
    (hz : ∀ j, j < 32 → M (F + BitVec.ofNat 32 (0x9F0 + j)) = 0) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x17C ∧
      (∀ t, t < 8 → memLoad32 M' (F + BitVec.ofNat 32 (0x9F0 + 4 * t)) =
        BitVec.ofNat 32 (leAcc M (F + BitVec.ofNat 32 (0x8F0 + 4 * t)) 4)) ∧
      (∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA10 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) ∧
      ∀ q : Fin 32, q.val ∈ [20, 21] → reg n' q = reg n q := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x14E) [.aluImm .add a0 x0 0, .aluImm .add a1 x0 8]
    (blockEnd_cons' ev_at_14a rfl (blockEnd_cons' ev_at_14c rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x150 ev_at_14e (by decide)
    (by rw [D1.st.zero, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try decide)
  have R : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q h0 h1 => by
    rw [u2.regs, hr1]
    by_cases hz0 : q.val = 0
    · rw [show q = 0 from Fin.ext hz0]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
      exact D.st.zero.symm
    · simp only [runBlock, BInstr.run, upd, hz0, h0, h1, ↓reduceIte]
  obtain ⟨n', M', c', D', W', kq'⟩ := ev_loop C (Mb := M) 8 0 rfl (by decide) (D1.jmp u2)
    ⟨fun t ht => absurd ht (by omega), fun j _ h2 => hz j h2, fun _ _ _ => rfl⟩
    (by rw [u2.regs, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by rw [u2.regs, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by rw [R _ (by decide) (by decide), h8])
    (by rw [R _ (by decide) (by decide), h18])
  exact ⟨n', M', c1.trans (.cons d2 c'), D', W'.hW, W'.hK, fun q hq => by
    rw [kq' q hq, R q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]⟩

end

end C3.RV32
