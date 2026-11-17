import C3BootProofs.Proofs.Ed25519VerifyP8

/-!
# `ed25519_verify`, offsets 0x40 to 0x104C: the checks before the hash

`evSpecA` is what the function checks before it hashes: the three input
checks, the key decoding to a point `A`, `s` being canonical, and `R`
decoding to a point with neither `R` nor `A` of small order. `ev_stageA`
runs the code from offset 0x40: it returns 0 through the epilogue when a
check fails and reaches the hash at 0x104C with `A` and the signature in the
frame when they all pass.
-/

namespace C3.RV32

open C3.Image

/-- The scalar `s`, the signature's last 32 bytes, as eight little-endian
words. -/
def sWords (M0 : Word → BitVec 8) (sig : Word) (i : Nat) : Nat :=
  if i < 8 then leAcc M0 (sig + BitVec.ofNat 32 (32 + 4 * i)) 4 % 2 ^ 32 else 0

/-- `s` is canonical: reduced modulo `L` it packs back to its own bytes, and
its top bit is clear. -/
def evSOk (M0 : Word → BitVec 8) (sig : Word) : Bool :=
  decide (memBytes M0 (sig + BitVec.ofNat 32 32) 32 = evPackS (evLimb (sWords M0 sig))) &&
    decide ((M0 (sig + BitVec.ofNat 32 63)).toNat < 128)

/-- The checks before the hash, and the key's point `A` when they pass. -/
def evSpecA (M0 : Word → BitVec 8) (pk sig : Word) : Option Pt :=
  if evChecks M0 pk sig = true then
    match evDec M0 (memBytes M0 pk 32) with
    | none => none
    | some (X, Y, Z, T) =>
      if (evSOk M0 sig && evRok (evDec M0 (memBytes M0 sig 32)) X Y Z) = true then some (X, Y, Z, T) else none
  else none

theorem memBytes_ext {M M' : Word → BitVec 8} {a b : Word} {n : Nat}
    (h : ∀ i, i < n → M' (a + BitVec.ofNat 32 i) = M (b + BitVec.ofNat 32 i)) : memBytes M' a n = memBytes M b n := by
  unfold memBytes
  exact List.map_congr_left fun i hi => congrArg BitVec.toNat (h i (List.mem_range.mp hi))

theorem evPackS_congr {L L' : Nat → Nat} (h : ∀ j, j < 9 → L j = L' j) : evPackS L = evPackS L' := by
  unfold evPackS
  exact List.map_congr_left fun j _ =>
    congrArg BitVec.toNat (s29PackByte_congr (fun i hi => by rw [s29Out_congr h hi]) j)

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The checks before the hash**, from offset 0x40. -/
theorem ev_stageA (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x40)
    (ha0 : reg n a0 = pk) (ha1 : reg n a1 = msg) (ha2 : reg n a2 = BitVec.ofNat 32 len) (ha3 : reg n a3 = sig) :
    ∃ n' M', Steps n n' ∧ (evSpecA M0 pk sig = none → EvSt M0 Ms F r0 M' n' 0x100A ∧ reg n' a0 = 0) ∧
      ∀ X Y Z T, evSpecA M0 pk sig = some (X, Y, Z, T) → EvSt M0 Ms F r0 M' n' 0x104C ∧
        reg n' 19 = F + 0x90F ∧ reg n' 27 = 0x1FFFFFFF ∧ memLoad32 M' (F + BitVec.ofNat 32 0xC) = msg ∧
        memLoad32 M' (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 len ∧
        memBytes M' (F + BitVec.ofNat 32 0x128) 32 = memBytes M0 pk 32 ∧
        feW M' (F + BitVec.ofNat 32 0x148) = X ∧ feW M' (F + BitVec.ofNat 32 0x170) = Y ∧
        feW M' (F + BitVec.ofNat 32 0x198) = Z ∧ feW M' (F + BitVec.ofNat 32 0x1C0) = T ∧
        (∀ j, j < 64 → M' (F + BitVec.ofNat 32 (0x1E8 + j)) = M0 (sig + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 64 → M' (F + BitVec.ofNat 32 (0x228 + j)) = M0 (sig + BitVec.ofNat 32 j)) := by
  obtain ⟨n1, M1, c1, F1, T1⟩ := ev_chk C D ha0 ha1 ha2 ha3
  cases hc : evChecks M0 pk sig
  · have e : evSpecA M0 pk sig = none := by unfold evSpecA; rw [hc]; rfl
    exact ⟨n1, M1, c1, fun _ => F1 hc, fun X Y Z T h => absurd (e.symm.trans h) (fun h' => nomatch h')⟩
  obtain ⟨D1, r8, r18, r21, r9, r19⟩ := T1 hc
  obtain ⟨n2, M2, c2, k2, r20, F2, T2⟩ := ev_vk C D1 r9
  cases hd : evDec M0 (memBytes M0 pk 32) with
  | none =>
    have e : evSpecA M0 pk sig = none := by unfold evSpecA; rw [hc, hd]; rfl
    exact ⟨n2, M2, c1.trans c2, fun _ => F2 hd,
      fun X Y Z T h => absurd (e.symm.trans h) (fun h' => nomatch h')⟩
  | some P =>
  obtain ⟨X, Y, Z, T⟩ := P
  obtain ⟨D2, V2, f2⟩ := T2 _ hd
  obtain ⟨v0, vb, vX, vY, vZ, vT⟩ := V2
  obtain ⟨n3, M3, c3, D3, k3, r9_3, len3, cpK, cpR, fr3⟩ := ev_cp1 C D2 (by rw [k2 8 (by decide), r8])
    (by rw [k2 18 (by decide), r18])
  obtain ⟨n4, M4, c4, D4, k4, r8_4, sig4, s4, fr4⟩ := ev_cp2 C D3 r9_3
    (by rw [k3 19 (by decide), k2 19 (by decide), r19]) cpR
  obtain ⟨n5, M5, c5, D5, k5, r18_5, d0_5, z5, fr5⟩ := ev_cp3 C D4
    (by rw [k4 20 (by decide), k3 20 (by decide), r20])
  obtain ⟨n6, M6, c6, D6, w6, fr6, k6⟩ := ev_words C D5 (by rw [k5 8 (by decide), r8_4]) r18_5 z5
  obtain ⟨n7, M7, c7, D7, l7, m7c, m7_10, m7_d0, fr7, r19_7, r27_7⟩ := ev_red C D6
    (by rw [k6 20 (by decide), k5 20 (by decide), k4 20 (by decide), k3 20 (by decide), r20])
    (by rw [k6 21 (by decide), k5 21 (by decide), k4 21 (by decide), k3 21 (by decide), k2 21 (by decide), r21])
  -- `s` canonical
  have b90F : M4 (F + BitVec.ofNat 32 0x90F) = M0 (sig + BitVec.ofNat 32 63) := s4 31 (by decide)
  have hD0 : memLoad32 M7 (F + 0xD0) = if decide ((M0 (sig + BitVec.ofNat 32 63)).toNat < 128) = true then 1 else 0 := by
    have h6 : memLoad32 M6 (F + BitVec.ofNat 32 0xD0) = memLoad32 M5 (F + BitVec.ofNat 32 0xD0) :=
      vk_ld2 fun j hj => by rw [add_ofNat_assoc]; exact fr6 (0xD0 + j) (by omega) (Or.inl (by omega))
    rw [m7_d0, show memLoad32 M6 (F + 0xD0) = memLoad32 M5 (F + BitVec.ofNat 32 0xD0) from h6, d0_5, b90F]
    by_cases h : (M0 (sig + BitVec.ofNat 32 63)).toNat < 128
    · simp only [h, decide_true, ↓reduceIte]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨n8, M8, c8, F8, T8, k8, r8_8, fr8⟩ := ev_canon C D7 hD0
  have eIn : evIn M6 F = sWords M0 sig := by
    funext i
    unfold evIn sWords
    by_cases hi : i < 8
    · simp only [hi, ↓reduceIte]
      rw [w6 i hi, BitVec.toNat_ofNat]
      congr 1
      exact leAcc_copy 4 fun u hu => by
        rw [add_ofNat_assoc, add_ofNat_assoc, fr5 _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)),
          show 0x8F0 + 4 * i + u = 0x8F0 + (4 * i + u) by omega, s4 _ (by omega)]
        rw [show 32 + (4 * i + u) = 32 + 4 * i + u by omega]
    · simp only [hi, ↓reduceIte]
  have eS : memBytes M7 (F + BitVec.ofNat 32 0x330) 32 = memBytes M0 (sig + BitVec.ofNat 32 32) 32 :=
    memBytes_ext fun i hi => by
      rw [add_ofNat_assoc, add_ofNat_assoc, fr7 _ (by omega) (by omega) (Or.inl (by omega)),
        fr6 _ (by omega) (Or.inl (by omega)), fr5 _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)),
        show 0x330 + i = 0x310 + (32 + i) by omega, sig4 _ (by omega)]
  have eP : evPackS (ssAw M7 (F + BitVec.ofNat 32 0x9F0)) = evPackS (evLimb (sWords M0 sig)) :=
    evPackS_congr fun j hj => by rw [l7 j hj, eIn]
  have eCond : (decide (memBytes M7 (F + BitVec.ofNat 32 0x330) 32 = evPackS (ssAw M7 (F + BitVec.ofNat 32 0x9F0))) &&
      decide ((M0 (sig + BitVec.ofNat 32 63)).toNat < 128)) = evSOk M0 sig := by
    rw [eS, eP]; rfl
  rw [eCond] at F8 T8
  cases hs : evSOk M0 sig
  · have e : evSpecA M0 pk sig = none := by unfold evSpecA; rw [hc, hd]; simp only [hs, Bool.false_and]; rfl
    exact ⟨n8, M8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans c8)))))), fun _ => F8 hs,
      fun X Y Z T h => absurd (e.symm.trans h) (fun h' => nomatch h')⟩
  have D8 := T8 hs
  -- `R`
  obtain ⟨n9, M9, c9, D9, k9, dec9, rA9, rB9, fr9⟩ := ev_rcp C D8 r8_8 fun j hj => by
    rw [fr8 _ (by omega) (Or.inl (by omega)), fr7 _ (by omega) (by omega) (Or.inl (by omega)),
      fr6 _ (by omega) (Or.inl (by omega)), fr5 _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)), sig4 j hj]
  have back : ∀ c, 0x128 ≤ c → c < 0x1E8 → M9 (F + BitVec.ofNat 32 c) = M3 (F + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [fr9 _ (by omega) (Or.inl h2), fr8 _ (by omega) (Or.inl (by omega)), fr7 _ (by omega) h1 (Or.inl (by omega)),
      fr6 _ (by omega) (Or.inl (by omega)), fr5 _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)),
      fr4 _ (by omega) (Or.inl (by omega))]
  have aK : ∀ j, j < 0xC0 → M9 (F + BitVec.ofNat 32 (0x128 + j)) = M2 (F + BitVec.ofNat 32 (0xEF4 + j)) :=
    fun j hj => by rw [back _ (by omega) (by omega), cpK j hj]
  have coord : ∀ o, o + 40 ≤ 0xC0 → 0x20 ≤ o →
      feW M9 (F + BitVec.ofNat 32 (0x128 + o)) = feW M2 (F + BitVec.ofNat 32 0xEF0 + BitVec.ofNat 32 (4 + o)) :=
    fun o h1 h2 => by
      rw [add_ofNat_assoc]
      exact fwB fun j hj => by
        rw [show 0x128 + o + j = 0x128 + (o + j) by omega, aK _ (by omega),
          show 0xEF4 + (o + j) = 0xEF0 + (4 + o) + j by omega]
  have hAX : feW M9 (F + BitVec.ofNat 32 0x148) = X := by
    rw [show (0x148 : Nat) = 0x128 + 0x20 from rfl, coord 0x20 (by decide) (by decide)]; exact vX
  have hAY : feW M9 (F + BitVec.ofNat 32 0x170) = Y := by
    rw [show (0x170 : Nat) = 0x128 + 0x48 from rfl, coord 0x48 (by decide) (by decide)]; exact vY
  have hAZ : feW M9 (F + BitVec.ofNat 32 0x198) = Z := by
    rw [show (0x198 : Nat) = 0x128 + 0x70 from rfl, coord 0x70 (by decide) (by decide)]; exact vZ
  have hAT : feW M9 (F + BitVec.ofNat 32 0x1C0) = T := by
    rw [show (0x1C0 : Nat) = 0x128 + 0x98 from rfl, coord 0x98 (by decide) (by decide)]; exact vT
  have r19_9 : reg n9 19 = F + 0x90F := by rw [k9 19 (by decide), k8 19 (by decide), r19_7]
  obtain ⟨n10, M10, c10, F10, T10⟩ := ev_rchk C D9 r19_9 dec9 hAX hAY hAZ
  have cs : Steps n n10 := c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
    (c9.trans c10))))))))
  cases hr : evRok (evDec M0 (memBytes M0 sig 32)) X Y Z
  · have e : evSpecA M0 pk sig = none := by unfold evSpecA; rw [hc, hd]; simp only [hs, hr, Bool.and_false]; rfl
    exact ⟨n10, M10, cs, fun _ => F10 hr, fun X Y Z T h => absurd (e.symm.trans h) (fun h' => nomatch h')⟩
  obtain ⟨D10, k10, -, fr10⟩ := T10 hr
  have e : evSpecA M0 pk sig = some (X, Y, Z, T) := by unfold evSpecA; rw [hc, hd]; simp only [hs, hr, Bool.and_self]; rfl
  refine ⟨n10, M10, cs, fun h => absurd (e.symm.trans h) (fun h' => nomatch h'), fun X' Y' Z' T' h => ?_⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : X = X' ∧ Y = Y' ∧ Z = Z' ∧ T = T' := by
    have := e.symm.trans h; simp only [Option.some.injEq, Prod.mk.injEq] at this; exact this
  have f10 : ∀ c, c < 0x268 → M10 (F + BitVec.ofNat 32 c) = M9 (F + BitVec.ofNat 32 c) := fun c hc =>
    fr10 c (by omega) (Or.inl hc)
  have fw10 : ∀ c, c + 40 ≤ 0x268 → feW M10 (F + BitVec.ofNat 32 c) = feW M9 (F + BitVec.ofNat 32 c) := fun c hc =>
    fwB fun j hj => f10 _ (by omega)
  refine ⟨D10, by rw [k10 19 (by decide), r19_9],
    by rw [k10 27 (by decide), k9 27 (by decide), k8 27 (by decide), r27_7], ?_, ?_, ?_, by rw [fw10 _ (by decide), hAX],
    by rw [fw10 _ (by decide), hAY], by rw [fw10 _ (by decide), hAZ], by rw [fw10 _ (by decide), hAT],
    fun j hj => by rw [f10 _ (by omega), rA9 j hj], fun j hj => by rw [f10 _ (by omega), rB9 j hj]⟩
  · rw [← (show memLoad32 M7 (F + BitVec.ofNat 32 0xC) = msg from m7c)]
    exact vk_ld2 fun j hj => by
      rw [add_ofNat_assoc, f10 _ (by omega), fr9 _ (by omega) (Or.inl (by omega)),
        fr8 _ (by omega) (Or.inl (by omega))]
  · have a : memLoad32 M10 (F + BitVec.ofNat 32 0x10) = memLoad32 M7 (F + BitVec.ofNat 32 0x10) :=
      vk_ld2 fun j hj => by
        rw [add_ofNat_assoc, f10 _ (by omega), fr9 _ (by omega) (Or.inl (by omega)),
          fr8 _ (by omega) (Or.inl (by omega))]
    have b : memLoad32 M6 (F + BitVec.ofNat 32 0x10) = memLoad32 M3 (F + BitVec.ofNat 32 0x10) :=
      vk_ld2 fun j hj => by
        rw [add_ofNat_assoc, fr6 _ (by omega) (Or.inl (by omega)),
          fr5 _ (by omega) (Or.inl (by omega)), fr4 _ (by omega) (Or.inl (by omega))]
    rw [a, show memLoad32 M7 (F + BitVec.ofNat 32 0x10) = memLoad32 M6 (F + BitVec.ofNat 32 0x10) from m7_10, b, len3]
  · rw [← vb]
    exact memBytes_ext fun i hi => by
      simp only [add_ofNat_assoc]
      rw [f10 _ (by omega), aK i (by omega)]

end

end C3.RV32


