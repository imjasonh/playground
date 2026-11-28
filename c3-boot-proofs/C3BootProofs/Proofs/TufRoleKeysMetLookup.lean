import C3BootProofs.Proofs.TufRoleKeysMetFrame
import C3BootProofs.Proofs.TufParseMetadataHead

/-!
# `RoleKeys::met`: the search for a key ID's signature

For listed key `i`, `RoleKeys::met` opens the signatures array with
`elements` and walks it with `next_element` from a cursor at `F + 0xC8`,
until an item's `keyid` is the key ID. `rm_look` proves that loop against
`metSig`; `rm_open` proves the `elements` call before it. The search ends
at 0x17E with the item's `sig`, at 0x2C0 when no item has the key ID, and
in the error tails otherwise, which `rm_fail` proves return an error.
-/

namespace C3.Json

theorem rm_eb_objGet (d key : Bytes) : ∀ e, objGet d key = .error e → e < 0x27 := by
  intro e h
  unfold objGet getOut at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; decide)

/-- Every error byte of `objField` is below 0x27. -/
theorem rm_eb_objField (d key : Bytes) : ∀ e, objField d key = .error e → e < 0x27 := by
  intro e h
  unfold objField at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; decide)
    | (cases h; exact rm_eb_objGet d key _ ‹_›)

/-! ## One step of `metSig` -/

theorem msig_none {a id : Bytes} {k pos : Nat} (h : nextElement a pos = none) : metSig a id (k + 1) pos = none := by
  simp only [metSig, h]
theorem msig_end {a id : Bytes} {k pos : Nat} (h : nextElement a pos = some none) : metSig a id (k + 1) pos = some none := by
  simp only [metSig, h]
theorem msig_kerr {a id : Bytes} {k pos ep el nx e : Nat} (h : nextElement a pos = some (some (ep, el, nx)))
    (hf : objField (slice a ep el) (ascii!"keyid") = .error e) : metSig a id (k + 1) pos = none := by
  simp only [metSig, h, hf]
theorem msig_kstr {a id : Bytes} {k pos ep el nx kp kl : Nat} (h : nextElement a pos = some (some (ep, el, nx)))
    (hf : objField (slice a ep el) (ascii!"keyid") = .ok (kp, kl))
    (hs : strBody (slice (slice a ep el) kp kl) = none) : metSig a id (k + 1) pos = none := by
  simp only [metSig, h, hf, hs]
theorem msig_ne {a id b : Bytes} {k pos ep el nx kp kl : Nat} (h : nextElement a pos = some (some (ep, el, nx)))
    (hf : objField (slice a ep el) (ascii!"keyid") = .ok (kp, kl))
    (hs : strBody (slice (slice a ep el) kp kl) = some b) (hb : b ≠ id) : metSig a id (k + 1) pos = metSig a id k nx := by
  simp only [metSig, h, hf, hs, hb, ↓reduceIte]
theorem msig_gerr {a id : Bytes} {k pos ep el nx kp kl e : Nat} (h : nextElement a pos = some (some (ep, el, nx)))
    (hf : objField (slice a ep el) (ascii!"keyid") = .ok (kp, kl))
    (hs : strBody (slice (slice a ep el) kp kl) = some id)
    (hg : objField (slice a ep el) (ascii!"sig") = .error e) : metSig a id (k + 1) pos = none := by
  simp only [metSig, h, hf, hs, hg, ↓reduceIte]
theorem msig_sig {a id : Bytes} {k pos ep el nx kp kl gp gl : Nat} (h : nextElement a pos = some (some (ep, el, nx)))
    (hf : objField (slice a ep el) (ascii!"keyid") = .ok (kp, kl))
    (hs : strBody (slice (slice a ep el) kp kl) = some id)
    (hg : objField (slice a ep el) (ascii!"sig") = .ok (gp, gl)) :
    metSig a id (k + 1) pos = (strBody (slice (slice a ep el) gp gl)).map some := by
  simp only [metSig, h, hf, hs, hg, ↓reduceIte]
end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

theorem rmKeepUpd {L : List (Fin 32)} (hL : ∀ x, x ∈ L → x.val ≠ 0) {f G : Fin 32 → Word} {rd : Fin 32} {v : Word}
    (hrd : rd ∉ L) (h : ∀ x, x ∈ L → f x = G x) : ∀ x, x ∈ L → upd f rd v x = G x := by
  intro x hx
  have hne : x ≠ rd := fun e => hrd (e ▸ hx)
  simp only [upd_app, hL x hx, hne, ↓reduceIte]; exact h x hx

theorem rmKeepClob {L : List (Fin 32)} {f G : Fin 32 → Word} {m : Machine} {cl : List (Fin 32)}
    (hcl : ∀ x, x ∈ cl → x ∉ L) (h : ∀ x, x ∈ L → f x = G x) : ∀ x, x ∈ L → clob f m cl x = G x := by
  intro x hx
  have hn : x ∉ cl := fun h' => hcl x h' hx
  simp only [clob_app, hn, ↓reduceIte]; exact h x hx

/-- Proves `∀ x, x ∈ L → g x = G x` for `g` a chain of `upd`s and `clob`s
over a register file that the hypothesis says it of. -/
syntax "rmkeep" term : tactic

macro_rules
  | `(tactic| rmkeep $h) =>
    `(tactic| ((repeat (first | refine rmKeepUpd (by decide) (by decide) ?_ | refine rmKeepClob (by decide) ?_)); exact $h))

/-- The registers that the search keeps: `sp`, 0x62 in `s2`, the
`RoleKeys` in `s3`, the count in `s4`, the key ID in `s5` and `s9`, `i` and
`i + 1` in `s6` and `s7`, the tag in `s8`, 0x21 in `s10`, and the slot in
`s11`. -/
abbrev rmKL : List (Fin 32) := [sp, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- `rmKL` without `s9`, which holds the signature after the search. -/
abbrev rmKLs : List (Fin 32) := [sp, 18, 19, 20, 21, 22, 23, 24, 26, 27]

/-- The frame bytes from `F + 0xC` to `F + 0x48` as in `Mz`: the counted
slots and the words that the outer loop keeps. -/
def RmLow (Mz Mk : Word → BitVec 8) (F : Word) : Prop :=
  ∀ j, j < 0x3C → Mk (F + BitVec.ofNat 32 0xC + BitVec.ofNat 32 j) = Mz (F + BitVec.ofNat 32 0xC + BitVec.ofNat 32 j)

theorem RmLow.refl (Mz : Word → BitVec 8) (F : Word) : RmLow Mz Mz F := fun _ _ => rfl

theorem RmLow.out {Mz Ma Mb : Word → BitVec 8} {F r : Word} {l : Nat} (h : RmLow Mz Ma F) (hO : Out Ma Mb r l)
    (hs : Sep r l (F + BitVec.ofNat 32 0xC) 0x3C) : RmLow Mz Mb F :=
  fun j hj => (hO _ (sep_pt hs hj)).trans (h j hj)

theorem RmLow.trans {Mz Ma Mb : Word → BitVec 8} {F : Word} (h : RmLow Mz Ma F) (h' : RmLow Ma Mb F) :
    RmLow Mz Mb F :=
  fun j hj => (h' j hj).trans (h j hj)

theorem RmLow.load {Mz Mk : Word → BitVec 8} {F : Word} (h : RmLow Mz Mk F) {c : Nat} (hc : c + 4 ≤ 0x3C) :
    memLoad32 Mk (F + BitVec.ofNat 32 (0xC + c)) = memLoad32 Mz (F + BitVec.ofNat 32 (0xC + c)) :=
  memLoad32_congr fun j hj => by
    have := h (c + j) (by omega)
    rw [add_ofNat_assoc, ← Nat.add_assoc] at this
    rw [add_ofNat_assoc]; exact this

theorem rm_sltu1 {i n : Nat} (hin : i < n) (hn : n < 2 ^ 32) :
    aluEval .sltu (BitVec.ofNat 32 i) (BitVec.ofNat 32 n) = 1 := by
  show (if (BitVec.ofNat 32 i).ult (BitVec.ofNat 32 n) then (1 : Word) else 0) = 1
  rw [ite_eq_left (by rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]

section
variable {M0 M1 Mk : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 g : Fin 32 → Word} {S : Prop}
  {H : Post}

/-- The epilogue with `i < n`: an error, whatever `a1` holds. -/
theorem rm_fail (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) (hsp : g sp = F)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {i n : Nat} (h22 : g 22 = BitVec.ofNat 32 i)
    (h20 : g 20 = BitVec.ofNat 32 n) (hin : i < n) (hn : n < 2 ^ 32) (he : (g 26 &&& 0xFF).toNat < 0x27) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x36E g :=
  rm_epi hsp (E.saved hO) E.hsp0 E.hret (by have := E.halF; omega) E.hz0 hfr (E.agree hO)
    (fun h => absurd h (by rw [h22, h20, rm_sltu1 hin hn]; decide)) fun _ => he

theorem rm_zb {b : BitVec 8} (h : b.toNat < 0x27) : (b.zeroExtend 32 &&& 0xFF).toNat < 0x27 := by
  rw [BitVec.toNat_and]
  refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
  rw [BitVec.toNat_setWidth]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; exact h

/-- The error tails at 0x342, 0x348, 0x34E, and 0x3AA. -/
theorem rm_342 (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) (hsp : g sp = F)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {i n : Nat} (h22 : g 22 = BitVec.ofNat 32 i)
    (h20 : g 20 = BitVec.ofNat 32 n) (hin : i < n) (hn : n < 2 ^ 32) (hz0 : g0 0 = 0)
    (he : (Mk (F + 0x49)).toNat < 0x27) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x342 g := by
  refine WP.lbu rkm_at_342 ?_; wn
  refine WP.jal rkm_at_346 (by decide) ?_; wn
  exact rm_fail E hO (by (try rsimp); exact hsp) (by keepz hz0) (by (try rsimp); exact h22)
    (by (try rsimp); exact h20) hin hn (by (try rsimp); rw [hsp]; exact rm_zb he)

theorem rm_348 (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) (hsp : g sp = F)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {i n : Nat} (h22 : g 22 = BitVec.ofNat 32 i)
    (h20 : g 20 = BitVec.ofNat 32 n) (hin : i < n) (hn : n < 2 ^ 32) (hz0 : g0 0 = 0)
    (he : (Mk (F + 0x4C)).toNat < 0x27) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x348 g := by
  refine WP.lbu rkm_at_348 ?_; wn
  refine WP.jal rkm_at_34c (by decide) ?_; wn
  exact rm_fail E hO (by (try rsimp); exact hsp) (by keepz hz0) (by (try rsimp); exact h22)
    (by (try rsimp); exact h20) hin hn (by (try rsimp); rw [hsp]; exact rm_zb he)

theorem rm_34e (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) (hsp : g sp = F)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {i n : Nat} (h22 : g 22 = BitVec.ofNat 32 i)
    (h20 : g 20 = BitVec.ofNat 32 n) (hin : i < n) (hn : n < 2 ^ 32) (hz0 : g0 0 = 0)
    (he : (Mk (F + 0x190)).toNat < 0x27) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x34E g := by
  refine WP.lbu rkm_at_34e ?_; wn
  refine WP.jal rkm_at_352 (by decide) ?_; wn
  exact rm_fail E hO (by (try rsimp); exact hsp) (by keepz hz0) (by (try rsimp); exact h22)
    (by (try rsimp); exact h20) hin hn (by (try rsimp); rw [hsp]; exact rm_zb he)

theorem rm_3aa (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) (hsp : g sp = F)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {i n : Nat} (h22 : g 22 = BitVec.ofNat 32 i)
    (h20 : g 20 = BitVec.ofNat 32 n) (hin : i < n) (hn : n < 2 ^ 32) (hz0 : g0 0 = 0)
    (he : (g 8 &&& 0xFF).toNat < 0x27) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x3AA g := by
  refine WP.alu rkm_at_3aa ?_; wn
  refine WP.jal rkm_at_3ac (by decide) ?_; wn
  exact rm_fail E hO (by (try rsimp); exact hsp) (by keepz hz0) (by (try rsimp); exact h22)
    (by (try rsimp); exact h20) hin hn
    (by (try rsimp); rw [(hfr 0 (by decide)).trans hz0]; show ((0 : Word) + g 8 &&& 255).toNat < 39
        rw [show (0 : Word) + g 8 = g 8 from BitVec.zero_add _]; exact he)

end


theorem rm_kls : ∀ x, x ∈ rmKLs → x ∈ rmKL := by decide

/-- The cursor at `F + 0xC8` after `next_element` moved it to `nx`. -/
theorem rm_cur_elem {Ma M2 : Word → BitVec 8} {F P : Word} {N pos nx : Nat}
    (hC : PmCc Ma (F + BitVec.ofNat 32 0xC8) P N pos)
    (hfa : ∀ x, Sep x 1 (F + 0x48) 12 → Sep x 1 (F + BitVec.ofNat 32 0xC8 + 8) 4 → M2 x = Ma x)
    (t4 : memLoad32 M2 (F + BitVec.ofNat 32 0xC8 + 8) = BitVec.ofNat 32 nx) :
    PmCc M2 (F + BitVec.ofNat 32 0xC8) P N nx := by
  have e4 : F + BitVec.ofNat 32 0xC8 + 4 = F + BitVec.ofNat 32 0xCC := by rw [BitVec.add_assoc]; rfl
  have e8 : F + BitVec.ofNat 32 0xC8 + 8 = F + BitVec.ofNat 32 0xD0 := by rw [BitVec.add_assoc]; rfl
  rw [e8] at hfa
  have h1 : ∀ {d : Nat}, 0xC8 ≤ d → d + 4 ≤ 0xD0 → Sep (F + 0x48) 12 (F + BitVec.ofNat 32 d) 4 := fun h h' =>
    rm_ff F (c := 0x48) (n := 12) (Or.inl (by omega)) (by decide) (by omega)
  have h2 : ∀ {d : Nat}, d + 4 ≤ 0xD0 → Sep (F + BitVec.ofNat 32 0xD0) 4 (F + BitVec.ofNat 32 d) 4 := fun h =>
    rm_ff F (c := 0xD0) (n := 4) (Or.inr (by omega)) (by decide) (by omega)
  refine ⟨(pm_ld2 hfa (h1 (d := 0xC8) (by decide) (by decide)) (h2 (by decide))).trans hC.1, ?_, t4⟩
  have hC2 := hC.2.1
  rw [e4] at hC2 ⊢
  exact (pm_ld2 hfa (h1 (d := 0xCC) (by decide) (by decide)) (h2 (by decide))).trans hC2

/-- `pm_ccopy` in the frame of `RoleKeys::met`, whose 0x1F0 bytes are
wider than `parse_metadata`'s. -/
theorem rm_ccopy {M2 M3 M5 : Word → BitVec 8} {F S q : Word} {d a l k : Nat}
    (hd : d + 12 ≤ 0x1F0)
    (hSD : Sep (F + BitVec.ofNat 32 d) 12 S 16)
    (t4 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 4)) = BitVec.ofNat 32 l)
    (t8 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 8)) = BitVec.ofNat 32 k)
    (hO3 : Out (copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7) M3 S 16)
    (hM5 : memStore8 (memStore32 M3 (F + BitVec.ofNat 32 d) q) (F + BitVec.ofNat 32 (d + 4))
      (M2 (F + BitVec.ofNat 32 (a + 4))) = M5) :
    PmCc M5 (F + BitVec.ofNat 32 d) q l k ∧
      ∀ x, Sep x 1 (F + BitVec.ofNat 32 d) 12 → Sep x 1 S 16 → M5 x = M2 x := by
  have oC : Out M2 (copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7)
      (F + BitVec.ofNat 32 (d + 5)) 7 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have hcp : ∀ c, 5 ≤ c → c < 12 → M5 (F + BitVec.ofNat 32 (d + c)) = M2 (F + BitVec.ofNat 32 (a + c)) := by
    intro c hc1 hc2
    rw [← hM5, memStore8_ne ?_]
    · rw [out_store32 _ _ _ _ ?_, hO3 _ ?_]
      · have := copyBytes_at (M := M2) (dst := F + BitVec.ofNat 32 (d + 5)) (src := F + BitVec.ofNat 32 (a + 5))
          (N := 7) (i := c - 5) (by omega) (by decide)
        rw [add_ofNat_assoc, add_ofNat_assoc, show d + 5 + (c - 5) = d + c by omega,
          show a + 5 + (c - 5) = a + c by omega] at this
        exact this
      · have := hSD.sub (c := c) (l := 1) (by omega)
        rwa [add_ofNat_assoc] at this
      · exact rm_ff F (c := d + c) (n := 1) (d := d) (k := 4) (Or.inr (by omega)) (by omega) (by omega)
    · exact sep_byte0 (rm_ff F (c := d + c) (n := 1) (d := d + 4) (k := 1) (Or.inr (by omega)) (by omega)
        (by omega)) (by decide)
  refine ⟨⟨?_, ?_, ?_⟩, fun x hx hS => ?_⟩
  · rw [← hM5, (out_store8 _ _ _).load32 (rm_ff F (c := d + 4) (n := 1) (d := d) (k := 4) (Or.inr (by omega))
      (by omega) (by omega)), memLoad32_store32_same]
  · rw [← t4]
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 d + BitVec.ofNat 32 4 + BitVec.ofNat 32 j) =
      M2 (F + BitVec.ofNat 32 (a + 4) + BitVec.ofNat 32 j)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [add_ofNat_assoc, Nat.add_zero]
      rw [← hM5, memStore8_same]
    · simp only [add_ofNat_assoc, Nat.add_assoc]
      rw [hcp (4 + j) (by omega) (by omega)]
  · rw [← t8]
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 d + BitVec.ofNat 32 8 + BitVec.ofNat 32 j) =
      M2 (F + BitVec.ofNat 32 (a + 8) + BitVec.ofNat 32 j)
    simp only [add_ofNat_assoc, Nat.add_assoc]
    rw [hcp (8 + j) (by omega) (by omega)]
  · have h4 : Sep x 1 (F + BitVec.ofNat 32 (d + 4)) 1 := by
      have := sep_in hx (d := 4) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
    have h0 : Sep x 1 (F + BitVec.ofNat 32 d) 4 := by
      have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h5 : Sep x 1 (F + BitVec.ofNat 32 (d + 5)) 7 := by
      have := sep_in hx (d := 5) (l := 7) (by decide); rwa [add_ofNat_assoc] at this
    rw [← hM5, memStore8_ne (sep_byte0 h4 (by decide)), out_store32 _ _ _ _ h0, hO3 _ hS, oC _ h5]

section
variable {M0 M1 : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word} {S : Prop}
  {H : Post}

/-- What `next_element` with its result at `F + 0x48` and its cursor at
`F + 0xC8` changes lies in the 0x38EC bytes at `s`. -/
theorem rm_elemOut (E : RmBase M0 M1 s F R MP SP ML SL g0) {Ma M2 : Word → BitVec 8}
    {r : Option (Option (Word × Nat × Nat))}
    (h : ElemRes Ma M2 (F + 0x48) (F + BitVec.ofNat 32 0xC8) r) : Out Ma M2 s 0x38EC := by
  intro x hx
  refine h.out ?_ ?_
  · show Sep x 1 (F + BitVec.ofNat 32 0x48) 12
    rw [E.Fc]; exact sep_in hx (by decide)
  · show Sep x 1 (F + BitVec.ofNat 32 0xC8 + BitVec.ofNat 32 8) 4
    rw [add_ofNat_assoc, E.Fc]; exact sep_in hx (by decide)

set_option maxHeartbeats 8000000 in
/-- The search at 0xE6 for the key ID, the `IL` bytes at `IDA` that `s5`
and `s9` hold, through the signatures array from the cursor at `F + 0xC8`.
It ends at 0x2C0 when no item has the key ID, at 0x17E with the first such
item's `sig` in `s9` and `F + 8`, and in an error otherwise. -/
theorem rm_look (E : RmBase M0 M1 s F R MP SP ML SL g0) {gK : Fin 32 → Word} (hKsp : gK sp = F) {IDA : Word}
    {IL i n : Nat} (hK21 : gK 21 = IDA) (hK25 : gK 25 = BitVec.ofNat 32 IL) (hK22 : gK 22 = BitVec.ofNat 32 i)
    (hK20 : gK 20 = BitVec.ofNat 32 n) (hin : i < n) (hn : n < 2 ^ 32) (hSI : Sep s 0x3920 IDA IL)
    (hIL : IL < 2 ^ 32) {Mz : Word → BitVec 8}
    (hnf : ∀ (Mk : Word → BitVec 8) (g : Fin 32 → Word), Out M1 Mk s 0x38EC → RmLow Mz Mk F →
      (∀ x, x ∈ rmKL → g x = gK x) → g 0 = 0 → (∀ x, x ∉ rkE → g x = g0 x) →
      metLookup (memBytes M0 SP SL) (memBytes M0 IDA IL) = some none →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x2C0 g)
    (hfd : ∀ (Mk : Word → BitVec 8) (g : Fin 32 → Word) (q l : Nat), Out M1 Mk s 0x38EC → RmLow Mz Mk F →
      (∀ x, x ∈ rmKLs → g x = gK x) → g 0 = 0 → (∀ x, x ∉ rkE → g x = g0 x) →
      g 25 = SP + BitVec.ofNat 32 q → memLoad32 Mk (F + 8) = BitVec.ofNat 32 l → q + l ≤ SL →
      metLookup (memBytes M0 SP SL) (memBytes M0 IDA IL) = some (some (memBytes M0 (SP + BitVec.ofNat 32 q) l)) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x17E g) :
    ∀ (k pos : Nat) (Mk : Word → BitVec 8) (g : Fin 32 → Word), Out M1 Mk s 0x38EC → RmLow Mz Mk F →
      PmCc Mk (F + BitVec.ofNat 32 0xC8) SP SL pos → pos ≤ SL → SL < pos + k →
      (∀ x, x ∈ rmKL → g x = gK x) → g 0 = 0 → (∀ x, x ∉ rkE → g x = g0 x) →
      metLookup (memBytes M0 SP SL) (memBytes M0 IDA IL) = metSig (memBytes M0 SP SL) (memBytes M0 IDA IL) k pos →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0xE6 g := by
  intro k
  induction k with
  | zero => intro pos _ _ _ _ _ h1 h2; exfalso; omega
  | succ k ih =>
  intro pos Mk g hO hLo hC hpos hk hK hz hfr hL
  have hgsp : g sp = F := (hK sp (by decide)).trans hKsp
  have hg22 : g 22 = BitVec.ofNat 32 i := (hK 22 (by decide)).trans hK22
  have hg20 : g 20 = BitVec.ofNat 32 n := (hK 20 (by decide)).trans hK20
  have hF4 : F.toNat % 4 = 0 := by have := E.halF; omega
  have hSL := E.hSL
  have hSw := E.hSw
  have hS0 := E.hS0
  have hc := E.codeA hO
  have hPS := tpm_parseSep (s := s) (k := 0x3920) (by have := E.hhi; omega) E.hro
  refine WP.aluImm rkm_at_e6 ?_; wn
  refine WP.aluImm rkm_at_e8 ?_; wn
  refine WP.callNextElement (tb := TPM_JNE) (out := F + 0x48) (c := F + BitVec.ofNat 32 0xC8)
    (s := s + BitVec.ofNat 32 0x369C) (p := SP) (n := SL) (pos := pos) rkm_at_ea rkm_at_ee (by decide) (by decide)
    (by decide) hc.rk.pm.ne hc.rk.pm.ri (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [ev_add, hgsp]; rfl)
    (by (try rsimp); rw [hgsp]; exact (E.sp 0x369C (by decide)).symm) (E.alS (by decide))
    (aligned_add hF4 (by decide)) (aligned_add hF4 (by decide)) hC.1 hC.2.1 hC.2.2
    (by omega) (by omega) hS0 (by omega)
    (by rw [show TPM_JNE + 0xFFFFF7E0 = TPM_JG + 0xFFFFF616 by decide]; exact hPS.2.ri.sub (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.hSS.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (rm_ff F (Or.inl (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO E.hSS] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hER⟩ := hR
  have hOE := rm_elemOut E hER
  have hO2 : Out M1 M2 s 0x38EC := hO.trans ((Out.upK rfl hOa (by decide)).trans hOE)
  have hCa : PmCc Ma (F + BitVec.ofNat 32 0xC8) SP SL pos :=
    hC.keep hOa (E.fs (c := 0xC8) (n := 12) (d := 0x369C) (k := 148) (Or.inr (by decide)) (by decide) (by decide)).symm
  have hLa : RmLow Mz Ma F :=
    hLo.out hOa (E.fs (c := 0xC) (n := 0x3C) (d := 0x369C) (k := 148) (Or.inr (by decide)) (by decide) (by decide)).symm
  refine WP.zero fun hz2 => ?_
  refine WP.lbu rkm_at_f2 ?_; wn
  rcases hne : nextElement (memBytes M0 SP SL) pos with _ | _ | ⟨ep, el, nx⟩ <;> rw [hne] at hER <;>
    simp only [elemRes, Option.map_none, Option.map_some] at hER
  · -- An error inside the array.
    obtain ⟨-, t1, t2⟩ := hER
    refine WP.branch rkm_at_f6 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    exact rm_342 E hO2 (by (try rsimp); exact hgsp) (by keepz E.hz0) (by (try rsimp); exact hg22)
      (by (try rsimp); exact hg20) hin hn E.hz0 (by rw [show F + 0x49 = F + 0x48 + 1 by rw [BitVec.add_assoc]; rfl, t2]; decide)
  · -- The end of the array: no item has the key ID.
    obtain ⟨hfa, t1, t2⟩ := hER
    refine WP.branch rkm_at_f6 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw rkm_at_fa (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x4C) (by decide)) ?_; wn
    refine WP.branch rkm_at_fc (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb)
      rw [hgsp, show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl, t2] at eb; exact absurd eb (by decide)
    have hLb : RmLow Mz M2 F := hLa.out (r := F + 0x48) (l := 12) (fun x hx => hfa x hx)
      (rm_ff F (Or.inr (by decide)) (by decide) (by decide))
    exact hnf _ _ hO2 hLb (by rmkeep hK) (by rsimp) (by keepz E.hz0) (hL.trans (msig_end hne))
  · -- An item at `ep`.
    obtain ⟨hfa, t1, t2, t3, t4⟩ := hER
    obtain ⟨rfl, hpx, hel, hle, hxN⟩ := nextElement_lt hne
    rw [memBytes_length] at hle hxN
    have hLb : RmLow Mz M2 F := fun j hj =>
      (hfa _ (by have := rm_ff F (c := 0x48) (n := 12) (d := 0xC + j) (k := 1) (Or.inr (by omega)) (by decide)
                    (by omega); rw [← add_ofNat_assoc] at this; exact this.symm)
              (by have := rm_ff F (c := 0xD0) (n := 4) (d := 0xC + j) (k := 1) (Or.inr (by omega)) (by decide)
                    (by omega); rw [← add_ofNat_assoc] at this
                  rw [show F + BitVec.ofNat 32 0xC8 + 8 = F + BitVec.ofNat 32 0xD0 by rw [BitVec.add_assoc]; rfl]
                  exact this.symm)).trans (hLa j hj)
    have hCb := rm_cur_elem hCa hfa t4
    refine WP.branch rkm_at_f6 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw rkm_at_fa (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x4C) (by decide)) ?_; wn
    have t2e : memLoad32 M2 (F + 0x4C) = SP + BitVec.ofNat 32 ep := by
      rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    have t3' : memLoad32 M2 (F + 0x50) = BitVec.ofNat 32 el := by
      rw [show F + 0x50 = F + 0x48 + 8 by rw [BitVec.add_assoc]; rfl]; exact t3
    have hq0 := nx_q0 hS0 (n := SL) (pos := ep) (by omega) (by omega)
    refine WP.branch rkm_at_fc (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t2e, hq0] at eb; exact absurd eb (by decide)
    refine WP.lw rkm_at_100 (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x50) (by decide)) ?_; wn
    refine WP.aluImm rkm_at_102 ?_; wn
    refine WP.aluImm rkm_at_104 ?_; wn
    refine WP.alu rkm_at_106 ?_; wn
    refine WP.alu rkm_at_108 ?_; wn
    refine WP.lui rkm_at_10a ?_; wn
    refine WP.aluImm rkm_at_10e ?_; wn
    have hc2 := E.codeA hO2
    have hSe : Sep s 0x3920 (SP + BitVec.ofNat 32 ep) el := E.hSS.subR hle
    refine WP.callField (tb := TPM_JF) (out := F + 0x48) (s := s + BitVec.ofNat 32 0x362C)
      (p := SP + BitVec.ofNat 32 ep) (kq := TPM_KK) (n := el) (kl := 5)
      rkm_at_112 rkm_at_116 (by decide) (by decide) (by decide) hc2.rk.pm.fieldC
      (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [hgsp, t2e, ev0]) (by (try rsimp); rw [hgsp, t3', ev0])
      (by (try rsimp); (try simp only [ev0]); (try rfl)) (by (try rsimp); (try simp only [ev0]); (try rfl))
      (by (try rsimp); rw [hgsp]; exact (E.sp 0x362C (by decide)).symm)
      (E.alS (by decide)) (aligned_add hF4 (by decide)) (by have := E.wS (d := 0x362C) (k := 260) (by decide); omega)
      (by decide) (by rw [tex_toNat (by omega)]; omega) (by rw [tex_toNat (by omega)]; omega)
      (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSe.sub (by decide))
      (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) fun m3 hR => ?_
    rw [E.bytes hO2 hSe, tpm_kk hc2.rk.pm] at hR
    generalize m3.mem = M3 at hR
    obtain ⟨Mb, hOb, hFR⟩ := hR
    have hO3 : Out M1 M3 s 0x38EC :=
      hO2.trans ((Out.upK rfl hOb (by decide)).trans (Out.upK (c := 0x3730 + 0x48) (E.Fc 0x48).symm hFR.out (by decide)))
    have hCc : PmCc M3 (F + BitVec.ofNat 32 0xC8) SP SL nx :=
      (hCb.keep hOb (E.fs (c := 0xC8) (n := 12) (d := 0x362C) (k := 260) (Or.inr (by decide)) (by decide)
        (by decide)).symm).keep hFR.out (rm_ff F (Or.inl (by decide)) (by decide) (by decide))
    have hLc : RmLow Mz M3 F :=
      (hLb.out hOb (E.fs (c := 0xC) (n := 0x3C) (d := 0x362C) (k := 260) (Or.inr (by decide)) (by decide)
        (by decide)).symm).out hFR.out (rm_ff F (Or.inr (by decide)) (by decide) (by decide))
    have hA1 : slice (memBytes M0 SP SL) ep el = memBytes M0 (SP + BitVec.ofNat 32 ep) el :=
      tuf_memBytes_drop_take hle
    refine WP.zero fun hz3 => ?_
    refine WP.lw rkm_at_11a (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x48) (by decide)) ?_; wn
    rcases hof : objField (memBytes M0 (SP + BitVec.ofNat 32 ep) el) (ascii!"keyid") with e | ⟨kp, kl⟩ <;>
      rw [hof] at hFR <;> simp only [fieldRes, Except.map] at hFR
    · -- No `keyid`.
      obtain ⟨-, t1, t2⟩ := hFR
      refine WP.branch rkm_at_11c (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
      exact rm_348 E hO3 (by (try rsimp); exact hgsp) (by keepz E.hz0) (by (try rsimp); exact hg22)
        (by (try rsimp); exact hg20) hin hn E.hz0 (by rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl, t2, BitVec.toNat_ofNat]; have := rm_eb_objField _ _ _ hof; omega)
    · -- `keyid` at `kp`.
      obtain ⟨-, t1, t2⟩ := hFR
      have hv := objField_val hof
      rw [memBytes_length] at hv
      have t2' : memLoad32 M3 (F + 0x4C) = BitVec.ofNat 32 kl := by
        rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
      have hpk : SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp = SP + BitVec.ofNat 32 (ep + kp) :=
        add_ofNat_assoc SP ep kp
      have hq1 := nx_q0 hS0 (n := SL) (pos := ep + kp) (by omega) (by omega)
      refine WP.branch rkm_at_11c (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; (try rsimp at eb); rw [hgsp, t1, hpk, hq1] at eb; exact absurd eb (by decide)
      refine WP.lw rkm_at_120 (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x4C) (by decide)) ?_; wn
      refine WP.aluImm rkm_at_122 ?_; wn
      have hc3 := E.codeA hO3
      refine WP.callStr (tb := TPM_JS) (out := F + 0x18C) (p := SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp)
        (n := kl) rkm_at_124 rkm_at_128 (by decide) (by decide) (by decide) hc3.rk.pm.str
        (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [hgsp, t1]) (by (try rsimp); rw [hgsp, t2'])
        (by omega) (aligned_add hF4 (k := 0x18C) (by decide)) (E.lowF (by decide) (by decide) (by decide))
        (E.lowF (by decide) (by decide) (by decide)) fun m4 hS => ?_
      have hSk : Sep s 0x3920 (SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl := by
        rw [hpk]; exact E.hSS.subR (by omega)
      rw [E.bytes hO3 hSk, tex_strRes] at hS
      generalize m4.mem = M4 at hS
      have hO4 : Out M1 M4 s 0x38EC := hO3.trans (Out.upK (c := 0x3730 + 0x18C) (E.Fc 0x18C).symm hS.out (by decide))
      have hCd : PmCc M4 (F + BitVec.ofNat 32 0xC8) SP SL nx :=
        hCc.keep hS.out (rm_ff F (Or.inr (by decide)) (by decide) (by decide))
      have hLd : RmLow Mz M4 F := hLc.out hS.out (rm_ff F (Or.inr (by decide)) (by decide) (by decide))
      have hA2 : slice (slice (memBytes M0 SP SL) ep el) kp kl =
          memBytes M0 (SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl := by
        rw [hA1]; exact tuf_memBytes_drop_take hv.2
      refine WP.zero fun hz4 => ?_
      refine WP.lw rkm_at_12c (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x18C) (by decide)) ?_; wn
      rcases hsb : strBody (memBytes M0 (SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl) with _ | b <;>
        rw [hsb] at hS <;> simp only [Option.map_none, Option.map_some] at hS
      · -- `keyid` is not a string.
        obtain ⟨-, t1, t2⟩ := hS
        refine WP.branch rkm_at_130 (fun _ => ?_) (fun eb => ?_) <;> wn
        rotate_left
        · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
        exact rm_34e E hO4 (by (try rsimp); exact hgsp) (by keepz E.hz0) (by (try rsimp); exact hg22)
          (by (try rsimp); exact hg20) hin hn E.hz0 (by rw [show F + 0x190 = F + 0x18C + 4 by rw [BitVec.add_assoc]; rfl, t2]; decide)
      · -- The key ID `b`: compare it with `id`.
        obtain ⟨-, t1, t2⟩ := hS
        obtain ⟨hb2, hbe⟩ := tex_body hsb
        rw [memBytes_length] at hb2 hbe
        rw [tuf_memBytes_drop_take (by omega), add_ofNat_assoc, add_ofNat_assoc, ← Nat.add_assoc] at hbe
        have hbl : b.length = kl - 2 := by rw [hbe, memBytes_length]
        have hpb : SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp + 1 = SP + BitVec.ofNat 32 (ep + kp + 1) := by
          rw [hpk]; exact add_ofNat_assoc SP (ep + kp) 1
        have t1' : memLoad32 M4 (F + 0x18C) = SP + BitVec.ofNat 32 (ep + kp + 1) := t1.trans hpb
        have t2' : memLoad32 M4 (F + 0x190) = BitVec.ofNat 32 b.length := by
          rw [show F + 0x190 = F + 0x18C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
        have hq2 := nx_q0 hS0 (n := SL) (pos := ep + kp + 1) (by omega) (by omega)
        refine WP.branch rkm_at_130 (fun eb => ?_) (fun _ => ?_) <;> wn
        · exfalso; (try rsimp at eb); rw [hgsp, t1', hq2] at eb; exact absurd eb (by decide)
        refine WP.lw rkm_at_134 (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x190) (by decide)) ?_; wn
        refine WP.alu rkm_at_138 ?_; wn
        refine WP.alu rkm_at_13a ?_; wn
        have hc4 := E.codeA hO4
        have hFm : F + 0xFFFFFFFC = s + BitVec.ofNat 32 0x372C := by rw [← E.hF, BitVec.add_assoc]; rfl
        have hSb : Sep s 0x3920 (SP + BitVec.ofNat 32 (ep + kp + 1)) b.length := E.hSS.subR (by omega)
        refine WP.callSliceEq (tb := TPM_JG + 0xFFFFFFEA) (p := SP + BitVec.ofNat 32 (ep + kp + 1)) (q := IDA)
          (pl := b.length) (ql := IL) rkm_at_13c rkm_at_140 (by decide) (by decide) (by decide) hc4.rk.pm.get.eq
          (by rw [show TPM_JG + 0xFFFFFFEA + 0xFFFFEBAA = TPM_JG + 0xFFFFF616 + 0xFFFFF57E by decide]
              exact hc4.rk.pm.get.ri.es)
          (by rw [show TPM_JG + 0xFFFFFFEA + 0xBF68 = TPM_JG + 0xFFFFF616 + 0xC93C by decide]
              exact hc4.rk.pm.get.ri.mc)
          (by (try rsimp); rw [hgsp, t1']) (by (try rsimp); rw [hgsp, t2'])
          (by (try rsimp); (try simp only [ev0]); exact (hK 21 (by decide)).trans hK21)
          (by (try rsimp); (try simp only [ev0]); exact (hK 25 (by decide)).trans hK25) (by omega) hIL
          (by (try rsimp); rw [hgsp]; exact hF4)
          (by (try rsimp); rw [hgsp, hFm,
                show TPM_JG + 0xFFFFFFEA + 0xFFFFEBAA = TPM_JG + 0xFFFFF616 + 0xFFFFF57E by decide]
              exact hPS.2.ri.es.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm, show TPM_JG + 0xFFFFFFEA + 0xBF68 = TPM_JG + 0xFFFFF616 + 0xC93C by decide]
              exact hPS.2.ri.mc.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm]; exact hSb.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm]; exact hSI.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm]; exact E.lowS (by decide) (by decide) (by decide)) fun m5 ha0 hO5 => ?_
        have hO5' : Out M4 m5.mem (s + BitVec.ofNat 32 0x372C) 4 := by
          (try rsimp at hO5); rw [hgsp, hFm] at hO5; exact hO5
        have hkb : memBytes M4 (SP + BitVec.ofNat 32 (ep + kp + 1)) b.length = b := by
          rw [E.bytes hO4 hSb, hbl, ← hbe]
        rw [hkb, E.bytes hO4 hSI] at ha0
        generalize m5.mem = M5 at hO5'
        have hO6 : Out M1 M5 s 0x38EC := hO4.trans (Out.upK rfl hO5' (by decide))
        have hCe : PmCc M5 (F + BitVec.ofNat 32 0xC8) SP SL nx :=
          hCd.keep hO5' (E.fs (c := 0xC8) (n := 12) (d := 0x372C) (k := 4) (Or.inr (by decide)) (by decide)
            (by decide)).symm
        have hLe : RmLow Mz M5 F := hLd.out hO5' (E.fs (c := 0xC) (n := 0x3C) (d := 0x372C) (k := 4)
          (Or.inr (by decide)) (by decide) (by decide)).symm
        refine WP.zero fun hz5 => ?_
        by_cases hbk : b = memBytes M0 IDA IL
        · -- The key ID matches: read `sig`.
          simp only [hbk, ↓reduceIte] at ha0
          refine WP.branch rkm_at_144 (fun eb => ?_) (fun _ => ?_) <;> wn
          · exfalso; (try rsimp at eb); rw [ha0] at eb; exact absurd eb (by decide)
          have hg8 : memLoad32 M2 (F + 0x4C) = SP + BitVec.ofNat 32 ep := t2e
          refine WP.aluImm rkm_at_146 ?_; wn
          refine WP.aluImm rkm_at_148 ?_; wn
          refine WP.alu rkm_at_14a ?_; wn
          refine WP.alu rkm_at_14c ?_; wn
          refine WP.lui rkm_at_14e ?_; wn
          refine WP.aluImm rkm_at_152 ?_; wn
          have hc5 := E.codeA hO6
          refine WP.callField (tb := TPM_JF) (out := F + 0x48) (s := s + BitVec.ofNat 32 0x362C)
            (p := SP + BitVec.ofNat 32 ep) (kq := TPM_KG) (n := el) (kl := 3)
            rkm_at_156 rkm_at_15a (by decide) (by decide) (by decide) hc5.rk.pm.fieldC
            (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [hgsp, hg8, ev0])
            (by (try rsimp); rw [hgsp, t3', ev0])
            (by (try rsimp); (try simp only [ev0]); (try rfl)) (by (try rsimp); (try simp only [ev0]); (try rfl))
            (by (try rsimp); rw [hgsp]; exact (E.sp 0x362C (by decide)).symm)
            (E.alS (by decide)) (aligned_add hF4 (by decide)) (by have := E.wS (d := 0x362C) (k := 260) (by decide); omega)
            (by decide) (by rw [tex_toNat (by omega)]; omega) (by rw [tex_toNat (by omega)]; omega)
            (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSe.sub (by decide))
            (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
            (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
            (E.lowF (by decide) (by decide) (by decide)) fun m6 hR => ?_
          rw [E.bytes hO6 hSe, tpm_kg hc5.rk.pm] at hR
          generalize m6.mem = M6 at hR
          obtain ⟨Mc, hOc, hGR⟩ := hR
          have hO7 : Out M1 M6 s 0x38EC :=
            hO6.trans ((Out.upK rfl hOc (by decide)).trans
              (Out.upK (c := 0x3730 + 0x48) (E.Fc 0x48).symm hGR.out (by decide)))
          have hLf : RmLow Mz M6 F :=
            (hLe.out hOc (E.fs (c := 0xC) (n := 0x3C) (d := 0x362C) (k := 260) (Or.inr (by decide)) (by decide)
              (by decide)).symm).out hGR.out (rm_ff F (Or.inr (by decide)) (by decide) (by decide))
          refine WP.zero fun hz6 => ?_
          refine WP.lw rkm_at_15e (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x48) (by decide)) ?_; wn
          rcases hog : objField (memBytes M0 (SP + BitVec.ofNat 32 ep) el) (ascii!"sig") with e | ⟨gp, gl⟩ <;>
            rw [hog] at hGR <;> simp only [fieldRes, Except.map] at hGR
          · -- No `sig`.
            obtain ⟨-, t1, t2⟩ := hGR
            refine WP.branch rkm_at_160 (fun _ => ?_) (fun eb => ?_) <;> wn
            rotate_left
            · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
            exact rm_348 E hO7 (by (try rsimp); exact hgsp) (by keepz E.hz0) (by (try rsimp); exact hg22)
              (by (try rsimp); exact hg20) hin hn E.hz0 (by rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl, t2, BitVec.toNat_ofNat]; have := rm_eb_objField _ _ _ hog; omega)
          · -- `sig` at `gp`.
            obtain ⟨-, t1, t2⟩ := hGR
            have hw := objField_val hog
            rw [memBytes_length] at hw
            have t2' : memLoad32 M6 (F + 0x4C) = BitVec.ofNat 32 gl := by
              rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
            have hpg : SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 gp = SP + BitVec.ofNat 32 (ep + gp) :=
              add_ofNat_assoc SP ep gp
            have hq3 := nx_q0 hS0 (n := SL) (pos := ep + gp) (by omega) (by omega)
            refine WP.branch rkm_at_160 (fun eb => ?_) (fun _ => ?_) <;> wn
            · exfalso; (try rsimp at eb); rw [hgsp, t1, hpg, hq3] at eb; exact absurd eb (by decide)
            refine WP.lw rkm_at_164 (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x4C) (by decide)) ?_; wn
            refine WP.aluImm rkm_at_166 ?_; wn
            have hc7 := E.codeA hO7
            refine WP.callStr (tb := TPM_JS) (out := F + 0x18C) (p := SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 gp)
              (n := gl) rkm_at_168 rkm_at_16c (by decide) (by decide) (by decide) hc7.rk.pm.str
              (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [hgsp, t1]) (by (try rsimp); rw [hgsp, t2'])
              (by omega) (aligned_add hF4 (k := 0x18C) (by decide)) (E.lowF (by decide) (by decide) (by decide))
              (E.lowF (by decide) (by decide) (by decide)) fun m7 hS => ?_
            have hSg : Sep s 0x3920 (SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 gp) gl := by
              rw [hpg]; exact E.hSS.subR (by omega)
            rw [E.bytes hO7 hSg, tex_strRes] at hS
            generalize m7.mem = M7 at hS
            have hO8 : Out M1 M7 s 0x38EC :=
              hO7.trans (Out.upK (c := 0x3730 + 0x18C) (E.Fc 0x18C).symm hS.out (by decide))
            have hLg : RmLow Mz M7 F := hLf.out hS.out (rm_ff F (Or.inr (by decide)) (by decide) (by decide))
            have hA3 : slice (slice (memBytes M0 SP SL) ep el) gp gl =
                memBytes M0 (SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 gp) gl := by
              rw [hA1]; exact tuf_memBytes_drop_take hw.2
            have hL2 := hL.trans (msig_sig hne (by rw [hA1]; exact hof) (by rw [hA2, hsb, hbk])
              (by rw [hA1]; exact hog))
            rw [hA3] at hL2
            refine WP.zero fun hz7 => ?_
            refine WP.lw rkm_at_170 (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x18C) (by decide)) ?_; wn
            rcases hsg : strBody (memBytes M0 (SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 gp) gl) with _ | c <;>
              rw [hsg] at hS <;> simp only [Option.map_none, Option.map_some] at hS
            · -- `sig` is not a string.
              obtain ⟨-, t1, t2⟩ := hS
              refine WP.branch rkm_at_174 (fun _ => ?_) (fun eb => ?_) <;> wn
              rotate_left
              · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
              exact rm_34e E hO8 (by (try rsimp); exact hgsp) (by keepz E.hz0) (by (try rsimp); exact hg22)
                (by (try rsimp); exact hg20) hin hn E.hz0 (by rw [show F + 0x190 = F + 0x18C + 4 by rw [BitVec.add_assoc]; rfl, t2]; decide)
            · -- The signature `c`.
              obtain ⟨-, t1, t2⟩ := hS
              obtain ⟨hc2', hce⟩ := tex_body hsg
              rw [memBytes_length] at hc2' hce
              rw [tuf_memBytes_drop_take (by omega), add_ofNat_assoc, add_ofNat_assoc, ← Nat.add_assoc] at hce
              have hcl : c.length = gl - 2 := by rw [hce, memBytes_length]
              have hpc : SP + BitVec.ofNat 32 ep + BitVec.ofNat 32 gp + 1 = SP + BitVec.ofNat 32 (ep + gp + 1) := by
                rw [hpg]; exact add_ofNat_assoc SP (ep + gp) 1
              have t1' : memLoad32 M7 (F + 0x18C) = SP + BitVec.ofNat 32 (ep + gp + 1) := t1.trans hpc
              have t2' : memLoad32 M7 (F + 0x190) = BitVec.ofNat 32 c.length := by
                rw [show F + 0x190 = F + 0x18C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
              have hq4 := nx_q0 hS0 (n := SL) (pos := ep + gp + 1) (by omega) (by omega)
              refine WP.branch rkm_at_174 (fun eb => ?_) (fun _ => ?_) <;> wn
              · exfalso; (try rsimp at eb); rw [hgsp, t1', hq4] at eb; exact absurd eb (by decide)
              refine WP.lw rkm_at_178 (by (try rsimp); rw [hgsp]; exact aligned_add hF4 (k := 0x190) (by decide))
                ?_; wn
              refine WP.sw rkm_at_17c (by (try rsimp); rw [hgsp]; exact E.alF (c := 8) (by decide))
                (by (try rsimp); rw [hgsp]; exact E.cF (c := 8) (by decide)) ?_; wn
              refine hfd _ _ (ep + gp + 1) c.length
                (by (try rsimp); rw [hgsp]
                    exact hO8.trans (Out.upK (c := 0x3730 + 8) (E.Fc 8).symm (out_store32 _ _ _) (by decide)))
                (by (try rsimp); rw [hgsp]
                    exact hLg.out (out_store32 _ _ _) (rm_ff F (Or.inl (by decide)) (by decide) (by decide)))
                (by rmkeep (fun x hx => hK x (rm_kls x hx))) (by (try rsimp)) (by keepz E.hz0) (by (try rsimp); rw [hgsp, t1'])
                (by (try rsimp); rw [hgsp, memLoad32_store32_same, t2']) (by omega) ?_
              rw [hL2, hsg, hcl, ← hce]; rfl
        · -- A different key ID: the next item.
          simp only [hbk, ↓reduceIte] at ha0
          refine WP.branch rkm_at_144 (fun _ => ?_) (fun eb => ?_) <;> wn
          rotate_left
          · exfalso; (try rsimp at eb); rw [ha0] at eb; exact absurd eb (by decide)
          refine ih nx M5 _ hO6 hLe hCe hxN (by omega) (by rmkeep hK) (by (try rsimp)) (by keepz E.hz0) ?_
          rw [hL, msig_ne hne (by rw [hA1]; exact hof) (by rw [hA2]; exact hsb) hbk]

/-- The registers that the search keeps: `sp`, and `s2` to `s11` but `s9`. -/
def RmRegs (g : Fin 32 → Word) (F R IDA : Word) (n i : Nat) (G : Fin 32 → Word) : Prop :=
  g sp = F ∧ g 18 = BitVec.ofNat 32 0x62 ∧ g 19 = R ∧ g 20 = BitVec.ofNat 32 n ∧ g 21 = IDA ∧
    g 22 = BitVec.ofNat 32 i ∧ g 23 = G 23 ∧ g 24 = G 24 ∧ g 26 = G 26 ∧ g 27 = G 27

theorem rm_regs {g' gK G : Fin 32 → Word} {F R IDA : Word} {n i : Nat} (hK : ∀ x, x ∈ rmKLs → g' x = gK x)
    (hsp : gK sp = F) (h18 : gK 18 = BitVec.ofNat 32 0x62) (h19 : gK 19 = R) (h20 : gK 20 = BitVec.ofNat 32 n)
    (h21 : gK 21 = IDA) (h22 : gK 22 = BitVec.ofNat 32 i) (h23 : gK 23 = G 23) (h24 : gK 24 = G 24)
    (h26 : gK 26 = G 26) (h27 : gK 27 = G 27) : RmRegs g' F R IDA n i G :=
  ⟨(hK sp (by decide)).trans hsp, (hK 18 (by decide)).trans h18, (hK 19 (by decide)).trans h19,
    (hK 20 (by decide)).trans h20, (hK 21 (by decide)).trans h21, (hK 22 (by decide)).trans h22,
    (hK 23 (by decide)).trans h23, (hK 24 (by decide)).trans h24, (hK 26 (by decide)).trans h26,
    (hK 27 (by decide)).trans h27⟩

theorem rm_metLookup {a id : Bytes} (h : ¬(a.length = 0 ∨ a.getD 0 0 ≠ 91)) :
    metLookup a id = metSig a id (a.length + 1) (skipWs a 1) := by
  unfold metLookup; exact ite_eq_right h

theorem rm_sll6 : ∀ i : Nat, i < 8 → aluEval .sll (BitVec.ofNat 32 i) 6 = BitVec.ofNat 32 (64 * i) := by decide

set_option maxHeartbeats 4000000 in
/-- From 0xAA: `elements` on the signatures, the `SL` bytes at `SP` that
`a3` and `a2` hold, a copy of its cursor to `F + 0xC8`, and the search for
the ID of key `i`, the `IL` bytes at `R + 0x318 + 64 i`. -/
theorem rm_open (E : RmBase M0 M1 s F R MP SP ML SL g0) {g : Fin 32 → Word} (hsp : g sp = F) {i n IL : Nat}
    (hi8 : i < 8) (hin : i < n) (hn : n < 2 ^ 32) (hIL : IL ≤ 0x40) (h19 : g 19 = R)
    (h20 : g 20 = BitVec.ofNat 32 n) (h22 : g 22 = BitVec.ofNat 32 i) (h25 : g 25 = BitVec.ofNat 32 IL)
    (h13 : g 13 = SP) (h12 : g 12 = BitVec.ofNat 32 SL) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    {Mk Mz : Word → BitVec 8} (hO : Out M1 Mk s 0x38EC) (hLo : RmLow Mz Mk F)
    (hnf : ∀ (Mk : Word → BitVec 8) (g' : Fin 32 → Word), Out M1 Mk s 0x38EC → RmLow Mz Mk F →
      RmRegs g' F R (R + BitVec.ofNat 32 (0x318 + 64 * i)) n i g → g' 0 = 0 → (∀ x, x ∉ rkE → g' x = g0 x) →
      metLookup (memBytes M0 SP SL) (memBytes M0 (R + BitVec.ofNat 32 (0x318 + 64 * i)) IL) = some none →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x2C0 g')
    (hfd : ∀ (Mk : Word → BitVec 8) (g' : Fin 32 → Word) (q l : Nat), Out M1 Mk s 0x38EC → RmLow Mz Mk F →
      RmRegs g' F R (R + BitVec.ofNat 32 (0x318 + 64 * i)) n i g → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → g' 25 = SP + BitVec.ofNat 32 q →
      memLoad32 Mk (F + 8) = BitVec.ofNat 32 l → q + l ≤ SL →
      metLookup (memBytes M0 SP SL) (memBytes M0 (R + BitVec.ofNat 32 (0x318 + 64 * i)) IL) =
        some (some (memBytes M0 (SP + BitVec.ofNat 32 q) l)) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x17E g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0xAA g := by
  have hF4 : F.toNat % 4 = 0 := by have := E.halF; omega
  have hSL := E.hSL
  have hSw := E.hSw
  have hS0 := E.hS0
  have hc := E.codeA hO
  refine WP.aluImm rkm_at_aa ?_; wn
  refine WP.aluImm rkm_at_ae ?_; wn
  refine WP.alu rkm_at_b0 ?_; wn
  refine WP.callElements (tb := TPM_JEL) (out := F + 0x48) (s := s + BitVec.ofNat 32 0x3720) (p := SP) (n := SL)
    rkm_at_b2 rkm_at_b6 (by decide) (by decide) (by decide) hc.rk.pm.el hc.rk.pm.sw
    (by (try rsimp); rw [ev_add, hsp]) (by (try rsimp); (try simp only [ev0]); exact h13)
    (by (try rsimp); (try simp only [ev0]); exact h12)
    (by (try rsimp); rw [hsp]; exact (E.sp 0x3720 (by decide)).symm) (by omega) (E.alS (by decide))
    (aligned_add hF4 (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.hSS.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO E.hSS] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hCR⟩ := hR
  have hO2 : Out M1 M2 s 0x38EC :=
    hO.trans ((Out.upK rfl hOa (by decide)).trans (Out.upK (c := 0x3730 + 0x48) (E.Fc 0x48).symm hCR.out (by decide)))
  have hL2 : RmLow Mz M2 F :=
    (hLo.out hOa (E.fs (c := 0xC) (n := 0x3C) (d := 0x3720) (k := 16) (Or.inr (by decide)) (by decide)
      (by decide)).symm).out hCR.out (rm_ff F (Or.inr (by decide)) (by decide) (by decide))
  refine WP.zero fun hz2 => ?_
  refine WP.lw rkm_at_ba (by (try rsimp); rw [hsp]; exact aligned_add hF4 (k := 0x48) (by decide)) ?_; wn
  refine WP.lbu rkm_at_bc ?_; wn
  rcases hco : curOpen 91 SP (memBytes M0 SP SL) with _ | ⟨q, l, k⟩ <;> rw [hco] at hCR
  · obtain ⟨-, t1, t2⟩ := hCR
    refine WP.branch rkm_at_c0 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    exact rm_3aa E hO2 (by (try rsimp); exact hsp) (by keepz E.hz0) (by (try rsimp); exact h22)
      (by (try rsimp); exact h20) hin hn E.hz0
      (by (try rsimp); rw [hsp, show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl, t2]; decide)
  · obtain ⟨hq, hl, hk, hnc⟩ := pm_co_some hco
    rw [memBytes_length] at hl
    obtain ⟨-, t1, t2, t3⟩ := hCR
    rw [hq] at t1; rw [hl] at t2; rw [hk] at t3
    refine WP.branch rkm_at_c0 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb
      have e0 : SP = 0 := by simpa [branchTaken] using eb
      exact hS0 (by rw [e0]; rfl)
    refine WP.aluImm rkm_at_c4 ?_; wn
    refine WP.aluImm rkm_at_c8 ?_; wn
    refine WP.alu rkm_at_cc ?_; wn
    refine WP.aluImm rkm_at_ce ?_; wn
    refine WP.aluImm rkm_at_d0 ?_; wn
    refine WP.aluImm rkm_at_d4 ?_; wn
    have hc2 := E.codeA hO2
    refine WP.callMemcpy (dst := F + 0xCD) (src := F + 0x4D) (F := s + BitVec.ofNat 32 0x3720)
      (N := 7) rkm_at_d8 rkm_at_dc (by decide) (by decide) (by decide) hc2.rk.tps.bms
      (E.mcFF hc2 (c := 0xCD) (d := 0x4D) (n := 7) (Or.inr (by decide)) (by decide) (by decide))
      (by (try rsimp); rw [ev_add, hsp]) (by (try rsimp); rw [ev_add, hsp]) (by (try rsimp); (try simp only [ev0]); try rfl)
      (by (try rsimp); rw [hsp]; exact (E.sp 0x3720 (by decide)).symm) (E.lowS (by decide) (by decide) (by decide))
      (E.cF (c := 0xCD) (by decide)) fun m3 hO3 => ?_
    generalize m3.mem = M3 at hO3
    refine WP.sw rkm_at_e0 (by (try rsimp); rw [hsp]; exact aligned_add hF4 (k := 0xC8) (by decide))
      (by (try rsimp); rw [hsp]; exact E.cF (c := 0xC8) (by decide)) ?_; wn
    refine WP.sb rkm_at_e2 (by (try rsimp); rw [hsp]; exact E.cF (c := 0xCC) (by decide)) ?_; wn
    (try rsimp)
    rw [hsp, t1, ri_ze]
    generalize hM5 : memStore8 (memStore32 M3 (F + 200) SP) (F + 204) (M2 (F + 76)) = M5
    have hsk := skipWs_le (memBytes M0 SP SL) 1
    rw [memBytes_length] at hsk hnc
    have hcc := rm_ccopy (M2 := M2) (M3 := M3) (F := F) (S := s + BitVec.ofNat 32 0x3720) (q := SP) (d := 0xC8)
      (a := 0x48) (by decide) (E.fs (Or.inr (by decide)) (by decide) (by decide))
      (by rw [show F + BitVec.ofNat 32 (0x48 + 4) = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2)
      (by rw [show F + BitVec.ofNat 32 (0x48 + 8) = F + 0x48 + 8 by rw [BitVec.add_assoc]; rfl]; exact t3) hO3 hM5
    obtain ⟨hC5, hfa⟩ := hcc
    have hO5 : Out M1 M5 s 0x38EC := fun x hx =>
      (hfa x (by rw [E.Fc]; exact sep_in hx (by decide)) (sep_in hx (by decide))).trans (hO2 x hx)
    have hL5 : RmLow Mz M5 F := fun j hj =>
      (hfa _ (by have := rm_ff F (c := 0xC8) (n := 12) (d := 0xC + j) (k := 1) (Or.inr (by omega)) (by decide)
                    (by omega); rw [← add_ofNat_assoc] at this; exact this.symm)
              (by have := E.fs (c := 0xC + j) (n := 1) (d := 0x3720) (k := 16) (Or.inr (by omega)) (by omega)
                    (by decide); rw [← add_ofNat_assoc] at this; exact this)).trans (hL2 j hj)
    have hIDA : aluEval .add (aluEval .sll (g 22) 6) (aluEval .add (g 19) 792) = R + BitVec.ofNat 32 (792 + 64 * i) := by
      rw [h22, h19, rm_sll6 i hi8, ev_add, ev_add, BitVec.add_comm, BitVec.add_assoc]
      exact congrArg (R + ·) (BitVec.ofNat_add_ofNat 792 (64 * i))
    refine rm_look E (gK := _) ?_ ?_ ?_ ?_ ?_ hin hn (E.hSR.subR (c := 0x318 + 64 * i) (l := IL) (by omega))
      (by omega)
      (fun Mk g' hO' hL' hK' hz' hfr' hm => hnf Mk g' hO' hL'
        (rm_regs (fun x hx => hK' x (rm_kls x hx)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) hz' hfr' hm)
      (fun Mk g' q l hO' hL' hK' hz' hfr' h25' h8 hql hm => hfd Mk g' q l hO' hL'
        (rm_regs hK' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) hz' hfr' h25' h8 hql hm)
      (SL + 1) _ M5 _ hO5 hL5 hC5 (by omega) (by omega) (fun _ _ => rfl) ?_ ?_ (by
        rw [rm_metLookup (by rw [memBytes_length]; exact hnc), memBytes_length])
    all_goals (try rsimp)
    all_goals first
      | exact hsp | exact h19 | exact h20 | exact h22 | exact h25 | exact hIDA
      | (show aluEval .add (g 0) 98 = _; rw [hz]; rfl) | skip
    all_goals keepz E.hz0

end

end C3.RV32
