import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.Bundle
import C3BootProofs.Proofs.MagicCur
import C3BootProofs.Proofs.U16
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.SvRoot
import C3BootProofs.Proofs.NonAdjacentForm
import C3BootProofs.Proofs.Sha2Update
import C3BootProofs.Proofs.ParseSpec

/-!
# `boot_main`'s first closure: tools for the bundle stage

`decodeBundle` on bytes in memory, the frame slots that the bundle stage
writes, and the calls it makes: `memcpy` for the trust root, then
`Reader::magic`, `Reader::version_1`, and `bundle::field`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-! ## `decodeBundle` on bytes in memory -/

theorem acb_app4 {a b c d e f g h : BitVec 8} (H : a ++ b ++ c ++ d = e ++ f ++ g ++ h) :
    a = e ∧ b = f ∧ c = g ∧ d = h := by
  have h1 := congrArg (fun x => x.extractLsb' 0 8) H
  have h2 := congrArg (fun x => x.extractLsb' 8 24) H
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h1 h2
  have h3 := congrArg (fun x => x.extractLsb' 0 8) h2
  have h4 := congrArg (fun x => x.extractLsb' 8 16) h2
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h3 h4
  have h5 := congrArg (fun x => x.extractLsb' 0 8) h4
  have h6 := congrArg (fun x => x.extractLsb' 8 8) h4
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h5 h6
  exact ⟨h6, h5, h3, h1⟩

theorem acb_mb2 (M : Word → BitVec 8) (p : Word) :
    memBytes M p 2 = [(M p).toNat, (M (p + 1)).toNat] := by
  unfold memBytes
  show [(M (p + BitVec.ofNat 32 0)).toNat, (M (p + BitVec.ofNat 32 1)).toNat] = _
  rw [add_ofNat_zero]; rfl

theorem acb_mb4 (M : Word → BitVec 8) (p : Word) :
    memBytes M p 4 = [(M p).toNat, (M (p + 1)).toNat, (M (p + 2)).toNat, (M (p + 3)).toNat] := by
  unfold memBytes
  show [(M (p + BitVec.ofNat 32 0)).toNat, (M (p + BitVec.ofNat 32 1)).toNat,
    (M (p + BitVec.ofNat 32 2)).toNat, (M (p + BitVec.ofNat 32 3)).toNat] = _
  rw [add_ofNat_zero]; rfl

theorem acb_readU32 (M : Word → BitVec 8) (p : Word) {n : Nat} (h : 4 ≤ n) :
    readU32 (memBytes M p n) = some ((memLoad32 M p).toNat, memBytes M (p + 4) (n - 4)) := by
  have e := memBytes_split M p 4 (n - 4)
  rw [show 4 + (n - 4) = n by omega] at e
  rw [e, acb_mb4, memLoad32_toNat]; rfl

/-- One field, read at offset `q` of the `L` bytes at `Bf`. -/
theorem acb_field_spec (M : Word → BitVec 8) (Bf : Word) {L q len : Nat} (lo hi : Nat) {q' q'' : Nat}
    (e1 : q' = q + 4) (e2 : q'' = q + 4 + len)
    (hl : q + 4 + len ≤ L) (hlen : (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat = len)
    (hlo : lo ≤ len) (hhi : len ≤ hi) :
    readField lo hi (memBytes M (Bf + BitVec.ofNat 32 q) (L - q)) =
      some (memBytes M (Bf + BitVec.ofNat 32 q') len, memBytes M (Bf + BitVec.ofNat 32 q'') (L - q'')) := by
  subst e1 e2
  unfold readField
  rw [acb_readU32 M _ (by omega), hlen]
  have hr : (lo ≤ len && len ≤ hi && len ≤ (memBytes M (Bf + BitVec.ofNat 32 q + 4) (L - q - 4)).length) = true := by
    rw [memBytes_length]; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hlo, hhi⟩, by omega⟩
  simp only [Option.bind_eq_bind, Option.bind_some, hr, require, ↓reduceIte]
  rw [memBytes_take M _ (by omega), memBytes_drop M _ (by omega),
    show Bf + BitVec.ofNat 32 q + 4 = Bf + BitVec.ofNat 32 (q + 4) from add_ofNat_assoc Bf q 4,
    add_ofNat_assoc, show L - q - 4 - len = L - (q + 4 + len) by omega]
  rfl

/-- The magic number `C3BN` and format version 1. -/
theorem acb_header_spec (M : Word → BitVec 8) (Bf : Word) {L : Nat} (h6 : 6 ≤ L)
    (hm : memLoad32 M Bf = 0x4E423343)
    (hv : (M (Bf + 4)).toNat + 256 * (M (Bf + 4 + 1)).toNat = 1) :
    readHeader magicBundle (memBytes M Bf L) = some (memBytes M (Bf + BitVec.ofNat 32 6) (L - 6)) := by
  have hb : M (Bf + 3) = 0x4E ∧ M (Bf + 2) = 0x42 ∧ M (Bf + 1) = 0x33 ∧ M Bf = 0x43 := by
    unfold memLoad32 at hm
    exact acb_app4 (hm.trans (by decide : (0x4E423343 : Word) = 0x4E#8 ++ 0x42#8 ++ 0x33#8 ++ 0x43#8))
  have e := memBytes_split M Bf 4 (L - 4)
  rw [show 4 + (L - 4) = L by omega] at e
  have e2 := memBytes_split M (Bf + BitVec.ofNat 32 4) 2 (L - 4 - 2)
  rw [show 2 + (L - 4 - 2) = L - 4 by omega] at e2
  have hx : readExpect magicBundle (memBytes M Bf L) = some (memBytes M (Bf + BitVec.ofNat 32 4) (L - 4)) := by
    unfold readExpect
    rw [e, acb_mb4, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, ite_eq_left]
    · rfl
    · rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      refine ⟨rfl, ?_⟩
      simp only [List.length_append, memBytes_length, List.length_cons, List.length_nil]
      show 4 ≤ _
      omega
  have hu : readU16 (memBytes M (Bf + BitVec.ofNat 32 4) (L - 4)) =
      some (1, memBytes M (Bf + BitVec.ofNat 32 6) (L - 6)) := by
    rw [e2, acb_mb2]
    show some ((M (Bf + BitVec.ofNat 32 4)).toNat + 256 * (M (Bf + BitVec.ofNat 32 4 + 1)).toNat,
      memBytes M (Bf + BitVec.ofNat 32 4 + BitVec.ofNat 32 2) (L - 4 - 2)) = _
    rw [show (M (Bf + BitVec.ofNat 32 4)).toNat + 256 * (M (Bf + BitVec.ofNat 32 4 + 1)).toNat = 1 from hv,
      add_ofNat_assoc, show L - 4 - 2 = L - 6 by omega]
  unfold readHeader
  rw [hx]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hu]
  rfl

/-- The log index: a little-endian 64-bit number. -/
theorem acb_leNat8 (M : Word → BitVec 8) (p : Word) :
    leNat (memBytes M p 8) = (memLoad32 M p).toNat + 2 ^ 32 * (memLoad32 M (p + 4)).toNat := by
  rw [show (8 : Nat) = 4 + 4 from rfl, memBytes_split, acb_mb4, acb_mb4, memLoad32_toNat, memLoad32_toNat]
  simp only [List.cons_append, List.nil_append, leNat, le32]
  rw [show p + BitVec.ofNat 32 4 = p + 4 from rfl]
  omega

theorem acb_u64 (M : Word → BitVec 8) (p : Word) {lo hi : Word} (hlo : memLoad32 M p = lo)
    (hhi : memLoad32 M (p + 4) = hi) :
    leNat (memBytes M p 8) < 2 ^ 64 ∧ BitVec.ofNat 32 (leNat (memBytes M p 8)) = lo ∧
      BitVec.ofNat 32 (leNat (memBytes M p 8) / 2 ^ 32) = hi := by
  rw [acb_leNat8, hlo, hhi]
  have h1 := lo.isLt; have h2 := hi.isLt
  refine ⟨by omega, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
  · rw [BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_ofNat]; omega

/-- **`decodeBundle` on the `L` bytes at `Bf`**, given what the code checked:
the header, then each field's length at its offset `q`. -/
theorem acb_decode (M : Word → BitVec 8) (Bf : Word) {L l1 l2 l4 l5 l6 : Nat}
    (hm : memLoad32 M Bf = 0x4E423343)
    (hv : (M (Bf + 4)).toNat + 256 * (M (Bf + 4 + 1)).toNat = 1)
    (h1 : (memLoad32 M (Bf + BitVec.ofNat 32 6)).toNat = l1) (r1 : 1 ≤ l1 ∧ l1 ≤ 4096)
    (h2 : (memLoad32 M (Bf + BitVec.ofNat 32 (10 + l1))).toNat = l2) (r2 : 8 ≤ l2 ∧ l2 ≤ 72)
    (h3 : (memLoad32 M (Bf + BitVec.ofNat 32 (14 + l1 + l2))).toNat = 8)
    (h4 : (memLoad32 M (Bf + BitVec.ofNat 32 (26 + l1 + l2))).toNat = l4) (r4 : l4 ≤ 2048)
    (m4 : l4 % 32 = 0)
    (h5 : (memLoad32 M (Bf + BitVec.ofNat 32 (30 + l1 + l2 + l4))).toNat = l5) (r5 : 1 ≤ l5 ∧ l5 ≤ 1024)
    (h6 : (memLoad32 M (Bf + BitVec.ofNat 32 (34 + l1 + l2 + l4 + l5))).toNat = l6)
    (r6 : 1 ≤ l6 ∧ l6 ≤ 8192)
    (hL : L = 38 + l1 + l2 + l4 + l5 + l6) :
    decodeBundle (memBytes M Bf L) = some
      ⟨memBytes M (Bf + BitVec.ofNat 32 10) l1, memBytes M (Bf + BitVec.ofNat 32 (14 + l1)) l2,
        leNat (memBytes M (Bf + BitVec.ofNat 32 (18 + l1 + l2)) 8),
        memBytes M (Bf + BitVec.ofNat 32 (30 + l1 + l2)) l4,
        memBytes M (Bf + BitVec.ofNat 32 (34 + l1 + l2 + l4)) l5,
        memBytes M (Bf + BitVec.ofNat 32 (38 + l1 + l2 + l4 + l5)) l6⟩ := by
  have f1 := acb_field_spec M Bf (L := L) (q := 6) (q' := 10) (q'' := 10 + l1) 1 4096 rfl (by omega)
    (by omega) h1 r1.1 r1.2
  have f2 := acb_field_spec M Bf (L := L) (q := 10 + l1) (q' := 14 + l1) (q'' := 14 + l1 + l2) 8 72
    (by omega) (by omega) (by omega) h2 r2.1 r2.2
  have f3 := acb_field_spec M Bf (L := L) (q := 14 + l1 + l2) (q' := 18 + l1 + l2) (q'' := 26 + l1 + l2) 8 8
    (by omega) (by omega) (by omega) h3 (by omega) (by omega)
  have f4 := acb_field_spec M Bf (L := L) (q := 26 + l1 + l2) (q' := 30 + l1 + l2) (q'' := 30 + l1 + l2 + l4)
    0 (maxProofHashes * 32) (by omega) (by omega) (by omega) h4 (by omega) (by unfold maxProofHashes; omega)
  have f5 := acb_field_spec M Bf (L := L) (q := 30 + l1 + l2 + l4) (q' := 34 + l1 + l2 + l4)
    (q'' := 34 + l1 + l2 + l4 + l5) 1 1024 (by omega) (by omega) (by omega) h5 r5.1 r5.2
  have f6 := acb_field_spec M Bf (L := L) (q := 34 + l1 + l2 + l4 + l5) (q' := 38 + l1 + l2 + l4 + l5)
    (q'' := L) 1 8192 (by omega) (by omega) (by omega) h6 r6.1 r6.2
  rw [Nat.sub_self] at f6
  unfold decodeBundle
  rw [acb_header_spec M Bf (by omega) hm hv]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [f1]; simp only [Option.bind_some]
  rw [f2]; simp only [Option.bind_some]
  rw [f3]; simp only [Option.bind_some]
  rw [f4]; simp only [Option.bind_some, memBytes_length, m4]
  rw [show require ((0 : Nat) == 0) = some () from rfl]; simp only [Option.bind_some]
  rw [f5]; simp only [Option.bind_some]
  rw [f6]; simp only [Option.bind_some]
  rfl

end C3.RV32.Ac
