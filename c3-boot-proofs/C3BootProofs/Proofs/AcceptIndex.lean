import C3BootProofs.Proofs.AcceptIndexTail

/-!
# `boot_main`'s first closure: the index stage

`AcIndexStage` is the stage from 0x2A6 to 0x4E4. It reads the TUF part's
header and its index of document lengths from flash, finds the trusted root
with `Index::doc`, and copies the index into the frame at `sp + 0x244`. It
reaches 0x4E4 only when `decodeTufParts` accepts the part, and then
`AcIndexPost` holds. A flash read that fails, a bad header, a length out of
range, or a trusted root that doesn't end the part leaves through an exit.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3

/-- At 0x2A6: the frame slot that the exits read holds the result pointer
`r`. -/
def AcIndexPre (B r : Word) (n : Machine) : Prop :=
  memLoad32 n.mem (acSlot B 0x40) = r

/-- At 0x4E4, for the part `tuf` that decodes to `parts`, from the state
`n0` at 0x2A6: `s4`, `s5`, `s7`, `s8`, `s9`, and `s11` keep their values,
`s1` points at `sp + 0x1310`, `sp + 0x30` holds `0x6800` more than
`sp + 0x34`, the frame from `sp + 0x34` to `sp + 0x48` keeps its bytes,
`sp + 0x1864` and `sp + 0x1868` hold the trusted root's offset and length in
the part, `sp + 0x34C` holds the number of roots, and `sp + 0x244` holds the
documents' lengths. -/
def AcIndexPost (B : Word) (n0 : Machine) (tuf : Bytes) (parts : TufParts) (n : Machine) : Prop :=
  (∀ q : Fin 32, q.val ∈ [20, 21, 23, 24, 25, 27] → reg n q = reg n0 q) ∧
  reg n (9 : Fin 32) = acSlot B 0x1310 ∧
  memLoad32 n.mem (acSlot B 0x30) = 0x6800 + memLoad32 n0.mem (acSlot B 0x34) ∧
  (∀ k, 0x34 ≤ k → k < 0x48 → n.mem (acSlot B k) = n0.mem (acSlot B k)) ∧
  memLoad32 n.mem (acSlot B 0x1864) = BitVec.ofNat 32 (tuf.length - parts.trustedRoot.length) ∧
  memLoad32 n.mem (acSlot B 0x1868) = BitVec.ofNat 32 parts.trustedRoot.length ∧
  tuf.drop (tuf.length - parts.trustedRoot.length) = parts.trustedRoot ∧
  memLoad32 n.mem (acSlot B 0x34C) = BitVec.ofNat 32 parts.roots.length ∧
  ∀ i, i < parts.roots.length + 2 →
    (memLoad32 n.mem (acSlot B (0x244 + 4 * i))).toNat =
      ((parts.roots ++ [parts.targets, parts.trustedRoot]).getD i []).length

/-- **The index stage**, from 0x2A6 to 0x4E4, for the callees' code in
memory that agrees with `M0` outside the stack and `Buffers`. The part is the
`s7` bytes of flash from `s8`. It reaches 0x4E4 only when the part decodes,
and then `AcIndexPost` holds. -/
def AcIndexStage : Prop :=
  ∀ (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat), RomRead flash R romBase romCode →
  ∀ (Rl : Nat), RomFn romBase romCode 0x40000040 Rl (fun _ => True) → Rl ≤ 0x3A50 →
  ∀ (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcIndexEnv romBase romCode M) →
    CodeIn n.mem AC bootMainClosure0Code → Fr B 0x5A70 → Sep B 0x5A70 romBase romCode.length →
    R ≤ 0x3A50 - 0x150 → R % 4 = 0 →
    St n.mem AC n 0x2A6 (reg n) → AcInv B Bf g t v M0 n → AcIndexPre B r n →
    AcStage B Bf g t r v M0 n 0x4E4 fun n' =>
      ∃ parts, decodeTufParts (flashBytes flash (reg n (24 : Fin 32)).toNat (reg n (23 : Fin 32)).toNat) =
        some parts ∧
        AcIndexPost B n (flashBytes flash (reg n (24 : Fin 32)).toNat (reg n (23 : Fin 32)).toNat) parts n'

theorem acx_flen (f : Nat → BitVec 8) (a len : Nat) : (flashBytes f a len).length = len := by
  rw [flashBytes, List.length_map, List.length_range]

theorem acx_takeLe (l : List Nat) (i : Nat) : (l.take i).sum ≤ l.sum := by
  have := congrArg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at this; omega

/-- The post at 0x4E4 from the frame's facts. -/
theorem acx_post {P : AcxP} (K : AcxK P) {c : Nat} {n : Machine} (S : AcxS4 P c n) :
    ∃ parts, decodeTufParts (acxTuf P) = some parts ∧ AcIndexPost P.B P.n0 (acxTuf P) parts n := by
  have F := K.F
  have hFh := F.hi
  have hc := S.hc
  have hlen : (acxTuf P).length = (reg P.n0 (23 : Fin 32)).toNat := acx_flen _ _ _
  have hosum : 8 + 4 * (c + 2) + ((acxLens (acxTuf P) 8 (c + 2)).take (c + 1)).sum +
      (acxLens (acxTuf P) 8 (c + 2)).getD (c + 1) 0 = 8 + 4 * (c + 2) + (acxLens (acxTuf P) 8 (c + 2)).sum :=
    acx_osum (P := P) (c := c)
  have hol : 8 + 4 * (c + 2) + ((acxLens (acxTuf P) 8 (c + 2)).take (c + 1)).sum +
      (acxLens (acxTuf P) 8 (c + 2)).getD (c + 1) 0 = (reg P.n0 (23 : Fin 32)).toNat := S.hol
  have hb : (acxLens (acxTuf P) 8 (c + 2)).sum ≤ (c + 2) * 0x2800 := acx_lsum S.ok
  have gD : ∀ i, i < 8 → (acxTuf P).getD i 0 = (P.flash ((reg P.n0 (24 : Fin 32)).toNat + i)).toNat :=
    fun i hi => acx_fbD (by omega)
  obtain ⟨parts, hd, hrl, hget⟩ := acx_decode (bs := acxTuf P) (count := c)
    (by rw [hlen]; exact S.hL) (by rw [gD 0 (by decide)]; exact S.f0) (by rw [gD 1 (by decide)]; exact S.f1)
    (by rw [gD 2 (by decide)]; exact S.f2) (by rw [gD 3 (by decide)]; exact S.f3)
    (by rw [gD 4 (by decide), gD 5 (by decide)]; exact S.fv) (by rw [gD 6 (by decide), gD 7 (by decide)]; exact S.fc)
    hc S.ok (by rw [hlen]; omega)
  have hdoc : ∀ i, i < c + 2 → ((parts.roots ++ [parts.targets, parts.trustedRoot]).getD i []).length =
      (acxLens (acxTuf P) 8 (c + 2)).getD i 0 := fun i hi => by
    rw [hget i hi, List.length_take, List.length_drop, hlen]
    have h1 : ((acxLens (acxTuf P) 8 (c + 2)).take (i + 1)).sum =
        ((acxLens (acxTuf P) 8 (c + 2)).take i).sum + (acxLens (acxTuf P) 8 (c + 2)).getD i 0 :=
      acx_takeS _ i (by rw [acx_lens_length]; exact hi)
    have h2 := acx_takeLe (acxLens (acxTuf P) 8 (c + 2)) (i + 1)
    omega
  have htr : (parts.roots ++ [parts.targets, parts.trustedRoot]).getD (c + 1) [] = parts.trustedRoot := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hrl,
      show c + 1 - c = 1 by omega]
    rfl
  have hl : parts.trustedRoot.length = (acxLens (acxTuf P) 8 (c + 2)).getD (c + 1) 0 := by
    rw [← htr]; exact hdoc (c + 1) (by omega)
  have ho : (acxTuf P).length - parts.trustedRoot.length =
      8 + 4 * (c + 2) + ((acxLens (acxTuf P) 8 (c + 2)).take (c + 1)).sum := by omega
  refine ⟨parts, hd, fun q hq => S.ac.kl q (by revert hq; revert q; decide), S.s1, S.w30,
    fun k h1 h2 => S.ac.keep _ (by rw [acSlot, F.at _ (by omega)]; omega) (by rw [acSlot, F.at _ (by omega)]; omega),
    by rw [ho]; exact S.ro, by rw [hl]; exact S.rl, ?_, by rw [hrl]; exact S.cnt, fun i hi => ?_⟩
  · rw [ho, ← htr, hget (c + 1) (by omega)]
    exact (List.take_of_length_le (by rw [List.length_drop, hlen]; omega)).symm
  · rw [hrl] at hi
    rw [hdoc i hi, acx_lens_getD _ _ _ _ hi, ← S.idx i hi, acSlot, show 0x3A50 + (0x244 + 4 * i) = 0x3C94 + 4 * i by
      omega]

set_option maxHeartbeats 4000000 in
/-- **The index stage holds.** -/
theorem acIndexStage : AcIndexStage := by
  intro flash R romBase romCode rd Rl log hRl n B Bf g t r v M0 E C F sRB hR hR4 s I pre
  let P : AcxP := ⟨flash, R, Rl, romBase, romCode, B, Bf, g, t, r, v, M0, n⟩
  have K : AcxK P := ⟨rd, log, hRl, hR, hR4, F, sRB, E, I, pre, C⟩
  have A : AcxC P n := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨n', st, h | ⟨c, S⟩⟩ := acx_to4e4 K A s
  · exact ⟨n', st, .inr ⟨h.1, .inl h.2⟩⟩
  · exact ⟨n', st, .inr ⟨S.ac.inv K, .inr ⟨S.st.pc, acx_post K S⟩⟩⟩

end C3.RV32.Ac
