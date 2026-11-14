import C3BootProofs.Proofs.MemsetAny

/-!
# Memory made of byte regions

The audit's non-vacuity witnesses build a memory that holds each function's
code, and each constant, at its load address. `regionMem` is that memory, and
`regionMem_codeIn` shows it holds a region's bytes from the regions' bounds
alone, so a witness doesn't make the kernel read the memory byte by byte.
-/

namespace C3.RV32

/-- Memory that holds each of `rs`'s byte lists from its address, the first
region that covers an address winning, and zeros elsewhere. -/
def regionMem : List (Nat × List Nat) → Word → BitVec 8
  | [], _ => 0
  | (b, c) :: rs, a =>
    if (a - BitVec.ofNat 32 b).toNat < c.length then byteAt c (a - BitVec.ofNat 32 b).toNat else regionMem rs a

/-- The regions don't wrap past the top of memory, and each lies apart from
every region after it. -/
def regionsApart : List (Nat × List Nat) → Bool
  | [] => true
  | (b, c) :: rs =>
    decide (b + c.length ≤ 2 ^ 32) && rs.all (fun r => decide (r.1 + r.2.length ≤ b ∨ b + c.length ≤ r.1)) &&
      regionsApart rs

theorem regionsApart_wrap : ∀ {rs : List (Nat × List Nat)} {b : Nat} {c : List Nat},
    regionsApart rs = true → (b, c) ∈ rs → b + c.length ≤ 2 ^ 32
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | (b', c') :: rs, b, c, h, hm => by
    simp only [regionsApart, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hm with e | e
    · cases e; exact h.1.1
    · exact regionsApart_wrap h.2 e

theorem regionMem_skip {b' i b : Nat} {c' c : List Nat} {rs : List (Nat × List Nat)}
    (hap : b + c.length ≤ b' ∨ b' + c'.length ≤ b) (hw' : b' + c'.length ≤ 2 ^ 32) (hw : b + c.length ≤ 2 ^ 32)
    (hi : i < c.length) :
    regionMem ((b', c') :: rs) (BitVec.ofNat 32 b + BitVec.ofNat 32 i) =
      regionMem rs (BitVec.ofNat 32 b + BitVec.ofNat 32 i) := by
  have hf : ¬ (BitVec.ofNat 32 b + BitVec.ofNat 32 i - BitVec.ofNat 32 b').toNat < c'.length := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hb : b % 2 ^ 32 = b := Nat.mod_eq_of_lt (by omega)
    have hi' : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    rw [hb, hi', Nat.mod_eq_of_lt (show b + i < 2 ^ 32 by omega)]
    by_cases hb' : b' < 2 ^ 32
    · rw [Nat.mod_eq_of_lt hb']
      omega
    · have : c'.length = 0 := by omega
      omega
  simp only [regionMem]
  rw [ite_eq_right hf]

/-- **A region's bytes are where it says.** -/
theorem regionMem_codeIn : ∀ {rs : List (Nat × List Nat)} {b : Nat} {c : List Nat},
    regionsApart rs = true → (b, c) ∈ rs → CodeIn (regionMem rs) (BitVec.ofNat 32 b) c
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | (b', c') :: rs, b, c, h, hm => fun i hi => by
    have hw := regionsApart_wrap h hm
    have h0 := h
    simp only [regionsApart, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h0
    by_cases e : (b, c) = (b', c')
    · cases e
      simp only [regionMem]
      rw [add_sub_toNat _ (by omega), ite_eq_left hi]
    · have hm' : (b, c) ∈ rs := (List.mem_cons.mp hm).resolve_left e
      have hap := h0.1.2 (b, c) hm'
      rw [regionMem_skip hap h0.1.1 hw hi]
      exact regionMem_codeIn h0.2 hm' i hi

/-- `regionMem_codeIn` at an address given another way. -/
theorem regionMem_codeIn' {rs : List (Nat × List Nat)} {base : Word} {b : Nat} {c : List Nat}
    (hb : base = BitVec.ofNat 32 b) (h : regionsApart rs = true) (hm : (b, c) ∈ rs) : CodeIn (regionMem rs) base c :=
  hb ▸ regionMem_codeIn h hm

/-- `regionMem_codeIn` with the region found by a check the kernel can run. -/
theorem regionMem_codeIn_of_any {rs : List (Nat × List Nat)} {base : Word} {c : List Nat}
    (h : regionsApart rs = true) (hm : rs.any (fun r => r.1 == base.toNat && r.2 == c) = true) :
    CodeIn (regionMem rs) base c := by
  obtain ⟨⟨b, c'⟩, hr, he⟩ := List.any_eq_true.mp hm
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨hb, hc⟩ := he
  subst hc
  have : base = BitVec.ofNat 32 b := by rw [hb, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact this ▸ regionMem_codeIn h hr

end C3.RV32
