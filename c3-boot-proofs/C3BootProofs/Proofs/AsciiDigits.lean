import C3BootProofs.Proofs.DerTlv
import C3BootProofs.Spec.Json

/-!
# `Iterator::all` over ASCII digits, as compiled

`allAsciiDigit` is `iter.all(|b| b.is_ascii_digit())` on a
`core::slice::Iter<u8>`, which `a0` points to: the current pointer at offset
0 and the end at offset 4. Each step stores the advanced pointer back, so
the iterator ends just past the first byte that isn't a digit, or at the end.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem aad_at_0 : fetchRel allAsciiDigitCode 0x0 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem aad_at_2 : fetchRel allAsciiDigitCode 0x2 = some (.load .lw a1 a0 0x4, 2) := by decide
theorem aad_at_4 : fetchRel allAsciiDigitCode 0x4 = some (.aluImm .add a2 x0 0xA, 2) := by decide
theorem aad_at_6 : fetchRel allAsciiDigitCode 0x6 = some (.alu .add a3 x0 a4, 2) := by decide
theorem aad_at_8 : fetchRel allAsciiDigitCode 0x8 = some (.branch .beq a4 a1 0x16, 4) := by decide
theorem aad_at_c : fetchRel allAsciiDigitCode 0xC = some (.load .lbu a5 a3 0x0, 4) := by decide
theorem aad_at_10 : fetchRel allAsciiDigitCode 0x10 = some (.aluImm .add a4 a3 0x1, 4) := by decide
theorem aad_at_14 : fetchRel allAsciiDigitCode 0x14 = some (.aluImm .add a5 a5 0xFFFFFFD0, 4) := by decide
theorem aad_at_18 : fetchRel allAsciiDigitCode 0x18 = some (.store .sw a0 a4 0x0, 2) := by decide
theorem aad_at_1a : fetchRel allAsciiDigitCode 0x1A = some (.branch .bltu a5 a2 0xFFFFFFEC, 4) := by decide
theorem aad_at_1e : fetchRel allAsciiDigitCode 0x1E = some (.alu .xor a1 a1 a3, 2) := by decide
theorem aad_at_20 : fetchRel allAsciiDigitCode 0x20 = some (.aluImm .sltu a0 a1 0x1, 4) := by decide
theorem aad_at_24 : fetchRel allAsciiDigitCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The index of the first byte from `k` that isn't an ASCII digit, among
`f` bytes at `p`, or `k + f` when all are. -/
def adScan (M : Word → BitVec 8) (p : Word) : Nat → Nat → Nat
  | k, 0 => k
  | k, f + 1 => if isDigit (M (p + BitVec.ofNat 32 k)).toNat then adScan M p (k + 1) f else k

/-- The iterator's position, as a count of bytes taken, when `all` returns
for the `n` bytes at `p`: just past the first non-digit, or `n`. -/
def adNext (M : Word → BitVec 8) (p : Word) (n : Nat) : Nat :=
  if adScan M p 0 n < n then adScan M p 0 n + 1 else n

/-- Memory with the iterator at `it` advanced `k` bytes past `p`. -/
def adMem (M : Word → BitVec 8) (it p : Word) (k : Nat) : Word → BitVec 8 :=
  if k = 0 then M else memStore32 M it (p + BitVec.ofNat 32 k)

theorem adScan_le (M : Word → BitVec 8) (p : Word) : ∀ f k, adScan M p k f ≤ k + f
  | 0, k => Nat.le_refl _
  | f + 1, k => by
    unfold adScan
    split
    · have := adScan_le M p f (k + 1); omega
    · omega

theorem adScan_ge (M : Word → BitVec 8) (p : Word) : ∀ f k, k ≤ adScan M p k f
  | 0, k => Nat.le_refl _
  | f + 1, k => by
    unfold adScan
    split
    · have := adScan_ge M p f (k + 1); omega
    · exact Nat.le_refl _

theorem adScan_full (M : Word → BitVec 8) (p : Word) : ∀ f k,
    adScan M p k f = k + f ↔ ∀ i, k ≤ i → i < k + f → isDigit (M (p + BitVec.ofNat 32 i)).toNat = true
  | 0, k => ⟨fun _ i h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | f + 1, k => by
    unfold adScan
    by_cases hd : isDigit (M (p + BitVec.ofNat 32 k)).toNat = true
    · rw [if_pos hd, show k + (f + 1) = k + 1 + f by omega, adScan_full M p f (k + 1)]
      constructor
      · intro h i h1 h2
        by_cases hik : i = k
        · rw [hik]; exact hd
        · exact h i (by omega) h2
      · intro h i h1 h2; exact h i (by omega) h2
    · rw [if_neg hd]
      constructor
      · intro h; exact absurd h (by omega)
      · intro h; exact absurd (h k (Nat.le_refl _) (by omega)) hd

/-- `adScan` reaches the end exactly when every byte is a digit. -/
theorem adScan_all (M : Word → BitVec 8) (p : Word) (n : Nat) :
    adScan M p 0 n = n ↔ (memBytes M p n).all isDigit = true := by
  rw [show (adScan M p 0 n = n) = (adScan M p 0 n = 0 + n) by rw [Nat.zero_add], adScan_full M p n 0,
    List.all_eq_true]
  constructor
  · intro h x hx
    unfold memBytes at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact h i (Nat.zero_le _) (by rw [Nat.zero_add]; exact List.mem_range.mp hi)
  · intro h i _ hi
    exact h _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)

theorem aad_digit : ∀ b : BitVec 8,
    branchTaken .bltu (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0xA = isDigit b.toNat := by
  decide

theorem aad_overwrite (M : Word → BitVec 8) (a v w : Word) :
    memStore32 (memStore32 M a v) a w = memStore32 M a w := by
  funext x
  simp only [memStore32, memStore8]
  by_cases h3 : x = a + 3
  · simp [h3]
  by_cases h2 : x = a + 2
  · simp [h2]
  by_cases h1 : x = a + 1
  · simp [h1]
  by_cases h0 : x = a
  · simp [h0]
  simp only [h3, h2, h1, h0, ite_false]

theorem aad_seqz (a b : Word) : aluEval .sltu (aluEval .xor a b) 0x1 = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    show aluEval .sltu (a ^^^ a) 0x1 = 1
    rw [BitVec.xor_self]; rfl
  · rw [if_neg h]
    have hx : a ^^^ b ≠ 0 := fun e => h (by
      have : b = a ^^^ (a ^^^ b) := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
      rw [e] at this
      exact (this.trans BitVec.xor_zero).symm)
    show (if (a ^^^ b).ult 1 then (1 : Word) else 0) = 0
    exact ite_eq_right (by
      show ¬ decide ((a ^^^ b).toNat < (1 : Word).toNat) = true
      rw [decide_eq_true_iff]; intro hlt
      exact hx (BitVec.eq_of_toNat_eq (by change (a ^^^ b).toNat < 1 at hlt; change _ = 0; omega)))

theorem aad_ofNat_inj {p : Word} {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32)
    (h : p + BitVec.ofNat 32 i = p + BitVec.ofNat 32 j) : i = j :=
  Decidable.byContradiction fun hne => add_ofNat_ne p hi hj hne h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `Iterator::all(u8::is_ascii_digit)`** over the slice
iterator at `it`, whose current pointer is `p` and end `p + n`: it returns 1
in `a0` when all `n` bytes are ASCII digits and 0 otherwise. It leaves the
iterator's current pointer `adNext` bytes past `p`, just past the first byte
that isn't a digit, and writes no other memory and only `a0` through `a5`.
The iterator's first word must be apart from the bytes and the code. -/
theorem allAsciiDigit_correct (m : Machine) {base retAddr it p : Word} {n : Nat}
    (hc : CodeIn m.mem base allAsciiDigitCode) (hpc : m.pc = base) (ha0 : reg m a0 = it)
    (hit : it.toNat % 4 = 0) (hcur : memLoad32 m.mem it = p) (hend : memLoad32 m.mem (it + 4) = p + BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32) (sIC : Sep it 4 base allAsciiDigitCode.length) (sIP : Sep it 4 p n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = adMem m.mem it p (adNext m.mem p n) ∧
      reg m' a0 = (if (memBytes m.mem p n).all isDigit then 1 else 0) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hcM : ∀ k, CodeIn (adMem m.mem it p k) base allAsciiDigitCode := fun k => by
    unfold adMem; split
    · exact hc
    · exact CodeIn.store32 hc sIC
  have rdM : ∀ k i, i < n → adMem m.mem it p k (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) :=
    fun k i hi => by
      unfold adMem; split
      · rfl
      · exact memStore32_get_sep (sIP.subR (c := i) (l := 1) (by omega))
  -- the exit, from 0x1E with the scan stopped at `j`
  have exit_ : ∀ {nn : Machine} (k j : Nat), j ≤ n → St (adMem m.mem it p k) base nn 0x1E (reg nn) →
      reg nn a3 = p + BitVec.ofNat 32 j → reg nn a1 = p + BitVec.ofNat 32 n →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg nn r = reg m r) →
      ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧ m'.mem = adMem m.mem it p k ∧
        reg m' a0 = (if j = n then 1 else 0) ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
    intro nn k j hj st r3 r1 kk
    obtain ⟨n1, d1, u1⟩ := st.alu (hcM k) aad_at_1e (off' := 0x20) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm (hcM k) aad_at_20 (off' := 0x24) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr (hcM k) aad_at_24
    refine ⟨n3, .cons d1 (.cons d2 (.single d3)), ?_, mem3, ?_, fun r h0 h1 h2 h3 h4 h5 => ?_⟩
    · rw [pc3, upd_ne' (by decide) u1.zero, upd_ne' (by decide) st.zero,
        kk ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      rw [r1, r3, aad_seqz]
      by_cases hjn : j = n
      · rw [if_pos hjn, if_pos (by rw [hjn])]
      · rw [if_neg hjn, if_neg (fun e => hjn (aad_ofNat_inj hn (by omega) e).symm)]
    · rw [regs3, upd_ne' h0 u1.zero, upd_ne' h1 st.zero]; exact kk r h0 h1 h2 h3 h4 h5
  -- the loop, from 0x6 at byte `k` with `f` bytes left
  have loop : ∀ f k, k + f = n → ∀ {nn : Machine}, St (adMem m.mem it p k) base nn 0x6 (reg nn) →
      reg nn a4 = p + BitVec.ofNat 32 k → reg nn a1 = p + BitVec.ofNat 32 n → reg nn a2 = 0xA →
      reg nn a0 = it →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg nn r = reg m r) →
      ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧
        m'.mem = adMem m.mem it p (if adScan m.mem p k f < n then adScan m.mem p k f + 1 else n) ∧
        reg m' a0 = (if adScan m.mem p k f = n then 1 else 0) ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
    intro f
    induction f with
    | zero =>
      intro k hk nn st r4 r1 r2 r0 kk
      obtain ⟨n1, d1, u1⟩ := st.alu (hcM k) aad_at_6 (off' := 0x8) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.taken (hcM k) 0x1E aad_at_8 (by decide) (by
        rw [upd_ne' (by decide) st.zero, upd_ne' (by decide) st.zero, r4, r1, show k = n by omega]
        exact beq_iff_eq.mpr rfl)
      obtain ⟨m', c', h1, h2, h3, h4⟩ := exit_ k k (by omega) u2.self
        (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, st.zero, zw, r4])
        (by rw [u2.regs, upd_ne' (by decide) st.zero, r1])
        (fun r h0 h1 h2 h3 h4 h5 => by rw [u2.regs, upd_ne' h3 st.zero]; exact kk r h0 h1 h2 h3 h4 h5)
      have hkn : k = n := by omega
      refine ⟨m', .cons d1 (.cons d2 c'), h1, ?_, ?_, h4⟩
      · rw [h2]; show adMem m.mem it p k = adMem m.mem it p (if k < n then k + 1 else n)
        rw [if_neg (show ¬ k < n by omega), hkn]
      · exact h3
    | succ f ih =>
      intro k hk nn st r4 r1 r2 r0 kk
      obtain ⟨n1, d1, u1⟩ := st.alu (hcM k) aad_at_6 (off' := 0x8) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.notTaken (hcM k) 0xC aad_at_8 (by decide) (by
        rw [upd_ne' (by decide) st.zero, upd_ne' (by decide) st.zero, r4, r1]
        simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
        intro e; have := aad_ofNat_inj (by omega) hn e; omega)
      have v3 : reg n2 a3 = p + BitVec.ofNat 32 k := by
        rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, st.zero, zw, r4]
      have k2 : ∀ q, q ≠ a3 → reg n2 q = reg nn q := fun q h => by rw [u2.regs, upd_ne' h st.zero]
      obtain ⟨n3, d3, u3⟩ := u2.self.lbu (hcM k) aad_at_c (off' := 0x10) (by decide)
      rw [v3, add_lit_zero, rdM k k (by omega)] at u3
      obtain ⟨n4, d4, u4⟩ := u3.aluImm (hcM k) aad_at_10 (off' := 0x14) (by decide)
      obtain ⟨n5, d5, u5⟩ := u4.aluImm (hcM k) aad_at_14 (off' := 0x18) (by decide)
      have v4 : ∀ (g : Fin 32 → Word), g = upd (upd (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32))
          a4 (aluEval .add (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32) a3) 0x1)) a5
          (aluEval .add (upd (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32)) a4
            (aluEval .add (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32) a3) 0x1) a5)
            0xFFFFFFD0) → g a4 = p + BitVec.ofNat 32 (k + 1) := by
        intro g hg; rw [hg]; simp +decide only [upd_app, ↓reduceIte]; rw [v3, ev_add]; exact add_ofNat_assoc p k 1
      have a0v : ∀ (g : Fin 32 → Word), g = upd (upd (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32))
          a4 (aluEval .add (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32) a3) 0x1)) a5
          (aluEval .add (upd (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32)) a4
            (aluEval .add (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32) a3) 0x1) a5)
            0xFFFFFFD0) → ∀ q, q ≠ a4 → q ≠ a5 → g q = reg n2 q := by
        intro g hg q h4 h5; rw [hg, upd_ne' h5 (by simp [upd, u2.self.zero]), upd_ne' h4 (by simp [upd, u2.self.zero]),
          upd_ne' h5 u2.self.zero]
      have r0' := a0v _ rfl a0 (by decide) (by decide)
      rw [k2 a0 (by decide), r0] at r0'
      obtain ⟨n6, d6, u6⟩ := u5.sw (hcM k) aad_at_18 (off' := 0x1A) (by decide) (by rw [r0', add_lit_zero]; exact hit)
      rw [r0', add_lit_zero, v4 _ rfl] at u6
      have eM : memStore32 (adMem m.mem it p k) it (p + BitVec.ofNat 32 (k + 1)) = adMem m.mem it p (k + 1) := by
        unfold adMem
        rw [if_neg (show ¬ (k + 1 = 0) by omega)]
        split
        · rfl
        · exact aad_overwrite _ _ _ _
      rw [eM] at u6
      have kk6 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 →
          upd (upd (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32))
          a4 (aluEval .add (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32) a3) 0x1)) a5
          (aluEval .add (upd (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32)) a4
            (aluEval .add (upd (reg n2) a5 ((m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32) a3) 0x1) a5)
            0xFFFFFFD0) r = reg m r := fun r h0 h1 h2 h3 h4 h5 => by
        rw [a0v _ rfl r h4 h5, k2 r h3]; exact kk r h0 h1 h2 h3 h4 h5
      have dig := aad_digit (m.mem (p + BitVec.ofNat 32 k))
      by_cases hd : isDigit (m.mem (p + BitVec.ofNat 32 k)).toNat = true
      · obtain ⟨n7, d7, u7⟩ := u6.taken (hcM (k + 1)) 0x6 aad_at_1a (by decide) (by
          simp +decide only [upd_app, ↓reduceIte]
          rw [k2 a2 (by decide), r2]; exact dig.trans hd)
        obtain ⟨m', c', h1, h2, h3, h4⟩ := ih (k + 1) (by omega) u7.self (by rw [u7.regs, v4 _ rfl])
          (by rw [u7.regs, a0v _ rfl a1 (by decide) (by decide), k2 a1 (by decide), r1])
          (by rw [u7.regs, a0v _ rfl a2 (by decide) (by decide), k2 a2 (by decide), r2])
          (by rw [u7.regs, r0'])
          (fun r h0 h1 h2 h3 h4 h5 => by rw [u7.regs]; exact kk6 r h0 h1 h2 h3 h4 h5)
        refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c')))))), h1, ?_, ?_, h4⟩
        · rw [h2]; conv => rhs; rw [adScan, if_pos hd]
        · rw [h3]; conv => rhs; rw [adScan, if_pos hd]
      · obtain ⟨n7, d7, u7⟩ := u6.notTaken (hcM (k + 1)) 0x1E aad_at_1a (by decide) (by
          simp +decide only [upd_app, ↓reduceIte]
          rw [k2 a2 (by decide), r2]; exact dig.trans (Bool.eq_false_iff.mpr hd))
        obtain ⟨m', c', h1, h2, h3, h4⟩ := exit_ (k + 1) k (by omega) u7.self
          (by rw [u7.regs, a0v _ rfl a3 (by decide) (by decide), v3])
          (by rw [u7.regs, a0v _ rfl a1 (by decide) (by decide), k2 a1 (by decide), r1])
          (fun r h0 h1 h2 h3 h4 h5 => by rw [u7.regs]; exact kk6 r h0 h1 h2 h3 h4 h5)
        refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c')))))), h1, ?_, ?_, h4⟩
        · rw [h2]; conv => rhs; rw [adScan, if_neg hd]
          rw [if_pos (by omega)]
        · rw [h3]; conv => rhs; rw [adScan, if_neg hd]
  obtain ⟨n1, d1, u1⟩ := s0.lw hc aad_at_0 (off' := 0x2) (by decide) (by rw [ha0, add_lit_zero]; exact hit)
  obtain ⟨n2, d2, u2⟩ := u1.lw hc aad_at_2 (off' := 0x4) (by decide) (by
    rw [upd_ne' (by decide) hz, ha0]; exact aligned_add hit (k := 4) (by decide))
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc aad_at_4 (off' := 0x6) (by decide)
  have hM0 : adMem m.mem it p 0 = m.mem := rfl
  obtain ⟨m', c', h1, h2, h3, h4⟩ := loop n 0 (Nat.zero_add n) (nn := n3) (by rw [hM0]; exact u3.self)
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, add_lit_zero, hcur, add_ofNat_zero])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; exact hend)
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0])
    (fun r h0 h1 h2 h3 h4 h5 => by
      rw [u3.regs, upd_ne' h2 (by simp [upd, hz]), upd_ne' h1 (by simp [upd, hz]), upd_ne' h4 hz])
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h1, by rw [h2]; rfl, ?_, h4⟩
  rw [h3]
  by_cases ha : (memBytes m.mem p n).all isDigit = true
  · rw [if_pos ((adScan_all m.mem p n).mpr ha), if_pos ha]
  · rw [if_neg (fun e => ha ((adScan_all m.mem p n).mp e)), if_neg ha]

end C3.RV32
