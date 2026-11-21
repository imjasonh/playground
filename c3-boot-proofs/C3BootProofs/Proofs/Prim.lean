import C3BootProofs.Proofs.CondNeg12
import C3BootProofs.Proofs.P384Sub
import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.DerTlv

/-!
# `u32_min` and `<[u8]>::reverse`, as compiled

`crypto_bigint::primitives::u32_min`, specialized to a bound of 62, picks
the smaller value in constant time through a mask that it passes through the
stack. `<[u8]>::reverse` swaps bytes from both ends toward the middle.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem umin_at_0 : fetchRel u32MinCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem umin_at_2 : fetchRel u32MinCode 0x2 = some (.aluImm .add a1 sp 0xF, 4) := by decide
theorem umin_at_6 : fetchRel u32MinCode 0x6 = some (.aluImm .xor a2 a0 0xFFFFFFFF, 4) := by decide
theorem umin_at_a : fetchRel u32MinCode 0xA = some (.aluImm .add a3 a0 0xFFFFFFC2, 4) := by decide
theorem umin_at_e : fetchRel u32MinCode 0xE = some (.alu .and a2 a2 a3, 2) := by decide
theorem umin_at_10 : fetchRel u32MinCode 0x10 = some (.aluImm .srl a2 a2 0x1F, 2) := by decide
theorem umin_at_12 : fetchRel u32MinCode 0x12 = some (.store .sb sp a2 0xF, 4) := by decide
theorem umin_at_16 : fetchRel u32MinCode 0x16 = some (.load .lbu a1 sp 0xF, 4) := by decide
theorem umin_at_1a : fetchRel u32MinCode 0x1A = some (.alu .sub a1 x0 a1, 4) := by decide
theorem umin_at_1e : fetchRel u32MinCode 0x1E = some (.aluImm .xor a0 a0 0x3E, 4) := by decide
theorem umin_at_22 : fetchRel u32MinCode 0x22 = some (.alu .and a0 a0 a1, 2) := by decide
theorem umin_at_24 : fetchRel u32MinCode 0x24 = some (.aluImm .xor a0 a0 0x3E, 4) := by decide
theorem umin_at_28 : fetchRel u32MinCode 0x28 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem umin_at_2a : fetchRel u32MinCode 0x2A = some (.jalr x0 ra 0x0, 2) := by decide
theorem srev_at_0 : fetchRel sliceReverseCode 0x0 = some (.alu .add a2 a1 a0, 4) := by decide
theorem srev_at_4 : fetchRel sliceReverseCode 0x4 = some (.aluImm .srl a1 a1 0x1, 2) := by decide
theorem srev_at_6 : fetchRel sliceReverseCode 0x6 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem srev_at_8 : fetchRel sliceReverseCode 0x8 = some (.branch .beq a1 x0 0x1A, 2) := by decide
theorem srev_at_a : fetchRel sliceReverseCode 0xA = some (.load .lbu a3 a2 0x0, 4) := by decide
theorem srev_at_e : fetchRel sliceReverseCode 0xE = some (.load .lbu a4 a0 0x0, 4) := by decide
theorem srev_at_12 : fetchRel sliceReverseCode 0x12 = some (.store .sb a0 a3 0x0, 4) := by decide
theorem srev_at_16 : fetchRel sliceReverseCode 0x16 = some (.store .sb a2 a4 0x0, 4) := by decide
theorem srev_at_1a : fetchRel sliceReverseCode 0x1A = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem srev_at_1c : fetchRel sliceReverseCode 0x1C = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem srev_at_1e : fetchRel sliceReverseCode 0x1E = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem srev_at_20 : fetchRel sliceReverseCode 0x20 = some (.branch .bne a1 x0 0xFFFFFFEA, 2) := by decide
theorem srev_at_22 : fetchRel sliceReverseCode 0x22 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `u32_min`'s whole body, from 0x0 to the return at 0x2A. -/
def uminBody : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .aluImm .add a1 sp 0xF, .aluImm .xor a2 a0 0xFFFFFFFF,
   .aluImm .add a3 a0 0xFFFFFFC2, .alu .and a2 a2 a3, .aluImm .srl a2 a2 0x1F, .sb sp a2 0xF, .lbu a1 sp 0xF,
   .alu .sub a1 x0 a1, .aluImm .xor a0 a0 0x3E, .alu .and a0 a0 a1, .aluImm .xor a0 a0 0x3E,
   .aluImm .add sp sp 0x10]

section
set_option maxRecDepth 20000
theorem uminBody_end : blockEnd u32MinCode 0x0 uminBody = some 0x2A := by decide
end

theorem umin_small : ∀ k, k < 62 → aluEval .srl (aluEval .and (aluEval .xor (BitVec.ofNat 32 k) 0xFFFFFFFF)
    (aluEval .add (BitVec.ofNat 32 k) 0xFFFFFFC2)) 0x1F = 1 := by decide

/-- The top bit of `!a & (a - 62)` is set exactly when `a < 62`. -/
theorem umin_bit (a : Word) :
    aluEval .srl (aluEval .and (aluEval .xor a 0xFFFFFFFF) (aluEval .add a 0xFFFFFFC2)) 0x1F =
      if a.toNat < 62 then 1 else 0 := by
  by_cases h : a.toNat < 62
  · rw [ite_eq_left h]
    have e := (ofNat_toNat_self a).symm
    rw [e]; exact umin_small _ h
  · rw [ite_eq_right h]
    apply BitVec.eq_of_toNat_eq
    rw [srl_mod, show (0x1F : Word).toNat % 32 = 31 from rfl, show (0 : Word).toNat = 0 from rfl]
    have hx := xor_ones_toNat a
    have ha := a.isLt
    have hand : (aluEval .and (aluEval .xor a 0xFFFFFFFF) (aluEval .add a 0xFFFFFFC2)).toNat =
        (aluEval .xor a 0xFFFFFFFF).toNat &&& (aluEval .add a 0xFFFFFFC2).toNat := BitVec.toNat_and _ _
    have hb : (aluEval .add a 0xFFFFFFC2).toNat = (a.toNat + 4294967234) % 2 ^ 32 := by
      show (a + 0xFFFFFFC2).toNat = _
      rw [BitVec.toNat_add]; rfl
    apply Nat.div_eq_of_lt
    rw [hand]
    by_cases hh : a.toNat < 2 ^ 31
    · exact Nat.lt_of_le_of_lt Nat.and_le_right (by rw [hb]; omega)
    · exact Nat.lt_of_le_of_lt Nat.and_le_left (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `u32_min (.169)`**: `a` when it is below 62, else 62. It
writes the byte below `sp`. -/
theorem u32Min_correct (m : Machine) {base retAddr a : Word} (hc : CodeIn m.mem base u32MinCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = a) (hsep : Sep (reg m sp + 0xFFFFFFFF) 1 base u32MinCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if a.toNat < 62 then a else 62) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFF) 1 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have e : reg m sp + 0xFFFFFFF0 + 0xF = reg m sp + 0xFFFFFFFF := by rw [BitVec.add_assoc]; rfl
  have hok : BlockOk base u32MinCode.length uminBody (m.mem, reg m) := by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, uminBody, upd_app, ↓reduceIte, and_true, true_and, ev_add]
    rw [e]; exact hsep
  obtain ⟨m1, c1, u1⟩ := St.block uminBody s0 hc uminBody_end hok
  have hc1 := hc.runBlock uminBody hok
  simp only [runBlock, BInstr.run, uminBody] at u1 hc1
  obtain ⟨m2, d2, pc2, mem2, regs2⟩ := u1.jalr hc1 umin_at_2a
  refine ⟨m2, c1.trans (.single d2), ?_, ?_, fun r h0' h1' h2' h3' => ?_, fun x hx => ?_⟩
  · rw [pc2]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [regs2]; simp +decide only [upd_app, ↓reduceIte]
    simp only [memStore8, ite_true, ha0]
    rw [umin_bit a]
    by_cases h : a.toNat < 62
    · rw [ite_eq_left h, ite_eq_left h]
      show ((a ^^^ 0x3E) &&& (0 - ((1 : Word).extractLsb' 0 8).zeroExtend 32)) ^^^ 0x3E = a
      rw [show (0 : Word) - ((1 : Word).extractLsb' 0 8).zeroExtend 32 = 0xFFFFFFFF by decide, and_ones,
        BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · rw [ite_eq_right h, ite_eq_right h]
      show ((a ^^^ 0x3E) &&& (0 - ((0 : Word).extractLsb' 0 8).zeroExtend 32)) ^^^ 0x3E = 0x3E
      rw [show (0 : Word) - ((0 : Word).extractLsb' 0 8).zeroExtend 32 = 0 by decide,
        show (a ^^^ 0x3E) &&& (0 : Word) = 0 from BitVec.and_zero]
      exact BitVec.zero_xor
  · rw [regs2]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    by_cases hs : r = sp
    · subst hs; simp +decide only [upd_app, ↓reduceIte]
      rw [ev_add, ev_add, BitVec.add_assoc, show (0xFFFFFFF0 : Word) + 0x10 = 0 by decide, add_lit_zero]
    simp only [upd_app, h0, hs, h0', h1', h2', h3', ite_false]
  · rw [mem2]; simp +decide only [upd_app, ↓reduceIte, ev_add]
    rw [e]; exact memStore8_ne fun ex => hx.point (i := 0) (j := 0) (by decide) (by decide) (by
      rw [add_ofNat_zero, add_ofNat_zero]; exact ex.symm)

/-- One swap of `<[u8]>::reverse`: bytes `k` and `n - 1 - k` of the `n` at
`p`. -/
def revSwap (M : Word → BitVec 8) (p : Word) (n k : Nat) : Word → BitVec 8 :=
  memStore8 (memStore8 M (p + BitVec.ofNat 32 k) (M (p + BitVec.ofNat 32 (n - 1 - k))))
    (p + BitVec.ofNat 32 (n - 1 - k)) (M (p + BitVec.ofNat 32 k))

/-- The first `k` swaps of `<[u8]>::reverse`. -/
def revIter (M : Word → BitVec 8) (p : Word) (n : Nat) : Nat → Word → BitVec 8
  | 0 => M
  | k + 1 => revSwap (revIter M p n k) p n k

theorem ofNat_eq_of_lt {p : Word} {c d : Nat} (hc : c < 2 ^ 32) (hd : d < 2 ^ 32)
    (h : p + BitVec.ofNat 32 c = p + BitVec.ofNat 32 d) : c = d := by
  by_cases e : c = d
  · exact e
  · exact absurd h (add_ofNat_ne p hc hd e)

/-- After `k` swaps, the first `k` bytes and the last `k` hold the far end's,
and the rest are as they were. -/
theorem revIter_get {M : Word → BitVec 8} {p : Word} {n : Nat} (hn : n < 2 ^ 32) :
    ∀ k, 2 * k ≤ n → ∀ j, j < n → revIter M p n k (p + BitVec.ofNat 32 j) =
      if j < k ∨ n - k ≤ j then M (p + BitVec.ofNat 32 (n - 1 - j)) else M (p + BitVec.ofNat 32 j)
  | 0, _, j, hj => by
    simp only [revIter]
    rw [ite_eq_right (fun h => h.elim (fun h => absurd h (Nat.not_lt_zero j)) (fun h => by omega))]
  | k + 1, hk, j, hj => by
    have ih := revIter_get (M := M) (p := p) hn k (by omega)
    simp only [revIter, revSwap]
    by_cases h1 : j = n - 1 - k
    · subst h1
      rw [memStore8_same, ih k (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        show n - 1 - (n - 1 - k) = k by omega]
    · rw [memStore8_ne (add_ofNat_ne p (by omega) (by omega) h1)]
      by_cases h2 : j = k
      · subst h2
        rw [memStore8_same, ih (n - 1 - j) (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [memStore8_ne (add_ofNat_ne p (by omega) (by omega) h2), ih j hj]
        by_cases h3 : j < k ∨ n - k ≤ j
        · rw [ite_eq_left h3, ite_eq_left (h3.elim (fun h => .inl (by omega)) (fun h => .inr (by omega)))]
        · rw [ite_eq_right h3, ite_eq_right (fun h => h3 (h.elim (fun h => .inl (by omega)) (fun h => .inr (by omega))))]

/-- Bytes outside the `n` at `p` never change. -/
theorem revIter_out {M : Word → BitVec 8} {p x : Word} {n : Nat} (hx : Sep p n x 1) :
    ∀ k, 2 * k ≤ n → revIter M p n k x = M x
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [revIter, revSwap]
    rw [memStore8_ne (fun e => hx (n - 1 - k) (by omega) 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => hx k (by omega) 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)),
      revIter_out hx k (by omega)]

/-- All `n / 2` swaps reverse the bytes. -/
theorem revIter_rev {M : Word → BitVec 8} {p : Word} {n : Nat} (hn : n < 2 ^ 32) :
    ∀ j, j < n → revIter M p n (n / 2) (p + BitVec.ofNat 32 j) = M (p + BitVec.ofNat 32 (n - 1 - j)) := by
  intro j hj
  rw [revIter_get hn (n / 2) (by omega) j hj]
  by_cases h : j < n / 2 ∨ n - n / 2 ≤ j
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, show n - 1 - j = j by omega]

/-- `<[u8]>::reverse`'s loop body, from 0xA to the branch at 0x20. -/
def srevBody : List BInstr :=
  [.lbu a3 a2 0x0, .lbu a4 a0 0x0, .sb a0 a3 0x0, .sb a2 a4 0x0, .aluImm .add a2 a2 0xFFFFFFFF,
   .aluImm .add a0 a0 0x1, .aluImm .add a1 a1 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem srevBody_end : blockEnd sliceReverseCode 0xA srevBody = some 0x20 := by decide
theorem srevPre_end : blockEnd sliceReverseCode 0x0 [.alu .add a2 a1 a0, .aluImm .srl a1 a1 0x1,
    .aluImm .add a2 a2 0xFFFFFFFF] = some 0x8 := by decide
end

theorem dec_one {j : Nat} (b : Word) : b + BitVec.ofNat 32 (j + 1) + 0xFFFFFFFF = b + BitVec.ofNat 32 j := by
  have e : BitVec.ofNat 32 (j + 1) + (0xFFFFFFFF : Word) = BitVec.ofNat 32 j := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  rw [BitVec.add_assoc, e]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `<[u8]>::reverse`**: it reverses the `n` bytes at `p`,
so byte `i` ends up holding byte `n - 1 - i`, and changes no other memory. -/
theorem sliceReverse_correct (m : Machine) {base retAddr p : Word} {n : Nat}
    (hc : CodeIn m.mem base sliceReverseCode) (hpc : m.pc = base) (ha0 : reg m a0 = p)
    (ha1 : reg m a1 = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) (hpn : p.toNat + n ≤ 2 ^ 32)
    (hsep : Sep p n base sliceReverseCode.length) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (∀ i, i < n → m'.mem (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 (n - 1 - i))) ∧
      (∀ x, Sep p n x 1 → m'.mem x = m.mem x) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hcI : ∀ k, 2 * k ≤ n → CodeIn (revIter m.mem p n k) base sliceReverseCode := fun k hk i hi => by
    rw [revIter_out (hsep.subR (c := i) (l := 1) (by omega)) k hk]; exact hc i hi
  -- returning from 0x22 with the first `n / 2` swaps done
  have ret : ∀ {n1 : Machine}, St (revIter m.mem p n (n / 2)) base n1 0x22 (reg n1) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧
        (∀ i, i < n → m'.mem (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 (n - 1 - i))) ∧
        (∀ x, Sep p n x 1 → m'.mem x = m.mem x) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) := by
    intro n1 s hk
    obtain ⟨n2, d2, pc2, mem2, regs2⟩ := s.jalr (hcI (n / 2) (by omega)) srev_at_22
    refine ⟨n2, .single d2, ?_, fun i hi => ?_, fun x hx => ?_, fun r h0 h1 h2 h3 h4 => ?_⟩
    · rw [pc2, hk ra (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero, hra, hret]
    · rw [mem2]; exact revIter_rev hn i hi
    · rw [mem2]; exact revIter_out hx _ (by omega)
    · rw [regs2]; exact hk r h0 h1 h2 h3 h4
  -- the loop, from 0xA with `k` swaps done and `r` left
  have loop : ∀ r k, k + r = n / 2 → 0 < r → ∀ {n1 : Machine}, St (revIter m.mem p n k) base n1 0xA (reg n1) →
      reg n1 a0 = p + BitVec.ofNat 32 k → reg n1 a2 = p + BitVec.ofNat 32 (n - 1 - k) →
      reg n1 a1 = BitVec.ofNat 32 r →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n1 r = reg m r) →
      ∃ n', Steps n1 n' ∧ St (revIter m.mem p n (n / 2)) base n' 0x22 (reg n') ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n' r = reg m r) := by
    intro r
    induction r with
    | zero => intro k _ h; exact absurd h (Nat.lt_irrefl 0)
    | succ r ih =>
      intro k hkr _ n1 s r0 r2 r1 hk
      have hc' := hcI k (by omega)
      have hok : BlockOk base sliceReverseCode.length srevBody (revIter m.mem p n k, reg n1) := by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, srevBody, upd_app, ↓reduceIte, and_true, true_and]
        rw [r0, r2, add_lit_zero, add_lit_zero]
        exact ⟨hsep.sub (c := k) (l := 1) (by omega), hsep.sub (c := n - 1 - k) (l := 1) (by omega)⟩
      obtain ⟨n2, c2, u2⟩ := St.block srevBody s hc' srevBody_end hok
      simp only [runBlock, BInstr.run, srevBody] at u2
      have u2' : St (revIter m.mem p n (k + 1)) base n2 0x20 (reg n2) := ⟨u2.pc, by
        rw [u2.mem]; simp +decide only [upd_app, ↓reduceIte]
        rw [r0, r2, add_lit_zero, add_lit_zero, tlv_zext, tlv_zext]; rfl, fun _ => rfl⟩
      have g2 : ∀ q, reg n2 q = _ := u2.regs
      have keep2 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg n2 q = reg m q :=
        fun q h0' h1' h2' h3' h4' => by
          rw [g2]
          by_cases h0 : q.val = 0
          · have : q = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h1', h2', h3', h4', ite_false]; exact hk q h0' h1' h2' h3' h4'
      have v1 : reg n2 a1 = BitVec.ofNat 32 r := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
        omega
      by_cases hr0 : r = 0
      · subst hr0
        obtain ⟨n3, d3, u3⟩ := u2'.notTaken (hcI (k + 1) (by omega)) 0x22 srev_at_20 (by decide) (by
          rw [v1, u2'.zero]; decide)
        refine ⟨n3, c2.trans (.single d3), ?_, fun q h0' h1' h2' h3' h4' => by rw [u3.regs]; exact keep2 q h0' h1' h2' h3' h4'⟩
        rw [show n / 2 = k + 1 by omega]; exact u3.self
      · obtain ⟨n3, d3, u3⟩ := u2'.taken (hcI (k + 1) (by omega)) 0xA srev_at_20 (by decide) (by
          rw [v1, u2'.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
          have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this; change _ = 0 at this; omega)
        obtain ⟨n', c', h1, h2⟩ := ih (k + 1) (by omega) (by omega) u3.self
          (by rw [u3.regs, g2]; simp +decide only [upd_app, ↓reduceIte]
              rw [r0, ev_add, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc])
          (by rw [u3.regs, g2]; simp +decide only [upd_app, ↓reduceIte]
              rw [r2, ev_add, show n - 1 - k = (n - 1 - (k + 1)) + 1 by omega, dec_one])
          (by rw [u3.regs, v1])
          (fun q h0' h1' h2' h3' h4' => by rw [u3.regs]; exact keep2 q h0' h1' h2' h3' h4')
        exact ⟨n', c2.trans (.cons d3 c'), h1, h2⟩
  obtain ⟨n1, c1, u1⟩ := St.block _ s0 hc srevPre_end (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have v1 : reg n1 a1 = BitVec.ofNat 32 (n / 2) := by
    rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1]
    apply BitVec.eq_of_toNat_eq
    rw [srl_mod, show (1 : Word).toNat % 32 = 1 from rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
  have keep1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg n1 q = reg m q :=
    fun q h0' h1' h2' h3' h4' => by
      rw [g1]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h1', h2', ite_false]
  by_cases hn2 : n / 2 = 0
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x22 srev_at_8 (by decide) (by rw [v1, hn2, u1.self.zero]; decide)
    have u2' : St (revIter m.mem p n (n / 2)) base n2 0x22 (reg n2) := ⟨u2.pc, by rw [u2.mem, hn2]; rfl, fun _ => rfl⟩
    obtain ⟨m', c', h1, h2, h3, h4⟩ := ret u2' (fun q h0' h1' h2' h3' h4' => by rw [u2.regs]; exact keep1 q h0' h1' h2' h3' h4')
    exact ⟨m', c1.trans (.cons d2 c'), h1, h2, h3, h4⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0xA srev_at_8 (by decide) (by
      rw [v1, u1.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this; change _ = 0 at this; omega)
    obtain ⟨n3, c3, s3, k3⟩ := loop (n / 2) 0 (by omega) (by omega) ⟨u2.pc, u2.mem, fun _ => rfl⟩
      (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, add_ofNat_zero])
      (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]
          rw [ha0, ha1, ev_add, ev_add, BitVec.add_comm (BitVec.ofNat 32 n) p, Nat.sub_zero]
          have := dec_one (j := n - 1) p; rwa [show n - 1 + 1 = n by omega] at this)
      (by rw [u2.regs, v1]) (fun q h0' h1' h2' h3' h4' => by rw [u2.regs]; exact keep1 q h0' h1' h2' h3' h4')
    obtain ⟨m', c', h1, h2, h3, h4⟩ := ret s3 k3
    exact ⟨m', c1.trans (.cons d2 (c3.trans c')), h1, h2, h3, h4⟩

end C3.RV32
