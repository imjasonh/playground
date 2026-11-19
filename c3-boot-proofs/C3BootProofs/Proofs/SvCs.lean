import C3BootProofs.Proofs.SvEd

/-!
# `sigstore::verify`: the checkpoint's signature lines

Byte tests for the signature lines' name and base64 scans.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

/-- A byte minus `' '` is zero exactly when the byte is `' '`. -/
theorem space_iff : ∀ b : BitVec 8, b.zeroExtend 32 + 0xFFFFFFE0 = 0 ↔ b = 0x20 := by decide

/-- A byte minus `'='` is zero exactly when the byte is `'='`. -/
theorem pad_iff : ∀ b : BitVec 8, b.zeroExtend 32 + 0xFFFFFFC3 = 0 ↔ b = 0x3D := by decide

theorem gl8 {b : BitVec 8} {j : Nat} (h : 8 ≤ j) : b.getLsbD j = false := BitVec.getLsbD_of_ge b j h
/-- Four bytes packed little-endian with shifts and `or`. -/
theorem pack4 (b0 b1 b2 b3 : BitVec 8) :
    (aluEval .sll (b1.zeroExtend 32) (BitVec.ofNat 32 0x8) ||| b0.zeroExtend 32) |||
      (aluEval .sll (b2.zeroExtend 32) (BitVec.ofNat 32 0x10) ||| aluEval .sll (b3.zeroExtend 32) (BitVec.ofNat 32 0x18)) =
      b3 ++ b2 ++ b1 ++ b0 := by
  simp only [aluEval]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    BitVec.toNat_ofNat, hi, decide_true, Bool.true_and]
  rw [show (8 : Nat) % 2 ^ 32 % 32 = 8 from rfl, show (16 : Nat) % 2 ^ 32 % 32 = 16 from rfl,
    show (24 : Nat) % 2 ^ 32 % 32 = 24 from rfl]
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.not_true, Bool.false_and, Bool.false_or, ↓reduceIte,
      show i < 16 from by omega, show i < 24 from by omega, Bool.or_false]
  · by_cases h16 : i < 16
    · simp only [h8, h16, decide_false, decide_true, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
        Bool.or_false, ↓reduceIte, show i < 24 from by omega, show i - 8 < 32 from by omega, show i - 8 < 8 from by omega,
        gl8 (show 8 ≤ i from by omega)]
    · by_cases h24 : i < 24
      · simp only [h8, h16, h24, decide_false, decide_true, Bool.not_false, Bool.not_true, Bool.true_and,
          Bool.false_and, Bool.or_false, Bool.false_or, ↓reduceIte, show i - 8 < 32 from by omega,
          show i - 16 < 32 from by omega, show ¬ i - 8 < 8 from by omega, show i - 16 < 8 from by omega,
          gl8 (show 8 ≤ i from by omega), gl8 (show 8 ≤ i - 8 from by omega), show i - 8 - 8 = i - 16 from by omega]
      · simp only [h8, h16, h24, decide_false, decide_true, Bool.not_false, Bool.true_and,
          Bool.false_or, Bool.or_false, ↓reduceIte, show i - 8 < 32 from by omega,
          show i - 16 < 32 from by omega, show i - 24 < 32 from by omega, show ¬ i - 8 < 8 from by omega,
          show ¬ i - 8 - 8 < 8 from by omega,
          gl8 (show 8 ≤ i from by omega), gl8 (show 8 ≤ i - 8 from by omega), gl8 (show 8 ≤ i - 16 from by omega),
          show i - 8 - 8 - 8 = i - 24 from by omega]

theorem ldb (M : Word → BitVec 8) (a : Word) :
    (memLoad32 M a).extractLsb' 0 8 = M a ∧ (memLoad32 M a).extractLsb' 8 8 = M (a + 1) ∧
    (memLoad32 M a).extractLsb' 16 8 = M (a + 2) ∧ (memLoad32 M a).extractLsb' 24 8 = M (a + 3) := by
  unfold memLoad32
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  · simp only [Nat.zero_add, hi, ↓reduceIte]
  · simp only [show ¬ (8 + i < 8) by omega, ↓reduceIte, show 8 + i - 8 = i by omega, hi]
  · simp only [show ¬ (16 + i < 8) by omega, show ¬ (16 + i - 8 < 8) by omega, ↓reduceIte,
      show 16 + i - 8 - 8 = i by omega, hi]
  · simp only [show ¬ (24 + i < 8) by omega, show ¬ (24 + i - 8 < 8) by omega, show ¬ (24 + i - 8 - 8 < 8) by omega,
      ↓reduceIte, show 24 + i - 8 - 8 - 8 = i by omega]
/-- Two words that load equal hold the same four bytes. -/
theorem mb4_of_ld {M M' : Word → BitVec 8} {a b : Word} (h : memLoad32 M a = memLoad32 M' b) :
    memBytes M a 4 = memBytes M' b 4 := by
  obtain ⟨x0, x1, x2, x3⟩ := ldb M a
  obtain ⟨y0, y1, y2, y3⟩ := ldb M' b
  rw [h] at x0 x1 x2 x3
  simp only [memBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_append,
    List.map_nil, add_ofNat_zero]
  rw [← x0, y0, show BitVec.ofNat 32 1 = 1 from rfl, show BitVec.ofNat 32 2 = 2 from rfl,
    show BitVec.ofNat 32 3 = 3 from rfl, ← x1, y1, ← x2, y2, ← x3, y3]

set_option maxHeartbeats 8000000 in
/-- **A call to `base64::decode_into`** on the `nl` bytes at offset `tc` of
the frame, with the result at offset `rc` and the output buffer of `L` bytes
at offset `oc`. -/
theorem sv_b64fF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {rc oc tc nl L : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (CK : SvCkCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BDI)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 rc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 tc)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha4 : reg n a4 = BitVec.ofNat 32 L) (hr2 : rc + 8 ≤ 0x1690) (hr3 : rc % 4 = 0) (ho2 : oc + L ≤ 0x1690)
    (ht2 : tc + nl ≤ 0x1690) (hs : rc + 8 ≤ oc ∨ oc + L ≤ rc) (hs2 : tc + nl ≤ oc ∨ oc + L ≤ tc) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(rc, 8), (oc, L)] ∧
      (∀ bs, base64Decode (memBytes M (B + 0x21A0 + BitVec.ofNat 32 tc) nl) = some bs → bs.length ≤ L →
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 rc) = 0) ∧
      ((∀ bs, base64Decode (memBytes M (B + 0x21A0 + BitVec.ofNat 32 tc) nl) = some bs → L < bs.length) →
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 rc) = 1) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have eB : MCS + 8 = BMB := by decide
  obtain ⟨n2, c2, pc2, sp2, k2, ok2, bad2, f2⟩ := base64DecodeInto_correct n1 (sp0 := B + 0x21A0)
    (by rw [mem1]; exact CK.b64) (by rw [mem1]; exact CK.cw) (by rw [mem1]; exact C.K.stub)
    (by rw [mem1, ← eB]; exact C.K.body) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [r1 a3 (by decide), ha3]) (by rw [r1 a4 (by decide), ha4])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; omega)
    (by rw [sv_at F _ (by omega)]; omega) (sv_al F (by omega) hr3) (by rw [sv_at F _ (by omega)]; omega)
    (by rw [sv_at F _ (by omega)]; omega)
    (by rw [sv_sp50, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [sv_sp50, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [sv_sp50, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) hs2 (by omega) (by omega))
    (sepS (B + 0x21A0) hs (by omega) (by omega))
  rw [mem1] at ok2 bad2 f2
  rw [sv_sp50] at f2
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x2150) 0x50 x 1 := fun x hx => by
    have := svR_lo (k := 0x50) hx (by decide) (by decide)
    rwa [sv_lo B 0x50 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    fun e he hL => ?_, fun bs hd hl => (ok2 bs hd hl).1, bad2,
    fun x hx => f2 x (hfS x hx) (svR_hi hx ho2) (svR_hi hx hr2)⟩
  have h1 := hL _ List.mem_cons_self
  have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only at h1 h2
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

end C3.RV32.Sv
