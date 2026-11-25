import C3BootProofs.Proofs.AcceptBundleSegs

/-!
# `boot_main`'s first closure: the bundle stage

From 0x1816 to the call to `sigstore::verify` at 0x1A46: move the trust root
to `sp + 0x1870`, read the bundle part with a `Reader` at `sp + 0xDD0`
(`Reader::magic`, `Reader::version_1`, and `bundle::field` six times), and
lay the `Bundle` out at `sp + 0x1320` for `sigstore::verify`, with the
image's digest at `sp + 0x108`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-! ## The `Bundle` and the arguments of `sigstore::verify` -/

/-- From 0x19B4 to 0x1A42: lay the `Bundle` out at `sp + 0x1320`, with the
log index's bytes joined into two words, and set the arguments. -/
def acbF : List BInstr :=
  [.aluImm .sll 19 19 0x8, .lw a1 sp 0x18, .aluImm .sll a1 a1 0x10, .lw a2 sp 0x14, .aluImm .sll a2 a2 0x18,
   .lw a3 sp 0x30, .alu .or a3 19 a3, .alu .or a1 a1 a2, .alu .or a1 a1 a3, .lw a2 sp 0x1C,
   .aluImm .sll a2 a2 0x8, .lw a3 sp 0x2C, .aluImm .sll a3 a3 0x10, .lw a4 sp 0x28, .aluImm .sll a4 a4 0x18,
   .alu .or a2 a2 9, .alu .or a3 a3 a4, .alu .or a2 a2 a3, .lw a3 sp 0x354, .aluImm .srl a4 23 0x8,
   .aluImm .srl a5 23 0x10, .aluImm .srl 9 23 0x18, .lui a6 0x1000, .aluImm .add a6 a6 0x310, .alu .add 8 sp a6,
   .sw 8 26 0x10, .sb 8 23 0x14, .sb 8 a4 0x15, .sb 8 a5 0x16, .sb 8 9 0x17, .lw a4 sp 0x38, .sw 8 a4 0x18,
   .lw a4 sp 0x34, .sw 8 a4 0x1C, .sw 8 18 0x20, .sw 8 22 0x24, .sw 8 20 0x28, .sw 8 24 0x2C, .sw 8 a0 0x30,
   .sw 8 a3 0x34, .sw 8 a2 0x38, .sw 8 a1 0x3C, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x5D1,
   .lui a1 0x1000, .aluImm .add a1 a1 0x320, .alu .add a1 a1 sp, .lui a2 0x2000,
   .aluImm .add a2 a2 0xFFFFF870, .alu .add a2 a2 sp, .aluImm .add a3 sp 0x108]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem acbF_end : blockEnd bootMainClosure0Code 0x19B4 acbF = some 0x1A42 := by decide

theorem acb_aadd (a b : Word) : aluEval .add a b = a + b := rfl

theorem acb_sb4 (M : Word → BitVec 8) (B v : Word) (c c1 c2 c3 : Nat) (h1 : c1 = c + 1) (h2 : c2 = c + 2)
    (h3 : c3 = c + 3) :
    memStore8 (memStore8 (memStore8 (memStore8 M (B + BitVec.ofNat 32 c) (v.extractLsb' 0 8))
      (B + BitVec.ofNat 32 c1) ((aluEval .srl v 0x8).extractLsb' 0 8))
      (B + BitVec.ofNat 32 c2) ((aluEval .srl v 0x10).extractLsb' 0 8))
      (B + BitVec.ofNat 32 c3) ((aluEval .srl v 0x18).extractLsb' 0 8) =
      memStore32 M (B + BitVec.ofNat 32 c) v := by
  subst h1 h2 h3
  have e : ∀ j, B + BitVec.ofNat 32 c + BitVec.ofNat 32 j = B + BitVec.ofNat 32 (c + j) := add_ofNat_assoc B c
  have sh : ∀ k : Nat, (v >>> k).extractLsb' 0 8 = v.extractLsb' k 8 := fun k => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero]
  simp only [memStore32, aluEval, sh]
  rw [← e 1, ← e 2, ← e 3]
  rfl

/-- The `Bundle`'s slots. -/
def acbBd : List (Nat × Nat) := [(0x4D70, 0x30)]

theorem acb_fs32 {M : Word → BitVec 8} {B v x : Word} {c : Nat} (hx : AcbOut acbBd B x) (h1 : 0x4D70 ≤ c)
    (h2 : c + 4 ≤ 0x4DA0) : memStore32 M (B + BitVec.ofNat 32 c) v x = M x :=
  memStore32_get_sep (acb_sep hx (p := (0x4D70, 0x30)) (List.mem_singleton_self _) h1 h2)

theorem acb_fs8 {M : Word → BitVec 8} {B x : Word} {v : BitVec 8} {c : Nat} (hx : AcbOut acbBd B x)
    (h1 : 0x4D70 ≤ c) (h2 : c + 1 ≤ 0x4DA0) : memStore8 M (B + BitVec.ofNat 32 c) v x = M x :=
  memStore8_ne (acb_ne1 (acb_sep hx (p := (0x4D70, 0x30)) (List.mem_singleton_self _) h1 h2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- From 0x19B4 to the call to `sigstore::verify` at 0x1A46. -/
theorem acb_seg6 {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) (s : St n.mem AC n 0x19B4 (reg n))
    {p1 w1 p2 w2 p4 w4 p5 w5 p6 w6 : Word} {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (r26 : reg n 26 = p1) (r23 : reg n 23 = w1) (h38 : memLoad32 n.mem (acSlot B 0x38) = p2)
    (h34 : memLoad32 n.mem (acSlot B 0x34) = w2) (r18 : reg n 18 = p4) (r22 : reg n 22 = w4)
    (r20 : reg n 20 = p5) (r24 : reg n 24 = w5) (ra0 : reg n a0 = p6)
    (h354 : memLoad32 n.mem (acSlot B 0x354) = w6) (r9 : reg n 9 = b0.zeroExtend 32)
    (h1C : memLoad32 n.mem (acSlot B 0x1C) = b1.zeroExtend 32)
    (h2C : memLoad32 n.mem (acSlot B 0x2C) = b2.zeroExtend 32)
    (h28 : memLoad32 n.mem (acSlot B 0x28) = b3.zeroExtend 32)
    (h30 : memLoad32 n.mem (acSlot B 0x30) = b4.zeroExtend 32) (r19 : reg n 19 = b5.zeroExtend 32)
    (h18 : memLoad32 n.mem (acSlot B 0x18) = b6.zeroExtend 32)
    (h14 : memLoad32 n.mem (acSlot B 0x14) = b7.zeroExtend 32) :
    ∃ n1, Steps n n1 ∧ AcbK B n0 n1 ∧ n1.pc = AC + BitVec.ofNat 32 0x1A46 ∧
      memLoad32 n1.mem (acSlot B 0x1320) = p1 ∧ memLoad32 n1.mem (acSlot B 0x1324) = w1 ∧
      memLoad32 n1.mem (acSlot B 0x1328) = p2 ∧ memLoad32 n1.mem (acSlot B 0x132C) = w2 ∧
      memLoad32 n1.mem (acSlot B 0x1330) = p4 ∧ memLoad32 n1.mem (acSlot B 0x1334) = w4 ∧
      memLoad32 n1.mem (acSlot B 0x1338) = p5 ∧ memLoad32 n1.mem (acSlot B 0x133C) = w5 ∧
      memLoad32 n1.mem (acSlot B 0x1340) = p6 ∧ memLoad32 n1.mem (acSlot B 0x1344) = w6 ∧
      (memLoad32 n1.mem (acSlot B 0x1348)).toNat = le32 b0.toNat b1.toNat b2.toNat b3.toNat ∧
      (memLoad32 n1.mem (acSlot B 0x134C)).toNat = le32 b4.toNat b5.toNat b6.toNat b7.toNat ∧
      reg n1 a0 = acSlot B 0xDD0 ∧ reg n1 a1 = acSlot B 0x1320 ∧ reg n1 a2 = acSlot B 0x1870 ∧
      reg n1 a3 = acSlot B 0x108 ∧ reg n1 ra = AC + BitVec.ofNat 32 0x1A42 + 0xC000 ∧
      ∀ x, AcbOut acbBd B x → n1.mem x = n.mem x := by
  have F := G.Y.fr
  have hz := s.zero
  have rsp : reg n sp = B + BitVec.ofNat 32 0x3A50 := K.sp
  obtain ⟨n1, c1, u1⟩ := s.block acbF (G.code K) acbF_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acbF]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]
    simp (disch := decide) only [acb_aadd, Dq.frame_lit, BitVec.reduceAdd, BitVec.reduceToNat, Nat.reduceAdd]
    repeat' apply And.intro
    acb_ok)
  simp only [acSlot, Nat.reduceAdd] at h38 h34 h354 h1C h2C h28 h30 h18 h14
  have m1 := u1.mem
  simp only [runBlock, BInstr.run, acbF] at m1; simp +decide only [upd, ↓reduceIte] at m1
  rw [rsp] at m1
  simp (disch := decide) only [acb_aadd, Dq.frame_lit, BitVec.reduceAdd, BitVec.reduceToNat, Nat.reduceAdd,
    acb_lst, acb_lsb, r26, r23, r18, r22, r20, r24, ra0, r9, r19, h38, h34, h354, h1C, h2C, h28, h30, h18,
    h14] at m1
  simp (disch := decide) only [acb_sb4] at m1
  have g : ∀ q, reg n1 q = (runBlock acbF (n.mem, reg n)).2 q := fun q => by rw [u1.regs]
  have s1 : St n1.mem AC n1 0x1A42 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have fr : ∀ x, AcbOut acbBd B x → n1.mem x = n.mem x := fun x hx => by
    rw [m1]; simp (disch := first | assumption | decide) only [acb_fs32]
  have rk : ∀ x : Fin 32, x.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 16, 19] → reg n1 x = reg n x := fun x hx => by
    rw [g, runBlock_reg _ _ _ x hz (by simp only [acbF]; revert hx; revert x; decide)]
  have K1 : AcbK B n0 n1 := ⟨by rw [rk sp (by decide)]; exact K.sp, by rw [rk 3 (by decide)]; exact K.gp,
    by rw [rk 4 (by decide)]; exact K.tp, fun x hx => (fr x (acb_mono (by decide) hx)).trans (K.keep x hx)⟩
  obtain ⟨m2, c2, s2⟩ := s1.auipc (off' := 0x1A46) (G.code K1) ac_at_1a42 (by decide)
  have z1 := s1.zero
  have rk2 : ∀ x : Fin 32, x ≠ ra → reg m2 x = reg n1 x := fun x hx => by rw [s2.regs, updz z1 hx]
  have K2 : AcbK B n0 m2 := K1.regs (l := [1]) s2.mem (fun x hx => rk2 x (acb_ne hx))
  have ld : ∀ (c : Nat) (u : Word), memLoad32 n1.mem (B + BitVec.ofNat 32 (0x3A50 + c)) = u →
      memLoad32 m2.mem (acSlot B c) = u := fun c u h => by rw [s2.mem]; exact h
  have rr : ∀ (x : Fin 32) (u : Word), x ≠ ra → reg n1 x = u → reg m2 x = u := fun x u hx h => by
    rw [rk2 x hx]; exact h
  refine ⟨m2, c1.trans (.cons c2 (.refl _)), K2, s2.pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun x hx => by rw [s2.mem]; exact fr x hx⟩
  any_goals (apply ld; rw [m1]
             simp (disch := decide) only [Nat.reduceAdd, acb_lst, memLoad32_store32_same]; done)
  · rw [s2.mem, ← le4_B]; congr 1; rw [m1]
    simp (disch := decide) only [acSlot, Nat.reduceAdd, acb_lst, memLoad32_store32_same]
  · rw [s2.mem, ← le4_A]; congr 1; rw [m1]
    simp (disch := decide) only [acSlot, Nat.reduceAdd, memLoad32_store32_same]
  all_goals first
    | (rw [s2.regs]; simp +decide only [upd, ↓reduceIte]; done)
    | (apply rr _ _ (by decide); rw [g]; simp only [runBlock, BInstr.run, acbF]
       simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp]
       simp (disch := decide) only [acSlot, acb_cm, Dq.frame_lit, BitVec.reduceAdd, BitVec.reduceToNat,
         Nat.reduceAdd])

end C3.RV32.Ac
