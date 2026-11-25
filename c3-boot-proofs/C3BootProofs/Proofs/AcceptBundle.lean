import C3BootProofs.Proofs.AcceptBundleSteps

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

/-- A block of register steps that keeps `sp`, `gp`, and `tp`. -/
theorem acb_blk {B : Word} {n0 n : Machine} {o o' : Nat} (K : AcbK B n0 n) (s : St n.mem AC n o (reg n))
    (C : CodeIn n.mem AC bootMainClosure0Code) (is : List BInstr)
    (hend : blockEnd bootMainClosure0Code o is = some o')
    (hok : BlockOk AC bootMainClosure0Code.length is (n.mem, reg n))
    (hm : (runBlock is (n.mem, reg n)).1 = n.mem)
    (hs : ∀ x ∈ is.filterMap BInstr.dst, x.val ∉ [0, 2, 3, 4]) :
    ∃ n1, Steps n n1 ∧ AcbK B n0 n1 ∧ St n1.mem AC n1 o' (reg n1) ∧ n1.mem = n.mem ∧
      (∀ x, reg n1 x = (runBlock is (n.mem, reg n)).2 x) ∧
      (∀ x, x ∉ is.filterMap BInstr.dst → reg n1 x = reg n x) := by
  obtain ⟨n1, c1, u1⟩ := s.block is C hend hok
  have m1 : n1.mem = n.mem := by rw [u1.mem, hm]
  have r1 : ∀ x, reg n1 x = (runBlock is (n.mem, reg n)).2 x := fun x => by rw [u1.regs]
  have k1 : ∀ x, x ∉ is.filterMap BInstr.dst → reg n1 x = reg n x := fun x hx => by
    rw [r1, runBlock_reg _ _ _ x s.zero hx]
  have aux : ∀ x : Fin 32, x.val ∉ [0, 1] ++ List.range' 5 27 → x.val ∈ [0, 2, 3, 4] := by decide
  exact ⟨n1, c1, K.regs (l := [0, 1] ++ List.range' 5 27) m1 (fun x hx => k1 x (fun h => hs x h (aux x hx))),
    ⟨u1.pc, rfl, fun _ => rfl⟩, m1, r1, k1⟩

set_option hygiene false in
/-- Evaluates a block's register, with `hz : reg n 0 = 0`. -/
macro "acb_rg" : tactic => `(tactic|
  simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, aluEval, x0, hz, BitVec.zero_add])

theorem acb_lsl {M : Word → BitVec 8} {B v : Word} {c d : Nat} (h : c + 4 ≤ d ∨ d + 4 ≤ c)
    (hc : 0x3A50 + c + 4 ≤ 2 ^ 32) (hd : 0x3A50 + d + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M (acSlot B c) v) (acSlot B d) = memLoad32 M (acSlot B d) :=
  acb_lst (by omega) hc hd

/-- The arguments of the image signature's field. -/
def acbA2 : List BInstr :=
  [.aluImm .add a0 sp 0x350, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x5D1, .aluImm .add a2 x0 0x8,
   .aluImm .add a3 x0 0x48]

set_option maxRecDepth 100000 in
theorem acbA2_end : blockEnd bootMainClosure0Code 0x18B4 acbA2 = some 0x18C4 := by decide

theorem acb_sl (B : Word) {k : Word} {c : Nat} (h : (0x3A50 : Word) + k = BitVec.ofNat 32 (0x3A50 + c)) :
    B + 0x3A50 + k = acSlot B c := by
  rw [BitVec.add_assoc, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The image signature's field, from 0x18B4 to 0x18DC: its pointer goes to
`sp + 0x38` and its length to `sp + 0x34`. -/
theorem acb_f2 {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) {q : Nat} (s : St n.mem AC n 0x18B4 (reg n))
    (R : AcbRd B Bf L q n.mem) (hq : q ≤ L) :
    AcbOr B n0 n (fun n' => St n'.mem AC n' 0x18DC (reg n') ∧
      (∀ x : Fin 32, x.val ∉ [1, 6, 10, 11, 12, 13, 14, 15] → reg n' x = reg n x) ∧
      memLoad32 n'.mem (acSlot B 0x38) = Bf + BitVec.ofNat 32 (q + 4) ∧
      memLoad32 n'.mem (acSlot B 0x34) = memLoad32 n0.mem (Bf + BitVec.ofNat 32 q) ∧
      q + 4 + (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat ≤ L ∧
      8 ≤ (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat ∧
      (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat ≤ 0x48 ∧
      AcbRd B Bf L (q + 4 + (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat) n'.mem ∧
      ∀ x, AcbOut acbFc B x → Sep (acSlot B 0x34) 8 x 1 → n'.mem x = n.mem x) := by
  have F := G.Y.fr; have hL := G.Y.hL; have hz := s.zero
  obtain ⟨n1, c1, K1, s1, m1, r1, k1⟩ := acb_blk K s (G.code K) acbA2 acbA2_end
    (by simp only [BlockOk, BInstr.ok, acbA2, and_self]) (by simp only [runBlock, BInstr.run, acbA2])
    (by decide)
  obtain ⟨n2, c2, s2, rg2, fr2, p2, l2, res⟩ := acb_fcall (lo := 8) (hi := 0x48) s1 (G.code K1) (G.env K1) G.Y
    (by rw [m1]; exact R) hq ac_at_18c4 ac_at_18c8 (by decide) (by decide) K1.sp
    (by rw [r1]; simp only [acbA2]; acb_rg; rw [K.sp]; exact acb_sl B (by decide))
    (by rw [r1]; simp only [acbA2]; acb_rg; rw [K.sp, acb_dd0]) (by rw [r1]; simp only [acbA2]; acb_rg)
    (by rw [r1]; simp only [acbA2]; acb_rg)
  have K2 : AcbK B n0 n2 := K1.call rg2 fr2
  have C2 := G.code K2
  have z2 := s2.zero
  obtain ⟨n3, e3, s3⟩ := s2.lw (off' := 0x18D0) C2 ac_at_18cc (by decide)
    (by rw [K2.sp, acb_sl B (c := 0x350) (by decide)]; exact acb_al F _ (by decide) (by decide))
  rw [K2.sp, acb_sl B (c := 0x350) (by decide)] at s3
  obtain ⟨n4, e4, s4⟩ := s3.sw (off' := 0x18D2) C2 ac_at_18d0 (by decide)
    (by rw [updz z2 (by decide), K2.sp, acb_sl B (c := 0x38) (by decide)]; exact acb_al F _ (by decide) (by decide))
  rw [updz z2 (by decide), K2.sp, acb_sl B (c := 0x38) (by decide), upd_same (by decide)] at s4
  have m4 := s4.mem
  rw [← s4.mem] at s4
  have K4 : AcbK B n0 n4 := ⟨by rw [s4.regs, updz z2 (by decide)]; exact K2.sp,
    by rw [s4.regs, updz z2 (by decide)]; exact K2.gp, by rw [s4.regs, updz z2 (by decide)]; exact K2.tp,
    fun x hx => by
      rw [m4, memStore32_get_sep (a := acSlot B 0x38) (acb_sep hx (p := (0x3A78, 0x14)) (by decide)
        (by decide) (by decide))]
      exact K2.keep x hx⟩
  have C4 := G.code K4
  rcases res with ⟨f0, f4⟩ | ⟨g1, g2, g3, g4, g5, g6⟩
  · obtain ⟨n5, e5, s5⟩ := s4.taken C4 0x1A66 ac_at_18d2 (by decide) (by rw [upd_same (by decide), f0]; rfl)
    have K5 : AcbK B n0 n5 := K4.regs (l := []) (by rw [s5.mem, s4.mem]) (fun x _ => by rw [s5.regs, s4.regs])
    refine acb_pre c1 (acb_pre c2 (acb_pre (.cons e3 (.cons e4 (.cons e5 (.refl _)))) ?_))
    refine acb_x66 K5 ⟨s5.pc, rfl, fun _ => rfl⟩ (G.code K5) ?_
    rw [s5.mem, m4, memStore32_get_sep (sep_offsets B (c := 0x3A50 + 0x38) (n := 4) (d := 0x3A50 + 0x354)
      (by decide) (by decide) (by decide))]
    exact f4
  · have hne : Bf + BitVec.ofNat 32 (q + 4) ≠ 0 := (G.Y.sv.sub (c := q + 4) (l := 0) (by omega)).pos_ne
    have hbuf : memLoad32 n.mem (Bf + BitVec.ofNat 32 q) = memLoad32 n0.mem (Bf + BitVec.ofNat 32 q) :=
      G.buf K (by unfold acBufLen; omega)
    simp only [m1, hbuf] at g1 g2 g3 g5 g6
    obtain ⟨n5, e5, s5⟩ := s4.notTaken C4 0x18D6 ac_at_18d2 (by decide) (by
      rw [upd_same (by decide), g4]; simp only [branchTaken, x0, upd_zero]; exact beq_eq_false_iff_ne.mpr hne)
    obtain ⟨n6, e6, s6⟩ := s5.lw (off' := 0x18DA) C4 ac_at_18d6 (by decide)
      (by rw [updz z2 (by decide), K2.sp, acb_sl B (c := 0x354) (by decide)]; exact acb_al F _ (by decide) (by decide))
    rw [updz z2 (by decide), K2.sp, acb_sl B (c := 0x354) (by decide)] at s6
    have w6 : memLoad32 n4.mem (acSlot B 0x354) = memLoad32 n0.mem (Bf + BitVec.ofNat 32 q) := by
      rw [m4]; simp (disch := decide) only [acb_lsl]; exact g5
    rw [w6] at s6
    obtain ⟨n7, e7, s7⟩ := s6.sw (off' := 0x18DC) C4 ac_at_18da (by decide)
      (by rw [updz (upd_zero _ _ _) (by decide), updz z2 (by decide), K2.sp, acb_sl B (c := 0x34) (by decide)]
          exact acb_al F _ (by decide) (by decide))
    rw [updz (upd_zero _ _ _) (by decide), updz z2 (by decide), K2.sp, acb_sl B (c := 0x34) (by decide),
      upd_same (by decide)] at s7
    have m7 := s7.mem
    rw [← s7.mem] at s7
    have rk : ∀ x : Fin 32, x.val ∉ [1, 6, 10, 11, 12, 13, 14, 15] → reg n7 x = reg n x := fun x hx => by
      rw [s7.regs, updz (upd_zero _ _ _) (acb_ne hx), updz z2 (acb_ne hx), rg2 x hx,
        k1 x (by simp only [acbA2]; revert hx; revert x; decide)]
    have K7 : AcbK B n0 n7 := ⟨by rw [rk sp (by decide)]; exact K.sp, by rw [rk 3 (by decide)]; exact K.gp,
      by rw [rk 4 (by decide)]; exact K.tp, fun x hx => by
        rw [m7, memStore32_get_sep (a := acSlot B 0x34) (acb_sep hx (p := (0x3A78, 0x14)) (by decide)
          (by decide) (by decide))]
        exact K4.keep x hx⟩
    refine acb_pre c1 (acb_pre c2 (acb_pre (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.refl _))))))
      (acb_ret K7 ⟨⟨s7.pc, rfl, fun _ => rfl⟩, rk, ?_, ?_, g1, g2, g3, ⟨?_, ?_, ?_⟩, ?_⟩)))
    · rw [m7]; simp (disch := decide) only [acb_lsl]; rw [m4, memLoad32_store32_same, g4]
    · rw [m7, memLoad32_store32_same]
    · rw [m7]; simp (disch := decide) only [acb_lsl]; rw [m4]; simp (disch := decide) only [acb_lsl]; exact p2
    · rw [m7]; simp (disch := decide) only [acb_lsl]; rw [m4]; simp (disch := decide) only [acb_lsl]; exact l2
    · rw [m7]; simp (disch := decide) only [acb_lsl]; rw [m4]; simp (disch := decide) only [acb_lsl]; exact g6
    · intro x hx h8
      have h38 : Sep (acSlot B 0x38) 4 x 1 := by
        have := h8.sub (c := 4) (l := 4) (by decide); rwa [acSlot, add_ofNat_assoc] at this
      rw [m7, memStore32_get_sep (acb_sub0 h8 (by decide)), m4, memStore32_get_sep h38, fr2 x hx, m1]

/-- One `lw rd sp k` from the frame slot `acSlot B c`. -/
theorem acb_lws {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) {o o' c : Nat} {k : Word} {rd : Fin 32}
    (s : St n.mem AC n o (reg n)) (hend : blockEnd bootMainClosure0Code o [.lw rd sp k] = some o')
    (hk : (0x3A50 : Word) + k = BitVec.ofNat 32 (0x3A50 + c)) (hc : 0x3A50 + c ≤ 0x5A70) (h4 : c % 4 = 0)
    (hrd : rd.val ∉ [0, 2, 3, 4]) :
    ∃ n1, Steps n n1 ∧ AcbK B n0 n1 ∧ St n1.mem AC n1 o' (reg n1) ∧ n1.mem = n.mem ∧
      reg n1 rd = memLoad32 n.mem (acSlot B c) ∧ ∀ x, x ≠ rd → reg n1 x = reg n x := by
  have hz := s.zero
  have e : reg n sp + k = acSlot B c := by rw [K.sp]; exact acb_sl B hk
  obtain ⟨n1, c1, K1, s1, m1, r1, k1⟩ := acb_blk K s (G.code K) [.lw rd sp k] hend
    (by simp only [BlockOk, BInstr.ok, and_true]; rw [e]; exact acb_al G.Y.fr _ hc (by omega))
    (by simp only [runBlock, BInstr.run])
    (by simp only [List.filterMap, BInstr.dst, List.mem_singleton]; rintro x rfl; exact hrd)
  refine ⟨n1, c1, K1, s1, m1, ?_, fun x hx => k1 x ?_⟩
  · rw [r1]; simp only [runBlock, BInstr.run]; rw [upd_same (fun h => hrd (by simp [h])), e]
  · simp only [List.filterMap, BInstr.dst, List.mem_singleton]; exact hx

/-- The leaf certificate's arguments. -/
def acbA1 : List BInstr :=
  [.aluImm .add a0 sp 0x350, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x5D1, .aluImm .add a2 x0 0x1,
   .lui a3 0x1000]

set_option maxRecDepth 100000 in
theorem acbA1_end : blockEnd bootMainClosure0Code 0x1892 acbA1 = some 0x18A0 := by decide

set_option maxRecDepth 100000 in
theorem acb_lw18b0 : blockEnd bootMainClosure0Code 0x18B0 [.lw 23 sp 0x354] = some 0x18B4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The leaf certificate and the image signature, from 0x1892 to 0x18DC. -/
theorem acb_s1 {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L l1 l2 : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) (s : St n.mem AC n 0x1892 (reg n))
    (R : AcbRd B Bf L 6 n.mem) (h6 : 6 ≤ L)
    (hl1 : (memLoad32 n0.mem (Bf + BitVec.ofNat 32 6)).toNat = l1)
    (hl2 : (memLoad32 n0.mem (Bf + BitVec.ofNat 32 (10 + l1))).toNat = l2) :
    AcbOr B n0 n (fun n' => St n'.mem AC n' 0x18DC (reg n') ∧ reg n' 26 = Bf + BitVec.ofNat 32 10 ∧
      (reg n' 23).toNat = l1 ∧ memLoad32 n'.mem (acSlot B 0x38) = Bf + BitVec.ofNat 32 (14 + l1) ∧
      (memLoad32 n'.mem (acSlot B 0x34)).toNat = l2 ∧ 1 ≤ l1 ∧ l1 ≤ 0x1000 ∧ 8 ≤ l2 ∧ l2 ≤ 0x48 ∧
      14 + l1 + l2 ≤ L ∧ AcbRd B Bf L (14 + l1 + l2) n'.mem) := by
  have hz := s.zero
  refine acb_bind (acb_fld (lo := 1) (hi := 0x1000) (o' := 0x18B0) G K s R h6 acbA1 acbA1_end
    (by simp only [BlockOk, BInstr.ok, acbA1, and_self]) (by simp only [runBlock, BInstr.run, acbA1])
    (by decide) (by simp only [acbA1]; acb_rg; rw [K.sp]; exact acb_sl B (by decide))
    (by simp only [acbA1]; acb_rg; rw [K.sp, acb_dd0]) (by simp only [acbA1]; acb_rg)
    (by simp only [acbA1]; acb_rg) ac_at_18a0 ac_at_18a4 (by decide) (by decide) ac_at_18a8 (by decide)
    ac_at_18ac (by decide) (by decide) (by decide)) ?_
  rintro n1 K1 ⟨s1, -, r26, w1, b1, lo1, hi1, R1, -⟩
  rw [hl1] at b1 lo1 hi1 R1
  obtain ⟨n2, c2, K2, s2, m2, r2, k2⟩ := acb_lws G K1 s1 acb_lw18b0 (c := 0x354) (by decide) (by decide)
    (by decide) (by decide)
  have R2 : AcbRd B Bf L (6 + 4 + l1) n2.mem := by rw [m2]; exact R1
  refine acb_pre c2 (acb_map (acb_f2 G K2 s2 R2 (by omega)) ?_)
  rintro n3 ⟨s3, rk3, p3, w3, b3, lo3, hi3, R3, -⟩
  have e10 : 6 + 4 + l1 = 10 + l1 := by omega
  rw [e10, hl2] at b3 lo3 hi3 R3
  rw [e10] at p3
  refine ⟨s3, ?_, ?_, ?_, ?_, by simpa using lo1, by simpa using hi1, by simpa using lo3, by simpa using hi3,
    by omega, ?_⟩
  · rw [rk3 26 (by decide), k2 26 (by decide)]; exact r26
  · rw [rk3 23 (by decide), r2, w1, hl1]
  · rw [p3]; congr 2; omega
  · rw [w3, hl2]
  · rw [show 14 + l1 + l2 = 10 + l1 + 4 + l2 by omega]; exact R3

/-- The log index's arguments, and the 8 it checks the length against. -/
def acbA3 : List BInstr :=
  [.aluImm .add a0 sp 0x350, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x5D1, .aluImm .add a2 x0 0x8,
   .aluImm .add a3 x0 0x8, .aluImm .add 18 x0 0x8]

set_option maxRecDepth 100000 in
theorem acbA3_end : blockEnd bootMainClosure0Code 0x18DC acbA3 = some 0x18EC := by decide

set_option maxRecDepth 100000 in
theorem acb_lw18fc : blockEnd bootMainClosure0Code 0x18FC [.lw a1 sp 0x354] = some 0x1900 := by decide

set_option maxRecDepth 100000 in
theorem acb_li1900 : blockEnd bootMainClosure0Code 0x1900 [.aluImm .add 8 x0 0x5] = some 0x1902 := by decide

theorem acb_w8 {w : Word} (h1 : (8 : Word).toNat ≤ w.toNat) (h2 : w.toNat ≤ (8 : Word).toNat) : w = 8 :=
  BitVec.eq_of_toNat_eq (Nat.le_antisymm h2 h1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The log index's field, from 0x18DC to 0x1906: its pointer in `a0`. -/
theorem acb_s2 {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L q : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) (s : St n.mem AC n 0x18DC (reg n))
    (R : AcbRd B Bf L q n.mem) (hq : q ≤ L) :
    AcbOr B n0 n (fun n' => St n'.mem AC n' 0x1906 (reg n') ∧ reg n' a0 = Bf + BitVec.ofNat 32 (q + 4) ∧
      reg n' 8 = 5 ∧
      (∀ x : Fin 32, x.val ∉ [1, 6, 8, 10, 11, 12, 13, 14, 15, 18] → reg n' x = reg n x) ∧
      (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat = 8 ∧ q + 12 ≤ L ∧ AcbRd B Bf L (q + 12) n'.mem ∧
      ∀ x, AcbOut acbFc B x → n'.mem x = n.mem x) := by
  have hz := s.zero
  refine acb_bind (acb_fld (lo := 8) (hi := 8) (o' := 0x18FC) G K s R hq acbA3 acbA3_end
    (by simp only [BlockOk, BInstr.ok, acbA3, and_self]) (by simp only [runBlock, BInstr.run, acbA3])
    (by decide) (by simp only [acbA3]; acb_rg; rw [K.sp]; exact acb_sl B (by decide))
    (by simp only [acbA3]; acb_rg; rw [K.sp, acb_dd0]) (by simp only [acbA3]; acb_rg)
    (by simp only [acbA3]; acb_rg) ac_at_18ec ac_at_18f0 (by decide) (by decide) ac_at_18f4 (by decide)
    ac_at_18f8 (by decide) (by decide) (by decide)) ?_
  rintro n1 K1 ⟨s1, rk1, r10, w1, b1, lo1, hi1, R1, f1⟩
  have h8 := acb_w8 lo1 hi1
  have e8 : (8 : Word).toNat = 8 := rfl
  rw [h8, e8] at b1 R1
  have z1 := s1.zero
  obtain ⟨n2, c2, K2, s2, m2, r2, k2⟩ := acb_lws G K1 s1 acb_lw18fc (c := 0x354) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨n3, c3, K3, s3, m3, r3, k3⟩ := acb_blk K2 s2 (G.code K2) [.aluImm .add 8 x0 0x5] acb_li1900
    (by simp only [BlockOk, BInstr.ok, and_self]) (by simp only [runBlock, BInstr.run]) (by decide)
  have z2 := s2.zero
  have r18 : reg n1 18 = 8 := by
    rw [rk1 18 (by decide) (by decide)]; simp only [acbA3]; acb_rg
  obtain ⟨n4, c4, s4⟩ := s3.notTaken (G.code K3) 0x1906 ac_at_1902 (by decide) (by
    rw [k3 a1 (by decide), k3 18 (by decide), r2, k2 18 (by decide), r18, w1, h8]
    simp only [branchTaken]; decide)
  have K4 : AcbK B n0 n4 := K3.regs (l := []) (by rw [s4.mem]) (fun x _ => by rw [s4.regs])
  have aux : ∀ x : Fin 32, x.val ∉ [1, 6, 8, 10, 11, 12, 13, 14, 15, 18] →
      x.val ∉ [1, 6, 10, 11, 12, 13, 14, 15] ∧ x ≠ a0 ∧ x ≠ a1 ∧ x ≠ 8 ∧ x ∉ acbA3.filterMap BInstr.dst := by
    decide
  refine acb_pre c2 (acb_pre c3 (acb_pre (.cons c4 (.refl _)) (acb_ret K4 ⟨⟨s4.pc, rfl, fun _ => rfl⟩,
    ?_, ?_, ?_, by rw [h8]; rfl, by omega, ?_, ?_⟩)))
  · rw [s4.regs, k3 a0 (by decide), k2 a0 (by decide), r10]
  · rw [s4.regs, r3]; simp only [runBlock, BInstr.run]; acb_rg; rw [z2]; rfl
  · intro x hx
    have ⟨a, b, c, d, e⟩ := aux x hx
    rw [s4.regs, k3 x (by simp only [List.filterMap, BInstr.dst, List.mem_singleton]; exact d), k2 x c, rk1 x a b, runBlock_reg _ _ _ x hz e]
  · rw [s4.mem, m3, m2, show q + 12 = q + 4 + 8 by omega]
    exact R1
  · intro x hx; rw [s4.mem, m3, m2, f1 x hx]

/-- The log index's bytes, spilled to the frame. -/
def acbB : List BInstr :=
  [.lbu a1 a0 0x4, .sw sp a1 0x30, .lbu 19 a0 0x5, .lbu a1 a0 0x6, .sw sp a1 0x18, .lbu a1 a0 0x7,
   .sw sp a1 0x14, .lbu 9 a0 0x0, .lbu a1 a0 0x1, .sw sp a1 0x1C, .lbu a1 a0 0x2, .sw sp a1 0x2C,
   .lbu a0 a0 0x3, .sw sp a0 0x28]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem acbB_end : blockEnd bootMainClosure0Code 0x1906 acbB = some 0x1932 := by decide

/-- The frame slots of the log index's bytes. -/
def acbS : List (Nat × Nat) := [(0x3A64, 0xC), (0x3A78, 0xC)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The log index's bytes, from 0x1906 to 0x1932. -/
theorem acb_blkB {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) {P : Word} (s : St n.mem AC n 0x1906 (reg n))
    (ra0 : reg n a0 = P)
    (hP : ∀ k : Word, k.toNat < 8 → ∀ c : Nat, c + 4 ≤ 0x5A70 → Sep (B + BitVec.ofNat 32 c) 4 (P + k) 1) :
    ∃ n1, Steps n n1 ∧ AcbK B n0 n1 ∧ St n1.mem AC n1 0x1932 (reg n1) ∧
      (∀ x, AcbOut acbS B x → n1.mem x = n.mem x) ∧
      memLoad32 n1.mem (acSlot B 0x30) = (n.mem (P + 4)).zeroExtend 32 ∧
      memLoad32 n1.mem (acSlot B 0x18) = (n.mem (P + 6)).zeroExtend 32 ∧
      memLoad32 n1.mem (acSlot B 0x14) = (n.mem (P + 7)).zeroExtend 32 ∧
      memLoad32 n1.mem (acSlot B 0x1C) = (n.mem (P + 1)).zeroExtend 32 ∧
      memLoad32 n1.mem (acSlot B 0x2C) = (n.mem (P + 2)).zeroExtend 32 ∧
      memLoad32 n1.mem (acSlot B 0x28) = (n.mem (P + 3)).zeroExtend 32 ∧
      reg n1 19 = (n.mem (P + 5)).zeroExtend 32 ∧ reg n1 9 = (n.mem (P + 0)).zeroExtend 32 ∧
      ∀ x : Fin 32, x.val ∉ [9, 10, 11, 19] → reg n1 x = reg n x := by
  have F := G.Y.fr
  have hz := s.zero
  have rsp : reg n sp = B + BitVec.ofNat 32 0x3A50 := K.sp
  have rb : ∀ (M : Word → BitVec 8) (c : Nat) (u k : Word), c + 4 ≤ 0x5A70 → k.toNat < 8 →
      memStore32 M (B + BitVec.ofNat 32 c) u (P + k) = M (P + k) := fun M c u k hc hk =>
    memStore32_get_sep (hP k hk c hc)
  obtain ⟨n1, c1, u1⟩ := s.block acbB (G.code K) acbB_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acbB]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]
    simp (disch := decide) only [Dq.frame_lit, BitVec.reduceToNat, Nat.reduceAdd]
    repeat' apply And.intro
    acb_ok)
  have m1 := u1.mem
  simp only [runBlock, BInstr.run, acbB] at m1; simp +decide only [upd, ↓reduceIte] at m1
  rw [rsp, ra0] at m1
  simp (disch := decide) only [Dq.frame_lit, BitVec.reduceToNat, Nat.reduceAdd, rb] at m1
  have g : ∀ q, reg n1 q = (runBlock acbB (n.mem, reg n)).2 q := fun q => by rw [u1.regs]
  have rk : ∀ x : Fin 32, x.val ∉ [9, 10, 11, 19] → reg n1 x = reg n x := fun x hx => by
    rw [g, runBlock_reg _ _ _ x hz (by simp only [acbB]; revert hx; revert x; decide)]
  have fr : ∀ x, AcbOut acbS B x → n1.mem x = n.mem x := fun x hx => by
    rw [m1, memStore32_get_sep (acb_sep hx (p := (0x3A78, 0xC)) (c := 14968) (l := 4) (by decide) (by decide)
        (by decide)),
      memStore32_get_sep (acb_sep hx (p := (0x3A78, 0xC)) (c := 14972) (l := 4) (by decide) (by decide)
        (by decide)),
      memStore32_get_sep (acb_sep hx (p := (0x3A64, 0xC)) (c := 14956) (l := 4) (by decide) (by decide)
        (by decide)),
      memStore32_get_sep (acb_sep hx (p := (0x3A64, 0xC)) (c := 14948) (l := 4) (by decide) (by decide)
        (by decide)),
      memStore32_get_sep (acb_sep hx (p := (0x3A64, 0xC)) (c := 14952) (l := 4) (by decide) (by decide)
        (by decide)),
      memStore32_get_sep (acb_sep hx (p := (0x3A78, 0xC)) (c := 14976) (l := 4) (by decide) (by decide)
        (by decide))]
  have K1 : AcbK B n0 n1 := ⟨by rw [rk sp (by decide)]; exact K.sp, by rw [rk 3 (by decide)]; exact K.gp,
    by rw [rk 4 (by decide)]; exact K.tp, fun x hx => (fr x (acb_mono (by decide) hx)).trans (K.keep x hx)⟩
  refine ⟨n1, c1, K1, ⟨u1.pc, rfl, fun _ => rfl⟩, fr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rk⟩
  all_goals first
    | (rw [m1]; simp (disch := decide) only [acSlot, Nat.reduceAdd, acb_lst, memLoad32_store32_same]; done)
    | (rw [g]; simp only [runBlock, BInstr.run, acbB]; simp +decide only [upd, ↓reduceIte]; rw [rsp, ra0]
       simp (disch := decide) only [Dq.frame_lit, BitVec.reduceToNat, Nat.reduceAdd, rb])

end C3.RV32.Ac
