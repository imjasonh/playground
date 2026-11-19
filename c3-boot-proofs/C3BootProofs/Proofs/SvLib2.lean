import C3BootProofs.Proofs.SvCalls

/-!
# `sigstore::verify`: steps on the frame

Lemmas that the generated stages of the `sigstore::verify` proof use: where
the frame is, the saved registers, stores to the frame, and `memcpy` within
it. Offsets are from the frame's base `B + 0x21A0`, which is `sp` between
the prologue and the epilogue.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- Proves that two sums of a base address and constants are equal. -/
macro "sv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]
               <;> omega))

theorem sv_at {B : Word} (F : Fr B 0x3830) (c : Nat) (hc : c ≤ 0x1690) :
    (B + 0x21A0 + BitVec.ofNat 32 c).toNat = B.toNat + 0x21A0 + c := by
  have := F.at (0x21A0 + c) (by omega); rw [← add_ofNat_assoc] at this; exact this.trans (by omega)

theorem sv_al {B : Word} (F : Fr B 0x3830) {c : Nat} (hc : c ≤ 0x1690) (ac : c % 4 = 0) :
    (B + 0x21A0 + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  have := F.al; rw [sv_at F c hc]; omega

theorem sv_wr {B : Word} (F : Fr B 0x3830) {c n : Nat} (hc : c + n ≤ 0x1690) :
    (B + 0x21A0 + BitVec.ofNat 32 c).toNat + n < 2 ^ 32 := by
  have := F.hi; rw [sv_at F c (by omega)]; omega

theorem sv_base (B : Word) (c : Nat) : B + BitVec.ofNat 32 (0x21A0 + c) = B + 0x21A0 + BitVec.ofNat 32 c :=
  (add_ofNat_assoc B 0x21A0 c).symm

/-- A byte outside the stack is outside every part of the frame. -/
theorem svR_hi {B x : Word} {c l : Nat} (hx : SvR B x) (h : c + l ≤ 0x1690) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 c) l x 1 := by
  have := hx.sub (c := 0x1A0 + 0x21A0 + c) (l := l) (by omega)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x21A0 + c) = B + 0x21A0 + BitVec.ofNat 32 c by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl, show (0x21A0 : Word).toNat = 0x21A0 from rfl]
    omega] at this

/-- A byte outside the stack is outside the `k` bytes below the frame. -/
theorem svR_lo {B x : Word} {k : Nat} (hx : SvR B x) (hk : k ≤ 0x2340) (hk0 : 0 < k) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k)) k x 1 := by
  have := hx.sub (c := 0x1A0 + 0x21A0 - k) (l := k) (by omega)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x21A0 - k) = B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k) by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl, show (0x21A0 : Word).toNat = 0x21A0 from rfl]
    omega] at this

/-- The saved registers at the top of the frame. -/
def SvSaves (B : Word) (M : Word → BitVec 8) (v : Nat → Word) : Prop :=
  ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x382C - 4 * k)) = v k

theorem SvSaves.keep {B : Word} {M M' : Word → BitVec 8} {v : Nat → Word} {c w : Nat} (V : SvSaves B M v)
    (K : SvKeep B M M' c w) (h : c + w ≤ 0x165C) : SvSaves B M' v := fun k hk => by
  rw [← V k hk, show 0x382C - 4 * k = 0x21A0 + (0x168C - 4 * k) by omega, sv_base]
  exact memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact K _ (by omega) (by omega)

theorem SvSaves.same {B : Word} {M M' : Word → BitVec 8} {v : Nat → Word} (V : SvSaves B M v) (h : M' = M) :
    SvSaves B M' v := by rw [h]; exact V

theorem SvKeep.w32 {B : Word} {M M' : Word → BitVec 8} {c w e : Nat} (K : SvKeep B M M' c w) (he : e + 4 ≤ 0x1690)
    (h : e + 4 ≤ c ∨ c + w ≤ e) :
    memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) = memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact K _ (by omega) (by omega)

theorem SvKeep.b8 {B : Word} {M M' : Word → BitVec 8} {c w e : Nat} (K : SvKeep B M M' c w) (he : e + 1 ≤ 0x1690)
    (h : e + 1 ≤ c ∨ c + w ≤ e) : M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  K _ he (by omega)

theorem SvKeep.same {B : Word} {M M' : Word → BitVec 8} (h : M' = M) : SvKeep B M M' 0 0 :=
  fun _ _ _ => by rw [h]

theorem byte0 (A B C D : BitVec 8) : (A ++ B ++ C ++ D).extractLsb' 0 8 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  simp [hi]

theorem byte1 (A B C D : BitVec 8) : (A ++ B ++ C ++ D).extractLsb' 8 8 = C := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  simp [hi, show ¬ (8 + i < 8) by omega, show 8 + i - 8 = i by omega]

theorem byte2 (A B C D : BitVec 8) : (A ++ B ++ C ++ D).extractLsb' 16 8 = B := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  simp [hi, show ¬ (16 + i < 8) by omega, show ¬ (16 + i - 8 < 8) by omega, show 16 + i - 8 - 8 = i by omega]

theorem byte3 (A B C D : BitVec 8) : (A ++ B ++ C ++ D).extractLsb' 24 8 = A := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  simp [hi, show ¬ (24 + i < 8) by omega, show ¬ (24 + i - 8 < 8) by omega, show ¬ (24 + i - 8 - 8 < 8) by omega,
    show 24 + i - 8 - 8 - 8 = i by omega]

theorem ld_cp {M M' : Word → BitVec 8} {S : Word} {c d : Nat}
    (h : ∀ q, q < 4 → M' (S + BitVec.ofNat 32 (c + q)) = M (S + BitVec.ofNat 32 (d + q))) :
    memLoad32 M' (S + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 d) :=
  by
  rw [ld_ofNat, ld_ofNat]
  simp only [add_ofNat_assoc]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- A byte of a word. -/
theorem byte_of_ld {M : Word → BitVec 8} {a w : Word} (h : memLoad32 M a = w) :
    M a = w.extractLsb' 0 8 ∧ M (a + 1) = w.extractLsb' 8 8 ∧ M (a + 2) = w.extractLsb' 16 8 ∧
      M (a + 3) = w.extractLsb' 24 8 := by
  subst h; unfold memLoad32
  exact ⟨(byte0 ..).symm, (byte1 ..).symm, (byte2 ..).symm, (byte3 ..).symm⟩

/-- A word from its four bytes. -/
theorem ld_of_bytes {M : Word → BitVec 8} {a w : Word} (h0 : M a = w.extractLsb' 0 8)
    (h1 : M (a + 1) = w.extractLsb' 8 8) (h2 : M (a + 2) = w.extractLsb' 16 8)
    (h3 : M (a + 3) = w.extractLsb' 24 8) : memLoad32 M a = w := by
  unfold memLoad32; rw [h0, h1, h2, h3]; exact bytes_reassemble w

/-- The low byte of a byte read with `lbu`. -/
theorem lbu_low (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]; omega

/-- The machine, after a step of `sigstore::verify`: what the frame and the
code are, and the saved registers. -/
structure SvPost (B : Word) (m m' : Machine) (off' : Nat) : Prop where
  steps : Steps m m'
  st : St m'.mem SV m' off' (reg m')
  fr : ∀ x, SvR B x → m'.mem x = m.mem x
  regs : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q

theorem SvCode.fr {B : Word} {M M' : Word → BitVec 8} (C : SvCode M) (F : Fr B 0x3830)
    (h : ∀ x, SvR B x → M' x = M x) : SvCode M' :=
  C.hi fun x hx => h x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))

set_option maxHeartbeats 4000000 in
/-- `sw` to the word at offset `c` of the frame. -/
theorem sv_sw {B : Word} {m : Machine} {off off' : Nat} {rs1 rs2 : Fin 32} {o len : Word} {c : Nat}
    (F : Fr B 0x3830) (E : SvCode m.mem) (s : St m.mem SV m off (reg m))
    (hf : fetchRel sigstoreVerifyCode off = some (.store .sw rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (ha : reg m rs1 + o = B + 0x21A0 + BitVec.ofNat 32 c)
    (hc : c + 4 ≤ 0x1690) (ac : c % 4 = 0) :
    ∃ m', Steps m m' ∧ St m'.mem SV m' off' (reg m') ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧
      SvKeep B m.mem m'.mem c 4 ∧ memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 c) = reg m rs2 ∧
      ∀ q, reg m' q = reg m q := by
  obtain ⟨m1, d1, u1⟩ := s.sw E.self hf hn (by rw [ha]; exact sv_al F (by omega) ac)
  rw [ha] at u1
  exact ⟨m1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩, fun x hx => by rw [u1.mem]; exact memStore32_get_sep (svR_hi hx hc),
    fun e he1 he2 => by
      rw [u1.mem]; exact memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)),
    by rw [u1.mem, memLoad32_store32_same], fun q => u1.regs q⟩

set_option maxHeartbeats 4000000 in
/-- `sb` to the byte at offset `c` of the frame. -/
theorem sv_sb {B : Word} {m : Machine} {off off' : Nat} {rs1 rs2 : Fin 32} {o len : Word} {c : Nat}
    (_F : Fr B 0x3830) (E : SvCode m.mem) (s : St m.mem SV m off (reg m))
    (hf : fetchRel sigstoreVerifyCode off = some (.store .sb rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (ha : reg m rs1 + o = B + 0x21A0 + BitVec.ofNat 32 c)
    (hc : c + 1 ≤ 0x1690) :
    ∃ m', Steps m m' ∧ St m'.mem SV m' off' (reg m') ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧
      SvKeep B m.mem m'.mem c 1 ∧ m'.mem (B + 0x21A0 + BitVec.ofNat 32 c) = (reg m rs2).extractLsb' 0 8 ∧
      ∀ q, reg m' q = reg m q := by
  obtain ⟨m1, d1, u1⟩ := s.sb E.self hf hn
  rw [ha] at u1
  exact ⟨m1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩,
    fun x hx => by rw [u1.mem]; exact memStore8_ne (sep1_ne (svR_hi (l := 1) hx hc)),
    fun e he1 he2 => by
      rw [u1.mem]; exact memStore8_ne (sep1_ne (sepS (B + 0x21A0) (by omega) (by omega) (by omega))),
    by rw [u1.mem, memStore8_same], fun q => u1.regs q⟩

set_option maxHeartbeats 4000000 in
/-- A call to `memcpy` of `N` bytes from offset `d` of the frame to offset `c`. -/
theorem sv_mc {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c d N : Nat} (F : Fr B 0x3830)
    (E : SvCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 c)
    (ha1 : reg m a1 = B + 0x21A0 + BitVec.ofNat 32 d) (ha2 : reg m a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x1690) (hd : d + N ≤ 0x1690) (hs : c + N ≤ d ∨ d + N ≤ c) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = m.mem (B + 0x21A0 + BitVec.ofNat 32 (d + j)) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hb16 : (B + 0x21A0 + 0xFFFFFFF0).toNat = (B + 0x21A0).toNat - 16 := FS.below 16 (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x21A0 + BitVec.ofNat 32 c)
    (src := B + 0x21A0 + BitVec.ofNat 32 d) (S := B + 0x21A0) (N := N) s E.self E.K h1 h2 hb he8 hsp ha0 ha1 ha2
    ⟨E.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega), FS.mcN (by omega),
      sepS (B + 0x21A0) hs (by omega) (by omega), fA, fW, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega⟩
  have lo16 : ∀ x, SvR B x → Sep (B + 0x21A0 + 0xFFFFFFF0) 16 x 1 := fun x hx => svR_lo (k := 16) hx (by decide) (by decide)
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (lo16 x hx), copyBytes_sep (svR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x21A0) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x21A0) c j, cp_at hj (by omega),
      add_ofNat_assoc]

end C3.RV32.Sv
