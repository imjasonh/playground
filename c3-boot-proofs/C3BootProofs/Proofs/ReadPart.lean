import C3BootProofs.Proofs.FlashRead
import C3BootProofs.Proofs.SmallFns

/-!
# `c3_bootloader::read_part`

`read_part(part, off, len, buf)` checks that `len` fits in `buf` and that
`part + off` doesn't wrap, then reads `len` bytes of flash from `part + off`
into `buf` with `flash::read`. It returns the slice as a pointer and a length:
`buf` when the read succeeded, and null otherwise.
-/

namespace C3.RV32

open C3.Image

theorem rp_at_0 : fetchRel readPartCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem rp_at_2 : fetchRel readPartCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem rp_at_4 : fetchRel readPartCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem rp_at_6 : fetchRel readPartCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem rp_at_8 : fetchRel readPartCode 0x8 = some (.alu .add (8 : Fin 32) x0 a2, 2) := by decide
theorem rp_at_a : fetchRel readPartCode 0xA = some (.branch .bltu a4 a2 0xA, 4) := by decide
theorem rp_at_e : fetchRel readPartCode 0xE = some (.alu .add a0 a0 a1, 2) := by decide
theorem rp_at_10 : fetchRel readPartCode 0x10 = some (.branch .bgeu a0 a1 0x8, 4) := by decide
theorem rp_at_14 : fetchRel readPartCode 0x14 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem rp_at_16 : fetchRel readPartCode 0x16 = some (.jal x0 0x16, 2) := by decide
theorem rp_at_18 : fetchRel readPartCode 0x18 = some (.alu .add (9 : Fin 32) x0 a3, 2) := by decide
theorem rp_at_1a : fetchRel readPartCode 0x1A = some (.alu .add a1 x0 a3, 2) := by decide
theorem rp_at_1c : fetchRel readPartCode 0x1C = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem rp_at_1e : fetchRel readPartCode 0x1E = some (.auipc ra 0x0, 4) := by decide
theorem rp_at_22 : fetchRel readPartCode 0x22 = some (.jalr ra ra 0x32, 4) := by decide
theorem rp_at_26 : fetchRel readPartCode 0x26 = some (.alu .sub a0 x0 a0, 4) := by decide
theorem rp_at_2a : fetchRel readPartCode 0x2A = some (.alu .and a0 a0 (9 : Fin 32), 2) := by decide
theorem rp_at_2c : fetchRel readPartCode 0x2C = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem rp_at_2e : fetchRel readPartCode 0x2E = some (.load .lw ra sp 0xC, 2) := by decide
theorem rp_at_30 : fetchRel readPartCode 0x30 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem rp_at_32 : fetchRel readPartCode 0x32 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem rp_at_34 : fetchRel readPartCode 0x34 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem rp_at_36 : fetchRel readPartCode 0x36 = some (.jalr x0 ra 0x0, 2) := by decide

/-- A `flash::read` environment for `len` bytes is one for fewer. -/
theorem FRdEnv.shrink {M : Word → BitVec 8} {P G out len : Word} {R : Nat} {romBase : Word} {romCode : List Nat}
    (env : FRdEnv M P G out len R romBase romCode) {len' : Word} (h : len'.toNat ≤ len.toNat) :
    FRdEnv M P G out len' R romBase romCode := by
  have sub : ∀ {b : Word} {k : Nat}, Sep out len.toNat b k → Sep out len'.toNat b k := fun hs => by
    have := hs.sub (c := 0) (l := len'.toNat) (by omega); rwa [add_ofNat_zero] at this
  exact ⟨env.hP, env.code, env.mset, env.fw, env.hG, env.hR, env.hGt, by have := env.hlen; omega, env.sGC,
    env.sGM, env.sGW, sub env.sOC, sub env.sOW, sub env.sOG, env.rom, env.sGR, sub env.sOR⟩

theorem romKeep_ne : ∀ q : Fin 32, romKeep q = true → q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`read_part`, as compiled**: with `flash::read` and the ROM where the
image puts them, `len` bytes of room at `buf`, and the stack that
`flash::read` needs plus 16 bytes below `sp`, it returns to `ra` with the
callee-saved registers restored and `len` in `a1`. `a0` is null, or it is
`buf`, `len` fit, `part + off` didn't wrap, and `buf` holds `len` bytes of
flash from `part + off`. Memory outside the stack and `buf` is unchanged. -/
theorem readPart_correct {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat}
    (hROM : RomRead flash R romBase romCode) (m : Machine) {G partOff rel len buf buflen retAddr : Word}
    (env : FRdEnv m.mem (img% flashReadAddress) G buf buflen R romBase romCode)
    (hc : CodeIn m.mem (img% readPartAddress) readPartCode) (hpc : m.pc = (img% readPartAddress))
    (ha0 : reg m a0 = partOff) (ha1 : reg m a1 = rel) (ha2 : reg m a2 = len) (ha3 : reg m a3 = buf)
    (ha4 : reg m a4 = buflen) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = G + BitVec.ofNat 32 (0x160 + R)) (hGt : G.toNat + 0x160 + R ≤ 2 ^ 32)
    (sFP : Sep (G + BitVec.ofNat 32 (0x150 + R)) 16 (img% readPartAddress) readPartCode.length)
    (sFC : Sep (G + BitVec.ofNat 32 (0x150 + R)) 16 (img% flashReadAddress) flashReadCode.length)
    (sFM : Sep (G + BitVec.ofNat 32 (0x150 + R)) 16 ((img% flashReadAddress) + 0x1309E) memsetCode.length)
    (sFW : Sep (G + BitVec.ofNat 32 (0x150 + R)) 16 ((img% flashReadAddress) + 0xFFFFFFE8) romFlashReadWordsCode.length)
    (sFR : Sep (G + BitVec.ofNat 32 (0x150 + R)) 16 romBase romCode.length)
    (sOF : Sep buf buflen.toNat (G + BitVec.ofNat 32 (0x150 + R)) 16)
    (sOP : Sep buf buflen.toNat (img% readPartAddress) readPartCode.length)
    (sGP : Sep G (0x150 + R) (img% readPartAddress) readPartCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧ reg m' a1 = len ∧
      (reg m' a0 = 0 ∨ (reg m' a0 = buf ∧ len.toNat ≤ buflen.toNat ∧ partOff.toNat + rel.toNat < 2 ^ 32 ∧
        ∀ i, i < len.toNat → m'.mem (buf + BitVec.ofNat 32 i) = flash (partOff.toNat + rel.toNat + i))) ∧
      ∀ x, Sep G (0x160 + R) x 1 → Sep buf buflen.toNat x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + BitVec.ofNat 32 (0x150 + R) = F := ⟨_, rfl⟩
  rw [hF] at sFP sFC sFM sFW sFR sOF
  have hR := env.hR
  have hFsp : reg m sp + 0xFFFFFFF0 = F := by
    rw [hsp, ← hF, BitVec.add_assoc, show (0xFFFFFFF0 : Word) = BitVec.ofNat 32 4294967280 from rfl, ofNat_add_ofNat]
    rw [show BitVec.ofNat 32 (0x160 + R + 4294967280) = BitVec.ofNat 32 (0x150 + R) from
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
  have hspF : F + 0x10 = reg m sp := by
    rw [hsp, ← hF, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, add_ofNat_assoc,
      show 0x150 + R + 0x10 = 0x160 + R by omega]
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hG (k := 0x150 + R) (by omega)
  have inF : ∀ x, Sep G (0x160 + R) x 1 → Sep F 16 x 1 := fun x hx => by
    rw [← hF]; exact hx.sub (c := 0x150 + R) (l := 16) (by omega)
  have fr : ∀ c l, c + l ≤ 16 → ∀ (x : Word) (n : Nat), Sep F 16 x n → Sep (F + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => hx.sub (c := c) (l := l) h
  have s0 : St m.mem (img% readPartAddress) m 0 (reg m) := ⟨by rw [hpc]; rfl, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc rp_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = F from hFsp] at t1
  have u1sp : upd (reg m) sp F sp = F := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp F r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc rp_at_2 (off' := 4) (by decide) (by rw [u1sp]; exact aligned_add hFa (k := 0xC) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (fr 0xC 4 (by omega) _ _ sFP)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 rp_at_4 (off' := 6) (by decide) (by rw [u1sp]; exact aligned_add hFa (k := 8) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (fr 8 4 (by omega) _ _ sFP)
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 rp_at_6 (off' := 8) (by decide) (by rw [u1sp]; exact aligned_add hFa (k := 4) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 (memStore32 m.mem (F + 0xC) (reg m ra)) (F + 8) (reg m 8)) (F + 4)
      (reg m 9) = M3 := ⟨_, rfl⟩
  rw [hM3] at t4
  have M3out : ∀ x, Sep F 16 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3]
    exact (memStore32_get_sep (fr 4 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 8 4 (by omega) x 1 hx)).trans
      (memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx)))
  have codeOut : ∀ {b : Word} {code : List Nat}, Sep F 16 b code.length → CodeIn m.mem b code → CodeIn M3 b code :=
    fun h hc' i hi => by rw [M3out _ (h.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have hc4 := codeOut sFP hc
  have fA : memLoad32 M3 (F + 0xC) = reg m ra := by
    rw [← hM3]
    exact (memLoad32_store32_sep (sep_offsets F (c := 4) (n := 4) (d := 12) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
      ((memLoad32_store32_sep (sep_offsets F (c := 8) (n := 4) (d := 12) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
        (memLoad32_store32_same _ _ _))
  have fB : memLoad32 M3 (F + 8) = reg m 8 := by
    rw [← hM3]
    exact (memLoad32_store32_sep (sep_offsets F (c := 4) (n := 4) (d := 8) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
      (memLoad32_store32_same _ _ _)
  have fC : memLoad32 M3 (F + 4) = reg m 9 := by rw [← hM3]; exact memLoad32_store32_same _ _ _
  obtain ⟨m5, e5, t5⟩ := t4.alu hc4 rp_at_8 (off' := 0xA) (by decide)
  have tail : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx (img% readPartAddress) mx 0x2C fx →
      CodeIn Mx (img% readPartAddress) readPartCode → fx sp = F → fx 8 = len →
      memLoad32 Mx (F + 0xC) = reg m ra → memLoad32 Mx (F + 8) = reg m 8 → memLoad32 Mx (F + 4) = reg m 9 →
      (∀ q, romKeep q = true → q ≠ sp → q ≠ 8 → q ≠ 9 → fx q = reg m q) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧ reg m' a1 = len ∧
        reg m' a0 = fx a0 ∧ m'.mem = Mx := by
    intro Mx mx fx s hcx hs h8 hA hB hC hk
    have hzx := s.zero
    obtain ⟨n1, d1, u1⟩ := s.alu hcx rp_at_2c (off' := 0x2E) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.lw hcx rp_at_2e (off' := 0x30) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hFa (k := 0xC) (by decide))
    rw [show upd fx a1 (aluEval .add (fx x0) (fx 8)) sp = F by simp +decide only [upd]; exact hs, hA] at u2
    obtain ⟨n3, d3, u3⟩ := u2.lw hcx rp_at_30 (off' := 0x32) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hFa (k := 8) (by decide))
    rw [show upd (upd fx a1 (aluEval .add (fx x0) (fx 8))) ra (reg m ra) sp = F by simp +decide only [upd]; exact hs,
      hB] at u3
    obtain ⟨n4, d4, u4⟩ := u3.lw hcx rp_at_32 (off' := 0x34) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hFa (k := 4) (by decide))
    rw [show upd (upd (upd fx a1 (aluEval .add (fx x0) (fx 8))) ra (reg m ra)) 8 (reg m 8) sp = F by
      simp +decide only [upd]; exact hs, hC] at u4
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hcx rp_at_34 (off' := 0x36) (by decide)
    obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hcx rp_at_36
    refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ?_, fun q hq => ?_, ?_, ?_,
      by rw [mem6]⟩
    · rw [pc6, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]; rw [hra, hret]
    · obtain ⟨q0, q1, q2, qra⟩ := romKeep_ne q hq
      rw [regs6]
      by_cases hr : q.val = 0
      · have : q = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      by_cases hsp' : q = sp
      · subst hsp'; simp +decide [upd]; rw [hs, ← hspF]; rfl
      by_cases h8' : q = 8
      · subst h8'; simp +decide [upd]
      by_cases h9' : q = 9
      · subst h9'; simp +decide [upd]
      simp [upd, hr, hsp', h8', h9', qra, q1]
      exact hk q hq hsp' h8' h9'
    · rw [regs6]; simp +decide only [upd, ite_true, ite_false]; rw [h8]; exact (congrArg (· + len) hzx).trans (BitVec.zero_add len)
    · rw [regs6]; simp +decide only [upd, ite_false]
  have fs5 : upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) sp = F := by
    simp +decide [upd]
  have f85 : upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) 8 = len := by
    simp +decide [upd, aluEval, ha2]
  have k5 : ∀ q, romKeep q = true → q ≠ sp → q ≠ 8 →
      upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) q = reg m q := fun q hq h1 h2 => by
    rw [updz t4.zero h2, updz hz h1]
  have pre5 : Steps m m5 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.single e5))))
  have from14 : ∀ (mx : Machine) (fx : Fin 32 → Word), Steps m mx → St M3 (img% readPartAddress) mx 0x14 fx → fx sp = F →
      fx 8 = len → (∀ q, romKeep q = true → q ≠ sp → q ≠ 8 → q ≠ 9 → fx q = reg m q) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧ reg m' a1 = len ∧
        (reg m' a0 = 0 ∨ (reg m' a0 = buf ∧ len.toNat ≤ buflen.toNat ∧ partOff.toNat + rel.toNat < 2 ^ 32 ∧
          ∀ i, i < len.toNat → m'.mem (buf + BitVec.ofNat 32 i) = flash (partOff.toNat + rel.toNat + i))) ∧
        ∀ x, Sep G (0x160 + R) x 1 → Sep buf buflen.toNat x 1 → m'.mem x = m.mem x := by
    intro mx fx c s hs h8 hk
    obtain ⟨n1, d1, u1⟩ := s.aluImm hc4 rp_at_14 (off' := 0x16) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.jump hc4 rp_at_16 (off' := 0x2C) (by decide) (by rw [u1.pc]; decide)
    obtain ⟨m', c', pc', keep', a1', a0', mem'⟩ := tail M3 n2 _ u2 hc4
      (by rw [updz s.zero (by decide)]; exact hs) (by rw [updz s.zero (by decide)]; exact h8) fA fB fC
      (fun q hq h1 h2 h3 => by rw [updz s.zero (romKeep_ne q hq).1]; exact hk q hq h1 h2 h3)
    refine ⟨m', c.trans (.cons d1 (.cons d2 c')), pc', keep', a1', Or.inl ?_, fun x hx _ => ?_⟩
    · rw [a0']; show aluEval .add (fx 0) 0 = 0; rw [s.zero]; rfl
    · rw [mem']; exact M3out x (inF x hx)
  by_cases hlt : buflen.ult len = true
  · obtain ⟨m6, e6, t6⟩ := t5.taken hc4 0x14 rp_at_a (by decide)
      (by rw [updz t4.zero (show a4 ≠ 8 by decide), updz hz (show a4 ≠ sp by decide), ha4,
        updz t4.zero (show a2 ≠ 8 by decide), updz hz (show a2 ≠ sp by decide), ha2]; exact hlt)
    exact from14 m6 _ (pre5.trans (.single e6)) t6 fs5 f85 (fun q hq h1 h2 _ => k5 q hq h1 h2)
  have hle : len.toNat ≤ buflen.toNat := by
    have : ¬ buflen.toNat < len.toNat := fun h => hlt (decide_eq_true h)
    omega
  obtain ⟨m6, e6, t6⟩ := t5.notTaken hc4 0xE rp_at_a (by decide)
    (by
      rw [updz t4.zero (show a4 ≠ 8 by decide), updz hz (show a4 ≠ sp by decide), ha4,
        updz t4.zero (show a2 ≠ 8 by decide), updz hz (show a2 ≠ sp by decide), ha2]
      show buflen.ult len = false
      cases h : buflen.ult len
      · rfl
      · exact absurd h hlt)
  obtain ⟨m7, e7, t7⟩ := t6.alu hc4 rp_at_e (off' := 0x10) (by decide)
  have k7 : ∀ q, romKeep q = true → q ≠ sp → q ≠ 8 → upd (upd (upd (reg m) sp F) 8
      (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2))) a0
      (aluEval .add (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) a0)
        (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) a1)) q = reg m q :=
    fun q hq h1 h2 => by rw [updz t5.zero (romKeep_ne q hq).1]; exact k5 q hq h1 h2
  have pre7 : Steps m m7 := pre5.trans (.cons e6 (.single e7))
  have fa07 : upd (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2))) a0
      (aluEval .add (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) a0)
        (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) a1)) a0 = partOff + rel := by
    simp +decide [upd, aluEval, ha0, ha1]
  have fa17 : upd (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2))) a0
      (aluEval .add (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) a0)
        (upd (upd (reg m) sp F) 8 (aluEval .add (upd (reg m) sp F x0) (upd (reg m) sp F a2)) a1)) a1 = rel := by
    simp +decide [upd, ha1]
  by_cases hov : (partOff + rel).ult rel = true
  · obtain ⟨m8, e8, t8⟩ := t7.notTaken hc4 0x14 rp_at_10 (by decide)
      (by rw [fa07, fa17]; show (!(partOff + rel).ult rel) = false; rw [hov]; rfl)
    exact from14 m8 _ (pre7.trans (.single e8)) t8 ((updz t5.zero (show sp ≠ a0 by decide)).trans fs5)
      ((updz t5.zero (show (8 : Fin 32) ≠ a0 by decide)).trans f85) (fun q hq h1 h2 _ => k7 q hq h1 h2)
  have hsum : partOff.toNat + rel.toNat < 2 ^ 32 := by
    have h1 : ¬ (partOff + rel).toNat < rel.toNat := fun h => hov (decide_eq_true h)
    rw [BitVec.toNat_add] at h1
    have := partOff.isLt; have := rel.isLt
    omega
  have haddr : (partOff + rel).toNat = partOff.toNat + rel.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hsum
  obtain ⟨m8, e8, t8⟩ := t7.taken hc4 0x18 rp_at_10 (by decide)
    (by
      rw [fa07, fa17]; show (!(partOff + rel).ult rel) = true
      cases h : (partOff + rel).ult rel
      · rfl
      · exact absurd h hov)
  obtain ⟨m9, e9, t9⟩ := t8.alu hc4 rp_at_18 (off' := 0x1A) (by decide)
  obtain ⟨m10, e10, t10⟩ := t9.alu hc4 rp_at_1a (off' := 0x1C) (by decide)
  obtain ⟨m11, e11, t11⟩ := t10.alu hc4 rp_at_1c (off' := 0x1E) (by decide)
  obtain ⟨m12, c12, pc12, mem12, regs12⟩ := t11.callRa (cb := (img% flashReadAddress)) hc4 rp_at_1e rp_at_22 (by decide) (by decide)
  have a012 : reg m12 a0 = partOff + rel := by rw [regs12]; simp +decide [upd, aluEval, ha0, ha1]
  have a112 : reg m12 a1 = buf := by rw [regs12]; simp +decide [upd, aluEval, ha3]
  have a212 : reg m12 a2 = len := by rw [regs12]; simp +decide [upd, aluEval, ha2]
  have ra12 : reg m12 ra = (img% readPartAddress) + BitVec.ofNat 32 (0x1E + 8) := by rw [regs12]; simp +decide [upd]
  have sp12 : reg m12 sp = F := by rw [regs12]; simp +decide [upd]
  have s012 : reg m12 8 = len := by rw [regs12]; simp +decide [upd, aluEval, ha2]
  have s112 : reg m12 9 = buf := by rw [regs12]; simp +decide [upd, aluEval, ha3]
  have envM3 : FRdEnv M3 (img% flashReadAddress) G buf buflen R romBase romCode :=
    ⟨env.hP, codeOut sFC env.code, codeOut sFM env.mset, codeOut sFW env.fw, env.hG, env.hR, env.hGt, env.hlen,
      env.sGC, env.sGM, env.sGW, env.sOC, env.sOW, env.sOG, codeOut sFR env.rom, env.sGR, env.sOR⟩
  have env12 : FRdEnv m12.mem (img% flashReadAddress) G buf len R romBase romCode := by rw [mem12]; exact envM3.shrink hle
  obtain ⟨m13, c13, pc13, sp13, k13, a013, by13, mem13⟩ := flashRead_correct hROM m12 env12 pc12 a012 a112 a212 ra12
    (even_clear _ (by decide)) (by rw [sp12, ← hF])
  have shr : ∀ {b : Word} {k : Nat}, Sep buf buflen.toNat b k → Sep buf len.toNat b k := fun hs => by
    have := hs.sub (c := 0) (l := len.toNat) (by omega); rwa [add_ofNat_zero] at this
  have shrG : ∀ x, Sep G (0x160 + R) x 1 → Sep G (0x150 + R) x 1 := fun x hx => by
    have := hx.sub (c := 0) (l := 0x150 + R) (by omega); rwa [add_ofNat_zero] at this
  have hc13 : CodeIn m13.mem (img% readPartAddress) readPartCode := fun i hi => by
    rw [mem13 _ (sGP.subR (c := i) (l := 1) (by omega)) ((shr sOP).subR (c := i) (l := 1) (by omega)), mem12]
    exact hc4 i hi
  have fr13 : ∀ c, 4 ≤ c → c + 4 ≤ 16 → memLoad32 m13.mem (F + BitVec.ofNat 32 c) = memLoad32 M3 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, mem13 _ ?_ ((shr sOF).subR (c := c + j) (l := 1) (by omega)), mem12]
      rw [← hF, add_ofNat_assoc]
      have := sep_offsets G (c := 0) (n := 0x150 + R) (d := 0x150 + R + (c + j)) (k := 1) (Or.inl (by omega))
        (by omega) (by omega)
      rwa [add_ofNat_zero] at this
  have t13 : St m13.mem (img% readPartAddress) m13 0x26 (reg m13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  obtain ⟨m14, e14, t14⟩ := t13.alu hc13 rp_at_26 (off' := 0x2A) (by decide)
  obtain ⟨m15, e15, t15⟩ := t14.alu hc13 rp_at_2a (off' := 0x2C) (by decide)
  have hz13 := t13.zero
  have s013 : reg m13 8 = len := (k13 8 (by decide)).trans s012
  have s113 : reg m13 9 = buf := (k13 9 (by decide)).trans s112
  obtain ⟨m', c', pc', keep', a1', a0', mem'⟩ := tail m13.mem m15 _ t15 hc13
    (by rw [updz t14.zero (by decide), updz hz13 (by decide), sp13, hF])
    (by rw [updz t14.zero (by decide), updz hz13 (by decide), s013])
    ((fr13 12 (by omega) (by omega)).trans fA) ((fr13 8 (by omega) (by omega)).trans fB)
    ((fr13 4 (by omega) (by omega)).trans fC)
    (fun q hq h1 h2 h3 => by
      obtain ⟨q0, q1, q2, qra⟩ := romKeep_ne q hq
      rw [updz t14.zero q0, updz hz13 q0, k13 q hq, regs12]
      by_cases hr : q.val = 0
      · have : q = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, q0, q1, q2, qra, h1, h2, h3])
  have fa0 : reg m' a0 = aluEval .and (aluEval .sub 0 (reg m13 a0)) buf := by
    rw [a0', ← s113, ← hz13]; rfl
  refine ⟨m', pre7.trans (.cons e8 (.cons e9 (.cons e10 (.cons e11 (c12.trans (c13.trans (.cons e14 (.cons e15 c')))))))),
    pc', keep', a1', ?_, fun x hx hb => ?_⟩
  · rcases a013 with h0 | h1
    · left; rw [fa0, h0]; show (0 : Word) &&& buf = 0; exact BitVec.zero_and
    · right
      refine ⟨by rw [fa0, h1]; show (0xFFFFFFFF : Word) &&& buf = buf; exact ones_and_left buf, hle, hsum, fun i hi => ?_⟩
      rw [mem', by13 h1 i hi, haddr]
  · rw [mem', mem13 x (shrG x hx) (shr hb), mem12]; exact M3out x (inF x hx)

end C3.RV32





