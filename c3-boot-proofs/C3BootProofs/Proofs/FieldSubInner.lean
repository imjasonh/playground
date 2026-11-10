import C3BootProofs.Proofs.FieldArith
import C3BootProofs.Proofs.FieldDecode
import C3BootProofs.Proofs.Parse

/-!
# `sub_inner`, as compiled

`p256::arithmetic::field::field_impl::sub_inner` subtracts the P-256
modulus from a 9-limb number with nine calls to `borrowing_sub`, then adds
the modulus back under the final borrow mask (`addBack`). Its frame is 0x30
bytes; each `borrowing_sub` call also writes the word 4 bytes below it.
-/

namespace C3.RV32

open C3.Image

theorem alu_zadd (x : Word) : aluEval .add 0#32 x = x := BitVec.zero_add x

theorem alu_zadd' (x : Word) : aluEval .add 0 x = x := BitVec.zero_add x

/-- `borrowing_sub`'s offset from `sub_inner`. -/
abbrev siBsub (P : Word) : Word := P + 0xFFFF1162

/-- A call from `sub_inner` to `borrowing_sub` with `sp` at `F`. -/
theorem si_bsub {Mx : Word → BitVec 8} {P F : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {imm o : Word} (s : St Mx P m off f) (hc : CodeIn Mx P subInnerCode)
    (hb : CodeIn Mx (siBsub P) borrowingSubCode) (hP : P.toNat % 2 = 0)
    (h1 : fetchRel subInnerCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel subInnerCode (off + 4) = some (.jalr ra ra o, 4))
    (hcb : P + BitVec.ofNat 32 off + imm + o = siBsub P) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = F) (hF : F.toNat % 4 = 0) (hsep : Sep (F + 0xFFFFFFFC) 4 (siBsub P) borrowingSubCode.length) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧
      reg m' a0 = bsubD (f a0) (f a1) (f a2) ∧ reg m' a1 = bsubB (f a0) (f a1) (bsubD (f a0) (f a1) (f a2)) ∧
      reg m' sp = F ∧ (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg m' q = f q) ∧
      ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → m'.mem x = Mx x := by
  have hev : (siBsub P).toNat % 2 = 0 := even_at P hP 0xFFFF1162 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hcb hev
  have hz := s.zero
  have r1 : ∀ q, q ≠ ra → reg m1 q = f q := fun q hq => by
    rw [regs1]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  obtain ⟨m2, c2, pc2, a02, a12, sp2, fr2, mem2⟩ := borrowingSub_correct m1 (siBsub P)
    (P + BitVec.ofNat 32 (off + 8)) (f a0) (f a1) (f a2) (by show CodeIn m1.mem _ _; rw [mem1]; exact hb) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hl) (by rw [r1 sp (by decide), hsp]; exact hF) (by rw [r1 sp (by decide), hsp]; exact hsep)
  rw [r1 sp (by decide), hsp] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, a12, sp2, fun q q0 q1 q2 q3 q4 qr => ?_,
    fun x hx => by rw [mem2 x hx, mem1]⟩
  rw [fr2 q q0 q1 q2 q3 q4, r1 q qr]

/-- One of `sub_inner`'s rounds 1 to 8: keep the last difference in `K`, load
limb `i` of both operands, move the borrow mask to `a2`, and call
`borrowing_sub`. -/
theorem si_round {Mx : Word → BitVec 8} {P F lp rp : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {K : Fin 32} {i : Nat} {imm o : Word} (s : St Mx P m off f) (hc : CodeIn Mx P subInnerCode)
    (hb : CodeIn Mx (siBsub P) borrowingSubCode) (hP : P.toNat % 2 = 0)
    (i1 : fetchRel subInnerCode off = some (.alu .add K x0 a0, 2))
    (i2 : fetchRel subInnerCode (off + 2) = some (.load .lw a0 (8 : Fin 32) (BitVec.ofNat 32 (4 * i)), 2))
    (i3 : fetchRel subInnerCode (off + 2 + 2) = some (.load .lw a2 (9 : Fin 32) (BitVec.ofNat 32 (4 * i)), 2))
    (i4 : fetchRel subInnerCode (off + 2 + 2 + 2) = some (.alu .add a3 x0 a1, 2))
    (i5 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2) = some (.alu .add a1 x0 a2, 2))
    (i6 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2 + 2) = some (.alu .add a2 x0 a3, 2))
    (i7 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2 + 2 + 2) = some (.auipc ra imm, 4))
    (i8 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2 + 2 + 2 + 4) = some (.jalr ra ra o, 4))
    (hcb : P + BitVec.ofNat 32 (off + 2 + 2 + 2 + 2 + 2 + 2) + imm + o = siBsub P)
    (hl : (P + BitVec.ofNat 32 (off + 2 + 2 + 2 + 2 + 2 + 2 + 8)).toNat % 2 = 0)
    (hK0 : K ≠ x0) (hKa : K ≠ a0 ∧ K ≠ a1 ∧ K ≠ a2 ∧ K ≠ a3) (hK8 : K ≠ (8 : Fin 32)) (hK9 : K ≠ (9 : Fin 32))
    (hKs : K ≠ sp) (hK4 : K ≠ a4) (hKr : K ≠ ra)
    (hs0 : f (8 : Fin 32) = lp) (hs1 : f (9 : Fin 32) = rp) (hsp : f sp = F) (hF : F.toNat % 4 = 0)
    (hlp : (lp + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0) (hrp : (rp + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0)
    (hsep : Sep (F + 0xFFFFFFFC) 4 (siBsub P) borrowingSubCode.length) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 2 + 2 + 2 + 2 + 2 + 2 + 8) (reg m') ∧ reg m' K = f a0 ∧
      reg m' a0 = bsubD (memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i)))
        (f a1) ∧
      reg m' a1 = bsubB (memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i))) (f a1)) ∧
      reg m' sp = F ∧
      (∀ q, q ≠ K → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg m' q = f q) ∧
      ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → m'.mem x = Mx x := by
  have hz := s.zero
  obtain ⟨m1, d1, u1⟩ := s.alu hc i1 (off' := off + 2) (ofNat_add_ofNat off 2)
  obtain ⟨m2, d2, u2⟩ := u1.lw hc i2 (off' := off + 2 + 2) (ofNat_add_ofNat _ 2)
    (by rw [updz hz (Ne.symm hK8), hs0]; exact hlp)
  obtain ⟨m3, d3, u3⟩ := u2.lw hc i3 (off' := off + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
    (by rw [updz (by simp) (show (9 : Fin 32) ≠ a0 by decide), updz hz (Ne.symm hK9), hs1]; exact hrp)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc i4 (off' := off + 2 + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
  obtain ⟨m5, d5, u5⟩ := u4.alu hc i5 (off' := off + 2 + 2 + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
  obtain ⟨m6, d6, u6⟩ := u5.alu hc i6 (off' := off + 2 + 2 + 2 + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
  have n0 : a0 ≠ K := Ne.symm hKa.1
  have n1 : a1 ≠ K := Ne.symm hKa.2.1
  have n2 : a2 ≠ K := Ne.symm hKa.2.2.1
  have n3 : a3 ≠ K := Ne.symm hKa.2.2.2
  have n8 : (8 : Fin 32) ≠ K := Ne.symm hK8
  have n9 : (9 : Fin 32) ≠ K := Ne.symm hK9
  have ns : sp ≠ K := Ne.symm hKs
  have fz : f 0 = 0 := hz
  have e0 : reg m6 a0 = memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i)) := by
    rw [u6.regs]; simp +decide [upd, n8, hs0]
  have e1 : reg m6 a1 = memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i)) := by
    rw [u6.regs]; simp +decide [upd, n9, hs1, alu_zadd]
  have e2 : reg m6 a2 = f a1 := by
    rw [u6.regs]; simp +decide [upd, n1, alu_zadd]
  have esp : reg m6 sp = F := by rw [u6.regs]; simp +decide [upd, ns, hsp]
  have eK : reg m6 K = f a0 := by
    rw [u6.regs]; simp +decide [upd, Ne.symm n0, Ne.symm n2, Ne.symm n3, Ne.symm n1, hK0, fz, alu_zadd]
  have fr6 : ∀ q, q ≠ K → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m6 q = f q := fun q qK q0 q1 q2 q3 => by
    rw [u6.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, fz]
    · simp [upd, h0, qK, q0, q1, q2, q3]
  obtain ⟨m7, c7, u7, a07, a17, sp7, fr7, mem7⟩ := si_bsub u6.self hc hb hP i7 i8 hcb hl esp hF hsep
  rw [e0, e1, e2] at a07 a17
  refine ⟨m7, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7))))), u7, ?_, a07, a17, sp7,
    fun q qK q0 q1 q2 q3 q4 qr => ?_, mem7⟩
  · rw [fr7 K hKa.1 hKa.2.1 hKa.2.2.1 hKa.2.2.2 hK4 hKr, eK]
  · rw [fr7 q q0 q1 q2 q3 q4 qr, fr6 q qK q0 q1 q2 q3]

/-! ## The whole function -/

/-- `sub_inner`'s add-back and stores, from offset 0xC6 to the restore call. -/
def siAddBlock : List BInstr :=
  [.alu .add (19 : Fin 32) (19 : Fin 32) a1, .alu .add (20 : Fin 32) (20 : Fin 32) a1,
   .alu .sltu a0 (19 : Fin 32) a1, .alu .add a0 a0 (20 : Fin 32), .alu .sltu a2 (20 : Fin 32) a1,
   .alu .sltu a3 a0 (20 : Fin 32), .alu .add (21 : Fin 32) (21 : Fin 32) a1, .alu .add a2 a2 a3,
   .alu .add a2 a2 (21 : Fin 32), .alu .sltu a3 (21 : Fin 32) a1, .alu .sltu a4 a2 (21 : Fin 32),
   .alu .add a3 a3 a4, .alu .add (22 : Fin 32) (22 : Fin 32) a3, .alu .sltu a3 (22 : Fin 32) a3,
   .alu .add (24 : Fin 32) (24 : Fin 32) a3, .aluImm .and a4 a1 0x1, .alu .sltu a3 (24 : Fin 32) a3,
   .alu .add (26 : Fin 32) (26 : Fin 32) a1, .alu .add (23 : Fin 32) (23 : Fin 32) a3,
   .alu .add (25 : Fin 32) (25 : Fin 32) a4, .alu .sltu a3 (23 : Fin 32) a3, .alu .sltu a4 (25 : Fin 32) a4,
   .alu .add a3 a3 (25 : Fin 32), .alu .sltu a5 a3 (25 : Fin 32), .sw (18 : Fin 32) (19 : Fin 32) 0x0,
   .alu .add (8 : Fin 32) x0 (18 : Fin 32), .sw (8 : Fin 32) a0 0x4, .sw (8 : Fin 32) a2 0x8,
   .sw (18 : Fin 32) (22 : Fin 32) 0xC, .alu .add a4 a4 a5, .alu .add a4 a4 (26 : Fin 32),
   .sw (18 : Fin 32) (24 : Fin 32) 0x10, .sw (18 : Fin 32) (23 : Fin 32) 0x14, .sw (8 : Fin 32) a3 0x18,
   .sw (8 : Fin 32) a4 0x1C, .sw (8 : Fin 32) a1 0x20]

set_option maxRecDepth 20000 in
theorem siAddBlock_end : blockEnd subInnerCode 0xC6 siAddBlock = some 0x12C := by decide


/-- What `sub_inner`'s save helper stores and its restore helper loads. -/
abbrev siPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0x2C), ((8 : Fin 32), BitVec.ofNat 32 0x28), ((9 : Fin 32), BitVec.ofNat 32 0x24),
   ((18 : Fin 32), BitVec.ofNat 32 0x20), ((19 : Fin 32), BitVec.ofNat 32 0x1C),
   ((20 : Fin 32), BitVec.ofNat 32 0x18), ((21 : Fin 32), BitVec.ofNat 32 0x14),
   ((22 : Fin 32), BitVec.ofNat 32 0x10), ((23 : Fin 32), BitVec.ofNat 32 0xC)]

theorem saveMem_outside {M : Word → BitVec 8} {G : Word} {f : Fin 32 → Word} {x : Word} :
    ∀ ps : List (Fin 32 × Word), (∀ p ∈ ps, Sep (G + p.2) 4 x 1) → saveMem M G f ps x = M x
  | [], _ => rfl
  | p :: ps, h => by
    simp only [saveMem]
    rw [saveMem_outside ps fun q hq => h q (List.mem_cons_of_mem _ hq),
      memStore32_get_sep (h p (List.mem_cons_self ..))]

theorem siSave_shape : SaveAt subInnerSaveCode 0 siPs := by simp only [SaveAt]; decide

theorem siRestore_shape : RestoreAt subInnerRestoreCode 0 siPs := by simp only [RestoreAt]; decide

/-- The P-256 modulus as `sub_inner`'s second operand holds it: eight limbs
and a zero. -/
def pLimbs : List Word :=
  [0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0, 0, 0, 1, 0xFFFFFFFF, 0]

theorem pLimbs_val : limbVal pLimbs = p256 := by decide

/-- The `n` words at `a`. -/
def wordsAt (M : Word → BitVec 8) (a : Word) (n : Nat) : List Word :=
  (List.range n).map fun i => memLoad32 M (a + BitVec.ofNat 32 (4 * i))

/-- Where `sub_inner` runs: its code and its helpers' at their offsets, the
0x34 bytes of stack below `sp0` that it and `borrowing_sub` use, and the
result and operands, aligned and apart from what each must not touch. -/
structure SIEnv (M : Word → BitVec 8) (P sp0 out lp rp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P subInnerCode
  bsub : CodeIn M (siBsub P) borrowingSubCode
  save : CodeIn M (P + 0xDC34) subInnerSaveCode
  restore : CodeIn M (P + 0xDE3E) subInnerRestoreCode
  hsp : sp0.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  hlp : lp.toNat % 4 = 0
  hrp : rp.toNat % 4 = 0
  hS : 0x34 ≤ sp0.toNat
  sSC : Sep (sp0 + 0xFFFFFFCC) 0x34 P subInnerCode.length
  sSB : Sep (sp0 + 0xFFFFFFCC) 0x34 (siBsub P) borrowingSubCode.length
  sSS : Sep (sp0 + 0xFFFFFFCC) 0x34 (P + 0xDC34) subInnerSaveCode.length
  sSR : Sep (sp0 + 0xFFFFFFCC) 0x34 (P + 0xDE3E) subInnerRestoreCode.length
  sOC : Sep out 36 P subInnerCode.length
  sOR : Sep out 36 (P + 0xDE3E) subInnerRestoreCode.length
  sOS : Sep out 36 (sp0 + 0xFFFFFFCC) 0x34
  sLS : Sep lp 36 (sp0 + 0xFFFFFFCC) 0x34
  sRS : Sep rp 36 (sp0 + 0xFFFFFFCC) 0x34
  hwrap : out.toNat + 36 ≤ 2 ^ 32 ∧ lp.toNat + 36 ≤ 2 ^ 32 ∧ rp.toNat + 36 ≤ 2 ^ 32
  pval : wordsAt M rp 9 = pLimbs

/-- Memory after storing the words `ws` at consecutive words from word `k`
past `a`. -/
def storeWords (a : Word) : (Word → BitVec 8) → Nat → List Word → Word → BitVec 8
  | M, _, [] => M
  | M, k, w :: ws => storeWords a (memStore32 M (a + BitVec.ofNat 32 (4 * k)) w) (k + 1) ws

theorem storeWords_outside {a x : Word} : ∀ (M : Word → BitVec 8) (k : Nat) (ws : List Word),
    Sep (a + BitVec.ofNat 32 (4 * k)) (4 * ws.length) x 1 → storeWords a M k ws x = M x
  | _, _, [], _ => rfl
  | M, k, w :: ws, h => by
    simp only [storeWords]
    rw [storeWords_outside _ (k + 1) ws (by
      have := h.sub (c := 4) (l := 4 * ws.length) (by simp; omega)
      rwa [add_ofNat_assoc, show 4 * k + 4 = 4 * (k + 1) by omega] at this),
      memStore32_get_sep (h.sub (c := 0) (l := 4) (by simp; omega) |> fun h' => by rwa [add_ofNat_zero] at h')]

theorem storeWords_load {a : Word} (hw : a.toNat + 36 ≤ 2 ^ 32) : ∀ (M : Word → BitVec 8) (k : Nat) (ws : List Word)
    (j : Nat), k ≤ j → j < k + ws.length → k + ws.length ≤ 9 →
    memLoad32 (storeWords a M k ws) (a + BitVec.ofNat 32 (4 * j)) = ws.getD (j - k) 0
  | _, _, [], _, h1, h2, _ => absurd h2 (by simp; omega)
  | M, k, w :: ws, j, h1, h2, h3 => by
    simp only [storeWords]
    by_cases hj : j = k
    · subst hj
      rw [memLoad32_congr (M := memStore32 M (a + BitVec.ofNat 32 (4 * j)) w) fun i hi => by
        rw [add_ofNat_assoc]
        exact storeWords_outside _ (j + 1) ws (sep_offsets a (Or.inr (by omega)) (by simp at h3; omega)
          (by omega))]
      rw [memLoad32_store32_same, Nat.sub_self]; rfl
    · rw [storeWords_load hw _ (k + 1) ws j (by omega) (by simp at h2 ⊢; omega) (by simp at h3 ⊢; omega)]
      rw [show j - k = (j - (k + 1)) + 1 by omega]; rfl

theorem siAdd_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {P out : Word}
    (hs2 : f (18 : Fin 32) = out) (hout : out.toNat % 4 = 0)
    (hS : Sep out 36 P subInnerCode.length) : BlockOk P subInnerCode.length siAddBlock (M, f) := by
  have oS : ∀ c, c + 4 ≤ 36 → Sep (out + BitVec.ofNat 32 c) 4 P subInnerCode.length := fun c h =>
    hS.sub (c := c) (l := 4) h
  have oA : ∀ c, c % 4 = 0 → c < 36 → (out + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 =>
    aligned_add hout (by omega)
  simp only [BlockOk, BInstr.ok, BInstr.run, siAddBlock]
  simp +decide only [upd, ↓reduceIte, hs2, alu_zadd']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, ⟨oA 0 rfl (by decide), oS 0 (by decide)⟩, trivial, ⟨oA 4 rfl (by decide), oS 4 (by decide)⟩,
    ⟨oA 8 rfl (by decide), oS 8 (by decide)⟩, ⟨oA 12 rfl (by decide), oS 12 (by decide)⟩, trivial, trivial,
    ⟨oA 16 rfl (by decide), oS 16 (by decide)⟩, ⟨oA 20 rfl (by decide), oS 20 (by decide)⟩,
    ⟨oA 24 rfl (by decide), oS 24 (by decide)⟩, ⟨oA 28 rfl (by decide), oS 28 (by decide)⟩,
    ⟨oA 32 rfl (by decide), oS 32 (by decide)⟩, trivial⟩

/-- The add-back block stores `addBack`'s words and the borrow mask in order. -/
theorem siAdd_mem {M : Word → BitVec 8} {f : Fin 32 → Word} {out : Word}
    (hs2 : f (18 : Fin 32) = out) :
    (runBlock siAddBlock (M, f)).1 = storeWords out M 0 (addBack (f (19 : Fin 32)) (f (20 : Fin 32))
      (f (21 : Fin 32)) (f (22 : Fin 32)) (f (24 : Fin 32)) (f (23 : Fin 32)) (f (25 : Fin 32)) (f (26 : Fin 32))
      (f a1) ++ [f a1]) := by
  simp only [runBlock, BInstr.run, siAddBlock]
  simp +decide only [upd, ↓reduceIte, hs2, alu_zadd']
  rfl

/-- The add-back block keeps `sp` and every register it doesn't write. -/
theorem siAdd_regs {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) →
      q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (22 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (24 : Fin 32) →
      q ≠ (25 : Fin 32) → q ≠ (26 : Fin 32) → (runBlock siAddBlock (M, f)).2 q = f q := by
  intro q h0 h1 h2 h3 h4 h5 h8 h19 h20 h21 h22 h23 h24 h25 h26
  simp only [runBlock, BInstr.run, siAddBlock]
  by_cases hq : q.val = 0
  · have : q = 0 := Fin.ext hq
    subst this; simp [upd, hz]
  · simp [upd, hq, h0, h2, h3, h4, h5, h8, h19, h20, h21, h22, h23, h24, h25, h26]

/-- The registers `sub_inner` and `borrowing_sub` write: `t0`, `ra`, `sp`,
`s0` through `s10`, and `a0` through `a5`. -/
def siWr (q : Fin 32) : Bool :=
  q = 1 || q = 2 || q = 5 || (8 ≤ q.val && q.val ≤ 15) || (18 ≤ q.val && q.val ≤ 26)

theorem siWr_ne : ∀ q : Fin 32, siWr q = false →
    q ≠ ra ∧ q ≠ sp ∧ q ≠ t0 ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧
      q ≠ a4 ∧ q ≠ a5 ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧ q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32) ∧
      q ≠ (22 : Fin 32) ∧ q ≠ (23 : Fin 32) ∧ q ≠ (24 : Fin 32) ∧ q ≠ (25 : Fin 32) ∧ q ≠ (26 : Fin 32) := by
  decide

end C3.RV32
