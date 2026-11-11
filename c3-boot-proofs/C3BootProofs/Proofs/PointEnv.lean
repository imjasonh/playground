import C3BootProofs.Proofs.FieldSpec
import C3BootProofs.Proofs.PointDecode
import C3BootProofs.Proofs.FieldMul

/-!
# Where the compiled point addition runs, and its calls

`primeorder`'s `add_assign` for P-256, as compiled, keeps 17 field elements
in a 0x240-byte frame and makes 46 calls: `FieldElement::multiply`,
`field_impl::add`, `field_impl::sub`, `FieldElement::double`, and three
`memcpy`s that write the result into `lhs`. `multiply` needs the most stack
below the frame, 0x130 bytes, so the stack it may change is the 0x370 bytes
below `sp`, which this file calls `S`; the frame starts 0x130 bytes into it.

`PAInv` is what holds at each point between the calls, and the lemmas here
carry it across one call or one argument instruction, with the call's
result.
-/

namespace C3.RV32

open C3.Image

/-- The curve constant `b` in Montgomery form, as the image stores it at
`bAddr`. -/
def bMont : Nat := 0xdc30061d04874834e5a220abf7212ed6acf005cd78843090d89cdf6229c4bddf

abbrev bAddr : Word := 0x3FCC4368

/-- Where the point addition runs: its code at `P`, its callees where the
image puts them, `b` at `bAddr`, `lhs` (the first point and the result) and
`rhs` (the second point), each 96 bytes, aligned, and the 0x370 bytes of
stack below `sp0` apart from the code, `b`, and both points. The result's
writes keep `lhs` apart from all code too. -/
structure PAEnv (M : Word → BitVec 8) (P sp0 lhs rhs : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P pointAddCode
  mul : CodeIn M (P + 0xE838) fieldMulCode
  wm : CodeIn M (P + 0xA71C) wideMulCode
  wms : CodeIn M (P + 0x1CB46) wideMulSaveCode
  wmr : CodeIn M (P + 0x1CB36) wideMulRestoreCode
  mset : CodeIn M (P + 0x1D100) memsetCode
  stub : CodeIn M (P + 0x1D168) memcpyStubCode
  body : CodeIn M (P + 0x1D170) memcpyBodyCode
  si : CodeIn M (P + 0xEC34) subInnerCode
  bsub : CodeIn M (siBsub (P + 0xEC34)) borrowingSubCode
  sis : CodeIn M (P + 0xEC34 + 0xDC34) subInnerSaveCode
  sir : CodeIn M (P + 0xEC34 + 0xDE3E) subInnerRestoreCode
  add : CodeIn M (P + 0xEF8A) fieldAddCode
  sub : CodeIn M (P + 0xF0AC) fieldSubCode
  dbl : CodeIn M (P + 0xF290) fieldDoubleCode
  bconst : limbVal (wordsAt M bAddr 8) = bMont
  hsp : sp0.toNat % 4 = 0
  hS : 0x370 ≤ sp0.toNat
  hl : lhs.toNat % 4 = 0
  hr : rhs.toNat % 4 = 0
  hwl : lhs.toNat + 96 < 2 ^ 32
  sC : Sep (sp0 + 0xFFFFFC90) 0x370 P pointAddCode.length
  sMul : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xE838) fieldMulCode.length
  sWm : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xA71C) wideMulCode.length
  sWms : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0x1CB46) wideMulSaveCode.length
  sWmr : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0x1CB36) wideMulRestoreCode.length
  sMs : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0x1D100) memsetCode.length
  sU : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0x1D168) memcpyStubCode.length
  sB : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0x1D170) memcpyBodyCode.length
  sI : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xEC34) subInnerCode.length
  sIb : Sep (sp0 + 0xFFFFFC90) 0x370 (siBsub (P + 0xEC34)) borrowingSubCode.length
  sIs : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xEC34 + 0xDC34) subInnerSaveCode.length
  sIr : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xEC34 + 0xDE3E) subInnerRestoreCode.length
  sA : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xEF8A) fieldAddCode.length
  sSb : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xF0AC) fieldSubCode.length
  sD : Sep (sp0 + 0xFFFFFC90) 0x370 (P + 0xF290) fieldDoubleCode.length
  sK : Sep bAddr 32 (sp0 + 0xFFFFFC90) 0x370
  sL : Sep lhs 96 (sp0 + 0xFFFFFC90) 0x370
  sR : Sep rhs 96 (sp0 + 0xFFFFFC90) 0x370
  lC : Sep lhs 96 P pointAddCode.length
  lMul : Sep lhs 96 (P + 0xE838) fieldMulCode.length
  lWm : Sep lhs 96 (P + 0xA71C) wideMulCode.length
  lWms : Sep lhs 96 (P + 0x1CB46) wideMulSaveCode.length
  lWmr : Sep lhs 96 (P + 0x1CB36) wideMulRestoreCode.length
  lMs : Sep lhs 96 (P + 0x1D100) memsetCode.length
  lU : Sep lhs 96 (P + 0x1D168) memcpyStubCode.length
  lB : Sep lhs 96 (P + 0x1D170) memcpyBodyCode.length
  lI : Sep lhs 96 (P + 0xEC34) subInnerCode.length
  lIb : Sep lhs 96 (siBsub (P + 0xEC34)) borrowingSubCode.length
  lIs : Sep lhs 96 (P + 0xEC34 + 0xDC34) subInnerSaveCode.length
  lIr : Sep lhs 96 (P + 0xEC34 + 0xDE3E) subInnerRestoreCode.length
  lA : Sep lhs 96 (P + 0xEF8A) fieldAddCode.length
  lSb : Sep lhs 96 (P + 0xF0AC) fieldSubCode.length
  lD : Sep lhs 96 (P + 0xF290) fieldDoubleCode.length

/-- The registers that no call or argument instruction of the point addition
changes: all but `ra`, `t0` through `t6`, and `a0` through `a7`. -/
def paKeep (q : Fin 32) : Bool := q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- What holds between the point addition's calls, at offset `off`: the
registers `paKeep` names hold `V`, memory outside `S` and the first `W`
bytes of `lhs` is as it was on entry (`M0`), and the register save slots at
the frame's top hold what they held after the prologue (`Ms`). -/
structure PAInv (M0 : Word → BitVec 8) (P sp0 lhs : Word) (V : Fin 32 → Word) (Ms : Word → BitVec 8)
    (W : Nat) (M : Word → BitVec 8) (n : Machine) (off : Nat) : Prop where
  st : St M P n off (reg n)
  keep : ∀ q, paKeep q = true → reg n q = V q
  fr : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → Sep lhs W x 1 → M x = M0 x
  sv : ∀ c, 0x224 ≤ c → c < 0x240 →
    M (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) = Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c)

/-- An operand a call may read: aligned, and apart from the callee's stack. -/
def PSrc (sp0 a : Word) : Prop := a.toNat % 4 = 0 ∧ Sep a 32 (sp0 + 0xFFFFFC90) 0x130

/-- A result slot in the frame: the 32 bytes at `d`, below the save slots. -/
def PDst (d : Nat) : Prop := 4 ≤ d ∧ d + 32 ≤ 0x224 ∧ d % 4 = 0

theorem sep_base0 {a b : Word} {n k : Nat} (h : Sep (a + BitVec.ofNat 32 0) n b k) : Sep a n b k := by
  rwa [add_ofNat_zero] at h

theorem sep_base0r {a b : Word} {n k : Nat} (h : Sep a n (b + BitVec.ofNat 32 0) k) : Sep a n b k := by
  rwa [add_ofNat_zero] at h

theorem paG_S (sp0 : Word) : sp0 + 0xFFFFFDC0 + 0xFFFFFED0 = sp0 + 0xFFFFFC90 := by
  rw [BitVec.add_assoc]; rfl

theorem paG_S2 (sp0 : Word) : sp0 + 0xFFFFFDC0 + 0xFFFFFF4C = sp0 + 0xFFFFFC90 + BitVec.ofNat 32 0x7C := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem paG_slot (sp0 : Word) (c : Nat) :
    sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c = sp0 + 0xFFFFFC90 + BitVec.ofNat 32 (0x130 + c) := by
  rw [← add_ofNat_assoc, show sp0 + 0xFFFFFDC0 = sp0 + 0xFFFFFC90 + BitVec.ofNat 32 0x130 from by
    rw [BitVec.add_assoc]; rfl]

section
variable {M0 : Word → BitVec 8} {P sp0 lhs rhs : Word}

theorem PAEnv.hG (env : PAEnv M0 P sp0 lhs rhs) : (sp0 + 0xFFFFFDC0).toNat = sp0.toNat - 0x240 := by
  have := env.hS
  rw [BitVec.toNat_add]; have : (0xFFFFFDC0 : Word).toNat = 4294966720 := rfl
  have := sp0.isLt; omega

theorem PAEnv.hGa (env : PAEnv M0 P sp0 lhs rhs) : (sp0 + 0xFFFFFDC0).toNat % 4 = 0 :=
  aligned_add env.hsp (k := 0xFFFFFDC0) (by decide)

/-- Code that is apart from `S` and `lhs` is still there. -/
theorem PAEnv.codeT (_env : PAEnv M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W : Nat}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 96)
    {b : Word} {code : List Nat} (hc : CodeIn M0 b code) (hs : Sep (sp0 + 0xFFFFFC90) 0x370 b code.length)
    (hl : Sep lhs 96 b code.length) : CodeIn M b code := fun i hi => by
  rw [fr _ (hs.subR (c := i) (l := 1) (by omega))
    ((sep_base0 (hl.sub (c := 0) (l := W) (by omega))).subR (c := i) (l := 1) (by omega))]
  exact hc i hi

theorem s130 {b : Word} {k : Nat} (h : Sep (sp0 + 0xFFFFFC90) 0x370 b k) : Sep (sp0 + 0xFFFFFC90) 0x130 b k :=
  sep_base0 (h.sub (c := 0) (l := 0x130) (by decide))

theorem s7C {b : Word} {k : Nat} (h : Sep (sp0 + 0xFFFFFC90) 0x370 b k) :
    Sep (sp0 + 0xFFFFFDC0 + 0xFFFFFF4C) 0xB4 b k := by
  rw [paG_S2]; exact h.sub (c := 0x7C) (l := 0xB4) (by decide)

theorem PDst.al {d : Nat} (env : PAEnv M0 P sp0 lhs rhs) (hd : PDst d) :
    (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d).toNat % 4 = 0 := aligned_add env.hGa hd.2.2

theorem PDst.wr {d : Nat} (env : PAEnv M0 P sp0 lhs rhs) (hd : PDst d) :
    (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d).toNat + 32 ≤ 2 ^ 32 := by
  have := env.hG; have := env.hS; have := sp0.isLt; have := hd.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem PDst.sS {d : Nat} (hd : PDst d) :
    Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 (sp0 + 0xFFFFFC90) 0x130 := by
  rw [paG_slot]
  exact sep_base0r (sep_offsets _ (c := 0x130 + d) (n := 32) (d := 0) (k := 0x130) (.inr (by omega))
    (by have := hd.2.1; omega) (by decide))

theorem PDst.inS {d : Nat} (hd : PDst d) {b : Word} {k : Nat} (h : Sep (sp0 + 0xFFFFFC90) 0x370 b k) :
    Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 b k := by
  rw [paG_slot]; exact h.sub (c := 0x130 + d) (l := 32) (by have := hd.2.1; omega)

/-- A frame slot below the save slots is an operand. -/
theorem psrc_slot {d : Nat} (env : PAEnv M0 P sp0 lhs rhs) (hd : PDst d) :
    PSrc sp0 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) := ⟨hd.al env, hd.sS⟩

/-- A coordinate of `lhs` is an operand. -/
theorem psrc_lhs (env : PAEnv M0 P sp0 lhs rhs) (k : Nat) (hk : k + 32 ≤ 96) (hk4 : k % 4 = 0) :
    PSrc sp0 (lhs + BitVec.ofNat 32 k) :=
  ⟨aligned_add env.hl hk4, sep_base0r ((env.sL.sub (c := k) (l := 32) hk).subR (c := 0) (l := 0x130) (by decide))⟩

/-- A coordinate of `rhs` is an operand. -/
theorem psrc_rhs (env : PAEnv M0 P sp0 lhs rhs) (k : Nat) (hk : k + 32 ≤ 96) (hk4 : k % 4 = 0) :
    PSrc sp0 (rhs + BitVec.ofNat 32 k) :=
  ⟨aligned_add env.hr hk4, sep_base0r ((env.sR.sub (c := k) (l := 32) hk).subR (c := 0) (l := 0x130) (by decide))⟩

/-- `b` is an operand. -/
theorem psrc_b (env : PAEnv M0 P sp0 lhs rhs) : PSrc sp0 bAddr :=
  ⟨by decide, sep_base0r (env.sK.subR (c := 0) (l := 0x130) (by decide))⟩

/-- The callee's stack and a result slot leave the save slots alone. -/
theorem sv_keep {d c : Nat} (hd : PDst d) (h1 : 0x224 ≤ c) (h2 : c < 0x240) :
    Sep (sp0 + 0xFFFFFC90) 0x130 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) 1 ∧
      Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) 1 := by
  refine ⟨?_, sep_offsets _ (.inl (by have := hd.2.1; omega)) (by have := hd.2.1; omega) (by omega)⟩
  rw [paG_slot]
  exact sep_base0 (sep_offsets _ (c := 0) (n := 0x130) (d := 0x130 + c) (k := 1) (.inl (by omega))
    (by decide) (by omega))

theorem pa_ret_even (env : PAEnv M0 P sp0 lhs rhs) {off : Nat} (hoff : off % 2 = 0) :
    (P + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = P + BitVec.ofNat 32 (off + 8) :=
  even_clear _ (even_at P env.hP (off + 8) (by omega))

/-- `FieldElement::multiply`'s environment, for a call from the point
addition with its result in the frame. -/
theorem PAEnv.fmEnv (env : PAEnv M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W d : Nat} {a b : Word}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 96)
    (hd : PDst d) (sa : PSrc sp0 a) (sb : PSrc sp0 b) :
    FMEnv M (P + 0xE838) (sp0 + 0xFFFFFDC0) (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) a b := by
  have cT := @PAEnv.codeT _ _ _ _ _ env M W fr hW
  have e1 : P + 0xE838 + 0xFFFFBEE4 = P + 0xA71C := by rw [BitVec.add_assoc]; rfl
  have e2 : P + 0xE838 + 0x3FC = P + 0xEC34 := by rw [BitVec.add_assoc]; rfl
  have e3 : P + 0xA71C + 0x1242A = P + 0x1CB46 := by rw [BitVec.add_assoc]; rfl
  have e4 : P + 0xA71C + 0x1241A = P + 0x1CB36 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0xA71C + 0x129E4 = P + 0x1D100 := by rw [BitVec.add_assoc]; rfl
  have e6 : P + 0xA71C + 0x12A4C = P + 0x1D168 := by rw [BitVec.add_assoc]; rfl
  have e7 : P + 0xA71C + 0x12A54 = P + 0x1D170 := by rw [BitVec.add_assoc]; rfl
  have hG := env.hG; have hS := env.hS
  refine ⟨even_at P env.hP 0xE838 (by decide), cT env.mul env.sMul env.lMul,
    by rw [e1]; exact cT env.wm env.sWm env.lWm, by rw [e1, e3]; exact cT env.wms env.sWms env.lWms,
    by rw [e1, e4]; exact cT env.wmr env.sWmr env.lWmr, by rw [e1, e5]; exact cT env.mset env.sMs env.lMs,
    by rw [e1, e6]; exact cT env.stub env.sU env.lU, by rw [e1, e7]; exact cT env.body env.sB env.lB,
    by rw [e2]; exact cT env.si env.sI env.lI, by rw [e2]; exact cT env.bsub env.sIb env.lIb,
    by rw [e2]; exact cT env.sis env.sIs env.lIs, by rw [e2]; exact cT env.sir env.sIr env.lIr,
    env.hGa, hd.al env, sa.1, sb.1, by omega, hd.wr env,
    by rw [paG_S]; exact s130 env.sMul, by rw [paG_S, e1]; exact s130 env.sWm,
    by rw [paG_S, e1, e3]; exact s130 env.sWms, by rw [paG_S, e1, e4]; exact s130 env.sWmr,
    by rw [paG_S, e1, e5]; exact s130 env.sMs, by rw [paG_S, e1, e6]; exact s130 env.sU,
    by rw [paG_S, e1, e7]; exact s130 env.sB, by rw [paG_S, e2]; exact s130 env.sI,
    by rw [paG_S, e2]; exact s130 env.sIb, by rw [paG_S, e2]; exact s130 env.sIs,
    by rw [paG_S, e2]; exact s130 env.sIr, by rw [paG_S]; exact hd.sS, hd.inS env.sMul,
    by rw [paG_S]; exact sa.2, by rw [paG_S]; exact sb.2⟩

/-- `field_impl::add`'s environment, for a call from the point addition. -/
theorem PAEnv.faEnv (env : PAEnv M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W d : Nat} {a b : Word}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 96)
    (hd : PDst d) (sa : PSrc sp0 a) (sb : PSrc sp0 b) :
    FAEnv M (P + 0xEF8A) (sp0 + 0xFFFFFDC0) (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) a b := by
  have cT := @PAEnv.codeT _ _ _ _ _ env M W fr hW
  have e : P + 0xEF8A + 0xFFFFFCAA = P + 0xEC34 := by rw [BitVec.add_assoc]; rfl
  have hG := env.hG; have hS := env.hS
  refine ⟨even_at P env.hP 0xEF8A (by decide), cT env.add env.sA env.lA,
    by rw [e]; exact cT env.si env.sI env.lI, by rw [e]; exact cT env.bsub env.sIb env.lIb,
    by rw [e]; exact cT env.sis env.sIs env.lIs, by rw [e]; exact cT env.sir env.sIr env.lIr,
    env.hGa, hd.al env, sa.1, sb.1, by omega, hd.wr env, s7C env.sA, by rw [e]; exact s7C env.sI,
    by rw [e]; exact s7C env.sIb, by rw [e]; exact s7C env.sIs, by rw [e]; exact s7C env.sIr,
    by rw [paG_S2]; exact hd.sS.subR (c := 0x7C) (l := 0xB4) (by decide), hd.inS env.sA,
    by rw [paG_S2]; exact sa.2.subR (c := 0x7C) (l := 0xB4) (by decide),
    by rw [paG_S2]; exact sb.2.subR (c := 0x7C) (l := 0xB4) (by decide)⟩

/-- `field_impl::sub`'s environment, for a call from the point addition. -/
theorem PAEnv.fsEnv (env : PAEnv M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W d : Nat} {a b : Word}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 96)
    (hd : PDst d) (sa : PSrc sp0 a) (sb : PSrc sp0 b) :
    FSEnv M (P + 0xF0AC) (sp0 + 0xFFFFFDC0) (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) a b := by
  have cT := @PAEnv.codeT _ _ _ _ _ env M W fr hW
  have e : P + 0xF0AC + 0xFFFFFB88 = P + 0xEC34 := by rw [BitVec.add_assoc]; rfl
  have hG := env.hG; have hS := env.hS
  refine ⟨even_at P env.hP 0xF0AC (by decide), cT env.sub env.sSb env.lSb,
    by rw [e]; exact cT env.si env.sI env.lI, by rw [e]; exact cT env.bsub env.sIb env.lIb,
    by rw [e]; exact cT env.sis env.sIs env.lIs, by rw [e]; exact cT env.sir env.sIr env.lIr,
    env.hGa, hd.al env, sa.1, sb.1, by omega, hd.wr env, s7C env.sSb, by rw [e]; exact s7C env.sI,
    by rw [e]; exact s7C env.sIb, by rw [e]; exact s7C env.sIs, by rw [e]; exact s7C env.sIr,
    by rw [paG_S2]; exact hd.sS.subR (c := 0x7C) (l := 0xB4) (by decide), hd.inS env.sSb,
    by rw [paG_S2]; exact sa.2.subR (c := 0x7C) (l := 0xB4) (by decide),
    by rw [paG_S2]; exact sb.2.subR (c := 0x7C) (l := 0xB4) (by decide)⟩

/-- After a call that changed only the callee's stack and a result slot, the
invariant holds at the return address. -/
theorem PAInv.after {M Ms M' : Word → BitVec 8} {V : Fin 32 → Word} {W d off : Nat} {n n' : Machine}
    (I : PAInv M0 P sp0 lhs V Ms W M n off) (hd : PDst d)
    (st : St M' P n' (off + 8) (reg n')) (keep : ∀ q, paKeep q = true → reg n' q = reg n q)
    (fr : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 →
      M' x = M x) :
    PAInv M0 P sp0 lhs V Ms W M' n' (off + 8) :=
  ⟨st, fun q hq => (keep q hq).trans (I.keep q hq),
    fun x hx hl => (fr x (hx.sub (c := 0) (l := 0x130) (by decide) |> sep_base0) (hd.inS hx)).trans (I.fr x hx hl),
    fun c h1 h2 => (fr _ (sv_keep hd h1 h2).1 (sv_keep hd h1 h2).2).trans (I.sv c h1 h2)⟩

end

section Calls
variable {M0 M Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {W off d : Nat}
  {n : Machine} {imm o a b : Word} {A B : Nat}

theorem keep_of_call {n1 n' : Machine} {L : Word} (regs1 : ∀ r, reg n1 r = upd (reg n) ra L r)
    (hz : reg n 0 = 0)
    (regs' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
      reg n' q = reg n1 q) :
    ∀ q, paKeep q = true → reg n' q = reg n q := fun q hq => by
  have k := fun r (hr : paKeep r = false) => bkeep_ne hq hr
  rw [regs' q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl)
    (k t0 rfl) (k t1 rfl) (k 7 rfl) (k 28 rfl) (k 29 rfl) (k 30 rfl) (k 31 rfl)]
  exact PEnv.reg1 regs1 hz q (k ra rfl)

set_option maxHeartbeats 1000000 in
/-- A call to `FieldElement::multiply` from the point addition: the result
slot gets the Montgomery product of the operands. -/
theorem pa_mul (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    (hVsp : V sp = sp0 + 0xFFFFFDC0)
    (h1 : fetchRel pointAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel pointAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xE838) (hoff : off % 2 = 0)
    (hd : PDst d) (ha0 : reg n a0 = sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d)
    (sa : PSrc sp0 a) (ha1 : reg n a1 = a) (sb : PSrc sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) (hB : limbVal (wordsAt M b 8) = B) (hBp : B < p256) :
    ∃ n' M', Steps n n' ∧ PAInv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 8) = fm A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0xE838 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', lt', fr'⟩ := fieldMul_correct n1
    (by rw [mem1]; exact env.fmEnv I.fr hW hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (pa_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA, hB] at val' lt'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [paG_S]; exact hx) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (keep_of_call regs1 I.st.zero regs') frS, frS, ?_⟩
  exact mont_fm (lt' (mul_lt_mont hAp hBp)) val'

set_option maxHeartbeats 1000000 in
/-- A call to `field_impl::add` from the point addition. -/
theorem pa_add (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    (hVsp : V sp = sp0 + 0xFFFFFDC0)
    (h1 : fetchRel pointAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel pointAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xEF8A) (hoff : off % 2 = 0)
    (hd : PDst d) (ha0 : reg n a0 = sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d)
    (sa : PSrc sp0 a) (ha1 : reg n a1 = a) (sb : PSrc sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) (hB : limbVal (wordsAt M b 8) = B) (hBp : B < p256) :
    ∃ n' M', Steps n n' ∧ PAInv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 8) = fa A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0xEF8A (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', fr'⟩ := fieldAdd_correct n1
    (by rw [mem1]; exact env.faEnv I.fr hW hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (pa_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA, hB] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [paG_S2]; exact hx.sub (c := 0x7C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (keep_of_call regs1 I.st.zero regs') frS, frS, ?_⟩
  rw [val', fa_eq hAp hBp]

set_option maxHeartbeats 1000000 in
/-- A call to `field_impl::sub` from the point addition. -/
theorem pa_sub (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    (hVsp : V sp = sp0 + 0xFFFFFDC0)
    (h1 : fetchRel pointAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel pointAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xF0AC) (hoff : off % 2 = 0)
    (hd : PDst d) (ha0 : reg n a0 = sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d)
    (sa : PSrc sp0 a) (ha1 : reg n a1 = a) (sb : PSrc sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) (hB : limbVal (wordsAt M b 8) = B) (hBp : B < p256) :
    ∃ n' M', Steps n n' ∧ PAInv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 8) = fs A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0xF0AC (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', fr'⟩ := fieldSub_correct n1
    (by rw [mem1]; exact env.fsEnv I.fr hW hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (pa_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA, hB] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [paG_S2]; exact hx.sub (c := 0x7C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (fun q hq => ?_) frS, frS, ?_⟩
  · have k := fun r (hr : paKeep r = false) => bkeep_ne hq hr
    rw [regs' q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl)
      (k t0 rfl)]
    exact r1 q (k ra rfl)
  · rw [val', fs_eq hAp hBp]

set_option maxHeartbeats 1000000 in
/-- A call to `FieldElement::double` from the point addition. -/
theorem pa_dbl (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    (hVsp : V sp = sp0 + 0xFFFFFDC0)
    (h1 : fetchRel pointAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel pointAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xF290) (hoff : off % 2 = 0)
    (hd : PDst d) (ha0 : reg n a0 = sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d)
    (sa : PSrc sp0 a) (ha1 : reg n a1 = a)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) :
    ∃ n' M', Steps n n' ∧ PAInv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 8) = fd A := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0xF290 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have e : P + 0xF290 + 0xFFFFFCFA = P + 0xEF8A := by rw [BitVec.add_assoc]; rfl
  have denv : FDEnv M (P + 0xF290) (sp0 + 0xFFFFFDC0) (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) a :=
    ⟨even_at P env.hP 0xF290 (by decide), env.codeT I.fr hW env.dbl env.sD env.lD,
      by rw [e]; exact env.faEnv I.fr hW hd sa sa⟩
  obtain ⟨n', c', pc', sp', regs', val', fr'⟩ := fieldDouble_correct n1 (by rw [mem1]; exact denv) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (pa_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [paG_S2]; exact hx.sub (c := 0x7C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (keep_of_call regs1 I.st.zero regs') frS, frS, ?_⟩
  rw [val', fd_eq hAp]

set_option maxHeartbeats 1000000 in
/-- A `memcpy` of a frame slot into the coordinate of `lhs` at `k`, the next
32 bytes of the result. -/
theorem pa_cpy {k : Nat} (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms k M n off)
    (hk : k + 32 ≤ 96) (hk4 : k % 4 = 0)
    (h1 : fetchRel pointAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel pointAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x1D168) (hoff : off % 2 = 0)
    (hd : PDst d) (ha0 : reg n a0 = lhs + BitVec.ofNat 32 k)
    (ha1 : reg n a1 = sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) (ha2 : reg n a2 = 0x20) :
    ∃ n' M', Steps n n' ∧ PAInv M0 P sp0 lhs V Ms (k + 32) M' n' (off + 8) ∧
      (∀ x, Sep (lhs + BitVec.ofNat 32 k) 32 x 1 → M' x = M x) ∧
      wordsAt M' (lhs + BitVec.ofNat 32 k) 8 = wordsAt M (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 8 := by
  have hW : k ≤ 96 := by omega
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0x1D168 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have e : P + 0x1D168 + 8 = P + 0x1D170 := by rw [BitVec.add_assoc]; rfl
  have hwl := env.hwl
  have hdw : (lhs + BitVec.ofNat 32 k).toNat = lhs.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sLk : Sep (lhs + BitVec.ofNat 32 k) 32 (sp0 + 0xFFFFFC90) 0x370 := env.sL.sub (c := k) (l := 32) hk
  obtain ⟨n', c', pc', mem', a0', regs'⟩ := memcpy_aligned n1 (P + 0x1D168) (P + BitVec.ofNat 32 (off + 8))
    (lhs + BitVec.ofNat 32 k) (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 8
    (fun i hi => by rw [mem1]; exact env.codeT I.fr hW env.stub env.sU env.lU i hi)
    (fun i hi => by rw [mem1, e]; exact env.codeT I.fr hW env.body env.sB env.lB i hi)
    (even_at P env.hP 0x1D168 (by decide)) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]; rfl)
    (by rw [regs1]; simp +decide [upd]) (pa_ret_even env hoff) (by decide) (by omega) (by decide)
    (aligned_add env.hl hk4) (hd.al env) (hd.inS sLk.symm).symm
    (by rw [e]; exact env.lB.sub (c := k) (l := 32) hk)
  rw [mem1] at mem'
  have out : ∀ x, Sep (lhs + BitVec.ofNat 32 k) 32 x 1 → n'.mem x = M x := fun x hx => by
    rw [mem']; exact copyWords_outside 8 hx
  refine ⟨n', n'.mem, c1.trans c', ⟨⟨by rw [pc'], rfl, fun _ => rfl⟩, fun q hq => ?_, fun x hx hl => ?_,
    fun c h1 h2 => ?_⟩, out, ?_⟩
  · have k' := fun r (hr : paKeep r = false) => bkeep_ne hq hr
    rw [regs' q (k' a1 rfl) (k' a2 rfl) (k' a3 rfl) (k' a4 rfl) (k' a5 rfl) (k' a6 rfl) (k' a7 rfl)
      (k' t0 rfl) (k' t1 rfl), r1 q (k' ra rfl)]
    exact I.keep q hq
  · rw [out x (hl.sub (c := k) (l := 32) (by omega))]
    exact I.fr x hx (sep_base0 (hl.sub (c := 0) (l := k) (by omega)))
  · rw [out _ (by rw [paG_slot]; exact sLk.subR (c := 0x130 + c) (l := 1) (by omega))]
    exact I.sv c h1 h2
  · rw [mem']
    unfold wordsAt
    exact List.map_congr_left fun i hi => copyWords_load 8 i (List.mem_range.mp hi) (by omega)

end Calls

section Keep
variable {M0 M M' Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {off : Nat} {n : Machine}

theorem bMont_lt : bMont < p256 := by decide

/-- Before any result is written, an operand outside `S` reads as on entry. -/
theorem PAInv.inp (I : PAInv M0 P sp0 lhs V Ms 0 M n off) {a : Word} (h : Sep a 32 (sp0 + 0xFFFFFC90) 0x370) :
    wordsAt M a 8 = wordsAt M0 a 8 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => I.fr _
    (by rw [add_ofNat_assoc]; exact h.symm.subR (c := 4 * i + j) (l := 1) (by omega))
    (fun _ h0 _ _ => absurd h0 (Nat.not_lt_zero _))

/-- A call that changed only the callee's stack and the slot at `d` left
the slot at `c` alone. -/
theorem slot_keep {d c : Nat}
    (f : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x)
    (hd : PDst d) (hc : PDst c) (hdc : d + 32 ≤ c ∨ c + 32 ≤ d) :
    wordsAt M' (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) 8 = wordsAt M (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) 8 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc (sp0 + 0xFFFFFDC0) c (4 * i), add_ofNat_assoc (sp0 + 0xFFFFFDC0) (c + 4 * i) j]
    have := hc.2.1; have := hd.2.1
    exact f _ (by
        rw [paG_slot]
        exact sep_base0 (sep_offsets _ (c := 0) (n := 0x130) (d := 0x130 + (c + 4 * i + j)) (k := 1)
          (.inl (by omega)) (by decide) (by omega)))
      (sep_offsets _ (c := d) (n := 32) (d := c + 4 * i + j) (k := 1)
        (by rcases hdc with h | h
            · exact .inl (by omega)
            · exact .inr (by omega)) (by omega) (by omega))

/-- A call that changed only `S` left the coordinate of `lhs` at `k` alone. -/
theorem lhs_keep (env : PAEnv M0 P sp0 lhs rhs) {d k : Nat}
    (f : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x130 x 1 → Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x)
    (hd : PDst d) (hk : k + 32 ≤ 96) :
    wordsAt M' (lhs + BitVec.ofNat 32 k) 8 = wordsAt M (lhs + BitVec.ofNat 32 k) 8 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc lhs k (4 * i), add_ofNat_assoc lhs (k + 4 * i) j]
    have hs := env.sL.sub (c := k + 4 * i + j) (l := 1) (by omega)
    exact f _ (s130 hs.symm) (hd.inS hs.symm)

/-- A `memcpy` into the coordinate of `lhs` at `k` left the frame slot at `c`
alone. -/
theorem slot_keep_cpy (env : PAEnv M0 P sp0 lhs rhs) {k c : Nat} (hk : k + 32 ≤ 96)
    (f : ∀ x, Sep (lhs + BitVec.ofNat 32 k) 32 x 1 → M' x = M x) (hc : PDst c) :
    wordsAt M' (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) 8 = wordsAt M (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) 8 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc (sp0 + 0xFFFFFDC0) c (4 * i), add_ofNat_assoc (sp0 + 0xFFFFFDC0) (c + 4 * i) j]
    exact f _ ((hc.inS (env.sL.sub (c := k) (l := 32) hk).symm).symm.subR (c := 4 * i + j) (l := 1) (by omega) |>
      fun h => by rw [add_ofNat_assoc] at h; simpa only [Nat.add_assoc] using h)

/-- A `memcpy` into the coordinate of `lhs` at `k` left the one at `k'`
alone. -/
theorem lhs_keep_cpy {k k' : Nat} (hk : k + 32 ≤ 96) (hk' : k' + 32 ≤ k)
    (f : ∀ x, Sep (lhs + BitVec.ofNat 32 k) 32 x 1 → M' x = M x) :
    wordsAt M' (lhs + BitVec.ofNat 32 k') 8 = wordsAt M (lhs + BitVec.ofNat 32 k') 8 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc lhs k' (4 * i), add_ofNat_assoc lhs (k' + 4 * i) j]
    exact f _ (sep_offsets _ (.inr (by omega)) (by omega) (by omega))

end Keep

section Steps
variable {M0 M Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {W off off' : Nat}
  {n : Machine}

/-- `addi rd, rs, imm` into a register `paKeep` doesn't name. -/
theorem pa_addi (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel pointAddCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : paKeep rd = false) :
    ∃ n', Steps n n' ∧ PAInv M0 P sp0 lhs V Ms W M n' off' ∧ reg n' rd = reg n rs + imm ∧
      ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.aluImm (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have h0 : rd.val ≠ 0 := fun h => by
    have : rd = 0 := Fin.ext h
    subst this; exact absurd hk (by decide)
  have ne : ∀ q, q ≠ rd → reg n' q = reg n q := fun q hq => by
    rw [u.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne hq0 hq
  exact ⟨n', .single d, ⟨u.self, fun q hq => (ne q (bkeep_ne hq hk)).trans (I.keep q hq), I.fr, I.sv⟩,
    by rw [u.regs, upd_same h0]; rfl, ne⟩

/-- `addi rd, rs, imm` into a register `paKeep` names: `V` changes there. -/
theorem pa_addiK (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel pointAddCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ PAInv M0 P sp0 lhs (upd V rd (reg n rs + imm)) Ms W M n' off' ∧
      reg n' rd = reg n rs + imm ∧ ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.aluImm (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have ne : ∀ q, q ≠ rd → reg n' q = reg n q := fun q hq => by
    rw [u.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne hq0 hq
  have same : reg n' rd = reg n rs + imm := by rw [u.regs, upd_same h0]; rfl
  refine ⟨n', .single d, ⟨u.self, fun q hq => ?_, I.fr, I.sv⟩, same, ne⟩
  by_cases hq0 : q.val = 0
  · have : q = 0 := Fin.ext hq0
    subst this; simp [upd]; exact u.self.zero
  by_cases e : q = rd
  · subst e; rw [same, upd_same h0]
  · rw [ne q e, upd_ne hq0 e]; exact I.keep q hq

/-- `lui rd, imm` into a register `paKeep` names. -/
theorem pa_luiK (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    {rd : Fin 32} {imm len : Word}
    (hf : fetchRel pointAddCode off = some (.lui rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ PAInv M0 P sp0 lhs (upd V rd imm) Ms W M n' off' ∧ reg n' rd = imm := by
  obtain ⟨n', d, u⟩ := I.st.lui (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have same : reg n' rd = imm := by rw [u.regs, upd_same h0]
  refine ⟨n', .single d, ⟨u.self, fun q hq => ?_, I.fr, I.sv⟩, same⟩
  by_cases hq0 : q.val = 0
  · have : q = 0 := Fin.ext hq0
    subst this; simp [upd]; exact u.self.zero
  by_cases e : q = rd
  · subst e; rw [same, upd_same h0]
  · rw [u.regs, upd_ne hq0 e, upd_ne hq0 e]; exact I.keep q hq

/-- `mv rd, rs` into a register `paKeep` doesn't name. -/
theorem pa_mv (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 96)
    {rd rs : Fin 32} {len : Word}
    (hf : fetchRel pointAddCode off = some (.alu .add rd 0 rs, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : paKeep rd = false) :
    ∃ n', Steps n n' ∧ PAInv M0 P sp0 lhs V Ms W M n' off' ∧ reg n' rd = reg n rs ∧
      ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.alu (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have h0 : rd.val ≠ 0 := fun h => by
    have : rd = 0 := Fin.ext h
    subst this; exact absurd hk (by decide)
  have ne : ∀ q, q ≠ rd → reg n' q = reg n q := fun q hq => by
    rw [u.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne hq0 hq
  exact ⟨n', .single d, ⟨u.self, fun q hq => (ne q (bkeep_ne hq hk)).trans (I.keep q hq), I.fr, I.sv⟩,
    by rw [u.regs, upd_same h0]; show reg n 0 + reg n rs = reg n rs; rw [I.st.zero]; exact BitVec.zero_add _, ne⟩

end Steps

/-- The registers the point addition saves, with their offsets in its frame. -/
abbrev paPs : List (Fin 32 × Nat) :=
  [(ra, 0x23C), ((8 : Fin 32), 0x238), ((9 : Fin 32), 0x234), ((18 : Fin 32), 0x230),
   ((19 : Fin 32), 0x22C), ((20 : Fin 32), 0x228), ((21 : Fin 32), 0x224)]

theorem pa_slot_addr (sp0 o : Word) (c : Nat) (h : (0x200 : Word) + o = BitVec.ofNat 32 c) :
    sp0 + 0xFFFFFDC0 + 0x200 + o = sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc (sp0 + 0xFFFFFDC0), h]

set_option maxHeartbeats 4000000 in
/-- The point addition's prologue, to 0x22: make the 0x240-byte frame, save
`ra` and `s0` through `s5` at its top, and keep the points' addresses in `s1`
and `s4`. -/
theorem pa_pro (m : Machine) {P sp0 lhs rhs : Word} (env : PAEnv m.mem P sp0 lhs rhs) (hpc : m.pc = P)
    (ha0 : reg m a0 = lhs) (ha1 : reg m a1 = rhs) (hsp : reg m sp = sp0) :
    ∃ n Ms, Steps m n ∧ PAInv m.mem P sp0 lhs (reg n) Ms 0 Ms n 0x22 ∧
      reg n sp = sp0 + 0xFFFFFDC0 ∧ reg n (9 : Fin 32) = rhs ∧ reg n (20 : Fin 32) = lhs ∧
      (∀ q, q ≠ sp → q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → reg n q = reg m q) ∧
      ∀ r c, (r, c) ∈ paPs → memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) = reg m r := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGa := env.hGa
  have F2 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → m.mem x = m.mem x := fun _ _ => rfl
  have codeS : ∀ {M' : Word → BitVec 8}, (∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M' x = m.mem x) →
      CodeIn M' P pointAddCode := fun hM i hi => by
    rw [hM _ (env.sC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have slotS : ∀ c, 0x224 ≤ c → c + 4 ≤ 0x240 → ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 →
      Sep (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 x hx => by
    rw [paG_slot]; exact hx.sub (by omega)
  obtain ⟨n1, d1, u1⟩ := s0.aluImm (codeS F2) pa_at_0 (off' := 4) (by decide)
  have e1 : reg n1 sp = sp0 + 0xFFFFFDC0 := by rw [u1.regs, upd_same (by decide), hsp]; rfl
  have k1 : ∀ q, q ≠ sp → reg n1 q = reg m q := fun q h => by
    rw [u1.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · exact upd_ne h0 h
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm (codeS F2) pa_at_4 (off' := 6) (by decide)
  have e2 : reg n2 a2 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [u2.regs, upd_same (by decide), e1]; rfl
  have k2 : ∀ q, q ≠ a2 → reg n2 q = reg n1 q := fun q h => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u1.self.zero.symm
    · exact upd_ne h0 h
  obtain ⟨n3, d3, u3⟩ := u2.self.sw (codeS F2) pa_at_6 (off' := 0xA) (by decide)
    (by rw [e2, pa_slot_addr sp0 0x3C 0x23C rfl]; exact aligned_add hGa (by decide))
  rw [e2, pa_slot_addr sp0 0x3C 0x23C rfl] at u3
  obtain ⟨M3, hM3⟩ : ∃ M, memStore32 m.mem (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x23C) (reg n2 ra) = M := ⟨_, rfl⟩
  rw [hM3] at u3
  have F3 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (slotS 0x23C (by decide) (by decide) x hx), F2 x hx]
  obtain ⟨n4, d4, u4⟩ := u3.sw (codeS F3) pa_at_a (off' := 0xC) (by decide)
    (by rw [e2, pa_slot_addr sp0 0x38 0x238 rfl]; exact aligned_add hGa (by decide))
  rw [e2, pa_slot_addr sp0 0x38 0x238 rfl] at u4
  obtain ⟨M4, hM4⟩ : ∃ M, memStore32 M3 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x238) (reg n2 (8 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM4] at u4
  have F4 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, memStore32_get_sep (slotS 0x238 (by decide) (by decide) x hx), F3 x hx]
  obtain ⟨n5, d5, u5⟩ := u4.sw (codeS F4) pa_at_c (off' := 0xE) (by decide)
    (by rw [e2, pa_slot_addr sp0 0x34 0x234 rfl]; exact aligned_add hGa (by decide))
  rw [e2, pa_slot_addr sp0 0x34 0x234 rfl] at u5
  obtain ⟨M5, hM5⟩ : ∃ M, memStore32 M4 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x234) (reg n2 (9 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM5] at u5
  have F5 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5, memStore32_get_sep (slotS 0x234 (by decide) (by decide) x hx), F4 x hx]
  obtain ⟨n6, d6, u6⟩ := u5.sw (codeS F5) pa_at_e (off' := 0x12) (by decide)
    (by rw [e2, pa_slot_addr sp0 0x30 0x230 rfl]; exact aligned_add hGa (by decide))
  rw [e2, pa_slot_addr sp0 0x30 0x230 rfl] at u6
  obtain ⟨M6, hM6⟩ : ∃ M, memStore32 M5 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x230) (reg n2 (18 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM6] at u6
  have F6 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M6 x = m.mem x := fun x hx => by
    rw [← hM6, memStore32_get_sep (slotS 0x230 (by decide) (by decide) x hx), F5 x hx]
  obtain ⟨n7, d7, u7⟩ := u6.sw (codeS F6) pa_at_12 (off' := 0x16) (by decide)
    (by rw [e2, pa_slot_addr sp0 0x2C 0x22C rfl]; exact aligned_add hGa (by decide))
  rw [e2, pa_slot_addr sp0 0x2C 0x22C rfl] at u7
  obtain ⟨M7, hM7⟩ : ∃ M, memStore32 M6 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x22C) (reg n2 (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM7] at u7
  have F7 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M7 x = m.mem x := fun x hx => by
    rw [← hM7, memStore32_get_sep (slotS 0x22C (by decide) (by decide) x hx), F6 x hx]
  obtain ⟨n8, d8, u8⟩ := u7.sw (codeS F7) pa_at_16 (off' := 0x1A) (by decide)
    (by rw [e2, pa_slot_addr sp0 0x28 0x228 rfl]; exact aligned_add hGa (by decide))
  rw [e2, pa_slot_addr sp0 0x28 0x228 rfl] at u8
  obtain ⟨M8, hM8⟩ : ∃ M, memStore32 M7 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x228) (reg n2 (20 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM8] at u8
  have F8 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8, memStore32_get_sep (slotS 0x228 (by decide) (by decide) x hx), F7 x hx]
  obtain ⟨n9, d9, u9⟩ := u8.sw (codeS F8) pa_at_1a (off' := 0x1E) (by decide)
    (by rw [e2, pa_slot_addr sp0 0x24 0x224 rfl]; exact aligned_add hGa (by decide))
  rw [e2, pa_slot_addr sp0 0x24 0x224 rfl] at u9
  obtain ⟨M9, hM9⟩ : ∃ M, memStore32 M8 (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x224) (reg n2 (21 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM9] at u9
  have F9 : ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → M9 x = m.mem x := fun x hx => by
    rw [← hM9, memStore32_get_sep (slotS 0x224 (by decide) (by decide) x hx), F8 x hx]
  obtain ⟨n10, d10, u10⟩ := u9.alu (codeS F9) pa_at_1e (off' := 0x20) (by decide)
  obtain ⟨n11, d11, u11⟩ := u10.self.alu (codeS F9) pa_at_20 (off' := 0x22) (by decide)
  have k11 : ∀ q, q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → reg n11 q = reg n2 q := fun q h9 h20 => by
    rw [u11.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u2.self.zero.symm
    · rw [upd_ne h0 h20, u10.regs, upd_ne h0 h9]
  refine ⟨n11, M9, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.single d11)))))))))),
    ⟨u11.self, fun _ _ => rfl, fun x hx _ => F9 x hx, fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k11 sp (by decide) (by decide), k2 sp (by decide), e1]
  · rw [u11.regs, upd_ne (by decide) (by decide), u10.regs, upd_same (by decide)]
    show reg n2 0 + reg n2 a1 = rhs
    rw [u2.self.zero, k2 a1 (by decide), k1 a1 (by decide), ha1]; exact BitVec.zero_add _
  · rw [u11.regs, upd_same (by decide)]
    show reg n10 0 + reg n10 a0 = lhs
    rw [u10.self.zero, u10.regs, upd_ne (by decide) (by decide), k2 a0 (by decide), k1 a0 (by decide), ha0]
    exact BitVec.zero_add _
  · intro q hsp' ha2 h9 h20
    rw [k11 q h9 h20, k2 q ha2, k1 q hsp']
  · intro r c h
    simp only [paPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [← hM9, ← hM8, ← hM7, ← hM6, ← hM5, ← hM4, ← hM3]
      simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
      rw [k2 _ (by decide), k1 _ (by decide)]

set_option maxHeartbeats 4000000 in
/-- The point addition's epilogue, from 0x2BC: restore `ra` and `s0` through
`s5` from the save slots, drop the frame, and return. -/
theorem pa_epi {M0 M Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {W : Nat} {n : Machine}
    (env : PAEnv M0 P sp0 lhs rhs) (I : PAInv M0 P sp0 lhs V Ms W M n 0x2BC) (hW : W ≤ 96)
    (hVsp : V sp = sp0 + 0xFFFFFDC0) :
    ∃ m', Steps n m' ∧ m'.pc = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x23C) &&& ~~~1 ∧ m'.mem = M ∧
      reg m' sp = sp0 ∧ (∀ r c, (r, c) ∈ paPs → reg m' r = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c)) ∧
      ∀ q, paKeep q = true → q ≠ sp → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → reg m' q = V q := by
  have cM := env.codeT I.fr hW env.code env.sC env.lC
  have hGa := env.hGa
  have ld : ∀ c, 0x224 ≤ c → c + 4 ≤ 0x240 →
      memLoad32 M (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact I.sv (c + j) (by omega) (by omega)
  obtain ⟨n1, d1, u1⟩ := I.st.aluImm cM pa_at_2bc (off' := 0x2BE) (by decide)
  have e1 : reg n1 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by
    rw [u1.regs, upd_same (by decide), I.keep sp rfl, hVsp]; rfl
  have k1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q h => by
    rw [u1.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne h0 h
  obtain ⟨n2, d2, u2⟩ := u1.self.lw cM pa_at_2be (off' := 0x2C2) (by decide)
    (by rw [e1, pa_slot_addr sp0 0x3C 0x23C rfl]; exact aligned_add hGa (by decide))
  have v2 : reg n2 ra = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x23C) := by
    rw [u2.regs, upd_same (by decide), e1, pa_slot_addr sp0 0x3C 0x23C rfl, ld _ (by decide) (by decide)]
  have k2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u1.self.zero.symm
    · exact upd_ne h0 h
  have a2 : reg n2 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [k2 a0 (by decide), e1]
  obtain ⟨n3, d3, u3⟩ := u2.self.lw cM pa_at_2c2 (off' := 0x2C4) (by decide)
    (by rw [a2, pa_slot_addr sp0 0x38 0x238 rfl]; exact aligned_add hGa (by decide))
  have v3 : reg n3 (8 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x238) := by
    rw [u3.regs, upd_same (by decide), a2, pa_slot_addr sp0 0x38 0x238 rfl, ld _ (by decide) (by decide)]
  have k3 : ∀ q, q ≠ (8 : Fin 32) → reg n3 q = reg n2 q := fun q h => by
    rw [u3.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u2.self.zero.symm
    · exact upd_ne h0 h
  have a3 : reg n3 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [k3 a0 (by decide), a2]
  obtain ⟨n4, d4, u4⟩ := u3.self.lw cM pa_at_2c4 (off' := 0x2C6) (by decide)
    (by rw [a3, pa_slot_addr sp0 0x34 0x234 rfl]; exact aligned_add hGa (by decide))
  have v4 : reg n4 (9 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x234) := by
    rw [u4.regs, upd_same (by decide), a3, pa_slot_addr sp0 0x34 0x234 rfl, ld _ (by decide) (by decide)]
  have k4 : ∀ q, q ≠ (9 : Fin 32) → reg n4 q = reg n3 q := fun q h => by
    rw [u4.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u3.self.zero.symm
    · exact upd_ne h0 h
  have a4 : reg n4 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [k4 a0 (by decide), a3]
  obtain ⟨n5, d5, u5⟩ := u4.self.lw cM pa_at_2c6 (off' := 0x2CA) (by decide)
    (by rw [a4, pa_slot_addr sp0 0x30 0x230 rfl]; exact aligned_add hGa (by decide))
  have v5 : reg n5 (18 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x230) := by
    rw [u5.regs, upd_same (by decide), a4, pa_slot_addr sp0 0x30 0x230 rfl, ld _ (by decide) (by decide)]
  have k5 : ∀ q, q ≠ (18 : Fin 32) → reg n5 q = reg n4 q := fun q h => by
    rw [u5.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u4.self.zero.symm
    · exact upd_ne h0 h
  have a5 : reg n5 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [k5 a0 (by decide), a4]
  obtain ⟨n6, d6, u6⟩ := u5.self.lw cM pa_at_2ca (off' := 0x2CE) (by decide)
    (by rw [a5, pa_slot_addr sp0 0x2C 0x22C rfl]; exact aligned_add hGa (by decide))
  have v6 : reg n6 (19 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x22C) := by
    rw [u6.regs, upd_same (by decide), a5, pa_slot_addr sp0 0x2C 0x22C rfl, ld _ (by decide) (by decide)]
  have k6 : ∀ q, q ≠ (19 : Fin 32) → reg n6 q = reg n5 q := fun q h => by
    rw [u6.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u5.self.zero.symm
    · exact upd_ne h0 h
  have a6 : reg n6 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [k6 a0 (by decide), a5]
  obtain ⟨n7, d7, u7⟩ := u6.self.lw cM pa_at_2ce (off' := 0x2D2) (by decide)
    (by rw [a6, pa_slot_addr sp0 0x28 0x228 rfl]; exact aligned_add hGa (by decide))
  have v7 : reg n7 (20 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x228) := by
    rw [u7.regs, upd_same (by decide), a6, pa_slot_addr sp0 0x28 0x228 rfl, ld _ (by decide) (by decide)]
  have k7 : ∀ q, q ≠ (20 : Fin 32) → reg n7 q = reg n6 q := fun q h => by
    rw [u7.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6.self.zero.symm
    · exact upd_ne h0 h
  have a7 : reg n7 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [k7 a0 (by decide), a6]
  obtain ⟨n8, d8, u8⟩ := u7.self.lw cM pa_at_2d2 (off' := 0x2D6) (by decide)
    (by rw [a7, pa_slot_addr sp0 0x24 0x224 rfl]; exact aligned_add hGa (by decide))
  have v8 : reg n8 (21 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFDC0 + BitVec.ofNat 32 0x224) := by
    rw [u8.regs, upd_same (by decide), a7, pa_slot_addr sp0 0x24 0x224 rfl, ld _ (by decide) (by decide)]
  have k8 : ∀ q, q ≠ (21 : Fin 32) → reg n8 q = reg n7 q := fun q h => by
    rw [u8.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u7.self.zero.symm
    · exact upd_ne h0 h
  have a8 : reg n8 a0 = sp0 + 0xFFFFFDC0 + 0x200 := by rw [k8 a0 (by decide), a7]
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm cM pa_at_2d6 (off' := 0x2DA) (by decide)
  have k9 : ∀ q, q ≠ sp → reg n9 q = reg n8 q := fun q h => by
    rw [u9.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u8.self.zero.symm
    · exact upd_ne h0 h
  obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.self.jalr cM pa_at_2da
  have back : ∀ q, q ≠ a0 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
      q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → reg n8 q = reg n q :=
    fun q h0 h1 h8 h9 h18 h19 h20 h21 => by
      rw [k8 q h21, k7 q h20, k6 q h19, k5 q h18, k4 q h9, k3 q h8, k2 q h1, k1 q h0]
  refine ⟨n10, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.single d10))))))))), ?_, mem10, ?_, ?_, ?_⟩
  · rw [pc10, k9 ra (by decide), k8 ra (by decide), k7 ra (by decide), k6 ra (by decide), k5 ra (by decide),
      k4 ra (by decide), k3 ra (by decide), v2, add_lit_zero]
  · rw [regs10, u9.regs, upd_same (by decide), back sp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), I.keep sp rfl, hVsp]
    show sp0 + 0xFFFFFDC0 + 0x240 = sp0
    rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · intro r c h
    rw [regs10]
    simp only [paPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide),
        k4 _ (by decide), k3 _ (by decide), v2]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide),
        k4 _ (by decide), v3]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), v4]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), v5]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), v6]
    · rw [k9 _ (by decide), k8 _ (by decide), v7]
    · rw [k9 _ (by decide), v8]
  · intro q hq hsp' h8 h9 h18 h19 h20 h21
    rw [regs10, k9 q hsp', back q (bkeep_ne hq (show paKeep a0 = false from rfl))
      (bkeep_ne hq (show paKeep ra = false from rfl)) h8 h9 h18 h19 h20 h21]
    exact I.keep q hq

end C3.RV32
