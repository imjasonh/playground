import C3BootProofs.Proofs.FeCall

/-!
# `EdwardsPoint ± ProjectiveNielsPoint`, as compiled

`<&EdwardsPoint as Add<&ProjectiveNielsPoint>>::add` computes the
`CompletedPoint` `(PP - MM, PP + MM, 2ZZ + TT2d, 2ZZ - TT2d)` with eleven
calls to the proved field add, sub, and mul, through stack temporaries.
`sub` is the same with the Niels point's `Y + X` and `Y - X` swapped and
the last two coordinates' add and sub swapped.
-/

namespace C3.RV32

open C3.Image

/-- Stores of each register of `ps` at its offset from register `b`, in
order. -/
def saveBlockR (b : Fin 32) (ps : List (Fin 32 × Word)) : List BInstr := ps.map fun p => .sw b p.1 p.2

/-- Loads of each register of `ps` from its offset from register `b`, in
order. -/
def restoreBlockR (b : Fin 32) (ps : List (Fin 32 × Word)) : List BInstr := ps.map fun p => .lw p.1 b p.2

theorem saveBlockR_run (b : Fin 32) (f : Fin 32 → Word) :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8), runBlock (saveBlockR b ps) (M, f) = (saveMem M (f b) f ps, f)
  | [], _ => rfl
  | (_, _) :: ps, _ => saveBlockR_run b f ps _

theorem saveBlockR_ok {base : Word} {len : Nat} (b : Fin 32) (f : Fin 32 → Word) :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8),
      (∀ p ∈ ps, (f b + p.2).toNat % 4 = 0 ∧ Sep (f b + p.2) 4 base len) → BlockOk base len (saveBlockR b ps) (M, f)
  | [], _, _ => trivial
  | (r, o) :: ps, _, h => ⟨h (r, o) List.mem_cons_self,
      saveBlockR_ok b f ps _ fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

theorem restoreBlockR_run (M : Word → BitVec 8) (G : Word) (b : Fin 32) (hb : b.val ≠ 0) :
    ∀ (ps : List (Fin 32 × Word)) (f : Fin 32 → Word), f b = G → (∀ p ∈ ps, p.1 ≠ b) →
      runBlock (restoreBlockR b ps) (M, f) = (M, restoreRegs M G f ps)
  | [], _, _, _ => rfl
  | (r, o) :: ps, f, hG, h => by
    have hr : r ≠ b := h (r, o) List.mem_cons_self
    have e : upd f r (memLoad32 M (f b + o)) b = G := by
      rw [← hG]; exact upd_ne hb (Ne.symm hr)
    show runBlock (restoreBlockR b ps) (M, upd f r (memLoad32 M (f b + o))) = _
    rw [restoreBlockR_run M G b hb ps _ e fun q hq => h q (List.mem_cons_of_mem _ hq), hG]
    rfl

theorem restoreBlockR_ok {base : Word} {len : Nat} (M : Word → BitVec 8) (G : Word) (b : Fin 32) (hb : b.val ≠ 0) :
    ∀ (ps : List (Fin 32 × Word)) (f : Fin 32 → Word), f b = G → (∀ p ∈ ps, p.1 ≠ b) →
      (∀ p ∈ ps, (G + p.2).toNat % 4 = 0) → BlockOk base len (restoreBlockR b ps) (M, f)
  | [], _, _, _, _ => trivial
  | (r, o) :: ps, f, hG, h, ha => by
    have hr : r ≠ b := h (r, o) List.mem_cons_self
    refine ⟨by show (f b + o).toNat % 4 = 0; rw [hG]; exact ha (r, o) List.mem_cons_self, ?_⟩
    refine restoreBlockR_ok M G b hb ps _ ?_ (fun q hq => h q (List.mem_cons_of_mem _ hq))
      (fun q hq => ha q (List.mem_cons_of_mem _ hq))
    show upd f r (memLoad32 M (f b + o)) b = G
    rw [← hG]; exact upd_ne hb (Ne.symm hr)

theorem feSubW_congr {x y x' y' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) (hy : ∀ i, i < 10 → y i = y' i) :
    feSubW x y = feSubW x' y' := by
  funext i
  unfold feSubW feSubSpec
  rw [hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide), hx 5 (by decide),
    hx 6 (by decide), hx 7 (by decide), hx 8 (by decide), hx 9 (by decide), hy 0 (by decide), hy 1 (by decide),
    hy 2 (by decide), hy 3 (by decide), hy 4 (by decide), hy 5 (by decide), hy 6 (by decide), hy 7 (by decide),
    hy 8 (by decide), hy 9 (by decide)]

theorem feMulW_congr {x y x' y' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) (hy : ∀ i, i < 10 → y i = y' i) :
    feMulW x y = feMulW x' y' := by
  funext i
  unfold feMulW
  rw [hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide), hx 5 (by decide),
    hx 6 (by decide), hx 7 (by decide), hx 8 (by decide), hx 9 (by decide), hy 0 (by decide), hy 1 (by decide),
    hy 2 (by decide), hy 3 (by decide), hy 4 (by decide), hy 5 (by decide), hy 6 (by decide), hy 7 (by decide),
    hy 8 (by decide), hy 9 (by decide)]

abbrev eanPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C)]

section
set_option maxRecDepth 20000
theorem ean_at_0 : fetchRel edAddNielsCode 0x0 = some (.aluImm .add sp sp 0xFFFFFED0, 2) := by decide
theorem ean_at_2 : fetchRel edAddNielsCode 0x2 = some (.aluImm .add a3 sp 0x100, 2) := by decide
theorem ean_at_4 : fetchRel edAddNielsCode 0x4 = some (.store .sw a3 ra 0x2C, 4) := by decide
theorem ean_at_8 : fetchRel edAddNielsCode 0x8 = some (.store .sw a3 (8 : Fin 32) 0x28, 2) := by decide
theorem ean_at_a : fetchRel edAddNielsCode 0xA = some (.store .sw a3 (9 : Fin 32) 0x24, 2) := by decide
theorem ean_at_c : fetchRel edAddNielsCode 0xC = some (.store .sw a3 (18 : Fin 32) 0x20, 4) := by decide
theorem ean_at_10 : fetchRel edAddNielsCode 0x10 = some (.store .sw a3 (19 : Fin 32) 0x1C, 4) := by decide
theorem ean_at_14 : fetchRel edAddNielsCode 0x14 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem ean_at_16 : fetchRel edAddNielsCode 0x16 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem ean_at_18 : fetchRel edAddNielsCode 0x18 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem ean_at_1a : fetchRel edAddNielsCode 0x1A = some (.aluImm .add (19 : Fin 32) a1 0x28, 4) := by decide
theorem ean_at_1e : fetchRel edAddNielsCode 0x1E = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ean_at_20 : fetchRel edAddNielsCode 0x20 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem ean_at_22 : fetchRel edAddNielsCode 0x22 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem ean_at_24 : fetchRel edAddNielsCode 0x24 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ean_at_28 : fetchRel edAddNielsCode 0x28 = some (.jalr ra ra 0x77A, 4) := by decide
theorem ean_at_2c : fetchRel edAddNielsCode 0x2C = some (.aluImm .add a0 sp 0x2C, 2) := by decide
theorem ean_at_2e : fetchRel edAddNielsCode 0x2E = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem ean_at_30 : fetchRel edAddNielsCode 0x30 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem ean_at_32 : fetchRel edAddNielsCode 0x32 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ean_at_36 : fetchRel edAddNielsCode 0x36 = some (.jalr ra ra 0x7BA, 4) := by decide
theorem ean_at_3a : fetchRel edAddNielsCode 0x3A = some (.aluImm .add a0 sp 0x54, 2) := by decide
theorem ean_at_3c : fetchRel edAddNielsCode 0x3C = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem ean_at_3e : fetchRel edAddNielsCode 0x3E = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem ean_at_40 : fetchRel edAddNielsCode 0x40 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ean_at_44 : fetchRel edAddNielsCode 0x44 = some (.jalr ra ra 0x3EA, 4) := by decide
theorem ean_at_48 : fetchRel edAddNielsCode 0x48 = some (.aluImm .add a2 (9 : Fin 32) 0x28, 4) := by decide
theorem ean_at_4c : fetchRel edAddNielsCode 0x4C = some (.aluImm .add a0 sp 0x7C, 2) := by decide
theorem ean_at_4e : fetchRel edAddNielsCode 0x4E = some (.aluImm .add a1 sp 0x2C, 2) := by decide
theorem ean_at_50 : fetchRel edAddNielsCode 0x50 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ean_at_54 : fetchRel edAddNielsCode 0x54 = some (.jalr ra ra 0x3DA, 4) := by decide
theorem ean_at_58 : fetchRel edAddNielsCode 0x58 = some (.aluImm .add a1 (8 : Fin 32) 0x78, 4) := by decide
theorem ean_at_5c : fetchRel edAddNielsCode 0x5C = some (.aluImm .add a2 (9 : Fin 32) 0x78, 4) := by decide
theorem ean_at_60 : fetchRel edAddNielsCode 0x60 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem ean_at_62 : fetchRel edAddNielsCode 0x62 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ean_at_66 : fetchRel edAddNielsCode 0x66 = some (.jalr ra ra 0x3C8, 4) := by decide
theorem ean_at_6a : fetchRel edAddNielsCode 0x6A = some (.aluImm .add a1 (8 : Fin 32) 0x50, 4) := by decide
theorem ean_at_6e : fetchRel edAddNielsCode 0x6E = some (.aluImm .add a2 (9 : Fin 32) 0x50, 4) := by decide
theorem ean_at_72 : fetchRel edAddNielsCode 0x72 = some (.aluImm .add a0 sp 0xCC, 2) := by decide
theorem ean_at_74 : fetchRel edAddNielsCode 0x74 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ean_at_78 : fetchRel edAddNielsCode 0x78 = some (.jalr ra ra 0x3B6, 4) := by decide
theorem ean_at_7c : fetchRel edAddNielsCode 0x7C = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem ean_at_7e : fetchRel edAddNielsCode 0x7E = some (.aluImm .add a1 sp 0xCC, 2) := by decide
theorem ean_at_80 : fetchRel edAddNielsCode 0x80 = some (.aluImm .add a2 sp 0xCC, 2) := by decide
theorem ean_at_82 : fetchRel edAddNielsCode 0x82 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ean_at_86 : fetchRel edAddNielsCode 0x86 = some (.jalr ra ra 0x71C, 4) := by decide
theorem ean_at_8a : fetchRel edAddNielsCode 0x8A = some (.aluImm .add a1 sp 0x54, 2) := by decide
theorem ean_at_8c : fetchRel edAddNielsCode 0x8C = some (.aluImm .add a2 sp 0x7C, 2) := by decide
theorem ean_at_8e : fetchRel edAddNielsCode 0x8E = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem ean_at_90 : fetchRel edAddNielsCode 0x90 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ean_at_94 : fetchRel edAddNielsCode 0x94 = some (.jalr ra ra 0x75C, 4) := by decide
theorem ean_at_98 : fetchRel edAddNielsCode 0x98 = some (.aluImm .add a0 (18 : Fin 32) 0x28, 4) := by decide
theorem ean_at_9c : fetchRel edAddNielsCode 0x9C = some (.aluImm .add a1 sp 0x54, 2) := by decide
theorem ean_at_9e : fetchRel edAddNielsCode 0x9E = some (.aluImm .add a2 sp 0x7C, 2) := by decide
theorem ean_at_a0 : fetchRel edAddNielsCode 0xA0 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ean_at_a4 : fetchRel edAddNielsCode 0xA4 = some (.jalr ra ra 0x6FE, 4) := by decide
theorem ean_at_a8 : fetchRel edAddNielsCode 0xA8 = some (.aluImm .add a0 (18 : Fin 32) 0x50, 4) := by decide
theorem ean_at_ac : fetchRel edAddNielsCode 0xAC = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem ean_at_ae : fetchRel edAddNielsCode 0xAE = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem ean_at_b0 : fetchRel edAddNielsCode 0xB0 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ean_at_b4 : fetchRel edAddNielsCode 0xB4 = some (.jalr ra ra 0x6EE, 4) := by decide
theorem ean_at_b8 : fetchRel edAddNielsCode 0xB8 = some (.aluImm .add a0 (18 : Fin 32) 0x78, 4) := by decide
theorem ean_at_bc : fetchRel edAddNielsCode 0xBC = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem ean_at_be : fetchRel edAddNielsCode 0xBE = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem ean_at_c0 : fetchRel edAddNielsCode 0xC0 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ean_at_c4 : fetchRel edAddNielsCode 0xC4 = some (.jalr ra ra 0x72C, 4) := by decide
theorem ean_at_c8 : fetchRel edAddNielsCode 0xC8 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem ean_at_ca : fetchRel edAddNielsCode 0xCA = some (.load .lw ra a0 0x2C, 4) := by decide
theorem ean_at_ce : fetchRel edAddNielsCode 0xCE = some (.load .lw (8 : Fin 32) a0 0x28, 2) := by decide
theorem ean_at_d0 : fetchRel edAddNielsCode 0xD0 = some (.load .lw (9 : Fin 32) a0 0x24, 2) := by decide
theorem ean_at_d2 : fetchRel edAddNielsCode 0xD2 = some (.load .lw (18 : Fin 32) a0 0x20, 4) := by decide
theorem ean_at_d6 : fetchRel edAddNielsCode 0xD6 = some (.load .lw (19 : Fin 32) a0 0x1C, 4) := by decide
theorem ean_at_da : fetchRel edAddNielsCode 0xDA = some (.aluImm .add sp sp 0x130, 2) := by decide
theorem ean_at_dc : fetchRel edAddNielsCode 0xDC = some (.jalr x0 ra 0x0, 2) := by decide
theorem eanSave_end : blockEnd edAddNielsCode 4 (saveBlockR a3 eanPs) = some 0x14 := by decide
theorem eanRestore_end : blockEnd edAddNielsCode 0xCA (restoreBlockR a0 eanPs) = some 0xDA := by decide
end

/-- `b` and the `n` bytes after it are apart from `add`'s code and every
function it calls. -/
structure EanCode (P b : Word) (n : Nat) : Prop where
  c : Sep b n P edAddNielsCode.length
  a : Sep b n (P + 0xFFFFE79E) feAddCode.length
  aS : Sep b n (P + 0xFFFFE79E + 0x5D88) memcpyStubCode.length
  aB : Sep b n (P + 0xFFFFE79E + 0x5D90) memcpyBodyCode.length
  s : Sep b n (P + 0xFFFFE7EC) feSubCode.length
  sR : Sep b n (P + 0xFFFFE7EC + 0xFFFFF72E) feReduceCode.length
  m : Sep b n (P + 0xFFFFD42A) feMulCode.length
  mR : Sep b n (P + 0xFFFFD42A + 0xAF0) feReduceCode.length

theorem EanCode.sub {P b : Word} {n : Nat} (h : EanCode P b n) {c l : Nat} (hl : c + l ≤ n) :
    EanCode P (b + BitVec.ofNat 32 c) l :=
  ⟨h.c.sub hl, h.a.sub hl, h.aS.sub hl, h.aB.sub hl, h.s.sub hl, h.sR.sub hl, h.m.sub hl, h.mR.sub hl⟩

/-- Where `add` runs: its code and its callees', the 0x270 bytes of stack
below `sp0`, the point at `ep`, the Niels point at `np`, and the result at
`out`, apart from what each must not touch. -/
structure EANEnv (M : Word → BitVec 8) (P sp0 out ep np : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P edAddNielsCode
  add : CodeIn M (P + 0xFFFFE79E) feAddCode
  addS : CodeIn M (P + 0xFFFFE79E + 0x5D88) memcpyStubCode
  addB : CodeIn M (P + 0xFFFFE79E + 0x5D90) memcpyBodyCode
  sub : CodeIn M (P + 0xFFFFE7EC) feSubCode
  subR : CodeIn M (P + 0xFFFFE7EC + 0xFFFFF72E) feReduceCode
  mul : CodeIn M (P + 0xFFFFD42A) feMulCode
  mulR : CodeIn M (P + 0xFFFFD42A + 0xAF0) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x270 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hep : ep.toNat % 4 = 0
  hnp : np.toNat % 4 = 0
  how : out.toNat + 0xA0 < 2 ^ 32
  hew : ep.toNat + 0xA0 < 2 ^ 32
  hnw : np.toNat + 0xA0 < 2 ^ 32
  sG : EanCode P (sp0 + 0xFFFFFD90) 0x270
  sO : EanCode P out 0xA0
  sOG : Sep out 0xA0 (sp0 + 0xFFFFFD90) 0x270
  sEG : Sep ep 0xA0 (sp0 + 0xFFFFFD90) 0x270
  sNG : Sep np 0xA0 (sp0 + 0xFFFFFD90) 0x270
  sEO : Sep ep 0xA0 out 0xA0
  sNO : Sep np 0xA0 out 0xA0

/-- The registers `add` keeps across its calls: `sp` at its frame, the
operand and result pointers in `s0` through `s3`, and the rest as the caller
left them. -/
def EanRegs (m nm : Machine) (F out ep np : Word) : Prop :=
  reg nm sp = F ∧ reg nm 8 = ep ∧ reg nm 9 = np ∧ reg nm 18 = out ∧ reg nm 19 = ep + 0x28 ∧
    ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q

theorem EanRegs.tr {m nm nm' : Machine} {F out ep np : Word} (h : EanRegs m nm F out ep np)
    (k : ∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm' q = reg nm q) :
    EanRegs m nm' F out ep np :=
  ⟨by rw [k sp (by decide)]; exact h.1, by rw [k 8 (by decide)]; exact h.2.1, by rw [k 9 (by decide)]; exact h.2.2.1,
    by rw [k 18 (by decide)]; exact h.2.2.2.1, by rw [k 19 (by decide)]; exact h.2.2.2.2.1,
    fun q hq => by rw [k q (by revert hq; revert q; decide)]; exact h.2.2.2.2.2 q hq⟩

/-- `PP = (Y + X)·(Y + X)ₙ`. -/
def eanPP (M : Word → BitVec 8) (ep np : Word) : Nat → Word :=
  feMulW (feAddW (limbs M (ep + 0x28)) (limbs M ep)) (limbs M np)

/-- `MM = (Y - X)·(Y - X)ₙ`. -/
def eanMM (M : Word → BitVec 8) (ep np : Word) : Nat → Word :=
  feMulW (feSubW (limbs M (ep + 0x28)) (limbs M ep)) (limbs M (np + 0x28))

/-- `TT2d = T·(2dT)ₙ`. -/
def eanTT (M : Word → BitVec 8) (ep np : Word) : Nat → Word :=
  feMulW (limbs M (ep + 0x78)) (limbs M (np + 0x78))

/-- `ZZ2 = ZZ + ZZ` for `ZZ = Z·Zₙ`. -/
def eanZZ2 (M : Word → BitVec 8) (ep np : Word) : Nat → Word :=
  feAddW (feMulW (limbs M (ep + 0x50)) (limbs M (np + 0x50))) (feMulW (limbs M (ep + 0x50)) (limbs M (np + 0x50)))

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `<&EdwardsPoint as Add<&ProjectiveNielsPoint>>::add`**:
from the point at `ep` and the Niels point at `np`, it stores at `out` the
limbs of `PP - MM`, `PP + MM`, `ZZ2 + TT2d`, and `ZZ2 - TT2d` as the field
operations compute them. -/
theorem edAddNiels_correct (m : Machine) {P sp0 out ep np retAddr : Word} (env : EANEnv m.mem P sp0 out ep np)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ep) (ha2 : reg m a2 = np)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ i, i < 10 →
        limbs m'.mem out i = feSubW (eanPP m.mem ep np) (eanMM m.mem ep np) i ∧
        limbs m'.mem (out + 0x28) i = feAddW (eanPP m.mem ep np) (eanMM m.mem ep np) i ∧
        limbs m'.mem (out + 0x50) i = feAddW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i ∧
        limbs m'.mem (out + 0x78) i = feSubW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i) ∧
      ∀ x, Sep (sp0 + 0xFFFFFD90) 0x270 x 1 → Sep out 0xA0 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFD90 = G := ⟨_, rfl⟩
  have sG := env.sG; have sOG := env.sOG; have sEG := env.sEG; have sNG := env.sNG
  rw [hG] at sG sOG sEG sNG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFED0 = F := ⟨_, rfl⟩
  have hGF : G + BitVec.ofNat 32 0x140 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFD90) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x140) (by decide)
  have hGw : G.toNat + 0x270 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFD90 : Word).toNat = 4294966672 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x140 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have gw : G.toNat + 0x270 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have eS : F + 0x130 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x140 + k) := fun k => by rw [← hGF, add_ofNat_assoc]
  have eFm : F + 0xFFFFFEC0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eA : F + 0x100 = G + BitVec.ofNat 32 0x240 := by rw [← hGF, BitVec.add_assoc]; rfl
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x270 → d + k ≤ 0x270 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have g0 : ∀ {a : Word} {n : Nat}, Sep a n G 0x270 → Sep a n G 0x140 := fun h => by
    have := h.subR (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have g0' : ∀ {b : Word} {l : Nat}, Sep G 0x270 b l → Sep G 0x140 b l := fun h => by
    have := h.sub (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have zg : ∀ {z : Word}, Sep G 0x270 z 1 → Sep G 0x140 z 1 := fun h => by
    have := h.sub (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x270 b code'.length → Sep out 0xA0 b code'.length →
      (∀ x, Sep G 0x270 x 1 → Sep out 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs ho hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- temporaries at `F + c`, the result's quarters at `out + k`
  have tS : ∀ c, c + 40 ≤ 0x11C → Sep (F + BitVec.ofNat 32 c) 40 G 0x140 := fun c h => by
    rw [eFk]; have := offs (c := 0x140 + c) (n := 40) (d := 0) (k := 0x140) (.inr (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have tC : ∀ c, c + 40 ≤ 0x11C → EanCode P (F + BitVec.ofNat 32 c) 40 := fun c h => by
    rw [eFk]; exact sG.sub (by omega)
  have tA : ∀ c, c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hFa h
  have tW : ∀ c, c + 40 ≤ 0x11C → (F + BitVec.ofNat 32 c).toNat + 40 < 2 ^ 32 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  have tIn : ∀ c, c + 40 ≤ 0x11C → ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep (F + BitVec.ofNat 32 c) 40 z 1 :=
    fun c h z hz _ => by rw [eFk]; exact hz.sub (by omega)
  have tT : ∀ c d, c + 40 ≤ d ∨ d + 40 ≤ c → c + 40 ≤ 0x11C → d + 40 ≤ 0x11C →
      Sep (F + BitVec.ofNat 32 c) 40 (F + BitVec.ofNat 32 d) 40 := fun c d h h1 h2 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have tSl : ∀ c k, c + 40 ≤ 0x11C → 0x25C ≤ k → k < 0x270 → Sep (F + BitVec.ofNat 32 c) 40 (G + BitVec.ofNat 32 k) 1 :=
    fun c k h h1 h2 => by rw [eFk]; exact offs (.inl (by omega)) (by omega) (by omega)
  have tO : ∀ c k, c + 40 ≤ 0x11C → k + 40 ≤ 0xA0 → Sep (F + BitVec.ofNat 32 c) 40 (out + BitVec.ofNat 32 k) 40 :=
    fun c k h1 h2 => by rw [eFk]; exact ((sOG.sub (c := k) (l := 40) h2).subR (c := 0x140 + c) (l := 40) (by omega)).symm
  have oS : ∀ k, k + 40 ≤ 0xA0 → Sep (out + BitVec.ofNat 32 k) 40 G 0x140 := fun k h => g0 (sOG.sub h)
  have oA : ∀ k, k % 4 = 0 → (out + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k h => aligned_add env.hout h
  have oW : ∀ k, k + 40 ≤ 0xA0 → (out + BitVec.ofNat 32 k).toNat + 40 < 2 ^ 32 := fun k h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.how; omega
  have oIn : ∀ k, k + 40 ≤ 0xA0 → ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep (out + BitVec.ofNat 32 k) 40 z 1 :=
    fun k h z _ hz => hz.sub h
  have oSl : ∀ k j, k + 40 ≤ 0xA0 → j < 0x270 → Sep (out + BitVec.ofNat 32 k) 40 (G + BitVec.ofNat 32 j) 1 :=
    fun k j h hj => (sOG.sub (c := k) (l := 40) h).subR (by omega)
  have oT : ∀ k k', k + 40 ≤ k' ∨ k' + 40 ≤ k → k + 40 ≤ 0xA0 → k' + 40 ≤ 0xA0 →
      Sep (out + BitVec.ofNat 32 k) 40 (out + BitVec.ofNat 32 k') 40 := fun k k' h h1 h2 =>
    sep_offsets out h (by omega) (by omega)
  -- the operands' limbs stay as they were
  have epK : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ c i, c + 40 ≤ 0xA0 → i < 10 → limbs M (ep + BitVec.ofNat 32 c) i = limbs m.mem (ep + BitVec.ofNat 32 c) i :=
    fun hM c i h hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact hM _ (sEG.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
        (env.sEO.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
  have npK : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ c i, c + 40 ≤ 0xA0 → i < 10 → limbs M (np + BitVec.ofNat 32 c) i = limbs m.mem (np + BitVec.ofNat 32 c) i :=
    fun hM c i h hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact hM _ (sNG.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
        (env.sNO.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
  have pers : ∀ {M M' : Word → BitVec 8} {o a : Word}, (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      Sep a 40 G 0x140 → Sep a 40 o 40 → ∀ i, i < 10 → limbs M' a i = limbs M a i :=
    fun hM h1 h2 i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact hM _ (h1.sub (c := 4 * i + j) (l := 1) (by omega)).symm (h2.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have invStep : ∀ {M M' : Word → BitVec 8} {o : Word}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep o 40 z 1) →
      ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M' z = m.mem z :=
    fun hI hM ho z h1 h2 => by rw [hM z (zg h1) (ho z h1 h2), hI z h1 h2]
  have mulCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x y : Word),
      St M P nm off (reg nm) → CodeIn M P edAddNielsCode →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      fetchRel edAddNielsCode off = some (.auipc ra imm, 4) →
      fetchRel edAddNielsCode (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0xFFFFD42A → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = y →
      o.toNat % 4 = 0 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → EanCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 → Sep y 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feMulW (limbs M x) (limbs M y) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x y s hc hI h1 h2 hb hev hs e0 e1 e2 hoa hxa hya hoc soG sxG syG
    have e : FeMEnv M (P + 0xFFFFD42A) (reg nm sp) (reg nm a0) (reg nm a1) (reg nm a2) := by
      rw [hs, e0, e1, e2]
      exact ⟨even_at P env.hP 0xFFFFD42A (by decide), cIn env.mul sG.m env.sO.m hI, cIn env.mulR sG.mR env.sO.mR hI,
        hFa, by omega, hoa, hxa, hya, by rw [eFm]; exact g0' sG.m, by rw [eFm]; exact g0' sG.mR, hoc.m, hoc.mR,
        by rw [eFm]; exact soG, by rw [eFm]; exact sxG, by rw [eFm]; exact syG⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeMul hc h1 h2 hb (even_at P env.hP (off + 8) hev) e
    rw [e0, e1, e2] at w1; rw [hs, e0, eFm] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, f1⟩
  have addCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x y : Word),
      St M P nm off (reg nm) → CodeIn M P edAddNielsCode →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      fetchRel edAddNielsCode off = some (.auipc ra imm, 4) →
      fetchRel edAddNielsCode (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0xFFFFE79E → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = y →
      o.toNat + 40 < 2 ^ 32 → x.toNat + 40 < 2 ^ 32 → y.toNat % 4 = 0 → EanCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 → Sep y 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feAddW (limbs M x) (limbs M y) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x y s hc hI h1 h2 hb hev hs e0 e1 e2 how hxw hya hoc soG sxG syG
    have e : FeAddEnv M (P + 0xFFFFE79E) (G + BitVec.ofNat 32 0xF0) (reg nm a0) (reg nm a1) (reg nm a2) := by
      rw [e0, e1, e2]
      exact ⟨even_at P env.hP 0xFFFFE79E (by decide), cIn env.add sG.a env.sO.a hI, cIn env.addS sG.aS env.sO.aS hI,
        cIn env.addB sG.aB env.sO.aB hI, aligned_add hGa (by decide),
        by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hya, how, hxw,
        sG.a.sub (by decide), sG.aS.sub (by decide), sG.aB.sub (by decide), hoc.a, hoc.aB,
        soG.subR (by decide), sxG.subR (by decide), syG.subR (by decide)⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeAdd hc h1 h2 hb (even_at P env.hP (off + 8) hev)
      (by rw [hs, ← hGF, BitVec.add_assoc]; rfl) e
    rw [e0, e1, e2] at w1; rw [e0] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, fun z hz ho => f1 z (hz.sub (by decide)) ho⟩
  have subCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x y : Word),
      St M P nm off (reg nm) → CodeIn M P edAddNielsCode →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      fetchRel edAddNielsCode off = some (.auipc ra imm, 4) →
      fetchRel edAddNielsCode (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0xFFFFE7EC → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = y →
      o.toNat % 4 = 0 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → EanCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 → Sep y 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feSubW (limbs M x) (limbs M y) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x y s hc hI h1 h2 hb hev hs e0 e1 e2 hoa hxa hya hoc soG sxG syG
    have e : FeSubEnv M (P + 0xFFFFE7EC) (G + BitVec.ofNat 32 0x90) (reg nm a0) (reg nm a1) (reg nm a2) := by
      rw [e0, e1, e2]
      exact ⟨even_at P env.hP 0xFFFFE7EC (by decide), cIn env.sub sG.s env.sO.s hI, cIn env.subR sG.sR env.sO.sR hI,
        aligned_add hGa (by decide), by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hxa, hya, hoa,
        sG.s.sub (by decide), sG.sR.sub (by decide), hoc.s,
        soG.subR (by decide), sxG.subR (by decide), syG.subR (by decide)⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeSub hc h1 h2 hb (even_at P env.hP (off + 8) hev)
      (by rw [hs, ← hGF, BitVec.add_assoc]; rfl) e
    rw [e0, e1, e2] at w1; rw [e0] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, fun z hz ho => f1 z (hz.sub (by decide)) ho⟩
  have eS0 : Sep ep 40 G 0x140 := by have := g0 (sEG.sub (c := 0) (l := 40) (by decide)); rwa [add_ofNat_zero] at this
  have nS0 : Sep np 40 G 0x140 := by have := g0 (sNG.sub (c := 0) (l := 40) (by decide)); rwa [add_ofNat_zero] at this
  have eSk : ∀ k, k + 40 ≤ 0xA0 → Sep (ep + BitVec.ofNat 32 k) 40 G 0x140 := fun k h => g0 (sEG.sub h)
  have nSk : ∀ k, k + 40 ≤ 0xA0 → Sep (np + BitVec.ofNat 32 k) 40 G 0x140 := fun k h => g0 (sNG.sub h)
  have eW : ∀ k, k + 40 ≤ 0xA0 → (ep + BitVec.ofNat 32 k).toNat + 40 < 2 ^ 32 := fun k h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.hew; omega
  have ep0K : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M ep i = limbs m.mem ep i := fun hM i hi => by
    have := epK hM 0 i (by decide) hi; rwa [add_ofNat_zero] at this
  have np0K : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M np i = limbs m.mem np i := fun hM i hi => by
    have := npK hM 0 i (by decide) hi; rwa [add_ofNat_zero] at this
  have gk : ∀ k, 0x140 ≤ k → k < 0x270 → Sep G 0x140 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    have := offs (c := 0) (n := 0x140) (d := k) (k := 1) (.inl (by omega)) (by decide) (by omega)
    rwa [add_ofNat_zero] at this
  -- the prologue
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod ean_at_0 (off' := 2) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm env.cod ean_at_2 (off' := 4) (by decide)
  have r2 : ∀ q, q.val ≠ 0 → q ≠ sp → q ≠ a3 → reg m2 q = reg m q := fun q hv hs h3 => by
    rw [u2.regs, upd_ne hv h3, upd_ne hv hs]
  have sp2 : reg m2 sp = F := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have a3v : reg m2 a3 = G + BitVec.ofNat 32 0x240 := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ev_add, hsp, hF, eA]
  have slA : ∀ (o : Word), 0x1C ≤ o.toNat → o.toNat + 4 ≤ 0x30 → ∀ {b : Word} {l : Nat}, Sep G 0x270 b l →
      Sep (G + BitVec.ofNat 32 0x240 + o) 4 b l := fun o h1 h2 b l h => by
    rw [← ofNat_toNat_self o, add_ofNat_assoc]; exact h.sub (by omega)
  obtain ⟨m3, cp3, u3⟩ := St.block (saveBlockR a3 eanPs) u2.self env.cod eanSave_end
    (saveBlockR_ok a3 _ eanPs _ fun p hp => by
      rw [a3v]
      simp only [eanPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add (aligned_add hGa (k := 0x240) (by decide)) (by decide), slA _ (by decide) (by decide) sG.c⟩)
  simp only [saveBlockR_run] at u3
  rw [a3v] at u3
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (G + BitVec.ofNat 32 0x240) (reg m2) eanPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u3
  have frSv : ∀ x, Sep G 0x270 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside eanPs fun p hp => by
      simp only [eanPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact slA _ (by decide) (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ eanPs → memLoad32 Msv (G + BitVec.ofNat 32 0x240 + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [eanPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      exact r2 _ (by decide) (by decide) (by decide)
  have inv0 : ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Msv z = m.mem z := fun z h _ => frSv z h
  have hcS : CodeIn Msv P edAddNielsCode := cIn env.cod sG.c env.sO.c inv0
  obtain ⟨m4, cp4, u4⟩ := St.block [.alu .add (9 : Fin 32) x0 a2, .alu .add (8 : Fin 32) x0 a1,
    .alu .add (18 : Fin 32) x0 a0, .aluImm .add (19 : Fin 32) a1 0x28] u3.self hcS (off' := 0x1E) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u4
  have R4 : EanRegs m m4 F out ep np := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.regs, sp2]
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a1 (by decide) (by decide) (by decide), ha1]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a2 (by decide) (by decide) (by decide), ha2]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a0 (by decide) (by decide) (by decide), ha0]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a1 (by decide) (by decide) (by decide), ha1]
    · have h : q.val ≠ 0 ∧ q ≠ 9 ∧ q ≠ 8 ∧ q ≠ 18 ∧ q ≠ 19 ∧ q ≠ sp ∧ q ≠ a3 := by revert hq; revert q; decide
      rw [u4.regs, upd_ne h.1 h.2.2.2.2.1, upd_ne h.1 h.2.2.2.1, upd_ne h.1 h.2.2.1, upd_ne h.1 h.2.1, u3.regs,
        r2 q h.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2]
  have oC0 : EanCode P out 40 := by have := env.sO.sub (c := 0) (l := 40) (by decide); rwa [add_ofNat_zero] at this
  have oS0 : Sep out 40 G 0x140 := by have := oS 0 (by decide); rwa [add_ofNat_zero] at this
  have oIn0 : ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep out 40 z 1 := fun z _ hz => by
    have := hz.sub (c := 0) (l := 40) (by decide); rwa [add_ofNat_zero] at this
  have oSl0 : ∀ j, j < 0x270 → Sep out 40 (G + BitVec.ofNat 32 j) 1 := fun j hj => by
    have := oSl 0 j (by decide) hj; rwa [add_ofNat_zero] at this
  have slot0 : ∀ k, 0x25C ≤ k → k < 0x270 → Msv (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun _ _ _ => rfl
  -- call 1
  obtain ⟨b1, cb1, ub1⟩ := St.block [.aluImm .add a0 sp 0x4, .alu .add a1 x0 (19 : Fin 32), .alu .add a2 x0 (8 : Fin 32)] u4.self hcS
    (off' := 0x24) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub1
  have rb1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b1 q = reg m4 q := fun q hv h0 h1 h2 => by
    rw [ub1.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := addCall (F + BitVec.ofNat 32 4) (ep + 0x28) ep ub1.self hcS inv0
    ean_at_24 ean_at_28 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb1 sp (by decide) (by decide) (by decide) (by decide)]; exact R4.1)
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (tW 4 (by decide)) (eW 0x28 (by decide)) (env.hep) (tC 4 (by decide)) (tS 4 (by decide)) (eSk 0x28 (by decide)) (eS0)
  have inv1 := invStep inv0 f1 (tIn 4 (by decide))
  have hc1 : CodeIn n1.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv1
  have slot1 : ∀ k, 0x25C ≤ k → k < 0x270 → n1.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f1 _ (gk k (by omega) h2) (tSl 4 k (by decide) h1 h2)).trans (slot0 k h1 h2)
  have R1 : EanRegs m n1 F out ep np := R4.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k1 q h.2.2.2.2.2 h.2.2.2.2.1, rb1 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 2
  obtain ⟨b2, cb2, ub2⟩ := St.block [.aluImm .add a0 sp 0x2C, .alu .add a1 x0 (19 : Fin 32), .alu .add a2 x0 (8 : Fin 32)] u1 hc1
    (off' := 0x32) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub2
  have rb2 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b2 q = reg n1 q := fun q hv h0 h1 h2 => by
    rw [ub2.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := subCall (F + BitVec.ofNat 32 0x2C) (ep + 0x28) ep ub2.self hc1 inv1
    ean_at_32 ean_at_36 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb2 sp (by decide) (by decide) (by decide) (by decide)]; exact R1.1)
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R1.1, R1.2.1, R1.2.2.1, R1.2.2.2.1, R1.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u1.zero]; first | rfl | exact zw _))
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R1.1, R1.2.1, R1.2.2.1, R1.2.2.2.1, R1.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u1.zero]; first | rfl | exact zw _))
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R1.1, R1.2.1, R1.2.2.1, R1.2.2.2.1, R1.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u1.zero]; first | rfl | exact zw _))
    (tA 0x2C (by decide)) (aligned_add env.hep (by decide)) (env.hep) (tC 0x2C (by decide)) (tS 0x2C (by decide)) (eSk 0x28 (by decide)) (eS0)
  have inv2 := invStep inv1 f2 (tIn 0x2C (by decide))
  have hc2 : CodeIn n2.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv2
  have slot2 : ∀ k, 0x25C ≤ k → k < 0x270 → n2.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f2 _ (gk k (by omega) h2) (tSl 0x2C k (by decide) h1 h2)).trans (slot1 k h1 h2)
  have R2 : EanRegs m n2 F out ep np := R1.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k2 q h.2.2.2.2.2 h.2.2.2.2.1, rb2 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 3
  obtain ⟨b3, cb3, ub3⟩ := St.block [.aluImm .add a0 sp 0x54, .aluImm .add a1 sp 0x4, .alu .add a2 x0 (9 : Fin 32)] u2 hc2
    (off' := 0x40) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub3
  have rb3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b3 q = reg n2 q := fun q hv h0 h1 h2 => by
    rw [ub3.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n3, c3, u3, sp3, k3, w3, f3⟩ := mulCall (F + BitVec.ofNat 32 0x54) (F + BitVec.ofNat 32 4) np ub3.self hc2 inv2
    ean_at_40 ean_at_44 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb3 sp (by decide) (by decide) (by decide) (by decide)]; exact R2.1)
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R2.1, R2.2.1, R2.2.2.1, R2.2.2.2.1, R2.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u2.zero]; first | rfl | exact zw _))
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R2.1, R2.2.1, R2.2.2.1, R2.2.2.2.1, R2.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u2.zero]; first | rfl | exact zw _))
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R2.1, R2.2.1, R2.2.2.1, R2.2.2.2.1, R2.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u2.zero]; first | rfl | exact zw _))
    (tA 0x54 (by decide)) (tA 4 (by decide)) (env.hnp) (tC 0x54 (by decide)) (tS 0x54 (by decide)) (tS 4 (by decide)) (nS0)
  have inv3 := invStep inv2 f3 (tIn 0x54 (by decide))
  have hc3 : CodeIn n3.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv3
  have slot3 : ∀ k, 0x25C ≤ k → k < 0x270 → n3.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f3 _ (gk k (by omega) h2) (tSl 0x54 k (by decide) h1 h2)).trans (slot2 k h1 h2)
  have R3 : EanRegs m n3 F out ep np := R2.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k3 q h.2.2.2.2.2 h.2.2.2.2.1, rb3 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 4
  obtain ⟨b4, cb4, ub4⟩ := St.block [.aluImm .add a2 (9 : Fin 32) 0x28, .aluImm .add a0 sp 0x7C, .aluImm .add a1 sp 0x2C] u3 hc3
    (off' := 0x50) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub4
  have rb4 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b4 q = reg n3 q := fun q hv h0 h1 h2 => by
    rw [ub4.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n4, c4, u4, sp4, k4, w4, f4⟩ := mulCall (F + BitVec.ofNat 32 0x7C) (F + BitVec.ofNat 32 0x2C) (np + 0x28) ub4.self hc3 inv3
    ean_at_50 ean_at_54 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb4 sp (by decide) (by decide) (by decide) (by decide)]; exact R3.1)
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R3.1, R3.2.1, R3.2.2.1, R3.2.2.2.1, R3.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u3.zero]; first | rfl | exact zw _))
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R3.1, R3.2.1, R3.2.2.1, R3.2.2.2.1, R3.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u3.zero]; first | rfl | exact zw _))
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R3.1, R3.2.1, R3.2.2.1, R3.2.2.2.1, R3.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u3.zero]; first | rfl | exact zw _))
    (tA 0x7C (by decide)) (tA 0x2C (by decide)) (aligned_add env.hnp (by decide)) (tC 0x7C (by decide)) (tS 0x7C (by decide)) (tS 0x2C (by decide)) (nSk 0x28 (by decide))
  have inv4 := invStep inv3 f4 (tIn 0x7C (by decide))
  have hc4 : CodeIn n4.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv4
  have slot4 : ∀ k, 0x25C ≤ k → k < 0x270 → n4.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f4 _ (gk k (by omega) h2) (tSl 0x7C k (by decide) h1 h2)).trans (slot3 k h1 h2)
  have R4 : EanRegs m n4 F out ep np := R3.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k4 q h.2.2.2.2.2 h.2.2.2.2.1, rb4 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 5
  obtain ⟨b5, cb5, ub5⟩ := St.block [.aluImm .add a1 (8 : Fin 32) 0x78, .aluImm .add a2 (9 : Fin 32) 0x78, .aluImm .add a0 sp 0xA4] u4 hc4
    (off' := 0x62) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub5
  have rb5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b5 q = reg n4 q := fun q hv h0 h1 h2 => by
    rw [ub5.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n5, c5, u5, sp5, k5, w5, f5⟩ := mulCall (F + BitVec.ofNat 32 0xA4) (ep + 0x78) (np + 0x78) ub5.self hc4 inv4
    ean_at_62 ean_at_66 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb5 sp (by decide) (by decide) (by decide) (by decide)]; exact R4.1)
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.zero]; first | rfl | exact zw _))
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.zero]; first | rfl | exact zw _))
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.zero]; first | rfl | exact zw _))
    (tA 0xA4 (by decide)) (aligned_add env.hep (by decide)) (aligned_add env.hnp (by decide)) (tC 0xA4 (by decide)) (tS 0xA4 (by decide)) (eSk 0x78 (by decide)) (nSk 0x78 (by decide))
  have inv5 := invStep inv4 f5 (tIn 0xA4 (by decide))
  have hc5 : CodeIn n5.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv5
  have slot5 : ∀ k, 0x25C ≤ k → k < 0x270 → n5.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f5 _ (gk k (by omega) h2) (tSl 0xA4 k (by decide) h1 h2)).trans (slot4 k h1 h2)
  have R5 : EanRegs m n5 F out ep np := R4.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k5 q h.2.2.2.2.2 h.2.2.2.2.1, rb5 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 6
  obtain ⟨b6, cb6, ub6⟩ := St.block [.aluImm .add a1 (8 : Fin 32) 0x50, .aluImm .add a2 (9 : Fin 32) 0x50, .aluImm .add a0 sp 0xCC] u5 hc5
    (off' := 0x74) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub6
  have rb6 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b6 q = reg n5 q := fun q hv h0 h1 h2 => by
    rw [ub6.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n6, c6, u6, sp6, k6, w6, f6⟩ := mulCall (F + BitVec.ofNat 32 0xCC) (ep + 0x50) (np + 0x50) ub6.self hc5 inv5
    ean_at_74 ean_at_78 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb6 sp (by decide) (by decide) (by decide) (by decide)]; exact R5.1)
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R5.1, R5.2.1, R5.2.2.1, R5.2.2.2.1, R5.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u5.zero]; first | rfl | exact zw _))
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R5.1, R5.2.1, R5.2.2.1, R5.2.2.2.1, R5.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u5.zero]; first | rfl | exact zw _))
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R5.1, R5.2.1, R5.2.2.1, R5.2.2.2.1, R5.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u5.zero]; first | rfl | exact zw _))
    (tA 0xCC (by decide)) (aligned_add env.hep (by decide)) (aligned_add env.hnp (by decide)) (tC 0xCC (by decide)) (tS 0xCC (by decide)) (eSk 0x50 (by decide)) (nSk 0x50 (by decide))
  have inv6 := invStep inv5 f6 (tIn 0xCC (by decide))
  have hc6 : CodeIn n6.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv6
  have slot6 : ∀ k, 0x25C ≤ k → k < 0x270 → n6.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f6 _ (gk k (by omega) h2) (tSl 0xCC k (by decide) h1 h2)).trans (slot5 k h1 h2)
  have R6 : EanRegs m n6 F out ep np := R5.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k6 q h.2.2.2.2.2 h.2.2.2.2.1, rb6 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 7
  obtain ⟨b7, cb7, ub7⟩ := St.block [.aluImm .add a0 sp 0xF4, .aluImm .add a1 sp 0xCC, .aluImm .add a2 sp 0xCC] u6 hc6
    (off' := 0x82) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub7
  have rb7 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b7 q = reg n6 q := fun q hv h0 h1 h2 => by
    rw [ub7.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n7, c7, u7, sp7, k7, w7, f7⟩ := addCall (F + BitVec.ofNat 32 0xF4) (F + BitVec.ofNat 32 0xCC) (F + BitVec.ofNat 32 0xCC) ub7.self hc6 inv6
    ean_at_82 ean_at_86 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb7 sp (by decide) (by decide) (by decide) (by decide)]; exact R6.1)
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R6.1, R6.2.1, R6.2.2.1, R6.2.2.2.1, R6.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u6.zero]; first | rfl | exact zw _))
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R6.1, R6.2.1, R6.2.2.1, R6.2.2.2.1, R6.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u6.zero]; first | rfl | exact zw _))
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R6.1, R6.2.1, R6.2.2.1, R6.2.2.2.1, R6.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u6.zero]; first | rfl | exact zw _))
    (tW 0xF4 (by decide)) (tW 0xCC (by decide)) (tA 0xCC (by decide)) (tC 0xF4 (by decide)) (tS 0xF4 (by decide)) (tS 0xCC (by decide)) (tS 0xCC (by decide))
  have inv7 := invStep inv6 f7 (tIn 0xF4 (by decide))
  have hc7 : CodeIn n7.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv7
  have slot7 : ∀ k, 0x25C ≤ k → k < 0x270 → n7.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f7 _ (gk k (by omega) h2) (tSl 0xF4 k (by decide) h1 h2)).trans (slot6 k h1 h2)
  have R7 : EanRegs m n7 F out ep np := R6.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k7 q h.2.2.2.2.2 h.2.2.2.2.1, rb7 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 8
  obtain ⟨b8, cb8, ub8⟩ := St.block [.aluImm .add a1 sp 0x54, .aluImm .add a2 sp 0x7C, .alu .add a0 x0 (18 : Fin 32)] u7 hc7
    (off' := 0x90) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub8
  have rb8 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b8 q = reg n7 q := fun q hv h0 h1 h2 => by
    rw [ub8.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n8, c8, u8, sp8, k8, w8, f8⟩ := subCall out (F + BitVec.ofNat 32 0x54) (F + BitVec.ofNat 32 0x7C) ub8.self hc7 inv7
    ean_at_90 ean_at_94 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb8 sp (by decide) (by decide) (by decide) (by decide)]; exact R7.1)
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R7.1, R7.2.1, R7.2.2.1, R7.2.2.2.1, R7.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u7.zero]; first | rfl | exact zw _))
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R7.1, R7.2.1, R7.2.2.1, R7.2.2.2.1, R7.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u7.zero]; first | rfl | exact zw _))
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R7.1, R7.2.1, R7.2.2.1, R7.2.2.2.1, R7.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u7.zero]; first | rfl | exact zw _))
    (env.hout) (tA 0x54 (by decide)) (tA 0x7C (by decide)) (oC0) (oS0) (tS 0x54 (by decide)) (tS 0x7C (by decide))
  have inv8 := invStep inv7 f8 (oIn0)
  have hc8 : CodeIn n8.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv8
  have slot8 : ∀ k, 0x25C ≤ k → k < 0x270 → n8.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f8 _ (gk k (by omega) h2) (oSl0 k (by omega))).trans (slot7 k h1 h2)
  have R8 : EanRegs m n8 F out ep np := R7.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k8 q h.2.2.2.2.2 h.2.2.2.2.1, rb8 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 9
  obtain ⟨b9, cb9, ub9⟩ := St.block [.aluImm .add a0 (18 : Fin 32) 0x28, .aluImm .add a1 sp 0x54, .aluImm .add a2 sp 0x7C] u8 hc8
    (off' := 0xa0) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub9
  have rb9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b9 q = reg n8 q := fun q hv h0 h1 h2 => by
    rw [ub9.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n9, c9, u9, sp9, k9, w9, f9⟩ := addCall (out + 0x28) (F + BitVec.ofNat 32 0x54) (F + BitVec.ofNat 32 0x7C) ub9.self hc8 inv8
    ean_at_a0 ean_at_a4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb9 sp (by decide) (by decide) (by decide) (by decide)]; exact R8.1)
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R8.1, R8.2.1, R8.2.2.1, R8.2.2.2.1, R8.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u8.zero]; first | rfl | exact zw _))
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R8.1, R8.2.1, R8.2.2.1, R8.2.2.2.1, R8.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u8.zero]; first | rfl | exact zw _))
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R8.1, R8.2.1, R8.2.2.1, R8.2.2.2.1, R8.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u8.zero]; first | rfl | exact zw _))
    (oW 0x28 (by decide)) (tW 0x54 (by decide)) (tA 0x7C (by decide)) (env.sO.sub (by decide)) (oS 0x28 (by decide)) (tS 0x54 (by decide)) (tS 0x7C (by decide))
  have inv9 := invStep inv8 f9 (oIn 0x28 (by decide))
  have hc9 : CodeIn n9.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv9
  have slot9 : ∀ k, 0x25C ≤ k → k < 0x270 → n9.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f9 _ (gk k (by omega) h2) (oSl 0x28 k (by decide) (by omega))).trans (slot8 k h1 h2)
  have R9 : EanRegs m n9 F out ep np := R8.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k9 q h.2.2.2.2.2 h.2.2.2.2.1, rb9 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 10
  obtain ⟨b10, cb10, ub10⟩ := St.block [.aluImm .add a0 (18 : Fin 32) 0x50, .aluImm .add a1 sp 0xF4, .aluImm .add a2 sp 0xA4] u9 hc9
    (off' := 0xb0) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub10
  have rb10 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b10 q = reg n9 q := fun q hv h0 h1 h2 => by
    rw [ub10.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n10, c10, u10, sp10, k10, w10, f10⟩ := addCall (out + 0x50) (F + BitVec.ofNat 32 0xF4) (F + BitVec.ofNat 32 0xA4) ub10.self hc9 inv9
    ean_at_b0 ean_at_b4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb10 sp (by decide) (by decide) (by decide) (by decide)]; exact R9.1)
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R9.1, R9.2.1, R9.2.2.1, R9.2.2.2.1, R9.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u9.zero]; first | rfl | exact zw _))
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R9.1, R9.2.1, R9.2.2.1, R9.2.2.2.1, R9.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u9.zero]; first | rfl | exact zw _))
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R9.1, R9.2.1, R9.2.2.1, R9.2.2.2.1, R9.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u9.zero]; first | rfl | exact zw _))
    (oW 0x50 (by decide)) (tW 0xF4 (by decide)) (tA 0xA4 (by decide)) (env.sO.sub (by decide)) (oS 0x50 (by decide)) (tS 0xF4 (by decide)) (tS 0xA4 (by decide))
  have inv10 := invStep inv9 f10 (oIn 0x50 (by decide))
  have hc10 : CodeIn n10.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv10
  have slot10 : ∀ k, 0x25C ≤ k → k < 0x270 → n10.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f10 _ (gk k (by omega) h2) (oSl 0x50 k (by decide) (by omega))).trans (slot9 k h1 h2)
  have R10 : EanRegs m n10 F out ep np := R9.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k10 q h.2.2.2.2.2 h.2.2.2.2.1, rb10 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 11
  obtain ⟨b11, cb11, ub11⟩ := St.block [.aluImm .add a0 (18 : Fin 32) 0x78, .aluImm .add a1 sp 0xF4, .aluImm .add a2 sp 0xA4] u10 hc10
    (off' := 0xc0) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub11
  have rb11 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b11 q = reg n10 q := fun q hv h0 h1 h2 => by
    rw [ub11.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n11, c11, u11, sp11, k11, w11, f11⟩ := subCall (out + 0x78) (F + BitVec.ofNat 32 0xF4) (F + BitVec.ofNat 32 0xA4) ub11.self hc10 inv10
    ean_at_c0 ean_at_c4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb11 sp (by decide) (by decide) (by decide) (by decide)]; exact R10.1)
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R10.1, R10.2.1, R10.2.2.1, R10.2.2.2.1, R10.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u10.zero]; first | rfl | exact zw _))
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R10.1, R10.2.1, R10.2.2.1, R10.2.2.2.1, R10.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u10.zero]; first | rfl | exact zw _))
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R10.1, R10.2.1, R10.2.2.1, R10.2.2.2.1, R10.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u10.zero]; first | rfl | exact zw _))
    (aligned_add env.hout (by decide)) (tA 0xF4 (by decide)) (tA 0xA4 (by decide)) (env.sO.sub (by decide)) (oS 0x78 (by decide)) (tS 0xF4 (by decide)) (tS 0xA4 (by decide))
  have inv11 := invStep inv10 f11 (oIn 0x78 (by decide))
  have hc11 : CodeIn n11.mem P edAddNielsCode := cIn env.cod sG.c env.sO.c inv11
  have slot11 : ∀ k, 0x25C ≤ k → k < 0x270 → n11.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f11 _ (gk k (by omega) h2) (oSl 0x78 k (by decide) (by omega))).trans (slot10 k h1 h2)
  have R11 : EanRegs m n11 F out ep np := R10.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k11 q h.2.2.2.2.2 h.2.2.2.2.1, rb11 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]

  -- what each call stored, in terms of the operands
  have oT0 : ∀ k, 40 ≤ k → k + 40 ≤ 0xA0 → Sep out 40 (out + BitVec.ofNat 32 k) 40 := fun k h1 h2 => by
    have := oT 0 k (.inl (by omega)) (by decide) h2; rwa [add_ofNat_zero] at this
  have E28 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (ep + 0x28) i = limbs m.mem (ep + 0x28) i := fun hM i hi => epK hM 0x28 i (by decide) hi
  have E50 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (ep + 0x50) i = limbs m.mem (ep + 0x50) i := fun hM i hi => epK hM 0x50 i (by decide) hi
  have E78 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (ep + 0x78) i = limbs m.mem (ep + 0x78) i := fun hM i hi => epK hM 0x78 i (by decide) hi
  have N28 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (np + 0x28) i = limbs m.mem (np + 0x28) i := fun hM i hi => npK hM 0x28 i (by decide) hi
  have N50 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (np + 0x50) i = limbs m.mem (np + 0x50) i := fun hM i hi => npK hM 0x50 i (by decide) hi
  have N78 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (np + 0x78) i = limbs m.mem (np + 0x78) i := fun hM i hi => npK hM 0x78 i (by decide) hi
  have tP : ∀ {M M' : Word → BitVec 8} {o : Word} (c : Nat), (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      c + 40 ≤ 0x11C → Sep (F + BitVec.ofNat 32 c) 40 o 40 → ∀ i, i < 10 →
      limbs M' (F + BitVec.ofNat 32 c) i = limbs M (F + BitVec.ofNat 32 c) i :=
    fun c hM hc ho i hi => pers hM (tS c hc) ho i hi
  have V1 : ∀ i, i < 10 → limbs n1.mem (F + BitVec.ofNat 32 4) i =
      feAddW (limbs m.mem (ep + 0x28)) (limbs m.mem ep) i := fun i hi => by
    rw [w1 i hi]; unfold feAddW
    rw [E28 inv0 i hi, ep0K inv0 i hi]
  have V2 : ∀ i, i < 10 → limbs n2.mem (F + BitVec.ofNat 32 0x2C) i =
      feSubW (limbs m.mem (ep + 0x28)) (limbs m.mem ep) i := fun i hi => by
    rw [w2 i hi, feSubW_congr (E28 inv1) (ep0K inv1)]
  have V3 : ∀ i, i < 10 → limbs n3.mem (F + BitVec.ofNat 32 0x54) i = eanPP m.mem ep np i := fun i hi => by
    rw [w3 i hi, feMulW_congr (x' := feAddW (limbs m.mem (ep + 0x28)) (limbs m.mem ep)) (y' := limbs m.mem np)
      (fun j hj => by
        rw [tP 4 f2 (by decide) (tT 4 0x2C (.inl (by decide)) (by decide) (by decide)) j hj]; exact V1 j hj)
      (np0K inv2)]
    rfl
  have V4 : ∀ i, i < 10 → limbs n4.mem (F + BitVec.ofNat 32 0x7C) i = eanMM m.mem ep np i := fun i hi => by
    rw [w4 i hi, feMulW_congr (x' := feSubW (limbs m.mem (ep + 0x28)) (limbs m.mem ep)) (y' := limbs m.mem (np + 0x28))
      (fun j hj => by
        rw [tP 0x2C f3 (by decide) (tT 0x2C 0x54 (.inl (by decide)) (by decide) (by decide)) j hj]; exact V2 j hj)
      (N28 inv3)]
    rfl
  have V5 : ∀ i, i < 10 → limbs n5.mem (F + BitVec.ofNat 32 0xA4) i = eanTT m.mem ep np i := fun i hi => by
    rw [w5 i hi, feMulW_congr (x' := limbs m.mem (ep + 0x78)) (y' := limbs m.mem (np + 0x78)) (E78 inv4) (N78 inv4)]
    rfl
  have V6 : ∀ i, i < 10 → limbs n6.mem (F + BitVec.ofNat 32 0xCC) i =
      feMulW (limbs m.mem (ep + 0x50)) (limbs m.mem (np + 0x50)) i := fun i hi => by
    rw [w6 i hi, feMulW_congr (x' := limbs m.mem (ep + 0x50)) (y' := limbs m.mem (np + 0x50)) (E50 inv5) (N50 inv5)]
  have V7 : ∀ i, i < 10 → limbs n7.mem (F + BitVec.ofNat 32 0xF4) i = eanZZ2 m.mem ep np i := fun i hi => by
    rw [w7 i hi]; unfold eanZZ2 feAddW; rw [V6 i hi]
  -- the temporaries stay until they are read
  have PP7 : ∀ i, i < 10 → limbs n7.mem (F + BitVec.ofNat 32 0x54) i = eanPP m.mem ep np i := fun i hi => by
    rw [tP 0x54 f7 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x54 f6 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x54 f5 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x54 f4 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi]
    exact V3 i hi
  have MM7 : ∀ i, i < 10 → limbs n7.mem (F + BitVec.ofNat 32 0x7C) i = eanMM m.mem ep np i := fun i hi => by
    rw [tP 0x7C f7 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x7C f6 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x7C f5 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi]
    exact V4 i hi
  have tO0 : ∀ c, c + 40 ≤ 0x11C → Sep (F + BitVec.ofNat 32 c) 40 out 40 := fun c h => by
    have := tO c 0 h (by decide); rwa [add_ofNat_zero] at this
  have TT9 : ∀ i, i < 10 → limbs n9.mem (F + BitVec.ofNat 32 0xA4) i = eanTT m.mem ep np i := fun i hi => by
    rw [tP 0xA4 f9 (by decide) (tO _ _ (by decide) (by decide)) i hi, tP 0xA4 f8 (by decide) (tO0 _ (by decide)) i hi,
      tP 0xA4 f7 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0xA4 f6 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi]
    exact V5 i hi
  have TT10 : ∀ i, i < 10 → limbs n10.mem (F + BitVec.ofNat 32 0xA4) i = eanTT m.mem ep np i := fun i hi => by
    rw [tP 0xA4 f10 (by decide) (tO _ _ (by decide) (by decide)) i hi]; exact TT9 i hi
  have ZZ9 : ∀ i, i < 10 → limbs n9.mem (F + BitVec.ofNat 32 0xF4) i = eanZZ2 m.mem ep np i := fun i hi => by
    rw [tP 0xF4 f9 (by decide) (tO _ _ (by decide) (by decide)) i hi, tP 0xF4 f8 (by decide) (tO0 _ (by decide)) i hi]
    exact V7 i hi
  have ZZ10 : ∀ i, i < 10 → limbs n10.mem (F + BitVec.ofNat 32 0xF4) i = eanZZ2 m.mem ep np i := fun i hi => by
    rw [tP 0xF4 f10 (by decide) (tO _ _ (by decide) (by decide)) i hi]; exact ZZ9 i hi
  -- the result's quarters
  have X8 : ∀ i, i < 10 → limbs n8.mem out i = feSubW (eanPP m.mem ep np) (eanMM m.mem ep np) i := fun i hi => by
    rw [w8 i hi, feSubW_congr PP7 MM7]
  have Y9 : ∀ i, i < 10 → limbs n9.mem (out + 0x28) i = feAddW (eanPP m.mem ep np) (eanMM m.mem ep np) i :=
    fun i hi => by
      rw [w9 i hi]; unfold feAddW
      rw [tP 0x54 f8 (by decide) (tO0 _ (by decide)) i hi, tP 0x7C f8 (by decide) (tO0 _ (by decide)) i hi,
        PP7 i hi, MM7 i hi]
  have Z10 : ∀ i, i < 10 → limbs n10.mem (out + 0x50) i = feAddW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i :=
    fun i hi => by rw [w10 i hi]; unfold feAddW; rw [ZZ9 i hi, TT9 i hi]
  have T11 : ∀ i, i < 10 → limbs n11.mem (out + 0x78) i = feSubW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i :=
    fun i hi => by rw [w11 i hi, feSubW_congr ZZ10 TT10]
  have X11 : ∀ i, i < 10 → limbs n11.mem out i = feSubW (eanPP m.mem ep np) (eanMM m.mem ep np) i := fun i hi => by
    rw [pers f11 oS0 (oT0 0x78 (by decide) (by decide)) i hi, pers f10 oS0 (oT0 0x50 (by decide) (by decide)) i hi,
      pers f9 oS0 (oT0 0x28 (by decide) (by decide)) i hi]
    exact X8 i hi
  have Y11 : ∀ i, i < 10 → limbs n11.mem (out + 0x28) i = feAddW (eanPP m.mem ep np) (eanMM m.mem ep np) i :=
    fun i hi => by
      have e1 : limbs n11.mem (out + 0x28) i = limbs n10.mem (out + 0x28) i :=
        pers f11 (oS 0x28 (by decide)) (oT 0x28 0x78 (.inl (by decide)) (by decide) (by decide)) i hi
      have e2 : limbs n10.mem (out + 0x28) i = limbs n9.mem (out + 0x28) i :=
        pers f10 (oS 0x28 (by decide)) (oT 0x28 0x50 (.inl (by decide)) (by decide) (by decide)) i hi
      rw [e1, e2]; exact Y9 i hi
  have Z11 : ∀ i, i < 10 → limbs n11.mem (out + 0x50) i = feAddW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i :=
    fun i hi => by
      have e1 : limbs n11.mem (out + 0x50) i = limbs n10.mem (out + 0x50) i :=
        pers f11 (oS 0x50 (by decide)) (oT 0x50 0x78 (.inl (by decide)) (by decide) (by decide)) i hi
      rw [e1]; exact Z10 i hi
  -- the epilogue, from 0xC8
  obtain ⟨e1, de1, ue1⟩ := u11.aluImm hc11 ean_at_c8 (off' := 0xCA) (by decide)
  have rA : upd (reg n11) a0 (aluEval .add (reg n11 sp) 0x100) a0 = G + BitVec.ofNat 32 0x240 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, R11.1, eA]
  have hpsA : ∀ p ∈ eanPs, p.1 ≠ a0 := by decide
  obtain ⟨e2, ce2, ue2⟩ := St.block (restoreBlockR a0 eanPs) ue1 hc11 eanRestore_end
    (restoreBlockR_ok n11.mem _ a0 (by decide) eanPs _ rA hpsA fun q hq => by
      simp only [eanPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        exact aligned_add (aligned_add hGa (k := 0x240) (by decide)) (by decide))
  simp only [restoreBlockR_run n11.mem _ a0 (by decide) eanPs _ rA hpsA] at ue2
  obtain ⟨e3, de3, ue3⟩ := ue2.aluImm hc11 ean_at_da (off' := 0xDC) (by decide)
  obtain ⟨e4, de4, pc4, mem4, regs4⟩ := ue3.jalr hc11 ean_at_dc
  have slotW : ∀ r o, (r, o) ∈ eanPs → memLoad32 n11.mem (G + BitVec.ofNat 32 0x240 + o) = reg m r := fun r o h => by
    have ho : 0x1C ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
      simp only [eanPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, add_ofNat_assoc, slot11 _ (by omega) (by omega)]
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs n11.mem (G + BitVec.ofNat 32 0x240) f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ eanPs →
      restoreRegs n11.mem (G + BitVec.ofNat 32 0x240) (upd (reg n11) a0 (aluEval .add (reg n11 sp) 0x100)) eanPs r =
        reg m r := fun r o hm => by
    simp only [eanPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  have rsp : restoreRegs n11.mem (G + BitVec.ofNat 32 0x240) (upd (reg n11) a0 (aluEval .add (reg n11 sp) 0x100))
      eanPs sp = F := by
    rw [rr _ _ sp (by decide) (by decide), upd_ne (by decide) (by decide)]; exact R11.1
  have S : Steps m n11 := by
    have S0 : Steps m m4 := .cons d1 (.cons d2 (cp3.trans cp4))
    exact S0.trans (cb1.trans (c1.trans (cb2.trans (c2.trans (cb3.trans (c3.trans (cb4.trans (c4.trans
      (cb5.trans (c5.trans (cb6.trans (c6.trans (cb7.trans (c7.trans (cb8.trans (c8.trans (cb9.trans (c9.trans
      (cb10.trans (c10.trans (cb11.trans c11)))))))))))))))))))))
  refine ⟨e4, S.trans (.cons de1 (ce2.trans (.cons de3 (.single de4)))), ?_, ?_, fun q hq => ?_,
    fun i hi => ?_, fun x hx ho => ?_⟩
  · rw [pc4]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x2C (by decide), hra, add_lit_zero, hret]
  · rw [regs4]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp, eS]
  · rw [regs4]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        (q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
          q ≠ a0 ∧ (∀ p ∈ eanPs, p.1 ≠ q)) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, ha, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x2C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x28 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x24 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x20 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x1C (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps, upd_ne h0 ha]; exact R11.2.2.2.2.2 q h1
  · rw [mem4]; exact ⟨X11 i hi, Y11 i hi, Z11 i hi, T11 i hi⟩
  · rw [mem4]; exact inv11 x hx ho


abbrev esnPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C)]

section
set_option maxRecDepth 20000
theorem esn_at_0 : fetchRel edSubNielsCode 0x0 = some (.aluImm .add sp sp 0xFFFFFED0, 2) := by decide
theorem esn_at_2 : fetchRel edSubNielsCode 0x2 = some (.aluImm .add a3 sp 0x100, 2) := by decide
theorem esn_at_4 : fetchRel edSubNielsCode 0x4 = some (.store .sw a3 ra 0x2C, 4) := by decide
theorem esn_at_8 : fetchRel edSubNielsCode 0x8 = some (.store .sw a3 (8 : Fin 32) 0x28, 2) := by decide
theorem esn_at_a : fetchRel edSubNielsCode 0xA = some (.store .sw a3 (9 : Fin 32) 0x24, 2) := by decide
theorem esn_at_c : fetchRel edSubNielsCode 0xC = some (.store .sw a3 (18 : Fin 32) 0x20, 4) := by decide
theorem esn_at_10 : fetchRel edSubNielsCode 0x10 = some (.store .sw a3 (19 : Fin 32) 0x1C, 4) := by decide
theorem esn_at_14 : fetchRel edSubNielsCode 0x14 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem esn_at_16 : fetchRel edSubNielsCode 0x16 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem esn_at_18 : fetchRel edSubNielsCode 0x18 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem esn_at_1a : fetchRel edSubNielsCode 0x1A = some (.aluImm .add (19 : Fin 32) a1 0x28, 4) := by decide
theorem esn_at_1e : fetchRel edSubNielsCode 0x1E = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem esn_at_20 : fetchRel edSubNielsCode 0x20 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem esn_at_22 : fetchRel edSubNielsCode 0x22 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem esn_at_24 : fetchRel edSubNielsCode 0x24 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem esn_at_28 : fetchRel edSubNielsCode 0x28 = some (.jalr ra ra 0x282, 4) := by decide
theorem esn_at_2c : fetchRel edSubNielsCode 0x2C = some (.aluImm .add a0 sp 0x2C, 2) := by decide
theorem esn_at_2e : fetchRel edSubNielsCode 0x2E = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem esn_at_30 : fetchRel edSubNielsCode 0x30 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem esn_at_32 : fetchRel edSubNielsCode 0x32 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem esn_at_36 : fetchRel edSubNielsCode 0x36 = some (.jalr ra ra 0x2C2, 4) := by decide
theorem esn_at_3a : fetchRel edSubNielsCode 0x3A = some (.aluImm .add a2 (9 : Fin 32) 0x28, 4) := by decide
theorem esn_at_3e : fetchRel edSubNielsCode 0x3E = some (.aluImm .add a0 sp 0x54, 2) := by decide
theorem esn_at_40 : fetchRel edSubNielsCode 0x40 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem esn_at_42 : fetchRel edSubNielsCode 0x42 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem esn_at_46 : fetchRel edSubNielsCode 0x46 = some (.jalr ra ra 0xFFFFFEF0, 4) := by decide
theorem esn_at_4a : fetchRel edSubNielsCode 0x4A = some (.aluImm .add a0 sp 0x7C, 2) := by decide
theorem esn_at_4c : fetchRel edSubNielsCode 0x4C = some (.aluImm .add a1 sp 0x2C, 2) := by decide
theorem esn_at_4e : fetchRel edSubNielsCode 0x4E = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem esn_at_50 : fetchRel edSubNielsCode 0x50 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem esn_at_54 : fetchRel edSubNielsCode 0x54 = some (.jalr ra ra 0xFFFFFEE2, 4) := by decide
theorem esn_at_58 : fetchRel edSubNielsCode 0x58 = some (.aluImm .add a1 (8 : Fin 32) 0x78, 4) := by decide
theorem esn_at_5c : fetchRel edSubNielsCode 0x5C = some (.aluImm .add a2 (9 : Fin 32) 0x78, 4) := by decide
theorem esn_at_60 : fetchRel edSubNielsCode 0x60 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem esn_at_62 : fetchRel edSubNielsCode 0x62 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem esn_at_66 : fetchRel edSubNielsCode 0x66 = some (.jalr ra ra 0xFFFFFED0, 4) := by decide
theorem esn_at_6a : fetchRel edSubNielsCode 0x6A = some (.aluImm .add a1 (8 : Fin 32) 0x50, 4) := by decide
theorem esn_at_6e : fetchRel edSubNielsCode 0x6E = some (.aluImm .add a2 (9 : Fin 32) 0x50, 4) := by decide
theorem esn_at_72 : fetchRel edSubNielsCode 0x72 = some (.aluImm .add a0 sp 0xCC, 2) := by decide
theorem esn_at_74 : fetchRel edSubNielsCode 0x74 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem esn_at_78 : fetchRel edSubNielsCode 0x78 = some (.jalr ra ra 0xFFFFFEBE, 4) := by decide
theorem esn_at_7c : fetchRel edSubNielsCode 0x7C = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem esn_at_7e : fetchRel edSubNielsCode 0x7E = some (.aluImm .add a1 sp 0xCC, 2) := by decide
theorem esn_at_80 : fetchRel edSubNielsCode 0x80 = some (.aluImm .add a2 sp 0xCC, 2) := by decide
theorem esn_at_82 : fetchRel edSubNielsCode 0x82 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem esn_at_86 : fetchRel edSubNielsCode 0x86 = some (.jalr ra ra 0x224, 4) := by decide
theorem esn_at_8a : fetchRel edSubNielsCode 0x8A = some (.aluImm .add a1 sp 0x54, 2) := by decide
theorem esn_at_8c : fetchRel edSubNielsCode 0x8C = some (.aluImm .add a2 sp 0x7C, 2) := by decide
theorem esn_at_8e : fetchRel edSubNielsCode 0x8E = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem esn_at_90 : fetchRel edSubNielsCode 0x90 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem esn_at_94 : fetchRel edSubNielsCode 0x94 = some (.jalr ra ra 0x264, 4) := by decide
theorem esn_at_98 : fetchRel edSubNielsCode 0x98 = some (.aluImm .add a0 (18 : Fin 32) 0x28, 4) := by decide
theorem esn_at_9c : fetchRel edSubNielsCode 0x9C = some (.aluImm .add a1 sp 0x54, 2) := by decide
theorem esn_at_9e : fetchRel edSubNielsCode 0x9E = some (.aluImm .add a2 sp 0x7C, 2) := by decide
theorem esn_at_a0 : fetchRel edSubNielsCode 0xA0 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem esn_at_a4 : fetchRel edSubNielsCode 0xA4 = some (.jalr ra ra 0x206, 4) := by decide
theorem esn_at_a8 : fetchRel edSubNielsCode 0xA8 = some (.aluImm .add a0 (18 : Fin 32) 0x50, 4) := by decide
theorem esn_at_ac : fetchRel edSubNielsCode 0xAC = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem esn_at_ae : fetchRel edSubNielsCode 0xAE = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem esn_at_b0 : fetchRel edSubNielsCode 0xB0 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem esn_at_b4 : fetchRel edSubNielsCode 0xB4 = some (.jalr ra ra 0x244, 4) := by decide
theorem esn_at_b8 : fetchRel edSubNielsCode 0xB8 = some (.aluImm .add a0 (18 : Fin 32) 0x78, 4) := by decide
theorem esn_at_bc : fetchRel edSubNielsCode 0xBC = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem esn_at_be : fetchRel edSubNielsCode 0xBE = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem esn_at_c0 : fetchRel edSubNielsCode 0xC0 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem esn_at_c4 : fetchRel edSubNielsCode 0xC4 = some (.jalr ra ra 0x1E6, 4) := by decide
theorem esn_at_c8 : fetchRel edSubNielsCode 0xC8 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem esn_at_ca : fetchRel edSubNielsCode 0xCA = some (.load .lw ra a0 0x2C, 4) := by decide
theorem esn_at_ce : fetchRel edSubNielsCode 0xCE = some (.load .lw (8 : Fin 32) a0 0x28, 2) := by decide
theorem esn_at_d0 : fetchRel edSubNielsCode 0xD0 = some (.load .lw (9 : Fin 32) a0 0x24, 2) := by decide
theorem esn_at_d2 : fetchRel edSubNielsCode 0xD2 = some (.load .lw (18 : Fin 32) a0 0x20, 4) := by decide
theorem esn_at_d6 : fetchRel edSubNielsCode 0xD6 = some (.load .lw (19 : Fin 32) a0 0x1C, 4) := by decide
theorem esn_at_da : fetchRel edSubNielsCode 0xDA = some (.aluImm .add sp sp 0x130, 2) := by decide
theorem esn_at_dc : fetchRel edSubNielsCode 0xDC = some (.jalr x0 ra 0x0, 2) := by decide
theorem esnSave_end : blockEnd edSubNielsCode 4 (saveBlockR a3 esnPs) = some 0x14 := by decide
theorem esnRestore_end : blockEnd edSubNielsCode 0xCA (restoreBlockR a0 esnPs) = some 0xDA := by decide
end

/-- `b` and the `n` bytes after it are apart from `sub`'s code and every
function it calls. -/
structure EsnCode (P b : Word) (n : Nat) : Prop where
  c : Sep b n P edSubNielsCode.length
  a : Sep b n (P + 0xFFFFE2A6) feAddCode.length
  aS : Sep b n (P + 0xFFFFE2A6 + 0x5D88) memcpyStubCode.length
  aB : Sep b n (P + 0xFFFFE2A6 + 0x5D90) memcpyBodyCode.length
  s : Sep b n (P + 0xFFFFE2F4) feSubCode.length
  sR : Sep b n (P + 0xFFFFE2F4 + 0xFFFFF72E) feReduceCode.length
  m : Sep b n (P + 0xFFFFCF32) feMulCode.length
  mR : Sep b n (P + 0xFFFFCF32 + 0xAF0) feReduceCode.length

theorem EsnCode.sub {P b : Word} {n : Nat} (h : EsnCode P b n) {c l : Nat} (hl : c + l ≤ n) :
    EsnCode P (b + BitVec.ofNat 32 c) l :=
  ⟨h.c.sub hl, h.a.sub hl, h.aS.sub hl, h.aB.sub hl, h.s.sub hl, h.sR.sub hl, h.m.sub hl, h.mR.sub hl⟩

/-- Where `sub` runs: its code and its callees', the 0x270 bytes of stack
below `sp0`, the point at `ep`, the Niels point at `np`, and the result at
`out`, apart from what each must not touch. -/
structure ESNEnv (M : Word → BitVec 8) (P sp0 out ep np : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P edSubNielsCode
  add : CodeIn M (P + 0xFFFFE2A6) feAddCode
  addS : CodeIn M (P + 0xFFFFE2A6 + 0x5D88) memcpyStubCode
  addB : CodeIn M (P + 0xFFFFE2A6 + 0x5D90) memcpyBodyCode
  sub : CodeIn M (P + 0xFFFFE2F4) feSubCode
  subR : CodeIn M (P + 0xFFFFE2F4 + 0xFFFFF72E) feReduceCode
  mul : CodeIn M (P + 0xFFFFCF32) feMulCode
  mulR : CodeIn M (P + 0xFFFFCF32 + 0xAF0) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x270 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hep : ep.toNat % 4 = 0
  hnp : np.toNat % 4 = 0
  how : out.toNat + 0xA0 < 2 ^ 32
  hew : ep.toNat + 0xA0 < 2 ^ 32
  hnw : np.toNat + 0xA0 < 2 ^ 32
  sG : EsnCode P (sp0 + 0xFFFFFD90) 0x270
  sO : EsnCode P out 0xA0
  sOG : Sep out 0xA0 (sp0 + 0xFFFFFD90) 0x270
  sEG : Sep ep 0xA0 (sp0 + 0xFFFFFD90) 0x270
  sNG : Sep np 0xA0 (sp0 + 0xFFFFFD90) 0x270
  sEO : Sep ep 0xA0 out 0xA0
  sNO : Sep np 0xA0 out 0xA0

/-- `PP = (Y + X)·(Y - X)ₙ`, as `sub` forms it. -/
def esnPP (M : Word → BitVec 8) (ep np : Word) : Nat → Word :=
  feMulW (feAddW (limbs M (ep + 0x28)) (limbs M ep)) (limbs M (np + 0x28))

/-- `MM = (Y - X)·(Y + X)ₙ`, as `sub` forms it. -/
def esnMM (M : Word → BitVec 8) (ep np : Word) : Nat → Word :=
  feMulW (feSubW (limbs M (ep + 0x28)) (limbs M ep)) (limbs M np)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `<&EdwardsPoint as Sub<&ProjectiveNielsPoint>>::sub`**:
from the point at `ep` and the Niels point at `np`, it stores at `out` the
limbs of `PP - MM`, `PP + MM`, `ZZ2 - TT2d`, and `ZZ2 + TT2d` as the field
operations compute them. -/
theorem edSubNiels_correct (m : Machine) {P sp0 out ep np retAddr : Word} (env : ESNEnv m.mem P sp0 out ep np)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ep) (ha2 : reg m a2 = np)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ i, i < 10 →
        limbs m'.mem out i = feSubW (esnPP m.mem ep np) (esnMM m.mem ep np) i ∧
        limbs m'.mem (out + 0x28) i = feAddW (esnPP m.mem ep np) (esnMM m.mem ep np) i ∧
        limbs m'.mem (out + 0x50) i = feSubW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i ∧
        limbs m'.mem (out + 0x78) i = feAddW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i) ∧
      ∀ x, Sep (sp0 + 0xFFFFFD90) 0x270 x 1 → Sep out 0xA0 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFD90 = G := ⟨_, rfl⟩
  have sG := env.sG; have sOG := env.sOG; have sEG := env.sEG; have sNG := env.sNG
  rw [hG] at sG sOG sEG sNG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFED0 = F := ⟨_, rfl⟩
  have hGF : G + BitVec.ofNat 32 0x140 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFD90) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x140) (by decide)
  have hGw : G.toNat + 0x270 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFD90 : Word).toNat = 4294966672 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x140 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have gw : G.toNat + 0x270 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have eS : F + 0x130 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x140 + k) := fun k => by rw [← hGF, add_ofNat_assoc]
  have eFm : F + 0xFFFFFEC0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eA : F + 0x100 = G + BitVec.ofNat 32 0x240 := by rw [← hGF, BitVec.add_assoc]; rfl
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x270 → d + k ≤ 0x270 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have g0 : ∀ {a : Word} {n : Nat}, Sep a n G 0x270 → Sep a n G 0x140 := fun h => by
    have := h.subR (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have g0' : ∀ {b : Word} {l : Nat}, Sep G 0x270 b l → Sep G 0x140 b l := fun h => by
    have := h.sub (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have zg : ∀ {z : Word}, Sep G 0x270 z 1 → Sep G 0x140 z 1 := fun h => by
    have := h.sub (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x270 b code'.length → Sep out 0xA0 b code'.length →
      (∀ x, Sep G 0x270 x 1 → Sep out 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs ho hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- temporaries at `F + c`, the result's quarters at `out + k`
  have tS : ∀ c, c + 40 ≤ 0x11C → Sep (F + BitVec.ofNat 32 c) 40 G 0x140 := fun c h => by
    rw [eFk]; have := offs (c := 0x140 + c) (n := 40) (d := 0) (k := 0x140) (.inr (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have tC : ∀ c, c + 40 ≤ 0x11C → EsnCode P (F + BitVec.ofNat 32 c) 40 := fun c h => by
    rw [eFk]; exact sG.sub (by omega)
  have tA : ∀ c, c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hFa h
  have tW : ∀ c, c + 40 ≤ 0x11C → (F + BitVec.ofNat 32 c).toNat + 40 < 2 ^ 32 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  have tIn : ∀ c, c + 40 ≤ 0x11C → ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep (F + BitVec.ofNat 32 c) 40 z 1 :=
    fun c h z hz _ => by rw [eFk]; exact hz.sub (by omega)
  have tT : ∀ c d, c + 40 ≤ d ∨ d + 40 ≤ c → c + 40 ≤ 0x11C → d + 40 ≤ 0x11C →
      Sep (F + BitVec.ofNat 32 c) 40 (F + BitVec.ofNat 32 d) 40 := fun c d h h1 h2 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have tSl : ∀ c k, c + 40 ≤ 0x11C → 0x25C ≤ k → k < 0x270 → Sep (F + BitVec.ofNat 32 c) 40 (G + BitVec.ofNat 32 k) 1 :=
    fun c k h h1 h2 => by rw [eFk]; exact offs (.inl (by omega)) (by omega) (by omega)
  have tO : ∀ c k, c + 40 ≤ 0x11C → k + 40 ≤ 0xA0 → Sep (F + BitVec.ofNat 32 c) 40 (out + BitVec.ofNat 32 k) 40 :=
    fun c k h1 h2 => by rw [eFk]; exact ((sOG.sub (c := k) (l := 40) h2).subR (c := 0x140 + c) (l := 40) (by omega)).symm
  have oS : ∀ k, k + 40 ≤ 0xA0 → Sep (out + BitVec.ofNat 32 k) 40 G 0x140 := fun k h => g0 (sOG.sub h)
  have oA : ∀ k, k % 4 = 0 → (out + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k h => aligned_add env.hout h
  have oW : ∀ k, k + 40 ≤ 0xA0 → (out + BitVec.ofNat 32 k).toNat + 40 < 2 ^ 32 := fun k h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.how; omega
  have oIn : ∀ k, k + 40 ≤ 0xA0 → ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep (out + BitVec.ofNat 32 k) 40 z 1 :=
    fun k h z _ hz => hz.sub h
  have oSl : ∀ k j, k + 40 ≤ 0xA0 → j < 0x270 → Sep (out + BitVec.ofNat 32 k) 40 (G + BitVec.ofNat 32 j) 1 :=
    fun k j h hj => (sOG.sub (c := k) (l := 40) h).subR (by omega)
  have oT : ∀ k k', k + 40 ≤ k' ∨ k' + 40 ≤ k → k + 40 ≤ 0xA0 → k' + 40 ≤ 0xA0 →
      Sep (out + BitVec.ofNat 32 k) 40 (out + BitVec.ofNat 32 k') 40 := fun k k' h h1 h2 =>
    sep_offsets out h (by omega) (by omega)
  -- the operands' limbs stay as they were
  have epK : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ c i, c + 40 ≤ 0xA0 → i < 10 → limbs M (ep + BitVec.ofNat 32 c) i = limbs m.mem (ep + BitVec.ofNat 32 c) i :=
    fun hM c i h hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact hM _ (sEG.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
        (env.sEO.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
  have npK : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ c i, c + 40 ≤ 0xA0 → i < 10 → limbs M (np + BitVec.ofNat 32 c) i = limbs m.mem (np + BitVec.ofNat 32 c) i :=
    fun hM c i h hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact hM _ (sNG.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
        (env.sNO.sub (c := c + (4 * i + j)) (l := 1) (by omega)).symm
  have pers : ∀ {M M' : Word → BitVec 8} {o a : Word}, (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      Sep a 40 G 0x140 → Sep a 40 o 40 → ∀ i, i < 10 → limbs M' a i = limbs M a i :=
    fun hM h1 h2 i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact hM _ (h1.sub (c := 4 * i + j) (l := 1) (by omega)).symm (h2.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have invStep : ∀ {M M' : Word → BitVec 8} {o : Word}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep o 40 z 1) →
      ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M' z = m.mem z :=
    fun hI hM ho z h1 h2 => by rw [hM z (zg h1) (ho z h1 h2), hI z h1 h2]
  have mulCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x y : Word),
      St M P nm off (reg nm) → CodeIn M P edSubNielsCode →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      fetchRel edSubNielsCode off = some (.auipc ra imm, 4) →
      fetchRel edSubNielsCode (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0xFFFFCF32 → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = y →
      o.toNat % 4 = 0 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → EsnCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 → Sep y 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feMulW (limbs M x) (limbs M y) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x y s hc hI h1 h2 hb hev hs e0 e1 e2 hoa hxa hya hoc soG sxG syG
    have e : FeMEnv M (P + 0xFFFFCF32) (reg nm sp) (reg nm a0) (reg nm a1) (reg nm a2) := by
      rw [hs, e0, e1, e2]
      exact ⟨even_at P env.hP 0xFFFFCF32 (by decide), cIn env.mul sG.m env.sO.m hI, cIn env.mulR sG.mR env.sO.mR hI,
        hFa, by omega, hoa, hxa, hya, by rw [eFm]; exact g0' sG.m, by rw [eFm]; exact g0' sG.mR, hoc.m, hoc.mR,
        by rw [eFm]; exact soG, by rw [eFm]; exact sxG, by rw [eFm]; exact syG⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeMul hc h1 h2 hb (even_at P env.hP (off + 8) hev) e
    rw [e0, e1, e2] at w1; rw [hs, e0, eFm] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, f1⟩
  have addCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x y : Word),
      St M P nm off (reg nm) → CodeIn M P edSubNielsCode →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      fetchRel edSubNielsCode off = some (.auipc ra imm, 4) →
      fetchRel edSubNielsCode (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0xFFFFE2A6 → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = y →
      o.toNat + 40 < 2 ^ 32 → x.toNat + 40 < 2 ^ 32 → y.toNat % 4 = 0 → EsnCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 → Sep y 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feAddW (limbs M x) (limbs M y) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x y s hc hI h1 h2 hb hev hs e0 e1 e2 how hxw hya hoc soG sxG syG
    have e : FeAddEnv M (P + 0xFFFFE2A6) (G + BitVec.ofNat 32 0xF0) (reg nm a0) (reg nm a1) (reg nm a2) := by
      rw [e0, e1, e2]
      exact ⟨even_at P env.hP 0xFFFFE2A6 (by decide), cIn env.add sG.a env.sO.a hI, cIn env.addS sG.aS env.sO.aS hI,
        cIn env.addB sG.aB env.sO.aB hI, aligned_add hGa (by decide),
        by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hya, how, hxw,
        sG.a.sub (by decide), sG.aS.sub (by decide), sG.aB.sub (by decide), hoc.a, hoc.aB,
        soG.subR (by decide), sxG.subR (by decide), syG.subR (by decide)⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeAdd hc h1 h2 hb (even_at P env.hP (off + 8) hev)
      (by rw [hs, ← hGF, BitVec.add_assoc]; rfl) e
    rw [e0, e1, e2] at w1; rw [e0] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, fun z hz ho => f1 z (hz.sub (by decide)) ho⟩
  have subCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x y : Word),
      St M P nm off (reg nm) → CodeIn M P edSubNielsCode →
      (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      fetchRel edSubNielsCode off = some (.auipc ra imm, 4) →
      fetchRel edSubNielsCode (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0xFFFFE2F4 → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = y →
      o.toNat % 4 = 0 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → EsnCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 → Sep y 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feSubW (limbs M x) (limbs M y) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x y s hc hI h1 h2 hb hev hs e0 e1 e2 hoa hxa hya hoc soG sxG syG
    have e : FeSubEnv M (P + 0xFFFFE2F4) (G + BitVec.ofNat 32 0x90) (reg nm a0) (reg nm a1) (reg nm a2) := by
      rw [e0, e1, e2]
      exact ⟨even_at P env.hP 0xFFFFE2F4 (by decide), cIn env.sub sG.s env.sO.s hI, cIn env.subR sG.sR env.sO.sR hI,
        aligned_add hGa (by decide), by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hxa, hya, hoa,
        sG.s.sub (by decide), sG.sR.sub (by decide), hoc.s,
        soG.subR (by decide), sxG.subR (by decide), syG.subR (by decide)⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeSub hc h1 h2 hb (even_at P env.hP (off + 8) hev)
      (by rw [hs, ← hGF, BitVec.add_assoc]; rfl) e
    rw [e0, e1, e2] at w1; rw [e0] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, fun z hz ho => f1 z (hz.sub (by decide)) ho⟩
  have eS0 : Sep ep 40 G 0x140 := by have := g0 (sEG.sub (c := 0) (l := 40) (by decide)); rwa [add_ofNat_zero] at this
  have nS0 : Sep np 40 G 0x140 := by have := g0 (sNG.sub (c := 0) (l := 40) (by decide)); rwa [add_ofNat_zero] at this
  have eSk : ∀ k, k + 40 ≤ 0xA0 → Sep (ep + BitVec.ofNat 32 k) 40 G 0x140 := fun k h => g0 (sEG.sub h)
  have nSk : ∀ k, k + 40 ≤ 0xA0 → Sep (np + BitVec.ofNat 32 k) 40 G 0x140 := fun k h => g0 (sNG.sub h)
  have eW : ∀ k, k + 40 ≤ 0xA0 → (ep + BitVec.ofNat 32 k).toNat + 40 < 2 ^ 32 := fun k h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.hew; omega
  have ep0K : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M ep i = limbs m.mem ep i := fun hM i hi => by
    have := epK hM 0 i (by decide) hi; rwa [add_ofNat_zero] at this
  have np0K : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M np i = limbs m.mem np i := fun hM i hi => by
    have := npK hM 0 i (by decide) hi; rwa [add_ofNat_zero] at this
  have gk : ∀ k, 0x140 ≤ k → k < 0x270 → Sep G 0x140 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    have := offs (c := 0) (n := 0x140) (d := k) (k := 1) (.inl (by omega)) (by decide) (by omega)
    rwa [add_ofNat_zero] at this
  -- the prologue
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod esn_at_0 (off' := 2) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm env.cod esn_at_2 (off' := 4) (by decide)
  have r2 : ∀ q, q.val ≠ 0 → q ≠ sp → q ≠ a3 → reg m2 q = reg m q := fun q hv hs h3 => by
    rw [u2.regs, upd_ne hv h3, upd_ne hv hs]
  have sp2 : reg m2 sp = F := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have a3v : reg m2 a3 = G + BitVec.ofNat 32 0x240 := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ev_add, hsp, hF, eA]
  have slA : ∀ (o : Word), 0x1C ≤ o.toNat → o.toNat + 4 ≤ 0x30 → ∀ {b : Word} {l : Nat}, Sep G 0x270 b l →
      Sep (G + BitVec.ofNat 32 0x240 + o) 4 b l := fun o h1 h2 b l h => by
    rw [← ofNat_toNat_self o, add_ofNat_assoc]; exact h.sub (by omega)
  obtain ⟨m3, cp3, u3⟩ := St.block (saveBlockR a3 esnPs) u2.self env.cod esnSave_end
    (saveBlockR_ok a3 _ esnPs _ fun p hp => by
      rw [a3v]
      simp only [esnPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add (aligned_add hGa (k := 0x240) (by decide)) (by decide), slA _ (by decide) (by decide) sG.c⟩)
  simp only [saveBlockR_run] at u3
  rw [a3v] at u3
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (G + BitVec.ofNat 32 0x240) (reg m2) esnPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u3
  have frSv : ∀ x, Sep G 0x270 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside esnPs fun p hp => by
      simp only [esnPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact slA _ (by decide) (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ esnPs → memLoad32 Msv (G + BitVec.ofNat 32 0x240 + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [esnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      exact r2 _ (by decide) (by decide) (by decide)
  have inv0 : ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Msv z = m.mem z := fun z h _ => frSv z h
  have hcS : CodeIn Msv P edSubNielsCode := cIn env.cod sG.c env.sO.c inv0
  obtain ⟨m4, cp4, u4⟩ := St.block [.alu .add (9 : Fin 32) x0 a2, .alu .add (8 : Fin 32) x0 a1,
    .alu .add (18 : Fin 32) x0 a0, .aluImm .add (19 : Fin 32) a1 0x28] u3.self hcS (off' := 0x1E) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u4
  have R4 : EanRegs m m4 F out ep np := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.regs, sp2]
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a1 (by decide) (by decide) (by decide), ha1]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a2 (by decide) (by decide) (by decide), ha2]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a0 (by decide) (by decide) (by decide), ha0]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, u3.regs]
      rw [ev_add, r2 a1 (by decide) (by decide) (by decide), ha1]
    · have h : q.val ≠ 0 ∧ q ≠ 9 ∧ q ≠ 8 ∧ q ≠ 18 ∧ q ≠ 19 ∧ q ≠ sp ∧ q ≠ a3 := by revert hq; revert q; decide
      rw [u4.regs, upd_ne h.1 h.2.2.2.2.1, upd_ne h.1 h.2.2.2.1, upd_ne h.1 h.2.2.1, upd_ne h.1 h.2.1, u3.regs,
        r2 q h.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2]
  have oC0 : EsnCode P out 40 := by have := env.sO.sub (c := 0) (l := 40) (by decide); rwa [add_ofNat_zero] at this
  have oS0 : Sep out 40 G 0x140 := by have := oS 0 (by decide); rwa [add_ofNat_zero] at this
  have oIn0 : ∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → Sep out 40 z 1 := fun z _ hz => by
    have := hz.sub (c := 0) (l := 40) (by decide); rwa [add_ofNat_zero] at this
  have oSl0 : ∀ j, j < 0x270 → Sep out 40 (G + BitVec.ofNat 32 j) 1 := fun j hj => by
    have := oSl 0 j (by decide) hj; rwa [add_ofNat_zero] at this
  have slot0 : ∀ k, 0x25C ≤ k → k < 0x270 → Msv (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun _ _ _ => rfl
  -- call 1
  obtain ⟨b1, cb1, ub1⟩ := St.block [.aluImm .add a0 sp 0x4, .alu .add a1 x0 (19 : Fin 32), .alu .add a2 x0 (8 : Fin 32)] u4.self hcS
    (off' := 0x24) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub1
  have rb1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b1 q = reg m4 q := fun q hv h0 h1 h2 => by
    rw [ub1.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := addCall (F + BitVec.ofNat 32 4) (ep + 0x28) ep ub1.self hcS inv0
    esn_at_24 esn_at_28 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb1 sp (by decide) (by decide) (by decide) (by decide)]; exact R4.1)
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (tW 4 (by decide)) (eW 0x28 (by decide)) (env.hep) (tC 4 (by decide)) (tS 4 (by decide)) (eSk 0x28 (by decide)) (eS0)
  have inv1 := invStep inv0 f1 (tIn 4 (by decide))
  have hc1 : CodeIn n1.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv1
  have slot1 : ∀ k, 0x25C ≤ k → k < 0x270 → n1.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f1 _ (gk k (by omega) h2) (tSl 4 k (by decide) h1 h2)).trans (slot0 k h1 h2)
  have R1 : EanRegs m n1 F out ep np := R4.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k1 q h.2.2.2.2.2 h.2.2.2.2.1, rb1 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 2
  obtain ⟨b2, cb2, ub2⟩ := St.block [.aluImm .add a0 sp 0x2C, .alu .add a1 x0 (19 : Fin 32), .alu .add a2 x0 (8 : Fin 32)] u1 hc1
    (off' := 0x32) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub2
  have rb2 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b2 q = reg n1 q := fun q hv h0 h1 h2 => by
    rw [ub2.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := subCall (F + BitVec.ofNat 32 0x2C) (ep + 0x28) ep ub2.self hc1 inv1
    esn_at_32 esn_at_36 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb2 sp (by decide) (by decide) (by decide) (by decide)]; exact R1.1)
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R1.1, R1.2.1, R1.2.2.1, R1.2.2.2.1, R1.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u1.zero]; first | rfl | exact zw _))
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R1.1, R1.2.1, R1.2.2.1, R1.2.2.2.1, R1.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u1.zero]; first | rfl | exact zw _))
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R1.1, R1.2.1, R1.2.2.1, R1.2.2.2.1, R1.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u1.zero]; first | rfl | exact zw _))
    (tA 0x2C (by decide)) (aligned_add env.hep (by decide)) (env.hep) (tC 0x2C (by decide)) (tS 0x2C (by decide)) (eSk 0x28 (by decide)) (eS0)
  have inv2 := invStep inv1 f2 (tIn 0x2C (by decide))
  have hc2 : CodeIn n2.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv2
  have slot2 : ∀ k, 0x25C ≤ k → k < 0x270 → n2.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f2 _ (gk k (by omega) h2) (tSl 0x2C k (by decide) h1 h2)).trans (slot1 k h1 h2)
  have R2 : EanRegs m n2 F out ep np := R1.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k2 q h.2.2.2.2.2 h.2.2.2.2.1, rb2 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 3
  obtain ⟨b3, cb3, ub3⟩ := St.block [.aluImm .add a2 (9 : Fin 32) 0x28, .aluImm .add a0 sp 0x54, .aluImm .add a1 sp 0x4] u2 hc2
    (off' := 0x42) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub3
  have rb3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b3 q = reg n2 q := fun q hv h0 h1 h2 => by
    rw [ub3.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n3, c3, u3, sp3, k3, w3, f3⟩ := mulCall (F + BitVec.ofNat 32 0x54) (F + BitVec.ofNat 32 4) (np + 0x28) ub3.self hc2 inv2
    esn_at_42 esn_at_46 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb3 sp (by decide) (by decide) (by decide) (by decide)]; exact R2.1)
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R2.1, R2.2.1, R2.2.2.1, R2.2.2.2.1, R2.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u2.zero]; first | rfl | exact zw _))
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R2.1, R2.2.1, R2.2.2.1, R2.2.2.2.1, R2.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u2.zero]; first | rfl | exact zw _))
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R2.1, R2.2.1, R2.2.2.1, R2.2.2.2.1, R2.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u2.zero]; first | rfl | exact zw _))
    (tA 0x54 (by decide)) (tA 4 (by decide)) (aligned_add env.hnp (by decide)) (tC 0x54 (by decide)) (tS 0x54 (by decide)) (tS 4 (by decide)) (nSk 0x28 (by decide))
  have inv3 := invStep inv2 f3 (tIn 0x54 (by decide))
  have hc3 : CodeIn n3.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv3
  have slot3 : ∀ k, 0x25C ≤ k → k < 0x270 → n3.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f3 _ (gk k (by omega) h2) (tSl 0x54 k (by decide) h1 h2)).trans (slot2 k h1 h2)
  have R3 : EanRegs m n3 F out ep np := R2.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k3 q h.2.2.2.2.2 h.2.2.2.2.1, rb3 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 4
  obtain ⟨b4, cb4, ub4⟩ := St.block [.aluImm .add a0 sp 0x7C, .aluImm .add a1 sp 0x2C, .alu .add a2 x0 (9 : Fin 32)] u3 hc3
    (off' := 0x50) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub4
  have rb4 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b4 q = reg n3 q := fun q hv h0 h1 h2 => by
    rw [ub4.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n4, c4, u4, sp4, k4, w4, f4⟩ := mulCall (F + BitVec.ofNat 32 0x7C) (F + BitVec.ofNat 32 0x2C) np ub4.self hc3 inv3
    esn_at_50 esn_at_54 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb4 sp (by decide) (by decide) (by decide) (by decide)]; exact R3.1)
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R3.1, R3.2.1, R3.2.2.1, R3.2.2.2.1, R3.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u3.zero]; first | rfl | exact zw _))
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R3.1, R3.2.1, R3.2.2.1, R3.2.2.2.1, R3.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u3.zero]; first | rfl | exact zw _))
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R3.1, R3.2.1, R3.2.2.1, R3.2.2.2.1, R3.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u3.zero]; first | rfl | exact zw _))
    (tA 0x7C (by decide)) (tA 0x2C (by decide)) (env.hnp) (tC 0x7C (by decide)) (tS 0x7C (by decide)) (tS 0x2C (by decide)) (nS0)
  have inv4 := invStep inv3 f4 (tIn 0x7C (by decide))
  have hc4 : CodeIn n4.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv4
  have slot4 : ∀ k, 0x25C ≤ k → k < 0x270 → n4.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f4 _ (gk k (by omega) h2) (tSl 0x7C k (by decide) h1 h2)).trans (slot3 k h1 h2)
  have R4 : EanRegs m n4 F out ep np := R3.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k4 q h.2.2.2.2.2 h.2.2.2.2.1, rb4 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 5
  obtain ⟨b5, cb5, ub5⟩ := St.block [.aluImm .add a1 (8 : Fin 32) 0x78, .aluImm .add a2 (9 : Fin 32) 0x78, .aluImm .add a0 sp 0xA4] u4 hc4
    (off' := 0x62) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub5
  have rb5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b5 q = reg n4 q := fun q hv h0 h1 h2 => by
    rw [ub5.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n5, c5, u5, sp5, k5, w5, f5⟩ := mulCall (F + BitVec.ofNat 32 0xA4) (ep + 0x78) (np + 0x78) ub5.self hc4 inv4
    esn_at_62 esn_at_66 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb5 sp (by decide) (by decide) (by decide) (by decide)]; exact R4.1)
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.zero]; first | rfl | exact zw _))
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.zero]; first | rfl | exact zw _))
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R4.1, R4.2.1, R4.2.2.1, R4.2.2.2.1, R4.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u4.zero]; first | rfl | exact zw _))
    (tA 0xA4 (by decide)) (aligned_add env.hep (by decide)) (aligned_add env.hnp (by decide)) (tC 0xA4 (by decide)) (tS 0xA4 (by decide)) (eSk 0x78 (by decide)) (nSk 0x78 (by decide))
  have inv5 := invStep inv4 f5 (tIn 0xA4 (by decide))
  have hc5 : CodeIn n5.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv5
  have slot5 : ∀ k, 0x25C ≤ k → k < 0x270 → n5.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f5 _ (gk k (by omega) h2) (tSl 0xA4 k (by decide) h1 h2)).trans (slot4 k h1 h2)
  have R5 : EanRegs m n5 F out ep np := R4.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k5 q h.2.2.2.2.2 h.2.2.2.2.1, rb5 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 6
  obtain ⟨b6, cb6, ub6⟩ := St.block [.aluImm .add a1 (8 : Fin 32) 0x50, .aluImm .add a2 (9 : Fin 32) 0x50, .aluImm .add a0 sp 0xCC] u5 hc5
    (off' := 0x74) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub6
  have rb6 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b6 q = reg n5 q := fun q hv h0 h1 h2 => by
    rw [ub6.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n6, c6, u6, sp6, k6, w6, f6⟩ := mulCall (F + BitVec.ofNat 32 0xCC) (ep + 0x50) (np + 0x50) ub6.self hc5 inv5
    esn_at_74 esn_at_78 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb6 sp (by decide) (by decide) (by decide) (by decide)]; exact R5.1)
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R5.1, R5.2.1, R5.2.2.1, R5.2.2.2.1, R5.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u5.zero]; first | rfl | exact zw _))
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R5.1, R5.2.1, R5.2.2.1, R5.2.2.2.1, R5.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u5.zero]; first | rfl | exact zw _))
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R5.1, R5.2.1, R5.2.2.1, R5.2.2.2.1, R5.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u5.zero]; first | rfl | exact zw _))
    (tA 0xCC (by decide)) (aligned_add env.hep (by decide)) (aligned_add env.hnp (by decide)) (tC 0xCC (by decide)) (tS 0xCC (by decide)) (eSk 0x50 (by decide)) (nSk 0x50 (by decide))
  have inv6 := invStep inv5 f6 (tIn 0xCC (by decide))
  have hc6 : CodeIn n6.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv6
  have slot6 : ∀ k, 0x25C ≤ k → k < 0x270 → n6.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f6 _ (gk k (by omega) h2) (tSl 0xCC k (by decide) h1 h2)).trans (slot5 k h1 h2)
  have R6 : EanRegs m n6 F out ep np := R5.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k6 q h.2.2.2.2.2 h.2.2.2.2.1, rb6 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 7
  obtain ⟨b7, cb7, ub7⟩ := St.block [.aluImm .add a0 sp 0xF4, .aluImm .add a1 sp 0xCC, .aluImm .add a2 sp 0xCC] u6 hc6
    (off' := 0x82) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub7
  have rb7 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b7 q = reg n6 q := fun q hv h0 h1 h2 => by
    rw [ub7.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n7, c7, u7, sp7, k7, w7, f7⟩ := addCall (F + BitVec.ofNat 32 0xF4) (F + BitVec.ofNat 32 0xCC) (F + BitVec.ofNat 32 0xCC) ub7.self hc6 inv6
    esn_at_82 esn_at_86 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb7 sp (by decide) (by decide) (by decide) (by decide)]; exact R6.1)
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R6.1, R6.2.1, R6.2.2.1, R6.2.2.2.1, R6.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u6.zero]; first | rfl | exact zw _))
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R6.1, R6.2.1, R6.2.2.1, R6.2.2.2.1, R6.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u6.zero]; first | rfl | exact zw _))
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R6.1, R6.2.1, R6.2.2.1, R6.2.2.2.1, R6.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u6.zero]; first | rfl | exact zw _))
    (tW 0xF4 (by decide)) (tW 0xCC (by decide)) (tA 0xCC (by decide)) (tC 0xF4 (by decide)) (tS 0xF4 (by decide)) (tS 0xCC (by decide)) (tS 0xCC (by decide))
  have inv7 := invStep inv6 f7 (tIn 0xF4 (by decide))
  have hc7 : CodeIn n7.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv7
  have slot7 : ∀ k, 0x25C ≤ k → k < 0x270 → n7.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f7 _ (gk k (by omega) h2) (tSl 0xF4 k (by decide) h1 h2)).trans (slot6 k h1 h2)
  have R7 : EanRegs m n7 F out ep np := R6.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k7 q h.2.2.2.2.2 h.2.2.2.2.1, rb7 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 8
  obtain ⟨b8, cb8, ub8⟩ := St.block [.aluImm .add a1 sp 0x54, .aluImm .add a2 sp 0x7C, .alu .add a0 x0 (18 : Fin 32)] u7 hc7
    (off' := 0x90) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub8
  have rb8 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b8 q = reg n7 q := fun q hv h0 h1 h2 => by
    rw [ub8.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n8, c8, u8, sp8, k8, w8, f8⟩ := subCall out (F + BitVec.ofNat 32 0x54) (F + BitVec.ofNat 32 0x7C) ub8.self hc7 inv7
    esn_at_90 esn_at_94 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb8 sp (by decide) (by decide) (by decide) (by decide)]; exact R7.1)
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R7.1, R7.2.1, R7.2.2.1, R7.2.2.2.1, R7.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u7.zero]; first | rfl | exact zw _))
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R7.1, R7.2.1, R7.2.2.1, R7.2.2.2.1, R7.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u7.zero]; first | rfl | exact zw _))
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R7.1, R7.2.1, R7.2.2.1, R7.2.2.2.1, R7.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u7.zero]; first | rfl | exact zw _))
    (env.hout) (tA 0x54 (by decide)) (tA 0x7C (by decide)) (oC0) (oS0) (tS 0x54 (by decide)) (tS 0x7C (by decide))
  have inv8 := invStep inv7 f8 (oIn0)
  have hc8 : CodeIn n8.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv8
  have slot8 : ∀ k, 0x25C ≤ k → k < 0x270 → n8.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f8 _ (gk k (by omega) h2) (oSl0 k (by omega))).trans (slot7 k h1 h2)
  have R8 : EanRegs m n8 F out ep np := R7.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k8 q h.2.2.2.2.2 h.2.2.2.2.1, rb8 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 9
  obtain ⟨b9, cb9, ub9⟩ := St.block [.aluImm .add a0 (18 : Fin 32) 0x28, .aluImm .add a1 sp 0x54, .aluImm .add a2 sp 0x7C] u8 hc8
    (off' := 0xa0) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub9
  have rb9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b9 q = reg n8 q := fun q hv h0 h1 h2 => by
    rw [ub9.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n9, c9, u9, sp9, k9, w9, f9⟩ := addCall (out + 0x28) (F + BitVec.ofNat 32 0x54) (F + BitVec.ofNat 32 0x7C) ub9.self hc8 inv8
    esn_at_a0 esn_at_a4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb9 sp (by decide) (by decide) (by decide) (by decide)]; exact R8.1)
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R8.1, R8.2.1, R8.2.2.1, R8.2.2.2.1, R8.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u8.zero]; first | rfl | exact zw _))
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R8.1, R8.2.1, R8.2.2.1, R8.2.2.2.1, R8.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u8.zero]; first | rfl | exact zw _))
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R8.1, R8.2.1, R8.2.2.1, R8.2.2.2.1, R8.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u8.zero]; first | rfl | exact zw _))
    (oW 0x28 (by decide)) (tW 0x54 (by decide)) (tA 0x7C (by decide)) (env.sO.sub (by decide)) (oS 0x28 (by decide)) (tS 0x54 (by decide)) (tS 0x7C (by decide))
  have inv9 := invStep inv8 f9 (oIn 0x28 (by decide))
  have hc9 : CodeIn n9.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv9
  have slot9 : ∀ k, 0x25C ≤ k → k < 0x270 → n9.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f9 _ (gk k (by omega) h2) (oSl 0x28 k (by decide) (by omega))).trans (slot8 k h1 h2)
  have R9 : EanRegs m n9 F out ep np := R8.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k9 q h.2.2.2.2.2 h.2.2.2.2.1, rb9 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 10
  obtain ⟨b10, cb10, ub10⟩ := St.block [.aluImm .add a0 (18 : Fin 32) 0x50, .aluImm .add a1 sp 0xF4, .aluImm .add a2 sp 0xA4] u9 hc9
    (off' := 0xb0) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub10
  have rb10 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b10 q = reg n9 q := fun q hv h0 h1 h2 => by
    rw [ub10.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n10, c10, u10, sp10, k10, w10, f10⟩ := subCall (out + 0x50) (F + BitVec.ofNat 32 0xF4) (F + BitVec.ofNat 32 0xA4) ub10.self hc9 inv9
    esn_at_b0 esn_at_b4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb10 sp (by decide) (by decide) (by decide) (by decide)]; exact R9.1)
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R9.1, R9.2.1, R9.2.2.1, R9.2.2.2.1, R9.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u9.zero]; first | rfl | exact zw _))
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R9.1, R9.2.1, R9.2.2.1, R9.2.2.2.1, R9.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u9.zero]; first | rfl | exact zw _))
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R9.1, R9.2.1, R9.2.2.1, R9.2.2.2.1, R9.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u9.zero]; first | rfl | exact zw _))
    (aligned_add env.hout (by decide)) (tA 0xF4 (by decide)) (tA 0xA4 (by decide)) (env.sO.sub (by decide)) (oS 0x50 (by decide)) (tS 0xF4 (by decide)) (tS 0xA4 (by decide))
  have inv10 := invStep inv9 f10 (oIn 0x50 (by decide))
  have hc10 : CodeIn n10.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv10
  have slot10 : ∀ k, 0x25C ≤ k → k < 0x270 → n10.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f10 _ (gk k (by omega) h2) (oSl 0x50 k (by decide) (by omega))).trans (slot9 k h1 h2)
  have R10 : EanRegs m n10 F out ep np := R9.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k10 q h.2.2.2.2.2 h.2.2.2.2.1, rb10 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  -- call 11
  obtain ⟨b11, cb11, ub11⟩ := St.block [.aluImm .add a0 (18 : Fin 32) 0x78, .aluImm .add a1 sp 0xF4, .aluImm .add a2 sp 0xA4] u10 hc10
    (off' := 0xc0) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub11
  have rb11 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b11 q = reg n10 q := fun q hv h0 h1 h2 => by
    rw [ub11.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n11, c11, u11, sp11, k11, w11, f11⟩ := addCall (out + 0x78) (F + BitVec.ofNat 32 0xF4) (F + BitVec.ofNat 32 0xA4) ub11.self hc10 inv10
    esn_at_c0 esn_at_c4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb11 sp (by decide) (by decide) (by decide) (by decide)]; exact R10.1)
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R10.1, R10.2.1, R10.2.2.1, R10.2.2.2.1, R10.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u10.zero]; first | rfl | exact zw _))
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R10.1, R10.2.1, R10.2.2.1, R10.2.2.2.1, R10.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u10.zero]; first | rfl | exact zw _))
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add, R10.1, R10.2.1, R10.2.2.1, R10.2.2.2.1, R10.2.2.2.2.1]
        all_goals first | rfl | exact zw _ | (rw [u10.zero]; first | rfl | exact zw _))
    (oW 0x78 (by decide)) (tW 0xF4 (by decide)) (tA 0xA4 (by decide)) (env.sO.sub (by decide)) (oS 0x78 (by decide)) (tS 0xF4 (by decide)) (tS 0xA4 (by decide))
  have inv11 := invStep inv10 f11 (oIn 0x78 (by decide))
  have hc11 : CodeIn n11.mem P edSubNielsCode := cIn env.cod sG.c env.sO.c inv11
  have slot11 : ∀ k, 0x25C ≤ k → k < 0x270 → n11.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f11 _ (gk k (by omega) h2) (oSl 0x78 k (by decide) (by omega))).trans (slot10 k h1 h2)
  have R11 : EanRegs m n11 F out ep np := R10.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k11 q h.2.2.2.2.2 h.2.2.2.2.1, rb11 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]

  -- what each call stored, in terms of the operands
  have oT0 : ∀ k, 40 ≤ k → k + 40 ≤ 0xA0 → Sep out 40 (out + BitVec.ofNat 32 k) 40 := fun k h1 h2 => by
    have := oT 0 k (.inl (by omega)) (by decide) h2; rwa [add_ofNat_zero] at this
  have E28 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (ep + 0x28) i = limbs m.mem (ep + 0x28) i := fun hM i hi => epK hM 0x28 i (by decide) hi
  have E50 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (ep + 0x50) i = limbs m.mem (ep + 0x50) i := fun hM i hi => epK hM 0x50 i (by decide) hi
  have E78 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (ep + 0x78) i = limbs m.mem (ep + 0x78) i := fun hM i hi => epK hM 0x78 i (by decide) hi
  have N28 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (np + 0x28) i = limbs m.mem (np + 0x28) i := fun hM i hi => npK hM 0x28 i (by decide) hi
  have N50 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (np + 0x50) i = limbs m.mem (np + 0x50) i := fun hM i hi => npK hM 0x50 i (by decide) hi
  have N78 : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x270 z 1 → Sep out 0xA0 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M (np + 0x78) i = limbs m.mem (np + 0x78) i := fun hM i hi => npK hM 0x78 i (by decide) hi
  have tP : ∀ {M M' : Word → BitVec 8} {o : Word} (c : Nat), (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      c + 40 ≤ 0x11C → Sep (F + BitVec.ofNat 32 c) 40 o 40 → ∀ i, i < 10 →
      limbs M' (F + BitVec.ofNat 32 c) i = limbs M (F + BitVec.ofNat 32 c) i :=
    fun c hM hc ho i hi => pers hM (tS c hc) ho i hi
  have V1 : ∀ i, i < 10 → limbs n1.mem (F + BitVec.ofNat 32 4) i =
      feAddW (limbs m.mem (ep + 0x28)) (limbs m.mem ep) i := fun i hi => by
    rw [w1 i hi]; unfold feAddW
    rw [E28 inv0 i hi, ep0K inv0 i hi]
  have V2 : ∀ i, i < 10 → limbs n2.mem (F + BitVec.ofNat 32 0x2C) i =
      feSubW (limbs m.mem (ep + 0x28)) (limbs m.mem ep) i := fun i hi => by
    rw [w2 i hi, feSubW_congr (E28 inv1) (ep0K inv1)]
  have V3 : ∀ i, i < 10 → limbs n3.mem (F + BitVec.ofNat 32 0x54) i = esnPP m.mem ep np i := fun i hi => by
    rw [w3 i hi, feMulW_congr (x' := feAddW (limbs m.mem (ep + 0x28)) (limbs m.mem ep)) (y' := limbs m.mem (np + 0x28))
      (fun j hj => by
        rw [tP 4 f2 (by decide) (tT 4 0x2C (.inl (by decide)) (by decide) (by decide)) j hj]; exact V1 j hj)
      (N28 inv2)]
    rfl
  have V4 : ∀ i, i < 10 → limbs n4.mem (F + BitVec.ofNat 32 0x7C) i = esnMM m.mem ep np i := fun i hi => by
    rw [w4 i hi, feMulW_congr (x' := feSubW (limbs m.mem (ep + 0x28)) (limbs m.mem ep)) (y' := limbs m.mem np)
      (fun j hj => by
        rw [tP 0x2C f3 (by decide) (tT 0x2C 0x54 (.inl (by decide)) (by decide) (by decide)) j hj]; exact V2 j hj)
      (np0K inv3)]
    rfl
  have V5 : ∀ i, i < 10 → limbs n5.mem (F + BitVec.ofNat 32 0xA4) i = eanTT m.mem ep np i := fun i hi => by
    rw [w5 i hi, feMulW_congr (x' := limbs m.mem (ep + 0x78)) (y' := limbs m.mem (np + 0x78)) (E78 inv4) (N78 inv4)]
    rfl
  have V6 : ∀ i, i < 10 → limbs n6.mem (F + BitVec.ofNat 32 0xCC) i =
      feMulW (limbs m.mem (ep + 0x50)) (limbs m.mem (np + 0x50)) i := fun i hi => by
    rw [w6 i hi, feMulW_congr (x' := limbs m.mem (ep + 0x50)) (y' := limbs m.mem (np + 0x50)) (E50 inv5) (N50 inv5)]
  have V7 : ∀ i, i < 10 → limbs n7.mem (F + BitVec.ofNat 32 0xF4) i = eanZZ2 m.mem ep np i := fun i hi => by
    rw [w7 i hi]; unfold eanZZ2 feAddW; rw [V6 i hi]
  -- the temporaries stay until they are read
  have PP7 : ∀ i, i < 10 → limbs n7.mem (F + BitVec.ofNat 32 0x54) i = esnPP m.mem ep np i := fun i hi => by
    rw [tP 0x54 f7 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x54 f6 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x54 f5 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x54 f4 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi]
    exact V3 i hi
  have MM7 : ∀ i, i < 10 → limbs n7.mem (F + BitVec.ofNat 32 0x7C) i = esnMM m.mem ep np i := fun i hi => by
    rw [tP 0x7C f7 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x7C f6 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0x7C f5 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi]
    exact V4 i hi
  have tO0 : ∀ c, c + 40 ≤ 0x11C → Sep (F + BitVec.ofNat 32 c) 40 out 40 := fun c h => by
    have := tO c 0 h (by decide); rwa [add_ofNat_zero] at this
  have TT9 : ∀ i, i < 10 → limbs n9.mem (F + BitVec.ofNat 32 0xA4) i = eanTT m.mem ep np i := fun i hi => by
    rw [tP 0xA4 f9 (by decide) (tO _ _ (by decide) (by decide)) i hi, tP 0xA4 f8 (by decide) (tO0 _ (by decide)) i hi,
      tP 0xA4 f7 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi,
      tP 0xA4 f6 (by decide) (tT _ _ (.inl (by decide)) (by decide) (by decide)) i hi]
    exact V5 i hi
  have TT10 : ∀ i, i < 10 → limbs n10.mem (F + BitVec.ofNat 32 0xA4) i = eanTT m.mem ep np i := fun i hi => by
    rw [tP 0xA4 f10 (by decide) (tO _ _ (by decide) (by decide)) i hi]; exact TT9 i hi
  have ZZ9 : ∀ i, i < 10 → limbs n9.mem (F + BitVec.ofNat 32 0xF4) i = eanZZ2 m.mem ep np i := fun i hi => by
    rw [tP 0xF4 f9 (by decide) (tO _ _ (by decide) (by decide)) i hi, tP 0xF4 f8 (by decide) (tO0 _ (by decide)) i hi]
    exact V7 i hi
  have ZZ10 : ∀ i, i < 10 → limbs n10.mem (F + BitVec.ofNat 32 0xF4) i = eanZZ2 m.mem ep np i := fun i hi => by
    rw [tP 0xF4 f10 (by decide) (tO _ _ (by decide) (by decide)) i hi]; exact ZZ9 i hi
  -- the result's quarters
  have X8 : ∀ i, i < 10 → limbs n8.mem out i = feSubW (esnPP m.mem ep np) (esnMM m.mem ep np) i := fun i hi => by
    rw [w8 i hi, feSubW_congr PP7 MM7]
  have Y9 : ∀ i, i < 10 → limbs n9.mem (out + 0x28) i = feAddW (esnPP m.mem ep np) (esnMM m.mem ep np) i :=
    fun i hi => by
      rw [w9 i hi]; unfold feAddW
      rw [tP 0x54 f8 (by decide) (tO0 _ (by decide)) i hi, tP 0x7C f8 (by decide) (tO0 _ (by decide)) i hi,
        PP7 i hi, MM7 i hi]
  have Z10 : ∀ i, i < 10 → limbs n10.mem (out + 0x50) i = feSubW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i :=
    fun i hi => by rw [w10 i hi, feSubW_congr ZZ9 TT9]
  have T11 : ∀ i, i < 10 → limbs n11.mem (out + 0x78) i = feAddW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i :=
    fun i hi => by rw [w11 i hi]; unfold feAddW; rw [ZZ10 i hi, TT10 i hi]
  have X11 : ∀ i, i < 10 → limbs n11.mem out i = feSubW (esnPP m.mem ep np) (esnMM m.mem ep np) i := fun i hi => by
    rw [pers f11 oS0 (oT0 0x78 (by decide) (by decide)) i hi, pers f10 oS0 (oT0 0x50 (by decide) (by decide)) i hi,
      pers f9 oS0 (oT0 0x28 (by decide) (by decide)) i hi]
    exact X8 i hi
  have Y11 : ∀ i, i < 10 → limbs n11.mem (out + 0x28) i = feAddW (esnPP m.mem ep np) (esnMM m.mem ep np) i :=
    fun i hi => by
      have e1 : limbs n11.mem (out + 0x28) i = limbs n10.mem (out + 0x28) i :=
        pers f11 (oS 0x28 (by decide)) (oT 0x28 0x78 (.inl (by decide)) (by decide) (by decide)) i hi
      have e2 : limbs n10.mem (out + 0x28) i = limbs n9.mem (out + 0x28) i :=
        pers f10 (oS 0x28 (by decide)) (oT 0x28 0x50 (.inl (by decide)) (by decide) (by decide)) i hi
      rw [e1, e2]; exact Y9 i hi
  have Z11 : ∀ i, i < 10 → limbs n11.mem (out + 0x50) i = feSubW (eanZZ2 m.mem ep np) (eanTT m.mem ep np) i :=
    fun i hi => by
      have e1 : limbs n11.mem (out + 0x50) i = limbs n10.mem (out + 0x50) i :=
        pers f11 (oS 0x50 (by decide)) (oT 0x50 0x78 (.inl (by decide)) (by decide) (by decide)) i hi
      rw [e1]; exact Z10 i hi
  -- the epilogue, from 0xC8
  obtain ⟨e1, de1, ue1⟩ := u11.aluImm hc11 esn_at_c8 (off' := 0xCA) (by decide)
  have rA : upd (reg n11) a0 (aluEval .add (reg n11 sp) 0x100) a0 = G + BitVec.ofNat 32 0x240 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, R11.1, eA]
  have hpsA : ∀ p ∈ esnPs, p.1 ≠ a0 := by decide
  obtain ⟨e2, ce2, ue2⟩ := St.block (restoreBlockR a0 esnPs) ue1 hc11 esnRestore_end
    (restoreBlockR_ok n11.mem _ a0 (by decide) esnPs _ rA hpsA fun q hq => by
      simp only [esnPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        exact aligned_add (aligned_add hGa (k := 0x240) (by decide)) (by decide))
  simp only [restoreBlockR_run n11.mem _ a0 (by decide) esnPs _ rA hpsA] at ue2
  obtain ⟨e3, de3, ue3⟩ := ue2.aluImm hc11 esn_at_da (off' := 0xDC) (by decide)
  obtain ⟨e4, de4, pc4, mem4, regs4⟩ := ue3.jalr hc11 esn_at_dc
  have slotW : ∀ r o, (r, o) ∈ esnPs → memLoad32 n11.mem (G + BitVec.ofNat 32 0x240 + o) = reg m r := fun r o h => by
    have ho : 0x1C ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
      simp only [esnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, add_ofNat_assoc, slot11 _ (by omega) (by omega)]
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs n11.mem (G + BitVec.ofNat 32 0x240) f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ esnPs →
      restoreRegs n11.mem (G + BitVec.ofNat 32 0x240) (upd (reg n11) a0 (aluEval .add (reg n11 sp) 0x100)) esnPs r =
        reg m r := fun r o hm => by
    simp only [esnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  have rsp : restoreRegs n11.mem (G + BitVec.ofNat 32 0x240) (upd (reg n11) a0 (aluEval .add (reg n11 sp) 0x100))
      esnPs sp = F := by
    rw [rr _ _ sp (by decide) (by decide), upd_ne (by decide) (by decide)]; exact R11.1
  have S : Steps m n11 := by
    have S0 : Steps m m4 := .cons d1 (.cons d2 (cp3.trans cp4))
    exact S0.trans (cb1.trans (c1.trans (cb2.trans (c2.trans (cb3.trans (c3.trans (cb4.trans (c4.trans
      (cb5.trans (c5.trans (cb6.trans (c6.trans (cb7.trans (c7.trans (cb8.trans (c8.trans (cb9.trans (c9.trans
      (cb10.trans (c10.trans (cb11.trans c11)))))))))))))))))))))
  refine ⟨e4, S.trans (.cons de1 (ce2.trans (.cons de3 (.single de4)))), ?_, ?_, fun q hq => ?_,
    fun i hi => ?_, fun x hx ho => ?_⟩
  · rw [pc4]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x2C (by decide), hra, add_lit_zero, hret]
  · rw [regs4]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp, eS]
  · rw [regs4]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        (q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
          q ≠ a0 ∧ (∀ p ∈ esnPs, p.1 ≠ q)) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, ha, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x2C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x28 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x24 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x20 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x1C (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps, upd_ne h0 ha]; exact R11.2.2.2.2.2 q h1
  · rw [mem4]; exact ⟨X11 i hi, Y11 i hi, Z11 i hi, T11 i hi⟩
  · rw [mem4]; exact inv11 x hx ho

end C3.RV32
