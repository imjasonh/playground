import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.AcceptIndexSpec
import C3BootProofs.Proofs.FlashPart
import C3BootProofs.Proofs.MagicCur
import C3BootProofs.Proofs.U16
import C3BootProofs.Proofs.MemsetAny
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.TufIndex
import C3BootProofs.Proofs.Sha2Update

/-!
# `boot_main`'s first closure: the index stage's frame

The index stage, from 0x2A6 to 0x4E4, reads the TUF part's header and its
index of lengths from flash and copies the index into the frame. This file
holds what its proof shares: the callees' code (`AcIndexEnv`), the stage's
fixed data (`AcxP`, `AcxK`), what every step keeps (`AcxC`), the exit from
0x434 (`acx_exit`), and one lemma for each kind of call.

The stage writes the frame below `sp + 0x34` and from `sp + 0x244` to the
saves; `AcxKeep` says that every other byte keeps its value.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

set_option maxRecDepth 100000

/-- The callees' code that the index stage runs, and the ROM's code. -/
structure AcIndexEnv (romBase : Word) (romCode : List Nat) (M : Word → BitVec 8) : Prop where
  fpr : CodeIn M (img% flashPartReadAddress) flashPartReadCode
  frd : CodeIn M (img% flashReadAddress) flashReadCode
  mset : CodeIn M (img% memsetAddress) memsetCode
  fw : CodeIn M (img% romFlashReadWordsAddress) romFlashReadWordsCode
  rom : CodeIn M romBase romCode
  magic : CodeIn M (img% readerMagicAddress) readerMagicCode
  array4 : CodeIn M (img% readerArray4Address) readerArray4Code
  bytes : CodeIn M (img% readerBytesAddress) readerBytesCode
  u16 : CodeIn M (img% readerU16Address) readerU16Code
  u32 : CodeIn M (img% readerU32Address) readerU32Code
  tid : CodeIn M (img% tufIndexDocAddress) tufIndexDocCode
  mcs : CodeIn M (img% memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M (img% memcpyBodyAddress) memcpyBodyCode
  tbl : CodeIn M (img% acRejectTableAddress) acRejectTableData

/-- The index stage's fixed data: flash and the ROM, the frame, and the
state at 0x2A6. -/
structure AcxP where
  flash : Nat → BitVec 8
  R : Nat
  Rl : Nat
  romBase : Word
  romCode : List Nat
  B : Word
  Bf : Word
  g : Word
  t : Word
  r : Word
  v : Nat → Word
  M0 : Word → BitVec 8
  n0 : Machine

/-- What the index stage assumes of its fixed data. -/
structure AcxK (P : AcxP) : Prop where
  rd : RomRead P.flash P.R P.romBase P.romCode
  log : RomFn P.romBase P.romCode 0x40000040 P.Rl fun _ => True
  hRl : P.Rl ≤ 0x3A50
  hR : P.R ≤ 0x3A50 - 0x150
  hR4 : P.R % 4 = 0
  F : Fr P.B 0x5A70
  sRB : Sep P.B 0x5A70 P.romBase P.romCode.length
  E : ∀ M, (∀ x, Sep x 1 P.B 0x5A70 → Sep x 1 P.Bf acBufLen → M x = P.M0 x) → AcIndexEnv P.romBase P.romCode M
  I : AcInv P.B P.Bf P.g P.t P.v P.M0 P.n0
  hr : memLoad32 P.n0.mem (acSlot P.B 0x40) = P.r
  C : CodeIn P.n0.mem AC bootMainClosure0Code

/-- Memory `M'` agrees with `M` but for the frame below `sp + 0x34` and
from `sp + 0x244` to the saves. -/
def AcxKeep (B : Word) (M M' : Word → BitVec 8) : Prop :=
  ∀ x : Word, (x.toNat < B.toNat ∨ B.toNat + 0x3A84 ≤ x.toNat) →
    (x.toNat < B.toNat + 0x3C94 ∨ B.toNat + 0x5A38 ≤ x.toNat) → M' x = M x

theorem AcxKeep.trans {B : Word} {M0 M1 M2 : Word → BitVec 8} (h1 : AcxKeep B M0 M1)
    (h2 : AcxKeep B M1 M2) : AcxKeep B M0 M2 := fun x a b => (h2 x a b).trans (h1 x a b)

/-- The registers the index stage never writes: `sp`, `gp`, `tp`, `s4`, `s5`,
`s7`, `s8`, `s9`, and `s11`. -/
def acxL (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 20, 21, 23, 24, 25, 27]

/-- What every step of the index stage keeps. -/
structure AcxC (P : AcxP) (n : Machine) : Prop where
  kl : ∀ q, acxL q = true → reg n q = reg P.n0 q
  keep : AcxKeep P.B P.n0.mem n.mem

/-- The registers that every call in the index stage keeps. -/
def acxS (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- From `n`, the closure reaches an exit or a state that `Q` holds of. -/
def AcxTo (P : AcxP) (n : Machine) (Q : Machine → Prop) : Prop :=
  ∃ n', Steps n n' ∧ ((AcInv P.B P.Bf P.g P.t P.v P.M0 n' ∧ AcFail P.B P.r n') ∨ Q n')

theorem AcxTo.pre {P : AcxP} {n n1 : Machine} {Q : Machine → Prop} (h : Steps n n1) (e : AcxTo P n1 Q) :
    AcxTo P n Q := by
  obtain ⟨n', s, h'⟩ := e
  exact ⟨n', h.trans s, h'⟩

theorem AcxTo.done {P : AcxP} {n : Machine} {Q : Machine → Prop} (h : Q n) : AcxTo P n Q :=
  ⟨n, .refl _, .inr h⟩

theorem AcxTo.bind {P : AcxP} {n : Machine} {Q R : Machine → Prop} (e : AcxTo P n Q)
    (k : ∀ n', Q n' → AcxTo P n' R) : AcxTo P n R := by
  obtain ⟨n1, s1, h1 | h1⟩ := e
  · exact ⟨n1, s1, .inl h1⟩
  · exact AcxTo.pre s1 (k n1 h1)

/-! ## Frame arithmetic -/

theorem acx_sepR {B : Word} (F : Fr B 0x5A70) {c l : Nat} (hcl : c + l ≤ 0x5A70) {x : Word}
    (h : x.toNat < B.toNat + c ∨ B.toNat + c + l ≤ x.toNat) : Sep (B + BitVec.ofNat 32 c) l x 1 := by
  intro i hi j hj e
  have hj0 : j = 0 := by omega
  subst hj0
  have := congrArg BitVec.toNat e
  rw [add_ofNat_assoc, add_ofNat_zero, F.at _ (by omega)] at this
  omega

theorem acx_sepR' {B : Word} (F : Fr B 0x5A70) {c l : Nat} (hcl : c + l ≤ 0x5A70) {x : Word}
    (h : Sep (B + BitVec.ofNat 32 c) l x 1) : x.toNat < B.toNat + c ∨ B.toNat + c + l ≤ x.toNat := by
  by_cases h1 : x.toNat < B.toNat + c
  · exact Or.inl h1
  by_cases h2 : B.toNat + c + l ≤ x.toNat
  · exact Or.inr h2
  exfalso
  have := F.hi
  refine h (x.toNat - B.toNat - c) (by omega) 0 (by decide) ?_
  rw [add_ofNat_assoc, add_ofNat_zero]
  apply BitVec.eq_of_toNat_eq
  rw [F.at _ (by omega)]; omega

theorem acx_out {B : Word} (F : Fr B 0x5A70) {x : Word} (h : Sep x 1 B 0x5A70) :
    x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat := by
  have := acx_sepR' F (c := 0) (l := 0x5A70) (by decide) (by rw [add_ofNat_zero]; exact h.symm)
  omega

theorem acx_ss {B : Word} {c l d k : Nat} (hc : c + l ≤ 0x5A70) (hd : d + k ≤ 0x5A70)
    (h : c + l ≤ d ∨ d + k ≤ c) : Sep (B + BitVec.ofNat 32 c) l (B + BitVec.ofNat 32 d) k :=
  sep_offsets B h (by omega) (by omega)

/-- A word in the frame that a write left alone. -/
theorem acx_wz {B : Word} (F : Fr B 0x5A70) {M M' : Word → BitVec 8} {e : Nat} (he : e + 4 ≤ 0x5A70)
    (h : ∀ x : Word, B.toNat + e ≤ x.toNat → x.toNat < B.toNat + e + 4 → M' x = M x) :
    memLoad32 M' (B + BitVec.ofNat 32 e) = memLoad32 M (B + BitVec.ofNat 32 e) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    exact h _ (by rw [F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)

/-- A byte in the frame that a write left alone. -/
theorem acx_bz {B : Word} (F : Fr B 0x5A70) {M M' : Word → BitVec 8} {e : Nat} (he : e < 0x5A70)
    (h : ∀ x : Word, B.toNat + e ≤ x.toNat → x.toNat < B.toNat + e + 1 → M' x = M x) :
    M' (B + BitVec.ofNat 32 e) = M (B + BitVec.ofNat 32 e) :=
  h _ (by rw [F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)

theorem acx_al {B : Word} (F : Fr B 0x5A70) {e : Nat} (he : e ≤ 0x5A70) (h4 : e % 4 = 0) :
    (B + BitVec.ofNat 32 e).toNat % 4 = 0 := by
  have := F.al; rw [F.at _ he]; omega

theorem acx_hiSep {B : Word} (F : Fr B 0x5A70) {c n : Nat} (h : c + n ≤ 0x5A70) {b : Word} {len : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (B + BitVec.ofNat 32 c) n b len :=
  F.sepHi h hb hl

/-! ## `AcxC` -/

theorem AcxC.rsp {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) : reg n sp = P.B + 0x3A50 := by
  rw [A.kl sp (by decide)]; exact K.I.sp

theorem AcxC.inv {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) :
    AcInv P.B P.Bf P.g P.t P.v P.M0 n where
  sp := A.rsp K
  gp := by rw [A.kl 3 (by decide)]; exact K.I.gp
  tp := by rw [A.kl 4 (by decide)]; exact K.I.tp
  saves := fun k hk => by
    have F := K.F
    rw [← K.I.saves k hk]
    exact acx_wz F (by omega) fun x h1 h2 => A.keep x (by omega) (by omega)
  out := fun x h1 h2 => by
    have F := K.F
    have := acx_out F h1
    rw [A.keep x (by omega) (by omega)]; exact K.I.out x h1 h2

theorem AcxC.env {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) :
    AcIndexEnv P.romBase P.romCode n.mem :=
  K.E n.mem (A.inv K).out

theorem AcxC.code {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) :
    CodeIn n.mem AC bootMainClosure0Code := fun i hi => by
  have F := K.F
  have hF := F.hi
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have h2 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h := BitVec.toNat_add AC (BitVec.ofNat 32 i)
  rw [h2, Nat.mod_eq_of_lt (by omega)] at h
  rw [A.keep _ (by omega) (by omega)]
  exact K.C i hi

theorem AcxC.r {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) :
    memLoad32 n.mem (acSlot P.B 0x40) = P.r := by
  have F := K.F
  rw [← K.hr]
  exact acx_wz F (by decide) fun x h1 h2 => A.keep x (by omega) (by omega)

/-- `AcxC` after a step that keeps the registers of `acxL` and memory
outside the frame's written parts. -/
theorem AcxC.next {P : AcxP} {n n' : Machine} (A : AcxC P n) (hk : ∀ q, acxL q = true → reg n' q = reg n q)
    (hm : AcxKeep P.B n.mem n'.mem) : AcxC P n' :=
  ⟨fun q hq => (hk q hq).trans (A.kl q hq), A.keep.trans hm⟩

/-- `AcxC` after a call that keeps the registers of `acxS`. -/
theorem AcxC.call {P : AcxP} {n n' : Machine} (A : AcxC P n) (hk : ∀ q, acxS q = true → reg n' q = reg n q)
    (hm : AcxKeep P.B n.mem n'.mem) : AcxC P n' :=
  A.next (fun q hq => hk q (by revert hq; revert q; decide)) hm

/-! ## The exit from 0x434 -/

/-- From 0x434: reload the result and the slot, and move the error to `s5`. -/
def acxX1 : List BInstr := [.lw (19 : Fin 32) sp 0x40, .lw (8 : Fin 32) sp 0x3C, .alu .add (21 : Fin 32) x0 a0]

theorem acxX1_end : blockEnd bootMainClosure0Code 0x434 acxX1 = some 0x43A := by decide

/-- From 0x7DA: the code's low byte, and 0x20. -/
def acxX2 : List BInstr := [.aluImm .and a0 (21 : Fin 32) 0xFF, .aluImm .add a1 x0 0x20]

theorem acxX2_end : blockEnd bootMainClosure0Code 0x7DA acxX2 = some 0x7E2 := by decide

/-- From 0x830: the log argument for code 0x26. -/
def acxX3 : List BInstr := [.aluImm .add a1 x0 0x106]

theorem acxX3_end : blockEnd bootMainClosure0Code 0x830 acxX3 = some 0x834 := by decide

theorem acx_inv_eq {P : AcxP} {n n' : Machine} (I : AcInv P.B P.Bf P.g P.t P.v P.M0 n) (hm : n'.mem = n.mem)
    (h2 : reg n' sp = reg n sp) (h3 : reg n' (3 : Fin 32) = reg n (3 : Fin 32))
    (h4 : reg n' (4 : Fin 32) = reg n (4 : Fin 32)) : AcInv P.B P.Bf P.g P.t P.v P.M0 n' :=
  ⟨by rw [h2]; exact I.sp, by rw [h3]; exact I.gp, by rw [h4]; exact I.tp, by rw [hm]; exact I.saves,
    by rw [hm]; exact I.out⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The exit from 0x434**, with an error code in `a0` that is below 0x20
or 0x26 (a failed flash read): the code reaches the closure's exit at
0x802, or, for 0x26, logs the code and reaches the exit at 0x16A. -/
theorem acx_exit {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x434 (reg n))
    {c : Nat} (hc : reg n a0 = BitVec.ofNat 32 c) (hcl : c < 0x20 ∨ c = 0x26) {Q : Machine → Prop} :
    AcxTo P n Q := by
  have F := K.F
  have C := A.code K
  have E := A.env K
  have I := A.inv K
  have rsp := A.rsp K
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block acxX1 C acxX1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acxX1]; simp +decide only [upd, ↓reduceIte, and_true]
    rw [rsp]; exact ⟨ac_fa F 0x40 (by decide) (by decide), ac_fa F 0x3C (by decide) (by decide)⟩)
  have M1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 21 → reg n1 q = reg n q := fun q h0 h1 h2 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acxX1]; revert h0 h1 h2; revert q; decide)]
  have q19 : reg n1 (19 : Fin 32) = P.r := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acxX1, upd, ↓reduceIte]
    rw [rsp, show (P.B + 0x3A50 + 0x40 : Word) = acSlot P.B 0x40 by rw [BitVec.add_assoc]; rfl]; exact A.r K
  have q21 : reg n1 (21 : Fin 32) = BitVec.ofNat 32 c := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acxX1, upd, ↓reduceIte]
    rw [← hc]; exact BitVec.zero_add _
  have t1 : St n1.mem AC n1 0x43A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have C1 : CodeIn n1.mem AC bootMainClosure0Code := by rw [M1]; exact C
  obtain ⟨n2, e2, t2⟩ := t1.jump C1 ac_at_43a (off' := 0x7DA) (by decide) (by rw [t1.pc]; decide)
  obtain ⟨n3, c3, u3⟩ := t2.block acxX2 C1 acxX2_end ⟨trivial, trivial, trivial⟩
  have M3 : n3.mem = n.mem := u3.mem.trans M1
  have z1 : reg n1 0 = 0 := t1.zero
  have r3 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 21 → q.val ≠ 10 → q.val ≠ 11 →
      reg n3 q = reg n q := fun q h0 h1 h2 h3 h4 => by
    rw [u3.regs, runBlock_reg _ _ _ q z1 (by simp only [acxX2]; revert h3 h4; revert q; decide), r1 q h0 h1 h2]
  have q19' : reg n3 (19 : Fin 32) = P.r := by
    rw [u3.regs, runBlock_reg _ _ _ _ z1 (by decide), q19]
  have a0v : reg n3 a0 = BitVec.ofNat 32 c &&& 0xFF := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acxX2, upd, ↓reduceIte]; rw [q21]; rfl
  have a1v : reg n3 a1 = 0x20 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acxX2, upd, ↓reduceIte]
  have t3 : St n3.mem AC n3 0x7E2 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have C3 : CodeIn n3.mem AC bootMainClosure0Code := by rw [M3]; exact C
  have I3 : AcInv P.B P.Bf P.g P.t P.v P.M0 n3 := acx_inv_eq I M3
    (r3 sp (by decide) (by decide) (by decide) (by decide) (by decide))
    (r3 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (r3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  rcases hcl with hlt | rfl
  · have hand : (BitVec.ofNat 32 c &&& 0xFF).toNat < 0x20 := by
      rw [BitVec.toNat_and]
      have h1 : (BitVec.ofNat 32 c).toNat = c := by rw [BitVec.toNat_ofNat]; omega
      have := Nat.and_le_left (n := (BitVec.ofNat 32 c).toNat) (m := (0xFF : Word).toNat)
      omega
    obtain ⟨n4, e4, t4⟩ := t3.taken C3 0x802 ac_at_7e2 (by decide)
      (by rw [a0v, a1v]; simp only [branchTaken, BitVec.ult, decide_eq_true_eq]; exact hand)
    refine ⟨n4, c1.trans ((Steps.single e2).trans (c3.trans (.single e4))), .inl ⟨?_, ?_⟩⟩
    · exact acx_inv_eq I3 t4.mem (by rw [t4.regs]) (by rw [t4.regs]) (by rw [t4.regs])
    · exact .inr (.inr (.inr ⟨t4.pc, by rw [t4.regs]; exact q19'⟩))
  · obtain ⟨n4, e4, t4⟩ := t3.notTaken C3 0x7E6 ac_at_7e2 (by decide)
      (by rw [a0v, a1v]; decide)
    have hk : (6 : Nat) < 7 := by decide
    obtain ⟨n5, c5, u5⟩ := t4.block (off' := 0x7FA) acJ2 C3 (by decide) (by
      simp only [BlockOk, BInstr.ok, BInstr.run, acJ2]; simp +decide only [upd, ↓reduceIte, and_true]
      rw [a0v, show BitVec.ofNat 32 0x26 &&& 0xFF = BitVec.ofNat 32 (0x20 + 6) by decide, ac_tbl_addr hk]
      exact ⟨trivial, trivial, trivial, trivial, trivial, ac_tbl_al hk⟩)
    have a5 : reg n5 a0 = AC + BitVec.ofNat 32 0x830 := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acJ2, upd, ↓reduceIte]
      rw [a0v, show BitVec.ofNat 32 0x26 &&& 0xFF = BitVec.ofNat 32 (0x20 + 6) by decide, ac_tbl_addr hk, M3]
      exact ac_tbl_load E.tbl hk
    have z3 : reg n3 0 = 0 := t3.zero
    have r5 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 21 → q.val ≠ 10 → q.val ≠ 11 →
        reg n5 q = reg n q := fun q h0 h1 h2 h3 h4 => by
      rw [u5.regs, runBlock_reg _ _ _ q z3 (by simp only [acJ2]; revert h3 h4; revert q; decide),
        r3 q h0 h1 h2 h3 h4]
    have q19'' : reg n5 (19 : Fin 32) = P.r := by
      rw [u5.regs, runBlock_reg _ _ _ _ z3 (by decide), q19']
    have M5 : n5.mem = n.mem := u5.mem.trans M3
    have t5 : St n.mem AC n5 0x7FA (reg n5) := ⟨u5.pc, M5, fun _ => rfl⟩
    obtain ⟨n6, e6, pc6, m6, k6⟩ := t5.jalr C ac_at_7fa
    have t6 : St n.mem AC n6 0x830 (reg n6) :=
      ⟨by rw [pc6, a5]; decide, m6, fun _ => rfl⟩
    have z6 : reg n6 0 = 0 := t6.zero
    obtain ⟨n7, c7, u7⟩ := t6.block acxX3 C acxX3_end ⟨trivial, trivial⟩
    have t7 : St n.mem AC n7 0x834 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
    obtain ⟨n8, e8, t8⟩ := t7.jump C ac_at_834 (off' := 0x806) (by decide) (by rw [t7.pc]; decide)
    obtain ⟨n9, c9, u9⟩ := t8.block (off' := 0x80E) acR1 C (by decide) ⟨trivial, trivial, trivial⟩
    have z8 : reg n7 0 = 0 := t7.zero
    have r9 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 21 → q.val ≠ 10 → q.val ≠ 11 →
        reg n9 q = reg n q := fun q h0 h1 h2 h3 h4 => by
      rw [u9.regs, runBlock_reg _ _ _ q z8 (by simp only [acR1]; revert h3; revert q; decide), u7.regs,
        runBlock_reg _ _ _ q z6 (by simp only [acxX3]; revert h4; revert q; decide), k6, r5 q h0 h1 h2 h3 h4]
    have q19''' : reg n9 (19 : Fin 32) = P.r := by
      rw [u9.regs, runBlock_reg _ _ _ _ z8 (by decide), u7.regs, runBlock_reg _ _ _ _ z6 (by decide), k6, q19'']
    have M9 : n9.mem = n.mem := u9.mem
    have t9 : St n9.mem AC n9 0x80E (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have rsp9 : reg n9 sp = P.B + 0x3A50 := by
      rw [r9 sp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rsp
    have hRl := K.hRl
    obtain ⟨n10, c10, pc10, k10, m10⟩ :=
      ac_log K.log K.hRl (by rw [M9]; exact C) (by rw [M9]; exact E.rom) F t9 rsp9 ac_at_80e ac_at_812
        (by decide) (by decide)
    have W10 : ∀ x, Sep (P.B + BitVec.ofNat 32 (0x3A50 - P.Rl)) P.Rl x 1 → n10.mem x = n.mem x :=
      fun x hx => by rw [m10 x hx, M9]
    have t10 : St n10.mem AC n10 0x816 (reg n10) := ⟨pc10, rfl, fun _ => rfl⟩
    have C10 := ac_wCode F K.hRl W10 C
    obtain ⟨n11, e11, t11⟩ := t10.jump C10 ac_at_816 (off' := 0x16A) (by decide) (by rw [t10.pc]; decide)
    have k11 : ∀ q : Fin 32, romKeep q = true → reg n11 q = reg n9 q := fun q hq => by
      rw [t11.regs q, k10 q hq]
    refine ⟨n11, c1.trans ((Steps.single e2).trans (c3.trans ((Steps.single e4).trans (c5.trans
      ((Steps.single e6).trans (c7.trans ((Steps.single e8).trans (c9.trans (c10.trans (.single e11)))))))))),
      .inl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, .inr (.inl ⟨t11.pc, ?_⟩)⟩⟩
    · rw [k11 sp (by decide)]; exact rsp9
    · rw [k11 3 (by decide), r9 3 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact I.gp
    · rw [k11 4 (by decide), r9 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact I.tp
    · rw [t11.mem]; exact ac_wSaves F K.hRl W10 I.saves
    · intro x h1 h2
      rw [t11.mem, W10 x (h1.symm.sub (c := 0x3A50 - P.Rl) (l := P.Rl) (by omega))]
      exact I.out x h1 h2
    · rw [k11 19 (by decide)]; exact q19'''

/-! ## Calls -/

theorem acx_magicMem_out {M : Word → BitVec 8} {self x : Word} (h : Sep (self + 8) 4 x 1) :
    magicMem M self x = M x := by
  unfold magicMem
  cases bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => rfl
  | some pe => exact memStore32_get_sep h

theorem acx_u16Mem_out {M : Word → BitVec 8} {self x : Word} (h : Sep (self + 8) 4 x 1) :
    u16Mem M self x = M x := by
  unfold u16Mem
  cases bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 2 with
  | none => rfl
  | some pe => exact memStore32_get_sep h

theorem acx_u32Mem_out {M : Word → BitVec 8} {out self x : Word} (ho : Sep out 8 x 1)
    (h : Sep (self + 8) 4 x 1) : Cur.u32Mem M out self x = M x := by
  have n0 : x ≠ out := fun e => ho 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])
  have n1 : x ≠ out + 1 := fun e => ho 1 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
  have h4 : Sep (out + 4) 4 x 1 := ho.sub (c := 4) (l := 4) (by decide)
  unfold Cur.u32Mem
  cases bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => exact (memStore8_ne n0).trans (memStore8_ne n1)
  | some pe =>
    obtain ⟨p, e⟩ := pe
    exact (memStore8_ne n0).trans ((memStore32_get_sep h4).trans (memStore32_get_sep h))

theorem acx_ptr_ne {B : Word} (F : Fr B 0x5A70) {e : Nat} (he : e ≤ 0x5A70) : B + BitVec.ofNat 32 e ≠ 0 := by
  intro h
  have hl := F.lo
  have := congrArg BitVec.toNat h
  rw [F.at _ he, show (0 : Word).toNat = 0 from rfl] at this
  omega

set_option maxHeartbeats 4000000 in
/-- A call of `flash_part_read` that reads `len` bytes into the frame at
`B + d`. -/
theorem acx_cfpr {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o : Nat} {imm o' : Word}
    (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% flashPartReadAddress))
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    {d len : Nat} (hd1 : 0x3C94 ≤ d) (hd2 : d + len ≤ 0x5A38)
    {start plen off : Word}
    (ha0 : reg n a0 = start) (ha1 : reg n a1 = plen) (ha2 : reg n a2 = off)
    (ha3 : reg n a3 = P.B + BitVec.ofNat 32 d) (ha4 : reg n a4 = BitVec.ofNat 32 len) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧ (reg n' a0 = 0 ∨ reg n' a0 = 1) ∧
      (reg n' a0 = 1 → off.toNat + len ≤ plen.toNat ∧ start.toNat + off.toNat < 2 ^ 32 ∧
        ∀ i, i < len → n'.mem (P.B + BitVec.ofNat 32 (d + i)) = P.flash (start.toNat + off.toNat + i)) ∧
      ∀ x : Word, (x.toNat < P.B.toNat + d ∨ P.B.toNat + d + len ≤ x.toNat) →
        (x.toNat < P.B.toNat + (0x3900 - P.R) ∨ P.B.toNat + 0x3A50 ≤ x.toNat) → n'.mem x = n.mem x := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have hR := K.hR
  have hR4 := K.hR4
  have E := A.env K
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (A.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have hlen : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  have hG : P.B + BitVec.ofNat 32 (0x3900 - P.R) + BitVec.ofNat 32 (0x150 + P.R) = P.B + 0x3A50 := by
    rw [add_ofNat_assoc, show 0x3900 - P.R + (0x150 + P.R) = 0x3A50 by omega]; rfl
  have env : FRdEnv n1.mem ((img% flashPartReadAddress) + 0xFFFFFEA8) (P.B + BitVec.ofNat 32 (0x3900 - P.R))
      (P.B + BitVec.ofNat 32 d) (BitVec.ofNat 32 len) P.R P.romBase P.romCode := by
    rw [mem1, show ((img% flashPartReadAddress) + 0xFFFFFEA8 : Word) = (img% flashReadAddress) by decide]
    refine ⟨rfl, E.frd, ?_, ?_, acx_al F (by omega) (by omega), hR4,
      by rw [F.at _ (by omega)]; omega, by rw [F.at _ (by omega), hlen]; omega,
      acx_hiSep F (by omega) (by decide) (by decide), acx_hiSep F (by omega) (by decide) (by decide),
      acx_hiSep F (by omega) (by decide) (by decide), ?_, ?_, ?_, E.rom, K.sRB.sub (by omega), ?_⟩
    · rw [show ((img% flashReadAddress) + (img% memsetAddress + 0x100000000 - flashReadAddress) : Word) =
        (img% memsetAddress) by decide]; exact E.mset
    · rw [show ((img% flashReadAddress) + 0xFFFFFFE8 : Word) = (img% romFlashReadWordsAddress) by decide]; exact E.fw
    · rw [hlen]; exact acx_hiSep F (by omega) (by decide) (by decide)
    · rw [hlen]; exact acx_hiSep F (by omega) (by decide) (by decide)
    · rw [hlen]; exact acx_ss (by omega) (by omega) (by omega)
    · rw [hlen]; exact K.sRB.sub (by omega)
  obtain ⟨n2, c2, pc2, sp2, k2, a02, ok2, mem2⟩ := flashPartRead_correct K.rd n1 (by rw [mem1]; exact E.fpr) env pc1
    ((r1 a0 (by decide)).trans ha0) ((r1 a1 (by decide)).trans ha1)
    ((r1 a2 (by decide)).trans ha2) ((r1 a3 (by decide)).trans ha3)
    ((r1 a4 (by decide)).trans ha4) (by rw [regs1]; simp +decide [upd]) (even_clear _ he)
    (by rw [r1 sp (by decide), A.rsp K, hG])
  have kk : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fr : ∀ x : Word, (x.toNat < P.B.toNat + d ∨ P.B.toNat + d + len ≤ x.toNat) →
      (x.toNat < P.B.toNat + (0x3900 - P.R) ∨ P.B.toNat + 0x3A50 ≤ x.toNat) → n2.mem x = n.mem x :=
    fun x hx hy => by
      rw [mem2 x (acx_sepR F (by omega) (by omega)) (by rw [hlen]; exact acx_sepR F (by omega) hx), mem1]
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, A.call kk fun x h1 h2 => fr x (by omega) (by omega),
    kk, a02, fun h => ?_, fr⟩
  obtain ⟨o1, o2, o3⟩ := ok2 h
  rw [hlen] at o1
  exact ⟨o1, o2, fun i hi => by rw [← add_ofNat_assoc]; exact o3 i (by rw [hlen]; exact hi)⟩

set_option maxHeartbeats 4000000 in
/-- A call of `Reader::magic` on the header's reader at `B + 0x580C`. -/
theorem acx_cmagic {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o : Nat} {imm o' k : Word}
    (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% readerMagicAddress))
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = P.B + BitVec.ofNat 32 0x580C) (ha1 : reg n a1 = k)
    (hp : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x580C) = P.B + BitVec.ofNat 32 0x5800)
    (hl : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5810) = 8) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧
      reg n' a0 = magicResult n.mem (P.B + BitVec.ofNat 32 0x580C) k ∧
      ∀ x : Word, (x.toNat < P.B.toNat + 0x3A20 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
        n'.mem x = magicMem n.mem (P.B + BitVec.ofNat 32 0x580C) x := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have E := A.env K
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (A.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp + 0xFFFFFFD0 = P.B + BitVec.ofNat 32 0x3A20 := by
    rw [r1 sp (by decide), A.rsp K, BitVec.add_assoc]; rfl
  have e4 : P.B + BitVec.ofNat 32 0x580C + 4 = P.B + BitVec.ofNat 32 0x5810 := add_ofNat_assoc _ _ _
  have e8 : P.B + BitVec.ofNat 32 0x580C + 8 = P.B + BitVec.ofNat 32 0x5814 := add_ofNat_assoc _ _ _
  have hp' : memLoad32 n1.mem (P.B + BitVec.ofNat 32 0x580C) = P.B + BitVec.ofNat 32 0x5800 := by
    rw [mem1]; exact hp
  have hl' : memLoad32 n1.mem (P.B + BitVec.ofNat 32 0x580C + 4) = 8 := by rw [mem1, e4]; exact hl
  have h8 : (8 : Word).toNat = 8 := rfl
  obtain ⟨n2, c2, pc2, sp2, a02, fr2, mem2⟩ := Cur.readerMagic_correct n1 (img% readerMagicAddress)
    (AC + BitVec.ofNat 32 (o + 8)) (P.B + BitVec.ofNat 32 0x580C) k
    (fun i hi => by rw [mem1]; exact E.magic i hi)
    (fun i hi => by
      rw [mem1, show ((img% readerMagicAddress) + 0xFFFFFFBA : Word) = (img% readerArray4Address) by decide]
      exact E.array4 i hi)
    (fun i hi => by
      rw [mem1, show ((img% readerMagicAddress) + 0xFFFFFFBA + 0xFFFFFF8A : Word) = (img% readerBytesAddress) by
        decide]
      exact E.bytes i hi)
    (by decide) pc1 ((r1 a0 (by decide)).trans ha0) ((r1 a1 (by decide)).trans ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he)
    (by rw [r1 sp (by decide), A.rsp K]; exact acx_al F (by decide) (by decide))
    (acx_al F (by decide) (by decide))
    ⟨by rw [hp']; exact acx_ptr_ne F (by decide), by rw [hp', hl', F.at _ (by decide), h8]; omega⟩
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_ss (by decide) (by decide) (by decide))
    (by rw [hp', hl', h8, sp1]; exact acx_ss (by decide) (by decide) (by decide))
    (by rw [hp', hl', h8, e8]; exact acx_ss (by decide) (by decide) (by decide))
  rw [mem1] at a02 mem2
  rw [sp1] at mem2
  have kk : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    rw [fr2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fr : ∀ x : Word, (x.toNat < P.B.toNat + 0x3A20 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
      n2.mem x = magicMem n.mem (P.B + BitVec.ofNat 32 0x580C) x :=
    fun x hx => mem2 x (acx_sepR F (by decide) (by omega))
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, A.call kk fun x h1 h2 => ?_, kk, a02, fr⟩
  rw [fr x (by omega), acx_magicMem_out (by rw [e8]; exact acx_sepR F (by decide) (by omega))]

set_option maxHeartbeats 4000000 in
/-- A call of `Reader::u16` on the header's reader at `B + 0x580C`. -/
theorem acx_cu16 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o : Nat} {imm o' : Word}
    (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% readerU16Address))
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = P.B + BitVec.ofNat 32 0x580C)
    (hp : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x580C) = P.B + BitVec.ofNat 32 0x5800)
    (hl : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5810) = 8) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧
      reg n' a0 = u16Result n.mem (P.B + BitVec.ofNat 32 0x580C) ∧
      ∀ x : Word, (x.toNat < P.B.toNat + 0x3A40 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
        n'.mem x = u16Mem n.mem (P.B + BitVec.ofNat 32 0x580C) x := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have E := A.env K
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (A.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp + 0xFFFFFFF0 = P.B + BitVec.ofNat 32 0x3A40 := by
    rw [r1 sp (by decide), A.rsp K, BitVec.add_assoc]; rfl
  have e4 : P.B + BitVec.ofNat 32 0x580C + 4 = P.B + BitVec.ofNat 32 0x5810 := add_ofNat_assoc _ _ _
  have e8 : P.B + BitVec.ofNat 32 0x580C + 8 = P.B + BitVec.ofNat 32 0x5814 := add_ofNat_assoc _ _ _
  have hp' : memLoad32 n1.mem (P.B + BitVec.ofNat 32 0x580C) = P.B + BitVec.ofNat 32 0x5800 := by
    rw [mem1]; exact hp
  have hl' : memLoad32 n1.mem (P.B + BitVec.ofNat 32 0x580C + 4) = 8 := by rw [mem1, e4]; exact hl
  have h8 : (8 : Word).toNat = 8 := rfl
  obtain ⟨n2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerU16_correct n1 (img% readerU16Address)
    (AC + BitVec.ofNat 32 (o + 8)) (P.B + BitVec.ofNat 32 0x580C)
    (fun i hi => by rw [mem1]; exact E.u16 i hi)
    (fun i hi => by
      rw [mem1, show ((img% readerU16Address) + 0x44 : Word) = (img% readerBytesAddress) by decide]
      exact E.bytes i hi)
    (by decide) pc1 ((r1 a0 (by decide)).trans ha0)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he)
    (by rw [r1 sp (by decide), A.rsp K]; exact acx_al F (by decide) (by decide))
    (acx_al F (by decide) (by decide))
    ⟨by rw [hp']; exact acx_ptr_ne F (by decide), by rw [hp', hl', F.at _ (by decide), h8]; omega⟩
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_ss (by decide) (by decide) (by decide))
    (by rw [hp', hl', h8, sp1]; exact acx_ss (by decide) (by decide) (by decide))
    (by rw [hp', hl', h8, e8]; exact acx_ss (by decide) (by decide) (by decide))
  rw [mem1] at a02 mem2
  rw [sp1] at mem2
  have kk : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    rw [fr2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r1 q (by revert hq; revert q; decide)]
  have fr : ∀ x : Word, (x.toNat < P.B.toNat + 0x3A40 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
      n2.mem x = u16Mem n.mem (P.B + BitVec.ofNat 32 0x580C) x :=
    fun x hx => mem2 x (acx_sepR F (by decide) (by omega))
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, A.call kk fun x h1 h2 => ?_, kk, a02, fr⟩
  rw [fr x (by omega), acx_u16Mem_out (by rw [e8]; exact acx_sepR F (by decide) (by omega))]

set_option maxHeartbeats 4000000 in
/-- A call of `Reader::u32` on the index's reader at `B + 0x5A2C`, into the
result at `B + 0x52B0`, with `len` bytes of index at `B + 0x5818`. -/
theorem acx_cu32 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o : Nat} {imm o' : Word}
    (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% readerU32Address))
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0) {len : Nat} (hlen : len ≤ 0x108)
    (ha0 : reg n a0 = P.B + BitVec.ofNat 32 0x52B0) (ha1 : reg n a1 = P.B + BitVec.ofNat 32 0x5A2C)
    (hp : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A2C) = P.B + BitVec.ofNat 32 0x5818)
    (hl : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 len) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧
      ∀ x : Word, (x.toNat < P.B.toNat + 0x3A20 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
        n'.mem x = Cur.u32Mem n.mem (P.B + BitVec.ofNat 32 0x52B0) (P.B + BitVec.ofNat 32 0x5A2C) x := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have E := A.env K
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (A.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp + 0xFFFFFFD0 = P.B + BitVec.ofNat 32 0x3A20 := by
    rw [r1 sp (by decide), A.rsp K, BitVec.add_assoc]; rfl
  have e4 : P.B + BitVec.ofNat 32 0x5A2C + 4 = P.B + BitVec.ofNat 32 0x5A30 := add_ofNat_assoc _ _ _
  have e8 : P.B + BitVec.ofNat 32 0x5A2C + 8 = P.B + BitVec.ofNat 32 0x5A34 := add_ofNat_assoc _ _ _
  have hp' : memLoad32 n1.mem (P.B + BitVec.ofNat 32 0x5A2C) = P.B + BitVec.ofNat 32 0x5818 := by
    rw [mem1]; exact hp
  have hl' : memLoad32 n1.mem (P.B + BitVec.ofNat 32 0x5A2C + 4) = BitVec.ofNat 32 len := by
    rw [mem1, e4]; exact hl
  have hL : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  obtain ⟨n2, c2, pc2, sp2, fr2, mem2⟩ := Cur.readerU32_correct n1 (img% readerU32Address)
    (AC + BitVec.ofNat 32 (o + 8)) (P.B + BitVec.ofNat 32 0x52B0) (P.B + BitVec.ofNat 32 0x5A2C)
    (fun i hi => by rw [mem1]; exact E.u32 i hi)
    (fun i hi => by
      rw [mem1, show ((img% readerU32Address) + 0x50 : Word) = (img% readerArray4Address) by decide]
      exact E.array4 i hi)
    (fun i hi => by
      rw [mem1, show ((img% readerU32Address) + 0x50 + 0xFFFFFF8A : Word) = (img% readerBytesAddress) by decide]
      exact E.bytes i hi)
    (by decide) pc1 ((r1 a0 (by decide)).trans ha0) ((r1 a1 (by decide)).trans ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he)
    (by rw [r1 sp (by decide), A.rsp K]; exact acx_al F (by decide) (by decide))
    (acx_al F (by decide) (by decide)) (acx_al F (by decide) (by decide))
    ⟨by rw [hp']; exact acx_ptr_ne F (by decide), by rw [hp', hl', F.at _ (by decide), hL]; omega⟩
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [e8]; exact acx_hiSep F (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_ss (by decide) (by decide) (by decide))
    (by rw [sp1]; exact acx_ss (by decide) (by decide) (by decide))
    (by rw [hp', hl', hL, sp1]; exact acx_ss (by omega) (by decide) (by omega))
    (by rw [hp', hl', hL, e8]; exact acx_ss (by omega) (by decide) (by omega))
  rw [mem1] at mem2
  rw [sp1] at mem2
  have kk : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    rw [fr2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r1 q (by revert hq; revert q; decide)]
  have fr : ∀ x : Word, (x.toNat < P.B.toNat + 0x3A20 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
      n2.mem x = Cur.u32Mem n.mem (P.B + BitVec.ofNat 32 0x52B0) (P.B + BitVec.ofNat 32 0x5A2C) x :=
    fun x hx => mem2 x (acx_sepR F (by decide) (by omega))
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, A.call kk fun x h1 h2 => ?_, kk, fr⟩
  rw [fr x (by omega), acx_u32Mem_out (acx_sepR F (by decide) (by omega))
    (by rw [e8]; exact acx_sepR F (by decide) (by omega))]

set_option maxHeartbeats 4000000 in
/-- A call of `memset` that zeroes `k` bytes of the frame at `B + d`. -/
theorem acx_cmemset {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o : Nat} {imm o' : Word}
    (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% memsetAddress))
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    {d k : Nat} (hd1 : 0x3C94 ≤ d) (hd2 : d + k ≤ 0x5A38)
    (ha0 : reg n a0 = P.B + BitVec.ofNat 32 d) (ha1 : reg n a1 = 0) (ha2 : reg n a2 = BitVec.ofNat 32 k) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧ n'.mem = fillBytes n.mem (P.B + BitVec.ofNat 32 d) 0 k := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have E := A.env K
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (A.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, mem2, a02, k2⟩ := memset_correct n1 (img% memsetAddress) (AC + BitVec.ofNat 32 (o + 8))
    (P.B + BitVec.ofNat 32 d) 0 k (fun i hi => by rw [mem1]; exact E.mset i hi) (by decide) pc1
    ((r1 a0 (by decide)).trans ha0) ((r1 a1 (by decide)).trans ha1)
    ((r1 a2 (by decide)).trans ha2) (by rw [regs1]; simp +decide [upd]) (even_clear _ he)
    (by rw [F.at _ (by omega)]; omega) (acx_hiSep F (by omega) (by decide) (by decide))
  rw [mem1] at mem2
  have kk : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, A.call kk fun x h1 h2 => ?_, kk, mem2⟩
  rw [mem2]; exact fillBytes_sep (acx_sepR F (by omega) (by omega)) (Nat.le_refl _)

set_option maxHeartbeats 4000000 in
/-- A call of `memcpy` that copies `N` bytes of the frame from `B + c` to
`B + d`. -/
theorem acx_cmemcpy {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o : Nat} {imm o' : Word}
    (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% memcpyStubAddress))
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    {c d N : Nat} (hd1 : 0x3C94 ≤ d) (hd2 : d + N ≤ 0x5A38) (hc1 : 0x3A50 ≤ c) (hc2 : c + N ≤ 0x5A70)
    (hcd : c + N ≤ d ∨ d + N ≤ c)
    (ha0 : reg n a0 = P.B + BitVec.ofNat 32 d) (ha1 : reg n a1 = P.B + BitVec.ofNat 32 c)
    (ha2 : reg n a2 = BitVec.ofNat 32 N) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧
      ∀ x : Word, (x.toNat < P.B.toNat + 0x3A40 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
        n'.mem x = copyBytes n.mem (P.B + BitVec.ofNat 32 d) (P.B + BitVec.ofNat 32 c) N x := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have E := A.env K
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (A.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp + 0xFFFFFFF0 = P.B + BitVec.ofNat 32 0x3A40 := by
    rw [r1 sp (by decide), A.rsp K, BitVec.add_assoc]; rfl
  have ME : McEnv n1.mem ((img% memcpyStubAddress) + 8) (P.B + BitVec.ofNat 32 d) (P.B + BitVec.ofNat 32 c)
      (reg n1 sp + 0xFFFFFFF0) N := by
    rw [sp1, mem1, show ((img% memcpyStubAddress) + 8 : Word) = (img% memcpyBodyAddress) by decide]
    exact ⟨E.mcb, acx_hiSep F (by omega) (by decide) (by decide), acx_hiSep F (by decide) (by decide) (by decide),
      acx_ss (by omega) (by decide) (by omega), acx_ss (by omega) (by decide) (by omega),
      acx_ss (by omega) (by omega) (by omega), acx_al F (by decide) (by decide),
      by rw [F.at _ (by decide)]; omega, by rw [F.at _ (by omega)]; omega, by rw [F.at _ (by omega)]; omega⟩
  obtain ⟨n2, c2, pc2, sp2, a02, mem2, k2⟩ := memcpy_correct n1 (img% memcpyStubAddress)
    (AC + BitVec.ofNat 32 (o + 8)) (P.B + BitVec.ofNat 32 d) (P.B + BitVec.ofNat 32 c) N
    (fun i hi => by rw [mem1]; exact E.mcs i hi) (by decide) pc1
    ((r1 a0 (by decide)).trans ha0) ((r1 a1 (by decide)).trans ha1)
    ((r1 a2 (by decide)).trans ha2) (by rw [regs1]; simp +decide [upd]) (even_clear _ he) ME
  rw [sp1, mem1] at mem2
  have kk : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    by_cases hs : q = sp
    · subst hs; rw [sp2, r1 sp (by decide)]
    · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) hs, r1 q (by revert hq; revert q; decide)]
  have fr : ∀ x : Word, (x.toNat < P.B.toNat + 0x3A40 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
      n2.mem x = copyBytes n.mem (P.B + BitVec.ofNat 32 d) (P.B + BitVec.ofNat 32 c) N x :=
    fun x hx => mem2 x (acx_sepR F (by decide) (by omega))
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, A.call kk fun x h1 h2 => ?_, kk, fr⟩
  rw [fr x (by omega)]; exact copyBytes_sep (acx_sepR F (by omega) (by omega)) (Nat.le_refl _)

set_option maxHeartbeats 4000000 in
/-- A call of `Index::doc` on the index at `B + 0x5920`, into the result at
`B + 0x52B0`. -/
theorem acx_ctid {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o : Nat} {imm o' iw : Word}
    (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% tufIndexDocAddress))
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = P.B + BitVec.ofNat 32 0x52B0) (ha1 : reg n a1 = P.B + BitVec.ofNat 32 0x5920)
    (ha2 : reg n a2 = iw) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧
      (∀ x, Sep (P.B + BitVec.ofNat 32 0x52B0) 12 x 1 → n'.mem x = n.mem x) ∧
      tidOut n'.mem (P.B + BitVec.ofNat 32 0x52B0) (tufIndexDocSpec n.mem (P.B + BitVec.ofNat 32 0x5920) iw.toNat) := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have E := A.env K
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (A.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, k2, mem2, out2⟩ := tufIndexDoc_correct n1 (by rw [mem1]; exact E.tid) (by decide) pc1
    ((r1 a0 (by decide)).trans ha0) ((r1 a1 (by decide)).trans ha1)
    ((r1 a2 (by decide)).trans ha2) (acx_al F (by decide) (by decide)) (acx_al F (by decide) (by decide))
    (acx_hiSep F (by decide) (by decide) (by decide)) (by rw [regs1]; simp +decide [upd]) (even_clear _ he)
  rw [mem1] at mem2 out2
  have kk : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, A.call kk fun x h1 h2 => ?_, kk, mem2, out2⟩
  exact mem2 x (acx_sepR F (by decide) (by omega))

end C3.RV32.Ac
