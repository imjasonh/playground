import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.ParseSpecCur
import C3BootProofs.Proofs.Sha2Finish
import C3BootProofs.Proofs.Sha2OneShot

/-!
# `boot_main`'s first closure: the read stage

From 0x32 to 0x1AA the closure reads the slot's manifest, the image's
header, the image's SHA-256, and the bundle:

* 0x32-0x5C: `memset` the 0x20-byte manifest buffer at `sp + 0x48`, then
  `flash::read` the manifest into it from the slot's base.
* 0x5C-0x7E: `manifest::parse` into `sp + 0x1870`, and test its error byte.
* 0x7E-0xC8: the image's flash address (saved at `sp + 0x44`), then
  `flash::read` of `min(length, 0x114)` header bytes into `Bf + 0xB840`.
* 0xC8-0x100: save the TUF offset, the bundle length, the slot, and the
  result at `sp + 0x30` to `sp + 0x40`, and start a hasher at `sp + 0x68`
  (`memcpy` of the initial hash value).
* 0x100-0x134: the loop that reads the image in 0x2800-byte chunks into
  `doc` (`Bf + 0x4000`) and feeds each to `update`.
* 0x134-0x1AA: `finish` into `sp + 0xD4`, then `flash::read` of the bundle
  into `Bf`, and the TUF part's flash address in `s8`.

Every call runs on the stack below `sp`, inside the closure's 0x3A50 bytes
for its callees, and writes nothing outside that stack, the frame's slots,
and `Buffers`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-- The callees' code and data that the read stage runs: `memset`,
`flash::read` with the ROM's `flash_read_words` stub before it, the manifest
parser and its readers, `memcpy`, SHA-256's `update` and `finish` with their
helpers, the initial hash value, and the round constants. -/
structure AcReadEnv (M : Word → BitVec 8) : Prop where
  ms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  fr : CodeIn M (img% flashReadAddress) flashReadCode
  fw : CodeIn M ((img% flashReadAddress) + 0xFFFFFFE8) romFlashReadWordsCode
  mp : Cur.MPCode M
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cIV : CodeIn M (BitVec.ofNat 32 shaIVAddress) shaIVData
  cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cUBlk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  cX : CodeIn M (BitVec.ofNat 32 shaFinishAddress) shaFinishCode
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cFBlk : CodeIn M (BitVec.ofNat 32 shaFinBlockAddress) shaFinBlockCode

/-! ## Separation in `Nat` -/

theorem acr_sep {a b : Word} {n k : Nat} (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat)
    (ha : a.toNat + n ≤ 2 ^ 32) (hb : b.toNat + k ≤ 2 ^ 32) : Sep a n b k := by
  rcases h with h | h
  · exact sep_of_le h hb
  · exact (sep_of_le h ha).symm

theorem acr_nsep {a b : Word} {n k : Nat} (h : Sep a n b k) (hn : 0 < n) (hk : 0 < k) (ha : a.toNat + n ≤ 2 ^ 32) :
    a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  have hb := b.isLt
  rcases Nat.lt_or_ge b.toNat (a.toNat + n) with h1 | h1
  · rcases Nat.lt_or_ge a.toNat (b.toNat + k) with h2 | h2
    · exfalso
      rcases Nat.lt_or_ge a.toNat b.toNat with h3 | h3
      · refine h (b.toNat - a.toNat) (by omega) 0 hk (BitVec.eq_of_toNat_eq ?_)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      · refine h 0 hn (a.toNat - b.toNat) (by omega) (BitVec.eq_of_toNat_eq ?_)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
    · exact .inr h2
  · exact .inl h1

theorem acr_tn (a : Word) (c : Nat) (h : a.toNat + c < 2 ^ 32) : (a + BitVec.ofNat 32 c).toNat = a.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt h]

theorem acr_slot_add (B : Word) (c d : Nat) : acSlot B c + BitVec.ofNat 32 d = acSlot B (c + d) := by
  unfold acSlot; rw [add_ofNat_assoc, Nat.add_assoc]

theorem acr_not_self (y : BitVec 8) : ~~~y ≠ y := by
  revert y; decide

/-- Data that every memory agreeing with `M0` outside the stack holds lies
outside the stack. -/
theorem acr_sepE {B Bf : Word} {M0 : Word → BitVec 8} {P : (Word → BitVec 8) → Prop}
    (hE : ∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → P M)
    {a : Word} {code : List Nat} (hc : ∀ M, P M → CodeIn M a code) :
    Sep a code.length B 0x5A70 := by
  intro i hi j hj e
  have h1 := hc M0 (hE M0 fun _ _ _ => rfl) i hi
  have h2 := hc (fun x => if x = B + BitVec.ofNat 32 j then ~~~(M0 x) else M0 x) (hE _ fun x hx _ => by
      have hne : x ≠ B + BitVec.ofNat 32 j := fun e' => by
        have := hx 0 (by decide) j hj; rw [add_ofNat_zero] at this; exact this e'
      simp only [hne, if_false]) i hi
  simp only [e, if_true] at h2
  rw [e] at h1
  exact acr_not_self _ (h2.trans h1.symm)

/-! ## The stage's context -/

/-- What holds throughout the stage. -/
structure AcrX (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat) (n0 : Machine)
    (B Bf : Word) (M0 : Word → BitVec 8) : Prop where
  rom : RomRead flash R romBase romCode
  hE : ∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcReadEnv M
  C : CodeIn n0.mem AC bootMainClosure0Code
  CR : CodeIn n0.mem romBase romCode
  hrb : 0x40000000 ≤ romBase.toNat
  hrl : romBase.toNat + romCode.length ≤ 2 ^ 32
  F : Fr B 0x5A70
  dj : B.toNat + 0x5A70 ≤ Bf.toNat ∨ Bf.toNat + acBufLen ≤ B.toNat
  hBa : Bf.toNat % 4 = 0
  hBw : Bf.toNat + acBufLen ≤ 0x40000000
  hR : R ≤ 0x3A50 - 0x150
  hR4 : R % 4 = 0
  out0 : ∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → n0.mem x = M0 x

/-- A state of the stage: memory agrees with the start outside the stack
below the saves and outside `Buffers`, and `sp`, `gp`, and `tp` are kept. -/
structure AcrAt (B Bf g t : Word) (n0 n : Machine) : Prop where
  K : ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x5A3C ≤ x.toNat) →
    (x.toNat < Bf.toNat ∨ Bf.toNat + acBufLen ≤ x.toNat) → n.mem x = n0.mem x
  sp : reg n sp = B + 0x3A50
  gp : reg n (3 : Fin 32) = g
  tp : reg n (4 : Fin 32) = t

section ctx

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

theorem AcrX.good (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n) :
    ∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → n.mem x = M0 x := fun x h1 h2 => by
  have hx := x.isLt
  have e1 := acr_nsep h1 (by decide) (by decide) (by omega)
  have e2 := acr_nsep h2 (by decide) (by decide) (by omega)
  rw [A.K x (by omega) (by omega), X.out0 x h1 h2]

theorem AcrX.env (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n) :
    AcReadEnv n.mem :=
  X.hE _ (X.good A)

theorem AcrX.hi (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    {b : Word} {code : List Nat} (hc : CodeIn n0.mem b code) (hb : 0x40000000 ≤ b.toNat)
    (hl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn n.mem b code := fun i hi => by
  have hF := X.F.hi
  have hBw := X.hBw
  have e : (b + BitVec.ofNat 32 i).toNat = b.toNat + i := acr_tn b i (by omega)
  rw [A.K _ (by omega) (by omega)]
  exact hc i hi

set_option maxRecDepth 100000 in
theorem AcrX.code (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n) :
    CodeIn n.mem AC bootMainClosure0Code :=
  X.hi A X.C (by decide) (by decide)

theorem AcrX.rc (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n) :
    CodeIn n.mem romBase romCode :=
  X.hi A X.CR X.hrb X.hrl

theorem AcrX.inv (X : AcrX flash R romBase romCode n0 B Bf M0) {v : Nat → Word} (I : AcInv B Bf g t v M0 n0)
    {n : Machine} (A : AcrAt B Bf g t n0 n) : AcInv B Bf g t v M0 n where
  sp := A.sp
  gp := A.gp
  tp := A.tp
  saves := fun k hk => by
    have hF := X.F.hi
    have dj := X.dj
    rw [memLoad32_congr fun j hj => A.K _ (by rw [add_ofNat_assoc, X.F.at _ (by omega)]; omega)
      (by rw [add_ofNat_assoc, X.F.at _ (by omega)]; omega)]
    exact I.saves k hk
  out := X.good A

set_option maxRecDepth 100000 in
/-- A word slot of the frame is aligned and lies below the code. -/
theorem AcrX.al (X : AcrX flash R romBase romCode n0 B Bf M0) (c : Nat) (hc : c + 4 ≤ 0x2020) (h4 : c % 4 = 0) :
    (acSlot B c).toNat % 4 = 0 ∧ Sep (acSlot B c) 4 AC bootMainClosure0Code.length := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have := hF.al
  refine ⟨by rw [hF.at _ (by omega)]; omega, hF.sepHi (by omega) (by decide) (by decide)⟩

/-- Two frame slots that don't overlap. -/
theorem AcrX.ss (X : AcrX flash R romBase romCode n0 B Bf M0) {a b la lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la ≤ 0x2020) (hb : b + lb ≤ 0x2020) : Sep (acSlot B a) la (acSlot B b) lb := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have := hF.hi
  exact acr_sep (by rw [hF.at _ (by omega), hF.at _ (by omega)]; omega) (by rw [hF.at _ (by omega)]; omega)
    (by rw [hF.at _ (by omega)]; omega)

theorem AcrX.g32 (X : AcrX flash R romBase romCode n0 B Bf M0) {M : Word → BitVec 8} {c : Nat} (v : Word)
    (hc : c + 4 ≤ 0x2020) {x : Word} (hx : x.toNat < B.toNat + 0x3A50 + c ∨ B.toNat + 0x3A50 + c + 4 ≤ x.toNat) :
    memStore32 M (acSlot B c) v x = M x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have := hF.hi
  have := x.isLt
  exact memStore32_get_sep (acr_sep (by rw [hF.at _ (by omega)]; omega) (by rw [hF.at _ (by omega)]; omega)
    (by omega))

theorem AcrX.g8 (X : AcrX flash R romBase romCode n0 B Bf M0) {M : Word → BitVec 8} {c : Nat} (v : BitVec 8)
    (hc : c + 1 ≤ 0x2020) {x : Word} (hx : x.toNat < B.toNat + 0x3A50 + c ∨ B.toNat + 0x3A50 + c + 1 ≤ x.toNat) :
    memStore8 M (acSlot B c) v x = M x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  refine memStore8_ne fun e => ?_
  rw [e, hF.at _ (by omega)] at hx
  omega

theorem AcrX.l32 (X : AcrX flash R romBase romCode n0 B Bf M0) {M : Word → BitVec 8} {c d : Nat} (v : Word)
    (h : c + 4 ≤ d ∨ d + 4 ≤ c) (hc : c + 4 ≤ 0x2020) (hd : d + 4 ≤ 0x2020) :
    memLoad32 (memStore32 M (acSlot B c) v) (acSlot B d) = memLoad32 M (acSlot B d) :=
  memLoad32_store32_sep (X.ss h hc hd)

theorem AcrX.l8 (X : AcrX flash R romBase romCode n0 B Bf M0) {M : Word → BitVec 8} {c d : Nat} (v : BitVec 8)
    (h : c + 1 ≤ d ∨ d + 4 ≤ c) (hc : c + 1 ≤ 0x2020) (hd : d + 4 ≤ 0x2020) :
    memLoad32 (memStore8 M (acSlot B c) v) (acSlot B d) = memLoad32 M (acSlot B d) :=
  memLoad32_congr fun j hj => memStore8_ne fun e =>
    X.ss h hc hd 0 (by decide) j hj (by rw [add_ofNat_zero, e])

/-- `sp + c` in `Nat`. -/
theorem AcrX.sl (X : AcrX flash R romBase romCode n0 B Bf M0) (c : Nat) (hc : c ≤ 0x2020) :
    (acSlot B c).toNat = B.toNat + 0x3A50 + c := by
  rw [X.F.at _ (by omega)]; omega

/-- `Bf + c` in `Nat`. -/
theorem AcrX.bf (X : AcrX flash R romBase romCode n0 B Bf M0) (c : Nat) (hc : c ≤ acBufLen) :
    (Bf + BitVec.ofNat 32 c).toNat = Bf.toNat + c := by
  have := X.hBw; exact acr_tn Bf c (by omega)

end ctx

/-- From `n`, the stage reaches an exit or a state that `Q` holds of. -/
def AcrGo (B Bf g t r : Word) (n0 n : Machine) (Q : Machine → Prop) : Prop :=
  ∃ n', Steps n n' ∧ AcrAt B Bf g t n0 n' ∧ (AcFail B r n' ∨ Q n')

theorem AcrGo.pre {B Bf g t r : Word} {n0 n n1 : Machine} {Q : Machine → Prop} (h : Steps n n1)
    (k : AcrGo B Bf g t r n0 n1 Q) : AcrGo B Bf g t r n0 n Q := by
  obtain ⟨n', h', A, q⟩ := k
  exact ⟨n', h.trans h', A, q⟩

theorem AcrGo.bind {B Bf g t r : Word} {n0 n : Machine} {Q Q' : Machine → Prop}
    (k : AcrGo B Bf g t r n0 n Q) (k2 : ∀ n', AcrAt B Bf g t n0 n' → Q n' → AcrGo B Bf g t r n0 n' Q') :
    AcrGo B Bf g t r n0 n Q' := by
  obtain ⟨n', h', A, q⟩ := k
  rcases q with f | q
  · exact ⟨n', h', A, .inl f⟩
  · exact AcrGo.pre h' (k2 n' A q)

theorem AcrGo.fail {B Bf g t r : Word} {n0 n n' : Machine} {Q : Machine → Prop} (h : Steps n n')
    (A : AcrAt B Bf g t n0 n') (f : AcFail B r n') : AcrGo B Bf g t r n0 n Q :=
  ⟨n', h, A, .inl f⟩

theorem AcrGo.done {B Bf g t r : Word} {n0 n n' : Machine} {Q : Machine → Prop} (h : Steps n n')
    (A : AcrAt B Bf g t n0 n') (q : Q n') : AcrGo B Bf g t r n0 n Q :=
  ⟨n', h, A, .inr q⟩

theorem AcrAt.next {B Bf g t : Word} {n0 n n' : Machine} (A : AcrAt B Bf g t n0 n)
    (hm : ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x5A3C ≤ x.toNat) →
      (x.toNat < Bf.toNat ∨ Bf.toNat + acBufLen ≤ x.toNat) → n'.mem x = n.mem x)
    (h2 : reg n' (2 : Fin 32) = reg n (2 : Fin 32)) (h3 : reg n' (3 : Fin 32) = reg n (3 : Fin 32))
    (h4 : reg n' (4 : Fin 32) = reg n (4 : Fin 32)) : AcrAt B Bf g t n0 n' where
  K := fun x e1 e2 => (hm x e1 e2).trans (A.K x e1 e2)
  sp := h2.trans A.sp
  gp := h3.trans A.gp
  tp := h4.trans A.tp

theorem AcrAt.keep {B Bf g t : Word} {n0 n n' : Machine} (A : AcrAt B Bf g t n0 n)
    (hm : ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x5A3C ≤ x.toNat) →
      (x.toNat < Bf.toNat ∨ Bf.toNat + acBufLen ≤ x.toNat) → n'.mem x = n.mem x)
    (hk : ∀ q, romKeep q = true → reg n' q = reg n q) : AcrAt B Bf g t n0 n' :=
  A.next hm (hk 2 (by decide)) (hk 3 (by decide)) (hk 4 (by decide))

/-- A state at `o`, from any `St` there. -/
theorem acr_re {M : Word → BitVec 8} {n : Machine} {o : Nat} {f : Fin 32 → Word} (s : St M AC n o f) :
    St n.mem AC n o (reg n) :=
  ⟨s.pc, rfl, fun _ => rfl⟩

/-- A conditional branch at `o`, either way. -/
theorem acr_br {n : Machine} {o : Nat} (s : St n.mem AC n o (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code)
    {op : BranchOp} {rs1 rs2 : Fin 32} {imm len : Word}
    (h : fetchRel bootMainClosure0Code o = some (.branch op rs1 rs2 imm, len)) {oT oF : Nat}
    (hT : BitVec.ofNat 32 o + imm = BitVec.ofNat 32 oT) (hF : BitVec.ofNat 32 o + len = BitVec.ofNat 32 oF) :
    ∃ n', step n = some n' ∧ n'.mem = n.mem ∧ (∀ q, reg n' q = reg n q) ∧
      ((branchTaken op (reg n rs1) (reg n rs2) = true ∧ St n'.mem AC n' oT (reg n')) ∨
       (branchTaken op (reg n rs1) (reg n rs2) = false ∧ St n'.mem AC n' oF (reg n'))) := by
  cases hb : branchTaken op (reg n rs1) (reg n rs2)
  · obtain ⟨n', e, u⟩ := s.notTaken C oF h hF hb
    exact ⟨n', e, u.mem, u.regs, .inr ⟨rfl, acr_re u⟩⟩
  · obtain ⟨n', e, u⟩ := s.taken C oT h hT hb
    exact ⟨n', e, u.mem, u.regs, .inl ⟨rfl, acr_re u⟩⟩

theorem acr_base_lt (slot : Word) : acBase slot < 0x220000 := by
  unfold acBase; split <;> decide

theorem acr_base_tn (slot : Word) : (BitVec.ofNat 32 (acBase slot)).toNat = acBase slot := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := acr_base_lt slot; omega)

theorem acr_ult {a b : Word} (h : a.ult b = true) : a.toNat < b.toNat := by
  unfold BitVec.ult at h; exact of_decide_eq_true h

theorem acr_ult' {a b : Word} (h : a.ult b = false) : b.toNat ≤ a.toNat := by
  unfold BitVec.ult at h; exact Nat.le_of_not_lt (of_decide_eq_false h)

theorem acr_readPart {lo hi : Nat} {bs : Bytes} {p : Part} {r : Bytes} (h : readPart lo hi bs = some (p, r)) :
    lo ≤ p.length ∧ p.length ≤ hi := by
  unfold readPart at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨o, r1⟩, -, ⟨⟨l, r2⟩, -, ⟨u, hu, h⟩⟩⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp only [require_eq_some, Bool.and_eq_true, decide_eq_true_eq] at hu
  exact hu

/-- What a decoded manifest says about its parts. -/
theorem acr_bounds {bs : Bytes} {mf : Manifest} (h : decodeManifest bs = some mf) :
    mf.image.offset = 0x10000 ∧ 37 ≤ mf.image.length ∧ mf.image.length ≤ 0x1D0000 ∧
    mf.bundle.length ≤ 16384 ∧ mf.image.offset + mf.image.length ≤ mf.bundle.offset ∧
    mf.bundle.offset + mf.bundle.length ≤ mf.tuf.offset ∧ mf.tuf.offset + mf.tuf.length ≤ 0x1E0000 := by
  unfold decodeManifest at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨r0, -, ⟨v, r1⟩, -, -, -, r2, -, ⟨im, r3⟩, him, ⟨bu, r4⟩, hbu, ⟨tu, r5⟩, -, -, -, u1, h1, u2, h2, u3, h3,
    h⟩ := h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  simp only [require_eq_some, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h1 h3
  have := acr_readPart him
  have := acr_readPart hbu
  simp only [Part.endOf] at h3
  dsimp only
  refine ⟨h1, by omega, by omega, by omega, h3.1.1, h3.1.2, ?_⟩
  have := h3.2
  simp only [slotSize] at this
  omega

theorem acr_on {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a).toNat = a := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem acr_oadd (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (b + a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem acr_zadd (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

/-- `sp + k` as a frame slot. -/
theorem acr_at (B k : Word) (c : Nat) (h : k.toNat = c) (hc : c < 0x2020) : B + 0x3A50 + k = acSlot B c := by
  subst h
  unfold acSlot
  rw [BitVec.add_assoc]; congr 1

/-- `acSlot B c + d` as a frame slot. -/
theorem acr_sa (B : Word) (c e : Nat) (d : Word) (h : c + d.toNat = e) : acSlot B c + d = acSlot B e := by
  rw [← h, ← acr_slot_add]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt d.isLt]

/-- A hasher with no input: a zero position byte, the initial hash value, and
a zero block count. -/
theorem acr_h0 {M M' : Word → BitVec 8} {S : Word} (cIV : CodeIn M' (BitVec.ofNat 32 shaIVAddress) shaIVData)
    (hpos : M (S + 0x3F) = 0)
    (hiv : ∀ k, k < 32 → M (S + 0x40 + BitVec.ofNat 32 k) = M' (BitVec.ofNat 32 shaIVAddress + BitVec.ofNat 32 k))
    (hlo : memLoad32 M (S + 0x60) = 0) (hhi : memLoad32 M (S + 0x64) = 0) : HasherAt M S [] where
  hlen := by decide
  pos := by rw [hpos]; rfl
  buf := rfl
  hash := by
    show _ = Sha256.h0
    rw [← iv_words cIV]
    exact wordsAt_copy fun k hk => hiv k hk
  lo := by rw [hlo]; rfl
  hi := hhi

theorem acr_sub {L c : Nat} (h : c ≤ L) (hL : L < 2 ^ 32) :
    BitVec.ofNat 32 L - BitVec.ofNat 32 c = BitVec.ofNat 32 (L - c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem acr_fb_add (flash : Nat → BitVec 8) (a c k : Nat) :
    flashBytes flash a (c + k) = flashBytes flash a c ++ flashBytes flash (a + c) k := by
  unfold flashBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.add_assoc]

theorem acr_fb_len (flash : Nat → BitVec 8) (a c : Nat) : (flashBytes flash a c).length = c := by
  unfold flashBytes; rw [List.length_map, List.length_range]

theorem acr_rk {q : Fin 32} (hq : romKeep q = true) (p : Fin 32) (hp : romKeep p = false) : q ≠ p :=
  fun e => by rw [e, hp] at hq; exact Bool.false_ne_true hq

theorem acr_ret {o : Nat} (ho : o % 2 = 0) (ho8 : o + 8 < 0x1B00) :
    AC + BitVec.ofNat 32 (o + 8) &&& ~~~1 = AC + BitVec.ofNat 32 (o + 8) := by
  have hA : AC.toNat % 2 = 0 ∧ AC.toNat < 0x40400000 := by decide
  exact even_clear _ (by rw [acr_tn _ _ (by omega)]; omega)

theorem acr_spn {B : Word} (F : Fr B 0x5A70) : (B + 0x3A50 : Word).toNat = B.toNat + 0x3A50 :=
  F.at 0x3A50 (by decide)

/-- `sp - c`, for the callees' stacks. -/
theorem acr_spm (B : Word) (k : Word) (c : Nat) (h : (0x3A50 : Word) + k = BitVec.ofNat 32 c) :
    B + 0x3A50 + k = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, h]

section calls

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A call of `flash::read`, which runs on the stack below `sp`. -/
theorem acr_fread (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    {o : Nat} {imm o' : Word} (s : St n.mem AC n o (reg n))
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = (img% flashReadAddress)) (ho : o % 2 = 0) (ho8 : o + 8 < 0x1B00)
    {addr out len : Word} (ha0 : reg n a0 = addr) (ha1 : reg n a1 = out) (ha2 : reg n a2 = len)
    (hO : B.toNat + 0x3A50 ≤ out.toNat ∨ out.toNat + len.toNat ≤ B.toNat)
    (hOw : out.toNat + len.toNat ≤ 0x40000000) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      (reg n' a0 = 0 ∨ reg n' a0 = 1) ∧
      (reg n' a0 = 1 → ∀ i, i < len.toNat → n'.mem (out + BitVec.ofNat 32 i) = flash (addr.toNat + i)) ∧
      ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) →
        (x.toNat < out.toNat ∨ out.toNat + len.toNat ≤ x.toNat) → n'.mem x = n.mem x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  have hR := X.hR
  have hR4 := X.hR4
  have hrb := X.hrb
  have hrl := X.hrl
  have EN := X.env A
  have hz := s.zero
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa (X.code A) h1 h2 hb (by decide)
  have r1 : ∀ q, q ≠ ra → reg m1 q = reg n q := fun q hq => by rw [regs1]; exact updz hz hq
  have hG : (B + BitVec.ofNat 32 (0x3A50 - 0x150 - R)).toNat = B.toNat + (0x3A50 - 0x150 - R) :=
    hF.at _ (by omega)
  have hsp : reg m1 sp = B + BitVec.ofNat 32 (0x3A50 - 0x150 - R) + BitVec.ofNat 32 (0x150 + R) := by
    rw [r1 sp (by decide), A.sp, add_ofNat_assoc, show 0x3A50 - 0x150 - R + (0x150 + R) = 0x3A50 by omega]; rfl
  have hm : ((img% flashReadAddress) : Word) + (img% memsetAddress + 0x100000000 - flashReadAddress) =
      BitVec.ofNat 32 memsetAddress := by decide
  obtain ⟨m', c', pc', -, kk', a0', ok', fr'⟩ := flashRead_correct X.rom m1 (P := img% flashReadAddress)
    (G := B + BitVec.ofNat 32 (0x3A50 - 0x150 - R)) (addr := addr) (out := out) (len := len)
    (retAddr := AC + BitVec.ofNat 32 (o + 8))
    { hP := rfl
      code := by rw [mem1]; exact EN.fr
      mset := by rw [mem1, hm]; exact EN.ms
      fw := by rw [mem1]; exact EN.fw
      hG := by rw [hG]; omega
      hR := hR4
      hGt := by rw [hG]; omega
      hlen := by omega
      sGC := data_code (by rw [hG]; omega) (by decide) (by decide)
      sGM := by rw [hm]; exact data_code (by rw [hG]; omega) (by decide) (by decide)
      sGW := data_code (by rw [hG]; omega) (by decide) (by decide)
      sOC := data_code hOw (by decide) (by decide)
      sOW := data_code hOw (by decide) (by decide)
      sOG := acr_sep (by rw [hG]; omega) (by omega) (by rw [hG]; omega)
      rom := by rw [mem1]; exact X.rc A
      sGR := data_code (by rw [hG]; omega) hrb hrl
      sOR := data_code hOw hrb hrl }
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp [upd]) (acr_ret ho ho8) hsp
  refine ⟨m', c1.trans c', ⟨pc', rfl, fun _ => rfl⟩, fun q hq => ?_, a0', ok', fun x e1 e2 => ?_⟩
  · rw [kk' q hq, r1 q (acr_rk hq ra (by decide))]
  · have hx := x.isLt
    rw [fr' x (acr_sep (by rw [hG]; omega) (by rw [hG]; omega) (by omega)) (acr_sep (by omega) (by omega) (by omega)),
      mem1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The call of `memset` at 0x40. -/
theorem acr_memset (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x40 (reg n)) {dst b : Word} {len : Nat} (ha0 : reg n a0 = dst) (ha1 : reg n a1 = b)
    (ha2 : reg n a2 = BitVec.ofNat 32 len) (hw : dst.toNat + len ≤ 0x40000000) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' 0x48 (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      n'.mem = fillBytes n.mem dst (b.extractLsb' 0 8) len := by
  have EN := X.env A
  have hz := s.zero
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BitVec.ofNat 32 memsetAddress) (X.code A) ac_at_40 ac_at_44 (by decide) (by decide)
  have r1 : ∀ q, q ≠ ra → reg m1 q = reg n q := fun q hq => by rw [regs1]; exact updz hz hq
  obtain ⟨m', c', pc', mem', -, kk'⟩ := memset_correct m1 _ (AC + BitVec.ofNat 32 (0x40 + 8)) dst b len
    (by intro i hi; rw [mem1]; exact EN.ms i hi) (by decide) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp [upd]) (acr_ret (o := 0x40) (by decide) (by decide)) (by omega)
    (data_code hw (by decide) (by decide))
  refine ⟨m', c1.trans c', ⟨pc', rfl, fun _ => rfl⟩, fun q hq => ?_, by rw [mem', mem1]⟩
  rw [kk' q (acr_rk hq a2 (by decide)) (acr_rk hq a3 (by decide)) (acr_rk hq a4 (by decide))
    (acr_rk hq a5 (by decide)) (acr_rk hq a6 (by decide)), r1 q (acr_rk hq ra (by decide))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The call of `manifest::parse` at 0x70. -/
theorem acr_parse (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x70 (reg n)) {out bp : Word} (ha0 : reg n a0 = out) (ha1 : reg n a1 = bp)
    (hbp : B.toNat + 0x3A50 ≤ bp.toNat) (hbw : bp.toNat + 32 ≤ 0x40000000)
    (hout : B.toNat + 0x3A50 ≤ out.toNat) (hoa : out.toNat % 4 = 0) (how : out.toNat + 28 ≤ 0x40000000) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' 0x78 (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      (∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) →
        (x.toNat < out.toNat ∨ out.toNat + 28 ≤ x.toNat) → n'.mem x = n.mem x) ∧
      match decodeManifest (manifestBytesV2 n.mem bp) with
      | none => n'.mem out = 1
      | some man =>
        n'.mem out = 0 ∧
        memLoad32 n'.mem (out + 4) = BitVec.ofNat 32 man.image.offset ∧
        memLoad32 n'.mem (out + 8) = BitVec.ofNat 32 man.image.length ∧
        memLoad32 n'.mem (out + 0x0C) = BitVec.ofNat 32 man.bundle.offset ∧
        memLoad32 n'.mem (out + 0x10) = BitVec.ofNat 32 man.bundle.length ∧
        memLoad32 n'.mem (out + 0x14) = BitVec.ofNat 32 man.tuf.offset ∧
        memLoad32 n'.mem (out + 0x18) = BitVec.ofNat 32 man.tuf.length := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  have EN := X.env A
  have hz := s.zero
  have hsn := acr_spn hF
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := Cur.MP) (X.code A) ac_at_70 ac_at_74 (by decide) (by decide)
  have r1 : ∀ q, q ≠ ra → reg m1 q = reg n q := fun q hq => by rw [regs1]; exact updz hz hq
  have e80 := acr_spm B 0xFFFFFF80 0x39D0 (by decide)
  have h80 : (B + BitVec.ofNat 32 0x39D0).toNat = B.toNat + 0x39D0 := hF.at _ (by omega)
  obtain ⟨m', c', pc', -, kk', fr', res⟩ := Cur.manifestParse_decodes m1 (sp0 := B + 0x3A50)
    (retAddr := AC + BitVec.ofNat 32 (0x70 + 8)) (by rw [mem1]; exact EN.mp) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp [upd])
    (acr_ret (o := 0x70) (by decide) (by decide)) (by rw [r1 sp (by decide), A.sp])
    (by rw [hsn]; omega) (by rw [hsn]; omega) (by rw [hsn]; omega)
    (fun e => by
      have h0 : (0 : Word).toNat = 0 := rfl
      rw [e, h0] at hbp; omega) (by omega)
    hoa how (by rw [e80]; exact acr_sep (by rw [h80]; omega) (by omega) (by rw [h80]; omega))
    (by rw [e80]; exact acr_sep (by rw [h80]; omega) (by omega) (by rw [h80]; omega))
  rw [mem1] at res
  refine ⟨m', c1.trans c', ⟨pc', rfl, fun _ => rfl⟩, fun q hq => ?_, fun x e1 e2 => ?_, res⟩
  · rw [kk' q (acr_rk hq a0 (by decide)) (acr_rk hq a1 (by decide)) (acr_rk hq a2 (by decide))
      (acr_rk hq a3 (by decide)) (acr_rk hq a4 (by decide)) (acr_rk hq a5 (by decide)) (acr_rk hq t0 (by decide)),
      r1 q (acr_rk hq ra (by decide))]
  · have hx := x.isLt
    rw [fr' x (by rw [e80]; exact acr_sep (by rw [h80]; omega) (by rw [h80]; omega) (by omega))
      (acr_sep (by omega) (by omega) (by omega)), mem1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The call of `memcpy` at 0xE2: the initial hash value into the hasher. -/
theorem acr_memcpy (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0xE2 (reg n)) (ha0 : reg n a0 = acSlot B 0xA8)
    (ha1 : reg n a1 = BitVec.ofNat 32 shaIVAddress) (ha2 : reg n a2 = BitVec.ofNat 32 32) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' 0xEA (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) →
        n'.mem x = copyBytes n.mem (acSlot B 0xA8) (BitVec.ofNat 32 shaIVAddress) 32 x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  have EN := X.env A
  have hz := s.zero
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) (X.code A) ac_at_e2 ac_at_e6 (by decide) (by decide)
  have r1 : ∀ q, q ≠ ra → reg m1 q = reg n q := fun q hq => by rw [regs1]; exact updz hz hq
  have eF := acr_spm B 0xFFFFFFF0 0x3A40 (by decide)
  have hFn : (B + BitVec.ofNat 32 0x3A40).toNat = B.toNat + 0x3A40 := hF.at _ (by omega)
  have sp1 : reg m1 sp = B + 0x3A50 := by rw [r1 sp (by decide), A.sp]
  have hIV : Sep (BitVec.ofNat 32 shaIVAddress) 32 B 0x5A70 := acr_sepE X.hE (fun _ e => e.cIV)
  have hdn := X.sl 0xA8 (by decide)
  obtain ⟨m', c', pc', sp', -, cp', kk'⟩ := memcpy_correct m1 (BitVec.ofNat 32 memcpyStubAddress)
    (AC + BitVec.ofNat 32 (0xE2 + 8)) (acSlot B 0xA8) (BitVec.ofNat 32 shaIVAddress) 32
    (by intro i hi; rw [mem1]; exact EN.cMS i hi) (by decide) pc1 (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]) (by rw [regs1]; simp [upd])
    (acr_ret (o := 0xE2) (by decide) (by decide))
    (by
      rw [sp1, eF]
      exact
        { code := by rw [mem1]; exact EN.cMB
          hDC := data_code (by rw [hdn]; omega) (by decide) (by decide)
          hFC := data_code (by rw [hFn]; omega) (by decide) (by decide)
          hdF := acr_sep (by rw [hdn, hFn]; omega) (by rw [hdn]; omega) (by rw [hFn]; omega)
          hsF := hIV.subR (c := 0x3A40) (l := 16) (by omega)
          hsep := (hIV.subR (c := 0x3A50 + 0xA8) (l := 32) (by omega)).symm
          hF := by rw [hFn]; omega
          hFw := by rw [hFn]; omega
          hdw := by rw [hdn]; omega
          hsw := by decide })
  refine ⟨m', c1.trans c', ⟨pc', rfl, fun _ => rfl⟩, fun q hq => ?_, fun x e1 => ?_⟩
  · have nk : ∀ p : Fin 32, romKeep p = false → q ≠ p := fun p hp => acr_rk hq p hp
    by_cases hs : q = sp
    · rw [hs, sp', r1 sp (by decide)]
    · rw [kk' q (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)) (nk a4 (by decide)) (nk a5 (by decide))
        (nk a6 (by decide)) (nk a7 (by decide)) (nk t0 (by decide)) (nk t1 (by decide)) (nk 7 (by decide))
        (nk 28 (by decide)) (nk 29 (by decide)) (nk 30 (by decide)) hs, r1 q (nk ra (by decide))]
  · have hx := x.isLt
    rw [cp' x (by rw [sp1, eF]; exact acr_sep (by rw [hFn]; omega) (by rw [hFn]; omega) (by omega)), mem1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The call of `update` at 0x126: `k` bytes at `D` into the hasher at `sp + 0x68`. -/
theorem acr_update (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x126 (reg n)) {D : Word} {k : Nat} {msg : Bytes}
    (ha0 : reg n a0 = acSlot B 0x68) (ha1 : reg n a1 = D) (ha2 : reg n a2 = BitVec.ofNat 32 k)
    (hD : D.toNat + k ≤ B.toNat ∨ B.toNat + 0x5A70 ≤ D.toNat) (hDw : D.toNat + k ≤ 0x40000000)
    (H : HasherAt n.mem (acSlot B 0x68) msg) (hk : k < 2 ^ 31) (hl : msg.length + k < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' 0x12E (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      HasherAt n'.mem (acSlot B 0x68) (msg ++ memBytes n.mem D k) ∧
      ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) →
        (x.toNat < B.toNat + 0x3AB8 ∨ B.toNat + 0x3B20 ≤ x.toNat) → n'.mem x = n.mem x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  have EN := X.env A
  have hz := s.zero
  have hsn := acr_spn hF
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BitVec.ofNat 32 shaUpdateAddress) (X.code A) ac_at_126 ac_at_12a (by decide) (by decide)
  have r1 : ∀ q, q ≠ ra → reg m1 q = reg n q := fun q hq => by rw [regs1]; exact updz hz hq
  have e100 := acr_spm B 0xFFFFFF00 0x3950 (by decide)
  have h100 : (B + BitVec.ofNat 32 0x3950).toNat = B.toNat + 0x3950 := hF.at _ (by omega)
  have hS := X.sl 0x68 (by decide)
  have hK : Sep (BitVec.ofNat 32 shaKAddress) 256 B 0x5A70 := acr_sepE X.hE (fun _ e => e.cK)
  obtain ⟨m', c', pc', sp', kk', H', fr'⟩ := shaUpdate_correct m1 (S := acSlot B 0x68) (D := D)
    (sp0 := B + 0x3A50) (n := k) (msg := msg) (retAddr := AC + BitVec.ofNat 32 (0x126 + 8))
    { cU := by rw [mem1]; exact EN.cU
      cBlk := by rw [mem1]; exact EN.cUBlk
      cC := by rw [mem1]; exact EN.cC
      cI := by rw [mem1]; exact EN.cI
      cK := by rw [mem1]; exact EN.cK
      cMS := by rw [mem1]; exact EN.cMS
      cMB := by rw [mem1]; exact EN.cMB
      hS := by rw [hS]; omega
      hSw := by rw [hS]; omega
      hsp := by rw [hsn]; omega
      hspl := by rw [hsn]; omega
      hspw := by rw [hsn]; omega
      hDw := hDw
      sDS := acr_sep (by rw [hS]; omega) (by omega) (by rw [hS]; omega)
      sDF := by rw [e100]; exact acr_sep (by rw [h100]; omega) (by omega) (by rw [h100]; omega)
      sSF := by rw [e100]; exact acr_sep (by rw [hS, h100]; omega) (by rw [hS]; omega) (by rw [h100]; omega)
      sKS := hK.subR (c := 0x3A50 + 0x68) (l := 0x68) (by omega)
      sKF := by rw [e100]; exact hK.subR (c := 0x3950) (l := 0x100) (by omega) }
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp [upd]) (acr_ret (o := 0x126) (by decide) (by decide)) (by rw [r1 sp (by decide), A.sp])
    (by rw [mem1]; exact H) hk hl
  rw [mem1] at H'
  refine ⟨m', c1.trans c', ⟨pc', rfl, fun _ => rfl⟩, fun q hq => ?_, H', fun x e1 e2 => ?_⟩
  · have nk : ∀ p : Fin 32, romKeep p = false → q ≠ p := fun p hp => acr_rk hq p hp
    by_cases hs : q = sp
    · rw [hs, sp', A.sp]
    · rw [kk' q (nk ra (by decide)) (nk t0 (by decide)) (nk t1 (by decide)) (nk 7 (by decide)) (nk a0 (by decide))
        (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)) (nk a4 (by decide)) (nk a5 (by decide))
        (nk a6 (by decide)) (nk a7 (by decide)) (nk 28 (by decide)) (nk 29 (by decide)) (nk 30 (by decide))
        (nk 31 (by decide)) hs, r1 q (nk ra (by decide))]
  · have hx := x.isLt
    rw [fr' x (by rw [e100]; exact acr_sep (by rw [h100]; omega) (by rw [h100]; omega) (by omega))
      (acr_sep (by rw [hS]; omega) (by rw [hS]; omega) (by omega)), mem1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The call of `finish` at 0x138: the digest into `sp + 0xD4`. -/
theorem acr_finish (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x138 (reg n)) {msg : Bytes} (ha0 : reg n a0 = acSlot B 0xD4)
    (ha1 : reg n a1 = acSlot B 0x68) (H : HasherAt n.mem (acSlot B 0x68) msg) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' 0x140 (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      memBytes n'.mem (acSlot B 0xD4) 32 = sha256 msg ∧
      ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) →
        (x.toNat < B.toNat + 0x3B24 ∨ B.toNat + 0x3B44 ≤ x.toNat) → n'.mem x = n.mem x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  have EN := X.env A
  have hz := s.zero
  have hsn := acr_spn hF
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BitVec.ofNat 32 shaFinishAddress) (X.code A) ac_at_138 ac_at_13c (by decide) (by decide)
  have r1 : ∀ q, q ≠ ra → reg m1 q = reg n q := fun q hq => by rw [regs1]; exact updz hz hq
  have e200 := acr_spm B 0xFFFFFE00 0x3850 (by decide)
  have h200 : (B + BitVec.ofNat 32 0x3850).toNat = B.toNat + 0x3850 := hF.at _ (by omega)
  have hS := X.sl 0x68 (by decide)
  have hO := X.sl 0xD4 (by decide)
  have hK : Sep (BitVec.ofNat 32 shaKAddress) 256 B 0x5A70 := acr_sepE X.hE (fun _ e => e.cK)
  obtain ⟨m', c', pc', -, kk', hd, fr'⟩ := shaFinish_correct m1 (S := acSlot B 0x68) (out := acSlot B 0xD4)
    (sp0 := B + 0x3A50) (msg := msg) (retAddr := AC + BitVec.ofNat 32 (0x138 + 8))
    { cX := by rw [mem1]; exact EN.cX
      cF := by rw [mem1]; exact EN.cF
      cZ := by rw [mem1]; exact EN.cZ
      cBlk := by rw [mem1]; exact EN.cFBlk
      cMs := by rw [mem1]; exact EN.ms
      cMS := by rw [mem1]; exact EN.cMS
      cMB := by rw [mem1]; exact EN.cMB
      cC := by rw [mem1]; exact EN.cC
      cI := by rw [mem1]; exact EN.cI
      cK := by rw [mem1]; exact EN.cK
      hSw := by rw [hS]; omega
      hsp := by rw [hsn]; omega
      hspl := by rw [hsn]; omega
      hspw := by rw [hsn]; omega
      hOw := by rw [hO]; omega
      sSF := by rw [e200]; exact acr_sep (by rw [hS, h200]; omega) (by rw [hS]; omega) (by rw [h200]; omega)
      sOF := by rw [e200]; exact acr_sep (by rw [hO, h200]; omega) (by rw [hO]; omega) (by rw [h200]; omega)
      sKF := by rw [e200]; exact hK.subR (c := 0x3850) (l := 0x200) (by omega) }
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp [upd])
    (acr_ret (o := 0x138) (by decide) (by decide)) (by rw [r1 sp (by decide), A.sp]) (by rw [mem1]; exact H)
  refine ⟨m', c1.trans c', ⟨pc', rfl, fun _ => rfl⟩, fun q hq => ?_, hd, fun x e1 e2 => ?_⟩
  · have nk : ∀ p : Fin 32, romKeep p = false → q ≠ p := fun p hp => acr_rk hq p hp
    rw [kk' q (nk t0 (by decide)) (nk t1 (by decide)) (nk 7 (by decide)) (nk a0 (by decide))
        (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)) (nk a4 (by decide)) (nk a5 (by decide))
        (nk a6 (by decide)) (nk a7 (by decide)) (nk 28 (by decide)) (nk 29 (by decide)) (nk 30 (by decide))
        (nk 31 (by decide)), r1 q (nk ra (by decide))]
  · have hx := x.isLt
    rw [fr' x (by rw [e200]; exact acr_sep (by rw [h200]; omega) (by rw [h200]; omega) (by omega))
      (acr_sep (by rw [hO]; omega) (by rw [hO]; omega) (by omega)), mem1]

end calls

/-! ## 0x32-0x5C: the manifest's bytes -/

def acrA1 : List BInstr := [.aluImm .add a0 sp 0x48, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]

set_option maxRecDepth 100000 in
theorem acrA1_end : blockEnd bootMainClosure0Code 0x38 acrA1 = some 0x40 := by decide

def acrA2 : List BInstr := [.aluImm .add a1 sp 0x48, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (24 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrA2_end : blockEnd bootMainClosure0Code 0x48 acrA2 = some 0x50 := by decide

section segs

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- From 0x32 to 0x5C: the slot's base in `s8`, and the slot's first 32
bytes at `sp + 0x48`. -/
theorem acr_segA (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x32 (reg n)) {r slot : Word} (h19 : reg n (19 : Fin 32) = r)
    (ha3 : reg n a3 = slot) (h24 : reg n (24 : Fin 32) = 0x210000) :
    AcrGo B Bf g t r n0 n fun n' => St n'.mem AC n' 0x5C (reg n') ∧
      (∀ q, romKeep q = true → q ≠ (24 : Fin 32) → reg n' q = reg n q) ∧
      reg n' (24 : Fin 32) = BitVec.ofNat 32 (acBase slot) ∧
      ∀ i, i < 32 → n'.mem (acSlot B 0x48 + BitVec.ofNat 32 i) = flash (acBase slot + i) := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hz := s.zero
  have C := X.code A
  have hsl := X.sl 0x48 (by decide)
  obtain ⟨n1, c1, s1, k1, b1, m1⟩ : ∃ n1, Steps n n1 ∧ St n1.mem AC n1 0x38 (reg n1) ∧
      (∀ q : Fin 32, q ≠ (24 : Fin 32) → reg n1 q = reg n q) ∧
      reg n1 (24 : Fin 32) = BitVec.ofNat 32 (acBase slot) ∧ n1.mem = n.mem := by
    by_cases hs : slot = 0
    · obtain ⟨m1, e1, u1⟩ := s.notTaken C 0x34 ac_at_32 (by decide)
        (by show (reg n a3 != reg n 0) = false; rw [ha3, hs, hz]; rfl)
      obtain ⟨m2, e2, u2⟩ := u1.lui C ac_at_34 (off' := 0x38) (by decide)
      refine ⟨m2, .cons e1 (.single e2), acr_re u2, fun q hq => ?_, ?_, u2.mem⟩
      · rw [u2.regs]; exact updz hz hq
      · rw [u2.regs, show acBase slot = 0x30000 from if_pos hs]; rfl
    · obtain ⟨m1, e1, u1⟩ := s.taken C 0x38 ac_at_32 (by decide)
        (by show (reg n a3 != reg n 0) = true; rw [ha3, hz]; exact bne_iff_ne.mpr hs)
      refine ⟨m1, .single e1, acr_re u1, fun q _ => u1.regs q, ?_, u1.mem⟩
      rw [u1.regs, h24, show acBase slot = 0x210000 from if_neg hs]; rfl
  have z1 := s1.zero
  have A1 : AcrAt B Bf g t n0 n1 := A.next (fun x _ _ => by rw [m1]) (k1 sp (by decide)) (k1 3 (by decide))
    (k1 4 (by decide))
  -- `memset` the buffer
  obtain ⟨n2, c2, u2⟩ := s1.block (off' := 0x40) acrA1 (X.code A1) acrA1_end ⟨trivial, trivial, trivial, trivial⟩
  have M2 : n2.mem = n1.mem := u2.mem
  have k2 : ∀ q : Fin 32, romKeep q = true → reg n2 q = reg n1 q := fun q hq => by
    rw [u2.regs, runBlock_reg _ _ _ q z1 (by simp only [acrA1]; revert hq; revert q; decide)]
  have e48 : (B + 0x3A50 + 0x48 : Word) = acSlot B 0x48 := acr_spm B 0x48 _ (by decide)
  have a0_2 : reg n2 a0 = acSlot B 0x48 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, acrA1, upd, ↓reduceIte, aluEval]
    rw [A1.sp, e48]
  have a1_2 : reg n2 a1 = 0 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, acrA1, upd, ↓reduceIte, aluEval]
  have a2_2 : reg n2 a2 = BitVec.ofNat 32 32 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, acrA1, upd, ↓reduceIte, aluEval]
  have A2 := A1.keep (fun x _ _ => by rw [M2]) k2
  obtain ⟨n3, c3, s3, k3, M3⟩ := acr_memset X A2 (acr_re u2) a0_2 a1_2 a2_2 (by rw [hsl]; omega)
  have A3 := A2.keep (fun x e _ => by
    rw [M3, fillBytes_sep (acr_sep (by rw [hsl]; omega) (by rw [hsl]; omega) (by have := x.isLt; omega))
      (Nat.le_refl 32)]) k3
  -- `flash::read` the manifest
  have z3 := s3.zero
  obtain ⟨n4, c4, u4⟩ := s3.block (off' := 0x50) acrA2 (X.code A3) acrA2_end ⟨trivial, trivial, trivial, trivial⟩
  have M4 : n4.mem = n3.mem := u4.mem
  have k4 : ∀ q : Fin 32, romKeep q = true → reg n4 q = reg n3 q := fun q hq => by
    rw [u4.regs, runBlock_reg _ _ _ q z3 (by simp only [acrA2]; revert hq; revert q; decide)]
  have a1_4 : reg n4 a1 = acSlot B 0x48 := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, acrA2, upd, ↓reduceIte, aluEval]
    rw [A3.sp, e48]
  have a2_4 : reg n4 a2 = BitVec.ofNat 32 32 := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, acrA2, upd, ↓reduceIte, aluEval]
  have b3 : reg n3 (24 : Fin 32) = BitVec.ofNat 32 (acBase slot) := by
    rw [k3 24 (by decide), k2 24 (by decide), b1]
  have a0_4 : reg n4 a0 = BitVec.ofNat 32 (acBase slot) := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, acrA2, upd, ↓reduceIte, aluEval]
    rw [b3, acr_zadd]
  have A4 := A3.keep (fun x _ _ => by rw [M4]) k4
  obtain ⟨n5, c5, s5, k5, a05, ok5, fr5⟩ := acr_fread X A4 (o := 0x50) (acr_re u4) ac_at_50 ac_at_54
    (by decide) (by decide) (by decide) a0_4 a1_4 a2_4 (.inl (by rw [hsl]; omega))
    (by rw [hsl, BitVec.toNat_ofNat]; omega)
  have A5 := A4.keep (fun x e _ => fr5 x (by omega) (by rw [hsl, BitVec.toNat_ofNat]; omega)) k5
  have K5 : ∀ q : Fin 32, romKeep q = true → q ≠ (24 : Fin 32) → reg n5 q = reg n q := fun q hq h =>
    by rw [k5 q hq, k4 q hq, k3 q hq, k2 q hq, k1 q h]
  obtain ⟨n6, e6, M6, r6, ⟨hb, s6⟩ | ⟨hb, s6⟩⟩ := acr_br s5 (X.code A5) ac_at_58 (oT := 0x16A) (oF := 0x5C)
    (by decide) (by decide)
  · refine AcrGo.fail (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.single e6)))))) (A5.keep
      (fun x _ _ => by rw [M6]) fun q _ => r6 q) (.inr (.inl ⟨s6.pc, ?_⟩))
    rw [r6, K5 19 (by decide) (by decide), h19]
  · have h1 : reg n5 a0 = 1 := by
      rcases a05 with h | h
      · rw [h, s5.zero] at hb; exact absurd hb (by decide)
      · exact h
    refine AcrGo.done (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.single e6)))))) (A5.keep
      (fun x _ _ => by rw [M6]) fun q _ => r6 q) ⟨s6, fun q hq h => by rw [r6, K5 q hq h], ?_, fun i hi => ?_⟩
    · rw [r6, k5 24 (by decide), k4 24 (by decide), b3]
    · rw [M6, ok5 h1 i (by rw [BitVec.toNat_ofNat]; omega), acr_base_tn]

end segs

/-! ## 0x5C-0x7E: `manifest::parse` -/

def acrB1 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add (9 : Fin 32) sp a0,
  .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF870, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x48]

set_option maxRecDepth 100000 in
theorem acrB1_end : blockEnd bootMainClosure0Code 0x5C acrB1 = some 0x70 := by decide

def acrB2 : List BInstr := [.lbu a0 (9 : Fin 32) 0x560]

set_option maxRecDepth 100000 in
theorem acrB2_end : blockEnd bootMainClosure0Code 0x78 acrB2 = some 0x7C := by decide

/-- The manifest's six fields, as `parse` leaves them at `sp + 0x1874`. -/
abbrev AcrFields (M : Word → BitVec 8) (B : Word) (mf : Manifest) : Prop :=
  memLoad32 M (acSlot B 0x1874) = BitVec.ofNat 32 mf.image.offset ∧
  memLoad32 M (acSlot B 0x1878) = BitVec.ofNat 32 mf.image.length ∧
  memLoad32 M (acSlot B 0x187C) = BitVec.ofNat 32 mf.bundle.offset ∧
  memLoad32 M (acSlot B 0x1880) = BitVec.ofNat 32 mf.bundle.length ∧
  memLoad32 M (acSlot B 0x1884) = BitVec.ofNat 32 mf.tuf.offset ∧
  memLoad32 M (acSlot B 0x1888) = BitVec.ofNat 32 mf.tuf.length

section segs

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- From 0x5C to 0x7E: the manifest decodes, and its fields are at
`sp + 0x1874`. -/
theorem acr_segB (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x5C (reg n)) {r slot : Word} (h19 : reg n (19 : Fin 32) = r)
    (hdr : ∀ i, i < 32 → n.mem (acSlot B 0x48 + BitVec.ofNat 32 i) = flash (acBase slot + i)) :
    AcrGo B Bf g t r n0 n fun n' => ∃ mf, decodeManifest (flashBytes flash (acBase slot) 32) = some mf ∧
      St n'.mem AC n' 0x7E (reg n') ∧ (∀ q, romKeep q = true → q ≠ (9 : Fin 32) → reg n' q = reg n q) ∧
      reg n' (9 : Fin 32) = acSlot B 0x1310 ∧ AcrFields n'.mem B mf := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  have z0 := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x70) acrB1 (X.code A) acrB1_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have M1 : n1.mem = n.mem := u1.mem
  have k1 : ∀ q : Fin 32, q ≠ (9 : Fin 32) → romKeep q = true → reg n1 q = reg n q := fun q h9 hq => by
    rw [u1.regs, runBlock_reg _ _ _ q z0 (by simp only [acrB1]; revert h9; revert hq; revert q; decide)]
  have s1v : reg n1 (9 : Fin 32) = acSlot B 0x1310 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acrB1, upd, ↓reduceIte, aluEval]
    rw [A.sp]; exact acr_spm B _ _ (by decide)
  have a0v : reg n1 a0 = acSlot B 0x1870 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acrB1, upd, ↓reduceIte, aluEval]
    rw [A.sp, BitVec.add_comm]; exact acr_spm B _ _ (by decide)
  have a1v : reg n1 a1 = acSlot B 0x48 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acrB1, upd, ↓reduceIte, aluEval]
    rw [A.sp]; exact acr_spm B _ _ (by decide)
  have A1 := A.next (fun x _ _ => by rw [M1]) (k1 2 (by decide) (by decide)) (k1 3 (by decide) (by decide)) (k1 4 (by decide) (by decide))
  have hO := X.sl 0x1870 (by decide)
  have hP := X.sl 0x48 (by decide)
  obtain ⟨n2, c2, s2, k2, fr2, res⟩ := acr_parse X A1 (acr_re u1) a0v a1v (by rw [hP]; omega) (by rw [hP]; omega)
    (by rw [hO]; omega) (by rw [hO]; omega) (by rw [hO]; omega)
  have hbytes : manifestBytesV2 n1.mem (acSlot B 0x48) = flashBytes flash (acBase slot) 32 := by
    unfold manifestBytesV2 flashBytes
    refine List.map_congr_left fun i hi => ?_
    show (n1.mem (acSlot B 0x48 + BitVec.ofNat 32 i)).toNat = _
    rw [M1, hdr i (List.mem_range.mp hi)]
  rw [hbytes] at res
  have A2 := A1.keep (fun x e1 e2 => fr2 x (by omega) (by rw [hO]; omega)) k2
  have z2 := s2.zero
  obtain ⟨n3, c3, u3⟩ := s2.block (off' := 0x7C) acrB2 (X.code A2) acrB2_end ⟨trivial, trivial⟩
  have M3 : n3.mem = n2.mem := u3.mem
  have k3 : ∀ q : Fin 32, romKeep q = true → reg n3 q = reg n2 q := fun q hq => by
    rw [u3.regs, runBlock_reg _ _ _ q z2 (by simp only [acrB2]; revert hq; revert q; decide)]
  have s2v : reg n2 (9 : Fin 32) = acSlot B 0x1310 := by rw [k2 9 (by decide), s1v]
  have a0_3 : reg n3 a0 = (n2.mem (acSlot B 0x1870)).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acrB2, upd, ↓reduceIte, aluEval]
    rw [s2v, show (0x560 : Word) = BitVec.ofNat 32 0x560 from rfl, acr_slot_add]
  have A3 := A2.keep (fun x _ _ => by rw [M3]) k3
  have K3 : ∀ q : Fin 32, romKeep q = true → q ≠ (9 : Fin 32) → reg n3 q = reg n q := fun q hq h9 => by
    rw [k3 q hq, k2 q hq, k1 q h9 hq]
  obtain ⟨n4, e4, M4, r4, ⟨hb, s4⟩ | ⟨hb, s4⟩⟩ := acr_br (acr_re u3) (X.code A3) ac_at_7c (oT := 0x16A)
    (oF := 0x7E) (by decide) (by decide)
  · refine AcrGo.fail (c1.trans (c2.trans (c3.trans (.single e4)))) (A3.keep (fun x _ _ => by rw [M4])
      fun q _ => r4 q) (.inr (.inl ⟨s4.pc, ?_⟩))
    rw [r4, K3 19 (by decide) (by decide), h19]
  · have hz3 := (acr_re u3).zero
    rw [a0_3, hz3] at hb
    cases hd : decodeManifest (flashBytes flash (acBase slot) 32) with
    | none =>
      rw [hd] at res
      dsimp only at res
      rw [res] at hb
      exact absurd hb (by decide)
    | some mf =>
      rw [hd] at res
      dsimp only at res
      obtain ⟨-, l4, l8, lC, l10, l14, l18⟩ := res
      have e : ∀ c : Nat, acSlot B 0x1870 + BitVec.ofNat 32 c = acSlot B (0x1870 + c) := acr_slot_add B 0x1870
      refine AcrGo.done (c1.trans (c2.trans (c3.trans (.single e4)))) (A3.keep (fun x _ _ => by rw [M4])
        fun q _ => r4 q) ⟨mf, rfl, s4, fun q hq h9 => by rw [r4, K3 q hq h9], by rw [r4, k3 9 (by decide), s2v],
        ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [M4, M3]
      · rw [← l4, show (4 : Word) = BitVec.ofNat 32 4 from rfl, e 4]
      · rw [← l8, show (8 : Word) = BitVec.ofNat 32 8 from rfl, e 8]
      · rw [← lC, show (0x0C : Word) = BitVec.ofNat 32 12 from rfl, e 12]
      · rw [← l10, show (0x10 : Word) = BitVec.ofNat 32 16 from rfl, e 16]
      · rw [← l14, show (0x14 : Word) = BitVec.ofNat 32 20 from rfl, e 20]
      · rw [← l18, show (0x18 : Word) = BitVec.ofNat 32 24 from rfl, e 24]

end segs

/-! ## 0x7E-0xC8: the image's header -/

def acrC1 : List BInstr := [.lw a0 (9 : Fin 32) 0x564, .alu .add a1 a0 (24 : Fin 32), .sw sp a1 0x44]

set_option maxRecDepth 100000 in
theorem acrC1_end : blockEnd bootMainClosure0Code 0x7E acrC1 = some 0x88 := by decide

def acrC2 : List BInstr :=
  [.lw (27 : Fin 32) (9 : Fin 32) 0x568, .aluImm .add a0 x0 0x114, .alu .add (22 : Fin 32) x0 (27 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrC2_end : blockEnd bootMainClosure0Code 0x8C acrC2 = some 0x96 := by decide

def acrC3 : List BInstr := [.aluImm .add (22 : Fin 32) x0 0x114]

set_option maxRecDepth 100000 in
theorem acrC3_end : blockEnd bootMainClosure0Code 0x9A acrC3 = some 0x9E := by decide

def acrC4 : List BInstr :=
  [.lw (18 : Fin 32) (9 : Fin 32) 0x56C, .lw (20 : Fin 32) (9 : Fin 32) 0x570, .lw (23 : Fin 32) (9 : Fin 32) 0x574,
    .lw (9 : Fin 32) (9 : Fin 32) 0x578, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF840,
    .alu .add (25 : Fin 32) (21 : Fin 32) a0, .lw a0 sp 0x44, .alu .add a1 x0 (25 : Fin 32),
    .alu .add a2 x0 (22 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrC4_end : blockEnd bootMainClosure0Code 0x9E acrC4 = some 0xBE := by decide

/-- The registers that the stage writes from 0x7E on and keeps. -/
def acrOut (q : Fin 32) : Bool :=
  q = 9 || q = 18 || q = 20 || q = 22 || q = 23 || q = 25 || q = 27

section segs

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From 0x7E to 0xC8: the image's flash address at `sp + 0x44`, the parts'
offsets and lengths in registers, and the header in `Bf + 0xB840`. -/
theorem acr_segC (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x7E (reg n)) {r slot : Word} {mf : Manifest}
    (hd : decodeManifest (flashBytes flash (acBase slot) 32) = some mf)
    (h19 : reg n (19 : Fin 32) = r) (h9 : reg n (9 : Fin 32) = acSlot B 0x1310) (h21 : reg n (21 : Fin 32) = Bf)
    (h24 : reg n (24 : Fin 32) = BitVec.ofNat 32 (acBase slot)) (FL : AcrFields n.mem B mf) :
    AcrGo B Bf g t r n0 n fun n' => St n'.mem AC n' 0xC8 (reg n') ∧
      (∀ q, romKeep q = true → acrOut q = false → reg n' q = reg n q) ∧
      reg n' (9 : Fin 32) = BitVec.ofNat 32 mf.tuf.length ∧
      reg n' (18 : Fin 32) = BitVec.ofNat 32 mf.bundle.offset ∧
      reg n' (20 : Fin 32) = BitVec.ofNat 32 mf.bundle.length ∧
      reg n' (22 : Fin 32) = BitVec.ofNat 32 (min mf.image.length 0x114) ∧
      reg n' (23 : Fin 32) = BitVec.ofNat 32 mf.tuf.offset ∧
      reg n' (25 : Fin 32) = Bf + 0xB840 ∧
      reg n' (27 : Fin 32) = BitVec.ofNat 32 mf.image.length ∧
      memLoad32 n'.mem (acSlot B 0x44) = BitVec.ofNat 32 (acBase slot + mf.image.offset) ∧
      ∀ i, i < min mf.image.length 0x114 →
        n'.mem (Bf + 0xB840 + BitVec.ofNat 32 i) = flash (acBase slot + mf.image.offset + i) := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  have dj := X.dj
  have hBw := X.hBw
  have hbl := acr_base_lt slot
  obtain ⟨io, il1, il2, bl, ib, bt, tt⟩ := acr_bounds hd
  obtain ⟨f4, f8, fC, f10, f14, f18⟩ := FL
  have z0 := s.zero
  have e44 := acr_at B 0x44 0x44 rfl (by decide)
  have al44 := X.al 0x44 (by decide) (by decide)
  -- the image's address at `sp + 0x44`
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x88) acrC1 (X.code A) acrC1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrC1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [h9, A.sp, acr_sa B 0x1310 0x1874 0x564 rfl, e44]
    exact ⟨(X.al 0x1874 (by decide) (by decide)).1, al44⟩)
  have k1 : ∀ q : Fin 32, romKeep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q z0 (by simp only [acrC1]; revert hq; revert q; decide)]
  have M1 : n1.mem = memStore32 n.mem (acSlot B 0x44) (BitVec.ofNat 32 (acBase slot + mf.image.offset)) := by
    rw [u1.mem]; simp +decide only [runBlock, BInstr.run, acrC1, upd, ↓reduceIte, aluEval]
    rw [h9, A.sp, acr_sa B 0x1310 0x1874 0x564 rfl, e44, f4, h24, acr_oadd]
  have st : ∀ c, 0x1874 ≤ c → c + 4 ≤ 0x2020 → memLoad32 n1.mem (acSlot B c) = memLoad32 n.mem (acSlot B c) :=
    fun c h1 h2 => by rw [M1, memLoad32_store32_sep (X.ss (.inl (by omega)) (by decide) h2)]
  have A1 := A.keep (fun x e _ => by
    rw [M1, memStore32_get_sep (acr_sep (by rw [X.sl 0x44 (by decide)]; omega) (by rw [X.sl 0x44 (by decide)]; omega)
      (by have := x.isLt; omega))]) k1
  obtain ⟨n2, e2, M2, r2, ⟨hb2, s2⟩ | ⟨hb2, s2⟩⟩ := acr_br (acr_re u1) (X.code A1) ac_at_88 (oT := 0x16A)
    (oF := 0x8C) (by decide) (by decide)
  · exact AcrGo.fail (c1.trans (.single e2)) (A1.keep (fun x _ _ => by rw [M2]) fun q _ => r2 q)
      (.inr (.inl ⟨s2.pc, by rw [r2, k1 19 (by decide), h19]⟩))
  have A2 := A1.keep (fun x _ _ => by rw [M2]) fun q _ => r2 q
  -- the header's length
  have z2 := s2.zero
  have h9' : reg n2 (9 : Fin 32) = acSlot B 0x1310 := by rw [r2, k1 9 (by decide), h9]
  obtain ⟨n3, c3, u3⟩ := s2.block (off' := 0x96) acrC2 (X.code A2) acrC2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrC2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [h9', acr_sa B 0x1310 0x1878 0x568 rfl]
    exact (X.al 0x1878 (by decide) (by decide)).1)
  have M3 : n3.mem = n2.mem := u3.mem
  have k3 : ∀ q : Fin 32, romKeep q = true → q ≠ (22 : Fin 32) → q ≠ (27 : Fin 32) → reg n3 q = reg n2 q :=
    fun q hq h1 h2 => by
      rw [u3.regs, runBlock_reg _ _ _ q z2 (by simp only [acrC2]; revert h2; revert h1; revert hq; revert q; decide)]
  have v27 : reg n3 (27 : Fin 32) = BitVec.ofNat 32 mf.image.length := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acrC2, upd, ↓reduceIte, aluEval]
    rw [h9', acr_sa B 0x1310 0x1878 0x568 rfl, M2, st 0x1878 (by decide) (by decide), f8]
  have v10 : reg n3 a0 = 0x114 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acrC2, upd, ↓reduceIte, aluEval]
  have v22 : reg n3 (22 : Fin 32) = BitVec.ofNat 32 mf.image.length := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acrC2, upd, ↓reduceIte, aluEval]
    rw [h9', acr_sa B 0x1310 0x1878 0x568 rfl, M2, st 0x1878 (by decide) (by decide), f8, acr_zadd]
  have A3 := A2.next (fun x _ _ => by rw [M3])
    (k3 2 (by decide) (by decide) (by decide)) (k3 3 (by decide) (by decide) (by decide)) (k3 4 (by decide) (by decide) (by decide))
  have hil : (BitVec.ofNat 32 mf.image.length).toNat = mf.image.length := acr_on (by omega)
  obtain ⟨n5, c5, s5, M5, k5, v22'⟩ : ∃ n5, Steps n3 n5 ∧ St n5.mem AC n5 0x9E (reg n5) ∧ n5.mem = n3.mem ∧
      (∀ q : Fin 32, q ≠ (22 : Fin 32) → reg n5 q = reg n3 q) ∧
      reg n5 (22 : Fin 32) = BitVec.ofNat 32 (min mf.image.length 0x114) := by
    obtain ⟨n4, e4, M4, r4, ⟨hb4, s4⟩ | ⟨hb4, s4⟩⟩ := acr_br (acr_re u3) (X.code A3) ac_at_96 (oT := 0x9E)
      (oF := 0x9A) (by decide) (by decide)
    · have := acr_ult hb4
      rw [v27, v10, hil] at this
      refine ⟨n4, .single e4, s4, M4, fun q _ => r4 q, ?_⟩
      rw [r4, v22, Nat.min_eq_left (by have : (0x114 : Word).toNat = 0x114 := rfl; omega)]
    · have := acr_ult' hb4
      rw [v27, v10, hil] at this
      have z4 := s4.zero
      obtain ⟨n5, c5, u5⟩ := s4.block (off' := 0x9E) acrC3 (X.code (A3.keep (fun x _ _ => by rw [M4])
        fun q _ => r4 q)) acrC3_end ⟨trivial, trivial⟩
      refine ⟨n5, .cons e4 c5, acr_re u5, by rw [u5.mem, M4]; rfl, fun q hq => ?_, ?_⟩
      · rw [u5.regs, runBlock_reg _ _ _ q z4 (by simp only [acrC3]; revert hq; revert q; decide), r4]
      · rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acrC3, upd, ↓reduceIte, aluEval]
        rw [Nat.min_eq_right (by have : (0x114 : Word).toNat = 0x114 := rfl; omega)]; rfl
  have A5 := A3.next (fun x _ _ => by rw [M5]) (k5 2 (by decide)) (k5 3 (by decide)) (k5 4 (by decide))
  -- the parts' offsets and lengths, and the header's read
  have z5 := s5.zero
  have h9'' : reg n5 (9 : Fin 32) = acSlot B 0x1310 := by
    rw [k5 9 (by decide), k3 9 (by decide) (by decide) (by decide), h9']
  have sp5 : reg n5 sp = B + 0x3A50 := A5.sp
  obtain ⟨n6, c6, u6⟩ := s5.block (off' := 0xBE) acrC4 (X.code A5) acrC4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrC4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [h9'', sp5, acr_sa B 0x1310 0x187C 0x56C rfl, acr_sa B 0x1310 0x1880 0x570 rfl,
      acr_sa B 0x1310 0x1884 0x574 rfl, acr_sa B 0x1310 0x1888 0x578 rfl, e44]
    exact ⟨(X.al 0x187C (by decide) (by decide)).1, (X.al 0x1880 (by decide) (by decide)).1,
      (X.al 0x1884 (by decide) (by decide)).1, (X.al 0x1888 (by decide) (by decide)).1, al44.1⟩)
  have M6 : n6.mem = n5.mem := u6.mem
  have mem5 : ∀ c, 0x1874 ≤ c → c + 4 ≤ 0x2020 → memLoad32 n5.mem (acSlot B c) = memLoad32 n.mem (acSlot B c) :=
    fun c h1 h2 => by rw [M5, M3, M2, st c h1 h2]
  have k6 : ∀ q : Fin 32, romKeep q = true → acrOut q = false → reg n6 q = reg n5 q := fun q hq ho => by
    rw [u6.regs, runBlock_reg _ _ _ q z5 (by simp only [acrC4]; revert ho; revert hq; revert q; decide)]
  have K6 : ∀ q : Fin 32, romKeep q = true → acrOut q = false → reg n6 q = reg n q := fun q hq ho => by
    have h22 : q ≠ 22 := fun e => by rw [e] at ho; exact absurd ho (by decide)
    have h27 : q ≠ 27 := fun e => by rw [e] at ho; exact absurd ho (by decide)
    rw [k6 q hq ho, k5 q h22, k3 q hq h22 h27, r2, k1 q hq]
  have v6 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 mf.tuf.length ∧
      reg n6 (18 : Fin 32) = BitVec.ofNat 32 mf.bundle.offset ∧
      reg n6 (20 : Fin 32) = BitVec.ofNat 32 mf.bundle.length ∧
      reg n6 (22 : Fin 32) = BitVec.ofNat 32 (min mf.image.length 0x114) ∧
      reg n6 (23 : Fin 32) = BitVec.ofNat 32 mf.tuf.offset ∧
      reg n6 (25 : Fin 32) = Bf + 0xB840 ∧
      reg n6 (27 : Fin 32) = BitVec.ofNat 32 mf.image.length ∧
      reg n6 a0 = BitVec.ofNat 32 (acBase slot + mf.image.offset) ∧
      reg n6 a1 = Bf + 0xB840 ∧
      reg n6 a2 = BitVec.ofNat 32 (min mf.image.length 0x114) := by
    have h21' : reg n5 (21 : Fin 32) = Bf := by
      rw [k5 21 (by decide), k3 21 (by decide) (by decide) (by decide), r2, k1 21 (by decide), h21]
    have h27' : reg n5 (27 : Fin 32) = BitVec.ofNat 32 mf.image.length := by rw [k5 27 (by decide), v27]
    simp only [u6.regs]
    simp +decide only [runBlock, BInstr.run, acrC4, upd, ↓reduceIte, aluEval]
    rw [h9'', sp5, acr_sa B 0x1310 0x187C 0x56C rfl, acr_sa B 0x1310 0x1880 0x570 rfl,
      acr_sa B 0x1310 0x1884 0x574 rfl, acr_sa B 0x1310 0x1888 0x578 rfl, e44, mem5 0x187C (by decide) (by decide),
      mem5 0x1880 (by decide) (by decide), mem5 0x1884 (by decide) (by decide), mem5 0x1888 (by decide) (by decide),
      fC, f10, f14, f18, h21', h27', v22', M5, M3, M2, M1, memLoad32_store32_same]
    simp only [acr_zadd]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨w9, w18, w20, w22, w23, w25, w27, wa0, wa1, wa2⟩ := v6
  have A6 := A5.next (fun x _ _ => by rw [M6]) (k6 2 (by decide) (by decide)) (k6 3 (by decide) (by decide))
    (k6 4 (by decide) (by decide))
  have hBo : (Bf + 0xB840 : Word).toNat = Bf.toNat + 0xB840 := X.bf 0xB840 (by decide)
  have hmin : (BitVec.ofNat 32 (min mf.image.length 0x114)).toNat = min mf.image.length 0x114 := acr_on (by omega)
  obtain ⟨n7, c7, s7, k7, a07, ok7, fr7⟩ := acr_fread X A6 (o := 0xBE) (acr_re u6) ac_at_be ac_at_c2
    (by decide) (by decide) (by decide) wa0 wa1 wa2
    (by rw [hBo, hmin]; omega) (by rw [hBo, hmin]; omega)
  have A7 := A6.keep (fun x e1 e2 => fr7 x (by omega) (by rw [hBo, hmin]; omega)) k7
  have K7 : ∀ q : Fin 32, romKeep q = true → reg n7 q = reg n6 q := k7
  obtain ⟨n8, e8, M8, r8, ⟨hb8, s8⟩ | ⟨hb8, s8⟩⟩ := acr_br s7 (X.code A7) ac_at_c6 (oT := 0x16A) (oF := 0xC8)
    (by decide) (by decide)
  · refine AcrGo.fail (c1.trans (.cons e2 (c3.trans (c5.trans (c6.trans (c7.trans (.single e8)))))))
      (A7.keep (fun x _ _ => by rw [M8]) fun q _ => r8 q) (.inr (.inl ⟨s8.pc, ?_⟩))
    rw [r8, K7 19 (by decide), K6 19 (by decide) (by decide), h19]
  · have h1 : reg n7 a0 = 1 := by
      rcases a07 with h | h
      · rw [h, s7.zero] at hb8; exact absurd hb8 (by decide)
      · exact h
    have hA : (BitVec.ofNat 32 (acBase slot + mf.image.offset)).toNat = acBase slot + mf.image.offset :=
      acr_on (by omega)
    have kk : ∀ q : Fin 32, romKeep q = true → reg n8 q = reg n6 q := fun q hq => by rw [r8, K7 q hq]
    refine AcrGo.done (c1.trans (.cons e2 (c3.trans (c5.trans (c6.trans (c7.trans (.single e8)))))))
      (A7.keep (fun x _ _ => by rw [M8]) fun q _ => r8 q) ⟨s8, fun q hq ho => by rw [kk q hq, K6 q hq ho],
        by rw [kk 9 (by decide), w9], by rw [kk 18 (by decide), w18], by rw [kk 20 (by decide), w20],
        by rw [kk 22 (by decide), w22], by rw [kk 23 (by decide), w23], by rw [kk 25 (by decide), w25],
        by rw [kk 27 (by decide), w27], ?_, fun i hi => ?_⟩
    · have hS := X.sl 0x44 (by decide)
      rw [M8, memLoad32_congr fun j hj => fr7 _ (by rw [acr_tn _ _ (by omega)]; omega)
        (by rw [acr_tn _ _ (by omega), hBo, hmin]; omega), M6, M5, M3, M2, M1, memLoad32_store32_same]
    · rw [M8, ok7 h1 i (by rw [hmin]; exact hi), hA]

end segs

/-! ## 0xC8-0x100: the frame slots and a fresh hasher -/

def acrD1 : List BInstr :=
  [.sw sp (23 : Fin 32) 0x30, .sw sp (20 : Fin 32) 0x38, .sw sp (8 : Fin 32) 0x3C, .sw sp (19 : Fin 32) 0x40,
    .sb sp x0 0xA7, .aluImm .add a0 sp 0xA8, .lui a1 0x3FCC4000, .aluImm .add a1 a1 0x118,
    .aluImm .add a2 x0 0x20]

set_option maxRecDepth 100000 in
theorem acrD1_end : blockEnd bootMainClosure0Code 0xC8 acrD1 = some 0xE2 := by decide

def acrD2 : List BInstr :=
  [.aluImm .add (19 : Fin 32) x0 0x0, .sw sp x0 0xC8, .sw sp x0 0xCC, .lui (20 : Fin 32) 0x4000,
    .aluImm .add (23 : Fin 32) x0 0x5, .sw sp (21 : Fin 32) 0x34, .alu .add (20 : Fin 32) (20 : Fin 32) (21 : Fin 32),
    .aluImm .sll (23 : Fin 32) (23 : Fin 32) 0xB, .lw (8 : Fin 32) sp 0x44]

set_option maxRecDepth 100000 in
theorem acrD2_end : blockEnd bootMainClosure0Code 0xEA acrD2 = some 0xFC := by decide

/-- The frame slots that the read stage leaves for the next stages. -/
abbrev AcrSlots (M : Word → BitVec 8) (B Bf r slot : Word) (mf : Manifest) : Prop :=
  memLoad32 M (acSlot B 0x30) = BitVec.ofNat 32 mf.tuf.offset ∧
  memLoad32 M (acSlot B 0x34) = Bf ∧
  memLoad32 M (acSlot B 0x38) = BitVec.ofNat 32 mf.bundle.length ∧
  memLoad32 M (acSlot B 0x3C) = slot ∧
  memLoad32 M (acSlot B 0x40) = r ∧
  memLoad32 M (acSlot B 0x44) = BitVec.ofNat 32 (acBase slot + mf.image.offset)

/-- The bytes that the loop and the last reads leave alone: outside the
callees' stack, the hasher, the digest, the bundle, and `doc`. -/
def AcrFr (B Bf x : Word) : Prop :=
  (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) ∧ (x.toNat < B.toNat + 0x3AB8 ∨ B.toNat + 0x3B44 ≤ x.toNat) ∧
  (x.toNat < Bf.toNat ∨ Bf.toNat + 0x6800 ≤ x.toNat)

section segs

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

theorem AcrX.slots (X : AcrX flash R romBase romCode n0 B Bf M0) {M M' : Word → BitVec 8} {r slot : Word}
    {mf : Manifest} (S : AcrSlots M B Bf r slot mf) (h : ∀ x, AcrFr B Bf x → M' x = M x) :
    AcrSlots M' B Bf r slot mf := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have := hF.hi
  have dj := X.dj
  have hBw := X.hBw
  have e : ∀ c, 0x30 ≤ c → c ≤ 0x44 → memLoad32 M' (acSlot B c) = memLoad32 M (acSlot B c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => h _ (by
      unfold AcrFr; rw [acr_slot_add, hF.at _ (by omega)]; exact ⟨by omega, by omega, by omega⟩)
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := S
  exact ⟨by rw [e _ (by decide) (by decide), s1], by rw [e _ (by decide) (by decide), s2],
    by rw [e _ (by decide) (by decide), s3], by rw [e _ (by decide) (by decide), s4],
    by rw [e _ (by decide) (by decide), s5], by rw [e _ (by decide) (by decide), s6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From 0xC8 to 0x100: the slots at `sp + 0x30` to `sp + 0x40`, a hasher
with no input at `sp + 0x68`, and the loop's registers. -/
theorem acr_segD (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0xC8 (reg n)) {r slot : Word} {mf : Manifest}
    (hd : decodeManifest (flashBytes flash (acBase slot) 32) = some mf)
    (h8 : reg n (8 : Fin 32) = slot) (h19 : reg n (19 : Fin 32) = r)
    (h20 : reg n (20 : Fin 32) = BitVec.ofNat 32 mf.bundle.length) (h21 : reg n (21 : Fin 32) = Bf)
    (h23 : reg n (23 : Fin 32) = BitVec.ofNat 32 mf.tuf.offset)
    (h27 : reg n (27 : Fin 32) = BitVec.ofNat 32 mf.image.length)
    (m44 : memLoad32 n.mem (acSlot B 0x44) = BitVec.ofNat 32 (acBase slot + mf.image.offset)) :
    AcrGo B Bf g t r n0 n fun n' => St n'.mem AC n' 0x100 (reg n') ∧
      (∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (23 : Fin 32) →
        reg n' q = reg n q) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (acBase slot + mf.image.offset) ∧ reg n' (19 : Fin 32) = 0 ∧
      reg n' (20 : Fin 32) = Bf + 0x4000 ∧ reg n' (23 : Fin 32) = 0x2800 ∧
      AcrSlots n'.mem B Bf r slot mf ∧ HasherAt n'.mem (acSlot B 0x68) [] ∧
      ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat) → n'.mem x = n.mem x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have hBa := hF.al
  obtain ⟨-, il1, -⟩ := acr_bounds hd
  have z0 := s.zero
  have e30 := acr_at B 0x30 0x30 rfl (by decide)
  have e34 := acr_at B 0x34 0x34 rfl (by decide)
  have e38 := acr_at B 0x38 0x38 rfl (by decide)
  have e3C := acr_at B 0x3C 0x3C rfl (by decide)
  have e40 := acr_at B 0x40 0x40 rfl (by decide)
  have e44 := acr_at B 0x44 0x44 rfl (by decide)
  have eA7 := acr_at B 0xA7 0xA7 rfl (by decide)
  have eA8 := acr_at B 0xA8 0xA8 rfl (by decide)
  have eC8 := acr_at B 0xC8 0xC8 rfl (by decide)
  have eCC := acr_at B 0xCC 0xCC rfl (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xE2) acrD1 (X.code A) acrD1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrD1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [A.sp, e30, e38, e3C, e40, eA7]
    exact ⟨X.al 0x30 (by decide) (by decide), X.al 0x38 (by decide) (by decide), X.al 0x3C (by decide) (by decide),
      X.al 0x40 (by decide) (by decide), hF.sepHi (c := 0x3A50 + 0xA7) (n := 1) (by omega) (by decide) (by decide)⟩)
  have M1 : n1.mem = memStore8 (memStore32 (memStore32 (memStore32 (memStore32 n.mem (acSlot B 0x30)
      (BitVec.ofNat 32 mf.tuf.offset)) (acSlot B 0x38) (BitVec.ofNat 32 mf.bundle.length)) (acSlot B 0x3C) slot)
      (acSlot B 0x40) r) (acSlot B 0xA7) 0 := by
    rw [u1.mem]; simp +decide only [runBlock, BInstr.run, acrD1, upd, ↓reduceIte]
    rw [A.sp, e30, e38, e3C, e40, eA7, h8, h19, h20, h23]; rfl
  have k1 : ∀ q : Fin 32, romKeep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q z0 (by simp only [acrD1]; revert hq; revert q; decide)]
  have a0v : reg n1 a0 = acSlot B 0xA8 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acrD1, upd, ↓reduceIte, aluEval]
    rw [A.sp, eA8]
  have a1v : reg n1 a1 = BitVec.ofNat 32 shaIVAddress := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acrD1, upd, ↓reduceIte, aluEval]
  have a2v : reg n1 a2 = BitVec.ofNat 32 32 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acrD1, upd, ↓reduceIte, aluEval]
  have G1 : ∀ x, (x.toNat < B.toNat + 0x3A80 ∨ B.toNat + 0x3B20 ≤ x.toNat) → n1.mem x = n.mem x := fun x hx => by
    rw [M1, X.g8 _ (by decide) (by omega), X.g32 _ (by decide) (by omega), X.g32 _ (by decide) (by omega),
      X.g32 _ (by decide) (by omega), X.g32 _ (by decide) (by omega)]
  have A1 := A.keep (fun x e _ => G1 x (by omega)) k1
  -- the initial hash value
  obtain ⟨n2, c2, s2, k2, cp2⟩ := acr_memcpy X A1 (acr_re u1) a0v a1v a2v
  have hA8 := X.sl 0xA8 (by decide)
  have G2 : ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) →
      (x.toNat < B.toNat + 0x3AF8 ∨ B.toNat + 0x3B18 ≤ x.toNat) → n2.mem x = n1.mem x := fun x e1 e2 => by
    rw [cp2 x e1, copyBytes_sep (acr_sep (by rw [hA8]; omega) (by rw [hA8]; omega) (by have := x.isLt; omega))
      (Nat.le_refl 32)]
  have A2 := A1.keep (fun x e _ => by
    rw [cp2 x (by omega), copyBytes_sep (acr_sep (by rw [hA8]; omega) (by rw [hA8]; omega)
      (by have := x.isLt; omega)) (Nat.le_refl 32)]) k2
  have L2 : ∀ c, c + 4 ≤ 0x2020 → (c + 4 ≤ 0xA8 ∨ 0xC8 ≤ c) →
      memLoad32 n2.mem (acSlot B c) = memLoad32 n1.mem (acSlot B c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => G2 _ (by rw [acr_slot_add, X.sl _ (by omega)]; omega)
      (by rw [acr_slot_add, X.sl _ (by omega)]; omega)
  -- the hasher's count, the slot of `Buffers`, and the image's address
  have z2 := s2.zero
  have sp2 : reg n2 sp = B + 0x3A50 := A2.sp
  obtain ⟨n3, c3, u3⟩ := s2.block (off' := 0xFC) acrD2 (X.code A2) acrD2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrD2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp2, eC8, eCC, e34, e44]
    exact ⟨X.al 0xC8 (by decide) (by decide), X.al 0xCC (by decide) (by decide), X.al 0x34 (by decide) (by decide),
      (X.al 0x44 (by decide) (by decide)).1⟩)
  have h21' : reg n2 (21 : Fin 32) = Bf := by rw [k2 21 (by decide), k1 21 (by decide), h21]
  have M3 : n3.mem = memStore32 (memStore32 (memStore32 n2.mem (acSlot B 0xC8) 0) (acSlot B 0xCC) 0)
      (acSlot B 0x34) Bf := by
    rw [u3.mem]; simp +decide only [runBlock, BInstr.run, acrD2, upd, ↓reduceIte]
    rw [sp2, eC8, eCC, e34, h21']
  have k3 : ∀ q : Fin 32, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (23 : Fin 32) → reg n3 q = reg n2 q := fun q hq h1 h2 h3 h4 => by
    rw [u3.regs, runBlock_reg _ _ _ q z2 (by
      simp only [acrD2]; revert h4; revert h3; revert h2; revert h1; revert hq; revert q; decide)]
  have m44' : memLoad32 n2.mem (acSlot B 0x44) = BitVec.ofNat 32 (acBase slot + mf.image.offset) := by
    rw [L2 _ (by decide) (.inl (by decide)), M1, X.l8 _ (.inr (by decide)) (by decide) (by decide),
      X.l32 _ (.inl (by decide)) (by decide) (by decide), X.l32 _ (.inl (by decide)) (by decide) (by decide),
      X.l32 _ (.inl (by decide)) (by decide) (by decide), X.l32 _ (.inl (by decide)) (by decide) (by decide), m44]
  have v3 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 (acBase slot + mf.image.offset) ∧ reg n3 (19 : Fin 32) = 0 ∧
      reg n3 (20 : Fin 32) = Bf + 0x4000 ∧ reg n3 (23 : Fin 32) = 0x2800 := by
    simp only [u3.regs]
    simp +decide only [runBlock, BInstr.run, acrD2, upd, ↓reduceIte, aluEval]
    rw [sp2, eC8, eCC, e34, e44, h21', X.l32 _ (.inl (by decide)) (by decide) (by decide),
      X.l32 _ (.inr (by decide)) (by decide) (by decide), X.l32 _ (.inr (by decide)) (by decide) (by decide), m44',
      BitVec.add_comm Bf]
    exact ⟨rfl, rfl, rfl, by decide⟩
  obtain ⟨w8, w19, w20, w23⟩ := v3
  have G3 : ∀ x, (x.toNat < B.toNat + 0x3A84 ∨ B.toNat + 0x3A88 ≤ x.toNat) →
      (x.toNat < B.toNat + 0x3B18 ∨ B.toNat + 0x3B20 ≤ x.toNat) → n3.mem x = n2.mem x := fun x e1 e2 => by
    rw [M3, X.g32 _ (by decide) (by omega), X.g32 _ (by decide) (by omega), X.g32 _ (by decide) (by omega)]
  have A3 := A2.next (fun x e _ => G3 x (by omega) (by omega))
    (k3 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (k3 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (k3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  -- the loop runs: the image isn't empty
  obtain ⟨n4, e4, M4, r4, ⟨hb4, s4⟩ | ⟨hb4, s4⟩⟩ := acr_br (acr_re u3) (X.code A3) ac_at_fc (oT := 0x134)
    (oF := 0x100) (by decide) (by decide)
  · exfalso
    have h27' : reg n3 (27 : Fin 32) = BitVec.ofNat 32 mf.image.length := by
      rw [k3 27 (by decide) (by decide) (by decide) (by decide) (by decide), k2 27 (by decide), k1 27 (by decide), h27]
    rw [h27', (acr_re u3).zero] at hb4
    have := congrArg BitVec.toNat (beq_iff_eq.mp hb4)
    obtain ⟨-, il1, il2, -⟩ := acr_bounds hd
    rw [acr_on (a := mf.image.length) (by omega)] at this
    have hl : mf.image.length = 0 := this.trans rfl
    omega
  have kk : ∀ q : Fin 32, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (23 : Fin 32) → reg n4 q = reg n q := fun q hq h1 h2 h3 h4 => by
    rw [r4, k3 q hq h1 h2 h3 h4, k2 q hq, k1 q hq]
  have L3 : ∀ c, c + 4 ≤ 0xA7 → (c + 4 ≤ 0x34 ∨ 0x38 ≤ c) → memLoad32 n3.mem (acSlot B c) = memLoad32 n2.mem (acSlot B c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => G3 _ (by rw [acr_slot_add, X.sl _ (by omega)]; omega)
      (by rw [acr_slot_add, X.sl _ (by omega)]; omega)
  have hS := X.sl 0x68 (by decide)
  refine AcrGo.done (c1.trans (c2.trans (c3.trans (.single e4)))) (A3.keep (fun x _ _ => by rw [M4])
    fun q _ => r4 q) ⟨s4, kk, by rw [r4, w8], by rw [r4, w19], by rw [r4, w20], by rw [r4, w23], ?_, ?_, ?_⟩
  · rw [M4]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [L3 _ (by decide) (by decide), L2 _ (by decide) (.inl (by decide)), M1,
        X.l8 _ (.inr (by decide)) (by decide) (by decide), X.l32 _ (.inr (by decide)) (by decide) (by decide),
        X.l32 _ (.inr (by decide)) (by decide) (by decide), X.l32 _ (.inr (by decide)) (by decide) (by decide),
        memLoad32_store32_same]
    · rw [M3, memLoad32_store32_same]
    · rw [L3 _ (by decide) (by decide), L2 _ (by decide) (.inl (by decide)), M1,
        X.l8 _ (.inr (by decide)) (by decide) (by decide), X.l32 _ (.inr (by decide)) (by decide) (by decide),
        X.l32 _ (.inr (by decide)) (by decide) (by decide), memLoad32_store32_same]
    · rw [L3 _ (by decide) (by decide), L2 _ (by decide) (.inl (by decide)), M1,
        X.l8 _ (.inr (by decide)) (by decide) (by decide), X.l32 _ (.inr (by decide)) (by decide) (by decide),
        memLoad32_store32_same]
    · rw [L3 _ (by decide) (by decide), L2 _ (by decide) (.inl (by decide)), M1,
        X.l8 _ (.inr (by decide)) (by decide) (by decide), memLoad32_store32_same]
    · rw [L3 _ (by decide) (by decide), m44']
  · rw [M4]
    refine acr_h0 (X.env A1).cIV ?_ (fun k hk => ?_) ?_ ?_
    · have hA7 := X.sl 0xA7 (by decide)
      rw [acr_sa B 0x68 0xA7 0x3F rfl, M3, X.g32 _ (by decide) (by omega), X.g32 _ (by decide) (by omega),
        X.g32 _ (by decide) (by omega), G2 _ (by omega) (by omega), M1, memStore8_same]
    · have hx : (acSlot B 0xA8 + BitVec.ofNat 32 k).toNat = B.toNat + 0x3A50 + 0xA8 + k := by
        rw [acr_slot_add, X.sl _ (by omega)]; omega
      rw [acr_sa B 0x68 0xA8 0x40 rfl, M3, X.g32 _ (by decide) (by omega), X.g32 _ (by decide) (by omega),
        X.g32 _ (by decide) (by omega), cp2 _ (by omega), copyBytes_in hk (by decide)]
    · rw [acr_sa B 0x68 0xC8 0x60 rfl, M3, X.l32 _ (.inl (by decide)) (by decide) (by decide),
        X.l32 _ (.inr (by decide)) (by decide) (by decide), memLoad32_store32_same]
    · rw [acr_sa B 0x68 0xCC 0x64 rfl, M3, X.l32 _ (.inl (by decide)) (by decide) (by decide),
        memLoad32_store32_same]
  · intro x hx
    have hx' := x.isLt
    have dj := X.dj
    rw [M4, G3 x (by omega) (by omega), G2 x (by omega) (by omega), G1 x (by omega)]

end segs

/-! ## 0x100-0x134: the image's hash, 0x2800 bytes at a time -/

def acrL1 : List BInstr := [.alu .sub (21 : Fin 32) (27 : Fin 32) (19 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrL1_end : blockEnd bootMainClosure0Code 0x100 acrL1 = some 0x104 := by decide

def acrL2 : List BInstr := [.alu .add (21 : Fin 32) x0 (23 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrL2_end : blockEnd bootMainClosure0Code 0x108 acrL2 = some 0x10A := by decide

def acrL3 : List BInstr := [.alu .add a0 (19 : Fin 32) (8 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrL3_end : blockEnd bootMainClosure0Code 0x10A acrL3 = some 0x10E := by decide

def acrL4 : List BInstr := [.alu .add a1 x0 (20 : Fin 32), .alu .add a2 x0 (21 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrL4_end : blockEnd bootMainClosure0Code 0x112 acrL4 = some 0x116 := by decide

def acrL5 : List BInstr := [.aluImm .add a0 sp 0x68, .alu .add a1 x0 (20 : Fin 32), .alu .add a2 x0 (21 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrL5_end : blockEnd bootMainClosure0Code 0x120 acrL5 = some 0x126 := by decide

def acrL6 : List BInstr := [.alu .add (19 : Fin 32) (19 : Fin 32) (21 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrL6_end : blockEnd bootMainClosure0Code 0x12E acrL6 = some 0x130 := by decide

/-- The loop's state at `o` after `c` bytes of the image at `Af`, against the
state `nD` at the loop's entry. -/
structure AcrLp (flash : Nat → BitVec 8) (B Bf : Word) (Af c : Nat) (nD n : Machine) (o : Nat) : Prop where
  st : St n.mem AC n o (reg n)
  keep : ∀ q, romKeep q = true → q ≠ (19 : Fin 32) → q ≠ (21 : Fin 32) → reg n q = reg nD q
  r19 : reg n (19 : Fin 32) = BitVec.ofNat 32 c
  fr : ∀ x, AcrFr B Bf x → n.mem x = nD.mem x
  H : HasherAt n.mem (acSlot B 0x68) (flashBytes flash Af c)

section segs

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

/-- The hasher's bytes are outside the callees' stack. -/
theorem AcrX.hcopy (X : AcrX flash R romBase romCode n0 B Bf M0) {M M' : Word → BitVec 8} {msg : Bytes}
    (H : HasherAt M (acSlot B 0x68) msg)
    (h : ∀ x, (x.toNat < B.toNat ∨ B.toNat + 0x3A50 ≤ x.toNat) →
      (x.toNat < Bf.toNat ∨ Bf.toNat + acBufLen ≤ x.toNat) → M' x = M x) :
    HasherAt M' (acSlot B 0x68) msg :=
  H.copy fun i hi => by
    have hF := X.F
    have hBL : acBufLen = 0xB954 := rfl
    have := hF.hi
    have dj := X.dj
    rw [acr_slot_add]
    exact h _ (by rw [hF.at _ (by omega)]; omega) (by rw [hF.at _ (by omega)]; omega)

/-- `sp + 0x40` is outside what the loop writes. -/
theorem AcrX.m40 (X : AcrX flash R romBase romCode n0 B Bf M0) {M M' : Word → BitVec 8}
    (h : ∀ x, AcrFr B Bf x → M' x = M x) : memLoad32 M' (acSlot B 0x40) = memLoad32 M (acSlot B 0x40) := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have := hF.hi
  have dj := X.dj
  have hBw := X.hBw
  exact memLoad32_congr fun j hj => h _ (by unfold AcrFr; rw [acr_slot_add, hF.at _ (by omega)]; exact ⟨by omega, by omega, by omega⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- One pass of the loop: `k` more bytes of the image, read into `doc` and
fed to the hasher. -/
theorem acr_iter (X : AcrX flash R romBase romCode n0 B Bf M0) {nD n : Machine} (A : AcrAt B Bf g t n0 n)
    {r : Word} {Af L c : Nat} (D8 : reg nD (8 : Fin 32) = BitVec.ofNat 32 Af)
    (D20 : reg nD (20 : Fin 32) = Bf + 0x4000) (D23 : reg nD (23 : Fin 32) = 0x2800)
    (D27 : reg nD (27 : Fin 32) = BitVec.ofNat 32 L) (D40 : memLoad32 nD.mem (acSlot B 0x40) = r)
    (hAL : Af + L < 2 ^ 31) (hc : c < L) (P : AcrLp flash B Bf Af c nD n 0x100) :
    AcrGo B Bf g t r n0 n fun n' => ∃ k, 0 < k ∧ c + k ≤ L ∧
      ((c + k < L ∧ AcrLp flash B Bf Af (c + k) nD n' 0x100) ∨ (c + k = L ∧ AcrLp flash B Bf Af L nD n' 0x134)) := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have dj := X.dj
  have hBw := X.hBw
  have s := P.st
  have z0 := s.zero
  have r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 Af := by rw [P.keep 8 (by decide) (by decide) (by decide), D8]
  have r20 : reg n (20 : Fin 32) = Bf + 0x4000 := by rw [P.keep 20 (by decide) (by decide) (by decide), D20]
  have r23 : reg n (23 : Fin 32) = 0x2800 := by rw [P.keep 23 (by decide) (by decide) (by decide), D23]
  have r27 : reg n (27 : Fin 32) = BitVec.ofNat 32 L := by rw [P.keep 27 (by decide) (by decide) (by decide), D27]
  -- the chunk's length
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x104) acrL1 (X.code A) acrL1_end ⟨trivial, trivial⟩
  have k1 : ∀ q : Fin 32, q ≠ (21 : Fin 32) → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q z0 (by simp only [acrL1]; revert hq; revert q; decide)]
  have v1 : reg n1 (21 : Fin 32) = BitVec.ofNat 32 (L - c) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acrL1, upd, ↓reduceIte, aluEval]
    rw [r27, P.r19, acr_sub (by omega) (by omega)]
  have A1 := A.next (fun x _ _ => by rw [u1.mem]; rfl) (k1 2 (by decide)) (k1 3 (by decide)) (k1 4 (by decide))
  have hLc : (BitVec.ofNat 32 (L - c)).toNat = L - c := acr_on (by omega)
  obtain ⟨n3, c3, s3, M3, k3, v3⟩ : ∃ n3, Steps n1 n3 ∧ St n3.mem AC n3 0x10A (reg n3) ∧ n3.mem = n1.mem ∧
      (∀ q : Fin 32, q ≠ (21 : Fin 32) → reg n3 q = reg n1 q) ∧
      reg n3 (21 : Fin 32) = BitVec.ofNat 32 (min (L - c) 0x2800) := by
    obtain ⟨n2, e2, M2, r2, ⟨hb2, s2⟩ | ⟨hb2, s2⟩⟩ := acr_br (acr_re u1) (X.code A1) ac_at_104 (oT := 0x10A)
      (oF := 0x108) (by decide) (by decide)
    · have := acr_ult hb2
      rw [v1, k1 23 (by decide), r23, hLc] at this
      refine ⟨n2, .single e2, s2, M2, fun q _ => r2 q, ?_⟩
      rw [r2, v1, Nat.min_eq_left (by have : (0x2800 : Word).toNat = 0x2800 := rfl; omega)]
    · have := acr_ult' hb2
      rw [v1, k1 23 (by decide), r23, hLc] at this
      have z2 := s2.zero
      obtain ⟨n3, c3, u3⟩ := s2.block (off' := 0x10A) acrL2 (X.code (A1.keep (fun x _ _ => by rw [M2])
        fun q _ => r2 q)) acrL2_end ⟨trivial, trivial⟩
      refine ⟨n3, .cons e2 c3, acr_re u3, by rw [u3.mem, M2]; rfl, fun q hq => ?_, ?_⟩
      · rw [u3.regs, runBlock_reg _ _ _ q z2 (by simp only [acrL2]; revert hq; revert q; decide), r2]
      · rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acrL2, upd, ↓reduceIte, aluEval]
        rw [show reg n2 x0 = 0 from z2, r2, k1 23 (by decide), r23, acr_zadd,
          Nat.min_eq_right (by have : (0x2800 : Word).toNat = 0x2800 := rfl; omega)]
        rfl
  have A3 := A1.next (fun x _ _ => by rw [M3]) (k3 2 (by decide)) (k3 3 (by decide)) (k3 4 (by decide))
  have K3 : ∀ q : Fin 32, q ≠ (21 : Fin 32) → reg n3 q = reg n q := fun q hq => by rw [k3 q hq, k1 q hq]
  generalize hk : min (L - c) 0x2800 = k at v3
  have hk1 : 0 < k := by omega
  have hk2 : k ≤ 0x2800 := by omega
  have hk3 : c + k ≤ L := by omega
  -- the flash address, and its overflow check
  have z3 := s3.zero
  obtain ⟨n4, c4, u4⟩ := s3.block (off' := 0x10E) acrL3 (X.code A3) acrL3_end ⟨trivial, trivial⟩
  have k4 : ∀ q : Fin 32, romKeep q = true → reg n4 q = reg n3 q := fun q hq => by
    rw [u4.regs, runBlock_reg _ _ _ q z3 (by simp only [acrL3]; revert hq; revert q; decide)]
  have v4 : reg n4 a0 = BitVec.ofNat 32 (Af + c) := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, acrL3, upd, ↓reduceIte, aluEval]
    rw [K3 19 (by decide), P.r19, K3 8 (by decide), r8, acr_oadd]
  have A4 := A3.keep (fun x _ _ => by rw [u4.mem]; rfl) k4
  have K4 : ∀ q : Fin 32, romKeep q = true → q ≠ (19 : Fin 32) → q ≠ (21 : Fin 32) → reg n4 q = reg nD q :=
    fun q hq h1 h2 => by rw [k4 q hq, K3 q h2, P.keep q hq h1 h2]
  have N4 : n4.mem = n3.mem := u4.mem
  have N1 : n1.mem = n.mem := u1.mem
  have F4 : ∀ x, AcrFr B Bf x → n4.mem x = nD.mem x := fun x h => by rw [N4, M3, N1]; exact P.fr x h
  obtain ⟨n5, e5, M5, r5, ⟨hb5, s5⟩ | ⟨hb5, s5⟩⟩ := acr_br (acr_re u4) (X.code A4) ac_at_10e (oT := 0x166)
    (oF := 0x112) (by decide) (by decide)
  · exact AcrGo.fail (c1.trans (c3.trans (c4.trans (.single e5)))) (A4.keep (fun x _ _ => by rw [M5])
      fun q _ => r5 q) (.inl ⟨s5.pc, by rw [M5, X.m40 F4, D40]⟩)
  have A5 := A4.keep (fun x _ _ => by rw [M5]) fun q _ => r5 q
  -- the chunk into `doc`
  have z5 := s5.zero
  obtain ⟨n6, c6, u6⟩ := s5.block (off' := 0x116) acrL4 (X.code A5) acrL4_end ⟨trivial, trivial, trivial⟩
  have k6 : ∀ q : Fin 32, romKeep q = true → reg n6 q = reg n5 q := fun q hq => by
    rw [u6.regs, runBlock_reg _ _ _ q z5 (by simp only [acrL4]; revert hq; revert q; decide)]
  have v6 : reg n6 a0 = BitVec.ofNat 32 (Af + c) ∧ reg n6 a1 = Bf + 0x4000 ∧ reg n6 a2 = BitVec.ofNat 32 k := by
    simp only [u6.regs]; simp +decide only [runBlock, BInstr.run, acrL4, upd, ↓reduceIte, aluEval]
    simp only [r5]
    rw [v4, k4 20 (by decide), K3 20 (by decide), r20, k4 21 (by decide), v3,
      show reg n4 x0 = 0 from (acr_re u4).zero]
    simp only [acr_zadd]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  have N6 : n6.mem = n5.mem := u6.mem
  have A6 := A5.keep (fun x _ _ => by rw [N6]) k6
  have hD : (Bf + 0x4000 : Word).toNat = Bf.toNat + 0x4000 := X.bf 0x4000 (by decide)
  have hkn : (BitVec.ofNat 32 k).toNat = k := acr_on (by omega)
  obtain ⟨n7, c7, s7, k7, a07, ok7, fr7⟩ := acr_fread X A6 (o := 0x116) (acr_re u6) ac_at_116 ac_at_11a
    (by decide) (by decide) (by decide) v6.1 v6.2.1 v6.2.2 (by rw [hD, hkn]; omega) (by rw [hD, hkn]; omega)
  have A7 := A6.keep (fun x e1 e2 => fr7 x (by omega) (by rw [hD, hkn]; omega)) k7
  have F7 : ∀ x, AcrFr B Bf x → n7.mem x = nD.mem x := fun x h => by
    obtain ⟨h1, h2, h3⟩ := h
    rw [fr7 x h1 (by rw [hD, hkn]; omega), N6, M5]
    exact F4 x ⟨h1, h2, h3⟩
  obtain ⟨n8, e8, M8, r8', ⟨hb8, s8⟩ | ⟨hb8, s8⟩⟩ := acr_br s7 (X.code A7) ac_at_11e (oT := 0x166) (oF := 0x120)
    (by decide) (by decide)
  · exact AcrGo.fail (c1.trans (c3.trans (c4.trans (.cons e5 (c6.trans (c7.trans (.single e8)))))))
      (A7.keep (fun x _ _ => by rw [M8]) fun q _ => r8' q) (.inl ⟨s8.pc, by rw [M8, X.m40 F7, D40]⟩)
  have h1 : reg n7 a0 = 1 := by
    rcases a07 with h | h
    · rw [h, s7.zero] at hb8; exact absurd hb8 (by decide)
    · exact h
  have A8 := A7.keep (fun x _ _ => by rw [M8]) fun q _ => r8' q
  have KK8 : ∀ q : Fin 32, romKeep q = true → reg n8 q = reg n4 q := fun q hq => by
    rw [r8', k7 q hq, k6 q hq, r5]
  -- the chunk into the hasher
  have z8 := s8.zero
  obtain ⟨n9, c9, u9⟩ := s8.block (off' := 0x126) acrL5 (X.code A8) acrL5_end ⟨trivial, trivial, trivial, trivial⟩
  have N9 : n9.mem = n8.mem := u9.mem
  have k9 : ∀ q : Fin 32, romKeep q = true → reg n9 q = reg n8 q := fun q hq => by
    rw [u9.regs, runBlock_reg _ _ _ q z8 (by simp only [acrL5]; revert hq; revert q; decide)]
  have v9 : reg n9 a0 = acSlot B 0x68 ∧ reg n9 a1 = Bf + 0x4000 ∧ reg n9 a2 = BitVec.ofNat 32 k := by
    simp only [u9.regs]; simp +decide only [runBlock, BInstr.run, acrL5, upd, ↓reduceIte, aluEval]
    rw [A8.sp, acr_at B 0x68 0x68 rfl (by decide), KK8 20 (by decide), k4 20 (by decide), K3 20 (by decide), r20,
      KK8 21 (by decide), k4 21 (by decide), v3]
    simp only [acr_zadd]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  have A9 := A8.keep (fun x _ _ => by rw [N9]) k9
  have hS := X.sl 0x68 (by decide)
  have H9 : HasherAt n9.mem (acSlot B 0x68) (flashBytes flash Af c) := X.hcopy P.H fun x e1 e2 => by
    rw [N9, M8, fr7 x e1 (by rw [hD, hkn]; omega), N6, M5, N4, M3, N1]
  obtain ⟨n10, c10, s10, k10, H10, fr10⟩ := acr_update X A9 (acr_re u9) v9.1 v9.2.1 v9.2.2
    (by rw [hD]; omega) (by rw [hD]; omega) H9 (by omega) (by rw [acr_fb_len]; omega)
  have A10 := A9.keep (fun x e1 e2 => fr10 x (by omega) (by omega)) k10
  have hm : memBytes n9.mem (Bf + 0x4000) k = flashBytes flash (Af + c) k := by
    unfold memBytes flashBytes
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [N9, M8, ok7 h1 i (by rw [hkn]; exact hi), acr_on (by omega)]
  rw [hm, ← acr_fb_add] at H10
  -- the count
  have z10 := s10.zero
  obtain ⟨n11, c11, u11⟩ := s10.block (off' := 0x130) acrL6 (X.code A10) acrL6_end ⟨trivial, trivial⟩
  have N11 : n11.mem = n10.mem := u11.mem
  have k11 : ∀ q : Fin 32, q ≠ (19 : Fin 32) → reg n11 q = reg n10 q := fun q hq => by
    rw [u11.regs, runBlock_reg _ _ _ q z10 (by simp only [acrL6]; revert hq; revert q; decide)]
  have KK : ∀ q : Fin 32, romKeep q = true → reg n10 q = reg n4 q := fun q hq => by
    rw [k10 q hq, k9 q hq, KK8 q hq]
  have v11 : reg n11 (19 : Fin 32) = BitVec.ofNat 32 (c + k) := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, acrL6, upd, ↓reduceIte, aluEval]
    rw [KK 19 (by decide), KK 21 (by decide), k4 19 (by decide), k4 21 (by decide), K3 19 (by decide), P.r19, v3,
      acr_oadd, Nat.add_comm]
  have A11 := A10.next (fun x _ _ => by rw [N11]) (k11 2 (by decide)) (k11 3 (by decide)) (k11 4 (by decide))
  have K11 : ∀ q : Fin 32, romKeep q = true → q ≠ (19 : Fin 32) → q ≠ (21 : Fin 32) → reg n11 q = reg nD q :=
    fun q hq h1 h2 => by rw [k11 q h1, KK q hq, K4 q hq h1 h2]
  have F11 : ∀ x, AcrFr B Bf x → n11.mem x = nD.mem x := fun x h => by
    obtain ⟨h1, h2, h3⟩ := h
    rw [N11, fr10 x h1 (by omega), N9, M8]
    exact F7 x ⟨h1, h2, h3⟩
  have hck : (BitVec.ofNat 32 (c + k)).toNat = c + k := acr_on (by omega)
  have hL : (BitVec.ofNat 32 L).toNat = L := acr_on (by omega)
  have r27' : reg n11 (27 : Fin 32) = BitVec.ofNat 32 L := by rw [K11 27 (by decide) (by decide) (by decide), D27]
  have steps := c1.trans (c3.trans (c4.trans (.cons e5 (c6.trans (c7.trans (.cons e8 (c9.trans (c10.trans c11))))))))
  obtain ⟨n12, e12, M12, r12, ⟨hb12, s12⟩ | ⟨hb12, s12⟩⟩ := acr_br (acr_re u11) (X.code A11) ac_at_130
    (oT := 0x100) (oF := 0x134) (by decide) (by decide)
  · have := acr_ult hb12
    rw [v11, r27', hck, hL] at this
    refine AcrGo.done (steps.trans (.single e12)) (A11.keep (fun x _ _ => by rw [M12]) fun q _ => r12 q)
      ⟨k, hk1, hk3, .inl ⟨this, ?_⟩⟩
    exact ⟨s12, fun q hq h1 h2 => by rw [r12, K11 q hq h1 h2], by rw [r12, v11], fun x h => by rw [M12, F11 x h],
      by rw [M12, N11]; exact H10⟩
  · have := acr_ult' hb12
    rw [v11, r27', hck, hL] at this
    have e : c + k = L := by omega
    refine AcrGo.done (steps.trans (.single e12)) (A11.keep (fun x _ _ => by rw [M12]) fun q _ => r12 q)
      ⟨k, hk1, hk3, .inr ⟨e, ?_⟩⟩
    rw [← e]
    exact ⟨s12, fun q hq h1 h2 => by rw [r12, K11 q hq h1 h2], by rw [r12, v11], fun x h => by rw [M12, F11 x h],
      by rw [M12, N11]; exact H10⟩

/-- The loop, to its end at 0x134. -/
theorem acr_loop (X : AcrX flash R romBase romCode n0 B Bf M0) {nD : Machine} {r : Word} {Af L : Nat}
    (D8 : reg nD (8 : Fin 32) = BitVec.ofNat 32 Af)
    (D20 : reg nD (20 : Fin 32) = Bf + 0x4000) (D23 : reg nD (23 : Fin 32) = 0x2800)
    (D27 : reg nD (27 : Fin 32) = BitVec.ofNat 32 L) (D40 : memLoad32 nD.mem (acSlot B 0x40) = r)
    (hAL : Af + L < 2 ^ 31) :
    ∀ d c n, L - c ≤ d → c < L → AcrAt B Bf g t n0 n → AcrLp flash B Bf Af c nD n 0x100 →
      AcrGo B Bf g t r n0 n fun n' => AcrLp flash B Bf Af L nD n' 0x134 := by
  intro d
  induction d with
  | zero => intro c n h hc; exact absurd (Nat.lt_of_lt_of_le (Nat.sub_pos_of_lt hc) h) (Nat.lt_irrefl 0)
  | succ d ih =>
    intro c n hd hc A P
    refine (acr_iter X A D8 D20 D23 D27 D40 hAL hc P).bind fun n' A' h => ?_
    obtain ⟨k, hk, -, h⟩ := h
    rcases h with ⟨h1, P'⟩ | ⟨-, P'⟩
    · exact ih (c + k) n' (by omega) h1 A' P'
    · exact AcrGo.done (.refl _) A' P'

end segs

/-! ## 0x134-0x1AA: the digest, and the bundle -/

def acrF1 : List BInstr := [.aluImm .add a0 sp 0xD4, .aluImm .add a1 sp 0x68]

set_option maxRecDepth 100000 in
theorem acrF1_end : blockEnd bootMainClosure0Code 0x134 acrF1 = some 0x138 := by decide

def acrF2 : List BInstr := [.lui a0 0x4000, .lw (8 : Fin 32) sp 0x38]

set_option maxRecDepth 100000 in
theorem acrF2_end : blockEnd bootMainClosure0Code 0x140 acrF2 = some 0x144 := by decide

def acrF3 : List BInstr := [.alu .add a0 (18 : Fin 32) (24 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrF3_end : blockEnd bootMainClosure0Code 0x148 acrF3 = some 0x14C := by decide

def acrF4 : List BInstr := [.lw a1 sp 0x34, .alu .add a2 x0 (8 : Fin 32)]

set_option maxRecDepth 100000 in
theorem acrF4_end : blockEnd bootMainClosure0Code 0x150 acrF4 = some 0x154 := by decide

def acrF5 : List BInstr := [.lw a0 sp 0x30, .alu .add (24 : Fin 32) (24 : Fin 32) a0]

set_option maxRecDepth 100000 in
theorem acrF5_end : blockEnd bootMainClosure0Code 0x15E acrF5 = some 0x162 := by decide

section segs

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {n0 : Machine}
  {B Bf : Word} {M0 : Word → BitVec 8} {g t : Word}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From 0x134 to 0x1AA: the digest into `sp + 0xD4`, and the bundle into
`Bf`. -/
theorem acr_segF (X : AcrX flash R romBase romCode n0 B Bf M0) {n : Machine} (A : AcrAt B Bf g t n0 n)
    (s : St n.mem AC n 0x134 (reg n)) {r slot : Word} {mf : Manifest} {msg : Bytes}
    (hd : decodeManifest (flashBytes flash (acBase slot) 32) = some mf)
    (h18 : reg n (18 : Fin 32) = BitVec.ofNat 32 mf.bundle.offset)
    (h24 : reg n (24 : Fin 32) = BitVec.ofNat 32 (acBase slot))
    (S : AcrSlots n.mem B Bf r slot mf) (H : HasherAt n.mem (acSlot B 0x68) msg) :
    AcrGo B Bf g t r n0 n fun n' => St n'.mem AC n' 0x1AA (reg n') ∧
      (∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (24 : Fin 32) → reg n' q = reg n q) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 mf.bundle.length ∧
      reg n' (24 : Fin 32) = BitVec.ofNat 32 (acBase slot + mf.tuf.offset) ∧
      memBytes n'.mem Bf mf.bundle.length = flashBytes flash (acBase slot + mf.bundle.offset) mf.bundle.length ∧
      memBytes n'.mem (acSlot B 0xD4) 32 = sha256 msg ∧
      ∀ x, AcrFr B Bf x → n'.mem x = n.mem x := by
  have hF := X.F
  have hBL : acBufLen = 0xB954 := rfl
  have hBl := hF.lo
  have hBh := hF.hi
  have dj := X.dj
  have hBw := X.hBw
  obtain ⟨-, -, -, hbl, hio, hbo, hto⟩ := acr_bounds hd
  have hab := acr_base_lt slot
  have z0 := s.zero
  have e30 := acr_at B 0x30 0x30 rfl (by decide)
  have e34 := acr_at B 0x34 0x34 rfl (by decide)
  have e38 := acr_at B 0x38 0x38 rfl (by decide)
  have e68 := acr_at B 0x68 0x68 rfl (by decide)
  have eD4 := acr_at B 0xD4 0xD4 rfl (by decide)
  -- the digest
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x138) acrF1 (X.code A) acrF1_end ⟨trivial, trivial, trivial⟩
  have N1 : n1.mem = n.mem := u1.mem
  have k1 : ∀ q : Fin 32, romKeep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q z0 (by simp only [acrF1]; revert hq; revert q; decide)]
  have v1 : reg n1 a0 = acSlot B 0xD4 ∧ reg n1 a1 = acSlot B 0x68 := by
    simp only [u1.regs]; simp +decide only [runBlock, BInstr.run, acrF1, upd, ↓reduceIte, aluEval]
    rw [A.sp, eD4, e68]
    exact ⟨rfl, rfl⟩
  have A1 := A.keep (fun x _ _ => by rw [N1]) k1
  obtain ⟨n2, c2, s2, k2, hd2, fr2⟩ := acr_finish X A1 (acr_re u1) v1.1 v1.2 (by rw [N1]; exact H)
  have A2 := A1.keep (fun x e1 e2 => fr2 x (by omega) (by omega)) k2
  have G2 : ∀ x, AcrFr B Bf x → n2.mem x = n.mem x := fun x h => by
    obtain ⟨h1, h2, -⟩ := h
    rw [fr2 x h1 (by omega), N1]
  have S2 := X.slots S G2
  have K2 : ∀ q : Fin 32, romKeep q = true → reg n2 q = reg n q := fun q hq => by rw [k2 q hq, k1 q hq]
  -- the bundle's length
  have z2 := s2.zero
  have sp2 : reg n2 sp = B + 0x3A50 := A2.sp
  obtain ⟨n3, c3, u3⟩ := s2.block (off' := 0x144) acrF2 (X.code A2) acrF2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrF2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp2, e38]
    exact (X.al 0x38 (by decide) (by decide)).1)
  have N3 : n3.mem = n2.mem := u3.mem
  have k3 : ∀ q : Fin 32, romKeep q = true → q ≠ (8 : Fin 32) → reg n3 q = reg n2 q := fun q hq h8 => by
    rw [u3.regs, runBlock_reg _ _ _ q z2 (by simp only [acrF2]; revert h8; revert hq; revert q; decide)]
  have v3 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 mf.bundle.length := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acrF2, upd, ↓reduceIte, aluEval]
    rw [sp2, e38, S2.2.2.1]
  have A3 := A2.next (fun x _ _ => by rw [N3]) (k3 2 (by decide) (by decide)) (k3 3 (by decide) (by decide))
    (k3 4 (by decide) (by decide))
  have r40 : ∀ {m : Machine}, m.mem = n2.mem → memLoad32 m.mem (acSlot B 0x40) = r := fun h => by
    rw [h]; exact S2.2.2.2.2.1
  obtain ⟨n4, e4, M4, r4, ⟨hb4, s4⟩ | ⟨hb4, s4⟩⟩ := acr_br (acr_re u3) (X.code A3) ac_at_144 (oT := 0x166)
    (oF := 0x148) (by decide) (by decide)
  · exact AcrGo.fail (c1.trans (c2.trans (c3.trans (.single e4)))) (A3.keep (fun x _ _ => by rw [M4])
      fun q _ => r4 q) (.inl ⟨s4.pc, r40 (by rw [M4, N3])⟩)
  have A4 := A3.keep (fun x _ _ => by rw [M4]) fun q _ => r4 q
  -- the bundle's flash address
  have z4 := s4.zero
  obtain ⟨n5, c5, u5⟩ := s4.block (off' := 0x14C) acrF3 (X.code A4) acrF3_end ⟨trivial, trivial⟩
  have N5 : n5.mem = n4.mem := u5.mem
  have k5 : ∀ q : Fin 32, romKeep q = true → reg n5 q = reg n4 q := fun q hq => by
    rw [u5.regs, runBlock_reg _ _ _ q z4 (by simp only [acrF3]; revert hq; revert q; decide)]
  have K4 : ∀ q : Fin 32, romKeep q = true → q ≠ (8 : Fin 32) → reg n4 q = reg n q := fun q hq h8 => by
    rw [r4, k3 q hq h8, K2 q hq]
  have v5 : reg n5 a0 = BitVec.ofNat 32 (acBase slot + mf.bundle.offset) := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acrF3, upd, ↓reduceIte, aluEval]
    rw [K4 18 (by decide) (by decide), K4 24 (by decide) (by decide), h18, h24, acr_oadd]
  have A5 := A4.keep (fun x _ _ => by rw [N5]) k5
  obtain ⟨n6, e6, M6, r6, ⟨hb6, s6⟩ | ⟨hb6, s6⟩⟩ := acr_br (acr_re u5) (X.code A5) ac_at_14c (oT := 0x166)
    (oF := 0x150) (by decide) (by decide)
  · exact AcrGo.fail (c1.trans (c2.trans (c3.trans (.cons e4 (c5.trans (.single e6)))))) (A5.keep
      (fun x _ _ => by rw [M6]) fun q _ => r6 q) (.inl ⟨s6.pc, r40 (by rw [M6, N5, M4, N3])⟩)
  have A6 := A5.keep (fun x _ _ => by rw [M6]) fun q _ => r6 q
  -- the bundle
  have z6 := s6.zero
  have sp6 : reg n6 sp = B + 0x3A50 := A6.sp
  obtain ⟨n7, c7, u7⟩ := s6.block (off' := 0x154) acrF4 (X.code A6) acrF4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrF4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp6, e34]
    exact (X.al 0x34 (by decide) (by decide)).1)
  have N7 : n7.mem = n6.mem := u7.mem
  have k7 : ∀ q : Fin 32, romKeep q = true → reg n7 q = reg n6 q := fun q hq => by
    rw [u7.regs, runBlock_reg _ _ _ q z6 (by simp only [acrF4]; revert hq; revert q; decide)]
  have v7 : reg n7 a0 = BitVec.ofNat 32 (acBase slot + mf.bundle.offset) ∧ reg n7 a1 = Bf ∧
      reg n7 a2 = BitVec.ofNat 32 mf.bundle.length := by
    simp only [u7.regs]; simp +decide only [runBlock, BInstr.run, acrF4, upd, ↓reduceIte, aluEval]
    rw [sp6, e34, M6, N5, M4, N3, S2.2.1, r6, r6, k5 8 (by decide), r4, v3, v5]
    simp only [acr_zadd]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  have A7 := A6.keep (fun x _ _ => by rw [N7]) k7
  have hbn : (BitVec.ofNat 32 mf.bundle.length).toNat = mf.bundle.length := acr_on (by omega)
  obtain ⟨n8, c8, s8, k8, a08, ok8, fr8⟩ := acr_fread X A7 (o := 0x154) (acr_re u7) ac_at_154 ac_at_158
    (by decide) (by decide) (by decide) v7.1 v7.2.1 v7.2.2 (by rw [hbn]; omega) (by rw [hbn]; omega)
  have A8 := A7.keep (fun x e1 e2 => fr8 x (by omega) (by rw [hbn]; omega)) k8
  have G8 : ∀ x, AcrFr B Bf x → n8.mem x = n2.mem x := fun x h => by
    obtain ⟨h1, -, h3⟩ := h
    rw [fr8 x h1 (by rw [hbn]; omega), N7, M6, N5, M4, N3]
  obtain ⟨n9, e9, M9, r9, ⟨hb9, s9⟩ | ⟨hb9, s9⟩⟩ := acr_br s8 (X.code A8) ac_at_15c (oT := 0x166) (oF := 0x15E)
    (by decide) (by decide)
  · refine AcrGo.fail (c1.trans (c2.trans (c3.trans (.cons e4 (c5.trans (.cons e6 (c7.trans (c8.trans
      (.single e9))))))))) (A8.keep (fun x _ _ => by rw [M9]) fun q _ => r9 q) (.inl ⟨s9.pc, ?_⟩)
    rw [M9, ← r40 (m := n2) rfl]
    exact memLoad32_congr fun j hj => G8 _ (by
      unfold AcrFr; rw [acr_slot_add, X.sl _ (by omega)]; exact ⟨by omega, by omega, by omega⟩)
  have h1 : reg n8 a0 = 1 := by
    rcases a08 with h | h
    · rw [h, s8.zero] at hb9; exact absurd hb9 (by decide)
    · exact h
  have A9 := A8.keep (fun x _ _ => by rw [M9]) fun q _ => r9 q
  -- the TUF part's flash address
  have z9 := s9.zero
  have sp9 : reg n9 sp = B + 0x3A50 := A9.sp
  obtain ⟨n10, c10, u10⟩ := s9.block (off' := 0x162) acrF5 (X.code A9) acrF5_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acrF5]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp9, e30]
    exact (X.al 0x30 (by decide) (by decide)).1)
  have N10 : n10.mem = n9.mem := u10.mem
  have k10 : ∀ q : Fin 32, romKeep q = true → q ≠ (24 : Fin 32) → reg n10 q = reg n9 q := fun q hq h => by
    rw [u10.regs, runBlock_reg _ _ _ q z9 (by simp only [acrF5]; revert h; revert hq; revert q; decide)]
  have m30 : memLoad32 n9.mem (acSlot B 0x30) = BitVec.ofNat 32 mf.tuf.offset := by
    rw [M9, ← S2.1]
    exact memLoad32_congr fun j hj => G8 _ (by
      unfold AcrFr; rw [acr_slot_add, X.sl _ (by omega)]; exact ⟨by omega, by omega, by omega⟩)
  have K9 : ∀ q : Fin 32, romKeep q = true → q ≠ (8 : Fin 32) → reg n9 q = reg n q := fun q hq h8 => by
    rw [r9, k8 q hq, k7 q hq, r6, k5 q hq, K4 q hq h8]
  have v10 : reg n10 a0 = BitVec.ofNat 32 mf.tuf.offset ∧
      reg n10 (24 : Fin 32) = BitVec.ofNat 32 (acBase slot + mf.tuf.offset) := by
    simp only [u10.regs]; simp +decide only [runBlock, BInstr.run, acrF5, upd, ↓reduceIte, aluEval]
    rw [sp9, e30, m30, K9 24 (by decide) (by decide), h24, acr_oadd, Nat.add_comm]
    exact ⟨rfl, rfl⟩
  have A10 := A9.next (fun x _ _ => by rw [N10]) (k10 2 (by decide) (by decide)) (k10 3 (by decide) (by decide)) (k10 4 (by decide) (by decide))
  have steps := c1.trans (c2.trans (c3.trans (.cons e4 (c5.trans (.cons e6 (c7.trans (c8.trans
    (.cons e9 c10))))))))
  obtain ⟨n11, e11, M11, r11, ⟨hb11, s11⟩ | ⟨hb11, s11⟩⟩ := acr_br (acr_re u10) (X.code A10) ac_at_162
    (oT := 0x1AA) (oF := 0x166) (by decide) (by decide)
  · have G11 : ∀ x, AcrFr B Bf x → n11.mem x = n2.mem x := fun x h => by rw [M11, N10, M9, G8 x h]
    refine AcrGo.done (steps.trans (.single e11)) (A10.keep (fun x _ _ => by rw [M11]) fun q _ => r11 q)
      ⟨s11, fun q hq h8 h24' => ?_, ?_, by rw [r11, v10.2], ?_, ?_, fun x h => by rw [G11 x h, G2 x h]⟩
    · rw [r11, k10 q hq h24', K9 q hq h8]
    · rw [r11, k10 8 (by decide) (by decide), r9, k8 8 (by decide), k7 8 (by decide), r6, k5 8 (by decide), r4, v3]
    · rw [M11, N10, M9]
      unfold memBytes flashBytes
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [ok8 h1 i (by rw [hbn]; exact hi), acr_on (by omega)]
    · rw [M11, N10, M9, ← hd2]
      exact memBytes_congr fun i hi => by
        have hO := X.sl 0xD4 (by decide)
        have e : (acSlot B 0xD4 + BitVec.ofNat 32 i).toNat = B.toNat + 0x3A50 + 0xD4 + i := by
          rw [acr_slot_add, X.sl _ (by omega)]; omega
        rw [fr8 _ (by omega) (by rw [hbn, e]; omega), N7, M6, N5, M4, N3]
  · exact AcrGo.fail (steps.trans (.single e11)) (A10.keep (fun x _ _ => by rw [M11]) fun q _ => r11 q)
      (.inl ⟨s11.pc, by
        rw [M11, N10, M9, ← r40 (m := n2) rfl]
        exact memLoad32_congr fun j hj => G8 _ (by
          unfold AcrFr; rw [acr_slot_add, X.sl _ (by omega)]; exact ⟨by omega, by omega, by omega⟩)⟩)

end segs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The read stage**, from 0x32 to 0x1AA: it never halts. -/
theorem acceptRead_pi : AcReadStagePI AcReadEnv := by
  intro flash R romBase romCode rom n B Bf g t r slot level v M0 hE C F sB hBa hBw hR CR hrb hrl hR4 s I h19 h26
    h21 h8 ha3 h24
  have hBL : acBufLen = 0xB954 := rfl
  have hBh := F.hi
  have X : AcrX flash R romBase romCode n B Bf M0 :=
    ⟨rom, hE, C, CR, hrb, hrl, F, acr_nsep sB (by decide) (by decide) (by omega), hBa, hBw, hR, hR4, I.out⟩
  have dj := X.dj
  have A0 : AcrAt B Bf g t n n := ⟨fun _ _ _ => rfl, I.sp, I.gp, I.tp⟩
  suffices K : AcrGo B Bf g t r n n fun n' => n'.pc = AC + BitVec.ofNat 32 0x1AA ∧
      ∃ mf, decodeManifest (flashBytes flash (acBase slot) 32) = some mf ∧ AcReadPost flash B Bf r slot level mf n' by
    obtain ⟨n', st, A', q⟩ := K
    exact ⟨n', st, .inr ⟨X.inv I A', q⟩⟩
  refine (acr_segA X A0 s h19 ha3 h24).bind fun n1 A1 h => ?_
  obtain ⟨s1, k1, r24, hdr⟩ := h
  refine (acr_segB X A1 s1 (by rw [k1 19 (by decide) (by decide), h19]) hdr).bind fun n2 A2 h => ?_
  obtain ⟨mf, hd, s2, k2, r9, FL⟩ := h
  obtain ⟨hio, il1, il2, hbl, hib, hbt, htt⟩ := acr_bounds hd
  have hab := acr_base_lt slot
  have K2 : ∀ q : Fin 32, romKeep q = true → q ≠ (9 : Fin 32) → q ≠ (24 : Fin 32) → reg n2 q = reg n q :=
    fun q hq h9 h24' => by rw [k2 q hq h9, k1 q hq h24']
  refine (acr_segC X A2 s2 hd (by rw [K2 19 (by decide) (by decide) (by decide), h19]) r9
    (by rw [K2 21 (by decide) (by decide) (by decide), h21]) (by rw [k2 24 (by decide) (by decide), r24]) FL).bind
    fun n3 A3 h => ?_
  obtain ⟨s3, k3, w9, w18, w20, w22, w23, w25, w27, m44, hb⟩ := h
  have e3 : ∀ q : Fin 32, romKeep q = true → acrOut q = false → q ≠ (24 : Fin 32) → reg n3 q = reg n q :=
    fun q hq ho h => by
      rw [k3 q hq ho, K2 q hq (fun e => by rw [e] at ho; exact absurd ho (by decide)) h]
  refine (acr_segD X A3 s3 hd (by rw [e3 8 (by decide) (by decide) (by decide), h8])
    (by rw [e3 19 (by decide) (by decide) (by decide), h19]) w20
    (by rw [e3 21 (by decide) (by decide) (by decide), h21]) w23 w27 m44).bind fun n4 A4 h => ?_
  obtain ⟨s4, k4, x8, x19, x20, x23, S4, H4, fr4⟩ := h
  have L4 := acr_loop X x8 x20 x23 (by rw [k4 27 (by decide) (by decide) (by decide) (by decide) (by decide), w27])
    S4.2.2.2.2.1 (by omega) mf.image.length 0 n4 (by omega) (by omega) A4
    ⟨s4, fun q _ _ _ => rfl, by rw [x19]; rfl, fun _ _ => rfl, H4⟩
  refine L4.bind fun n5 A5 P5 => ?_
  have K5 : ∀ q : Fin 32, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) → reg n5 q = reg n3 q := fun q hq a b c d e => by
    rw [P5.keep q hq b d, k4 q hq a b c e]
  have h24' : reg n5 (24 : Fin 32) = BitVec.ofNat 32 (acBase slot) := by
    rw [K5 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k3 24 (by decide) (by decide),
      k2 24 (by decide) (by decide), r24]
  have S5 := X.slots S4 P5.fr
  refine (acr_segF X A5 P5.st hd (by
      rw [K5 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w18]) h24' S5 P5.H).bind
    fun n6 A6 h => ?_
  obtain ⟨s6, k6, y8, y24, mB, mD, fr6⟩ := h
  have S6 := X.slots S5 fr6
  have K6 : ∀ q : Fin 32, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (24 : Fin 32) → reg n6 q = reg n3 q := fun q hq a b c d e f => by
    rw [k6 q hq a f, K5 q hq a b c d e]
  refine AcrGo.done (.refl _) A6 ⟨s6.pc, mf, hd, S6.2.1, S6.2.2.1, S6.2.2.2.1, S6.2.2.2.2.1, S6.2.2.2.2.2, y8,
    by rw [K6 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w9],
    by rw [k6 20 (by decide) (by decide) (by decide), P5.keep 20 (by decide) (by decide) (by decide), x20],
    by rw [K6 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w22], y24,
    by rw [K6 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w25],
    by rw [K6 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      e3 26 (by decide) (by decide) (by decide), h26],
    by rw [K6 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w27],
    by omega, ?_, mB, mD⟩
  unfold memBytes flashBytes
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hBo : (Bf + 0xB840 : Word).toNat = Bf.toNat + 0xB840 := X.bf 0xB840 (by decide)
  have e : (Bf + 0xB840 + BitVec.ofNat 32 i).toNat = Bf.toNat + 0xB840 + i := by
    rw [acr_tn _ _ (by rw [hBo]; omega), hBo]
  have hx : AcrFr B Bf (Bf + 0xB840 + BitVec.ofNat 32 i) := by unfold AcrFr; rw [e]; exact ⟨by omega, by omega, by omega⟩
  rw [fr6 _ hx, P5.fr _ hx, fr4 _ (by rw [e]; omega), hb i hi]

/-- **The read stage**, from 0x32 to 0x1AA. -/
theorem acceptRead : AcReadStage AcReadEnv := acceptRead_pi.acStage

end C3.RV32.Ac
