import C3BootProofs.Proofs.DerAlgorithm
import C3BootProofs.Proofs.SliceEq

/-!
# `lists_oid`, as compiled

`lists_oid` walks a DER list of `SEQUENCE`s with a reader on its own stack.
For each element, the proved `Der::sequence` reads the `SEQUENCE`, whose
reader `lists_oid` rebuilds with an 11-byte `memcpy`, the proved `Der::oid`
reads the `SEQUENCE`'s first element, and the proved `[u8]` comparison checks
that OID against the caller's. It returns `Ok(true)` at the first match and
`Ok(false)` when the list runs out.
-/

namespace C3.RV32

open C3.Image

abbrev loPs : List (Fin 32 × Word) :=
  [(ra, 0x5C), ((8 : Fin 32), 0x58), ((9 : Fin 32), 0x54), ((18 : Fin 32), 0x50), ((19 : Fin 32), 0x4C),
   ((20 : Fin 32), 0x48), ((21 : Fin 32), 0x44)]

/-- The instructions from 0x10 to 0x24: `Der::new` on the stack, and the
`memcpy` operands the loop keeps in `s2` and `s3`. -/
def loNew : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a3, .alu .add (21 : Fin 32) x0 a2, .sw sp a0 0xC, .sw sp a1 0x10, .sw sp a0 0x14,
   .sw sp a1 0x18, .aluImm .add (18 : Fin 32) sp 0x39, .aluImm .add (19 : Fin 32) sp 0x29]

section
set_option maxRecDepth 20000
theorem lo_at_0 : fetchRel listsOidCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem lo_at_2 : fetchRel listsOidCode 0x2 = some (.store .sw sp ra 0x5C, 2) := by decide
theorem lo_at_4 : fetchRel listsOidCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x58, 2) := by decide
theorem lo_at_6 : fetchRel listsOidCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x54, 2) := by decide
theorem lo_at_8 : fetchRel listsOidCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x50, 2) := by decide
theorem lo_at_a : fetchRel listsOidCode 0xA = some (.store .sw sp (19 : Fin 32) 0x4C, 2) := by decide
theorem lo_at_c : fetchRel listsOidCode 0xC = some (.store .sw sp (20 : Fin 32) 0x48, 2) := by decide
theorem lo_at_e : fetchRel listsOidCode 0xE = some (.store .sw sp (21 : Fin 32) 0x44, 2) := by decide
theorem lo_at_10 : fetchRel listsOidCode 0x10 = some (.alu .add (20 : Fin 32) x0 a3, 2) := by decide
theorem lo_at_12 : fetchRel listsOidCode 0x12 = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem lo_at_14 : fetchRel listsOidCode 0x14 = some (.store .sw sp a0 0xC, 2) := by decide
theorem lo_at_16 : fetchRel listsOidCode 0x16 = some (.store .sw sp a1 0x10, 2) := by decide
theorem lo_at_18 : fetchRel listsOidCode 0x18 = some (.store .sw sp a0 0x14, 2) := by decide
theorem lo_at_1a : fetchRel listsOidCode 0x1A = some (.store .sw sp a1 0x18, 2) := by decide
theorem lo_at_1c : fetchRel listsOidCode 0x1C = some (.aluImm .add (18 : Fin 32) sp 0x39, 4) := by decide
theorem lo_at_20 : fetchRel listsOidCode 0x20 = some (.aluImm .add (19 : Fin 32) sp 0x29, 4) := by decide
theorem lo_at_24 : fetchRel listsOidCode 0x24 = some (.branch .beq a1 x0 0x4E, 2) := by decide
theorem lo_at_26 : fetchRel listsOidCode 0x26 = some (.aluImm .add a0 sp 0x34, 2) := by decide
theorem lo_at_28 : fetchRel listsOidCode 0x28 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem lo_at_2a : fetchRel listsOidCode 0x2A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem lo_at_2e : fetchRel listsOidCode 0x2E = some (.jalr ra ra 0x5A0, 4) := by decide
theorem lo_at_32 : fetchRel listsOidCode 0x32 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem lo_at_34 : fetchRel listsOidCode 0x34 = some (.load .lbu (8 : Fin 32) sp 0x38, 4) := by decide
theorem lo_at_38 : fetchRel listsOidCode 0x38 = some (.branch .beq (9 : Fin 32) x0 0x44, 2) := by decide
theorem lo_at_3a : fetchRel listsOidCode 0x3A = some (.aluImm .add a2 x0 0xB, 2) := by decide
theorem lo_at_3c : fetchRel listsOidCode 0x3C = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem lo_at_3e : fetchRel listsOidCode 0x3E = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem lo_at_40 : fetchRel listsOidCode 0x40 = some (.auipc ra 0xC000, 4) := by decide
theorem lo_at_44 : fetchRel listsOidCode 0x44 = some (.jalr ra ra 0xFFFFFF0E, 4) := by decide
theorem lo_at_48 : fetchRel listsOidCode 0x48 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem lo_at_4a : fetchRel listsOidCode 0x4A = some (.store .sb sp (8 : Fin 32) 0x28, 4) := by decide
theorem lo_at_4e : fetchRel listsOidCode 0x4E = some (.aluImm .add a0 sp 0x1C, 2) := by decide
theorem lo_at_50 : fetchRel listsOidCode 0x50 = some (.aluImm .add a1 sp 0x24, 2) := by decide
theorem lo_at_52 : fetchRel listsOidCode 0x52 = some (.auipc ra 0x0, 4) := by decide
theorem lo_at_56 : fetchRel listsOidCode 0x56 = some (.jalr ra ra 0xFFFFFE48, 4) := by decide
theorem lo_at_5a : fetchRel listsOidCode 0x5A = some (.load .lw a0 sp 0x1C, 2) := by decide
theorem lo_at_5c : fetchRel listsOidCode 0x5C = some (.branch .beq a0 x0 0x1C, 2) := by decide
theorem lo_at_5e : fetchRel listsOidCode 0x5E = some (.load .lw a1 sp 0x20, 2) := by decide
theorem lo_at_60 : fetchRel listsOidCode 0x60 = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem lo_at_62 : fetchRel listsOidCode 0x62 = some (.alu .add a3 x0 (20 : Fin 32), 2) := by decide
theorem lo_at_64 : fetchRel listsOidCode 0x64 = some (.auipc ra 0x0, 4) := by decide
theorem lo_at_68 : fetchRel listsOidCode 0x68 = some (.jalr ra ra 0xFFFFFDDA, 4) := by decide
theorem lo_at_6c : fetchRel listsOidCode 0x6C = some (.branch .bne a0 x0 0x14, 2) := by decide
theorem lo_at_6e : fetchRel listsOidCode 0x6E = some (.load .lw a1 sp 0x18, 2) := by decide
theorem lo_at_70 : fetchRel listsOidCode 0x70 = some (.branch .bne a1 x0 0xFFFFFFB6, 2) := by decide
theorem lo_at_72 : fetchRel listsOidCode 0x72 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem lo_at_74 : fetchRel listsOidCode 0x74 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem lo_at_76 : fetchRel listsOidCode 0x76 = some (.jal x0 0xE, 2) := by decide
theorem lo_at_78 : fetchRel listsOidCode 0x78 = some (.load .lbu (8 : Fin 32) sp 0x20, 4) := by decide
theorem lo_at_7c : fetchRel listsOidCode 0x7C = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem lo_at_7e : fetchRel listsOidCode 0x7E = some (.jal x0 0x6, 2) := by decide
theorem lo_at_80 : fetchRel listsOidCode 0x80 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem lo_at_82 : fetchRel listsOidCode 0x82 = some (.aluImm .add (8 : Fin 32) x0 0x1, 2) := by decide
theorem lo_at_84 : fetchRel listsOidCode 0x84 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem lo_at_86 : fetchRel listsOidCode 0x86 = some (.load .lw ra sp 0x5C, 2) := by decide
theorem lo_at_88 : fetchRel listsOidCode 0x88 = some (.load .lw (8 : Fin 32) sp 0x58, 2) := by decide
theorem lo_at_8a : fetchRel listsOidCode 0x8A = some (.load .lw (9 : Fin 32) sp 0x54, 2) := by decide
theorem lo_at_8c : fetchRel listsOidCode 0x8C = some (.load .lw (18 : Fin 32) sp 0x50, 2) := by decide
theorem lo_at_8e : fetchRel listsOidCode 0x8E = some (.load .lw (19 : Fin 32) sp 0x4C, 2) := by decide
theorem lo_at_90 : fetchRel listsOidCode 0x90 = some (.load .lw (20 : Fin 32) sp 0x48, 2) := by decide
theorem lo_at_92 : fetchRel listsOidCode 0x92 = some (.load .lw (21 : Fin 32) sp 0x44, 2) := by decide
theorem lo_at_94 : fetchRel listsOidCode 0x94 = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem lo_at_96 : fetchRel listsOidCode 0x96 = some (.jalr x0 ra 0x0, 2) := by decide
theorem loSave_end : blockEnd listsOidCode 2 (saveBlock loPs) = some 0x10 := by decide
theorem loRestore_end : blockEnd listsOidCode 0x86 (restoreBlock loPs) = some 0x94 := by decide
theorem loNew_end : blockEnd listsOidCode 0x10 loNew = some 0x24 := by decide
end

theorem derTlv_header {L : Bytes} {t : DerTlv} (h : derTlv L = .ok t) : 2 ≤ t.header := by
  match L with
  | [] => simp only [derTlv] at h; cases h
  | [tag] =>
    simp only [derTlv] at h
    by_cases h1 : tag % 32 = 31
    · simp only [h1, ↓reduceIte] at h; cases h
    · simp only [h1, ↓reduceIte] at h; cases h
  | tag :: first :: afterLen =>
    simp only [derTlv] at h
    by_cases h1 : tag % 32 = 31
    · simp only [h1, ↓reduceIte] at h; cases h
    simp only [h1, ↓reduceIte] at h
    by_cases h2 : first < 0x80
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : afterLen.length < first
      · simp only [h3, ↓reduceIte] at h; cases h
      · simp only [h3, ↓reduceIte] at h; cases h; exact Nat.le_refl _
    simp only [h2, ↓reduceIte] at h
    by_cases h3 : first % 128 = 0 ∨ 4 < first % 128
    · simp only [h3, ↓reduceIte] at h; cases h
    simp only [h3, ↓reduceIte] at h
    clear h3
    by_cases h4 : afterLen.length < first % 128
    · simp only [h4, ↓reduceIte] at h; cases h
    simp only [h4, ↓reduceIte] at h
    by_cases h5 : afterLen.head? = some 0
    · simp only [h5, ↓reduceIte] at h; cases h
    simp only [h5, ↓reduceIte] at h
    cases hl : derLongLen 0 (afterLen.take (first % 128)) with
    | error e => simp only [hl] at h; cases h
    | ok len =>
      simp only [hl] at h
      by_cases h6 : len < 0x80
      · simp only [h6, ↓reduceIte] at h; cases h
      simp only [h6, ↓reduceIte] at h
      by_cases h7 : afterLen.length - first % 128 < len
      · simp only [h7, ↓reduceIte] at h; cases h
      simp only [h7, ↓reduceIte] at h; cases h; exact Nat.le_add_right _ _

theorem derElement_header {tag : Nat} {L : Bytes} {t : DerTlv} (h : derElement tag L = .ok t) : 2 ≤ t.header := by
  unfold derElement at h
  split at h
  · cases h
  · split at h
    · exact derTlv_header h
    · cases h

/-- `lists_oid`'s loop with `k` passes left, over the `n` unread bytes at
`p`: whether one of their `SEQUENCE`s starts with the OID `oid`, or the
error byte of the first element that doesn't parse. `k` passes suffice
when `k` is at least `n`, as each pass reads at least two bytes. -/
def listsOidLoop (M : Word → BitVec 8) (oid : Bytes) : Nat → Word → Nat → Except (BitVec 8) Bool
  | 0, _, _ => .ok false
  | k + 1, p, n =>
    if n = 0 then .ok false
    else
      match derElement 0x30 (memBytes M p n) with
      | .error e => .error (derErrByte e)
      | .ok t =>
        match derOid (memBytes M (p + BitVec.ofNat 32 t.header) t.len) with
        | .error e => .error (derErrByte e)
        | .ok o =>
          if memBytes M (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header) o.len = oid then .ok true
          else listsOidLoop M oid k (p + BitVec.ofNat 32 (t.header + t.len)) (n - (t.header + t.len))

/-- `lists_oid`'s result for the `n` bytes at `p` and the OID `oid`. -/
def listsOidOf (M : Word → BitVec 8) (p : Word) (n : Nat) (oid : Bytes) : Except (BitVec 8) Bool :=
  listsOidLoop M oid n p n

theorem listsOidLoop_zero (M : Word → BitVec 8) (oid : Bytes) (k : Nat) (p : Word) :
    listsOidLoop M oid k p 0 = .ok false := by
  cases k <;> rfl

/-- What `lists_oid` returning from `m` to `retAddr` guarantees: `sp` back
at `sp0`, the callee-saved registers kept, memory changed only in the
0x80 bytes at `G`, and the `Result<bool, Error>` for `R` in `a0` and `a1`. -/
def LOResult (m : Machine) (retAddr sp0 G : Word) (R : Except (BitVec 8) Bool) : Prop :=
  ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
    (∀ r, r.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' r = reg m r) ∧
    (∀ x, Sep G 0x80 x 1 → m'.mem x = m.mem x) ∧
    match R with
    | .error b => reg m' a0 = 1 ∧ reg m' a1 = b.zeroExtend 32
    | .ok v => reg m' a0 = 0 ∧ reg m' a1 = if v then 1 else 0

/-- Where `lists_oid` runs: its code and its callees', the 0x80 bytes of
stack below `sp0`, the list's `n` bytes at `p`, and the OID's `ql` bytes at
`q`, apart from what each must not touch. -/
structure LOEnv (M : Word → BitVec 8) (P sp0 p q : Word) (n ql : Nat) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P listsOidCode
  seq : CodeIn M (P + 0xFFFFF5CA) derSequenceCode
  nst : CodeIn M (P + 0xFFFFF842) derNestedCode
  elem : CodeIn M (P + 0xFFFFF762) derElementCode
  tlv : CodeIn M (P + 0xFFFFF788) derTlvCode
  oid : CodeIn M (P + 0xFFFFFE9A) derOidCode
  seqq : CodeIn M (P + 0xFFFFFE3E) sliceEqCode
  esl : CodeIn M (P + 0xFFFFF5B4) equalSameLengthCode
  cmp : CodeIn M (P + 0xBEC6) memcmpCode
  mcs : CodeIn M (P + 0xBF4E) memcpyStubCode
  mcb : CodeIn M (P + 0xBF56) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x80 ≤ sp0.toNat
  hp : 0 < p.toNat
  hpn : p.toNat + n < 2 ^ 32
  hql : ql < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF80) 0x80 P listsOidCode.length
  sGQ : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFF5CA) derSequenceCode.length
  sGN : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFF842) derNestedCode.length
  sGE : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFF762) derElementCode.length
  sGT : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFF788) derTlvCode.length
  sGO : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFFE9A) derOidCode.length
  sGS : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFFE3E) sliceEqCode.length
  sGL : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFF5B4) equalSameLengthCode.length
  sGM : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xBEC6) memcmpCode.length
  sGU : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xBF4E) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xBF56) memcpyBodyCode.length
  sRG : Sep p n (sp0 + 0xFFFFFF80) 0x80
  sQG : Sep q ql (sp0 + 0xFFFFFF80) 0x80

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `lists_oid`**: with the list's `n` bytes at `p` and the
OID's `ql` bytes at `q`, it returns `listsOidOf` of them as a
`Result<bool, Error>` in `a0` and `a1`, and writes only its stack. -/
theorem listsOid_correct (m : Machine) {P sp0 p q retAddr : Word} {n ql : Nat}
    (env : LOEnv m.mem P sp0 p q n ql) (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = p)
    (ha1 : reg m a1 = BitVec.ofNat 32 n) (ha2 : reg m a2 = q) (ha3 : reg m a3 = BitVec.ofNat 32 ql)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' r = reg m r) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → m'.mem x = m.mem x) ∧
      match listsOidOf m.mem p n (memBytes m.mem q ql) with
      | .error b => reg m' a0 = 1 ∧ reg m' a1 = b.zeroExtend 32
      | .ok v => reg m' a0 = 0 ∧ reg m' a1 = if v then 1 else 0 := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF80 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFA0 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGQ := env.sGQ; have sGN := env.sGN; have sGE := env.sGE; have sGT := env.sGT
  have sGO := env.sGO; have sGS := env.sGS; have sGL := env.sGL; have sGM := env.sGM; have sGU := env.sGU
  have sGB := env.sGB; have sRG := env.sRG; have sQG := env.sQG
  rw [hG] at sGC sGQ sGN sGE sGT sGO sGS sGL sGM sGU sGB sRG sQG ⊢
  have hn : n < 2 ^ 32 := by have := env.hpn; omega
  have hGF : G + BitVec.ofNat 32 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF80) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x20) (by decide)
  have hGw : G.toNat + 0x80 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF80 : Word).toNat = 4294967168 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x20 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x60 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by rw [← hGF, add_ofNat_assoc]
  have eNF : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eSc : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x10 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eS4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x1C := by rw [← hGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x80 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x80 → d + k ≤ 0x80 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have sFk : ∀ {b : Word} {l : Nat} (c k : Nat), c + k ≤ 0x60 → Sep G 0x80 b l →
      Sep (F + BitVec.ofNat 32 c) k b l := fun c k h hs => by rw [eFk]; exact hs.sub (by omega)
  have sepF : ∀ {c n k : Nat}, c + n ≤ k ∨ k + 1 ≤ c → c + n ≤ 0x60 → k < 0x60 →
      Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 k) 1 := fun h h1 h2 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x80 b code'.length → (∀ x, Sep G 0x80 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have slotC : ∀ (o : Word), 0x44 ≤ o.toNat → o.toNat + 4 ≤ 0x60 → ∀ {b : Word} {l : Nat}, Sep G 0x80 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x20 + o.toNat) (l := 4) (by omega)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod lo_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock loPs) u1 env.cod loSave_end (saveBlock_ok _ loPs _ fun p hp => by
    rw [sp1]
    simp only [loPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0)) loPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep G 0x80 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside loPs fun p hp => by
      simp only [loPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact slotC _ (by decide) (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ loPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [loPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P listsOidCode := cIn env.cod sGC frSv
  have hpsp : ∀ p ∈ loPs, p.1 ≠ sp := by decide
  -- the result in `a1`, and the epilogue, from 0x84
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m n → St Mx P n 0x84 (reg n) →
      CodeIn Mx P listsOidCode →
      (∀ k, 0x44 ≤ k → k < 0x60 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg n sp = F →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧ reg n' a0 = reg n a0 ∧
        reg n' a1 = reg n 8 ∧
        ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q := by
    intro Mx n S st hc hsl rsp kq
    obtain ⟨n0, d0, u0⟩ := st.alu hc lo_at_84 (off' := 0x86) (by decide)
    have rsp0 : upd (reg n) a1 (aluEval .add (reg n 0) (reg n 8)) sp = F := by
      rw [upd_ne (by decide) (by decide), rsp]
    have slotW : ∀ r o, (r, o) ∈ loPs → memLoad32 Mx (F + o) = reg m r := fun r o h => by
      have ho : 0x44 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x60 := by
        simp only [loPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [← hslv r o h]
      apply memLoad32_congr; intro j hj
      rw [← ofNat_toNat_self o, add_ofNat_assoc, hsl _ (by omega) (by omega)]
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock loPs) u0 hc loRestore_end
      (restoreBlock_ok Mx F loPs _ rsp0 hpsp fun q hq => by
        simp only [loPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mx F loPs _ rsp0 hpsp] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc lo_at_94 (off' := 0x96) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc lo_at_96
    have rsp1 : restoreRegs Mx F (upd (reg n) a1 (aluEval .add (reg n 0) (reg n 8))) loPs sp = F := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp0
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs Mx F f ps q = f q := by
      intro f ps q h0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
    have hreg : ∀ r o, (r, o) ∈ loPs →
        restoreRegs Mx F (upd (reg n) a1 (aluEval .add (reg n 0) (reg n 8))) loPs r = reg m r := fun r o hm => by
      simp only [loPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact slotW _ _ (by decide)
    have ra1 : restoreRegs Mx F (upd (reg n) a1 (aluEval .add (reg n 0) (reg n 8))) loPs a1 = reg n 8 := by
      rw [rr _ _ a1 (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; exact zw _
    have ra0 : restoreRegs Mx F (upd (reg n) a1 (aluEval .add (reg n 0) (reg n 8))) loPs a0 = reg n a0 := by
      rw [rr _ _ a0 (by decide) (by decide), upd_ne (by decide) (by decide)]
    refine ⟨n3, S.trans (.cons d0 (c1.trans (.cons d2 (.single d3)))), ?_, mem3, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x5C (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; exact ra0
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; exact ra1
    · rw [regs3]
      have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ (q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
            q ≠ a1 ∧ (∀ p ∈ loPs, p.1 ≠ q)) := by decide
      rcases key q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, ha, hps⟩
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x5C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x58 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x54 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x50 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x4C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x48 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x44 (by decide)
      · rw [upd_ne h0 hs, rr _ _ q h0 hps, upd_ne h0 ha]; exact kq q h1
  have done : ∀ {Mx : Word → BitVec 8} {nm : Machine} (R : Except (BitVec 8) Bool), Steps m nm →
      St Mx P nm 0x84 (reg nm) → CodeIn Mx P listsOidCode → (∀ x, Sep G 0x80 x 1 → Mx x = m.mem x) →
      (∀ k, 0x44 ≤ k → k < 0x60 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg nm sp = F →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) →
      (match R with
        | .error b => reg nm a0 = 1 ∧ reg nm 8 = b.zeroExtend 32
        | .ok v => reg nm a0 = 0 ∧ reg nm 8 = if v then 1 else 0) →
      LOResult m retAddr sp0 G R := by
    intro Mx nm R S st hc hM hsl rsp kq hR
    obtain ⟨n', S', pc', mem', sp', a0', a1', k'⟩ := fin S st hc hsl rsp kq
    refine ⟨n', S', pc', sp', k', fun x hx => by rw [mem', hM x hx], ?_⟩
    cases R with
    | error b => obtain ⟨h1, h2⟩ := hR; exact ⟨by rw [a0', h1], by rw [a1', h2]⟩
    | ok v => obtain ⟨h1, h2⟩ := hR; exact ⟨by rw [a0', h1], by rw [a1', h2]⟩
  -- `Err(b)` from 0x7C, with the error byte in `s0`
  have errExit : ∀ {Mx : Word → BitVec 8} {nm : Machine} {b : BitVec 8}, Steps m nm →
      St Mx P nm 0x7C (reg nm) → CodeIn Mx P listsOidCode → (∀ x, Sep G 0x80 x 1 → Mx x = m.mem x) →
      (∀ k, 0x44 ≤ k → k < 0x60 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg nm sp = F →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) → reg nm 8 = b.zeroExtend 32 →
      LOResult m retAddr sp0 G (.error b) := by
    intro Mx nm b S st hc hM hsl rsp kq h8
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc lo_at_7c (off' := 0x7E) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.jump hc lo_at_7e (off' := 0x84) (by decide) (by
      rw [u1.pc, show P + BitVec.ofNat 32 0x7E + 0x6 = P + BitVec.ofNat 32 0x84 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x84 (by decide)))
    exact done (.error b) (S.trans (.cons d1 (.single d2))) u2.self hc hM hsl
      (by rw [u2.regs, upd_ne (by decide) (by decide), rsp])
      (fun q hq => by
        rw [u2.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact kq q hq)
      ⟨by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl,
        by rw [u2.regs, upd_ne (by decide) (by decide), h8]⟩
  -- `Ok(false)` from 0x72
  have falseExit : ∀ {Mx : Word → BitVec 8} {nm : Machine}, Steps m nm →
      St Mx P nm 0x72 (reg nm) → CodeIn Mx P listsOidCode → (∀ x, Sep G 0x80 x 1 → Mx x = m.mem x) →
      (∀ k, 0x44 ≤ k → k < 0x60 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg nm sp = F →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) →
      LOResult m retAddr sp0 G (.ok false) := by
    intro Mx nm S st hc hM hsl rsp kq
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc lo_at_72 (off' := 0x74) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc lo_at_74 (off' := 0x76) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.jump hc lo_at_76 (off' := 0x84) (by decide) (by
      rw [u2.pc, show P + BitVec.ofNat 32 0x76 + 0xE = P + BitVec.ofNat 32 0x84 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x84 (by decide)))
    have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ 8 → reg n3 q = reg nm q := fun q hv h0 h8 => by
      rw [u3.regs, upd_ne hv h0, u1.regs, upd_ne hv h8]
    exact done (.ok false) (S.trans (.cons d1 (.cons d2 (.single d3)))) u3.self hc hM hsl
      (by rw [k3 sp (by decide) (by decide) (by decide), rsp])
      (fun q hq => by
        rw [k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        exact kq q hq)
      ⟨by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.self.zero]; rfl,
        by rw [u3.regs, upd_ne (by decide) (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
           rw [st.zero]; rfl⟩
  -- `Ok(true)` from 0x80
  have trueExit : ∀ {Mx : Word → BitVec 8} {nm : Machine}, Steps m nm →
      St Mx P nm 0x80 (reg nm) → CodeIn Mx P listsOidCode → (∀ x, Sep G 0x80 x 1 → Mx x = m.mem x) →
      (∀ k, 0x44 ≤ k → k < 0x60 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg nm sp = F →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) →
      LOResult m retAddr sp0 G (.ok true) := by
    intro Mx nm S st hc hM hsl rsp kq
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc lo_at_80 (off' := 0x82) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc lo_at_82 (off' := 0x84) (by decide)
    have k2 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ 8 → reg n2 q = reg nm q := fun q hv h0 h8 => by
      rw [u2.regs, upd_ne hv h8, u1.regs, upd_ne hv h0]
    exact done (.ok true) (S.trans (.cons d1 (.single d2))) u2.self hc hM hsl
      (by rw [k2 sp (by decide) (by decide) (by decide), rsp])
      (fun q hq => by
        rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        exact kq q hq)
      ⟨by rw [u2.regs, upd_ne (by decide) (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [st.zero]; rfl,
        by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.self.zero]; rfl⟩
  -- `Der::new` on the stack at `sp + 0xC`
  obtain ⟨m3, c3, u3⟩ := St.block loNew u2.self hcS loNew_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, loNew, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp2]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      first | exact aligned_add hFa (by decide) | exact sFk _ 4 (by decide) sGC)
  simp only [runBlock, BInstr.run, loNew] at u3
  simp +decide only [upd_app, ↓reduceIte] at u3
  rw [sp2, r2 a0 (by decide), r2 a1 (by decide), ha0, ha1] at u3
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 (memStore32 (memStore32 Msv (F + 0xC) p) (F + 0x10)
      (BitVec.ofNat 32 n)) (F + 0x14) p) (F + 0x18) (BitVec.ofNat 32 n) = M3 := ⟨_, rfl⟩
  rw [hM3] at u3
  have M3k : ∀ k, (k + 1 ≤ 0xC ∨ 0x1C ≤ k) → k < 0x60 → M3 (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      rw [← hM3, memStore32_get_sep (a := F + 0x18) (sepF (c := 0x18) (n := 4) (by omega) (by decide) h2),
        memStore32_get_sep (a := F + 0x14) (sepF (c := 0x14) (n := 4) (by omega) (by decide) h2),
        memStore32_get_sep (a := F + 0x10) (sepF (c := 0x10) (n := 4) (by omega) (by decide) h2),
        memStore32_get_sep (a := F + 0xC) (sepF (c := 0xC) (n := 4) (by omega) (by decide) h2)]
  have M3G : ∀ x, Sep G 0x80 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (a := F + 0x18) (sFk 0x18 4 (by decide) hx),
      memStore32_get_sep (a := F + 0x14) (sFk 0x14 4 (by decide) hx),
      memStore32_get_sep (a := F + 0x10) (sFk 0x10 4 (by decide) hx),
      memStore32_get_sep (a := F + 0xC) (sFk 0xC 4 (by decide) hx), frSv x hx]
  have l14 : memLoad32 M3 (F + 0x14) = p := by
    rw [← hM3, memLoad32_store32_sep (a := F + 0x18) (b := F + 0x14)
      (sep_offsets F (c := 0x18) (n := 4) (d := 0x14) (k := 4) (.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  have l18 : memLoad32 M3 (F + 0x18) = BitVec.ofNat 32 n := by rw [← hM3, memLoad32_store32_same]
  have hc3 : CodeIn M3 P listsOidCode := cIn env.cod sGC M3G
  have k3 : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 10, 11, 22, 23, 24, 25, 26, 27] → reg m3 q = reg m q := fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ 18 ∧ q ≠ 19 ∧ q ≠ 20 ∧ q ≠ 21 ∧ q ≠ sp := by revert hq; revert q; decide
    rw [u3.regs, upd_ne h.1 h.2.2.1, upd_ne h.1 h.2.1, upd_ne h.1 h.2.2.2.2.1, upd_ne h.1 h.2.2.2.1, r2 q h.2.2.2.2.2]
  have sp3 : reg m3 sp = F := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp2
  have a1_3 : reg m3 a1 = BitVec.ofNat 32 n := by rw [k3 a1 (by decide), ha1]
  have s18_3 : reg m3 18 = F + 0x39 := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rfl
  have s19_3 : reg m3 19 = F + 0x29 := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rfl
  have s20_3 : reg m3 20 = BitVec.ofNat 32 ql := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a3 (by decide), ha3, u2.self.zero]; exact zw _
  have s21_3 : reg m3 21 = q := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a2 (by decide), ha2]; exact zw _
  have S3 : Steps m m3 := .cons d1 (c2.trans c3)
  have slot3 : ∀ k, 0x44 ≤ k → k < 0x60 → M3 (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => M3k k (.inr (by omega)) h2
  have Km3 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m3 q = reg m q := fun q hq =>
    k3 q (by revert hq; revert q; decide)
  -- a call to `memcpy` through its stub
  have mcCall : ∀ {Mx : Word → BitVec 8} {n : Machine} {o : Nat} {imm oo dst src : Word} {N : Nat},
      St Mx P n o (reg n) → CodeIn Mx P listsOidCode →
      fetchRel listsOidCode o = some (.auipc ra imm, 4) →
      fetchRel listsOidCode (o + 4) = some (.jalr ra ra oo, 4) →
      P + BitVec.ofNat 32 o + imm + oo = P + 0xBF4E → (o + 8) % 2 = 0 →
      CodeIn Mx (P + 0xBF4E) memcpyStubCode → CodeIn Mx (P + 0xBF56) memcpyBodyCode →
      reg n sp = F → reg n a0 = dst → reg n a1 = src → reg n a2 = BitVec.ofNat 32 N →
      Sep dst N (P + 0xBF56) memcpyBodyCode.length → Sep dst N (G + BitVec.ofNat 32 0x10) 16 →
      Sep src N (G + BitVec.ofNat 32 0x10) 16 → Sep dst N src N → dst.toNat + N < 2 ^ 32 → src.toNat + N < 2 ^ 32 →
      ∃ n', Steps n n' ∧ St n'.mem P n' (o + 8) (reg n') ∧ reg n' sp = F ∧
        (∀ x, Sep (G + BitVec.ofNat 32 0x10) 16 x 1 → n'.mem x = copyBytes Mx dst src N x) ∧
        ∀ r, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg n r := by
    intro Mx n o imm oo dst src N st hc h1 h2 hb ho hcs hcb rsp ra0 ra1 ra2 sDB sDF sSF sDS hdw hsw
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa hc h1 h2 (cb := P + 0xBF4E) hb (even_at P env.hP 0xBF4E (by decide))
    have r1 := PEnv.reg1 regs1 st.zero
    have sp1 : reg n1 sp = F := by rw [r1 sp (by decide), rsp]
    obtain ⟨n2, c2, pc2, sp2', a02, mem2, k2⟩ := memcpy_correct n1 (P + 0xBF4E) (P + BitVec.ofNat 32 (o + 8))
      dst src N (by show CodeIn n1.mem _ _; rw [mem1]; exact hcs) (even_at P env.hP 0xBF4E (by decide)) pc1
      (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1]) (by rw [r1 a2 (by decide), ra2])
      (by rw [regs1]; simp +decide [upd]) (even_clear _ (even_at P env.hP (o + 8) ho))
      (by
        rw [mem1, sp1, eSc, show P + 0xBF4E + 8 = P + 0xBF56 by rw [BitVec.add_assoc]; rfl]
        exact ⟨hcb, sDB, (sGB.sub (c := 0x10) (l := 16) (by decide)), sDF, sSF, sDS,
          aligned_add hGa (k := 0x10) (by decide), by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hdw, hsw⟩)
    refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2', sp1], fun x hx => ?_, fun r hr => ?_⟩
    · rw [mem2 x (by rw [sp1, eSc]; exact hx), mem1]
    · obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15⟩ :=
        (by decide : ∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ a6 ∧ r ≠ a7 ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ (7 : Fin 32) ∧
          r ≠ (28 : Fin 32) ∧ r ≠ (29 : Fin 32) ∧ r ≠ (30 : Fin 32) ∧ r ≠ sp ∧ r ≠ ra) r hr
      rw [k2 r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14, r1 r q15]
  -- one pass of the loop, from 0x26
  have iter : ∀ k, ∀ {Mx : Word → BitVec 8} {nm : Machine} {p' : Word} {n' : Nat}, Steps m nm →
      St Mx P nm 0x26 (reg nm) → (∀ x, Sep G 0x80 x 1 → Mx x = m.mem x) →
      (∀ k, 0x44 ≤ k → k < 0x60 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) →
      memLoad32 Mx (F + 0x14) = p' → memLoad32 Mx (F + 0x18) = BitVec.ofNat 32 n' → 0 < n' → n' ≤ k →
      Sep p' n' G 0x80 → 0 < p'.toNat → p'.toNat + n' < 2 ^ 32 →
      reg nm sp = F → reg nm 18 = F + 0x39 → reg nm 19 = F + 0x29 → reg nm 20 = BitVec.ofNat 32 ql →
      reg nm 21 = q → (∀ r, r.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm r = reg m r) →
      LOResult m retAddr sp0 G (listsOidLoop m.mem (memBytes m.mem q ql) k p' n') := by
    intro k
    induction k with
    | zero =>
      intro _ _ _ _ _ _ _ _ _ _ hn0 hnk
      exact absurd (Nat.lt_of_lt_of_le hn0 hnk) (Nat.lt_irrefl 0)
    | succ k ih =>
    intro Mx nm p' n' S st hM hsl lp ln hn0 hnk sR hp' hpn' rsp r18 r19 r20 r21 kq
    have hn' : n' < 2 ^ 32 := by omega
    have hn0' : n' ≠ 0 := by omega
    have hc : CodeIn Mx P listsOidCode := cIn env.cod sGC hM
    have eD8 : F + 0xC + 8 = F + 0x14 := by rw [BitVec.add_assoc]; rfl
    have eDC : F + 0xC + 0xC = F + 0x18 := by rw [BitVec.add_assoc]; rfl
    -- `Der::sequence` with the result at `sp + 0x34` and the list's reader at `sp + 0xC`
    obtain ⟨m5, c5, u5⟩ := St.block [.aluImm .add a0 sp 0x34, .aluImm .add a1 sp 0xC] st hc (off' := 0x2A)
      (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u5
    have k5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m5 q = reg nm q := fun q hv h0 h1 => by
      rw [u5.regs, upd_ne hv h1, upd_ne hv h0]
    obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5.self.callRa hc lo_at_2a lo_at_2e (cb := P + 0xFFFFF5CA)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF5CA (by decide))
    have r6 := PEnv.reg1 regs6 u5.self.zero
    have sp6 : reg m6 sp = F := by rw [r6 sp (by decide), k5 sp (by decide) (by decide) (by decide), rsp]
    have eN : P + 0xFFFFF5CA + 0x278 = P + 0xFFFFF842 := by rw [BitVec.add_assoc]; rfl
    have hNE : NestEnv m6.mem (P + 0xFFFFF5CA + 0x278) F (F + 0x34) (F + 0xC) := by
      rw [mem6, eN]
      refine ⟨even_at P env.hP 0xFFFFF842 (by decide), cIn env.nst sGN hM,
        by rw [BitVec.add_assoc]; exact cIn env.elem sGE hM, by rw [BitVec.add_assoc]; exact cIn env.tlv sGT hM,
        hFa, by omega, aligned_add hFa (k := 0x34) (by decide), aligned_add hFa (k := 0xC) (by decide),
        by rw [eNF]; exact sGN.sub (by decide),
        by rw [eNF, BitVec.add_assoc]; exact sGE.sub (by decide),
        by rw [eNF, BitVec.add_assoc]; exact sGT.sub (by decide),
        sFk 0x34 16 (by decide) sGN, by rw [eD8]; exact sFk 0x14 8 (by decide) sGN,
        by rw [eD8, BitVec.add_assoc]; exact sFk 0x14 8 (by decide) sGT,
        by rw [eNF, show F + 0x34 = F + BitVec.ofNat 32 0x34 from rfl, eFk]
           exact offs (.inr (by decide)) (by decide) (by decide),
        by rw [eNF, eD8, show F + 0x14 = F + BitVec.ofNat 32 0x14 from rfl, eFk]
           exact offs (.inr (by decide)) (by decide) (by decide),
        by rw [eD8, eDC, lp, ln, ofNat_tn hn', eNF]; exact sR.subR (by decide),
        by rw [eD8, lp]; exact hp', by rw [eD8, eDC, lp, ln, ofNat_tn hn']; exact hpn'⟩
    obtain ⟨m7, c7, pc7, sp7, k7, f7⟩ := derSequence_correct m6 (even_at P env.hP 0xFFFFF5CA (by decide))
      (by rw [mem6]; exact cIn env.seq sGQ hM) hNE pc6 sp6
      (by rw [r6 a0 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
      (by rw [r6 a1 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
      (by rw [regs6]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x2A + 8) (by decide)))
    have eL : memBytes Mx p' n' = memBytes m.mem p' n' :=
      memBytes_congr fun i hi => hM _ (sR.sub (c := i) (l := 1) (by omega)).symm
    rw [mem6, eD8, eDC, lp, ln, ofNat_tn hn', eL] at f7
    generalize hR : derElement 0x30 (memBytes m.mem p' n') = R at f7
    have S7 : Steps m m7 := S.trans (c5.trans (c6.trans c7))
    have f7k : ∀ k, k < 0x60 → m7.mem (F + BitVec.ofNat 32 k) =
        derNestedMem (derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') R) (F + 0x34) p' R (F + BitVec.ofNat 32 k) :=
      fun k hk => f7 _ (by rw [eNF, eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
    have memN : ∀ x, Sep G 0x80 x 1 → m7.mem x = m.mem x := fun x hx => by
      rw [f7 x (by rw [eNF]; exact hx.sub (c := 0) (l := 0x20) (by decide)),
        nestedMem_outside (out := F + 0x34) R (sFk 0x34 16 (by decide) hx),
        derAdvance_outside (d := F + 0xC) R (by rw [eD8]; exact sFk 0x14 8 (by decide) hx), hM x hx]
    have hc7 : CodeIn m7.mem P listsOidCode := cIn env.cod sGC memN
    have slot7 : ∀ k, 0x44 ≤ k → k < 0x60 → m7.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
      fun k h1 h2 => by
        rw [f7k k h2, nestedMem_outside (out := F + 0x34) R (sepF (c := 0x34) (n := 16) (.inl (by omega))
            (by decide) h2),
          derAdvance_outside (d := F + 0xC) R
            (by rw [eD8]; exact sepF (c := 0x14) (n := 8) (.inl (by omega)) (by decide) h2), hsl k h1 h2]
    have K7 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m7 q = reg nm q := fun q hq => by
      have h : oidKeep q = true ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 := by revert hq; revert q; decide
      rw [k7 q h.1, r6 q h.2.1, k5 q h.2.2.1 h.2.2.2.1 h.2.2.2.2]
    have u7 : St m7.mem P m7 0x32 (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
    obtain ⟨m8, c8, u8⟩ := St.block [.lw (9 : Fin 32) sp 0x34, .lbu (8 : Fin 32) sp 0x38] u7 hc7 (off' := 0x38)
      (by decide) (by
        simp +decide only [BlockOk, BInstr.ok, and_true]
        rw [sp7]; exact aligned_add hFa (k := 0x34) (by decide))
    simp only [runBlock, BInstr.run] at u8
    have sp7' : reg m7 sp = F := sp7
    have l34 : memLoad32 m7.mem (F + 0x34) =
        memLoad32 (derNestedMem (derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') R) (F + 0x34) p' R) (F + 0x34) :=
      memLoad32_congr fun j hj => by
        rw [show F + 0x34 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x34 + j) by rw [← add_ofNat_assoc]; rfl,
          f7k _ (by omega)]
    have h38 : m7.mem (F + 0x38) =
        derNestedMem (derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') R) (F + 0x34) p' R (F + 0x34 + 4) := by
      rw [show F + 0x34 + 4 = F + BitVec.ofNat 32 0x38 by rw [BitVec.add_assoc]; rfl, ← f7k _ (by decide)]; rfl
    have v8s1 : reg m8 9 = memLoad32 m7.mem (F + 0x34) := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7']
    have v8s0 : reg m8 8 = (m7.mem (F + 0x38)).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7']
    have k8 : ∀ q, q.val ≠ 0 → q ≠ 8 → q ≠ 9 → reg m8 q = reg m7 q := fun q hv h8 h9 => by
      rw [u8.regs, upd_ne hv h8, upd_ne hv h9]
    have K8 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m8 q = reg nm q := fun q hq => by
      rw [k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
      exact K7 q hq
    have sp8 : reg m8 sp = F := by rw [k8 sp (by decide) (by decide) (by decide), sp7']
    have Km8 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m8 q = reg m q := fun q hq => by
      rw [K8 q (by revert hq; revert q; decide)]; exact kq q hq
    have S8 : Steps m m8 := S7.trans c8
    cases R with
    | error e =>
      obtain ⟨z0, z4⟩ := nestedMem_err (M := derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') (.error e))
        (out := F + 0x34) (rp := p') e
      obtain ⟨m9, d9, u9⟩ := u8.self.taken hc7 0x7C lo_at_38 (by decide) (by rw [v8s1, l34, z0, u8.self.zero]; rfl)
      have hspec : listsOidLoop m.mem (memBytes m.mem q ql) (k + 1) p' n' = .error (derErrByte e) := by
        simp only [listsOidLoop, hn0', ↓reduceIte, hR]
      rw [hspec]
      exact errExit (S8.trans (.single d9)) u9.self hc7 memN slot7 (by rw [u9.regs, sp8])
        (fun q hq => by rw [u9.regs]; exact Km8 q hq) (by rw [u9.regs, v8s0, h38, z4])
    | ok t =>
      obtain ⟨z0, z4, z8, zC⟩ := nestedMem_ok (M := derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') (.ok t))
        (out := F + 0x34) (rp := p') t
      have hb : t.header + t.len ≤ n' := by have := derElement_bound hR; rwa [memBytes_length] at this
      have hh2 : 2 ≤ t.header := derElement_header hR
      have hlen : t.len < 2 ^ 32 := by omega
      have hpH : (p' + BitVec.ofNat 32 t.header).toNat = p'.toNat + t.header := by
        rw [BitVec.toNat_add, ofNat_tn (by omega)]; omega
      have hp0 : p' + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
        have := congrArg BitVec.toNat h; rw [hpH, show (0 : Word).toNat = 0 from rfl] at this; omega
      obtain ⟨m9, d9, u9⟩ := u8.self.notTaken hc7 0x3A lo_at_38 (by decide) (by
        rw [v8s1, l34, z0, u8.self.zero]; exact beq_false_of_ne hp0)
      -- rebuild the `SEQUENCE`'s reader at `sp + 0x24`
      obtain ⟨m10, c10, u10⟩ := St.block [.aluImm .add a2 x0 0xB, .alu .add a0 x0 (19 : Fin 32),
        .alu .add a1 x0 (18 : Fin 32)] u9 hc7 (off' := 0x40) (by decide) (by simp [BlockOk, BInstr.ok])
      simp only [runBlock, BInstr.run] at u10
      have k10 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m10 q = reg m8 q := fun q hv h0 h1 h2 => by
        rw [u10.regs, upd_ne hv h1, upd_ne hv h0, upd_ne hv h2]
      have sp10 : reg m10 sp = F := by rw [k10 sp (by decide) (by decide) (by decide) (by decide), sp8]
      have r19_8 : reg m8 19 = F + 0x29 := by rw [K8 19 (by decide), r19]
      have r18_8 : reg m8 18 = F + 0x39 := by rw [K8 18 (by decide), r18]
      obtain ⟨m11, c11, u11, sp11, f11, k11⟩ := mcCall (dst := F + 0x29) (src := F + 0x39) (N := 11) u10.self hc7
        lo_at_40 lo_at_44 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (cIn env.mcs sGU memN)
        (cIn env.mcb sGB memN) sp10
        (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r19_8]; exact zw _)
        (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r18_8]; exact zw _)
        (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u8.self.zero]; rfl)
        (sFk 0x29 11 (by decide) sGB)
        (by rw [show F + 0x29 = F + BitVec.ofNat 32 0x29 from rfl, eFk]
            exact offs (.inr (by decide)) (by decide) (by decide))
        (by rw [show F + 0x39 = F + BitVec.ofNat 32 0x39 from rfl, eFk]
            exact offs (.inr (by decide)) (by decide) (by decide))
        (sep_offsets F (c := 0x29) (n := 11) (d := 0x39) (k := 11) (.inl (by decide)) (by decide) (by decide))
        (by rw [BitVec.toNat_add, show (0x29 : Word).toNat = 0x29 from rfl]; have := sp0.isLt; omega)
        (by rw [BitVec.toNat_add, show (0x39 : Word).toNat = 0x39 from rfl]; have := sp0.isLt; omega)
      have m11F : ∀ k, k < 0x60 → m11.mem (F + BitVec.ofNat 32 k) =
          copyBytes m7.mem (F + 0x29) (F + 0x39) 11 (F + BitVec.ofNat 32 k) := fun k hk =>
        f11 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
      have m11G : ∀ x, Sep G 0x80 x 1 → m11.mem x = m.mem x := fun x hx => by
        rw [f11 x (hx.sub (c := 0x10) (l := 16) (by decide)),
          copyBytes_sep (dst := F + 0x29) (n := 11) (sFk 0x29 11 (by decide) hx) (Nat.le_refl _), memN x hx]
      have hc11 : CodeIn m11.mem P listsOidCode := cIn env.cod sGC m11G
      have s9_11 : reg m11 9 = p' + BitVec.ofNat 32 t.header := by
        rw [k11 9 (by decide), k10 9 (by decide) (by decide) (by decide) (by decide), v8s1, l34, z0]
      have s8_11 : reg m11 8 = (m7.mem (F + 0x38)).zeroExtend 32 := by
        rw [k11 8 (by decide), k10 8 (by decide) (by decide) (by decide) (by decide), v8s0]
      obtain ⟨m12, d12, u12⟩ := u11.sw hc11 lo_at_48 (off' := 0x4A) (by decide)
        (by rw [sp11]; exact aligned_add hFa (k := 0x24) (by decide))
      rw [sp11, s9_11] at u12
      have hc12 := CodeIn.store32 (a := F + 0x24) (v := p' + BitVec.ofNat 32 t.header) hc11 (sFk 0x24 4 (by decide) sGC)
      obtain ⟨m13, d13, u13⟩ := u12.sb hc12 lo_at_4a (off' := 0x4E) (by decide)
      rw [sp11, s8_11, tlv_zext] at u13
      obtain ⟨M13, hM13⟩ : ∃ M, memStore8 (memStore32 m11.mem (F + 0x24) (p' + BitVec.ofNat 32 t.header)) (F + 0x28)
          (m7.mem (F + 0x38)) = M := ⟨_, rfl⟩
      rw [hM13] at u13
      have hc13 : CodeIn M13 P listsOidCode := by
        rw [← hM13]; exact CodeIn.store8 hc12 (sFk 0x28 1 (by decide) sGC)
      have M13F : ∀ k, (k + 1 ≤ 0x24 ∨ 0x29 ≤ k) → k < 0x60 → M13 (F + BitVec.ofNat 32 k) = m11.mem (F + BitVec.ofNat 32 k) :=
        fun k h1 h2 => by
          rw [← hM13, memStore8_ne fun e => (sepF (c := 0x28) (n := 1) (k := k) (by omega) (by decide) h2).point
              (i := 0) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm),
            memStore32_get_sep (a := F + 0x24) (sepF (c := 0x24) (n := 4) (k := k) (by omega) (by decide) h2)]
      have M13G : ∀ x, Sep G 0x80 x 1 → M13 x = m.mem x := fun x hx => by
        rw [← hM13, memStore8_ne fun e => (sFk 0x28 1 (by decide) hx).point (i := 0) (j := 0) (by decide) (by decide)
            (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm),
          memStore32_get_sep (a := F + 0x24) (sFk 0x24 4 (by decide) hx), m11G x hx]
      have cp : ∀ j, j < 8 → M13 (F + BitVec.ofNat 32 (0x2C + j)) = m7.mem (F + BitVec.ofNat 32 (0x3C + j)) :=
        fun j hj => by
          rw [M13F _ (by omega) (by omega), m11F _ (by omega),
            show F + BitVec.ofNat 32 (0x2C + j) = F + 0x29 + BitVec.ofNat 32 (3 + j) by
              rw [show (0x29 : Word) = BitVec.ofNat 32 0x29 from rfl, add_ofNat_assoc,
                show 0x29 + (3 + j) = 0x2C + j by omega],
            ds_copy_in (by omega) (by decide),
            show F + 0x39 + BitVec.ofNat 32 (3 + j) = F + BitVec.ofNat 32 (0x3C + j) by
              rw [show (0x39 : Word) = BitVec.ofNat 32 0x39 from rfl, add_ofNat_assoc,
                show 0x39 + (3 + j) = 0x3C + j by omega]]
      have lq : memLoad32 M13 (F + 0x2C) = p' + BitVec.ofNat 32 t.header := by
        rw [← z8]
        calc memLoad32 M13 (F + 0x2C) = memLoad32 m7.mem (F + BitVec.ofNat 32 0x3C) :=
              memLoad32_congr2 fun jj hj => by
                rw [show F + 0x2C + BitVec.ofNat 32 jj = F + BitVec.ofNat 32 (0x2C + jj) by
                  rw [show (0x2C : Word) = BitVec.ofNat 32 0x2C from rfl, add_ofNat_assoc], add_ofNat_assoc,
                  cp jj (by omega)]
          _ = _ := by
              rw [show F + 0x34 + 8 = F + BitVec.ofNat 32 0x3C by rw [BitVec.add_assoc]; rfl]
              exact memLoad32_congr fun jj hj => by rw [add_ofNat_assoc, f7k _ (by omega)]
      have lk : memLoad32 M13 (F + 0x30) = BitVec.ofNat 32 t.len := by
        rw [← zC]
        calc memLoad32 M13 (F + 0x30) = memLoad32 m7.mem (F + BitVec.ofNat 32 0x40) :=
              memLoad32_congr2 fun jj hj => by
                rw [show F + 0x30 + BitVec.ofNat 32 jj = F + BitVec.ofNat 32 (0x2C + (4 + jj)) by
                  rw [show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, add_ofNat_assoc,
                    show 0x30 + jj = 0x2C + (4 + jj) by omega], add_ofNat_assoc,
                  cp _ (by omega), show 0x3C + (4 + jj) = 0x40 + jj by omega]
          _ = _ := by
              rw [show F + 0x34 + 0xC = F + BitVec.ofNat 32 0x40 by rw [BitVec.add_assoc]; rfl]
              exact memLoad32_congr fun jj hj => by rw [add_ofNat_assoc, f7k _ (by omega)]
      -- `Der::oid` with the result at `sp + 0x1C` and the rebuilt reader at `sp + 0x24`
      obtain ⟨m14, c14, u14⟩ := St.block [.aluImm .add a0 sp 0x1C, .aluImm .add a1 sp 0x24] u13 hc13
        (off' := 0x52) (by decide) (by simp [BlockOk, BInstr.ok])
      simp only [runBlock, BInstr.run] at u14
      have k14 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m14 q = reg m11 q := fun q hv h0 h1 => by
        rw [u14.regs, upd_ne hv h1, upd_ne hv h0]
      obtain ⟨m15, c15, pc15, mem15, regs15⟩ := u14.self.callRa hc13 lo_at_52 lo_at_56 (cb := P + 0xFFFFFE9A)
        (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFE9A (by decide))
      have r15 := PEnv.reg1 regs15 u14.self.zero
      have sp15 : reg m15 sp = F := by rw [r15 sp (by decide), k14 sp (by decide) (by decide) (by decide), sp11]
      have sIn : Sep (p' + BitVec.ofNat 32 t.header) t.len G 0x80 := sR.sub (by omega)
      have eD2 : F + 0x24 + 8 = F + 0x2C := by rw [BitVec.add_assoc]; rfl
      have eD2C : F + 0x24 + 0xC = F + 0x30 := by rw [BitVec.add_assoc]; rfl
      have oenv : OidEnv m15.mem (P + 0xFFFFFE9A) F (F + 0x1C) (F + 0x24) := by
        rw [mem15]
        refine ⟨even_at P env.hP 0xFFFFFE9A (by decide), cIn env.oid sGO M13G,
          by rw [BitVec.add_assoc]; exact cIn env.elem sGE M13G, by rw [BitVec.add_assoc]; exact cIn env.tlv sGT M13G,
          hFa, by omega, aligned_add hFa (k := 0x1C) (by decide), aligned_add hFa (k := 0x24) (by decide),
          by rw [eNF]; exact sGO.sub (by decide), by rw [eNF, BitVec.add_assoc]; exact sGE.sub (by decide),
          by rw [eNF, BitVec.add_assoc]; exact sGT.sub (by decide), sFk 0x1C 8 (by decide) sGO,
          by rw [eD2]; exact sFk 0x2C 8 (by decide) sGO,
          by rw [eD2, BitVec.add_assoc]; exact sFk 0x2C 8 (by decide) sGT,
          by rw [eNF, show F + 0x1C = F + BitVec.ofNat 32 0x1C from rfl, eFk]
             exact offs (.inr (by decide)) (by decide) (by decide),
          by rw [eNF, eD2, show F + 0x2C = F + BitVec.ofNat 32 0x2C from rfl, eFk]
             exact offs (.inr (by decide)) (by decide) (by decide),
          by rw [eD2, eD2C, lq, lk, ofNat_tn hlen, eNF]; exact sIn.subR (by decide),
          by rw [eD2, eD2C, lq, lk, ofNat_tn hlen, show F + 0x2C = F + BitVec.ofNat 32 0x2C from rfl, eFk]
             exact sIn.subR (by decide),
          by rw [eD2, lq, hpH]; omega, by rw [eD2, eD2C, lq, lk, ofNat_tn hlen, hpH]; omega⟩
      obtain ⟨m16, c16, pc16, sp16, k16, f16⟩ := derOid_correct m15 oenv pc15 sp15
        (by rw [r15 a0 (by decide), u14.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp11]; rfl)
        (by rw [r15 a1 (by decide), u14.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp11]; rfl)
        (by rw [regs15]; simp +decide only [upd_app, ↓reduceIte])
        (even_clear _ (even_at P env.hP (0x52 + 8) (by decide)))
      have eB : memBytes M13 (p' + BitVec.ofNat 32 t.header) t.len =
          memBytes m.mem (p' + BitVec.ofNat 32 t.header) t.len :=
        memBytes_congr fun i hi => M13G _ (sIn.sub (c := i) (l := 1) (by omega)).symm
      rw [mem15, eD2, eD2C, lq, lk, ofNat_tn hlen, eB] at f16
      generalize hO : derOid (memBytes m.mem (p' + BitVec.ofNat 32 t.header) t.len) = O at f16
      obtain ⟨A, hA⟩ : ∃ A, derAdvance M13 (F + 0x24) (p' + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len)
          (derElement 6 (memBytes m.mem (p' + BitVec.ofNat 32 t.header) t.len)) = A := ⟨_, rfl⟩
      rw [hA] at f16
      have S16 : Steps m m16 :=
        S8.trans (.cons d9 (c10.trans (c11.trans (.cons d12 (.cons d13 (c14.trans (c15.trans c16)))))))
      have f16k : ∀ k, k < 0x60 → m16.mem (F + BitVec.ofNat 32 k) =
          derOidMem A (F + 0x1C) (p' + BitVec.ofNat 32 t.header) O (F + BitVec.ofNat 32 k) := fun k hk =>
        f16 _ (by rw [eNF, eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
      have AO : ∀ x, Sep (F + 0x2C) 8 x 1 → A x = M13 x := fun x hx => by
        rw [← hA]; exact derAdvance_outside (d := F + 0x24) _ (by rw [eD2]; exact hx)
      have m16G : ∀ x, Sep G 0x80 x 1 → m16.mem x = m.mem x := fun x hx => by
        rw [f16 x (by rw [eNF]; exact hx.sub (c := 0) (l := 0x20) (by decide)),
          oidMem_outside (out := F + 0x1C) O (sFk 0x1C 8 (by decide) hx), AO x (sFk 0x2C 8 (by decide) hx), M13G x hx]
      have hc16 : CodeIn m16.mem P listsOidCode := cIn env.cod sGC m16G
      have slot16 : ∀ k, 0x44 ≤ k → k < 0x60 → m16.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
        fun k h1 h2 => by
          rw [f16k k h2, oidMem_outside (out := F + 0x1C) O (sepF (c := 0x1C) (n := 8) (.inl (by omega)) (by decide) h2),
            AO _ (sepF (c := 0x2C) (n := 8) (.inl (by omega)) (by decide) h2), M13F k (by omega) h2, m11F k h2,
            copyBytes_sep (dst := F + 0x29) (n := 11) (sepF (c := 0x29) (n := 11) (.inl (by omega)) (by decide) h2)
              (Nat.le_refl _), slot7 k h1 h2]
      have K16 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m16 q = reg nm q := fun q hq => by
        have h : oidKeep q = true ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧
            q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
        rw [k16 q h.1, r15 q h.2.1, k14 q h.2.2.1 h.2.2.2.1 h.2.2.2.2.1, k11 q h.2.2.2.2.2.2,
          k10 q h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1]
        exact K8 q hq
      have u16 : St m16.mem P m16 0x5A (reg m16) := ⟨by rw [pc16], rfl, fun _ => rfl⟩
      obtain ⟨m17, d17, u17⟩ := u16.lw hc16 lo_at_5a (off' := 0x5C) (by decide)
        (by rw [sp16]; exact aligned_add hFa (k := 0x1C) (by decide))
      have l1C : memLoad32 m16.mem (F + 0x1C) =
          memLoad32 (derOidMem A (F + 0x1C) (p' + BitVec.ofNat 32 t.header) O) (F + 0x1C) :=
        memLoad32_congr fun j hj => by
          rw [show F + 0x1C + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x1C + j) by rw [← add_ofNat_assoc]; rfl,
            f16k _ (by omega)]
      have v17 : reg m17 a0 = memLoad32 m16.mem (F + 0x1C) := by
        rw [u17.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp16]
      have k17 : ∀ q, q.val ≠ 0 → q ≠ a0 → reg m17 q = reg m16 q := fun q hv h0 => by rw [u17.regs, upd_ne hv h0]
      cases O with
      | error e =>
        obtain ⟨m18, d18, u18⟩ := u17.self.taken hc16 0x78 lo_at_5c (by decide)
          (by rw [v17, l1C, (oidMem_err e).1, u17.self.zero]; rfl)
        obtain ⟨m19, d19, u19⟩ := u18.lbu hc16 lo_at_78 (off' := 0x7C) (by decide)
        have e20 : m16.mem (F + 0x20) = derErrByte e := by
          rw [show F + 0x20 = F + BitVec.ofNat 32 0x20 from rfl, f16k _ (by decide),
            show F + BitVec.ofNat 32 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]
          exact (oidMem_err e).2
        have hspec : listsOidLoop m.mem (memBytes m.mem q ql) (k + 1) p' n' = .error (derErrByte e) := by
          simp only [listsOidLoop, hn0', ↓reduceIte, hR, hO]
        rw [hspec]
        exact errExit (S16.trans (.cons d17 (.cons d18 (.single d19)))) u19.self hc16 m16G slot16
          (by rw [u19.regs, upd_ne (by decide) (by decide), k17 sp (by decide) (by decide), sp16])
          (fun q hq => by
            rw [u19.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide),
              k17 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
              K16 q (by revert hq; revert q; decide)]
            exact kq q hq)
          (by rw [u19.regs]; simp +decide only [upd_app, ↓reduceIte]
              rw [k17 sp (by decide) (by decide), sp16, e20])
      | ok o =>
        have hoE := derOid_ok_elem hO
        rw [hoE] at hA
        have hob : o.header + o.len ≤ t.len := by have := derElement_bound hoE; rwa [memBytes_length] at this
        have hpo : (p' + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header).toNat = p'.toNat + t.header + o.header := by
          rw [BitVec.toNat_add, hpH, ofNat_tn (by omega)]; omega
        have hs1 : p' + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header ≠ 0 := fun h => by
          have := congrArg BitVec.toNat h; rw [hpo, show (0 : Word).toNat = 0 from rfl] at this; omega
        have l17 : memLoad32 m16.mem (F + 0x1C) = p' + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header := by
          rw [l1C, (oidMem_ok o).1]
        have l20 : memLoad32 m16.mem (F + 0x20) = BitVec.ofNat 32 o.len := by
          have : memLoad32 m16.mem (F + 0x20) =
              memLoad32 (derOidMem A (F + 0x1C) (p' + BitVec.ofNat 32 t.header) (.ok o)) (F + 0x20) :=
            memLoad32_congr fun j hj => by
              rw [show F + 0x20 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x20 + j) by rw [← add_ofNat_assoc]; rfl,
                f16k _ (by omega)]
          rw [this, show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact (oidMem_ok o).2
        have sp17 : reg m17 sp = F := by rw [k17 sp (by decide) (by decide), sp16]
        obtain ⟨m18, d18, u18⟩ := u17.self.notTaken hc16 0x5E lo_at_5c (by decide)
          (by rw [v17, l17, u17.self.zero]; exact beq_false_of_ne hs1)
        obtain ⟨m19, d19, u19⟩ := u18.lw hc16 lo_at_5e (off' := 0x60) (by decide)
          (by rw [sp17]; exact aligned_add hFa (k := 0x20) (by decide))
        obtain ⟨m20, c20, u20⟩ := St.block [.alu .add a2 x0 (21 : Fin 32), .alu .add a3 x0 (20 : Fin 32)] u19.self hc16
          (off' := 0x64) (by decide) (by simp [BlockOk, BInstr.ok])
        simp only [runBlock, BInstr.run] at u20
        have k20 : ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m20 q = reg m17 q := fun q hv h1 h2 h3 => by
          rw [u20.regs, upd_ne hv h3, upd_ne hv h2, u19.regs, upd_ne hv h1]
        obtain ⟨m21, c21, pc21, mem21, regs21⟩ := u20.self.callRa hc16 lo_at_64 lo_at_68 (cb := P + 0xFFFFFE3E)
          (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFE3E (by decide))
        have r21' := PEnv.reg1 regs21 u20.self.zero
        have sp21 : reg m21 sp = F := by
          rw [r21' sp (by decide), k20 sp (by decide) (by decide) (by decide) (by decide), sp17]
        have K21 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m21 q = reg nm q :=
          fun q hq => by
            have h : q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a0 := by revert hq; revert q; decide
            rw [r21' q h.1, k20 q h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1, k17 q h.2.1 h.2.2.2.2.2]; exact K16 q hq
        obtain ⟨m22, c22, pc22, a022, k22, f22⟩ := sliceEq_correct m21 (base := P + 0xFFFFFE3E)
          (p := p' + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header) (q := q) (pl := o.len) (ql := ql) (even_at P env.hP 0xFFFFFE3E (by decide)) (by rw [mem21]; exact cIn env.seqq sGS m16G)
          (by rw [mem21, BitVec.add_assoc]; exact cIn env.esl sGL m16G)
          (by rw [mem21, BitVec.add_assoc]; exact cIn env.cmp sGM m16G) pc21
          (by rw [r21' a0 (by decide), k20 a0 (by decide) (by decide) (by decide) (by decide), v17, l17])
          (by rw [r21' a1 (by decide), u20.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide),
                u19.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp17, l20])
          (by rw [r21' a2 (by decide), u20.regs, upd_ne (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
              rw [u19.self.zero, u19.regs, upd_ne (by decide) (by decide), k17 21 (by decide) (by decide),
                K16 21 (by decide), r21]
              all_goals exact zw q)
          (by rw [r21' a3 (by decide), u20.regs]; simp +decide only [upd_app, ↓reduceIte]
              rw [u19.regs, upd_ne (by decide) (by decide), k17 20 (by decide) (by decide),
                K16 20 (by decide), r20]
              all_goals exact zw _)
          (by omega) env.hql (by rw [regs21]; simp +decide only [upd_app, ↓reduceIte])
          (even_clear _ (even_at P env.hP (0x64 + 8) (by decide))) (by rw [sp21]; exact hFa)
          (by rw [sp21, eS4, BitVec.add_assoc]; exact sGL.sub (by decide))
          (by rw [sp21, eS4, BitVec.add_assoc]; exact sGM.sub (by decide))
          (by rw [sp21, eS4, add_ofNat_assoc]
              exact (sR.sub (c := t.header + o.header) (l := o.len) (by omega)).symm.sub (c := 0x1C) (l := 4)
                (by decide))
          (by rw [sp21, eS4]; exact sQG.symm.sub (c := 0x1C) (l := 4) (by decide))
        rw [mem21] at a022
        rw [mem21, sp21, eS4] at f22
        have eq1 : memBytes m16.mem (p' + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header) o.len =
            memBytes m.mem (p' + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header) o.len :=
          memBytes_congr fun i hi => by
            rw [add_ofNat_assoc, add_ofNat_assoc]
            exact m16G _ (sR.sub (c := t.header + (o.header + i)) (l := 1) (by omega)).symm
        have eq2 : memBytes m16.mem q ql = memBytes m.mem q ql :=
          memBytes_congr fun i hi => m16G _ (sQG.sub (c := i) (l := 1) (by omega)).symm
        rw [eq1, eq2] at a022
        have m22F : ∀ k, k < 0x60 → m22.mem (F + BitVec.ofNat 32 k) = m16.mem (F + BitVec.ofNat 32 k) := fun k hk =>
          f22 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
        have m22G : ∀ x, Sep G 0x80 x 1 → m22.mem x = m.mem x := fun x hx => by
          rw [f22 x (hx.sub (c := 0x1C) (l := 4) (by decide)), m16G x hx]
        have hc22 : CodeIn m22.mem P listsOidCode := cIn env.cod sGC m22G
        have slot22 : ∀ k, 0x44 ≤ k → k < 0x60 → m22.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
          fun k h1 h2 => by rw [m22F k h2, slot16 k h1 h2]
        have K22 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m22 q = reg nm q :=
          fun q hq => by
            have h : q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ t1 := by revert hq; revert q; decide
            rw [k22 q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2]; exact K21 q hq
        have sp22 : reg m22 sp = F := by
          rw [k22 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp21]
        have Km22 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m22 q = reg m q := fun q hq => by
          rw [K22 q (by revert hq; revert q; decide)]; exact kq q hq
        have u22 : St m22.mem P m22 0x6C (reg m22) := ⟨by rw [pc22], rfl, fun _ => rfl⟩
        have S22 : Steps m m22 := S16.trans (.cons d17 (.cons d18 (.cons d19 (c20.trans (c21.trans c22)))))
        by_cases heq : memBytes m.mem (p' + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header) o.len =
            memBytes m.mem q ql
        · obtain ⟨m23, d23, u23⟩ := u22.taken hc22 0x80 lo_at_6c (by decide)
            (by rw [a022, ite_eq_left heq, u22.zero]; rfl)
          have hspec : listsOidLoop m.mem (memBytes m.mem q ql) (k + 1) p' n' = .ok true := by
            simp only [listsOidLoop, hn0', ↓reduceIte, hR, hO, heq]
          rw [hspec]
          exact trueExit (S22.trans (.single d23)) u23.self hc22 m22G slot22 (by rw [u23.regs, sp22])
            (fun q hq => by rw [u23.regs]; exact Km22 q hq)
        · obtain ⟨m23, d23, u23⟩ := u22.notTaken hc22 0x6E lo_at_6c (by decide)
            (by rw [a022, ite_eq_right heq, u22.zero]; rfl)
          have rd : ∀ j, j < 8 → m22.mem (F + BitVec.ofNat 32 (0x14 + j)) =
              derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') (.ok t) (F + BitVec.ofNat 32 (0x14 + j)) := fun j hj => by
            rw [m22F _ (by omega), f16k _ (by omega),
              oidMem_outside (out := F + 0x1C) (.ok o) (sepF (c := 0x1C) (n := 8) (.inr (by omega)) (by decide) (by omega)),
              AO _ (sepF (c := 0x2C) (n := 8) (.inr (by omega)) (by decide) (by omega)), M13F _ (by omega) (by omega),
              m11F _ (by omega),
              copyBytes_sep (dst := F + 0x29) (n := 11) (sepF (c := 0x29) (n := 11) (.inr (by omega)) (by decide)
                (by omega)) (Nat.le_refl _), f7k _ (by omega),
              nestedMem_outside (out := F + 0x34) (.ok t) (sepF (c := 0x34) (n := 16) (.inr (by omega)) (by decide)
                (by omega))]
          have ld14 : memLoad32 m22.mem (F + 0x14) = p' + BitVec.ofNat 32 (t.header + t.len) := by
            have : memLoad32 m22.mem (F + 0x14) =
                memLoad32 (derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') (.ok t)) (F + 0x14) :=
              memLoad32_congr fun j hj => by
                rw [show F + 0x14 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x14 + j) by rw [← add_ofNat_assoc]; rfl,
                  rd j (by omega)]
            rw [this, ← eD8, (derAdvance_ld t).1]
          have ld18 : memLoad32 m22.mem (F + 0x18) = BitVec.ofNat 32 (n' - (t.header + t.len)) := by
            have : memLoad32 m22.mem (F + 0x18) =
                memLoad32 (derAdvance Mx (F + 0xC) p' (BitVec.ofNat 32 n') (.ok t)) (F + 0x18) :=
              memLoad32_congr fun j hj => by
                rw [show F + 0x18 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x14 + (4 + j)) by
                    rw [show 0x14 + (4 + j) = 0x18 + j by omega, ← add_ofNat_assoc]; rfl,
                  rd _ (by omega)]
            rw [this, ← eDC, (derAdvance_ld t).2]; exact sub_val hb hn'
          obtain ⟨m24, d24, u24⟩ := u23.lw hc22 lo_at_6e (off' := 0x70) (by decide)
            (by rw [sp22]; exact aligned_add hFa (k := 0x18) (by decide))
          have r24a1 : reg m24 a1 = BitVec.ofNat 32 (n' - (t.header + t.len)) := by
            rw [u24.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp22, ld18]
          have k24 : ∀ q, q.val ≠ 0 → q ≠ a1 → reg m24 q = reg m22 q := fun q hv h1 => by rw [u24.regs, upd_ne hv h1]
          have S24 : Steps m m24 := S22.trans (.cons d23 (.single d24))
          by_cases hz : n' - (t.header + t.len) = 0
          · obtain ⟨m25, d25, u25⟩ := u24.self.notTaken hc22 0x72 lo_at_70 (by decide)
              (by rw [r24a1, hz, u24.self.zero]; rfl)
            have hspec : listsOidLoop m.mem (memBytes m.mem q ql) (k + 1) p' n' = .ok false := by
              simp only [listsOidLoop, hn0', ↓reduceIte, hR, hO, heq, hz, listsOidLoop_zero]
            rw [hspec]
            exact falseExit (S24.trans (.single d25)) u25.self hc22 m22G slot22
              (by rw [u25.regs, k24 sp (by decide) (by decide), sp22])
              (fun q hq => by
                rw [u25.regs, k24 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
                exact Km22 q hq)
          · have hl : n' - (t.header + t.len) < 2 ^ 32 := by omega
            obtain ⟨m25, d25, u25⟩ := u24.self.taken hc22 0x26 lo_at_70 (by decide) (by
              rw [r24a1, u24.self.zero]
              simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
              have := congrArg BitVec.toNat h; rw [ofNat_tn hl] at this; exact hz this)
            have hspec : listsOidLoop m.mem (memBytes m.mem q ql) (k + 1) p' n' =
                listsOidLoop m.mem (memBytes m.mem q ql) k (p' + BitVec.ofNat 32 (t.header + t.len))
                  (n' - (t.header + t.len)) := by
              simp only [listsOidLoop, hn0', ↓reduceIte, hR, hO, heq]
            have hpT : (p' + BitVec.ofNat 32 (t.header + t.len)).toNat = p'.toNat + (t.header + t.len) := by
              rw [BitVec.toNat_add, ofNat_tn (by omega)]; omega
            have K25 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m25 q = reg nm q :=
              fun q hq => by
                rw [u25.regs, k24 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact K22 q hq
            rw [hspec]
            exact ih (S24.trans (.single d25)) u25.self m22G slot22 ld14 ld18 (by omega) (by omega)
              (sR.sub (by omega)) (by rw [hpT]; omega) (by rw [hpT]; omega)
              (by rw [u25.regs, k24 sp (by decide) (by decide), sp22])
              (by rw [K25 18 (by decide), r18]) (by rw [K25 19 (by decide), r19]) (by rw [K25 20 (by decide), r20])
              (by rw [K25 21 (by decide), r21])
              (fun q hq => by rw [K25 q (by revert hq; revert q; decide)]; exact kq q hq)
  show LOResult m retAddr sp0 G (listsOidLoop m.mem (memBytes m.mem q ql) n p n)
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨m4, d4, u4⟩ := u3.self.taken hc3 0x72 lo_at_24 (by decide) (by rw [a1_3, u3.self.zero]; rfl)
    rw [← (funext u4.regs : reg m4 = reg m3)] at sp3 Km3
    exact (listsOidLoop_zero _ _ _ _).symm ▸ falseExit (S3.trans (.single d4)) u4.self hc3 M3G slot3 sp3 Km3
  · obtain ⟨m4, d4, u4⟩ := u3.self.notTaken hc3 0x26 lo_at_24 (by decide) (by
      rw [a1_3, u3.self.zero]; exact beq_false_of_ne fun h => by
        have := congrArg BitVec.toNat h; rw [ofNat_tn hn] at this; exact hn0 this)
    rw [← (funext u4.regs : reg m4 = reg m3)] at sp3 s18_3 s19_3 s20_3 s21_3 Km3
    exact iter n (S3.trans (.single d4)) u4.self M3G slot3 l14 l18 (by omega) (Nat.le_refl _) sRG env.hp env.hpn sp3
      s18_3 s19_3 s20_3 s21_3 Km3

end C3.RV32
