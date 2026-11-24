import C3BootProofs.Proofs.DerAlgorithm
import C3BootProofs.Proofs.SliceEq

/-!
# `tsa::is_sha256`, as compiled

`is_sha256` reads an `AlgorithmIdentifier` with the proved `Der::algorithm`,
compares its OID with SHA-256's, `2.16.840.1.101.3.4.2.1`, which the image
keeps at `sha256OidAddress`, through the proved `[u8]` comparison, and accepts
absent parameters or a `NULL`.
-/

namespace C3.RV32

open C3.Image

theorem memBytes_agree {M M' : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M' (p + BitVec.ofNat 32 i)) {c l : Nat} (hl : c + l ≤ n) :
    memBytes M (p + BitVec.ofNat 32 c) l = memBytes M' (p + BitVec.ofNat 32 c) l :=
  (memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact (h _ (by omega)).symm).symm

theorem derAlgOf_congr {M M' : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M' (p + BitVec.ofNat 32 i)) :
    derAlgOf M p n = derAlgOf M' p n := by
  have e0 : memBytes M p n = memBytes M' p n := by
    have := memBytes_agree h (c := 0) (l := n) (by omega); rwa [add_ofNat_zero] at this
  unfold derAlgOf
  rw [e0]
  cases hR : derElement 0x30 (memBytes M' p n) with
  | error e => rfl
  | ok t =>
    dsimp only
    have hb : t.header + t.len ≤ n := by have := derElement_bound hR; rwa [memBytes_length] at this
    rw [memBytes_agree h (c := t.header) (l := t.len) (by omega)]
    cases hO : derOid (memBytes M' (p + BitVec.ofNat 32 t.header) t.len) with
    | error e => rfl
    | ok o =>
      dsimp only
      have hob : o.header + o.len ≤ t.len := by
        have := derElement_bound (derOid_ok_elem hO); rwa [memBytes_length] at this
      by_cases hz : t.len - (o.header + o.len) = 0
      · rw [ite_eq_left hz, ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz, add_ofNat_assoc,
          memBytes_agree h (c := t.header + (o.header + o.len)) (l := t.len - (o.header + o.len)) (by omega)]

theorem derAlgOf_ok_range {M : Word → BitVec 8} {p : Word} {n : Nat} {op : Word} {ol : Nat}
    {r : Option (Word × DerTlv)} (h : derAlgOf M p n = .ok ((op, ol), r)) :
    ∃ c, op = p + BitVec.ofNat 32 c ∧ c + ol ≤ n := by
  unfold derAlgOf at h
  split at h
  · cases h
  · rename_i t hR
    have hb : t.header + t.len ≤ n := by have := derElement_bound hR; rwa [memBytes_length] at this
    split at h
    · cases h
    · rename_i o hO
      have hob : o.header + o.len ≤ t.len := by
        have := derElement_bound (derOid_ok_elem hO); rwa [memBytes_length] at this
      have key : op = p + BitVec.ofNat 32 (t.header + o.header) ∧ ol = o.len := by
        split at h
        · cases h; exact ⟨add_ofNat_assoc _ _ _, rfl⟩
        · split at h
          · cases h
          · split at h
            · cases h; exact ⟨add_ofNat_assoc _ _ _, rfl⟩
            · cases h
      exact ⟨t.header + o.header, key.1, by omega⟩

theorem derAlgOf_some_range {M : Word → BitVec 8} {p : Word} {n : Nat} {x : Word × Nat} {rp : Word} {u : DerTlv}
    (h : derAlgOf M p n = .ok (x, some (rp, u))) :
    ∃ c, rp = p + BitVec.ofNat 32 c ∧ c + u.header + u.len ≤ n := by
  unfold derAlgOf at h
  split at h
  · cases h
  · rename_i t hR
    have hb : t.header + t.len ≤ n := by have := derElement_bound hR; rwa [memBytes_length] at this
    split at h
    · cases h
    · rename_i o hO
      have hob : o.header + o.len ≤ t.len := by
        have := derElement_bound (derOid_ok_elem hO); rwa [memBytes_length] at this
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i u' hU
          have hub : u'.header + u'.len ≤ t.len - (o.header + o.len) := by
            have := derTlv_bound hU; rwa [memBytes_length] at this
          split at h
          · cases h; exact ⟨t.header + (o.header + o.len), add_ofNat_assoc _ _ _, by omega⟩
          · cases h

abbrev isPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C)]

section
set_option maxRecDepth 20000
theorem is_at_0 : fetchRel isSha256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem is_at_2 : fetchRel isSha256Code 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem is_at_4 : fetchRel isSha256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem is_at_6 : fetchRel isSha256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem is_at_8 : fetchRel isSha256Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem is_at_a : fetchRel isSha256Code 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem is_at_c : fetchRel isSha256Code 0xC = some (.alu .add a1 x0 a0, 2) := by decide
theorem is_at_e : fetchRel isSha256Code 0xE = some (.alu .add a0 x0 sp, 2) := by decide
theorem is_at_10 : fetchRel isSha256Code 0x10 = some (.auipc ra 0x0, 4) := by decide
theorem is_at_14 : fetchRel isSha256Code 0x14 = some (.jalr ra ra 0x17A, 4) := by decide
theorem is_at_18 : fetchRel isSha256Code 0x18 = some (.load .lw (8 : Fin 32) sp 0x0, 2) := by decide
theorem is_at_1a : fetchRel isSha256Code 0x1A = some (.branch .beq (8 : Fin 32) x0 0x32, 2) := by decide
theorem is_at_1c : fetchRel isSha256Code 0x1C = some (.load .lw a1 sp 0x4, 2) := by decide
theorem is_at_1e : fetchRel isSha256Code 0x1E = some (.load .lw (9 : Fin 32) sp 0x8, 2) := by decide
theorem is_at_20 : fetchRel isSha256Code 0x20 = some (.load .lw (18 : Fin 32) sp 0xC, 2) := by decide
theorem is_at_22 : fetchRel isSha256Code 0x22 = some (.load .lbu (19 : Fin 32) sp 0x18, 4) := by decide
theorem is_at_26 : fetchRel isSha256Code 0x26 = some (.lui a2 0x3FCC5000, 4) := by decide
theorem is_at_2a : fetchRel isSha256Code 0x2A = some (.aluImm .add a2 a2 0xFFFFF880, 4) := by decide
theorem is_at_2e : fetchRel isSha256Code 0x2E = some (.aluImm .add a3 x0 0x9, 2) := by decide
theorem is_at_30 : fetchRel isSha256Code 0x30 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem is_at_32 : fetchRel isSha256Code 0x32 = some (.auipc ra 0x0, 4) := by decide
theorem is_at_36 : fetchRel isSha256Code 0x36 = some (.jalr ra ra 0xFFFFFEFE, 4) := by decide
theorem is_at_3a : fetchRel isSha256Code 0x3A = some (.branch .beq a0 x0 0x18, 2) := by decide
theorem is_at_3c : fetchRel isSha256Code 0x3C = some (.branch .beq (9 : Fin 32) x0 0x1A, 2) := by decide
theorem is_at_3e : fetchRel isSha256Code 0x3E = some (.aluImm .xor a0 (19 : Fin 32) 0x5, 4) := by decide
theorem is_at_42 : fetchRel isSha256Code 0x42 = some (.alu .or a0 a0 (18 : Fin 32), 4) := by decide
theorem is_at_46 : fetchRel isSha256Code 0x46 = some (.aluImm .sltu a1 a0 0x1, 4) := by decide
theorem is_at_4a : fetchRel isSha256Code 0x4A = some (.jal x0 0xE, 2) := by decide
theorem is_at_4c : fetchRel isSha256Code 0x4C = some (.load .lbu a1 sp 0x4, 4) := by decide
theorem is_at_50 : fetchRel isSha256Code 0x50 = some (.jal x0 0x8, 2) := by decide
theorem is_at_52 : fetchRel isSha256Code 0x52 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem is_at_54 : fetchRel isSha256Code 0x54 = some (.jal x0 0x4, 2) := by decide
theorem is_at_56 : fetchRel isSha256Code 0x56 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem is_at_58 : fetchRel isSha256Code 0x58 = some (.aluImm .sltu a0 (8 : Fin 32) 0x1, 4) := by decide
theorem is_at_5c : fetchRel isSha256Code 0x5C = some (.load .lw ra sp 0x2C, 2) := by decide
theorem is_at_5e : fetchRel isSha256Code 0x5E = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem is_at_60 : fetchRel isSha256Code 0x60 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem is_at_62 : fetchRel isSha256Code 0x62 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem is_at_64 : fetchRel isSha256Code 0x64 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem is_at_66 : fetchRel isSha256Code 0x66 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem is_at_68 : fetchRel isSha256Code 0x68 = some (.jalr x0 ra 0x0, 2) := by decide
theorem isSave_end : blockEnd isSha256Code 2 (saveBlock isPs) = some 0xC := by decide
theorem isRestore_end : blockEnd isSha256Code 0x5C (restoreBlock isPs) = some 0x66 := by decide
end

/-- SHA-256's OID's address in the image. -/
abbrev isOid : Word := (img% sha256OidAddress)

/-- `is_sha256`'s result for the reader whose unread bytes are the `n` at
`p`: the error byte, or whether the `AlgorithmIdentifier` there names
SHA-256 with absent or `NULL` parameters. -/
def isSha256Of (M : Word → BitVec 8) (p : Word) (n : Nat) : Except (BitVec 8) Bool :=
  match derAlgOf M p n with
  | .error b => .error b
  | .ok ((op, ol), none) => .ok (decide (memBytes M op ol = sha256OidData))
  | .ok ((op, ol), some (_, u)) =>
    .ok (decide (memBytes M op ol = sha256OidData ∧ u.tag % 256 = 5 ∧ u.len = 0))

theorem is_seqz (x : Word) : aluEval .sltu x 1 = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · rw [h]; rfl
  · rw [ite_eq_right h]
    show (if x.ult 1 then (1 : Word) else 0) = 0
    refine ite_eq_right fun h' => h ?_
    have : x.toNat < 1 := of_decide_eq_true h'
    exact BitVec.eq_of_toNat_eq (by rw [show (0 : Word).toNat = 0 from rfl]; omega)

theorem is_or0 {x y : Word} : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  have z : ∀ i, (0 : Word).getLsbD i = false := fun i => by
    rw [show (0 : Word) = 0#32 from rfl, BitVec.getLsbD_zero]
  constructor
  · intro h
    have h1 : ∀ i, x.getLsbD i = false ∧ y.getLsbD i = false := fun i => by
      have := congrArg (fun w => w.getLsbD i) h
      simp only [BitVec.getLsbD_or, z, Bool.or_eq_false_iff] at this; exact this
    exact ⟨BitVec.eq_of_getLsbD_eq fun i _ => by rw [(h1 i).1, z],
      BitVec.eq_of_getLsbD_eq fun i _ => by rw [(h1 i).2, z]⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem is_tag5 : ∀ b : BitVec 8, (b.zeroExtend 32 ^^^ 5 = 0) ↔ b = 5 := by decide

/-- What `isSha256_correct` concludes, for the result `R`. -/
def ISResult (m : Machine) (retAddr sp0 G : Word) (D : Word → BitVec 8) (R : Except (BitVec 8) Bool) : Prop :=
  ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
    (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
    (∀ x, Sep G 0xA0 x 1 → m'.mem x = D x) ∧
    match R with
    | .error b => reg m' a0 = 1 ∧ reg m' a1 = b.zeroExtend 32
    | .ok v => reg m' a0 = 0 ∧ reg m' a1 = if v then 1 else 0

/-- Where `is_sha256` runs: its code and its callees', the 0xA0 bytes of
stack below `sp0`, the reader at `d` over the `n` bytes at `p`, and the OID
at `isOid`, apart from what each must not touch. -/
structure ISEnv (M : Word → BitVec 8) (P sp0 d p : Word) (n : Nat) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P isSha256Code
  alg : CodeIn M (P + 0x18A) derAlgorithmCode
  seq : CodeIn M (P + 0x18A + 0xFFFFF532) derSequenceCode
  nst : CodeIn M (P + 0x18A + 0xFFFFF7AA) derNestedCode
  elem : CodeIn M (P + 0x18A + 0xFFFFF6CA) derElementCode
  tlv : CodeIn M (P + 0x18A + 0xFFFFF6F0) derTlvCode
  oid : CodeIn M (P + 0x18A + 0xFFFFFE02) derOidCode
  mcs : CodeIn M (P + 0x18A + 0xBEB6) memcpyStubCode
  mcb : CodeIn M (P + 0x18A + 0xBEBE) memcpyBodyCode
  seqq : CodeIn M (P + 0xFFFFFF30) sliceEqCode
  esl : CodeIn M (P + 0xFFFFFF30 + 0xFFFFF776) equalSameLengthCode
  cmp : CodeIn M (P + 0xFFFFFF30 + 0xC088) memcmpCode
  hoid : memBytes M isOid 9 = sha256OidData
  hsp : sp0.toNat % 4 = 0
  hS : 0xA0 ≤ sp0.toNat
  hd : d.toNat % 4 = 0
  hdp : memLoad32 M (d + 8) = p
  hdn : memLoad32 M (d + 0xC) = BitVec.ofNat 32 n
  hp : 0 < p.toNat
  hpn : p.toNat + n < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF60) 0xA0 P isSha256Code.length
  sGA : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A) derAlgorithmCode.length
  sGQ : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A + 0xFFFFF532) derSequenceCode.length
  sGN : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A + 0xFFFFF7AA) derNestedCode.length
  sGE : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A + 0xFFFFF6CA) derElementCode.length
  sGT : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A + 0xFFFFF6F0) derTlvCode.length
  sGO : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A + 0xFFFFFE02) derOidCode.length
  sGU : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A + 0xBEB6) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0x18A + 0xBEBE) memcpyBodyCode.length
  sGS : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF30) sliceEqCode.length
  sGL : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF30 + 0xFFFFF776) equalSameLengthCode.length
  sGM : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF30 + 0xC088) memcmpCode.length
  sDP : Sep (d + 8) 8 P isSha256Code.length
  sDC : Sep (d + 8) 8 (P + 0x18A) derAlgorithmCode.length
  sDN : Sep (d + 8) 8 (P + 0x18A + 0xFFFFF7AA) derNestedCode.length
  sDE : Sep (d + 8) 8 (P + 0x18A + 0xFFFFF6CA) derElementCode.length
  sDT : Sep (d + 8) 8 (P + 0x18A + 0xFFFFF6F0) derTlvCode.length
  sDO : Sep (d + 8) 8 (P + 0x18A + 0xFFFFFE02) derOidCode.length
  sDU : Sep (d + 8) 8 (P + 0x18A + 0xBEB6) memcpyStubCode.length
  sDB : Sep (d + 8) 8 (P + 0x18A + 0xBEBE) memcpyBodyCode.length
  sDS : Sep (d + 8) 8 (P + 0xFFFFFF30) sliceEqCode.length
  sDL : Sep (d + 8) 8 (P + 0xFFFFFF30 + 0xFFFFF776) equalSameLengthCode.length
  sDM : Sep (d + 8) 8 (P + 0xFFFFFF30 + 0xC088) memcmpCode.length
  sDG : Sep (d + 8) 8 (sp0 + 0xFFFFFF60) 0xA0
  sRG : Sep p n (sp0 + 0xFFFFFF60) 0xA0
  sRD : Sep p n (d + 8) 8
  sQG : Sep isOid 9 (sp0 + 0xFFFFFF60) 0xA0
  sQD : Sep isOid 9 (d + 8) 8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `tsa::is_sha256`**: with the reader at `d` over the `n`
bytes at `p`, it returns `isSha256Of` of them as a `Result<bool, Error>` in
`a0` and `a1`, and moves the reader past the `AlgorithmIdentifier`. -/
theorem isSha256_correct (m : Machine) {P sp0 d p retAddr : Word} {n : Nat} (env : ISEnv m.mem P sp0 d p n)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = d) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 →
        m'.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) (derElement 0x30 (memBytes m.mem p n)) x) ∧
      match isSha256Of m.mem p n with
      | .error b => reg m' a0 = 1 ∧ reg m' a1 = b.zeroExtend 32
      | .ok v => reg m' a0 = 0 ∧ reg m' a1 = if v then 1 else 0 := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF60 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFD0 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGA := env.sGA; have sGQ := env.sGQ; have sGN := env.sGN; have sGE := env.sGE
  have sGT := env.sGT; have sGO := env.sGO; have sGU := env.sGU; have sGB := env.sGB; have sGS := env.sGS
  have sGL := env.sGL; have sGM := env.sGM; have sDG := env.sDG; have sRG := env.sRG; have sQG := env.sQG
  rw [hG] at sGC sGA sGQ sGN sGE sGT sGO sGU sGB sGS sGL sGM sDG sRG sQG ⊢
  obtain ⟨D, hD⟩ : ∃ D, derAdvance m.mem d p (BitVec.ofNat 32 n) (derElement 0x30 (memBytes m.mem p n)) = D :=
    ⟨_, rfl⟩
  rw [hD]
  show ISResult m retAddr sp0 G D (isSha256Of m.mem p n)
  have hn : n < 2 ^ 32 := by have := env.hpn; omega
  have hGF : G + BitVec.ofNat 32 0x70 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF60) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x70) (by decide)
  have hGw : G.toNat + 0xA0 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF60 : Word).toNat = 4294967136 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x70 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x30 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x70 + k) := fun k => by rw [← hGF, add_ofNat_assoc]
  have eAG : F + 0xFFFFFF90 = G + BitVec.ofNat 32 0 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eS4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x6C := by rw [← hGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0xA0 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0xA0 → d + k ≤ 0xA0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have sepF : ∀ {c n k : Nat}, c + n ≤ k ∨ k + 1 ≤ c → c + n ≤ 0x30 → k < 0x30 →
      Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 k) 1 := fun h h1 h2 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0xA0 b code'.length → (∀ x, Sep G 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have slotC : ∀ (o : Word), 0x1C ≤ o.toNat → o.toNat + 4 ≤ 0x30 → ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x70 + o.toNat) (l := 4) (by omega)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod is_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock isPs) u1 env.cod isSave_end (saveBlock_ok _ isPs _ fun p hp => by
    rw [sp1]
    simp only [isPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) isPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep G 0xA0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside isPs fun p hp => by
      simp only [isPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ isPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [isPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P isSha256Code := cIn env.cod sGC frSv
  have hpsp : ∀ p ∈ isPs, p.1 ≠ sp := by decide
  -- `a0 = (s0 == 0)` and the epilogue, from 0x58
  have fin : ∀ {Mx : Word → BitVec 8} {nm : Machine}, Steps m nm → St Mx P nm 0x58 (reg nm) →
      CodeIn Mx P isSha256Code →
      (∀ k, 0x1C ≤ k → k < 0x30 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg nm sp = F →
      (∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        reg n' a0 = (if reg nm 8 = 0 then 1 else 0) ∧ reg n' a1 = reg nm a1 ∧
        ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q := by
    intro Mx nm S st hc hsl rsp kq
    obtain ⟨n0, d0, u0⟩ := st.aluImm hc is_at_58 (off' := 0x5C) (by decide)
    have rsp0 : upd (reg nm) a0 (aluEval .sltu (reg nm 8) 1) sp = F := by
      rw [upd_ne (by decide) (by decide), rsp]
    have slotW : ∀ r o, (r, o) ∈ isPs → memLoad32 Mx (F + o) = reg m r := fun r o h => by
      have ho : 0x1C ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
        simp only [isPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [← hslv r o h]
      apply memLoad32_congr; intro j hj
      rw [← ofNat_toNat_self o, add_ofNat_assoc, hsl _ (by omega) (by omega)]
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock isPs) u0 hc isRestore_end
      (restoreBlock_ok Mx F isPs _ rsp0 hpsp fun q hq => by
        simp only [isPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mx F isPs _ rsp0 hpsp] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc is_at_66 (off' := 0x68) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc is_at_68
    have rsp1 : restoreRegs Mx F (upd (reg nm) a0 (aluEval .sltu (reg nm 8) 1)) isPs sp = F := by
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
    have hreg : ∀ r o, (r, o) ∈ isPs →
        restoreRegs Mx F (upd (reg nm) a0 (aluEval .sltu (reg nm 8) 1)) isPs r = reg m r := fun r o hm => by
      simp only [isPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact slotW _ _ (by decide)
    have ra1 : restoreRegs Mx F (upd (reg nm) a0 (aluEval .sltu (reg nm 8) 1)) isPs a1 = reg nm a1 := by
      rw [rr _ _ a1 (by decide) (by decide), upd_ne (by decide) (by decide)]
    have ra0 : restoreRegs Mx F (upd (reg nm) a0 (aluEval .sltu (reg nm 8) 1)) isPs a0 =
        if reg nm 8 = 0 then 1 else 0 := by
      rw [rr _ _ a0 (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact is_seqz _
    refine ⟨n3, S.trans (.cons d0 (c1.trans (.cons d2 (.single d3)))), ?_, mem3, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x2C (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; exact ra0
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; exact ra1
    · rw [regs3]
      have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          (q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
            q ≠ a0 ∧ (∀ p ∈ isPs, p.1 ≠ q)) := by decide
      rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, ha, hps⟩
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x2C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x28 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x24 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x20 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x1C (by decide)
      · rw [upd_ne h0 hs, rr _ _ q h0 hps, upd_ne h0 ha]; exact kq q h1
  have done : ∀ {Mx : Word → BitVec 8} {nm : Machine} (R : Except (BitVec 8) Bool), isSha256Of m.mem p n = R →
      Steps m nm → St Mx P nm 0x58 (reg nm) → CodeIn Mx P isSha256Code → (∀ x, Sep G 0xA0 x 1 → Mx x = D x) →
      (∀ k, 0x1C ≤ k → k < 0x30 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg nm sp = F →
      (∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) →
      (match R with
        | .error b => reg nm 8 = 0 ∧ reg nm a1 = b.zeroExtend 32
        | .ok v => reg nm 8 ≠ 0 ∧ reg nm a1 = if v then 1 else 0) →
      ISResult m retAddr sp0 G D (isSha256Of m.mem p n) := by
    intro Mx nm R hR S st hc hM hsl rsp kq hv
    obtain ⟨n', S', pc', mem', sp', a0', a1', k'⟩ := fin S st hc hsl rsp kq
    refine ⟨n', S', pc', sp', k', fun x hx => by rw [mem', hM x hx], ?_⟩
    rw [hR]
    cases R with
    | error b => obtain ⟨h1, h2⟩ := hv; exact ⟨by rw [a0', ite_eq_left h1], by rw [a1', h2]⟩
    | ok v => obtain ⟨h1, h2⟩ := hv; exact ⟨by rw [a0', ite_eq_right h1], by rw [a1', h2]⟩
  -- `Der::algorithm(&mut out, d)` with `out` at `sp`
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add a1 x0 a0, .alu .add a0 x0 sp] u2.self hcS (off' := 0x10) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS is_at_10 is_at_14 (cb := P + 0x18A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x18A (by decide))
  have r4' := PEnv.reg1 regs4 u3.self.zero
  have r3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m3 q = reg m2 q := fun q hv h0 h1 => by
    rw [u3.regs, upd_ne hv h0, upd_ne hv h1]
  have sp4 : reg m4 sp = F := by rw [r4' sp (by decide), r3 sp (by decide) (by decide) (by decide), sp2]
  have a04 : reg m4 a0 = F := by
    rw [r4' a0 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [ev_add, sp2]; exact zw _
  have a14 : reg m4 a1 = d := by
    rw [r4' a1 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [ev_add, r2 a0 (by decide), ha0]; exact zw _
  have hdp : memLoad32 Msv (d + 8) = p := by
    rw [← env.hdp]; exact memLoad32_congr fun j hj => frSv _ (sDG.sub (c := j) (l := 1) (by omega)).symm
  have hdn : memLoad32 Msv (d + 0xC) = BitVec.ofNat 32 n := by
    rw [← env.hdn, show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact frSv _ (sDG.sub (c := 4 + j) (l := 1) (by omega)).symm
  have sOG : Sep F 0x1C (F + 0xFFFFFF90) 0x70 := by
    rw [eAG, ← hGF]; exact offs (c := 0x70) (n := 0x1C) (d := 0) (k := 0x70) (.inr (by omega)) (by omega) (by omega)
  have aenv : AlgEnv Msv (P + 0x18A) F F d p n :=
    { hP := even_at P env.hP 0x18A (by decide), cod := cIn env.alg sGA frSv, seq := cIn env.seq sGQ frSv,
      nst := cIn env.nst sGN frSv, elem := cIn env.elem sGE frSv, tlv := cIn env.tlv sGT frSv,
      oid := cIn env.oid sGO frSv, mcs := cIn env.mcs sGU frSv, mcb := cIn env.mcb sGB frSv,
      hsp := hFa, hS := by omega, hout := hFa, how := by omega, hd := env.hd, hdp := hdp, hdn := hdn,
      hp := env.hp, hpn := env.hpn,
      sGC := by rw [eAG]; exact sGA.sub (by decide), sGQ := by rw [eAG]; exact sGQ.sub (by decide),
      sGN := by rw [eAG]; exact sGN.sub (by decide), sGE := by rw [eAG]; exact sGE.sub (by decide),
      sGT := by rw [eAG]; exact sGT.sub (by decide), sGO := by rw [eAG]; exact sGO.sub (by decide),
      sGU := by rw [eAG]; exact sGU.sub (by decide), sGB := by rw [eAG]; exact sGB.sub (by decide),
      sOC := by rw [← hGF]; exact sGA.sub (by decide), sOB := by rw [← hGF]; exact sGB.sub (by decide),
      sOG := sOG,
      sDC := env.sDC, sDN := env.sDN, sDE := env.sDE, sDT := env.sDT, sDO := env.sDO, sDU := env.sDU,
      sDB := env.sDB, sDG := by rw [eAG]; exact sDG.subR (by decide),
      sOD := by rw [← hGF]; exact sDG.symm.sub (by decide), sRG := by rw [eAG]; exact sRG.subR (by decide),
      sRD := env.sRD }
  obtain ⟨m5, c5, pc5, sp5, k5, fr5, res5⟩ := derAlgorithm_correct m4 (by rw [mem4]; exact aenv) pc4 sp4 a04 a14
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x10 + 8) (by decide)))
  rw [mem4] at fr5 res5
  have eR : ∀ i, i < n → Msv (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun i hi =>
    frSv _ (sRG.sub (c := i) (l := 1) (by omega)).symm
  have eB : memBytes Msv p n = memBytes m.mem p n := by
    have := memBytes_agree eR (c := 0) (l := n) (by omega); rwa [add_ofNat_zero] at this
  rw [derAlgOf_congr eR] at res5
  rw [eB] at fr5
  have M5G : ∀ x, Sep G 0xA0 x 1 → m5.mem x = D x := fun x hx => by
    rw [fr5 x (by rw [eAG]; exact hx.sub (by decide)) (by rw [← hGF]; exact hx.sub (by decide)), ← hD]
    exact derAdvance_pt _ (frSv x hx)
  have M5o : ∀ x, Sep G 0xA0 x 1 → Sep (d + 8) 8 x 1 → m5.mem x = m.mem x := fun x hx hd => by
    rw [M5G x hx, ← hD]; exact derAdvance_outside _ hd
  have slot5 : ∀ k, 0x1C ≤ k → k < 0x30 → m5.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      rw [fr5 _ (by rw [eAG, eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
        (by have := sepF (c := 0) (n := 0x1C) (k := k) (.inl (by omega)) (by decide) h2
            rwa [add_ofNat_zero] at this)]
      exact derAdvance_outside _ (by rw [eFk]; exact sDG.subR (by omega))
  have hc5 : CodeIn m5.mem P isSha256Code := fun i hi => by
    rw [M5o _ (sGC.subR (c := i) (l := 1) (by omega)) (env.sDP.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have u5 : St m5.mem P m5 0x18 (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have sp5' : reg m5 sp = F := sp5
  have K5 : ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    have h : q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ sp := by revert hq; revert q; decide
    rw [k5 q (by revert hq; revert q; decide), r4' q h.1, r3 q h.2.1 h.2.2.1 h.2.2.2.1, r2 q h.2.2.2.2]
  obtain ⟨m6, d6, u6⟩ := u5.lw hc5 is_at_18 (off' := 0x1A) (by decide)
    (by rw [sp5', add_lit_zero]; exact hFa)
  rw [sp5', add_lit_zero] at u6
  have S6 : Steps m m6 := (Steps.cons d1 (c2.trans (c3.trans (c4.trans c5)))).trans (.single d6)
  have r6 : ∀ q, q.val ≠ 0 → q ≠ 8 → reg m6 q = reg m5 q := fun q hv h8 => by rw [u6.regs, upd_ne hv h8]
  have v6 : reg m6 8 = memLoad32 m5.mem F := by rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]
  have sp6 : reg m6 sp = F := by rw [r6 sp (by decide) (by decide), sp5']
  have z6 : reg m6 0 = 0 := u6.self.zero
  have K6 : ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg m6 q = reg m q := fun q hq => by
    rw [r6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact K5 q hq
  rcases hA : derAlgOf m.mem p n with b | ⟨⟨op, ol⟩, r⟩
  · -- `Err(b)`
    rw [hA] at res5
    obtain ⟨h0, hb⟩ := res5
    obtain ⟨m7, d7, u7⟩ := u6.self.taken hc5 0x4C is_at_1a (by decide) (by rw [v6, h0, z6]; rfl)
    obtain ⟨m8, d8, u8⟩ := u7.lbu hc5 is_at_4c (off' := 0x50) (by decide)
    obtain ⟨m9, d9, u9⟩ := u8.jump hc5 is_at_50 (off' := 0x58) (by decide) (by
      rw [u8.pc, show P + BitVec.ofNat 32 0x50 + 0x8 = P + BitVec.ofNat 32 0x58 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x58 (by decide)))
    have k9 : ∀ q, q.val ≠ 0 → q ≠ a1 → reg m9 q = reg m6 q := fun q hv h1 => by rw [u9.regs, upd_ne hv h1]
    exact done (.error b) (by unfold isSha256Of; rw [hA]) (S6.trans (.cons d7 (.cons d8 (.single d9))))
      u9.self hc5 M5G slot5 (by rw [k9 sp (by decide) (by decide), sp6])
      (fun q hq => by
        rw [k9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact K6 q hq)
      ⟨by rw [k9 8 (by decide) (by decide), v6, h0],
        by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp6, hb]⟩
  · have hcom : memLoad32 m5.mem F = op ∧ memLoad32 m5.mem (F + 4) = BitVec.ofNat 32 ol := by
      rw [hA] at res5
      cases r with
      | none => exact ⟨res5.1, res5.2.1⟩
      | some ru => exact ⟨res5.1, res5.2.1⟩
    obtain ⟨c, hop, hcl⟩ := derAlgOf_ok_range hA
    have hop0 : op ≠ 0 := fun h => by
      have h1 := congrArg BitVec.toNat h
      rw [hop, BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at h1
      have := env.hp; have := env.hpn; omega
    obtain ⟨m7, d7, u7⟩ := u6.self.notTaken hc5 0x1C is_at_1a (by decide)
      (by rw [v6, hcom.1, z6]; exact beq_false_of_ne hop0)
    have sp7 : reg m7 sp = F := by rw [u7.regs, sp6]
    obtain ⟨m8, c8, u8⟩ := St.block [.lw a1 sp 0x4, .lw (9 : Fin 32) sp 0x8,
        .lw (18 : Fin 32) sp 0xC, .lbu (19 : Fin 32) sp 0x18, .lui a2 (img% hi20 sha256OidAddress),
        .aluImm .add a2 a2 (img% lo12 sha256OidAddress), .aluImm .add a3 x0 0x9, .alu .add a0 x0 (8 : Fin 32)] u7.self hc5
      (off' := 0x32) (by decide) (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, upd_app, ↓reduceIte, and_true]
        rw [sp7]
        exact ⟨aligned_add hFa (by decide), aligned_add hFa (by decide), aligned_add hFa (by decide)⟩)
    simp only [runBlock, BInstr.run] at u8
    have r7 : ∀ q, reg m7 q = reg m6 q := u7.regs
    have v8 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ 9 → q ≠ 18 → q ≠ 19 →
        reg m8 q = reg m6 q := fun q hv h0 h1 h2 h3 h9 h18 h19 => by
      rw [u8.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2, upd_ne hv h3, upd_ne hv h9, upd_ne hv h18,
        upd_ne hv h19]; exact r7 q
    have a08 : reg m8 a0 = op := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, r7, v6, hcom.1]; exact zw _
    have a18 : reg m8 a1 = BitVec.ofNat 32 ol := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r7, sp6, hcom.2]
    have a28 : reg m8 a2 = isOid := by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
    have a38 : reg m8 a3 = BitVec.ofNat 32 9 := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
    have s18 : reg m8 9 = memLoad32 m5.mem (F + 8) := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r7, sp6]
    have s28 : reg m8 18 = memLoad32 m5.mem (F + 0xC) := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r7, sp6]
    have s38 : reg m8 19 = (m5.mem (F + 0x18)).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r7, sp6]
    have sp8 : reg m8 sp = F := by
      rw [v8 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp6]
    obtain ⟨m9, c9, pc9, mem9, regs9⟩ := u8.self.callRa hc5 is_at_32 is_at_36 (cb := P + 0xFFFFFF30)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFF30 (by decide))
    have r9' := PEnv.reg1 regs9 u8.self.zero
    have sp9 : reg m9 sp = F := by rw [r9' sp (by decide), sp8]
    have cIn5 : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0xA0 b code'.length →
        Sep (d + 8) 8 b code'.length → CodeIn m5.mem b code' := fun hc hs hd i hi => by
      rw [M5o _ (hs.subR (c := i) (l := 1) (by omega)) (hd.subR (c := i) (l := 1) (by omega))]; exact hc i hi
    have hol : ol < 2 ^ 32 := by omega
    obtain ⟨m10, c10, pc10, a010, k10, f10⟩ := sliceEq_correct m9 (base := P + 0xFFFFFF30) (p := op) (q := isOid)
      (pl := ol) (ql := 9) (even_at P env.hP 0xFFFFFF30 (by decide)) (by rw [mem9]; exact cIn5 env.seqq sGS env.sDS)
      (by rw [mem9]; exact cIn5 env.esl sGL env.sDL) (by rw [mem9]; exact cIn5 env.cmp sGM env.sDM) pc9
      (by rw [r9' a0 (by decide), a08]) (by rw [r9' a1 (by decide), a18]) (by rw [r9' a2 (by decide), a28])
      (by rw [r9' a3 (by decide), a38]) hol (by decide) (by rw [regs9]; simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at P env.hP (0x32 + 8) (by decide))) (by rw [sp9]; exact hFa)
      (by rw [sp9, eS4]; exact sGL.sub (by decide)) (by rw [sp9, eS4]; exact sGM.sub (by decide))
      (by rw [sp9, eS4, hop]; exact (sRG.sub (c := c) (l := ol) (by omega)).symm.sub (by decide))
      (by rw [sp9, eS4]; exact sQG.symm.sub (by decide))
    rw [mem9] at a010
    rw [mem9, sp9, eS4] at f10
    have eq1 : memBytes m5.mem op ol = memBytes m.mem op ol := by
      rw [hop]; exact memBytes_congr fun i hi => by
        rw [add_ofNat_assoc]
        exact (M5o _ (sRG.sub (c := c + i) (l := 1) (by omega)).symm
          (env.sRD.sub (c := c + i) (l := 1) (by omega)).symm)
    have eq2 : memBytes m5.mem isOid 9 = sha256OidData := by
      rw [← env.hoid]; exact memBytes_congr fun i hi => by
        exact (M5o _ (sQG.sub (c := i) (l := 1) (by omega)).symm (env.sQD.sub (c := i) (l := 1) (by omega)).symm)
    rw [eq1, eq2] at a010
    have M10G : ∀ x, Sep G 0xA0 x 1 → m10.mem x = D x := fun x hx => by
      rw [f10 x (hx.sub (by decide)), M5G x hx]
    have slot10 : ∀ k, 0x1C ≤ k → k < 0x30 → m10.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
      fun k h1 h2 => by
        rw [f10 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega)), slot5 k h1 h2]
    have hc10 : CodeIn m10.mem P isSha256Code := fun i hi => by
      rw [M10G _ (sGC.subR (c := i) (l := 1) (by omega)), ← hD,
        derAdvance_outside _ (env.sDP.subR (c := i) (l := 1) (by omega))]
      exact env.cod i hi
    have u10 : St m10.mem P m10 0x3A (reg m10) := ⟨by rw [pc10], rfl, fun _ => rfl⟩
    have k10' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m10 q = reg m8 q :=
      fun q hq => by
        rw [k10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
          r9' q (by revert hq; revert q; decide)]
    have sp10 : reg m10 sp = F := by
      rw [k10 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp9]
    have K10 : ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg m10 q = reg m q := fun q hq => by
      rw [k10' q (by revert hq; revert q; decide),
        v8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
      exact K6 q hq
    have o10 : reg m10 8 = op := by rw [k10' 8 (by decide), v8 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), v6, hcom.1]
    have S10 : Steps m m10 := S6.trans (.cons d7 (c8.trans (c9.trans c10)))
    have z10 : reg m10 0 = 0 := u10.zero
    by_cases hm : memBytes m.mem op ol = sha256OidData
    · rw [ite_eq_left hm] at a010
      obtain ⟨m11, d11, u11⟩ := u10.notTaken hc10 0x3C is_at_3a (by decide) (by rw [a010, z10]; rfl)
      have s110 : reg m10 9 = memLoad32 m5.mem (F + 8) := by rw [k10' 9 (by decide), s18]
      cases r with
      | none =>
        rw [hA] at res5
        obtain ⟨m12, d12, u12⟩ := u11.taken hc10 0x56 is_at_3c (by decide) (by rw [s110, res5.2.2, z10]; rfl)
        obtain ⟨m13, d13, u13⟩ := u12.aluImm hc10 is_at_56 (off' := 0x58) (by decide)
        have k13 : ∀ q, q.val ≠ 0 → q ≠ a1 → reg m13 q = reg m10 q := fun q hv h1 => by rw [u13.regs, upd_ne hv h1]
        exact done (.ok true) (by unfold isSha256Of; rw [hA]; show Except.ok (decide _) = _; rw [decide_eq_true hm])
          (S10.trans (.cons d11 (.cons d12 (.single d13)))) u13.self hc10 M10G slot10
          (by rw [k13 sp (by decide) (by decide), sp10])
          (fun q hq => by
            rw [k13 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact K10 q hq)
          ⟨by rw [k13 8 (by decide) (by decide), o10]; exact hop0,
            by rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z10]; rfl⟩
      | some ru =>
        obtain ⟨rp, u⟩ := ru
        rw [hA] at res5
        obtain ⟨c', hrp, hcu⟩ := derAlgOf_some_range hA
        have hs1 : rp + BitVec.ofNat 32 u.header ≠ 0 := fun h => by
          have h1 := congrArg BitVec.toNat h
          rw [hrp, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show (0 : Word).toNat = 0 from rfl] at h1
          have := env.hp; have := env.hpn; omega
        obtain ⟨m12, d12, u12⟩ := u11.notTaken hc10 0x3E is_at_3c (by decide)
          (by rw [s110, res5.2.2.1, z10]; exact beq_false_of_ne hs1)
        obtain ⟨m13, c13, u13⟩ := St.block [.aluImm .xor a0 (19 : Fin 32) 0x5, .alu .or a0 a0 (18 : Fin 32),
            .aluImm .sltu a1 a0 0x1] u12 hc10 (off' := 0x4A) (by decide) (by simp [BlockOk, BInstr.ok])
        simp only [runBlock, BInstr.run] at u13
        obtain ⟨m14, d14, u14⟩ := u13.jump hc10 is_at_4a (off' := 0x58) (by decide) (by
          rw [u13.pc, show P + BitVec.ofNat 32 0x4A + 0xE = P + BitVec.ofNat 32 0x58 by rw [BitVec.add_assoc]; rfl]
          exact even_bit0 (even_at P env.hP 0x58 (by decide)))
        have k14 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m14 q = reg m10 q := fun q hv h0 h1 => by
          rw [u14.regs, upd_ne hv h1, upd_ne hv h0, upd_ne hv h0]
        have a1v : reg m14 a1 =
            if ((BitVec.ofNat 8 u.tag).zeroExtend 32 ^^^ 5) ||| BitVec.ofNat 32 u.len = 0 then 1 else 0 := by
          rw [u14.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [is_seqz, ev_or, ev_xor, k10' 19 (by decide), s38, k10' 18 (by decide), s28, res5.2.2.2.1,
            res5.2.2.2.2.2.2]
        have hu : u.len < 2 ^ 32 := by omega
        have hv : ((BitVec.ofNat 8 u.tag).zeroExtend 32 ^^^ 5) ||| BitVec.ofNat 32 u.len = 0 ↔
            (memBytes m.mem op ol = sha256OidData ∧ u.tag % 256 = 5 ∧ u.len = 0) := by
          rw [is_or0, is_tag5]
          have e8 : BitVec.ofNat 8 u.tag = 5 ↔ u.tag % 256 = 5 := by
            constructor
            · intro h; have h2 := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at h2
              have : (5 : BitVec 8).toNat = 5 := rfl; omega
            · intro h; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact h)
          have e32 : BitVec.ofNat 32 u.len = 0 ↔ u.len = 0 := by
            constructor
            · intro h; have h2 := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at h2
              have : (0 : Word).toNat = 0 := rfl; omega
            · intro h; rw [h]; rfl
          rw [e8, e32]
          exact ⟨fun h => ⟨hm, h⟩, fun h => h.2⟩
        refine done (.ok (decide (memBytes m.mem op ol = sha256OidData ∧ u.tag % 256 = 5 ∧ u.len = 0)))
          (by unfold isSha256Of; rw [hA]) (S10.trans (.cons d11 (.cons d12 (c13.trans (.single d14)))))
          u14.self hc10 M10G slot10 (by rw [k14 sp (by decide) (by decide) (by decide), sp10])
          (fun q hq => by
            rw [k14 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
              (by revert hq; revert q; decide)]
            exact K10 q hq)
          ⟨by rw [k14 8 (by decide) (by decide) (by decide), o10]; exact hop0, ?_⟩
        rw [a1v]
        by_cases hP : memBytes m.mem op ol = sha256OidData ∧ u.tag % 256 = 5 ∧ u.len = 0
        · rw [ite_eq_left (hv.mpr hP), decide_eq_true hP]; rfl
        · rw [ite_eq_right (fun h => hP (hv.mp h)), decide_eq_false hP]; rfl
    · rw [ite_eq_right hm] at a010
      obtain ⟨m11, d11, u11⟩ := u10.taken hc10 0x52 is_at_3a (by decide) (by rw [a010, z10]; rfl)
      obtain ⟨m12, d12, u12⟩ := u11.aluImm hc10 is_at_52 (off' := 0x54) (by decide)
      obtain ⟨m13, d13, u13⟩ := u12.jump hc10 is_at_54 (off' := 0x58) (by decide) (by
        rw [u12.pc, show P + BitVec.ofNat 32 0x54 + 0x4 = P + BitVec.ofNat 32 0x58 by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x58 (by decide)))
      have k13 : ∀ q, q.val ≠ 0 → q ≠ a1 → reg m13 q = reg m10 q := fun q hv h1 => by rw [u13.regs, upd_ne hv h1]
      have hR : isSha256Of m.mem p n = .ok false := by
        unfold isSha256Of; rw [hA]
        cases r with
        | none => show Except.ok (decide _) = _; rw [decide_eq_false hm]
        | some ru =>
          obtain ⟨rp, u⟩ := ru
          show Except.ok (decide _) = _; rw [decide_eq_false (fun h => hm h.1)]
      exact done (.ok false) hR (S10.trans (.cons d11 (.cons d12 (.single d13)))) u13.self hc10 M10G slot10
        (by rw [k13 sp (by decide) (by decide), sp10])
        (fun q hq => by
          rw [k13 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact K10 q hq)
        ⟨by rw [k13 8 (by decide) (by decide), o10]; exact hop0,
          by rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z10]; rfl⟩

end C3.RV32
