import C3BootProofs.Proofs.EcdsaSig
import C3BootProofs.Proofs.DerOptional

/-!
# `Der::algorithm`, as compiled

`Der::algorithm` reads an `AlgorithmIdentifier`: a `SEQUENCE` through the
proved `Der::sequence`, whose reader it rebuilds on its stack with an 11-byte
`memcpy`, then the `OBJECT IDENTIFIER` through the proved `Der::oid`, then, if
bytes remain, one element of parameters through the proved `Der::tlv`, which
must end the `SEQUENCE`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem alg_at_0 : fetchRel derAlgorithmCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem alg_at_2 : fetchRel derAlgorithmCode 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem alg_at_4 : fetchRel derAlgorithmCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem alg_at_6 : fetchRel derAlgorithmCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem alg_at_8 : fetchRel derAlgorithmCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem alg_at_a : fetchRel derAlgorithmCode 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem alg_at_c : fetchRel derAlgorithmCode 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem alg_at_e : fetchRel derAlgorithmCode 0xE = some (.store .sw sp (21 : Fin 32) 0x34, 2) := by decide
theorem alg_at_10 : fetchRel derAlgorithmCode 0x10 = some (.alu .add (21 : Fin 32) x0 a0, 2) := by decide
theorem alg_at_12 : fetchRel derAlgorithmCode 0x12 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem alg_at_14 : fetchRel derAlgorithmCode 0x14 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem alg_at_18 : fetchRel derAlgorithmCode 0x18 = some (.jalr ra ra 0x6C, 4) := by decide
theorem alg_at_1c : fetchRel derAlgorithmCode 0x1C = some (.load .lw (8 : Fin 32) sp 0x20, 2) := by decide
theorem alg_at_1e : fetchRel derAlgorithmCode 0x1E = some (.load .lbu (9 : Fin 32) sp 0x24, 4) := by decide
theorem alg_at_22 : fetchRel derAlgorithmCode 0x22 = some (.branch .beq (8 : Fin 32) x0 0x60, 2) := by decide
theorem alg_at_24 : fetchRel derAlgorithmCode 0x24 = some (.aluImm .add a1 sp 0x25, 4) := by decide
theorem alg_at_28 : fetchRel derAlgorithmCode 0x28 = some (.aluImm .add a0 sp 0x5, 4) := by decide
theorem alg_at_2c : fetchRel derAlgorithmCode 0x2C = some (.aluImm .add a2 x0 0xB, 2) := by decide
theorem alg_at_2e : fetchRel derAlgorithmCode 0x2E = some (.auipc ra 0xA000, 4) := by decide
theorem alg_at_32 : fetchRel derAlgorithmCode 0x32 = some (.jalr ra ra 0x348, 4) := by decide
theorem alg_at_36 : fetchRel derAlgorithmCode 0x36 = some (.store .sw sp (8 : Fin 32) 0x0, 2) := by decide
theorem alg_at_38 : fetchRel derAlgorithmCode 0x38 = some (.store .sb sp (9 : Fin 32) 0x4, 4) := by decide
theorem alg_at_3c : fetchRel derAlgorithmCode 0x3C = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem alg_at_3e : fetchRel derAlgorithmCode 0x3E = some (.alu .add a1 x0 sp, 2) := by decide
theorem alg_at_40 : fetchRel derAlgorithmCode 0x40 = some (.auipc ra 0x0, 4) := by decide
theorem alg_at_44 : fetchRel derAlgorithmCode 0x44 = some (.jalr ra ra 0x9A, 4) := by decide
theorem alg_at_48 : fetchRel derAlgorithmCode 0x48 = some (.load .lw (9 : Fin 32) sp 0x20, 2) := by decide
theorem alg_at_4a : fetchRel derAlgorithmCode 0x4A = some (.branch .beq (9 : Fin 32) x0 0x42, 2) := by decide
theorem alg_at_4c : fetchRel derAlgorithmCode 0x4C = some (.load .lw a0 sp 0xC, 2) := by decide
theorem alg_at_4e : fetchRel derAlgorithmCode 0x4E = some (.load .lw (18 : Fin 32) sp 0x24, 2) := by decide
theorem alg_at_50 : fetchRel derAlgorithmCode 0x50 = some (.branch .beq a0 x0 0x4A, 2) := by decide
theorem alg_at_52 : fetchRel derAlgorithmCode 0x52 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem alg_at_54 : fetchRel derAlgorithmCode 0x54 = some (.alu .add a1 x0 sp, 2) := by decide
theorem alg_at_56 : fetchRel derAlgorithmCode 0x56 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem alg_at_5a : fetchRel derAlgorithmCode 0x5A = some (.jalr ra ra 0x1E8, 4) := by decide
theorem alg_at_5e : fetchRel derAlgorithmCode 0x5E = some (.load .lw (20 : Fin 32) sp 0x20, 2) := by decide
theorem alg_at_60 : fetchRel derAlgorithmCode 0x60 = some (.load .lbu (19 : Fin 32) sp 0x24, 4) := by decide
theorem alg_at_64 : fetchRel derAlgorithmCode 0x64 = some (.branch .beq (20 : Fin 32) x0 0x5C, 4) := by decide
theorem alg_at_68 : fetchRel derAlgorithmCode 0x68 = some (.aluImm .add a1 sp 0x25, 4) := by decide
theorem alg_at_6c : fetchRel derAlgorithmCode 0x6C = some (.aluImm .add a0 sp 0x11, 4) := by decide
theorem alg_at_70 : fetchRel derAlgorithmCode 0x70 = some (.aluImm .add a2 x0 0xF, 2) := by decide
theorem alg_at_72 : fetchRel derAlgorithmCode 0x72 = some (.auipc ra 0xA000, 4) := by decide
theorem alg_at_76 : fetchRel derAlgorithmCode 0x76 = some (.jalr ra ra 0x304, 4) := by decide
theorem alg_at_7a : fetchRel derAlgorithmCode 0x7A = some (.load .lw a0 sp 0xC, 2) := by decide
theorem alg_at_7c : fetchRel derAlgorithmCode 0x7C = some (.branch .beq a0 x0 0x20, 2) := by decide
theorem alg_at_7e : fetchRel derAlgorithmCode 0x7E = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem alg_at_80 : fetchRel derAlgorithmCode 0x80 = some (.jal x0 0x10, 2) := by decide
theorem alg_at_82 : fetchRel derAlgorithmCode 0x82 = some (.store .sw (21 : Fin 32) x0 0x0, 4) := by decide
theorem alg_at_86 : fetchRel derAlgorithmCode 0x86 = some (.store .sb (21 : Fin 32) (9 : Fin 32) 0x4, 4) := by decide
theorem alg_at_8a : fetchRel derAlgorithmCode 0x8A = some (.jal x0 0x3E, 2) := by decide
theorem alg_at_8c : fetchRel derAlgorithmCode 0x8C = some (.load .lbu a0 sp 0x24, 4) := by decide
theorem alg_at_90 : fetchRel derAlgorithmCode 0x90 = some (.store .sw (21 : Fin 32) x0 0x0, 4) := by decide
theorem alg_at_94 : fetchRel derAlgorithmCode 0x94 = some (.store .sb (21 : Fin 32) a0 0x4, 4) := by decide
theorem alg_at_98 : fetchRel derAlgorithmCode 0x98 = some (.jal x0 0x30, 2) := by decide
theorem alg_at_9a : fetchRel derAlgorithmCode 0x9A = some (.aluImm .add (20 : Fin 32) x0 0x0, 2) := by decide
theorem alg_at_9c : fetchRel derAlgorithmCode 0x9C = some (.aluImm .add a0 (21 : Fin 32) 0xD, 4) := by decide
theorem alg_at_a0 : fetchRel derAlgorithmCode 0xA0 = some (.aluImm .add a1 sp 0x11, 4) := by decide
theorem alg_at_a4 : fetchRel derAlgorithmCode 0xA4 = some (.aluImm .add a2 x0 0xF, 2) := by decide
theorem alg_at_a6 : fetchRel derAlgorithmCode 0xA6 = some (.auipc ra 0xA000, 4) := by decide
theorem alg_at_aa : fetchRel derAlgorithmCode 0xAA = some (.jalr ra ra 0x2D0, 4) := by decide
theorem alg_at_ae : fetchRel derAlgorithmCode 0xAE = some (.store .sw (21 : Fin 32) (9 : Fin 32) 0x0, 4) := by decide
theorem alg_at_b2 : fetchRel derAlgorithmCode 0xB2 = some (.store .sw (21 : Fin 32) (18 : Fin 32) 0x4, 4) := by decide
theorem alg_at_b6 : fetchRel derAlgorithmCode 0xB6 = some (.store .sw (21 : Fin 32) (20 : Fin 32) 0x8, 4) := by decide
theorem alg_at_ba : fetchRel derAlgorithmCode 0xBA = some (.store .sb (21 : Fin 32) (19 : Fin 32) 0xC, 4) := by decide
theorem alg_at_be : fetchRel derAlgorithmCode 0xBE = some (.jal x0 0xA, 2) := by decide
theorem alg_at_c0 : fetchRel derAlgorithmCode 0xC0 = some (.store .sw (21 : Fin 32) x0 0x0, 4) := by decide
theorem alg_at_c4 : fetchRel derAlgorithmCode 0xC4 = some (.store .sb (21 : Fin 32) (19 : Fin 32) 0x4, 4) := by decide
theorem alg_at_c8 : fetchRel derAlgorithmCode 0xC8 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem alg_at_ca : fetchRel derAlgorithmCode 0xCA = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem alg_at_cc : fetchRel derAlgorithmCode 0xCC = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem alg_at_ce : fetchRel derAlgorithmCode 0xCE = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem alg_at_d0 : fetchRel derAlgorithmCode 0xD0 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem alg_at_d2 : fetchRel derAlgorithmCode 0xD2 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem alg_at_d4 : fetchRel derAlgorithmCode 0xD4 = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem alg_at_d6 : fetchRel derAlgorithmCode 0xD6 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem alg_at_d8 : fetchRel derAlgorithmCode 0xD8 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem derOid_ok_elem {L : Bytes} {o : DerTlv} (h : derOid L = .ok o) : derElement 6 L = .ok o := by
  unfold derOid at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h; exact ht
    · cases h

/-- `Der::algorithm`'s result for the reader whose unread bytes are the `n` at
`p`: the error byte, or the OID's contents and the parameters' element. -/
def derAlgOf (M : Word → BitVec 8) (p : Word) (n : Nat) :
    Except (BitVec 8) ((Word × Nat) × Option (Word × DerTlv)) :=
  match derElement 0x30 (memBytes M p n) with
  | .error e => .error (derErrByte e)
  | .ok t =>
    match derOid (memBytes M (p + BitVec.ofNat 32 t.header) t.len) with
    | .error e => .error (derErrByte e)
    | .ok o =>
      if t.len - (o.header + o.len) = 0 then
        .ok ((p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header, o.len), none)
      else
        match derTlv (memBytes M (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len))
            (t.len - (o.header + o.len))) with
        | .error e => .error (derErrByte e)
        | .ok u =>
          if u.header + u.len = t.len - (o.header + o.len) then
            .ok ((p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header, o.len),
              some (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len), u))
          else .error 1

theorem oidMem_outside {M : Word → BitVec 8} {out rp x : Word} (R : Except DerError DerTlv)
    (hx : Sep out 8 x 1) : derOidMem M out rp R x = M x := by
  have h0 : Sep out 4 x 1 := by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  cases R with
  | error e =>
    simp only [derOidMem]
    rw [memStore8_ne fun e' => hx.point (i := 4) (j := 0) (by decide) (by decide)
      (by rw [add_ofNat_zero]; exact e'.symm), memStore32_get_sep h0]
  | ok t =>
    simp only [derOidMem]
    rw [memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)), memStore32_get_sep h0]

theorem oidMem_err {M : Word → BitVec 8} {out rp : Word} (e : DerError) :
    memLoad32 (derOidMem M out rp (.error e)) out = 0 ∧ derOidMem M out rp (.error e) (out + 4) = derErrByte e := by
  simp only [derOidMem]
  refine ⟨?_, memStore8_same _ _ _⟩
  rw [memLoad32_store8_sep (sep_offsets out (c := 4) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide)
    (by decide) |> fun h => by rwa [add_ofNat_zero] at h), memLoad32_store32_same]

theorem oidMem_ok {M : Word → BitVec 8} {out rp : Word} (t : DerTlv) :
    memLoad32 (derOidMem M out rp (.ok t)) out = rp + BitVec.ofNat 32 t.header ∧
    memLoad32 (derOidMem M out rp (.ok t)) (out + 4) = BitVec.ofNat 32 t.len := by
  simp only [derOidMem]
  refine ⟨?_, memLoad32_store32_same _ _ _⟩
  have h : Sep (out + 4) 4 out 4 := (sep_off0 out (d := 4) (k := 4) (by decide) (by decide)).symm
  rw [memLoad32_store32_sep (a := out + 4) (b := out) h, memLoad32_store32_same]

theorem derTlvMem_ok8 {M : Word → BitVec 8} {o d rp rl : Word} (t : DerTlv) :
    memLoad32 (derTlvMem M o d rp rl (.ok t)) (o + 8) = rp := by
  simp only [derTlvMem]
  rw [show o + 4 = o + BitVec.ofNat 32 4 from rfl, show o + 8 = o + BitVec.ofNat 32 8 from rfl,
    show o + 0xC = o + BitVec.ofNat 32 0xC from rfl, show o + 0x10 = o + BitVec.ofNat 32 0x10 from rfl]
  rw [memLoad32_store8_sep (sep_offsets o (c := 0x10) (n := 1) (d := 8) (k := 4) (.inr (by decide)) (by decide)
      (by decide)),
    memLoad32_store32_sep (sep_offsets o (c := 0xC) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide)
      (by decide)),
    memLoad32_store32_same]

theorem derTlvMem_okC {M : Word → BitVec 8} {o d rp rl : Word} (t : DerTlv) :
    memLoad32 (derTlvMem M o d rp rl (.ok t)) (o + 0xC) = BitVec.ofNat 32 (t.header + t.len) := by
  simp only [derTlvMem]
  rw [show o + 0xC = o + BitVec.ofNat 32 0xC from rfl, show o + 0x10 = o + BitVec.ofNat 32 0x10 from rfl]
  rw [memLoad32_store8_sep (sep_offsets o (c := 0x10) (n := 1) (d := 0xC) (k := 4) (.inr (by decide)) (by decide)
      (by decide)), memLoad32_store32_same]

theorem derTlvMem_ok10 {M : Word → BitVec 8} {o d rp rl : Word} (t : DerTlv) :
    derTlvMem M o d rp rl (.ok t) (o + 0x10) = BitVec.ofNat 8 t.tag := by
  simp only [derTlvMem]; rw [memStore8_same]

abbrev algPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), ((8 : Fin 32), 0x48), ((9 : Fin 32), 0x44), ((18 : Fin 32), 0x40), ((19 : Fin 32), 0x3C),
   ((20 : Fin 32), 0x38), ((21 : Fin 32), 0x34)]

section
set_option maxRecDepth 20000
theorem algSave_end : blockEnd derAlgorithmCode 2 (saveBlock algPs) = some 0x10 := by decide
theorem algRestore_end : blockEnd derAlgorithmCode 0xC8 (restoreBlock algPs) = some 0xD6 := by decide
end

/-- Where `Der::algorithm` runs: its code and its callees', the 0x70 bytes of
stack below `sp0`, the 28-byte result at `out`, the reader at `d`, and the
`n` unread bytes at `p`, apart from what each must not touch. -/
structure AlgEnv (M : Word → BitVec 8) (P sp0 out d p : Word) (n : Nat) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P derAlgorithmCode
  seq : CodeIn M (P + 0xFFFFF532) derSequenceCode
  nst : CodeIn M (P + 0xFFFFF7AA) derNestedCode
  elem : CodeIn M (P + 0xFFFFF6CA) derElementCode
  tlv : CodeIn M (P + 0xFFFFF6F0) derTlvCode
  oid : CodeIn M (P + 0xFFFFFE02) derOidCode
  mcs : CodeIn M (P + 0xBEB6) memcpyStubCode
  mcb : CodeIn M (P + 0xBEBE) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x70 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  how : out.toNat + 0x1C < 2 ^ 32
  hd : d.toNat % 4 = 0
  hdp : memLoad32 M (d + 8) = p
  hdn : memLoad32 M (d + 0xC) = BitVec.ofNat 32 n
  hp : 0 < p.toNat
  hpn : p.toNat + n < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF90) 0x70 P derAlgorithmCode.length
  sGQ : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xFFFFF532) derSequenceCode.length
  sGN : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xFFFFF7AA) derNestedCode.length
  sGE : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xFFFFF6CA) derElementCode.length
  sGT : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xFFFFF6F0) derTlvCode.length
  sGO : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xFFFFFE02) derOidCode.length
  sGU : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xBEB6) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xBEBE) memcpyBodyCode.length
  sOC : Sep out 0x1C P derAlgorithmCode.length
  sOB : Sep out 0x1C (P + 0xBEBE) memcpyBodyCode.length
  sOG : Sep out 0x1C (sp0 + 0xFFFFFF90) 0x70
  sDC : Sep (d + 8) 8 P derAlgorithmCode.length
  sDN : Sep (d + 8) 8 (P + 0xFFFFF7AA) derNestedCode.length
  sDE : Sep (d + 8) 8 (P + 0xFFFFF6CA) derElementCode.length
  sDT : Sep (d + 8) 8 (P + 0xFFFFF6F0) derTlvCode.length
  sDO : Sep (d + 8) 8 (P + 0xFFFFFE02) derOidCode.length
  sDU : Sep (d + 8) 8 (P + 0xBEB6) memcpyStubCode.length
  sDB : Sep (d + 8) 8 (P + 0xBEBE) memcpyBodyCode.length
  sDG : Sep (d + 8) 8 (sp0 + 0xFFFFFF90) 0x70
  sOD : Sep out 0x1C (d + 8) 8
  sRG : Sep p n (sp0 + 0xFFFFFF90) 0x70
  sRD : Sep p n (d + 8) 8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `Der::algorithm`**: with the reader at `d` over the `n`
unread bytes at `p`, it stores `derAlgOf` of them in its
`Result<(&[u8], Option<Tlv>), Error>` at `out`, and moves the reader past the
`SEQUENCE` it read. -/
theorem derAlgorithm_correct (m : Machine) {P sp0 out d p retAddr : Word} {n : Nat}
    (env : AlgEnv m.mem P sp0 out d p n) (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = d) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF90) 0x70 x 1 → Sep out 0x1C x 1 →
        m'.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) (derElement 0x30 (memBytes m.mem p n)) x) ∧
      match derAlgOf m.mem p n with
      | .error b => memLoad32 m'.mem out = 0 ∧ m'.mem (out + 4) = b
      | .ok ((op, ol), none) => memLoad32 m'.mem out = op ∧ memLoad32 m'.mem (out + 4) = BitVec.ofNat 32 ol ∧
          memLoad32 m'.mem (out + 8) = 0
      | .ok ((op, ol), some (rp, u)) => memLoad32 m'.mem out = op ∧
          memLoad32 m'.mem (out + 4) = BitVec.ofNat 32 ol ∧
          memLoad32 m'.mem (out + 8) = rp + BitVec.ofNat 32 u.header ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 u.len ∧ memLoad32 m'.mem (out + 0x10) = rp ∧
          memLoad32 m'.mem (out + 0x14) = BitVec.ofNat 32 (u.header + u.len) ∧
          m'.mem (out + 0x18) = BitVec.ofNat 8 u.tag := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF90 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFB0 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGQ := env.sGQ; have sGN := env.sGN; have sGE := env.sGE; have sGT := env.sGT
  have sGO := env.sGO; have sGU := env.sGU; have sGB := env.sGB; have sOG := env.sOG; have sDG := env.sDG
  have sRG := env.sRG
  rw [hG] at sGC sGQ sGN sGE sGT sGO sGU sGB sOG sDG sRG ⊢
  have hn : n < 2 ^ 32 := by have := env.hpn; omega
  have hGF : G + BitVec.ofNat 32 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF90) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x20) (by decide)
  have hGw : G.toNat + 0x70 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF90 : Word).toNat = 4294967184 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x20 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x50 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by rw [← hGF, add_ofNat_assoc]
  have eNF : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eSc : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x10 := by rw [← hGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x70 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x70 → d + k ≤ 0x70 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have sFk : ∀ {b : Word} {l : Nat} (c k : Nat), c + k ≤ 0x50 → Sep G 0x70 b l →
      Sep (F + BitVec.ofNat 32 c) k b l := fun c k h hs => by rw [eFk]; exact hs.sub (by omega)
  have sepF : ∀ {c n k : Nat}, c + n ≤ k ∨ k + 1 ≤ c → c + n ≤ 0x50 → k < 0x50 →
      Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 k) 1 := fun h h1 h2 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x70 b code'.length → (∀ x, Sep G 0x70 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have slotC : ∀ (o : Word), 0x34 ≤ o.toNat → o.toNat + 4 ≤ 0x50 → ∀ {b : Word} {l : Nat}, Sep G 0x70 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x20 + o.toNat) (l := 4) (by omega)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod alg_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock algPs) u1 env.cod algSave_end (saveBlock_ok _ algPs _ fun p hp => by
    rw [sp1]
    simp only [algPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) algPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep G 0x70 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside algPs fun p hp => by
      simp only [algPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact slotC _ (by decide) (by decide) hx
  have frLo : ∀ k, k < 0x34 → Msv (F + BitVec.ofNat 32 k) = m.mem (F + BitVec.ofNat 32 k) := fun k hk => by
    rw [← hMsv]
    exact saveMem_outside algPs fun p hp => by
      simp only [algPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact sep_offsets F (.inr (by simp; omega)) (by simp) (by omega)
  have hslv : ∀ r o, (r, o) ∈ algPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [algPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P derAlgorithmCode := cIn env.cod sGC frSv
  have hpsp : ∀ p ∈ algPs, p.1 ≠ sp := by decide
  -- the epilogue, from 0xC8
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m n → St Mx P n 0xC8 (reg n) →
      CodeIn Mx P derAlgorithmCode →
      (∀ k, 0x34 ≤ k → k < 0x50 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg n sp = F →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q := by
    intro Mx n S st hc hsl rsp kq
    have slotW : ∀ r o, (r, o) ∈ algPs → memLoad32 Mx (F + o) = reg m r := fun r o h => by
      have ho : 0x34 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x50 := by
        simp only [algPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [← hslv r o h]
      apply memLoad32_congr; intro j hj
      rw [← ofNat_toNat_self o, add_ofNat_assoc, hsl _ (by omega) (by omega)]
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock algPs) st hc algRestore_end
      (restoreBlock_ok Mx F algPs (reg n) rsp hpsp fun q hq => by
        simp only [algPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mx F algPs (reg n) rsp hpsp] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc alg_at_d6 (off' := 0xD8) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc alg_at_d8
    have rsp1 : restoreRegs Mx F (reg n) algPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs Mx F f ps q = f q := by
      intro f ps q h0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
    have hreg : ∀ r o, (r, o) ∈ algPs → restoreRegs Mx F (reg n) algPs r = reg m r := fun r o hm => by
      simp only [algPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact slotW _ _ (by decide)
    refine ⟨n3, S.trans (c1.trans (.cons d2 (.single d3))), ?_, mem3, ?_, fun q hq => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x4C (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
    · rw [regs3]
      have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ (q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
            (∀ p ∈ algPs, p.1 ≠ q)) := by decide
      rcases key q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x4C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x48 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x44 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x40 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x3C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x38 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x34 (by decide)
      · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kq q h1
  -- `Der::sequence` with the result at `sp + 0x20` and the caller's reader
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (21 : Fin 32) x0 a0, .aluImm .add a0 sp 0x20] u2.self hcS
    (off' := 0x14) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ (21 : Fin 32) → reg m3 q = reg m2 q := fun q hv h0 h21 => by
    rw [u3.regs, upd_ne hv h0, upd_ne hv h21]
  have s21_3 : reg m3 21 = out := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero, r2 a0 (by decide), ha0]; exact zw out
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS alg_at_14 alg_at_18 (cb := P + 0xFFFFF532)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF532 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have sp4 : reg m4 sp = F := by
    rw [r4 sp (by decide), k3 sp (by decide) (by decide) (by decide), sp2]
  have lP : memLoad32 Msv (d + 8) = p := by
    rw [← env.hdp]; exact memLoad32_congr fun j hj => frSv _ (sDG.sub (c := j) (l := 1) (by omega)).symm
  have lN : memLoad32 Msv (d + 0xC) = BitVec.ofNat 32 n := by
    rw [← env.hdn, show d + 0xC = d + 8 + 4 by rw [BitVec.add_assoc]; rfl]
    exact memLoad32_congr fun j hj => frSv _ (by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
      exact (sDG.sub (c := 4 + j) (l := 1) (by omega)).symm)
  have eN : P + 0xFFFFF532 + 0x278 = P + 0xFFFFF7AA := by rw [BitVec.add_assoc]; rfl
  have hNE : NestEnv m4.mem (P + 0xFFFFF532 + 0x278) F (F + 0x20) d := by
    rw [mem4, eN]
    refine ⟨even_at P env.hP 0xFFFFF7AA (by decide), cIn env.nst sGN frSv,
      by rw [BitVec.add_assoc]; exact cIn env.elem sGE frSv, by rw [BitVec.add_assoc]; exact cIn env.tlv sGT frSv,
      hFa, by omega, aligned_add hFa (k := 0x20) (by decide), env.hd,
      by rw [eNF]; exact sGN.sub (by decide),
      by rw [eNF, BitVec.add_assoc]; exact sGE.sub (by decide),
      by rw [eNF, BitVec.add_assoc]; exact sGT.sub (by decide),
      sFk 0x20 16 (by decide) sGN, env.sDN, by rw [BitVec.add_assoc]; exact env.sDT,
      by rw [eNF, show F + 0x20 = F + BitVec.ofNat 32 0x20 from rfl, eFk]
         exact offs (.inr (by decide)) (by decide) (by decide),
      by rw [eNF]; exact sDG.subR (by decide),
      by rw [lP, lN, ofNat_tn hn, eNF]; exact sRG.subR (by decide),
      by rw [lP]; exact env.hp,
      by rw [lP, lN, ofNat_tn hn]; exact env.hpn⟩
  obtain ⟨m5, c5, pc5, sp5, k5, f5⟩ := derSequence_correct m4 (even_at P env.hP 0xFFFFF532 (by decide))
    (by rw [mem4]; exact cIn env.seq sGQ frSv) hNE pc4 sp4
    (by rw [r4 a0 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r4 a1 (by decide), k3 a1 (by decide) (by decide) (by decide), r2 a1 (by decide), ha1])
    (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x14 + 8) (by decide)))
  have eL : memBytes Msv p n = memBytes m.mem p n :=
    memBytes_congr fun i hi => frSv _ (sRG.sub (c := i) (l := 1) (by omega)).symm
  rw [mem4, lP, lN, ofNat_tn hn, eL] at f5
  generalize hR : derElement 0x30 (memBytes m.mem p n) = R at f5
  have S5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  have K5 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    have ho : oidKeep q = true := by revert hq; revert q; decide
    have h : q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ (21 : Fin 32) ∧ q ≠ sp := by revert hq; revert q; decide
    rw [k5 q ho, r4 q h.1, k3 q h.2.1 h.2.2.1 h.2.2.2.1, r2 q h.2.2.2.2]
  have s21_5 : reg m5 21 = out := by
    rw [k5 21 (by decide), r4 21 (by decide), s21_3]
  -- memory after `Der::sequence`: the reader moved, the result in the frame
  have memN : ∀ x, Sep G 0x70 x 1 → m5.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) R x := fun x hx => by
    rw [f5 x (by rw [eNF]; exact hx.sub (by decide)),
      nestedMem_outside (out := F + 0x20) R (sFk 0x20 16 (by decide) hx)]
    exact derAdvance_pt R (frSv x hx)
  have cN : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x70 b code'.length →
      Sep (d + 8) 8 b code'.length → CodeIn m5.mem b code' := fun hc hs hd i hi => by
    rw [memN _ (hs.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside R (hd.subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have hc5 := cN env.cod sGC env.sDC
  have f5k : ∀ k, k < 0x50 → m5.mem (F + BitVec.ofNat 32 k) =
      derNestedMem (derAdvance Msv d p (BitVec.ofNat 32 n) R) (F + 0x20) p R (F + BitVec.ofNat 32 k) :=
    fun k hk => f5 _ (by rw [eNF, eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
  have slot5 : ∀ j, 0x34 ≤ j → j < 0x50 → m5.mem (F + BitVec.ofNat 32 j) = Msv (F + BitVec.ofNat 32 j) :=
    fun j h1 h2 => by
      rw [f5k j h2, nestedMem_outside (out := F + 0x20) R (sepF (c := 0x20) (n := 16) (.inl (by omega)) (by omega) h2),
        derAdvance_outside R (by
          rw [eFk]; exact (sDG.subR (c := 0x20 + j) (l := 1) (by omega)))]
  have u5 : St m5.mem P m5 (0x14 + 8) (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  obtain ⟨m6, c6, u6⟩ := St.block [.lw (8 : Fin 32) sp 0x20, .lbu (9 : Fin 32) sp 0x24] u5 hc5 (off' := 0x22)
    (by decide) (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, upd_app, ↓reduceIte, and_true, true_and]
      rw [sp5]; exact aligned_add hFa (k := 0x20) (by decide))
  simp only [runBlock, BInstr.run] at u6
  have l20 : memLoad32 m5.mem (F + 0x20) = memLoad32 (derNestedMem (derAdvance Msv d p (BitVec.ofNat 32 n) R)
      (F + 0x20) p R) (F + 0x20) := memLoad32_congr fun j hj => by
    rw [show F + 0x20 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x20 + j) by rw [← add_ofNat_assoc]; rfl,
      f5k _ (by omega)]
  have h24 : m5.mem (F + 0x24) = derNestedMem (derAdvance Msv d p (BitVec.ofNat 32 n) R) (F + 0x20) p R
      (F + 0x20 + 4) := by
    rw [show F + 0x20 + 4 = F + BitVec.ofNat 32 0x24 by rw [BitVec.add_assoc]; rfl, ← f5k _ (by decide)]; rfl
  have v6s0 : reg m6 8 = memLoad32 m5.mem (F + 0x20) := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]
  have v6s1 : reg m6 9 = (m5.mem (F + 0x24)).zeroExtend 32 := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]
  have k6 : ∀ q, q.val ≠ 0 → q ≠ 8 → q ≠ 9 → reg m6 q = reg m5 q := fun q hv h8 h9 => by
    rw [u6.regs, upd_ne hv h9, upd_ne hv h8]
  -- the error stores, `sw zero, 0(s5)` and `sb rb, 4(s5)`
  have sO0 : Sep out 4 P derAlgorithmCode.length := by
    have := env.sOC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have errSt : ∀ {Mx : Word → BitVec 8} {n : Machine} {o : Nat} {rb : Fin 32} {b : BitVec 8},
      St Mx P n o (reg n) → CodeIn Mx P derAlgorithmCode →
      fetchRel derAlgorithmCode o = some (.store .sw (21 : Fin 32) x0 0x0, 4) →
      fetchRel derAlgorithmCode (o + 4) = some (.store .sb (21 : Fin 32) rb 0x4, 4) →
      reg n 21 = out → (reg n rb).extractLsb' 0 8 = b →
      ∃ n', Steps n n' ∧ St (memStore8 (memStore32 Mx out 0) (out + 4) b) P n' (o + 8) (reg n) ∧
        CodeIn (memStore8 (memStore32 Mx out 0) (out + 4) b) P derAlgorithmCode := by
    intro Mx n o rb b st hc h1 h2 r21 rbv
    obtain ⟨n1, d1, u1⟩ := st.sw hc h1 (off' := o + 4) (ofNat_add_ofNat o 4)
      (by rw [r21, add_lit_zero]; exact env.hout)
    rw [r21, add_lit_zero, st.zero] at u1
    have hc1 := CodeIn.store32 (v := 0) hc sO0
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 h2 (off' := o + 8)
      (by rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_ofNat])
    rw [r21, rbv] at u2
    exact ⟨n2, .cons d1 (.single d2), u2, CodeIn.store8 hc1 (env.sOC.sub (c := 4) (l := 1) (by decide))⟩
  have outG : ∀ k, k < 0x50 → Sep out 0x1C (F + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [eFk]; exact sOG.subR (by omega)
  have errFin : ∀ {Mx : Word → BitVec 8} {nm : Machine} {b : BitVec 8}, Steps m nm →
      St (memStore8 (memStore32 Mx out 0) (out + 4) b) P nm 0xC8 (reg nm) →
      CodeIn (memStore8 (memStore32 Mx out 0) (out + 4) b) P derAlgorithmCode →
      (∀ k, 0x34 ≤ k → k < 0x50 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) →
      (∀ x, Sep G 0x70 x 1 → Mx x = derAdvance m.mem d p (BitVec.ofNat 32 n) R x) → reg nm sp = F →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q) ∧
        (∀ x, Sep G 0x70 x 1 → Sep out 0x1C x 1 → n'.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) R x) ∧
        memLoad32 n'.mem out = 0 ∧ n'.mem (out + 4) = b := by
    intro Mx nm b S st hc hsl hM rsp kq
    have ne4 : ∀ x, Sep out 0x1C x 1 → x ≠ out + 4 := fun x hx e =>
      hx.point (i := 4) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero]; exact e.symm)
    have s04 : ∀ x, Sep out 0x1C x 1 → Sep out 4 x 1 := fun x hx => by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin S st hc (fun k h1 h2 => by
      rw [memStore8_ne (ne4 _ (outG k h2)), memStore32_get_sep (s04 _ (outG k h2))]; exact hsl k h1 h2) rsp kq
    refine ⟨n', S', pc', sp', k', fun x hx ho => ?_, ?_, ?_⟩
    · rw [mem', memStore8_ne (ne4 x ho), memStore32_get_sep (s04 x ho), hM x hx]
    · rw [mem', memLoad32_store8_sep (by
        have := (sep_off0 out (d := 4) (k := 1) (by decide) (by decide)).symm
        exact fun i hi j hj => this i hi j hj), memLoad32_store32_same]
    · rw [mem', memStore8_same]
  -- a call to `memcpy` through its stub
  have mcCall : ∀ {Mx : Word → BitVec 8} {n : Machine} {o : Nat} {imm oo dst src : Word} {N : Nat},
      St Mx P n o (reg n) → CodeIn Mx P derAlgorithmCode →
      fetchRel derAlgorithmCode o = some (.auipc ra imm, 4) →
      fetchRel derAlgorithmCode (o + 4) = some (.jalr ra ra oo, 4) →
      P + BitVec.ofNat 32 o + imm + oo = P + 0xBEB6 → (o + 8) % 2 = 0 →
      CodeIn Mx (P + 0xBEB6) memcpyStubCode → CodeIn Mx (P + 0xBEBE) memcpyBodyCode →
      reg n sp = F → reg n a0 = dst → reg n a1 = src → reg n a2 = BitVec.ofNat 32 N →
      Sep dst N (P + 0xBEBE) memcpyBodyCode.length → Sep dst N (G + BitVec.ofNat 32 0x10) 16 →
      Sep src N (G + BitVec.ofNat 32 0x10) 16 → Sep dst N src N → dst.toNat + N < 2 ^ 32 → src.toNat + N < 2 ^ 32 →
      ∃ n', Steps n n' ∧ St n'.mem P n' (o + 8) (reg n') ∧ reg n' sp = F ∧
        (∀ x, Sep (G + BitVec.ofNat 32 0x10) 16 x 1 → n'.mem x = copyBytes Mx dst src N x) ∧
        ∀ r, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg n r := by
    intro Mx n o imm oo dst src N st hc h1 h2 hb ho hcs hcb rsp ra0 ra1 ra2 sDB sDF sSF sDS hdw hsw
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa hc h1 h2 (cb := P + 0xBEB6) hb (even_at P env.hP 0xBEB6 (by decide))
    have r1 := PEnv.reg1 regs1 st.zero
    have sp1 : reg n1 sp = F := by rw [r1 sp (by decide), rsp]
    obtain ⟨n2, c2, pc2, sp2', a02, mem2, k2⟩ := memcpy_correct n1 (P + 0xBEB6) (P + BitVec.ofNat 32 (o + 8))
      dst src N (by show CodeIn n1.mem _ _; rw [mem1]; exact hcs) (even_at P env.hP 0xBEB6 (by decide)) pc1
      (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1]) (by rw [r1 a2 (by decide), ra2])
      (by rw [regs1]; simp +decide [upd]) (even_clear _ (even_at P env.hP (o + 8) ho))
      (by
        rw [mem1, sp1, eSc, show P + 0xBEB6 + 8 = P + 0xBEBE by rw [BitVec.add_assoc]; rfl]
        exact ⟨hcb, sDB, (sGB.sub (c := 0x10) (l := 16) (by decide)), sDF, sSF, sDS,
          aligned_add hGa (k := 0x10) (by decide), by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hdw, hsw⟩)
    refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2', sp1], fun x hx => ?_, fun r hr => ?_⟩
    · rw [mem2 x (by rw [sp1, eSc]; exact hx), mem1]
    · obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15⟩ :=
        (by decide : ∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ a6 ∧ r ≠ a7 ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ (7 : Fin 32) ∧
          r ≠ (28 : Fin 32) ∧ r ≠ (29 : Fin 32) ∧ r ≠ (30 : Fin 32) ∧ r ≠ sp ∧ r ≠ ra) r hr
      rw [k2 r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14, r1 r q15]
  have K6 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m6 q = reg m q := fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ 8 ∧ q ≠ 9 := by revert hq; revert q; decide
    rw [k6 q h.1 h.2.1 h.2.2]; exact K5 q (by revert hq; revert q; decide)
  have sp6 : reg m6 sp = F := by rw [k6 sp (by decide) (by decide) (by decide), sp5]
  have s21_6 : reg m6 21 = out := by rw [k6 21 (by decide) (by decide) (by decide), s21_5]
  -- the success stores, from 0x9C: the parameters' tail with `memcpy`, then the words
  have okTail : ∀ {Mx : Word → BitVec 8} {nm : Machine}, Steps m nm → St Mx P nm 0x9C (reg nm) →
      CodeIn Mx P derAlgorithmCode → (∀ x, Sep G 0x70 x 1 → Mx x = derAdvance m.mem d p (BitVec.ofNat 32 n) R x) →
      (∀ k, 0x34 ≤ k → k < 0x50 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg nm sp = F →
      reg nm 21 = out → (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q) ∧
        (∀ x, Sep G 0x70 x 1 → Sep out 0x1C x 1 → n'.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) R x) ∧
        memLoad32 n'.mem out = reg nm 9 ∧ memLoad32 n'.mem (out + 4) = reg nm 18 ∧
        memLoad32 n'.mem (out + 8) = reg nm 20 ∧ n'.mem (out + 0xC) = (reg nm 19).extractLsb' 0 8 ∧
        ∀ j, j < 15 → n'.mem (out + 0xD + BitVec.ofNat 32 j) = Mx (F + 0x11 + BitVec.ofNat 32 j) := by
    intro Mx nm S st hc hM hsl rsp r21 kq
    have hcx : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x70 b code'.length →
        Sep (d + 8) 8 b code'.length → CodeIn Mx b code' := fun hc' hs hd i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)), derAdvance_outside R (hd.subR (c := i) (l := 1) (by omega))]
      exact hc' i hi
    obtain ⟨n1, c1, u1⟩ := St.block [.aluImm .add a0 (21 : Fin 32) 0xD, .aluImm .add a1 sp 0x11, .aluImm .add a2 x0 0xF]
      st hc (off' := 0xA6) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u1
    have k1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg nm q := fun q hv h0 h1 h2 => by
      rw [u1.regs, upd_ne hv h2, upd_ne hv h1, upd_ne hv h0]
    have sp1 : reg n1 sp = F := by rw [k1 sp (by decide) (by decide) (by decide) (by decide), rsp]
    have hoD : (out + 0xD).toNat = out.toNat + 0xD := by
      rw [BitVec.toNat_add, show (0xD : Word).toNat = 0xD from rfl]; have := env.how; omega
    have sOD' : Sep (out + 0xD) 15 G 0x70 := sOG.sub (c := 0xD) (l := 15) (by decide)
    obtain ⟨n2, c2, u2, sp2', f2, k2⟩ := mcCall (dst := out + 0xD) (src := F + 0x11) (N := 15) u1.self hc
      alg_at_a6 alg_at_aa (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (hcx env.mcs sGU env.sDU)
      (hcx env.mcb sGB env.sDB) sp1
      (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r21]; rfl)
      (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
      (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte])
      (env.sOB.sub (c := 0xD) (l := 15) (by decide)) (sOD'.subR (c := 0x10) (l := 16) (by decide))
      (by rw [show F + 0x11 = F + BitVec.ofNat 32 0x11 from rfl, eFk]
          exact offs (.inr (by decide)) (by decide) (by decide))
      (by rw [show F + 0x11 = F + BitVec.ofNat 32 0x11 from rfl, eFk]; exact sOD'.subR (by decide))
      (by rw [hoD]; have := env.how; omega)
      (by rw [BitVec.toNat_add, show (0x11 : Word).toNat = 0x11 from rfl]; have := sp0.isLt; omega)
    have m2G : ∀ x, Sep G 0x70 x 1 → Sep out 0x1C x 1 → n2.mem x = Mx x := fun x hx ho => by
      rw [f2 x (hx.sub (c := 0x10) (l := 16) (by decide)),
        copyBytes_sep (dst := out + 0xD) (n := 15) (ho.sub (c := 0xD) (l := 15) (by decide)) (Nat.le_refl _)]
    have m2F : ∀ k, k < 0x50 → n2.mem (F + BitVec.ofNat 32 k) = Mx (F + BitVec.ofNat 32 k) := fun k hk => by
      rw [f2 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega)),
        copyBytes_sep (dst := out + 0xD) (n := 15) ((outG k hk).sub (c := 0xD) (l := 15) (by decide)) (Nat.le_refl _)]
    have hc2 : CodeIn n2.mem P derAlgorithmCode := fun i hi => by
      rw [m2G _ (sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
    have v9 : reg n2 9 = reg nm 9 := by rw [k2 9 (by decide), k1 9 (by decide) (by decide) (by decide) (by decide)]
    have v18 : reg n2 18 = reg nm 18 := by
      rw [k2 18 (by decide), k1 18 (by decide) (by decide) (by decide) (by decide)]
    have v19 : reg n2 19 = reg nm 19 := by
      rw [k2 19 (by decide), k1 19 (by decide) (by decide) (by decide) (by decide)]
    have v20 : reg n2 20 = reg nm 20 := by
      rw [k2 20 (by decide), k1 20 (by decide) (by decide) (by decide) (by decide)]
    have v21 : reg n2 21 = out := by
      rw [k2 21 (by decide), k1 21 (by decide) (by decide) (by decide) (by decide), r21]
    have ow : ∀ c, c + 4 ≤ 0x1C → (out + BitVec.ofNat 32 c).toNat % 4 = 0 ∨ c % 4 ≠ 0 := fun c hc => by
      by_cases h : c % 4 = 0
      · exact .inl (aligned_add env.hout (by omega))
      · exact .inr h
    obtain ⟨n3, d3, w3⟩ := u2.sw hc2 alg_at_ae (off' := 0xB2) (by decide) (by rw [v21, add_lit_zero]; exact env.hout)
    rw [v21, add_lit_zero, v9] at w3
    have sOC4 : ∀ c, c + 4 ≤ 0x1C → Sep (out + BitVec.ofNat 32 c) 4 P derAlgorithmCode.length := fun c h =>
      env.sOC.sub (by omega)
    have hc3 := CodeIn.store32 (v := reg nm 9) hc2 sO0
    obtain ⟨n4, d4, w4⟩ := w3.sw hc3 alg_at_b2 (off' := 0xB6) (by decide)
      (by rw [v21]; exact aligned_add env.hout (k := 4) (by decide))
    rw [v21, v18] at w4
    have hc4 := CodeIn.store32 (v := reg nm 18) hc3 (sOC4 4 (by decide))
    obtain ⟨n5, d5, w5⟩ := w4.sw hc4 alg_at_b6 (off' := 0xBA) (by decide)
      (by rw [v21]; exact aligned_add env.hout (k := 8) (by decide))
    rw [v21, v20] at w5
    have hc5' := CodeIn.store32 (v := reg nm 20) hc4 (sOC4 8 (by decide))
    obtain ⟨n6, d6, w6⟩ := w5.sb hc5' alg_at_ba (off' := 0xBE) (by decide)
    rw [v21, v19] at w6
    have hc6 := CodeIn.store8 (v := (reg nm 19).extractLsb' 0 8) hc5' (env.sOC.sub (c := 0xC) (l := 1) (by decide))
    obtain ⟨n7, d7, w7⟩ := w6.jump hc6 alg_at_be (off' := 0xC8) (by decide) (by
      rw [w6.pc, show P + BitVec.ofNat 32 0xBE + 0xA = P + BitVec.ofNat 32 0xC8 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0xC8 (by decide)))
    obtain ⟨Mo, hMo⟩ : ∃ Mo, memStore8 (memStore32 (memStore32 (memStore32 n2.mem out (reg nm 9)) (out + 4) (reg nm 18))
        (out + 8) (reg nm 20)) (out + 0xC) ((reg nm 19).extractLsb' 0 8) = Mo := ⟨_, rfl⟩
    rw [hMo] at w7
    have hc7 : CodeIn Mo P derAlgorithmCode := by rw [← hMo]; exact hc6
    have ss : ∀ x, Sep out 0x1C x 1 → ∀ c, c + 4 ≤ 0x1C → Sep (out + BitVec.ofNat 32 c) 4 x 1 := fun x hx c hc =>
      hx.sub (by omega)
    have MoOut : ∀ x, Sep out 0x1C x 1 → Mo x = n2.mem x := fun x hx => by
      rw [← hMo, memStore8_ne fun e => hx.point (i := 0xC) (j := 0) (by decide) (by decide)
          (by rw [add_ofNat_zero]; exact e.symm),
        memStore32_get_sep (a := out + 8) (ss x hx 8 (by decide)), memStore32_get_sep (a := out + 4) (ss x hx 4 (by decide)),
        memStore32_get_sep (by have := ss x hx 0 (by decide); rwa [add_ofNat_zero] at this)]
    have S7 : Steps m n7 := S.trans (c1.trans (c2.trans (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.single d7)))))))
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin S7 w7.self hc7
      (fun k h1 h2 => by rw [MoOut _ (outG k h2), m2F k h2]; exact hsl k h1 h2)
      (by rw [w7.regs, sp2']) (fun q hq => by
        rw [w7.regs, k2 q (by revert hq; revert q; decide),
          k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
            (by revert hq; revert q; decide)]
        exact kq q hq)
    have s48 : Sep (out + 4) 4 (out + 8) 4 := sep_offsets out (c := 4) (n := 4) (d := 8) (k := 4) (.inl (by decide))
      (by decide) (by decide)
    have s4C : Sep (out + 0xC) 1 (out + 4) 4 := sep_offsets out (c := 0xC) (n := 1) (d := 4) (k := 4) (.inr (by decide))
      (by decide) (by decide)
    have s8C : Sep (out + 0xC) 1 (out + 8) 4 := sep_offsets out (c := 0xC) (n := 1) (d := 8) (k := 4) (.inr (by decide))
      (by decide) (by decide)
    have s0C : Sep (out + 0xC) 1 out 4 := by
      have := sep_offsets out (c := 0xC) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    refine ⟨n', S', pc', sp', k', fun x hx ho => by rw [mem', MoOut x ho, m2G x hx ho, hM x hx], ?_, ?_, ?_, ?_,
      fun j hj => ?_⟩
    · rw [mem', ← hMo, memLoad32_store8_sep s0C,
        memLoad32_store32_sep (a := out + 8) (b := out) (sep_off0 out (d := 8) (k := 4) (by decide) (by decide)).symm,
        memLoad32_store32_sep (a := out + 4) (b := out) (sep_off0 out (d := 4) (k := 4) (by decide) (by decide)).symm,
        memLoad32_store32_same]
    · rw [mem', ← hMo, memLoad32_store8_sep s4C, memLoad32_store32_sep s48.symm, memLoad32_store32_same]
    · rw [mem', ← hMo, memLoad32_store8_sep s8C, memLoad32_store32_same]
    · rw [mem', ← hMo, memStore8_same]
    · have hx : Sep (out + 0xD + BitVec.ofNat 32 j) 1 (out + 0xC) 1 ∧ ∀ c, c + 4 ≤ 0xC →
          Sep (out + BitVec.ofNat 32 c) 4 (out + 0xD + BitVec.ofNat 32 j) 1 := by
        rw [show (0xD : Word) = BitVec.ofNat 32 0xD from rfl, add_ofNat_assoc]
        exact ⟨sep_offsets out (c := 0xD + j) (n := 1) (d := 0xC) (k := 1) (.inr (by omega)) (by omega) (by decide),
          fun c hc => sep_offsets out (c := c) (n := 4) (d := 0xD + j) (k := 1) (.inl (by omega)) (by omega)
            (by omega)⟩
      rw [mem', ← hMo, memStore8_ne fun e => hx.1.point (i := 0) (j := 0) (by decide) (by decide)
          (by rw [add_ofNat_zero, add_ofNat_zero]; exact e),
        memStore32_get_sep (a := out + 8) (hx.2 8 (by decide)), memStore32_get_sep (a := out + 4) (hx.2 4 (by decide)),
        memStore32_get_sep (by have := hx.2 0 (by decide); rwa [add_ofNat_zero] at this),
        f2 _ ((sOD'.sub (c := j) (l := 1) (by omega)).subR (c := 0x10) (l := 16) (by decide)).symm,
        ds_copy_in hj (by decide)]
  cases R with
  | error e =>
    obtain ⟨z0, z4⟩ := nestedMem_err (M := derAdvance Msv d p (BitVec.ofNat 32 n) (.error e)) (out := F + 0x20)
      (rp := p) e
    obtain ⟨m7, d7, u7⟩ := u6.self.taken hc5 0x82 alg_at_22 (by decide) (by rw [v6s0, l20, z0, u6.self.zero]; rfl)
    obtain ⟨m8, c8, u8, hc8⟩ := errSt (b := derErrByte e) u7.self hc5 alg_at_82 alg_at_86 (by rw [u7.regs, s21_6])
      (by rw [u7.regs, v6s1, h24, z4, tlv_zext])
    obtain ⟨m9, d9, u9⟩ := u8.jump hc8 alg_at_8a (off' := 0xC8) (by decide) (by
      rw [u8.pc, show P + BitVec.ofNat 32 (0x82 + 8) + 0x3E = P + BitVec.ofNat 32 0xC8 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0xC8 (by decide)))
    obtain ⟨n', S', pc', sp', k', fr', o0, o4⟩ := errFin (S5.trans (c6.trans (.cons d7 (c8.trans (.single d9)))))
      u9.self hc8 slot5 memN (by rw [u9.regs, u7.regs, sp6]) (fun q hq => by rw [u9.regs, u7.regs]; exact K6 q hq)
    have hspec : derAlgOf m.mem p n = .error (derErrByte e) := by unfold derAlgOf; rw [hR]
    refine ⟨n', S', pc', sp', k', ?_, ?_⟩
    · exact fr'
    · rw [hspec]; exact ⟨o0, o4⟩
  | ok t =>
    obtain ⟨z0, z4, z8, zC⟩ := nestedMem_ok (M := derAdvance Msv d p (BitVec.ofNat 32 n) (.ok t))
      (out := F + 0x20) (rp := p) t
    have hb : t.header + t.len ≤ n := by have := derElement_bound hR; rwa [memBytes_length] at this
    have hpH : (p + BitVec.ofNat 32 t.header).toNat = p.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; have := env.hpn; omega
    have hp0 : p + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hpH, show (0 : Word).toNat = 0 from rfl] at this; have := env.hp; omega
    obtain ⟨m7, d7, u7⟩ := u6.self.notTaken hc5 0x24 alg_at_22 (by decide) (by
      rw [v6s0, l20, z0, u6.self.zero]; exact beq_false_of_ne hp0)
    obtain ⟨m8, c8, u8⟩ := St.block [.aluImm .add a1 sp 0x25, .aluImm .add a0 sp 0x5, .aluImm .add a2 x0 0xB]
      u7.self hc5 (off' := 0x2E) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u8
    have k8 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m8 q = reg m6 q := fun q hv h0 h1 h2 => by
      rw [u8.regs, upd_ne hv h2, upd_ne hv h0, upd_ne hv h1, u7.regs]
    have sp8 : reg m8 sp = F := by rw [k8 sp (by decide) (by decide) (by decide) (by decide), sp6]
    obtain ⟨m9, c9, u9, sp9, f9, k9⟩ := mcCall (dst := F + 5) (src := F + 0x25) (N := 11) u8.self hc5
      alg_at_2e alg_at_32 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (cN env.mcs sGU env.sDU)
      (cN env.mcb sGB env.sDB) sp8
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u7.regs, sp6]; rfl)
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u7.regs, sp6]; rfl)
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte])
      (sFk 5 11 (by decide) sGB)
      (by rw [show F + 5 = F + BitVec.ofNat 32 5 from rfl, eFk]; exact offs (.inr (by decide)) (by decide) (by decide))
      (by rw [show F + 0x25 = F + BitVec.ofNat 32 0x25 from rfl, eFk]
          exact offs (.inr (by decide)) (by decide) (by decide))
      (sep_offsets F (c := 5) (n := 11) (d := 0x25) (k := 11) (.inl (by decide)) (by decide) (by decide))
      (by rw [BitVec.toNat_add, show (5 : Word).toNat = 5 from rfl]; have := sp0.isLt; omega)
      (by rw [BitVec.toNat_add, show (0x25 : Word).toNat = 0x25 from rfl]; have := sp0.isLt; omega)
    have m9F : ∀ k, k < 0x50 → m9.mem (F + BitVec.ofNat 32 k) =
        copyBytes m5.mem (F + 5) (F + 0x25) 11 (F + BitVec.ofNat 32 k) := fun k hk =>
      f9 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
    have m9O : ∀ x, Sep G 0x70 x 1 → m9.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) (.ok t) x := fun x hx => by
      rw [f9 x (hx.sub (c := 0x10) (l := 16) (by decide)),
        copyBytes_sep (dst := F + 5) (n := 11) (sFk 5 11 (by decide) hx) (Nat.le_refl _), memN x hx]
    have cc9 : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x70 b code'.length →
        Sep (d + 8) 8 b code'.length → CodeIn m9.mem b code' := fun hc hs hd i hi => by
      rw [m9O _ (hs.subR (c := i) (l := 1) (by omega)),
        derAdvance_outside (.ok t) (hd.subR (c := i) (l := 1) (by omega))]
      exact hc i hi
    have hc9 := cc9 env.cod sGC env.sDC
    have s8_9 : reg m9 8 = p + BitVec.ofNat 32 t.header := by
      rw [k9 8 (by decide), k8 8 (by decide) (by decide) (by decide) (by decide), v6s0, l20, z0]
    have s9_9 : reg m9 9 = (m5.mem (F + 0x24)).zeroExtend 32 := by
      rw [k9 9 (by decide), k8 9 (by decide) (by decide) (by decide) (by decide), v6s1]
    obtain ⟨m10, d10, u10⟩ := u9.sw hc9 alg_at_36 (off' := 0x38) (by decide) (by rw [sp9, add_lit_zero]; exact hFa)
    rw [sp9, add_lit_zero, s8_9] at u10
    have hc10 := CodeIn.store32 (a := F) (v := p + BitVec.ofNat 32 t.header) hc9
      (by have := sFk 0 4 (by decide) sGC; rwa [add_ofNat_zero] at this)
    obtain ⟨m11, d11, u11⟩ := u10.sb hc10 alg_at_38 (off' := 0x3C) (by decide)
    rw [sp9, s9_9, tlv_zext] at u11
    obtain ⟨M11, hM11⟩ : ∃ M, memStore8 (memStore32 m9.mem F (p + BitVec.ofNat 32 t.header)) (F + 4)
        (m5.mem (F + 0x24)) = M := ⟨_, rfl⟩
    rw [hM11] at u11
    have hc11 : CodeIn M11 P derAlgorithmCode := by
      rw [← hM11]; exact CodeIn.store8 hc10 (sFk 4 1 (by decide) sGC)
    have M11F : ∀ k, 5 ≤ k → k < 0x50 → M11 (F + BitVec.ofNat 32 k) = m9.mem (F + BitVec.ofNat 32 k) :=
      fun k h1 h2 => by
        rw [← hM11, memStore8_ne fun e => (sepF (c := 4) (n := 1) (k := k) (.inl (by omega)) (by decide) h2).point
            (i := 0) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm),
          memStore32_get_sep (a := F) (by
            have := sepF (c := 0) (n := 4) (k := k) (.inl (by omega)) (by decide) h2
            rwa [add_ofNat_zero] at this)]
    have M11O : ∀ x, Sep G 0x70 x 1 → M11 x = derAdvance m.mem d p (BitVec.ofNat 32 n) (.ok t) x := fun x hx => by
      rw [← hM11, memStore8_ne fun e => (sFk 4 1 (by decide) hx).point (i := 0) (j := 0) (by decide) (by decide)
          (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm),
        memStore32_get_sep (a := F) (by have := sFk 0 4 (by decide) hx; rwa [add_ofNat_zero] at this), m9O x hx]
    have c11 : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x70 b code'.length →
        Sep (d + 8) 8 b code'.length → CodeIn M11 b code' := fun hc hs hd i hi => by
      rw [M11O _ (hs.subR (c := i) (l := 1) (by omega)),
        derAdvance_outside (.ok t) (hd.subR (c := i) (l := 1) (by omega))]
      exact hc i hi
    -- the rebuilt reader's unread bytes
    have cp : ∀ j, j < 8 → M11 (F + BitVec.ofNat 32 (8 + j)) = m5.mem (F + BitVec.ofNat 32 (0x28 + j)) :=
      fun j hj => by
        rw [M11F _ (by omega) (by omega), m9F _ (by omega),
          show F + BitVec.ofNat 32 (8 + j) = F + 5 + BitVec.ofNat 32 (3 + j) by
            rw [show (5 : Word) = BitVec.ofNat 32 5 from rfl, add_ofNat_assoc, show 5 + (3 + j) = 8 + j by omega],
          ds_copy_in (by omega) (by decide),
          show F + 0x25 + BitVec.ofNat 32 (3 + j) = F + BitVec.ofNat 32 (0x28 + j) by
            rw [show (0x25 : Word) = BitVec.ofNat 32 0x25 from rfl, add_ofNat_assoc, show 0x25 + (3 + j) = 0x28 + j by omega]]
    have lq : memLoad32 M11 (F + 8) = p + BitVec.ofNat 32 t.header := by
      rw [← z8]
      calc memLoad32 M11 (F + 8) = memLoad32 m5.mem (F + BitVec.ofNat 32 0x28) :=
            memLoad32_congr2 fun jj hj => by
              rw [show F + 8 + BitVec.ofNat 32 jj = F + BitVec.ofNat 32 (8 + jj) by
                rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc], add_ofNat_assoc, cp jj (by omega)]
        _ = _ := by
            rw [show F + 0x20 + 8 = F + BitVec.ofNat 32 0x28 by rw [BitVec.add_assoc]; rfl]
            exact memLoad32_congr fun jj hj => by rw [add_ofNat_assoc, f5k _ (by omega)]
    have lk : memLoad32 M11 (F + 0xC) = BitVec.ofNat 32 t.len := by
      rw [← zC]
      calc memLoad32 M11 (F + 0xC) = memLoad32 m5.mem (F + BitVec.ofNat 32 0x2C) :=
            memLoad32_congr2 fun jj hj => by
              rw [show F + 0xC + BitVec.ofNat 32 jj = F + BitVec.ofNat 32 (8 + (4 + jj)) by
                rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, add_ofNat_assoc,
                  show 0xC + jj = 8 + (4 + jj) by omega], add_ofNat_assoc,
                cp _ (by omega), show 0x28 + (4 + jj) = 0x2C + jj by omega]
        _ = _ := by
            rw [show F + 0x20 + 0xC = F + BitVec.ofNat 32 0x2C by rw [BitVec.add_assoc]; rfl]
            exact memLoad32_congr fun jj hj => by rw [add_ofNat_assoc, f5k _ (by omega)]
    -- `Der::oid` with the result at `sp + 0x20` and the rebuilt reader at `sp`
    obtain ⟨m12, c12, u12⟩ := St.block [.aluImm .add a0 sp 0x20, .alu .add a1 x0 sp] u11.self hc11 (off' := 0x40)
      (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u12
    have k11 : ∀ q, reg m11 q = reg m9 q := fun q => by rw [u11.regs]
    have k12 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m12 q = reg m9 q := fun q hv h0 h1 => by
      rw [u12.regs, upd_ne hv h1, upd_ne hv h0, k11]
    obtain ⟨m13, c13, pc13, mem13, regs13⟩ := u12.self.callRa hc11 alg_at_40 alg_at_44 (cb := P + 0xFFFFFE02)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFE02 (by decide))
    have r13 := PEnv.reg1 regs13 u12.self.zero
    have sp13 : reg m13 sp = F := by rw [r13 sp (by decide), k12 sp (by decide) (by decide) (by decide), sp9]
    have hlen : t.len < 2 ^ 32 := by omega
    have sIn : Sep (p + BitVec.ofNat 32 t.header) t.len G 0x70 := sRG.sub (by omega)
    have sInD : Sep (p + BitVec.ofNat 32 t.header) t.len (d + 8) 8 := env.sRD.sub (by omega)
    have oenv : OidEnv m13.mem (P + 0xFFFFFE02) F (F + 0x20) F := by
      rw [mem13]
      refine ⟨even_at P env.hP 0xFFFFFE02 (by decide), c11 env.oid sGO env.sDO,
        by rw [BitVec.add_assoc]; exact c11 env.elem sGE env.sDE, by rw [BitVec.add_assoc]; exact c11 env.tlv sGT env.sDT,
        hFa, by omega, aligned_add hFa (k := 0x20) (by decide), hFa,
        by rw [eNF]; exact sGO.sub (by decide), by rw [eNF, BitVec.add_assoc]; exact sGE.sub (by decide),
        by rw [eNF, BitVec.add_assoc]; exact sGT.sub (by decide), sFk 0x20 8 (by decide) sGO,
        by rw [show F + 8 = F + BitVec.ofNat 32 8 from rfl]; exact sFk 8 8 (by decide) sGO,
        by rw [show F + 8 = F + BitVec.ofNat 32 8 from rfl, BitVec.add_assoc]; exact sFk 8 8 (by decide) sGT,
        by rw [eNF, show F + 0x20 = F + BitVec.ofNat 32 0x20 from rfl, eFk]
           exact offs (.inr (by decide)) (by decide) (by decide),
        by rw [eNF, show F + 8 = F + BitVec.ofNat 32 8 from rfl, eFk]
           exact offs (.inr (by decide)) (by decide) (by decide),
        by rw [lq, lk, ofNat_tn hlen, eNF]; exact sIn.subR (by decide),
        by rw [lq, lk, ofNat_tn hlen, show F + 8 = F + BitVec.ofNat 32 8 from rfl, eFk]; exact sIn.subR (by decide),
        by rw [lq, hpH]; have := env.hp; omega,
        by rw [lq, lk, ofNat_tn hlen, hpH]; have := env.hpn; omega⟩
    obtain ⟨m14, c14, pc14, sp14, k14, f14⟩ := derOid_correct m13 oenv pc13 sp13
      (by rw [r13 a0 (by decide), u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k11, sp9]; rfl)
      (by rw [r13 a1 (by decide), u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k11, sp9]; exact zw F)
      (by rw [regs13]; simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at P env.hP (0x40 + 8) (by decide)))
    have eB : memBytes M11 (p + BitVec.ofNat 32 t.header) t.len = memBytes m.mem (p + BitVec.ofNat 32 t.header) t.len :=
      memBytes_congr fun i hi => by
        rw [M11O _ (sIn.sub (c := i) (l := 1) (by omega)).symm,
          derAdvance_outside (.ok t) (sInD.sub (c := i) (l := 1) (by omega)).symm]
    rw [mem13, lq, lk, ofNat_tn hlen, eB] at f14
    generalize hO : derOid (memBytes m.mem (p + BitVec.ofNat 32 t.header) t.len) = O at f14
    obtain ⟨A, hA⟩ : ∃ A, derAdvance M11 F (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len)
        (derElement 6 (memBytes m.mem (p + BitVec.ofNat 32 t.header) t.len)) = A := ⟨_, rfl⟩
    rw [hA] at f14
    have S14 : Steps m m14 :=
      S5.trans (c6.trans (.cons d7 (c8.trans (c9.trans (.cons d10 (.cons d11 (c12.trans (c13.trans c14))))))))
    have f14k : ∀ k, k < 0x50 → m14.mem (F + BitVec.ofNat 32 k) =
        derOidMem A (F + 0x20) (p + BitVec.ofNat 32 t.header) O (F + BitVec.ofNat 32 k) := fun k hk =>
      f14 _ (by rw [eNF, eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
    have AO : ∀ x, Sep (F + 8) 8 x 1 → A x = M11 x := fun x hx => by
      rw [← hA]; exact derAdvance_outside _ hx
    have m14G : ∀ x, Sep G 0x70 x 1 → m14.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) (.ok t) x :=
      fun x hx => by
        rw [f14 x (by rw [eNF]; exact hx.sub (c := 0) (l := 0x20) (by decide)),
          oidMem_outside (out := F + 0x20) O (sFk 0x20 8 (by decide) hx), AO x (sFk 8 8 (by decide) hx), M11O x hx]
    have c14 : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x70 b code'.length →
        Sep (d + 8) 8 b code'.length → CodeIn m14.mem b code' := fun hc hs hd i hi => by
      rw [m14G _ (hs.subR (c := i) (l := 1) (by omega)),
        derAdvance_outside (.ok t) (hd.subR (c := i) (l := 1) (by omega))]
      exact hc i hi
    have hc14 := c14 env.cod sGC env.sDC
    have slot14 : ∀ k, 0x34 ≤ k → k < 0x50 → m14.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
      fun k h1 h2 => by
        rw [f14k k h2, oidMem_outside (out := F + 0x20) O (sepF (c := 0x20) (n := 8) (.inl (by omega)) (by decide) h2),
          AO _ (sepF (c := 8) (n := 8) (.inl (by omega)) (by decide) h2), M11F k (by omega) h2, m9F k h2,
          copyBytes_sep (dst := F + 5) (n := 11) (sepF (c := 5) (n := 11) (.inl (by omega)) (by decide) h2)
            (Nat.le_refl _), slot5 k h1 h2]
    have K14 : ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg m14 q = reg m6 q := fun q hq => by
      have h : oidKeep q = true ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧
          q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q ≠ a2 := by
        revert hq; revert q; decide
      rw [k14 q h.1, r13 q h.2.1, k12 q h.2.2.1 h.2.2.2.1 h.2.2.2.2.1, k9 q h.2.2.2.2.2.1,
        k8 q h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2]
    have Km14 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m14 q = reg m q := fun q hq => by
      rw [K14 q (by revert hq; revert q; decide)]; exact K6 q hq
    have s21_14 : reg m14 21 = out := by rw [K14 21 (by decide), s21_6]
    have u14 : St m14.mem P m14 0x48 (reg m14) := ⟨by rw [pc14], rfl, fun _ => rfl⟩
    obtain ⟨m15, d15, u15⟩ := u14.lw hc14 alg_at_48 (off' := 0x4A) (by decide)
      (by rw [sp14]; exact aligned_add hFa (k := 0x20) (by decide))
    have l1420 : memLoad32 m14.mem (F + 0x20) =
        memLoad32 (derOidMem A (F + 0x20) (p + BitVec.ofNat 32 t.header) O) (F + 0x20) :=
      memLoad32_congr fun j hj => by
        rw [show F + 0x20 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x20 + j) by rw [← add_ofNat_assoc]; rfl,
          f14k _ (by omega)]
    have v15 : reg m15 9 = memLoad32 m14.mem (F + 0x20) := by
      rw [u15.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp14]
    have k15 : ∀ q, q.val ≠ 0 → q ≠ 9 → reg m15 q = reg m14 q := fun q hv h9 => by rw [u15.regs, upd_ne hv h9]
    cases O with
    | error e =>
      obtain ⟨m16, d16, u16⟩ := u15.self.taken hc14 0x8C alg_at_4a (by decide)
        (by rw [v15, l1420, (oidMem_err e).1, u15.self.zero]; rfl)
      obtain ⟨m17, d17, u17⟩ := u16.lbu hc14 alg_at_8c (off' := 0x90) (by decide)
      have e24 : m14.mem (F + 0x24) = derErrByte e := by
        rw [show F + 0x24 = F + BitVec.ofNat 32 0x24 from rfl, f14k _ (by decide),
          show F + BitVec.ofNat 32 0x24 = F + 0x20 + 4 by rw [BitVec.add_assoc]; rfl]
        exact (oidMem_err e).2
      obtain ⟨m18, c18, u18, hc18⟩ := errSt (b := derErrByte e) u17.self hc14 alg_at_90 alg_at_94
        (by rw [u17.regs, upd_ne (by decide) (by decide), k15 21 (by decide) (by decide), s21_14])
        (by rw [u17.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k15 sp (by decide) (by decide), sp14, e24,
              tlv_zext])
      obtain ⟨m19, d19, u19⟩ := u18.jump hc18 alg_at_98 (off' := 0xC8) (by decide) (by
        rw [u18.pc, show P + BitVec.ofNat 32 (0x90 + 8) + 0x30 = P + BitVec.ofNat 32 0xC8 by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0xC8 (by decide)))
      obtain ⟨n', S', pc', sp', k', fr', o0, o4⟩ :=
        errFin (S14.trans (.cons d15 (.cons d16 (.cons d17 (c18.trans (.single d19)))))) u19.self hc18 slot14 m14G
          (by rw [u19.regs, u17.regs, upd_ne (by decide) (by decide), k15 sp (by decide) (by decide), sp14])
          (fun q hq => by
            rw [u19.regs, u17.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide),
              k15 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
            exact Km14 q hq)
      have hspec : derAlgOf m.mem p n = .error (derErrByte e) := by
        unfold derAlgOf; rw [hR]; dsimp only; rw [hO]
      refine ⟨n', S', pc', sp', k', fr', ?_⟩
      rw [hspec]; exact ⟨o0, o4⟩
    | ok o =>
      have hoE := derOid_ok_elem hO
      rw [hoE] at hA
      have hob : o.header + o.len ≤ t.len := by have := derElement_bound hoE; rwa [memBytes_length] at this
      have hpo : (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header).toNat = p.toNat + t.header + o.header := by
        rw [BitVec.toNat_add, hpH, ofNat_tn (by omega)]; have := env.hpn; omega
      have hs1 : p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header ≠ 0 := fun h => by
        have := congrArg BitVec.toNat h; rw [hpo, show (0 : Word).toNat = 0 from rfl] at this; have := env.hp; omega
      have l15 : memLoad32 m14.mem (F + 0x20) = p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header := by
        rw [l1420, (oidMem_ok o).1]
      have hrem : memLoad32 m14.mem (F + 0xC) = BitVec.ofNat 32 (t.len - (o.header + o.len)) := by
        have : memLoad32 m14.mem (F + 0xC) = memLoad32 A (F + 0xC) := memLoad32_congr fun j hj => by
          rw [show F + 0xC + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0xC + j) by rw [← add_ofNat_assoc]; rfl,
            f14k _ (by omega), oidMem_outside (out := F + 0x20) (.ok o)
              (sepF (c := 0x20) (n := 8) (.inr (by omega)) (by decide) (by omega))]
        rw [this, ← hA, (derAdvance_ld o).2]
        exact sub_val hob hlen
      have l24 : memLoad32 m14.mem (F + 0x24) = BitVec.ofNat 32 o.len := by
        have : memLoad32 m14.mem (F + 0x24) =
            memLoad32 (derOidMem A (F + 0x20) (p + BitVec.ofNat 32 t.header) (.ok o)) (F + 0x24) :=
          memLoad32_congr fun j hj => by
            rw [show F + 0x24 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x24 + j) by rw [← add_ofNat_assoc]; rfl,
              f14k _ (by omega)]
        rw [this, show F + 0x24 = F + 0x20 + 4 by rw [BitVec.add_assoc]; rfl]; exact (oidMem_ok o).2
      obtain ⟨m16, d16, u16⟩ := u15.self.notTaken hc14 0x4C alg_at_4a (by decide)
        (by rw [v15, l15, u15.self.zero]; exact beq_false_of_ne hs1)
      have sp15 : reg m15 sp = F := by rw [k15 sp (by decide) (by decide), sp14]
      obtain ⟨m17, d17, u17⟩ := u16.lw hc14 alg_at_4c (off' := 0x4E) (by decide)
        (by rw [sp15]; exact aligned_add hFa (k := 0xC) (by decide))
      obtain ⟨m18, d18, u18⟩ := u17.self.lw hc14 alg_at_4e (off' := 0x50) (by decide)
        (by rw [u17.regs, upd_ne (by decide) (by decide), sp15]; exact aligned_add hFa (k := 0x24) (by decide))
      have k18 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ 18 → reg m18 q = reg m15 q := fun q hv h0 h18 => by
        rw [u18.regs, upd_ne hv h18, u17.regs, upd_ne hv h0]
      have r18a0 : reg m18 a0 = BitVec.ofNat 32 (t.len - (o.header + o.len)) := by
        rw [u18.regs, upd_ne (by decide) (by decide), u17.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [sp15, hrem]
      have r18s2 : reg m18 18 = BitVec.ofNat 32 o.len := by
        rw [u18.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u17.regs, upd_ne (by decide) (by decide), sp15, l24]
      have r18s1 : reg m18 9 = p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header := by
        rw [k18 9 (by decide) (by decide) (by decide), v15, l15]
      have sp18 : reg m18 sp = F := by rw [k18 sp (by decide) (by decide) (by decide), sp15]
      have s21_18 : reg m18 21 = out := by
        rw [k18 21 (by decide) (by decide) (by decide), k15 21 (by decide) (by decide), s21_14]
      have Km18 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m18 q = reg m q := fun q hq => by
        rw [k18 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
          k15 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        exact Km14 q hq
      have S18 : Steps m m18 := S14.trans (.cons d15 (.cons d16 (.cons d17 (.single d18))))
      by_cases hz : t.len - (o.header + o.len) = 0
      · obtain ⟨m19, d19, u19⟩ := u18.self.taken hc14 0x9A alg_at_50 (by decide)
          (by rw [r18a0, hz, u18.self.zero]; rfl)
        obtain ⟨m20, d20, u20⟩ := u19.aluImm hc14 alg_at_9a (off' := 0x9C) (by decide)
        have r20 : ∀ q, q.val ≠ 0 → q ≠ 20 → reg m20 q = reg m18 q := fun q hv h => by rw [u20.regs, upd_ne hv h]
        obtain ⟨n', S', pc', sp', k', fr', o0, o4, o8, -, -⟩ := okTail (S18.trans (.cons d19 (.single d20))) u20.self
          hc14 m14G slot14 (by rw [r20 sp (by decide) (by decide), sp18])
          (by rw [r20 21 (by decide) (by decide), s21_18])
          (fun q hq => by
            rw [r20 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact Km18 q hq)
        have hspec : derAlgOf m.mem p n =
            .ok ((p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header, o.len), none) := by
          unfold derAlgOf; rw [hR]; dsimp only; rw [hO]; dsimp only; rw [ite_eq_left hz]
        refine ⟨n', S', pc', sp', k', fr', ?_⟩
        rw [hspec]
        refine ⟨by rw [o0, r20 9 (by decide) (by decide), r18s1], by rw [o4, r20 18 (by decide) (by decide), r18s2],
          by rw [o8, u20.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u18.self.zero]; rfl⟩
      · have hrl : t.len - (o.header + o.len) < 2 ^ 32 := by omega
        obtain ⟨m19, d19, u19⟩ := u18.self.notTaken hc14 0x52 alg_at_50 (by decide)
          (by rw [r18a0, u18.self.zero]; exact beq_false_of_ne fun h => by
                have := congrArg BitVec.toNat h; rw [ofNat_tn hrl] at this; exact hz this)
        obtain ⟨m20, c20, u20⟩ := St.block [.aluImm .add a0 sp 0x20, .alu .add a1 x0 sp] u19 hc14 (off' := 0x56)
          (by decide) (by simp [BlockOk, BInstr.ok])
        simp only [runBlock, BInstr.run] at u20
        have k20 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m20 q = reg m18 q := fun q hv h0 h1 => by
          rw [u20.regs, upd_ne hv h1, upd_ne hv h0]
        obtain ⟨m21, c21, pc21, mem21, regs21⟩ := u20.self.callRa hc14 alg_at_56 alg_at_5a (cb := P + 0xFFFFF6F0)
          (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF6F0 (by decide))
        have r21 := PEnv.reg1 regs21 u20.self.zero
        obtain ⟨m22, c22, pc22, mem22, k22⟩ := derTlv_correct m21 (out := F + 0x20) (d := F) (even_at P env.hP 0xFFFFF6F0 (by decide))
          (by rw [mem21]; exact c14 env.tlv sGT env.sDT) pc21
          (by rw [r21 a0 (by decide), u20.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp18]; rfl)
          (by rw [r21 a1 (by decide), u20.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp18]; exact zw F)
          (by rw [regs21]; simp +decide only [upd_app, ↓reduceIte])
          (even_clear _ (even_at P env.hP (0x56 + 8) (by decide))) (aligned_add hFa (k := 0x20) (by decide)) hFa
          (sFk 0x20 17 (by decide) sGT) (sFk 8 8 (by decide) sGT)
        have l8 : memLoad32 m14.mem (F + 8) = p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len) := by
          have : memLoad32 m14.mem (F + 8) = memLoad32 A (F + 8) := memLoad32_congr fun j hj => by
            rw [show F + 8 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (8 + j) by rw [← add_ofNat_assoc]; rfl,
              f14k _ (by omega), oidMem_outside (out := F + 0x20) (.ok o)
                (sepF (c := 0x20) (n := 8) (.inr (by omega)) (by decide) (by omega))]
          rw [this, ← hA, (derAdvance_ld o).1]
        have eB2 : memBytes m14.mem (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len))
            (t.len - (o.header + o.len)) =
            memBytes m.mem (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len))
              (t.len - (o.header + o.len)) :=
          memBytes_congr fun i hi => by
            rw [add_ofNat_assoc, add_ofNat_assoc,
              m14G _ (sRG.sub (c := t.header + (o.header + o.len + i)) (l := 1) (by omega)).symm,
              derAdvance_outside (.ok t) (env.sRD.sub (c := t.header + (o.header + o.len + i)) (l := 1) (by omega)).symm]
        rw [mem21, l8, hrem, ofNat_tn hrl, eB2] at mem22
        generalize hU : derTlv (memBytes m.mem (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len))
          (t.len - (o.header + o.len))) = U at mem22
        have K22 : ∀ q, q.val ≠ 0 → q ≠ ra → q ≠ a0 → q ≠ a1 → tlvClob q = false → reg m22 q = reg m18 q :=
          fun q hv hr h0 h1 hc => by rw [k22 q hc, r21 q hr, k20 q hv h0 h1]
        have sp22 : reg m22 sp = F := by rw [K22 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp18]
        have m22G : ∀ x, Sep G 0x70 x 1 → m22.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) (.ok t) x :=
          fun x hx => by
            rw [mem22, derTlvMem_outside (o := F + 0x20) U (sFk 0x20 17 (by decide) hx),
              derAdvance_outside (d := F) U (sFk 8 8 (by decide) hx), m14G x hx]
        have c22' : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x70 b code'.length →
            Sep (d + 8) 8 b code'.length → CodeIn m22.mem b code' := fun hc hs hd i hi => by
          rw [m22G _ (hs.subR (c := i) (l := 1) (by omega)),
            derAdvance_outside (.ok t) (hd.subR (c := i) (l := 1) (by omega))]
          exact hc i hi
        have hc22 := c22' env.cod sGC env.sDC
        have slot22 : ∀ k, 0x34 ≤ k → k < 0x50 → m22.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
          fun k h1 h2 => by
            rw [mem22, derTlvMem_outside (o := F + 0x20) U (sepF (c := 0x20) (n := 17) (.inl (by omega)) (by decide) h2),
              derAdvance_outside (d := F) U (sepF (c := 8) (n := 8) (.inl (by omega)) (by decide) h2), slot14 k h1 h2]
        have u22 : St m22.mem P m22 0x5E (reg m22) := ⟨by rw [pc22], rfl, fun _ => rfl⟩
        obtain ⟨m23, d23, u23⟩ := u22.lw hc22 alg_at_5e (off' := 0x60) (by decide)
          (by rw [sp22]; exact aligned_add hFa (k := 0x20) (by decide))
        obtain ⟨m24, d24, u24⟩ := u23.self.lbu hc22 alg_at_60 (off' := 0x64) (by decide)
        have k24 : ∀ q, q.val ≠ 0 → q ≠ 19 → q ≠ 20 → reg m24 q = reg m22 q := fun q hv h19 h20 => by
          rw [u24.regs, upd_ne hv h19, u23.regs, upd_ne hv h20]
        have r24s4 : reg m24 20 = memLoad32 m22.mem (F + 0x20) := by
          rw [u24.regs, upd_ne (by decide) (by decide), u23.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp22]
        have r24s3 : reg m24 19 = (m22.mem (F + 0x24)).zeroExtend 32 := by
          rw [u24.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u23.regs, upd_ne (by decide) (by decide), sp22]
        have sp24 : reg m24 sp = F := by rw [k24 sp (by decide) (by decide) (by decide), sp22]
        have s21_24 : reg m24 21 = out := by
          rw [k24 21 (by decide) (by decide) (by decide),
            K22 21 (by decide) (by decide) (by decide) (by decide) (by decide), s21_18]
        have Km24 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m24 q = reg m q := fun q hq => by
          have h : q.val ≠ 0 ∧ q ≠ 19 ∧ q ≠ 20 ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ tlvClob q = false := by
            revert hq; revert q; decide
          rw [k24 q h.1 h.2.1 h.2.2.1, K22 q h.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2]; exact Km18 q hq
        have S24 : Steps m m24 := S18.trans (.cons d19 (c20.trans (c21.trans (c22.trans (.cons d23 (.single d24))))))
        cases U with
        | error e =>
          obtain ⟨m25, d25, u25⟩ := u24.self.taken hc22 0xC0 alg_at_64 (by decide)
            (by rw [r24s4, mem22, derTlvMem_err0, u24.self.zero]; rfl)
          obtain ⟨m26, c26, u26, hc26⟩ := errSt (b := derErrByte e) (rb := 19) u25.self hc22 alg_at_c0 alg_at_c4
            (by rw [u25.regs, s21_24])
            (by rw [u25.regs, r24s3, tlv_zext, mem22, show F + 0x24 = F + 0x20 + 4 by rw [BitVec.add_assoc]; rfl,
                  derTlvMem_err4])
          obtain ⟨n', S', pc', sp', k', fr', o0, o4⟩ := errFin (S24.trans (.cons d25 c26)) u26.self hc26 slot22 m22G
            (by rw [u26.regs, u25.regs, sp24]) (fun q hq => by rw [u26.regs, u25.regs]; exact Km24 q hq)
          have hspec : derAlgOf m.mem p n = .error (derErrByte e) := by
            unfold derAlgOf; rw [hR]; dsimp only; rw [hO]; dsimp only; rw [ite_eq_right hz, hU]
          refine ⟨n', S', pc', sp', k', fr', ?_⟩
          rw [hspec]; exact ⟨o0, o4⟩
        | ok u =>
          have hub : u.header + u.len ≤ t.len - (o.header + o.len) := by
            have := derTlv_bound hU; rwa [memBytes_length] at this
          have hrp2 : (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len) +
              BitVec.ofNat 32 u.header).toNat = p.toNat + t.header + (o.header + o.len) + u.header := by
            rw [BitVec.toNat_add, BitVec.toNat_add, hpH, ofNat_tn (by omega), ofNat_tn (by omega)]
            have := env.hpn; omega
          have hs4 : p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len) + BitVec.ofNat 32 u.header ≠ 0 :=
            fun h => by
              have := congrArg BitVec.toNat h; rw [hrp2, show (0 : Word).toNat = 0 from rfl] at this
              have := env.hp; omega
          obtain ⟨m25, d25, u25⟩ := u24.self.notTaken hc22 0x68 alg_at_64 (by decide)
            (by rw [r24s4, mem22, derTlvMem_ok0, u24.self.zero]; exact beq_false_of_ne hs4)
          obtain ⟨m26, c26, u26⟩ := St.block [.aluImm .add a1 sp 0x25, .aluImm .add a0 sp 0x11, .aluImm .add a2 x0 0xF]
            u25 hc22 (off' := 0x72) (by decide) (by simp [BlockOk, BInstr.ok])
          simp only [runBlock, BInstr.run] at u26
          have k26 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m26 q = reg m24 q := fun q hv h0 h1 h2 => by
            rw [u26.regs, upd_ne hv h2, upd_ne hv h0, upd_ne hv h1]
          have sp26 : reg m26 sp = F := by rw [k26 sp (by decide) (by decide) (by decide) (by decide), sp24]
          obtain ⟨m27, c27, u27, sp27, f27, k27⟩ := mcCall (dst := F + 0x11) (src := F + 0x25) (N := 15) u26.self hc22
            alg_at_72 alg_at_76 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (c22' env.mcs sGU env.sDU)
            (c22' env.mcb sGB env.sDB) sp26
            (by rw [u26.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp24]; rfl)
            (by rw [u26.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp24]; rfl)
            (by rw [u26.regs]; simp +decide only [upd_app, ↓reduceIte])
            (sFk 0x11 15 (by decide) sGB)
            (by rw [show F + 0x11 = F + BitVec.ofNat 32 0x11 from rfl, eFk]
                exact offs (.inr (by decide)) (by decide) (by decide))
            (by rw [show F + 0x25 = F + BitVec.ofNat 32 0x25 from rfl, eFk]
                exact offs (.inr (by decide)) (by decide) (by decide))
            (sep_offsets F (c := 0x11) (n := 15) (d := 0x25) (k := 15) (.inl (by decide)) (by decide) (by decide))
            (by rw [BitVec.toNat_add, show (0x11 : Word).toNat = 0x11 from rfl]; have := sp0.isLt; omega)
            (by rw [BitVec.toNat_add, show (0x25 : Word).toNat = 0x25 from rfl]; have := sp0.isLt; omega)
          have m27G : ∀ x, Sep G 0x70 x 1 → m27.mem x = derAdvance m.mem d p (BitVec.ofNat 32 n) (.ok t) x :=
            fun x hx => by
              rw [f27 x (hx.sub (c := 0x10) (l := 16) (by decide)),
                copyBytes_sep (dst := F + 0x11) (n := 15) (sFk 0x11 15 (by decide) hx) (Nat.le_refl _), m22G x hx]
          have f27k : ∀ k, k < 0x50 → m27.mem (F + BitVec.ofNat 32 k) =
              copyBytes m22.mem (F + 0x11) (F + 0x25) 15 (F + BitVec.ofNat 32 k) := fun k hk =>
            f27 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
          have slot27 : ∀ k, 0x34 ≤ k → k < 0x50 → m27.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
            fun k h1 h2 => by
              rw [f27k k h2, copyBytes_sep (dst := F + 0x11) (n := 15)
                (sepF (c := 0x11) (n := 15) (.inl (by omega)) (by decide) h2) (Nat.le_refl _), slot22 k h1 h2]
          have hc27 : CodeIn m27.mem P derAlgorithmCode := fun i hi => by
            rw [m27G _ (sGC.subR (c := i) (l := 1) (by omega)),
              derAdvance_outside (.ok t) (env.sDC.subR (c := i) (l := 1) (by omega))]
            exact env.cod i hi
          have l27C : memLoad32 m27.mem (F + 0xC) =
              BitVec.ofNat 32 (t.len - (o.header + o.len) - (u.header + u.len)) := by
            have : memLoad32 m27.mem (F + 0xC) = memLoad32 (derAdvance m14.mem F
                (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len))
                (BitVec.ofNat 32 (t.len - (o.header + o.len))) (.ok u)) (F + 0xC) := memLoad32_congr fun j hj => by
              rw [show F + 0xC + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0xC + j) by rw [← add_ofNat_assoc]; rfl,
                f27k _ (by omega), copyBytes_sep (dst := F + 0x11) (n := 15)
                  (sepF (c := 0x11) (n := 15) (.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _),
                mem22, derTlvMem_outside (o := F + 0x20) (.ok u)
                  (sepF (c := 0x20) (n := 17) (.inr (by omega)) (by decide) (by omega))]
            rw [this, (derAdvance_ld u).2]; exact sub_val hub hrl
          obtain ⟨m28, d28, u28⟩ := u27.lw hc27 alg_at_7a (off' := 0x7C) (by decide)
            (by rw [sp27]; exact aligned_add hFa (k := 0xC) (by decide))
          have r28a0 : reg m28 a0 = BitVec.ofNat 32 (t.len - (o.header + o.len) - (u.header + u.len)) := by
            rw [u28.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp27, l27C]
          have k28 : ∀ q, q.val ≠ 0 → q ≠ a0 → reg m28 q = reg m27 q := fun q hv h0 => by rw [u28.regs, upd_ne hv h0]
          have K28 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m28 q = reg m24 q :=
            fun q hq => by
              have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 := by revert hq; revert q; decide
              rw [k28 q h.1 h.2.1, k27 q hq, k26 q h.1 h.2.1 h.2.2.1 h.2.2.2]
          have sp28 : reg m28 sp = F := by rw [k28 sp (by decide) (by decide), sp27]
          have S28 : Steps m m28 := S24.trans (.cons d25 (c26.trans (c27.trans (.single d28))))
          by_cases hfit : u.header + u.len = t.len - (o.header + o.len)
          · obtain ⟨m29, d29, u29⟩ := u28.self.taken hc27 0x9C alg_at_7c (by decide)
              (by rw [r28a0, show t.len - (o.header + o.len) - (u.header + u.len) = 0 by omega, u28.self.zero]; rfl)
            obtain ⟨n', S', pc', sp', k', fr', o0, o4, o8, oC, oD⟩ := okTail (S28.trans (.single d29)) u29.self hc27
              m27G slot27 (by rw [u29.regs, sp28]) (by rw [u29.regs, K28 21 (by decide), s21_24])
              (fun q hq => by rw [u29.regs, K28 q (by revert hq; revert q; decide)]; exact Km24 q hq)
            have hspec : derAlgOf m.mem p n = .ok ((p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header, o.len),
                some (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len), u)) := by
              unfold derAlgOf; rw [hR]; dsimp only; rw [hO]; dsimp only; rw [ite_eq_right hz, hU]; dsimp only
              rw [ite_eq_left hfit]
            have bt : ∀ i, 0xC ≤ i → i < 0x1C →
                n'.mem (out + BitVec.ofNat 32 i) = m22.mem (F + BitVec.ofNat 32 (0x18 + i)) := by
              intro i h1 h2
              rcases Nat.lt_or_ge i 0xD with h | h
              · obtain rfl : i = 0xC := by omega
                rw [show out + BitVec.ofNat 32 0xC = out + 0xC from rfl, oC, u29.regs, K28 19 (by decide), r24s3,
                  tlv_zext]
                rfl
              · rw [show out + BitVec.ofNat 32 i = out + 0xD + BitVec.ofNat 32 (i - 0xD) by
                    rw [show (0xD : Word) = BitVec.ofNat 32 0xD from rfl, add_ofNat_assoc]
                    exact congrArg (fun k => out + BitVec.ofNat 32 k) (by omega),
                  oD (i - 0xD) (by omega),
                  f27 (F + 0x11 + BitVec.ofNat 32 (i - 0xD)) (by
                    rw [show (0x11 : Word) = BitVec.ofNat 32 0x11 from rfl, add_ofNat_assoc, eFk]
                    exact offs (.inl (by omega)) (by decide) (by omega)),
                  ds_copy_in (by omega) (by decide), show (0x25 : Word) = BitVec.ofNat 32 0x25 from rfl,
                  add_ofNat_assoc]
                exact congrArg (fun k => m22.mem (F + BitVec.ofNat 32 k)) (by omega)
            have ld : ∀ c, 0xC ≤ c → c + 4 ≤ 0x1C →
                memLoad32 n'.mem (out + BitVec.ofNat 32 c) = memLoad32 m22.mem (F + BitVec.ofNat 32 (0x18 + c)) :=
              fun c h1 h2 => memLoad32_congr2 fun j hj => by
                rw [add_ofNat_assoc, add_ofNat_assoc, bt _ (by omega) (by omega)]
                exact congrArg (fun k => m22.mem (F + BitVec.ofNat 32 k)) (by omega)
            have K9 : ∀ q, q.val ∈ [9, 18] → reg m29 q = reg m18 q := fun q hq => by
              have h : q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ 19 ∧ q ≠ 20 ∧
                  q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ tlvClob q = false := by revert hq; revert q; decide
              rw [u29.regs, K28 q h.1, k24 q h.2.1 h.2.2.1 h.2.2.2.1,
                K22 q h.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2]
            refine ⟨n', S', pc', sp', k', fr', ?_⟩
            rw [hspec]
            refine ⟨by rw [o0, K9 9 (by decide), r18s1], by rw [o4, K9 18 (by decide), r18s2],
              by rw [o8, u29.regs, K28 20 (by decide), r24s4, mem22, derTlvMem_ok0], ?_, ?_, ?_, ?_⟩
            · rw [show out + 0xC = out + BitVec.ofNat 32 0xC from rfl, ld 0xC (by decide) (by decide),
                show F + BitVec.ofNat 32 (0x18 + 0xC) = F + 0x20 + 4 by rw [BitVec.add_assoc]; rfl, mem22,
                derTlvMem_ok4]
            · rw [show out + 0x10 = out + BitVec.ofNat 32 0x10 from rfl, ld 0x10 (by decide) (by decide),
                show F + BitVec.ofNat 32 (0x18 + 0x10) = F + 0x20 + 8 by rw [BitVec.add_assoc]; rfl, mem22,
                derTlvMem_ok8]
            · rw [show out + 0x14 = out + BitVec.ofNat 32 0x14 from rfl, ld 0x14 (by decide) (by decide),
                show F + BitVec.ofNat 32 (0x18 + 0x14) = F + 0x20 + 0xC by rw [BitVec.add_assoc]; rfl, mem22,
                derTlvMem_okC]
            · rw [show out + 0x18 = out + BitVec.ofNat 32 0x18 from rfl, bt 0x18 (by decide) (by decide),
                show F + BitVec.ofNat 32 (0x18 + 0x18) = F + 0x20 + 0x10 by rw [BitVec.add_assoc]; rfl, mem22,
                derTlvMem_ok10]
          · obtain ⟨m29, d29, u29⟩ := u28.self.notTaken hc27 0x7E alg_at_7c (by decide)
              (by rw [r28a0, u28.self.zero]; exact beq_false_of_ne fun h => by
                    have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this
                    change _ = 0 at this; exact hfit (by omega))
            obtain ⟨m30, d30, u30⟩ := u29.aluImm hc27 alg_at_7e (off' := 0x80) (by decide)
            obtain ⟨m31, d31, u31⟩ := u30.jump hc27 alg_at_80 (off' := 0x90) (by decide) (by
              rw [u30.pc, show P + BitVec.ofNat 32 0x80 + 0x10 = P + BitVec.ofNat 32 0x90 by rw [BitVec.add_assoc]; rfl]
              exact even_bit0 (even_at P env.hP 0x90 (by decide)))
            obtain ⟨m32, c32, u32, hc32⟩ := errSt (b := 1) (rb := a0) u31.self hc27 alg_at_90 alg_at_94
              (by rw [u31.regs, upd_ne (by decide) (by decide), K28 21 (by decide), s21_24])
              (by rw [u31.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u28.self.zero]; rfl)
            obtain ⟨m33, d33, u33⟩ := u32.jump hc32 alg_at_98 (off' := 0xC8) (by decide) (by
              rw [u32.pc, show P + BitVec.ofNat 32 (0x90 + 8) + 0x30 = P + BitVec.ofNat 32 0xC8 by
                rw [BitVec.add_assoc]; rfl]
              exact even_bit0 (even_at P env.hP 0xC8 (by decide)))
            obtain ⟨n', S', pc', sp', k', fr', o0, o4⟩ :=
              errFin (S28.trans (.cons d29 (.cons d30 (.cons d31 (c32.trans (.single d33)))))) u33.self hc32 slot27
                m27G (by rw [u33.regs, u31.regs, upd_ne (by decide) (by decide), sp28])
                (fun q hq => by
                  rw [u33.regs, u31.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide),
                    K28 q (by revert hq; revert q; decide)]
                  exact Km24 q hq)
            have hspec : derAlgOf m.mem p n = .error 1 := by
              unfold derAlgOf; rw [hR]; dsimp only; rw [hO]; dsimp only; rw [ite_eq_right hz, hU]; dsimp only
              rw [ite_eq_right hfit]
            refine ⟨n', S', pc', sp', k', fr', ?_⟩
            rw [hspec]; exact ⟨o0, o4⟩

end C3.RV32
