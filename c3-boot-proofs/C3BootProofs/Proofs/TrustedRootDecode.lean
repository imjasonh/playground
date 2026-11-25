import C3BootProofs.Proofs.Base64Decode
import C3BootProofs.Proofs.JsonNextElement
import C3BootProofs.Proofs.JsonStr

/-!
# `trusted_root::decode`

`decode(text, free)` base64-decodes `text` into the front of the scratch
slice `free` and moves `free` past the bytes it wrote. The compiled function
calls `base64::decode_into`, which `base64DecodeInto_correct` proves.

`trustedRootDecode_correct` proves the function from its entry to its
return. When the text decodes and the bytes fit, `out` holds the decoded
slice and `free` holds the rest of the buffer. Otherwise `out` holds `Err`
and `free` keeps its value. The error byte is the one that `decode_into`
returned, which its theorem doesn't name. The `ScratchTooSmall` branch after
the call is dead: `decode_into` returns `Ok` only when the bytes fit.

The walk uses the steps of `JsonWp.lean` at the function's address in the
image. `WP.trCallSaved` steps over a call to a function whose theorem keeps
`sp` and the callee-saved registers, as the theorems of the functions at
fixed addresses do.
-/

namespace C3.RV32

open C3.Image

/-- Where `decode` is in the image. -/
abbrev TRDC : Word := BitVec.ofNat 32 trustedRootDecodeAddress

theorem trdc_at_0 : fetchRel trustedRootDecodeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem trdc_at_2 : fetchRel trustedRootDecodeCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem trdc_at_4 : fetchRel trustedRootDecodeCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem trdc_at_6 : fetchRel trustedRootDecodeCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem trdc_at_8 : fetchRel trustedRootDecodeCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem trdc_at_a : fetchRel trustedRootDecodeCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem trdc_at_c : fetchRel trustedRootDecodeCode 0xC = some (.alu .add (9 : Fin 32) x0 a3, 2) := by decide
theorem trdc_at_e : fetchRel trustedRootDecodeCode 0xE = some (.load .lw (18 : Fin 32) a3 0x0, 4) := by decide
theorem trdc_at_12 : fetchRel trustedRootDecodeCode 0x12 = some (.load .lw (8 : Fin 32) a3 0x4, 2) := by decide
theorem trdc_at_14 : fetchRel trustedRootDecodeCode 0x14 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem trdc_at_16 : fetchRel trustedRootDecodeCode 0x16 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem trdc_at_18 : fetchRel trustedRootDecodeCode 0x18 = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem trdc_at_1a : fetchRel trustedRootDecodeCode 0x1A = some (.alu .add a4 x0 (8 : Fin 32), 2) := by decide
theorem trdc_at_1c : fetchRel trustedRootDecodeCode 0x1C = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trdc_at_20 : fetchRel trustedRootDecodeCode 0x20 = some (.jalr ra ra 0xFFFFFD76, 4) := by decide
theorem trdc_at_24 : fetchRel trustedRootDecodeCode 0x24 = some (.load .lbu a0 sp 0x4, 4) := by decide
theorem trdc_at_28 : fetchRel trustedRootDecodeCode 0x28 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem trdc_at_2a : fetchRel trustedRootDecodeCode 0x2A = some (.load .lbu a0 sp 0x5, 4) := by decide
theorem trdc_at_2e : fetchRel trustedRootDecodeCode 0x2E = some (.jal x0 0x12, 2) := by decide
theorem trdc_at_30 : fetchRel trustedRootDecodeCode 0x30 = some (.load .lw a0 sp 0x8, 2) := by decide
theorem trdc_at_32 : fetchRel trustedRootDecodeCode 0x32 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem trdc_at_34 : fetchRel trustedRootDecodeCode 0x34 = some (.store .sw (9 : Fin 32) a1 0x0, 2) := by decide
theorem trdc_at_36 : fetchRel trustedRootDecodeCode 0x36 = some (.store .sw (9 : Fin 32) x0 0x4, 4) := by decide
theorem trdc_at_3a : fetchRel trustedRootDecodeCode 0x3A = some (.branch .bgeu (8 : Fin 32) a0 0x10, 4) := by decide
theorem trdc_at_3e : fetchRel trustedRootDecodeCode 0x3E = some (.aluImm .add a0 x0 0x13, 2) := by decide
theorem trdc_at_40 : fetchRel trustedRootDecodeCode 0x40 = some (.store .sw (19 : Fin 32) x0 0x0, 4) := by decide
theorem trdc_at_44 : fetchRel trustedRootDecodeCode 0x44 = some (.store .sb (19 : Fin 32) a0 0x4, 4) := by decide
theorem trdc_at_48 : fetchRel trustedRootDecodeCode 0x48 = some (.jal x0 0x14, 2) := by decide
theorem trdc_at_4a : fetchRel trustedRootDecodeCode 0x4A = some (.alu .add a1 (18 : Fin 32) a0, 4) := by decide
theorem trdc_at_4e : fetchRel trustedRootDecodeCode 0x4E = some (.alu .sub (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem trdc_at_50 : fetchRel trustedRootDecodeCode 0x50 = some (.store .sw (9 : Fin 32) a1 0x0, 2) := by decide
theorem trdc_at_52 : fetchRel trustedRootDecodeCode 0x52 = some (.store .sw (9 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem trdc_at_54 : fetchRel trustedRootDecodeCode 0x54 = some (.store .sw (19 : Fin 32) (18 : Fin 32) 0x0, 4) := by decide
theorem trdc_at_58 : fetchRel trustedRootDecodeCode 0x58 = some (.store .sw (19 : Fin 32) a0 0x4, 4) := by decide
theorem trdc_at_5c : fetchRel trustedRootDecodeCode 0x5C = some (.load .lw ra sp 0x1C, 2) := by decide
theorem trdc_at_5e : fetchRel trustedRootDecodeCode 0x5E = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem trdc_at_60 : fetchRel trustedRootDecodeCode 0x60 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem trdc_at_62 : fetchRel trustedRootDecodeCode 0x62 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem trdc_at_64 : fetchRel trustedRootDecodeCode 0x64 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem trdc_at_66 : fetchRel trustedRootDecodeCode 0x66 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem trdc_at_68 : fetchRel trustedRootDecodeCode 0x68 = some (.jalr x0 ra 0x0, 2) := by decide

/-- `rsimp`, and `mv` read as its source. -/
macro "trsimp" : tactic => `(tactic| simp +decide only [upd_app, clob_app, ↓reduceIte, ev0])

/-- The registers besides `sp` that a function keeps by the RISC-V calling
convention: `ra`, `gp`, `tp`, and `s0`–`s11`. -/
abbrev trSaved : List Nat := [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem tr_notClob : ∀ x : Fin 32, x ∉ jClob → x = 0 ∨ x = sp ∨ x.val ∈ trSaved := by decide

/-- A function returned to `g0 ra` with `sp` and the registers in `trSaved`
kept, and `R` of the memory. -/
def trPost (R : (Word → BitVec 8) → Prop) (g0 : Fin 32 → Word) : Post :=
  fun pc M g => pc = g0 ra ∧ g sp = g0 sp ∧ (∀ q : Fin 32, q.val ∈ trSaved → g q = g0 q) ∧ R M

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to a function that returns with `sp` and every register in
`trSaved` kept. -/
theorem WP.trCallSaved {P : Machine → Prop} {hi lo tb : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (base + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = tb)
    (hcallee : ∀ m1 : Machine, m1.pc = tb → m1.mem = M →
      (∀ x, reg m1 x = upd f ra (base + BitVec.ofNat 32 (off + 8)) x) → base.toNat % 2 = 0 →
      ∃ m2, Steps m1 m2 ∧ m2.pc = base + BitVec.ofNat 32 (off + 8) ∧ P m2 ∧ reg m2 sp = reg m1 sp ∧
        ∀ q : Fin 32, q.val ∈ trSaved → reg m2 q = reg m1 q)
    (hcode : ∀ m2 : Machine, P m2 → CodeIn M base code → CodeIn m2.mem base code)
    (k : ∀ m2 : Machine, P m2 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f :=
  WP.callGen h1 h2 htgt (fun m1 hpc hmem hreg hb => by
    obtain ⟨m2, c2, pc2, hP, hsp, hk⟩ := hcallee m1 hpc hmem hreg hb
    refine ⟨m2, c2, pc2, hP, fun x hx => ?_⟩
    rcases tr_notClob x hx with rfl | rfl | h
    · rfl
    · exact hsp
    · exact hk x h) hcode k

end

/-- A memory that agrees with `M` outside three ranges below `0x40000000`
agrees with it on the code. -/
theorem tr_hi3 {M M' : Word → BitVec 8} {a b c : Word} {k l n : Nat} (ha : a.toNat + k ≤ 0x40000000)
    (hb : b.toNat + l ≤ 0x40000000) (hc : c.toNat + n ≤ 0x40000000)
    (h : ∀ x, Sep a k x 1 → Sep b l x 1 → Sep c n x 1 → M' x = M x) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x := fun x hx =>
  h x (lowSep ha hx (by have := x.isLt; omega)) (lowSep hb hx (by have := x.isLt; omega))
    (lowSep hc hx (by have := x.isLt; omega))

/-- `decode` and the functions it calls. -/
structure TrDecCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TRDC trustedRootDecodeCode
  bdi : CodeIn M BDI base64DecodeIntoCode
  cw : CodeIn M BCW copyFromSliceU8Code
  stub : CodeIn M BMS memcpyStubCode
  body : CodeIn M BMB memcpyBodyCode

set_option maxRecDepth 20000 in
theorem TrDecCode.hi {M M' : Word → BitVec 8} (C : TrDecCode M)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : TrDecCode M' :=
  ⟨C.self.hi h (by decide) (by decide), C.bdi.hi h (by decide) (by decide), C.cw.hi h (by decide) (by decide),
    C.stub.hi h (by decide) (by decide), C.body.hi h (by decide) (by decide)⟩

/-- What `decode` returns when the text decodes to `d` and the scratch slice
has `fl` bytes: the decoded bytes when they fit. -/
def trDecodeRes (d : Option Bytes) (fl : Nat) : Option Bytes :=
  d.bind fun bs => if bs.length ≤ fl then some bs else none

/-- `out` and the scratch slice at `fr` after `decode`, when the slice was
the `fl` bytes at `fp`. `some bs` is `Ok(bs)`: `out` holds the slice of `bs`
at `fp`, and the scratch slice holds the rest of the buffer. `none` is
`Err`: `out` holds a null pointer, the niche of `Err`, and the scratch slice
is unchanged. -/
def TrDecOut (M : Word → BitVec 8) (out fr fp : Word) (fl : Nat) : Option Bytes → Prop
  | some bs => memLoad32 M out = fp ∧ memLoad32 M (out + 4) = BitVec.ofNat 32 bs.length ∧
      memLoad32 M fr = fp + BitVec.ofNat 32 bs.length ∧
      memLoad32 M (fr + 4) = BitVec.ofNat 32 (fl - bs.length) ∧ memBytes M fp bs.length = bs
  | none => memLoad32 M out = 0 ∧ memLoad32 M fr = fp ∧ memLoad32 M (fr + 4) = BitVec.ofNat 32 fl

/-- The memory part of `decode`'s postcondition: `r` at `out` and `fr`, and
no change outside the stack region `[G, G + 0x70)`, `out`, `fr`, and the
buffer. -/
def trDecMem (M0 : Word → BitVec 8) (G out fr fp : Word) (fl : Nat) (r : Option Bytes)
    (M : Word → BitVec 8) : Prop :=
  TrDecOut M out fr fp fl r ∧ ∀ x, Sep G 0x70 x 1 → Sep out 8 x 1 → Sep fr 8 x 1 → Sep fp fl x 1 → M x = M0 x

theorem trdc_ev_sub (a b : Word) : aluEval .sub a b = a - b := rfl

theorem trdc_zx8 : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide

theorem trdc_slot {M : Word → BitVec 8} {s v w : Word} (c d : Nat) (h : c + 4 ≤ d ∨ d + 4 ≤ c)
    (hc : c + 4 ≤ 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) (k : memLoad32 M (s + BitVec.ofNat 32 c) = w) :
    memLoad32 (memStore32 M (s + BitVec.ofNat 32 d) v) (s + BitVec.ofNat 32 c) = w :=
  ld_skip c d h hc hd k

section
variable {F : Word} {f g0 : Fin 32 → Word}

theorem trdc_saved_cases : ∀ q : Fin 32, q.val ∈ trSaved →
    q = ra ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] := by decide

/-- The epilogue at 0x5C: restores `ra` and `s0`–`s3` from the frame at
`F` and returns. -/
theorem trdc_epi {R : (Word → BitVec 8) → Prop} {Mf : Word → BitVec 8} (hsp : f sp = F)
    (e1 : memLoad32 Mf (F + 0x1C) = g0 ra) (e2 : memLoad32 Mf (F + 0x18) = g0 8)
    (e3 : memLoad32 Mf (F + 0x14) = g0 9) (e4 : memLoad32 Mf (F + 0x10) = g0 18)
    (e5 : memLoad32 Mf (F + 0xC) = g0 19) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x20)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hfr : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → f q = g0 q) (hR : R Mf) :
    WP trustedRootDecodeCode TRDC (trPost R g0) Mf 0x5C f := by
  refine WP.lw trdc_at_5c (by rw [hsp]; exact aligned_add hal (k := 0x1C) (by decide)) ?_; wn
  refine WP.lw trdc_at_5e (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x18) (by decide)) ?_; wn
  refine WP.lw trdc_at_60 (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x14) (by decide)) ?_; wn
  refine WP.lw trdc_at_62 (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x10) (by decide)) ?_; wn
  refine WP.lw trdc_at_64 (by trsimp; rw [hsp]; exact aligned_add hal (k := 0xC) (by decide)) ?_; wn
  refine WP.aluImm trdc_at_66 ?_; wn
  refine WP.ret trdc_at_68 ⟨?_, ?_, fun q hq => ?_, hR⟩
  · trsimp; rw [hsp, e1, add_lit_zero, hret]
  · trsimp; rw [hsp, hsp0]; rfl
  · rcases trdc_saved_cases q hq with rfl | rfl | rfl | rfl | rfl | h
    · trsimp; rw [hsp, e1]
    · trsimp; rw [hsp, e2]
    · trsimp; rw [hsp, e3]
    · trsimp; rw [hsp, e4]
    · trsimp; rw [hsp, e5]
    · have hn : q ≠ ra ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 18 ∧ q ≠ 19 ∧ q ≠ sp ∧ q.val ≠ 0 := by
        revert q; decide
      obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hn
      simp only [upd_app, n1, n2, n3, n4, n5, n6, n7, ↓reduceIte]
      exact hfr q h

end

theorem trSepR {a b : Word} {n k k' : Nat} (h : Sep a n b k) (hk : k' ≤ k) : Sep a n b k' :=
  (sep_low h.symm hk).symm

theorem tr_lowAt {a b : Word} {c k l : Nat} (h : a.toNat + c + k ≤ 0x40000000) (hb : 0x40000000 ≤ b.toNat)
    (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (a + BitVec.ofNat 32 c) k b l :=
  lowSep (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hb hbl

theorem tr_load2 {M M' : Word → BitVec 8} {a b c : Word} {k l : Nat}
    (h : ∀ x, Sep x 1 b k → Sep x 1 c l → M' x = M x) (hb : Sep b k a 4) (hc : Sep c l a 4) :
    memLoad32 M' a = memLoad32 M a :=
  memLoad32_congr fun _ hj => h _ (sep_pt hb hj) (sep_pt hc hj)

theorem trdc_rest_cases : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] →
    q = 3 ∨ q = 4 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨ q = 25 ∨ q = 26 ∨ q = 27 := by decide

theorem trdc_pair (M : Word → BitVec 8) (a v w : Word) :
    Out M (memStore32 (memStore32 M a v) (a + 4) w) a 8 ∧
      memLoad32 (memStore32 (memStore32 M a v) (a + 4) w) a = v ∧
      memLoad32 (memStore32 (memStore32 M a v) (a + 4) w) (a + 4) = w := by
  refine ⟨((out_store32 _ _ _).mono (by decide)).trans (Out.widen (d := 4) (out_store32 _ _ _) (by decide)),
    ?_, memLoad32_store32_same _ _ _⟩
  rw [memLoad32_store32_sep (sep_out04 a).symm, memLoad32_store32_same]

/-- The five saves of the prologue, into the frame at `F`. -/
def trdcSave (M : Word → BitVec 8) (F r1 r8 r9 r18 r19 : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (F + BitVec.ofNat 32 0x1C) r1)
    (F + BitVec.ofNat 32 0x18) r8) (F + BitVec.ofNat 32 0x14) r9) (F + BitVec.ofNat 32 0x10) r18)
    (F + BitVec.ofNat 32 0xC) r19

theorem trdcSave_spec (M : Word → BitVec 8) (F r1 r8 r9 r18 r19 : Word) :
    Out M (trdcSave M F r1 r8 r9 r18 r19) F 0x20 ∧
      memLoad32 (trdcSave M F r1 r8 r9 r18 r19) (F + BitVec.ofNat 32 0x1C) = r1 ∧
      memLoad32 (trdcSave M F r1 r8 r9 r18 r19) (F + BitVec.ofNat 32 0x18) = r8 ∧
      memLoad32 (trdcSave M F r1 r8 r9 r18 r19) (F + BitVec.ofNat 32 0x14) = r9 ∧
      memLoad32 (trdcSave M F r1 r8 r9 r18 r19) (F + BitVec.ofNat 32 0x10) = r18 ∧
      memLoad32 (trdcSave M F r1 r8 r9 r18 r19) (F + BitVec.ofNat 32 0xC) = r19 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((Out.upK rfl (out_store32 _ _ _) (by decide)).trans (Out.upK rfl (out_store32 _ _ _) (by decide))).trans
      (Out.upK rfl (out_store32 _ _ _) (by decide))).trans (Out.upK rfl (out_store32 _ _ _) (by decide))).trans
      (Out.upK rfl (out_store32 _ _ _) (by decide))
  · exact trdc_slot 0x1C 0xC (by decide) (by decide) (by decide) <|
      trdc_slot 0x1C 0x10 (by decide) (by decide) (by decide) <|
      trdc_slot 0x1C 0x14 (by decide) (by decide) (by decide) <|
      trdc_slot 0x1C 0x18 (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact trdc_slot 0x18 0xC (by decide) (by decide) (by decide) <|
      trdc_slot 0x18 0x10 (by decide) (by decide) (by decide) <|
      trdc_slot 0x18 0x14 (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact trdc_slot 0x14 0xC (by decide) (by decide) (by decide) <|
      trdc_slot 0x14 0x10 (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact trdc_slot 0x10 0xC (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact memLoad32_store32_same _ _ _

section
variable {M0 : Word → BitVec 8} {G out t fr fp : Word} {n fl : Nat} {f : Fin 32 → Word}

set_option maxHeartbeats 4000000 in
theorem trdc_wp (h0 : f a0 = out) (h1 : f a1 = t) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = fr)
    (hsp : f sp = G + BitVec.ofNat 32 0x70) (hret : f ra &&& ~~~1 = f ra)
    (hC : TrDecCode M0) (hGa : G.toNat % 4 = 0) (hGw : G.toNat + 0x70 ≤ 0x40000000)
    (hoa : out.toNat % 4 = 0) (how : out.toNat + 8 ≤ 0x40000000)
    (hfa : fr.toNat % 4 = 0) (hfw : fr.toNat + 8 ≤ 0x40000000)
    (hfp : memLoad32 M0 fr = fp) (hfl : memLoad32 M0 (fr + 4) = BitVec.ofNat 32 fl)
    (hbw : fp.toNat + fl ≤ 0x40000000) (htw : t.toNat + n ≤ 0x40000000)
    (sOG : Sep out 8 G 0x70) (sFG : Sep fr 8 G 0x70) (sBG : Sep fp fl G 0x70) (sTG : Sep t n G 0x70)
    (sTB : Sep t n fp fl) (sOB : Sep out 8 fp fl) (sFB : Sep fr 8 fp fl) (sOF : Sep out 8 fr 8) :
    WP trustedRootDecodeCode TRDC
      (trPost (fun M => trDecMem M0 G out fr fp fl (trDecodeRes (base64Decode (memBytes M0 t n)) fl) M ∧
        (trDecodeRes (base64Decode (memBytes M0 t n)) fl = none →
          M (out + 4) = BitVec.ofNat 8 (bdiErr (memBytes M0 t n) fl))) f) M0 0 f := by
  refine WP.zero fun hz => ?_
  have hGc : ∀ c, c ≤ 0x70 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hlow : ∀ {a : Word} {k : Nat}, a.toNat + k ≤ 0x40000000 → Sep a k TRDC trustedRootDecodeCode.length :=
    fun h => lowSep h (by decide) (by decide)
  have hlo : ∀ {a : Word} {c k : Nat}, a.toNat + c + k ≤ 0x40000000 →
      Sep (a + BitVec.ofNat 32 c) k TRDC trustedRootDecodeCode.length :=
    fun h => tr_lowAt h (by decide) (by decide)
  refine WP.aluImm trdc_at_0 ?_; wn
  rw [show aluEval .add (f sp) 0xFFFFFFE0 = G + BitVec.ofNat 32 0x50 by rw [hsp, ev_add, BitVec.add_assoc]; rfl]
  generalize hF : G + BitVec.ofNat 32 0x50 = F
  have hFG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x50 + c) := fun c => by
    rw [← hF, add_ofNat_assoc]
  have hFn : F.toNat = G.toNat + 0x50 := by rw [← hF]; exact hGc _ (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have hFs : ∀ {c w : Nat}, 0x50 + c + w ≤ 0x70 →
      Sep (F + BitVec.ofNat 32 c) w TRDC trustedRootDecodeCode.length :=
    fun hc => by rw [hFG]; exact hlo (by omega)
  refine WP.sw trdc_at_2 (by trsimp; exact aligned_add hFa (k := 0x1C) (by decide))
    (by trsimp; exact hFs (by decide)) ?_; wn
  refine WP.sw trdc_at_4 (by trsimp; exact aligned_add hFa (k := 0x18) (by decide))
    (by trsimp; exact hFs (by decide)) ?_; wn
  refine WP.sw trdc_at_6 (by trsimp; exact aligned_add hFa (k := 0x14) (by decide))
    (by trsimp; exact hFs (by decide)) ?_; wn
  refine WP.sw trdc_at_8 (by trsimp; exact aligned_add hFa (k := 0x10) (by decide))
    (by trsimp; exact hFs (by decide)) ?_; wn
  refine WP.sw trdc_at_a (by trsimp; exact aligned_add hFa (k := 0xC) (by decide))
    (by trsimp; exact hFs (by decide)) ?_; wn
  change WP trustedRootDecodeCode TRDC _ (trdcSave M0 F (f ra) (f 8) (f 9) (f 18) (f 19)) 0xC _
  obtain ⟨hO1, v1, v2, v3, v4, v5⟩ := trdcSave_spec M0 F (f ra) (f 8) (f 9) (f 18) (f 19)
  generalize trdcSave M0 F (f ra) (f 8) (f 9) (f 18) (f 19) = M1 at hO1 v1 v2 v3 v4 v5
  have hO1G : Out M0 M1 G 0x70 := Out.upK hF hO1 (by decide)
  have hC1 : TrDecCode M1 := hC.hi fun x hx => hO1G x (lowSep hGw hx (by have := x.isLt; omega)).symm
  have hfp1 : memLoad32 M1 fr = fp := (hO1G.load32 (sep_low sFG (by decide)).symm).trans hfp
  have hfl1 : memLoad32 M1 (fr + 4) = BitVec.ofNat 32 fl :=
    (hO1G.load32 (sFG.sub (c := 4) (l := 4) (by decide)).symm).trans hfl
  have hd1 : memBytes M1 t n = memBytes M0 t n := hO1G.bytes sTG.symm
  refine WP.alu trdc_at_c ?_; wn
  refine WP.lw trdc_at_e (by trsimp; rw [h3, add_lit_zero]; exact hfa) ?_; wn
  refine WP.lw trdc_at_12 (by trsimp; rw [h3]; exact aligned_add hfa (k := 4) (by decide)) ?_; wn
  refine WP.alu trdc_at_14 ?_; wn
  refine WP.aluImm trdc_at_16 ?_; wn
  refine WP.alu trdc_at_18 ?_; wn
  refine WP.alu trdc_at_1a ?_; wn
  have hFB : F + 0xFFFFFFB0 = G := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero G
  have hF4 : F + 4 = G + BitVec.ofNat 32 0x54 := hFG 4
  have sR : Sep (F + 4) 8 G 0x50 := by
    rw [hF4]
    have := sep_offsets G (c := 0x54) (n := 8) (d := 0) (k := 0x50) (Or.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have sRB : Sep (F + 4) 8 fp fl := by rw [hF4]; exact (sBG.subR (c := 0x54) (l := 8) (by decide)).symm
  have hRn : (F + 4).toNat = G.toNat + 0x54 := by rw [hF4]; exact hGc _ (by decide)
  refine WP.trCallSaved (tb := BDI)
    (P := fun m2 => ∃ m1 : Machine, m1.mem = M1 ∧
      BdiResult m1 F (F + 4) t fp (TRDC + BitVec.ofNat 32 (0x1C + 8)) n fl m2)
    trdc_at_1c trdc_at_20 (by decide) (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP hc => ?_) (fun m2 hP => ?_)
  · obtain ⟨m2, c2, R⟩ := base64DecodeInto_correct m1 (sp0 := F) (res := F + 4) (t := t) (out := fp) (n := n)
      (L := fl) (retAddr := TRDC + BitVec.ofNat 32 (0x1C + 8))
      (by rw [hmem1]; exact hC1.bdi) (by rw [hmem1]; exact hC1.cw) (by rw [hmem1]; exact hC1.stub)
      (by rw [hmem1]; exact hC1.body) hpc1
      (by rw [hreg1]; trsimp; rw [ev_add]) (by rw [hreg1]; trsimp; exact h1) (by rw [hreg1]; trsimp; exact h2)
      (by rw [hreg1]; trsimp; rw [h3, add_lit_zero, hfp1]) (by rw [hreg1]; trsimp; rw [h3, hfl1])
      (by rw [hreg1]; trsimp) (by decide) (by rw [hreg1]; trsimp) hFa (by omega) (by omega) (by omega)
      (by rw [hF4]; exact aligned_add hGa (by decide)) hbw htw
      (by rw [hFB]; exact trSepR sBG (by decide)) (by rw [hFB]; exact trSepR sTG (by decide))
      (by rw [hFB]; exact sR) sTB sRB
    exact ⟨m2, c2, R.1, ⟨m1, hmem1, R⟩, by rw [R.2.1, hreg1]; trsimp, R.2.2.1⟩
  · obtain ⟨m1, hm1, -, -, -, -, -, fr2⟩ := hP
    refine hc.hi (tr_hi3 (a := G) (b := fp) (c := F + 4) (k := 0x50) (l := fl) (n := 8) (by omega) hbw (by omega) ?_) (by decide) (by decide)
    intro x s1 s2 s3; rw [← hm1]; exact fr2 x (by rw [hFB]; exact s1) s2 s3
  · obtain ⟨m1, hm1, -, -, -, ok2, err2, fr2⟩ := hP
    rw [hm1, hd1] at ok2 err2
    rw [hm1, hFB] at fr2
    generalize m2.mem = M2 at ok2 err2 fr2 ⊢
    have hM2 : ∀ x, Sep x 1 G 0x70 → Sep x 1 fp fl → M2 x = M0 x := fun x hG hB => by
      rw [← hO1G x hG]
      refine fr2 x ?_ hB.symm ?_
      · have := hG.subR (c := 0) (l := 0x50) (by decide); rw [add_ofNat_zero] at this; exact this.symm
      · rw [hF4]; exact (hG.subR (c := 0x54) (l := 8) (by decide)).symm
    have hS2 : ∀ c, 0xC ≤ c → c + 4 ≤ 0x20 →
        memLoad32 M2 (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) := by
      intro c hc1 hc2
      refine memLoad32_congr fun j hj => ?_
      rw [hFG, add_ofNat_assoc]
      refine fr2 _ ?_ ?_ ?_
      · have := sep_offsets G (c := 0) (n := 0x50) (d := 0x50 + c + j) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at this
      · exact sBG.subR (c := 0x50 + c + j) (l := 1) (by omega)
      · rw [hF4]
        exact sep_offsets G (c := 0x54) (n := 8) (d := 0x50 + c + j) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)
    have hcase : (trDecodeRes (base64Decode (memBytes M0 t n)) fl = none ∧ M2 (F + 4) = 1 ∧
          M2 (F + 4 + 1) = BitVec.ofNat 8 (bdiErr (memBytes M0 t n) fl)) ∨
        ∃ bs, trDecodeRes (base64Decode (memBytes M0 t n)) fl = some bs ∧ bs.length ≤ fl ∧ M2 (F + 4) = 0 ∧
          memLoad32 M2 (F + 4 + 4) = BitVec.ofNat 32 bs.length ∧ memBytes M2 fp bs.length = bs := by
      rcases hdd : base64Decode (memBytes M0 t n) with _ | bs
      · exact Or.inl ⟨rfl, err2 fun bs h => by rw [hdd] at h; cases h⟩
      · by_cases hl : bs.length ≤ fl
        · obtain ⟨e0, e1, e2⟩ := ok2 bs hdd hl
          exact Or.inr ⟨bs, by simp [trDecodeRes, hl], hl, e0, e1, e2⟩
        · refine Or.inl ⟨by simp [trDecodeRes, hl], err2 fun bs' h => ?_⟩
          rw [hdd] at h; cases h; omega
    have hslot : ∀ {Mf : Word → BitVec 8}, (∀ x, Sep x 1 out 8 → Sep x 1 fr 8 → Mf x = M2 x) →
        ∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 Mf (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
      fun hMf c hc1 hc2 => by
        rw [← hS2 c hc1 hc2]
        refine memLoad32_congr fun j hj => ?_
        rw [hFG, add_ofNat_assoc]
        exact hMf _ (sOG.subR (c := 0x50 + c + j) (l := 1) (by omega)).symm
          (sFG.subR (c := 0x50 + c + j) (l := 1) (by omega)).symm
    have hM2l : ∀ {a : Word}, Sep G 0x70 a 4 → Sep fp fl a 4 → memLoad32 M2 a = memLoad32 M0 a :=
      fun hG hB => tr_load2 hM2 hG hB
    have hsp0 : f sp = F + BitVec.ofNat 32 0x20 := by rw [hsp, ← hF, add_ofNat_assoc]
    have hfl32 : fl < 2 ^ 32 := by omega
    rcases hcase with ⟨hr, hb1, hbe⟩ | ⟨bs, hr, hl, hb0, hlen, hbytes⟩
    · rw [hr]
      refine WP.lbu trdc_at_24 ?_; wn
      refine WP.branch trdc_at_28 (fun ht => ?_) (fun _ => ?_)
      · exfalso; revert ht; trsimp; rw [hb1]; decide
      refine WP.lbu trdc_at_2a ?_; wn
      refine WP.jal trdc_at_2e (by decide) ?_; wn
      refine WP.sw trdc_at_40 (by trsimp; rw [h0, add_lit_zero]; exact hoa) (by trsimp; rw [h0, add_lit_zero]; exact hlow (by omega)) ?_
      wn
      refine WP.sb trdc_at_44 (by trsimp; rw [h0]; exact hlo (c := 4) (by omega)) ?_; wn
      refine WP.jal trdc_at_48 (by decide) ?_; wn
      simp only [ev0, h0, add_lit_zero]
      generalize hb : BitVec.extractLsb' 0 8 _ = b
      obtain ⟨hOe, he0, -⟩ := sliceRes_err M2 out b
      have hOe' : ∀ x, Sep x 1 out 8 → Sep x 1 fr 8 → memStore8 (memStore32 M2 out 0) (out + 4) b x = M2 x :=
        fun x h _ => hOe x h
      refine trdc_epi (by trsimp) ((hslot hOe' 0x1C (by decide) (by decide)).trans v1)
        ((hslot hOe' 0x18 (by decide) (by decide)).trans v2) ((hslot hOe' 0x14 (by decide) (by decide)).trans v3)
        ((hslot hOe' 0x10 (by decide) (by decide)).trans v4) ((hslot hOe' 0xC (by decide) (by decide)).trans v5)
        hsp0 hret hFa (fun q hq => by
          rcases trdc_rest_cases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trsimp)
        ⟨⟨⟨he0, ?_, ?_⟩, fun x sG sO sF sB => (hOe x sO.symm).trans (hM2 x sG.symm sB.symm)⟩, fun _ => ?_⟩
      · rw [Out.load32 hOe (trSepR sOF (by decide)), hM2l (sep_low sFG (by decide)).symm
          (sep_low sFB (by decide)).symm, hfp]
      · refine (Out.load32 hOe (a := fr + 4) (sOF.subR (c := 4) (l := 4) (by decide))).trans ?_
        exact (hM2l (a := fr + 4) (sFG.sub (c := 4) (l := 4) (by decide)).symm
          (sFB.sub (c := 4) (l := 4) (by decide)).symm).trans hfl
      · rw [memStore8_same, ← hb, trdc_zx8, ← hbe, show F + 4 + 1 = F + 5 by rw [BitVec.add_assoc]; rfl]
    · rw [hr]
      have hbs : bs.length < 2 ^ 32 := by omega
      refine WP.lbu trdc_at_24 ?_; wn
      refine WP.branch trdc_at_28 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hb0]; decide))
      wn
      have hF8 : F + 4 + 4 = F + BitVec.ofNat 32 8 := by rw [BitVec.add_assoc]; rfl
      refine WP.lw trdc_at_30 (by trsimp; exact aligned_add hFa (k := 8) (by decide)) ?_; wn
      rw [show F + 8 = F + 4 + 4 by rw [hF8]; rfl, hlen]
      refine WP.aluImm trdc_at_32 ?_; wn
      refine WP.sw trdc_at_34 (by trsimp; rw [h3, add_lit_zero]; exact hfa) (by trsimp; rw [h3, add_lit_zero]; exact hlow (by omega)) ?_
      wn
      refine WP.sw trdc_at_36 (by trsimp; rw [h3]; exact aligned_add hfa (k := 4) (by decide))
        (by trsimp; rw [h3]; exact hlo (c := 4) (by omega)) ?_; wn
      refine WP.branch trdc_at_3a (fun _ => ?_) (fun hf => by
        exfalso; revert hf; trsimp; rw [h3, hfl1, br_bgeu hfl32 hbs]; intro hf
        exact absurd (not_dec_false hf) (by omega))
      wn
      refine WP.alu trdc_at_4a ?_; wn
      refine WP.alu trdc_at_4e ?_; wn
      refine WP.sw trdc_at_50 (by trsimp; rw [h3, add_lit_zero]; exact hfa) (by trsimp; rw [h3, add_lit_zero]; exact hlow (by omega)) ?_
      wn
      refine WP.sw trdc_at_52 (by trsimp; rw [h3]; exact aligned_add hfa (k := 4) (by decide))
        (by trsimp; rw [h3]; exact hlo (c := 4) (by omega)) ?_; wn
      refine WP.sw trdc_at_54 (by trsimp; rw [h0, add_lit_zero]; exact hoa) (by trsimp; rw [h0, add_lit_zero]; exact hlow (by omega)) ?_
      wn
      refine WP.sw trdc_at_58 (by trsimp; rw [h0]; exact aligned_add hoa (k := 4) (by decide))
        (by trsimp; rw [h0]; exact hlo (c := 4) (by omega)) ?_; wn
      simp only [ev0, h0, h3, hfp1, hfl1, add_lit_zero]
      simp only [ev_add, trdc_ev_sub]
      rw [sub_ofNat_le hl hfl32]
      obtain ⟨hOa, -, -⟩ := trdc_pair M2 fr 1 0
      obtain ⟨hOb, hb1, hb2⟩ := trdc_pair (memStore32 (memStore32 M2 fr 1) (fr + 4) 0) fr
        (fp + BitVec.ofNat 32 bs.length) (BitVec.ofNat 32 (fl - bs.length))
      generalize memStore32 (memStore32 (memStore32 (memStore32 M2 fr 1) (fr + 4) 0) fr
        (fp + BitVec.ofNat 32 bs.length)) (fr + 4) (BitVec.ofNat 32 (fl - bs.length)) = M5 at hOb hb1 hb2 ⊢
      have hO5 := hOa.trans hOb
      obtain ⟨hOc, hc1, hc2⟩ := trdc_pair M5 out fp (BitVec.ofNat 32 bs.length)
      generalize memStore32 (memStore32 M5 out fp) (out + 4) (BitVec.ofNat 32 bs.length) = M7 at hOc hc1 hc2 ⊢
      have hM7 : ∀ x, Sep x 1 out 8 → Sep x 1 fr 8 → M7 x = M2 x := fun x so sf =>
        (hOc x so).trans (hO5 x sf)
      refine trdc_epi (by trsimp) ((hslot hM7 0x1C (by decide) (by decide)).trans v1)
        ((hslot hM7 0x18 (by decide) (by decide)).trans v2) ((hslot hM7 0x14 (by decide) (by decide)).trans v3)
        ((hslot hM7 0x10 (by decide) (by decide)).trans v4) ((hslot hM7 0xC (by decide) (by decide)).trans v5)
        hsp0 hret hFa (fun q hq => by
          rcases trdc_rest_cases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trsimp)
        ⟨⟨⟨hc1, hc2, ?_, ?_, ?_⟩, fun x sG sO sF sB => (hM7 x sO.symm sF.symm).trans (hM2 x sG.symm sB.symm)⟩,
          fun h => by cases h⟩
      · rw [hOc.load32 (trSepR sOF (by decide)), hb1]
      · exact (hOc.load32 (a := fr + 4) (sOF.subR (c := 4) (l := 4) (by decide))).trans hb2
      · rw [hOc.bytes (trSepR sOB hl), hO5.bytes (trSepR sFB hl), hbytes]

end

/-- `trusted_root::decode(text, free)` called with `out` in `a0`, the `n`
bytes of text at `t` in `a1` and `a2`, and the scratch slice `free` at `fr`
in `a3`, which holds the `fl` bytes at `fp`. It returns with the callee-saved
registers kept, its result at `out` and the rest of the scratch slice at
`fr`, as `trDecMem` says: the decoded bytes, written to the start of the
scratch buffer, when the text decodes and fits; otherwise `Err`, with `fr`
unchanged and the error byte that `bdiErr` names at `out + 4`. Below `sp` it uses 0x70 bytes, 0x20 of its own and 0x50 for
`base64::decode_into`. -/
theorem trustedRootDecode_correct (m : Machine) {sp0 out t fr fp retAddr : Word} {n fl : Nat}
    (hc : TrDecCode m.mem) (hpc : m.pc = TRDC) (ha0 : reg m a0 = out) (ha1 : reg m a1 = t)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (ha3 : reg m a3 = fr) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0)
    (hsl : 0x70 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000) (hoa : out.toNat % 4 = 0)
    (how : out.toNat + 8 ≤ 0x40000000) (hfa : fr.toNat % 4 = 0) (hfw : fr.toNat + 8 ≤ 0x40000000)
    (hfp : memLoad32 m.mem fr = fp) (hfl : memLoad32 m.mem (fr + 4) = BitVec.ofNat 32 fl)
    (hbw : fp.toNat + fl ≤ 0x40000000) (htw : t.toNat + n ≤ 0x40000000)
    (sOG : Sep out 8 (sp0 + 0xFFFFFF90) 0x70) (sFG : Sep fr 8 (sp0 + 0xFFFFFF90) 0x70)
    (sBG : Sep fp fl (sp0 + 0xFFFFFF90) 0x70) (sTG : Sep t n (sp0 + 0xFFFFFF90) 0x70)
    (sTB : Sep t n fp fl) (sOB : Sep out 8 fp fl) (sFB : Sep fr 8 fp fl) (sOF : Sep out 8 fr 8) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q : Fin 32, q.val ∈ trSaved → reg m' q = reg m q) ∧
      trDecMem m.mem (sp0 + 0xFFFFFF90) out fr fp fl (trDecodeRes (base64Decode (memBytes m.mem t n)) fl) m'.mem ∧
      (trDecodeRes (base64Decode (memBytes m.mem t n)) fl = none →
        m'.mem (out + 4) = BitVec.ofNat 8 (bdiErr (memBytes m.mem t n) fl)) := by
  have hG : (sp0 + 0xFFFFFF90 : Word).toNat = sp0.toNat - 0x70 := by
    rw [BitVec.toNat_add, show (0xFFFFFF90 : Word).toNat = 2 ^ 32 - 0x70 from rfl]; omega
  obtain ⟨m', hs, hpc', hsp', hk, hR⟩ := WP.run (trdc_wp (f := reg m) (M0 := m.mem) (G := sp0 + 0xFFFFFF90)
    ha0 ha1 ha2 ha3 (by rw [hsp, BitVec.add_assoc]; exact (BitVec.add_zero sp0).symm) (by rw [hra]; exact hret)
    hc (by omega) (by omega) hoa how hfa hfw hfp hfl hbw htw sOG sFG sBG sTG sTB sOB sFB sOF) (by decide) hc.self hpc
  exact ⟨m', hs, hpc'.trans hra, hsp'.trans hsp, hk, hR⟩

end C3.RV32
