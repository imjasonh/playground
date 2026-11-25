import C3BootProofs.Proofs.TufCalls
import C3BootProofs.Image.BootloaderData8

/-!
# `tuf::expires`, as compiled

`expires(meta)` reads `meta.signed.field("expires")`, takes the string's
body with `str`, and parses it with `time::rfc3339`. The compiler passes the
`signed` value's slice in `a1` and `a2` and the result's address in `a0`. A
`Result<u64, TufError>` keeps its tag byte at `out`, the error byte at
`out + 1`, and the time's low and high words at `out + 8` and `out + 0xC`.

The function keeps two registers in a 0x30-byte frame, and `field` uses 260
more bytes, so the stack region is the 308 bytes below `sp`.
`tufExpires_correct` is the contract, against `expiresModel`.
-/

namespace C3.Json

/-- The bytes between a string value's quotes, as `Value::str` reads them. -/
def strBody (v : Bytes) : Option Bytes :=
  if v.length < 2 then none
  else if v.getD 0 0 ≠ 34 then none
  else if v.getD (v.length - 1) 0 ≠ 34 then none
  else some ((v.drop 1).take (v.length - 2))

/-- `tuf::expires` on the `signed` value `d`: the time, or the error byte
(`0x21` for a missing or non-string `expires`, `0x20` for JSON outside the
profile, `0x19` for a time `time::rfc3339` rejects). -/
def expiresModel (d : Bytes) : Except Nat Nat :=
  match objField d (ascii!"expires") with
  | .error e => .error e
  | .ok (vp, vl) =>
    match strBody ((d.drop vp).take vl) with
    | none => .error 0x21
    | some t =>
      match rfc3339 t with
      | some v => .ok v
      | none => .error 0x19

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

abbrev TEX : Word := BitVec.ofNat 32 tufExpiresAddress
abbrev TEX_JF : Word := BitVec.ofNat 32 jsonFieldAddress
abbrev TEX_JS : Word := BitVec.ofNat 32 jsonStrAddress
abbrev TEX_KEY : Word := BitVec.ofNat 32 tufExpiresKeyAddress

theorem tex_at_0 : fetchRel tufExpiresCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem tex_at_2 : fetchRel tufExpiresCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem tex_at_4 : fetchRel tufExpiresCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem tex_at_6 : fetchRel tufExpiresCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem tex_at_8 : fetchRel tufExpiresCode 0x8 = some (.lui a3 0x3FCC5000, 4) := by decide
theorem tex_at_c : fetchRel tufExpiresCode 0xC = some (.aluImm .add a3 a3 0xFFFFF8B7, 4) := by decide
theorem tex_at_10 : fetchRel tufExpiresCode 0x10 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem tex_at_12 : fetchRel tufExpiresCode 0x12 = some (.aluImm .add a4 x0 0x7, 2) := by decide
theorem tex_at_14 : fetchRel tufExpiresCode 0x14 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem tex_at_18 : fetchRel tufExpiresCode 0x18 = some (.jalr ra ra 0xFFFFFA8E, 4) := by decide
theorem tex_at_1c : fetchRel tufExpiresCode 0x1C = some (.load .lw a1 sp 0x20, 2) := by decide
theorem tex_at_1e : fetchRel tufExpiresCode 0x1E = some (.branch .beq a1 x0 0x2A, 2) := by decide
theorem tex_at_20 : fetchRel tufExpiresCode 0x20 = some (.load .lw a2 sp 0x24, 2) := by decide
theorem tex_at_22 : fetchRel tufExpiresCode 0x22 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem tex_at_24 : fetchRel tufExpiresCode 0x24 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem tex_at_28 : fetchRel tufExpiresCode 0x28 = some (.jalr ra ra 0xFFFFFABA, 4) := by decide
theorem tex_at_2c : fetchRel tufExpiresCode 0x2C = some (.load .lw a1 sp 0x18, 2) := by decide
theorem tex_at_2e : fetchRel tufExpiresCode 0x2E = some (.branch .beq a1 x0 0x20, 2) := by decide
theorem tex_at_30 : fetchRel tufExpiresCode 0x30 = some (.load .lw a2 sp 0x1C, 2) := by decide
theorem tex_at_32 : fetchRel tufExpiresCode 0x32 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem tex_at_34 : fetchRel tufExpiresCode 0x34 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem tex_at_38 : fetchRel tufExpiresCode 0x38 = some (.jalr ra ra 0x29A, 4) := by decide
theorem tex_at_3c : fetchRel tufExpiresCode 0x3C = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem tex_at_40 : fetchRel tufExpiresCode 0x40 = some (.branch .beq a0 x0 0x24, 2) := by decide
theorem tex_at_42 : fetchRel tufExpiresCode 0x42 = some (.load .lbu a0 sp 0x9, 4) := by decide
theorem tex_at_46 : fetchRel tufExpiresCode 0x46 = some (.jal x0 0xC, 2) := by decide
theorem tex_at_48 : fetchRel tufExpiresCode 0x48 = some (.load .lbu a0 sp 0x24, 4) := by decide
theorem tex_at_4c : fetchRel tufExpiresCode 0x4C = some (.jal x0 0x6, 2) := by decide
theorem tex_at_4e : fetchRel tufExpiresCode 0x4E = some (.load .lbu a0 sp 0x1C, 4) := by decide
theorem tex_at_52 : fetchRel tufExpiresCode 0x52 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem tex_at_54 : fetchRel tufExpiresCode 0x54 = some (.store .sb (8 : Fin 32) a1 0x0, 4) := by decide
theorem tex_at_58 : fetchRel tufExpiresCode 0x58 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem tex_at_5c : fetchRel tufExpiresCode 0x5C = some (.load .lw ra sp 0x2C, 2) := by decide
theorem tex_at_5e : fetchRel tufExpiresCode 0x5E = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem tex_at_60 : fetchRel tufExpiresCode 0x60 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem tex_at_62 : fetchRel tufExpiresCode 0x62 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tex_at_64 : fetchRel tufExpiresCode 0x64 = some (.load .lw a0 sp 0x10, 2) := by decide
theorem tex_at_66 : fetchRel tufExpiresCode 0x66 = some (.load .lw a1 sp 0x14, 2) := by decide
theorem tex_at_68 : fetchRel tufExpiresCode 0x68 = some (.store .sb (8 : Fin 32) x0 0x0, 4) := by decide
theorem tex_at_6c : fetchRel tufExpiresCode 0x6C = some (.store .sw (8 : Fin 32) a0 0x8, 2) := by decide
theorem tex_at_6e : fetchRel tufExpiresCode 0x6E = some (.store .sw (8 : Fin 32) a1 0xC, 2) := by decide
theorem tex_at_70 : fetchRel tufExpiresCode 0x70 = some (.jal x0 0xFFFFFFEC, 2) := by decide

/-- The code `expires` runs, and the key it looks up. -/
structure TexCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TEX tufExpiresCode
  field : FieldCode M TEX_JF
  str : CodeIn M TEX_JS jsonStrCode
  rfc : CodeIn M RFC timeRfc3339Code
  dt : CodeIn M DT dateTimeCode
  td : CodeIn M TD timeDigits2Code
  td4 : CodeIn M TD4 timeDigits4Code
  aad : CodeIn M AAD allAsciiDigitCode
  key : CodeIn M TEX_KEY tufExpiresKeyData

/-- What `expires` leaves: memory outside the 308 bytes at `s` and the 16
bytes at `out` as before, and `r` at `out`. -/
def TexRes (M M' : Word → BitVec 8) (s out : Word) : Except Nat Nat → Prop
  | .ok t => (∀ x, Sep x 1 s 308 → Sep x 1 out 16 → M' x = M x) ∧ M' out = 0 ∧
      memLoad32 M' (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧ memLoad32 M' (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)
  | .error e => (∀ x, Sep x 1 s 308 → Sep x 1 out 16 → M' x = M x) ∧ M' out = 1 ∧
      M' (out + 1) = BitVec.ofNat 8 e

section
variable {M0 : Word → BitVec 8} {s out F : Word} {f g0 : Fin 32 → Word}

theorem tex_epi {R : (Word → BitVec 8) → Prop} {Mf : Word → BitVec 8} (hsp : f sp = F)
    (e1 : memLoad32 Mf (F + 0x2C) = g0 ra) (e2 : memLoad32 Mf (F + 0x28) = g0 8)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ jClob ++ [ra, sp, 8] → f x = g0 x) (hR : R Mf) :
    WP tufExpiresCode TEX (RPost (g0 ra) R g0) Mf 0x5C f := by
  refine WP.lw tex_at_5c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x2C) (by decide)) ?_; wn
  refine WP.lw tex_at_5e (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x28) (by decide)) ?_; wn
  refine WP.aluImm tex_at_60 ?_; wn
  refine WP.ret tex_at_62 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]

theorem tex_toNat {a : Word} {c : Nat} (h : a.toNat + c < 2 ^ 32) : (a + BitVec.ofNat 32 c).toNat = a.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega), Nat.mod_eq_of_lt h]

/-- The two byte stores of an error, at `out` and `out + 1`, give `TexRes`. -/
theorem tex_err_res {M Mf : Word → BitVec 8} (e : Nat) (hO : ∀ x, Sep x 1 s 308 → Mf x = M x) :
    TexRes M (memStore8 (memStore8 Mf out (BitVec.extractLsb' 0 8 (1 : Word))) (out + 1)
      (BitVec.ofNat 8 e)) s out (.error e) := by
  refine ⟨fun x h1 h2 => ?_, ?_, memStore8_same _ _ _⟩
  · rw [memStore8_ne (sep_byte1 h2 (by decide)), memStore8_ne (sep_byte0 h2 (by decide))]; exact hO x h1
  · rw [memStore8_ne (ne_add_one out).symm, memStore8_same]; rfl

theorem tex_codeIn {M M' : Word → BitVec 8} {k : Nat} {b : Word} {code : List Nat} (h : CodeIn M b code)
    (hO : Out M M' s k) (hs : s.toNat + k ≤ 0x40000000) (hb : 0x40000000 ≤ b.toNat)
    (hbl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn M' b code :=
  hO.codeIn h (lowSep hs hb hbl)

theorem TexCode.of_out {M M' : Word → BitVec 8} {k : Nat} (h : TexCode M) (hO : Out M M' s k)
    (hs : s.toNat + k ≤ 0x40000000) (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize) :
    TexCode M' :=
  ⟨tex_codeIn h.self hO hs (by decide) (by decide),
    ⟨tex_codeIn h.field.field hO hs (by decide) (by decide), h.field.get.out hO (tuf_fieldSep hs hro).get⟩,
    tex_codeIn h.str hO hs (by decide) (by decide), tex_codeIn h.rfc hO hs (by decide) (by decide),
    tex_codeIn h.dt hO hs (by decide) (by decide), tex_codeIn h.td hO hs (by decide) (by decide),
    tex_codeIn h.td4 hO hs (by decide) (by decide), tex_codeIn h.aad hO hs (by decide) (by decide),
    hO.codeIn h.key (tuf_sep_ro hro (by decide) (by decide))⟩

theorem tex_key {M : Word → BitVec 8} (h : TexCode M) : memBytes M TEX_KEY 7 = ascii!"expires" :=
  tuf_codeIn_memBytes h.key (by decide)

/-- `strRes` is `strBody` with the body's address and length. -/
theorem tex_strRes (q : Word) (d : Bytes) : strRes q d = (strBody d).map fun b => (q + 1, b.length) := by
  unfold strRes strBody
  split
  · rfl
  split
  · rfl
  split
  · rfl
  simp only [Option.map_some, List.length_take, List.length_drop]
  congr 2
  omega

theorem tex_body {v b : Bytes} (h : strBody v = some b) : 2 ≤ v.length ∧ b = (v.drop 1).take (v.length - 2) := by
  unfold strBody at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  exact ⟨by omega, rfl⟩

theorem tex_sepR {a b : Word} {n k l : Nat} (h : Sep a n b k) (hl : l ≤ k) : Sep a n b l :=
  fun i hi j hj => h i hi j (by omega)

theorem tex_sepL {a b : Word} {n k l : Nat} (h : Sep a n b k) (hl : l ≤ n) : Sep a l b k :=
  fun i hi j hj => h i (by omega) j hj

theorem tex_sepS {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 2 ^ 32) : Sep s n (s + BitVec.ofNat 32 d) k := by
  have := sep_offsets s (c := 0) (n := n) (d := d) (k := k) (Or.inl (by omega)) (by omega) hd
  rwa [add_ofNat_zero] at this

theorem tex_upd_keep {g : Fin 32 → Word} {rd : Fin 32} {v : Word} (hrd : rd ∈ jClob) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ jClob ++ [ra, sp, 8] → g x = g0 x) :
    ∀ x, x ∉ jClob ++ [ra, sp, 8] → upd g rd v x = g0 x := fun x hx => by
  have hx1 : x ≠ rd := fun h => hx (by subst h; exact List.mem_append_left _ hrd)
  by_cases h0 : x.val = 0
  · have : x = 0 := Fin.ext h0
    subst this; simp only [upd, h0, ↓reduceIte]; exact hz0.symm
  · simp only [upd, h0, hx1, ↓reduceIte]; exact hfr x hx

/-- The error tail at 0x52: the tag byte 1 at `out`, the error byte at
`out + 1`, and the epilogue. -/
theorem tex_tail {Mf : Word → BitVec 8} {g : Fin 32 → Word} {e : Nat} (h8 : g 8 = out) (hsp : g sp = F)
    (ha0 : (g a0).extractLsb' 0 8 = BitVec.ofNat 8 e) (hz : g 0 = 0) (e1 : memLoad32 Mf (F + 0x2C) = g0 ra)
    (e2 : memLoad32 Mf (F + 0x28) = g0 8) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30)
    (hret : g0 ra &&& ~~~1 = g0 ra) (halF : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ jClob ++ [ra, sp, 8] → g x = g0 x) (hOf : ∀ x, Sep x 1 s 308 → Mf x = M0 x)
    (how : out.toNat + 16 ≤ 0x40000000) (ho2C : Sep out 16 (F + BitVec.ofNat 32 0x2C) 4)
    (ho28 : Sep out 16 (F + BitVec.ofNat 32 0x28) 4) :
    WP tufExpiresCode TEX (RPost (g0 ra) (fun M' => TexRes M0 M' s out (.error e)) g0) Mf 0x52 g := by
  have hoT : Sep out 16 TEX tufExpiresCode.length := lowSep how (by decide) (by decide)
  refine WP.aluImm tex_at_52 ?_; wn
  refine WP.sb tex_at_54 (by rsimp; rw [h8, add_lit_zero]; exact tex_sepL hoT (by decide)) ?_; wn
  refine WP.sb tex_at_58 (by rsimp; rw [h8]; exact hoT.sub (c := 1) (l := 1) (by decide)) ?_; wn
  (try rsimp)
  rw [h8, add_lit_zero, hz, ev0, ha0]
  have hOs : Out Mf (memStore8 (memStore8 Mf out (BitVec.extractLsb' 0 8 (1 : Word))) (out + 1)
      (BitVec.ofNat 8 e)) out 16 :=
    ((out_store8 _ _ _).mono (by decide)).trans (Out.widen (d := 1) (out_store8 _ _ _) (by decide))
  exact tex_epi (by rsimp; exact hsp) ((hOs.load32 ho2C).trans e1) ((hOs.load32 ho28).trans e2) hsp0 hret halF hz0
    (tex_upd_keep (rd := a1) (by decide) hz0 hfr) (tex_err_res e hOf)

/-- The success tail at 0x64: the time's words from the frame to `out + 8`
and `out + 0xC`, the tag byte 0 at `out`, and the epilogue. -/
theorem tex_tail_ok {Mf : Word → BitVec 8} {g : Fin 32 → Word} {t : Nat} (h8 : g 8 = out) (hsp : g sp = F)
    (lo : memLoad32 Mf (F + 0x10) = BitVec.ofNat 32 (t % 2 ^ 32))
    (hi : memLoad32 Mf (F + 0x14) = BitVec.ofNat 32 (t / 2 ^ 32)) (e1 : memLoad32 Mf (F + 0x2C) = g0 ra)
    (e2 : memLoad32 Mf (F + 0x28) = g0 8) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30)
    (hret : g0 ra &&& ~~~1 = g0 ra) (halF : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ jClob ++ [ra, sp, 8] → g x = g0 x) (hOf : ∀ x, Sep x 1 s 308 → Mf x = M0 x)
    (halo : out.toNat % 4 = 0) (how : out.toNat + 16 ≤ 0x40000000)
    (ho2C : Sep out 16 (F + BitVec.ofNat 32 0x2C) 4) (ho28 : Sep out 16 (F + BitVec.ofNat 32 0x28) 4) :
    WP tufExpiresCode TEX (RPost (g0 ra) (fun M' => TexRes M0 M' s out (.ok t)) g0) Mf 0x64 g := by
  have hoT : Sep out 16 TEX tufExpiresCode.length := lowSep how (by decide) (by decide)
  refine WP.lw tex_at_64 (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 0x10) (by decide)) ?_; wn
  refine WP.lw tex_at_66 (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 0x14) (by decide)) ?_; wn
  refine WP.sb tex_at_68 (by rsimp; rw [h8, add_lit_zero]; exact tex_sepL hoT (by decide)) ?_; wn
  refine WP.sw tex_at_6c (by rsimp; rw [h8]; exact aligned_add halo (k := 8) (by decide))
    (by rsimp; rw [h8]; exact hoT.sub (c := 8) (l := 4) (by decide)) ?_; wn
  refine WP.sw tex_at_6e (by rsimp; rw [h8]; exact aligned_add halo (k := 0xC) (by decide))
    (by rsimp; rw [h8]; exact hoT.sub (c := 0xC) (l := 4) (by decide)) ?_; wn
  refine WP.jal tex_at_70 (by decide) ?_; wn
  (try rsimp)
  rw [h8, add_lit_zero, hsp, lo, hi]
  generalize hM : memStore32 (memStore32 (memStore8 Mf out (BitVec.extractLsb' 0 8 (0 : Word))) (out + 8)
    (BitVec.ofNat 32 (t % 2 ^ 32))) (out + 0xC) (BitVec.ofNat 32 (t / 2 ^ 32)) = Mf'
  have hOs : Out Mf Mf' out 16 := by
    rw [← hM]
    exact (((out_store8 _ _ _).mono (by decide)).trans (Out.widen (d := 8) (out_store32 _ _ _) (by decide))).trans
      (Out.widen (d := 0xC) (out_store32 _ _ _) (by decide))
  have s8C : Sep (out + 8) 4 (out + 0xC) 4 := sep_offsets out (c := 8) (d := 0xC) (Or.inl (by decide)) (by decide) (by decide)
  have s0C : Sep out 1 (out + 0xC) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 0xC) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    rw [add_ofNat_zero] at this; exact this
  have s08 : Sep out 1 (out + 8) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 8) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    rw [add_ofNat_zero] at this; exact this
  refine tex_epi (Mf := Mf') (by rsimp; exact hsp) ((hOs.load32 ho2C).trans e1) ((hOs.load32 ho28).trans e2) hsp0
    hret halF hz0 (tex_upd_keep (rd := a1) (by decide) hz0 (tex_upd_keep (rd := a0) (by decide) hz0 hfr))
    ⟨fun x h1 h2 => (hOs x h2).trans (hOf x h1), ?_, ?_, ?_⟩
  · rw [← hM, memStore32_get_sep s0C.symm, memStore32_get_sep s08.symm, memStore8_same]; rfl
  · rw [← hM, memLoad32_store32_sep s8C.symm, memLoad32_store32_same]
  · rw [← hM, memLoad32_store32_same]

theorem objField_val {d key : Bytes} {vp vl : Nat} (h : objField d key = .ok (vp, vl)) :
    vp < d.length ∧ vp + vl ≤ d.length := by
  unfold objField at h
  split at h
  · cases h
  · cases h
  · cases h; exact objGet_val (by assumption)

end

section
variable {M0 : Word → BitVec 8} {s out p : Word} {n : Nat} {f : Fin 32 → Word}

set_option maxHeartbeats 2000000 in
theorem tex_wp (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = s + BitVec.ofNat 32 308) (hret : f ra &&& ~~~1 = f ra) (hal : s.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hsw : s.toNat + 308 ≤ 0x40000000)
    (hro : Sep s 308 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (hp0 : p.toNat ≠ 0)
    (hpw : p.toNat + n + 4 ≤ 0x40000000) (hSp : Sep s 308 p (n + 4)) (how : out.toNat + 16 ≤ 0x40000000)
    (hso : Sep out 16 s 308) (hc : TexCode M0) :
    WP tufExpiresCode TEX (RPost (f ra) (fun M' => TexRes M0 M' s out (expiresModel (memBytes M0 p n))) f)
      M0 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFD0 = s + 260 := by rw [hsp, ev_add, BitVec.add_assoc]; rfl
  refine WP.aluImm tex_at_0 ?_; wn
  rw [esp]
  generalize hF : s + 260 = F
  have hF' : s + BitVec.ofNat 32 260 = F := hF
  have hFn : F.toNat = s.toNat + 260 := by rw [← hF']; exact tex_toNat (by omega)
  have halF : F.toNat % 4 = 0 := by omega
  have hsp0 : f sp = F + BitVec.ofNat 32 0x30 := by rw [hsp, ← hF', BitVec.add_assoc]; rfl
  have hFc : ∀ c, F + BitVec.ofNat 32 c = s + BitVec.ofNat 32 (260 + c) := fun c => by rw [← hF', add_ofNat_assoc]
  have hFN : ∀ {c}, c ≤ 48 → (F + BitVec.ofNat 32 c).toNat = s.toNat + 260 + c := fun hc => by
    rw [tex_toNat (by omega), hFn]
  -- A frame word and the code.
  have hFT : ∀ {c w : Nat}, c + w ≤ 48 → Sep (F + BitVec.ofNat 32 c) w TEX tufExpiresCode.length :=
    fun hc => lowSep (by rw [hFN (by omega)]; omega) (by decide) (by decide)
  -- A frame word inside the region.
  have hFs : ∀ {c w : Nat}, c + w ≤ 48 → ∀ {a : Word} {l : Nat}, Sep s 308 a l →
      Sep (F + BitVec.ofNat 32 c) w a l := fun hc _ _ h => by rw [hFc]; exact h.sub (by omega)
  have hsN : s.toNat + 308 < 2 ^ 32 := by omega
  have hFS : ∀ {n c k : Nat}, n ≤ 260 + c → 260 + c + k ≤ 2 ^ 32 → Sep s n (F + BitVec.ofNat 32 c) k :=
    fun h1 h2 => by rw [hFc]; exact tex_sepS h1 h2
  refine WP.sw tex_at_2 (by rsimp; exact aligned_add halF (k := 0x2C) (by decide))
    (by rsimp; exact hFT (by decide)) ?_; wn
  refine WP.sw tex_at_4 (by rsimp; exact aligned_add halF (k := 0x28) (by decide))
    (by rsimp; exact hFT (by decide)) ?_; wn
  change WP tufExpiresCode TEX _ (memStore32 (memStore32 M0 (F + 0x2C) (f ra)) (F + 0x28) (f 8)) 0x6 _
  have v1 : memLoad32 (memStore32 (memStore32 M0 (F + 0x2C) (f ra)) (F + 0x28) (f 8)) (F + 0x2C) = f ra :=
    (memLoad32_store32_sep (sep_offsets F (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by decide))
      (by decide) (by decide))).trans (memLoad32_store32_same _ _ _)
  have v2 : memLoad32 (memStore32 (memStore32 M0 (F + 0x2C) (f ra)) (F + 0x28) (f 8)) (F + 0x28) = f 8 :=
    memLoad32_store32_same _ _ _
  have hO1 : Out M0 (memStore32 (memStore32 M0 (F + 0x2C) (f ra)) (F + 0x28) (f 8)) s 308 :=
    (Out.upK (c := 304) (hFc 0x2C).symm (out_store32 _ _ _) (by decide)).trans
      (Out.upK (c := 300) (hFc 0x28).symm (out_store32 _ _ _) (by decide))
  generalize memStore32 (memStore32 M0 (F + 0x2C) (f ra)) (F + 0x28) (f 8) = M1 at v1 v2 hO1
  have hSpn : Sep s 308 p n := tex_sepR hSp (by omega)
  have hd1 : memBytes M1 p n = memBytes M0 p n := hO1.bytes hSpn
  -- Everything after the prologue writes only below the saved registers.
  have hCk : ∀ {Mk : Word → BitVec 8}, Out M1 Mk s 300 → TexCode Mk := fun h =>
    hc.of_out (hO1.trans (h.mono (by decide))) hsw hro
  have hVk : ∀ {Mk : Word → BitVec 8}, Out M1 Mk s 300 →
      memLoad32 Mk (F + 0x2C) = f ra ∧ memLoad32 Mk (F + 0x28) = f 8 := fun h =>
    ⟨(h.load32 (hFS (c := 0x2C) (by decide) (by decide))).trans v1,
      (h.load32 (hFS (c := 0x28) (by decide) (by decide))).trans v2⟩
  have hBk : ∀ {Mk : Word → BitVec 8}, Out M1 Mk s 300 → memBytes Mk p n = memBytes M0 p n := fun h =>
    (h.bytes (tex_sepL hSpn (by decide))).trans hd1
  have hc1 : TexCode M1 := hCk (fun _ _ => rfl)
  have hSb : ∀ {k}, k ≤ 308 → Sep s k TEX tufExpiresCode.length := fun hk =>
    lowSep (by omega) (by decide) (by decide)
  -- The call to `field`.
  refine WP.alu tex_at_6 ?_; wn
  refine WP.lui tex_at_8 ?_; wn
  refine WP.aluImm tex_at_c ?_; wn
  refine WP.aluImm tex_at_10 ?_; wn
  refine WP.aluImm tex_at_12 ?_; wn
  refine WP.callField (tb := TEX_JF) (out := F + 0x20) (s := s) (p := p) (kq := TEX_KEY) (n := n) (kl := 7)
    tex_at_14 tex_at_18 (by decide) (by decide) (by decide) hc1.field
    (by (try rsimp); (try rw [ev_add])) (by (try rsimp); exact h1) (by (try rsimp); exact h2)
    (by (try rsimp); (try decide)) (by (try rsimp); (try decide)) (by (try rsimp); exact hF'.symm)
    hal (aligned_add halF (k := 0x20) (by decide)) (by omega) (by decide) hp0 (by omega)
    (tuf_fieldSep (by omega) (sep_low hro (by decide))) (tex_sepL hSpn (by decide))
    (tuf_sep_ro (sep_low hro (by decide)) (by decide) (by decide))
    (hFS (c := 0x20) (by decide) (by decide)).symm
    (lowSep (a := F + BitVec.ofNat 32 0x20) (by rw [hFN (by decide)]; omega) (by decide) (by decide))
    (hSb (by decide)) (hFT (by decide))
    fun m2 hR => ?_
  rw [hd1, tex_key hc1] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hFR⟩ := hR
  have hO2 : Out M1 M2 s 300 := (hOa.mono (by decide)).trans (Out.upK (c := 292) (hFc 0x20).symm hFR.out (by decide))
  obtain ⟨e1, e2⟩ := hVk hO2
  have ho2C : Sep out 16 (F + BitVec.ofNat 32 0x2C) 4 := by rw [hFc]; exact hso.subR (by decide)
  have ho28 : Sep out 16 (F + BitVec.ofNat 32 0x28) 4 := by rw [hFc]; exact hso.subR (by decide)
  refine WP.zero fun hz2 => ?_
  refine WP.lw tex_at_1c (by (try rsimp); exact aligned_add halF (k := 0x20) (by decide)) ?_; wn
  unfold expiresModel
  rcases hof : objField (memBytes M0 p n) (ascii!"expires") with e | ⟨vp, vl⟩ <;> rw [hof] at hFR
  · -- `field` failed.
    obtain ⟨-, t1, t2⟩ := hFR
    refine WP.branch tex_at_1e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [t1] at eb; exact absurd eb (by decide)
    refine WP.lbu tex_at_48 ?_; wn
    refine WP.jal tex_at_4c (by decide) ?_; wn
    have t2' : M2 (F + 0x24) = BitVec.ofNat 8 e := by
      rw [show F + 0x24 = F + 32 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    exact tex_tail (by rsimp; (try simp only [ev0]); exact h0) (by rsimp) (by rsimp; rw [t2', ri_ze]) (by rsimp)
      e1 e2 hsp0 hret halF hz (by keepz hz) (hO1.trans (hO2.mono (by decide))) how ho2C ho28
  · -- `field` found the value at `p + vp`.
    obtain ⟨-, t1, t2⟩ := hFR
    have t2' : memLoad32 M2 (F + 0x24) = BitVec.ofNat 32 vl := by
      rw [show F + 0x24 = F + 32 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    have hv := objField_val hof
    rw [memBytes_length] at hv
    have hq0 := nx_q0 hp0 (n := n) (pos := vp) (by omega) hv.1
    refine WP.branch tex_at_1e (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [t1, hq0] at eb; exact absurd eb (by decide)
    refine WP.lw tex_at_20 (by (try rsimp); exact aligned_add halF (k := 0x24) (by decide)) ?_; wn
    refine WP.aluImm tex_at_22 ?_; wn
    -- The call to `str`.
    refine WP.callStr (tb := TEX_JS) (out := F + 0x18) (p := p + BitVec.ofNat 32 vp) (n := vl)
      tex_at_24 tex_at_28 (by decide) (by decide) (by decide) (hCk hO2).str (by (try rsimp); (try rw [ev_add]))
      (by (try rsimp); exact t1) (by (try rsimp); exact t2') (by omega) (aligned_add halF (k := 0x18) (by decide))
      (lowSep (a := F + BitVec.ofNat 32 0x18) (by rw [hFN (by decide)]; omega) (by decide) (by decide))
      (hFT (by decide)) fun m3 hS => ?_
    have hSv : Sep s 300 (p + BitVec.ofNat 32 vp) vl := (tex_sepL hSpn (by decide)).subR (by omega)
    rw [(hO2.bytes hSv).trans (hO1.bytes (hSpn.subR (by omega))), tex_strRes] at hS
    generalize m3.mem = M3 at hS
    have hO3 : Out M1 M3 s 300 := hO2.trans (Out.upK (c := 284) (hFc 0x18).symm hS.out (by decide))
    obtain ⟨e1, e2⟩ := hVk hO3
    refine WP.zero fun hz3 => ?_
    refine WP.lw tex_at_2c (by (try rsimp); exact aligned_add halF (k := 0x18) (by decide)) ?_; wn
    rw [tuf_memBytes_drop_take hv.2]
    rcases hsb : strBody (memBytes M0 (p + BitVec.ofNat 32 vp) vl) with _ | b <;>
      rw [hsb] at hS <;> simp only [Option.map_none, Option.map_some] at hS
    · -- Not a string.
      obtain ⟨-, t1, t2⟩ := hS
      refine WP.branch tex_at_2e (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [t1] at eb; exact absurd eb (by decide)
      refine WP.lbu tex_at_4e ?_; wn
      have t2' : M3 (F + 0x1C) = BitVec.ofNat 8 0x21 := by
        rw [show F + 0x1C = F + 0x18 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
      exact tex_tail (by rsimp; (try simp only [ev0]); exact h0) (by rsimp) (by rsimp; rw [t2', ri_ze]) (by rsimp)
        e1 e2 hsp0 hret halF hz (by keepz hz) (hO1.trans (hO3.mono (by decide))) how ho2C ho28
    · -- A string: parse its body.
      obtain ⟨-, t1, t2⟩ := hS
      obtain ⟨hb2, hbe⟩ := tex_body hsb
      rw [memBytes_length] at hb2 hbe
      rw [tuf_memBytes_drop_take (by omega), add_ofNat_assoc] at hbe
      have hbl : b.length = vl - 2 := by rw [hbe, memBytes_length]
      have hpq : p + BitVec.ofNat 32 vp + 1 = p + BitVec.ofNat 32 (vp + 1) := add_ofNat_assoc p vp 1
      have t1' : memLoad32 M3 (F + 0x18) = p + BitVec.ofNat 32 (vp + 1) := t1.trans hpq
      have t2' : memLoad32 M3 (F + 0x1C) = BitVec.ofNat 32 b.length := by
        rw [show F + 0x1C = F + 0x18 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
      have hq1 := nx_q0 hp0 (n := n) (pos := vp + 1) (by omega) (by omega)
      refine WP.branch tex_at_2e (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; (try rsimp at eb); rw [t1', hq1] at eb; exact absurd eb (by decide)
      refine WP.lw tex_at_30 (by (try rsimp); exact aligned_add halF (k := 0x1C) (by decide)) ?_; wn
      refine WP.aluImm tex_at_32 ?_; wn
      -- The call to `time::rfc3339`, with its frame the 0x90 bytes below `F`.
      have hG : F + 0xFFFFFF70 = s + BitVec.ofNat 32 116 := by rw [← hF', BitVec.add_assoc]; rfl
      have hqN : (p + BitVec.ofNat 32 (vp + 1)).toNat = p.toNat + (vp + 1) := tex_toNat (by omega)
      have hc3 := hCk hO3
      refine WP.callRfc (sp0 := F) (out := F + 8) (p := p + BitVec.ofNat 32 (vp + 1)) (n := b.length)
        tex_at_34 tex_at_38 (by decide) (by decide) hc3.rfc hc3.dt hc3.td hc3.td4 hc3.aad
        (by (try rsimp); (try rw [ev_add])) (by (try rsimp); exact t1') (by (try rsimp); exact t2') (by rsimp)
        halF (by omega) (by omega) (by rw [show F + 8 = F + BitVec.ofNat 32 8 from rfl, hFN (by decide)]; omega)
        (aligned_add halF (k := 8) (by decide))
        (by rw [hqN]; omega)
        (by rw [hG]; show Sep (F + BitVec.ofNat 32 8) 16 _ _; rw [hFc]
            exact sep_offsets s (Or.inr (by decide)) (by decide) (by decide))
        (by rw [hG]; exact (hSp.symm.sub (c := vp + 1) (l := b.length + 4) (by omega)).subR (by decide))
        (by rw [hG]; exact lowSep (by rw [tex_toNat (by omega)]; omega) (by decide) (by decide))
        (hFT (by decide)) fun m4 hR => ?_
      have hbq : memBytes M3 (p + BitVec.ofNat 32 (vp + 1)) b.length = b := by
        have hS1 : Sep s 300 (p + BitVec.ofNat 32 (vp + 1)) b.length :=
          (tex_sepL hSpn (by decide)).subR (by omega)
        rw [(hO3.bytes hS1).trans (hO1.bytes (hSpn.subR (by omega))), hbl, ← hbe]
      unfold RfcRes at hR
      rw [hbq] at hR
      generalize m4.mem = M4 at hR
      obtain ⟨hok, hno, hfr4⟩ := hR
      have hO4 : Out M1 M4 s 300 := hO3.trans fun x hx => hfr4 x
        (by rw [hG]; exact (hx.symm.sub (c := 116) (l := 144) (by decide)))
        (by show Sep (F + BitVec.ofNat 32 8) 16 x 1; rw [hFc]; exact (hx.symm.sub (c := 268) (l := 16) (by decide)))
      obtain ⟨e1, e2⟩ := hVk hO4
      refine WP.zero fun hz4 => ?_
      refine WP.lbu tex_at_3c ?_; wn
      rcases hrf : rfc3339 b with _ | t
      · -- `time::rfc3339` rejected the body.
        obtain ⟨r1, r2⟩ := hno hrf
        refine WP.branch tex_at_40 (fun eb => ?_) (fun _ => ?_) <;> wn
        · exfalso; (try rsimp at eb); rw [r1] at eb; exact absurd eb (by decide)
        refine WP.lbu tex_at_42 ?_; wn
        refine WP.jal tex_at_46 (by decide) ?_; wn
        have r2' : M4 (F + 9) = BitVec.ofNat 8 0x19 := by
          rw [show F + 9 = F + 8 + 1 by rw [BitVec.add_assoc]; rfl]; exact r2
        exact tex_tail (by rsimp; (try simp only [ev0]); exact h0) (by rsimp) (by rsimp; rw [r2', ri_ze])
          (by rsimp) e1 e2 hsp0 hret halF hz (by keepz hz) (hO1.trans (hO4.mono (by decide))) how ho2C ho28
      · -- The time.
        obtain ⟨-, r1, r2, r3⟩ := hok t hrf
        refine WP.branch tex_at_40 (fun _ => ?_) (fun eb => ?_) <;> wn
        rotate_left
        · exfalso; (try rsimp at eb); rw [r1] at eb; exact absurd eb (by decide)
        have r2' : memLoad32 M4 (F + 0x10) = BitVec.ofNat 32 (t % 2 ^ 32) := by
          rw [show F + 0x10 = F + 8 + 8 by rw [BitVec.add_assoc]; rfl]; exact r2
        have r3' : memLoad32 M4 (F + 0x14) = BitVec.ofNat 32 (t / 2 ^ 32) := by
          rw [show F + 0x14 = F + 8 + 0xC by rw [BitVec.add_assoc]; rfl]; exact r3
        exact tex_tail_ok (by rsimp; (try simp only [ev0]); exact h0) (by rsimp) r2' r3' e1 e2 hsp0 hret halF hz
          (by keepz hz) (hO1.trans (hO4.mono (by decide))) halo how ho2C ho28

end

/-- `tuf::expires` on the `n` bytes at `p`, the `signed` value's slice in
`a1` and `a2`, with the result at `out` in `a0` and the stack the 308 bytes
below `sp`. It returns to `ra` with `expiresModel` of those bytes at `out`,
memory outside the stack and the 16 bytes at `out` as before, and every
register outside `jClob` as before. The stack and `out` lie below the code,
the stack is apart from the read-only data window, and the input bytes, with
the 4 bytes after them that `time::rfc3339` may read, are apart from the
stack. -/
theorem tufExpires_correct (m : Machine) {retAddr out s p : Word} {n : Nat}
    (hc : TexCode m.mem) (hpc : m.pc = TEX) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hsp : reg m sp = s + BitVec.ofNat 32 308) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hsw : s.toNat + 308 ≤ 0x40000000) (hro : Sep s 308 (BitVec.ofNat 32 roWindowAddress) roWindowSize)
    (hp0 : p.toNat ≠ 0) (hpw : p.toNat + n + 4 ≤ 0x40000000) (hSp : Sep s 308 p (n + 4))
    (how : out.toNat + 16 ≤ 0x40000000) (hso : Sep out 16 s 308) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ TexRes m.mem m'.mem s out (expiresModel (memBytes m.mem p n)) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (tex_wp ha0 ha1 ha2 hsp (by rw [hra]; exact hret) hal halo hsw hro
    hp0 hpw hSp how hso hc) (by decide) hc.self hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
