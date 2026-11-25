import C3BootProofs.Proofs.JsonField
import C3BootProofs.Proofs.JsonStr
import C3BootProofs.Proofs.TimeRfc3339

/-!
# Calls from the TUF metadata checks

One lemma for each function that the checks in `c3_verify::tuf` call: from
the call instruction, with the arguments in registers, to the instruction
after it, with what the callee left in memory and the registers it may
change taken from the machine it returned.
-/

namespace C3.RV32

open C3.Image C3.Json

/-- A range apart from the read-only window is apart from each range inside
it. -/
theorem tuf_sep_ro {s a : Word} {k l : Nat} (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize)
    (h1 : roWindowAddress ≤ a.toNat) (h2 : a.toNat + l ≤ roWindowAddress + roWindowSize) : Sep s k a l := by
  have hA : roWindowAddress = (img% roWindowAddress) := rfl
  have hS : roWindowSize = (img% roWindowSize) := rfl
  rw [hA] at hro h1 h2
  rw [hS] at hro h2
  intro i hi j hj e
  refine hro i hi (a.toNat - (img% roWindowAddress) + j) (by omega) ?_
  rw [e]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show (img% roWindowAddress) < 2 ^ 32 by decide)]
  omega

/-- The bytes of `code` in memory that holds it. -/
theorem tuf_codeIn_memBytes {M : Word → BitVec 8} {base : Word} {code : List Nat} (C : CodeIn M base code)
    (hb : ∀ b ∈ code, b < 256) : memBytes M base code.length = code := by
  unfold memBytes
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [C i h2]
    unfold byteAt
    rw [BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))

theorem tuf_memBytes_drop_take {M : Word → BitVec 8} {p : Word} {n h l : Nat} (hl : h + l ≤ n) :
    ((memBytes M p n).drop h).take l = memBytes M (p + BitVec.ofNat 32 h) l := by
  unfold memBytes
  rw [← List.map_drop, ← List.map_take]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, List.length_range]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [add_ofNat_assoc]

set_option maxRecDepth 100000 in
/-- The stack below the code and apart from the read-only window is apart
from `field` and its callees at their addresses in the image. -/
theorem tuf_fieldSep {s : Word} {k : Nat} (hs : s.toNat + k ≤ 0x40000000)
    (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize) :
    FieldSep s k (BitVec.ofNat 32 jsonFieldAddress) :=
  ⟨lowSep hs (by decide) (by decide),
    ⟨lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide),
      lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide),
      lowSep hs (by decide) (by decide),
      ⟨lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide),
        lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide), lowSep hs (by decide) (by decide),
        lowSep hs (by decide) (by decide), tuf_sep_ro hro (by decide) (by decide),
        tuf_sep_ro hro (by decide) (by decide)⟩⟩⟩

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `field(key)` on the `n` bytes at `p`, with the key the `kl`
bytes at `kq` and the code at `tb`. -/
theorem WP.callField {hi lo tb p kq out s : Word} {n kl : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : FieldCode M tb) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = kq)
    (ha4 : f a4 = BitVec.ofNat 32 kl) (hsp : f sp = s + BitVec.ofNat 32 260)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hsw : s.toNat + 260 < 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hfs : FieldSep s 260 tb) (hSp : Sep s 260 p n)
    (hSk : Sep s 260 kq kl) (hso : Sep out 8 s 260) (hsc : Sep out 8 tb jsonFieldCode.length)
    (hSb : Sep s 260 base code.length) (hsb : Sep out 8 base code.length)
    (k : ∀ m2 : Machine, FieldResF M m2.mem out s 260 (fieldRes p (objField (memBytes M p n) (memBytes M kq kl))) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => FieldResF M m2.mem out s 260 (fieldRes p (objField (memBytes M p n) (memBytes M kq kl))))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hU⟩ := hP
      exact hU.out.codeIn (hO.codeIn hc hSb) hsb) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonField_correct m1 (base := tb) (out := out) (s := s) (p := p) (kq := kq)
    (n := n) (kl := kl) htb (by rw [hmem1]; exact hct) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact ha3)
    (by rw [hreg1]; rsimp; exact ha4) (by rw [hreg1]; rsimp; exact hsp)
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hal halo hsw hkl hp0 hpn hfs hSp hSk hso hsc
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

/-- A call to `str()` on the `n` bytes at `p`, with the code at `tb`. -/
theorem WP.callStr {hi lo tb p out : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonStrCode) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32) (hal : out.toNat % 4 = 0) (hsep : Sep out 8 tb jsonStrCode.length)
    (hsb : Sep out 8 base code.length)
    (k : ∀ m2 : Machine, SliceRes M m2.mem out 0x21 (strRes p (memBytes M p n)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 strClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := strClob)
    (P := fun m2 => SliceRes M m2.mem out 0x21 (strRes p (memBytes M p n)))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.out.codeIn hc hsb) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonStr_correct m1 (base := tb) (out := out) (p := p) (n := n) htb
    (by rw [hmem1]; exact hct) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) hn hal hsep (retAddr := base + BitVec.ofNat 32 (off + 8))
    (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

/-- What `time::rfc3339` leaves at `out` for the `n` bytes at `p`, with its
stack the 0x90 bytes below `sp0`. -/
def RfcRes (M M' : Word → BitVec 8) (sp0 out p : Word) (n : Nat) : Prop :=
  (∀ t, rfc3339 (memBytes M p n) = some t → t < 2 ^ 64 ∧ M' out = 0 ∧
    memLoad32 M' (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧ memLoad32 M' (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
  (rfc3339 (memBytes M p n) = none → M' out = 1 ∧ M' (out + 1) = 0x19) ∧
  ∀ x, Sep (sp0 + 0xFFFFFF70) 0x90 x 1 → Sep out 16 x 1 → M' x = M x

/-- A call to `time::rfc3339` on the `n` bytes at `p`. -/
theorem WP.callRfc {hi lo sp0 p out : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = RFC) (hev : (off + 8) % 2 = 0)
    (hcR : CodeIn M RFC timeRfc3339Code) (hcD : CodeIn M DT dateTimeCode)
    (hcT : CodeIn M TD timeDigits2Code) (hcF : CodeIn M TD4 timeDigits4Code)
    (hcA : CodeIn M AAD allAsciiDigitCode) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x90 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 16 ≤ 0x40000000) (hoa : out.toNat % 4 = 0) (hpw : p.toNat + n + 4 ≤ 0x40000000)
    (sOG : Sep out 16 (sp0 + 0xFFFFFF70) 0x90) (sPG : Sep p (n + 4) (sp0 + 0xFFFFFF70) 0x90)
    (hSb : Sep (sp0 + 0xFFFFFF70) 0x90 base code.length) (hsb : Sep out 16 base code.length)
    (k : ∀ m2 : Machine, RfcRes M m2.mem sp0 out p n →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := RFC) (cl := jClob) (P := fun m2 => RfcRes M m2.mem sp0 out p n)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by
      rw [hP.2.2 _ (hSb.symm.sub (c := i) (l := 1) hi).symm (hsb.symm.sub (c := i) (l := 1) hi).symm]
      exact hc i hi) k
  obtain ⟨m2, c2, pc2, rsp, hkeep, hok, herr, hfr⟩ := timeRfc3339_correct m1 (sp0 := sp0) (out := out) (p := p)
    (n := n) (by rw [hmem1]; exact hcR) (by rw [hmem1]; exact hcD) (by rw [hmem1]; exact hcT)
    (by rw [hmem1]; exact hcF) (by rw [hmem1]; exact hcA) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    (by rw [hreg1]; rsimp; exact hsp) hsa hsl hsw how hoa hpw sOG sPG
  rw [hmem1] at hok herr hfr
  refine ⟨m2, c2, pc2, ⟨hok, herr, fun x h1 h2 => hfr x h1 h2⟩, fun x hx => ?_⟩
  have hsp1 : reg m1 sp = sp0 := by rw [hreg1]; rsimp; exact hsp
  by_cases hx0 : x.val = 0
  · simp only [reg, hx0, ↓reduceIte]
  by_cases hx2 : x = sp
  · rw [hx2, rsp, hsp1]
  refine hkeep x ?_
  revert hx hx0 hx2
  revert x
  decide

end

end C3.RV32
