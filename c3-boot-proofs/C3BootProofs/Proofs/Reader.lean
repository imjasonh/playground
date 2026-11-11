import C3BootProofs.Proof.Step
import C3BootProofs.Image.BootloaderV0

/-!
# `c3_verify::reader::Reader::bytes`, as compiled

`Reader::bytes(&mut self, n)` takes `n` bytes from a reader over a byte
slice. The compiled function gets the address of its `Result<&[u8], Error>`
in `a0`, the reader in `a1`, and `n` in `a2`. The reader is three words: the
slice's address, its length, and the position. `readerBytes_correct` proves
that the image's bytes for it, at any address, run on the RV32 model to the
return address, change only `a3` through `a5` among the registers, and
leave memory exactly as `bytesMem` says. On success it stores the new
position in the reader and the slice's address and length in the result. On
failure it stores a null address and the byte 0 (the index of
`Error::Truncated`) at the result's offset 4, which is how this compiled
code encodes the error; the theorem is about what the code stores, not
about Rust's layout rules.
-/

namespace C3.RV32

open C3.ImageV0

/-- What `Reader::bytes` returns for a reader over `len` bytes at `ptr`,
at position `pos`, asked for `n` bytes: the slice's address and the new
position, or `none` if `pos + n` overflows or passes `len`. -/
def bytesResult (ptr len pos n : Word) : Option (Word × Word) :=
  if (pos + n).ult pos then none
  else if len.ult (pos + n) then none
  else some (ptr + pos, pos + n)

/-- `bytesResult` in plain arithmetic: `Reader::bytes` succeeds exactly when
`pos + n` is at most `len` as natural numbers, so a sum that wraps past
2^32 fails. -/
theorem bytesResult_eq (ptr len pos n : Word) :
    bytesResult ptr len pos n =
      if pos.toNat + n.toNat ≤ len.toNat then some (ptr + pos, pos + n) else none := by
  unfold bytesResult
  have hl := len.isLt
  have hp := pos.isLt
  have hn := n.isLt
  by_cases h : pos.toNat + n.toNat ≤ len.toNat
  · have h1 : (pos + n).ult pos = false := by
      simp only [BitVec.ult, BitVec.toNat_add, decide_eq_false_iff_not]; omega
    have h2 : len.ult (pos + n) = false := by
      simp only [BitVec.ult, BitVec.toNat_add, decide_eq_false_iff_not]; omega
    rw [h1, h2, ite_eq_left h]; rfl
  · rw [ite_eq_right h]
    by_cases h1 : (pos + n).ult pos = true
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1]
      have h2 : len.ult (pos + n) = true := by
        simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq] at h1 ⊢; omega
      rw [ite_eq_left h2]

/-- Memory after `Reader::bytes` returns, for a result at `out` and a reader
at `self`. -/
def bytesMem (M : Word → BitVec 8) (out self n : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n with
  | none => memStore8 (memStore32 M out 0) (out + 4) 0
  | some (p, e) => memStore32 (memStore32 (memStore32 M (self + 8) e) out p) (out + 4) n

theorem rb_at_00 : fetchRel readerBytesCode 0x00 = some (.load .lw a3 a1 8, 2) := by decide
theorem rb_at_02 : fetchRel readerBytesCode 0x02 = some (.alu .add a4 a3 a2, 4) := by decide
theorem rb_at_06 : fetchRel readerBytesCode 0x06 = some (.branch .bltu a4 a3 0x0A, 4) := by decide
theorem rb_at_0a : fetchRel readerBytesCode 0x0A = some (.load .lw a5 a1 4, 2) := by decide
theorem rb_at_0c : fetchRel readerBytesCode 0x0C = some (.branch .bgeu a5 a4 0x0E, 4) := by decide
theorem rb_at_10 : fetchRel readerBytesCode 0x10 = some (.store .sw a0 x0 0, 4) := by decide
theorem rb_at_14 : fetchRel readerBytesCode 0x14 = some (.store .sb a0 x0 4, 4) := by decide
theorem rb_at_18 : fetchRel readerBytesCode 0x18 = some (.jalr x0 ra 0, 2) := by decide
theorem rb_at_1a : fetchRel readerBytesCode 0x1A = some (.load .lw a5 a1 0, 2) := by decide
theorem rb_at_1c : fetchRel readerBytesCode 0x1C = some (.alu .add a3 a3 a5, 2) := by decide
theorem rb_at_1e : fetchRel readerBytesCode 0x1E = some (.store .sw a1 a4 8, 2) := by decide
theorem rb_at_20 : fetchRel readerBytesCode 0x20 = some (.store .sw a0 a3 0, 2) := by decide
theorem rb_at_22 : fetchRel readerBytesCode 0x22 = some (.store .sw a0 a2 4, 2) := by decide
theorem rb_at_24 : fetchRel readerBytesCode 0x24 = some (.jalr x0 ra 0, 2) := by decide

theorem add_lit_zero (a : Word) : a + (0 : Word) = a := BitVec.add_zero a

theorem aligned_add {a : Word} (h : a.toNat % 4 = 0) {k : Nat} (hk : k % 4 = 0) :
    (a + BitVec.ofNat 32 k).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem Sep.sub {a b : Word} {n k : Nat} (h : Sep a n b k) {c l : Nat} (hcl : c + l ≤ n) :
    Sep (a + BitVec.ofNat 32 c) l b k := by
  intro i hi j hj
  rw [add_ofNat_assoc]
  exact h (c + i) (by omega) j hj

/-- The failure path: store a null address and `Error::Truncated`, then
return. -/
theorem rb_fail {M : Word → BitVec 8} {base out retAddr : Word} {m : Machine}
    {f : Fin 32 → Word} (hc : CodeIn M base readerBytesCode) (s : St M base m 0x10 f)
    (h0 : f a0 = out) (hra : f ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hout : out.toNat % 4 = 0) (hsep : Sep out 8 base readerBytesCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = memStore8 (memStore32 M out 0) (out + 4) 0 ∧
      ∀ r, reg m' r = f r := by
  have hz := s.zero
  obtain ⟨m1, e1, s1⟩ := s.sw hc rb_at_10 (off' := 0x14) (by decide)
    (by rw [h0, add_lit_zero]; exact hout)
  rw [h0, hz, add_lit_zero] at s1
  have hc1 : CodeIn (memStore32 M out 0) base readerBytesCode :=
    hc.store32 (by have := hsep.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this)
  obtain ⟨m2, e2, s2⟩ := s1.sb hc1 rb_at_14 (off' := 0x18) (by decide)
  rw [h0, hz] at s2
  have hc2 : CodeIn (memStore8 (memStore32 M out 0) (out + 4) ((0 : Word).extractLsb' 0 8)) base
      readerBytesCode := hc1.store8 (hsep.sub (c := 4) (l := 1) (by omega))
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := s2.jalr hc2 rb_at_18
  refine ⟨m3, .cons e1 (.cons e2 (.single e3)), ?_, ?_, regs3⟩
  · rw [pc3, hra]; simpa using hret
  · rw [mem3]; rfl

/-- **The compiled `Reader::bytes` is correct.** With its bytes in memory at
any `base`, a result address `out` in `a0` and a reader `self` in `a1`, both
4-byte aligned and neither overlapping the code, and `n` in `a2`, there is
an execution that reaches the return address in `ra` with every register but
`a3`, `a4`, and `a5` unchanged and memory as `bytesMem` says. -/
theorem readerBytes_correct (m : Machine) (base retAddr out self n : Word)
    (hcode : CodeAt m base readerBytesCode) (hpc : m.pc = base) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = self) (ha2 : reg m a2 = n) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0) (hself : self.toNat % 4 = 0)
    (hsepO : Sep out 8 base readerBytesCode.length)
    (hsepS : Sep (self + 8) 4 base readerBytesCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = bytesMem m.mem out self n ∧
      ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
  have hc : CodeIn m.mem base readerBytesCode := hcode
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, s1⟩ := s0.lw hc rb_at_00 (off' := 0x02) (by decide)
    (by rw [ha1]; exact aligned_add hself (k := 8) (by decide))
  obtain ⟨m2, e2, s2⟩ := s1.alu hc rb_at_02 (off' := 0x06) (by decide)
  have r2a3 : reg m2 a3 = memLoad32 m.mem (self + 8) := by
    rw [s2.regs]; simp +decide [upd, ha1]
  have r2a4 : reg m2 a4 = memLoad32 m.mem (self + 8) + n := by
    rw [s2.regs]; simp +decide [upd, aluEval, ha1, ha2]
  have r2fr : ∀ r, r ≠ a3 → r ≠ a4 → reg m2 r = reg m r := by
    intro r r3 r4
    rw [s2.regs]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, r3, r4]
  have s2' := s2.self
  by_cases hov : (memLoad32 m.mem (self + 8) + n).ult (memLoad32 m.mem (self + 8)) = true
  · obtain ⟨m3, e3, s3⟩ := s2'.taken hc 0x10 rb_at_06 (by decide)
      (by rw [r2a4, r2a3]; simpa [branchTaken] using hov)
    obtain ⟨m', hs, hpc', hmem', hregs'⟩ := rb_fail hc s3
      (by rw [r2fr a0 (by decide) (by decide), ha0]) (by rw [r2fr ra (by decide) (by decide), hra])
      hret hout hsepO
    refine ⟨m', .cons e1 (.cons e2 (.cons e3 hs)), hpc', ?_, ?_⟩
    · rw [hmem']; unfold bytesMem bytesResult; rw [ite_eq_left hov]
    · intro r r3 r4 _; rw [hregs', r2fr r r3 r4]
  · obtain ⟨m3, e3, s3⟩ := s2'.notTaken hc 0x0A rb_at_06 (by decide)
      (by rw [r2a4, r2a3]; simpa [branchTaken] using hov)
    obtain ⟨m4, e4, s4⟩ := s3.lw hc rb_at_0a (off' := 0x0C) (by decide)
      (by rw [r2fr a1 (by decide) (by decide), ha1]; exact aligned_add hself (k := 4) (by decide))
    have r4a5 : reg m4 a5 = memLoad32 m.mem (self + 4) := by
      rw [s4.regs]; simp +decide [upd, r2fr a1 (by decide) (by decide), ha1]
    have r4fr : ∀ r, r ≠ a5 → reg m4 r = reg m2 r := by
      intro r r5
      rw [s4.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [reg]
      · simp [upd, hr, r5]
    have s4' := s4.self
    by_cases hlen : (memLoad32 m.mem (self + 4)).ult (memLoad32 m.mem (self + 8) + n) = true
    · obtain ⟨m5, e5, s5⟩ := s4'.notTaken hc 0x10 rb_at_0c (by decide)
        (by rw [r4a5, r4fr a4 (by decide), r2a4]; simp only [branchTaken, hlen, Bool.not_true])
      obtain ⟨m', hs, hpc', hmem', hregs'⟩ := rb_fail hc s5
        (by rw [r4fr a0 (by decide), r2fr a0 (by decide) (by decide), ha0])
        (by rw [r4fr ra (by decide), r2fr ra (by decide) (by decide), hra]) hret hout hsepO
      refine ⟨m', .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 hs)))), hpc', ?_, ?_⟩
      · rw [hmem']; unfold bytesMem bytesResult; rw [ite_eq_right hov, ite_eq_left hlen]
      · intro r r3 r4 r5; rw [hregs', r4fr r r5, r2fr r r3 r4]
    · obtain ⟨m5, e5, s5⟩ := s4'.taken hc 0x1A rb_at_0c (by decide)
        (by rw [r4a5, r4fr a4 (by decide), r2a4]; simp only [branchTaken, Bool.not_eq_true'];
            simpa using hlen)
      have q1 : reg m4 a1 = self := by rw [r4fr a1 (by decide), r2fr a1 (by decide) (by decide), ha1]
      obtain ⟨m6, e6, s6⟩ := s5.lw hc rb_at_1a (off' := 0x1C) (by decide)
        (by rw [q1, add_lit_zero]; exact hself)
      rw [q1, add_lit_zero] at s6
      obtain ⟨m7, e7, s7⟩ := s6.alu hc rb_at_1c (off' := 0x1E) (by decide)
      have hz4 : reg m4 0 = 0 := by simp [reg]
      have r7 : ∀ r, r ≠ a3 → r ≠ a5 → reg m7 r = reg m4 r := by
        intro r r3 r5
        rw [s7.regs]
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; simp [hz4]
        · simp [upd, hr, r3, r5]
      have r7a3 : reg m7 a3 = memLoad32 m.mem (self + 8) + memLoad32 m.mem self := by
        rw [s7.regs]; simp +decide [upd, aluEval, r4fr a3 (by decide), r2a3]
      have q4 : reg m7 a4 = memLoad32 m.mem (self + 8) + n := by
        rw [r7 a4 (by decide) (by decide), r4fr a4 (by decide), r2a4]
      have q1' : reg m7 a1 = self := by rw [r7 a1 (by decide) (by decide), q1]
      have q0 : reg m7 a0 = out := by
        rw [r7 a0 (by decide) (by decide), r4fr a0 (by decide), r2fr a0 (by decide) (by decide), ha0]
      have q2 : reg m7 a2 = n := by
        rw [r7 a2 (by decide) (by decide), r4fr a2 (by decide), r2fr a2 (by decide) (by decide), ha2]
      obtain ⟨m8, e8, s8⟩ := s7.self.sw hc rb_at_1e (off' := 0x20) (by decide)
        (by rw [q1']; exact aligned_add hself (k := 8) (by decide))
      rw [q1', q4] at s8
      have hc1 := hc.store32 (v := memLoad32 m.mem (self + 8) + n) hsepS
      obtain ⟨m9, e9, s9⟩ := s8.sw hc1 rb_at_20 (off' := 0x22) (by decide)
        (by rw [q0, add_lit_zero]; exact hout)
      rw [q0, add_lit_zero, r7a3] at s9
      have hc2 := hc1.store32 (v := memLoad32 m.mem (self + 8) + memLoad32 m.mem self)
        (by have := hsepO.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this)
      obtain ⟨m10, e10, s10⟩ := s9.sw hc2 rb_at_22 (off' := 0x24) (by decide)
        (by rw [q0]; exact aligned_add hout (k := 4) (by decide))
      rw [q0, q2] at s10
      have hc3 := hc2.store32 (v := n) (hsepO.sub (c := 4) (l := 4) (by omega))
      obtain ⟨m11, e11, pc11, mem11, regs11⟩ := s10.jalr hc3 rb_at_24
      refine ⟨m11, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7
        (.cons e8 (.cons e9 (.cons e10 (.single e11)))))))))), ?_, ?_, ?_⟩
      · rw [pc11, r7 ra (by decide) (by decide), r4fr ra (by decide),
          r2fr ra (by decide) (by decide), hra]
        simpa using hret
      · rw [mem11]; unfold bytesMem bytesResult
        rw [ite_eq_right hov, ite_eq_right hlen, BitVec.add_comm (memLoad32 m.mem self)]
      · intro r r3 r4 r5
        rw [regs11, r7 r r3 r5, r4fr r r5, r2fr r r3 r4]

end C3.RV32
