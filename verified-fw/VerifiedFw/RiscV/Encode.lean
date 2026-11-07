/-
The instruction encoder. It is not trusted: `decode_encode` proves it agrees
with the trusted decoder in `Decode.lean`.
-/
import VerifiedFw.RiscV.Decode

namespace VerifiedFw.RiscV

private def encR (f7 : Nat) (rs2 rs1 : Reg) (f3 : Nat) (rd : Reg) (op : Nat) : Word :=
  .ofNat 32 (op + rd.val * 128 + f3 * 4096 + rs1.val * 32768 + rs2.val * 1048576 +
    f7 * 33554432)

private def encI (imm : BitVec 12) (rs1 : Reg) (f3 : Nat) (rd : Reg) (op : Nat) : Word :=
  .ofNat 32 (op + rd.val * 128 + f3 * 4096 + rs1.val * 32768 + imm.toNat * 1048576)

private def encS (imm : BitVec 12) (rs2 rs1 : Reg) (f3 : Nat) (op : Nat) : Word :=
  .ofNat 32 (op + imm.toNat % 32 * 128 + f3 * 4096 + rs1.val * 32768 +
    rs2.val * 1048576 + imm.toNat / 32 * 33554432)

private def encB (off : BitVec 12) (rs2 rs1 : Reg) (f3 : Nat) (op : Nat) : Word :=
  .ofNat 32 (op + off.toNat / 1024 % 2 * 128 + off.toNat % 16 * 256 + f3 * 4096 +
    rs1.val * 32768 + rs2.val * 1048576 + off.toNat / 16 % 64 * 33554432 +
    off.toNat / 2048 * 2147483648)

private def encU (imm : BitVec 20) (rd : Reg) (op : Nat) : Word :=
  .ofNat 32 (op + rd.val * 128 + imm.toNat * 4096)

private def encJ (off : BitVec 20) (rd : Reg) (op : Nat) : Word :=
  .ofNat 32 (op + rd.val * 128 + off.toNat / 2048 % 256 * 4096 +
    off.toNat / 1024 % 2 * 1048576 + off.toNat % 1024 * 2097152 +
    off.toNat / 524288 * 2147483648)

def encode : Instr → Word
  | .lui rd imm => encU imm rd 0x37
  | .addi rd rs1 imm => encI imm rs1 0 rd 0x13
  | .add rd rs1 rs2 => encR 0x00 rs2 rs1 0 rd 0x33
  | .sub rd rs1 rs2 => encR 0x20 rs2 rs1 0 rd 0x33
  | .sll rd rs1 rs2 => encR 0x00 rs2 rs1 1 rd 0x33
  | .sltu rd rs1 rs2 => encR 0x00 rs2 rs1 3 rd 0x33
  | .xor rd rs1 rs2 => encR 0x00 rs2 rs1 4 rd 0x33
  | .srl rd rs1 rs2 => encR 0x00 rs2 rs1 5 rd 0x33
  | .or rd rs1 rs2 => encR 0x00 rs2 rs1 6 rd 0x33
  | .and rd rs1 rs2 => encR 0x00 rs2 rs1 7 rd 0x33
  | .lw rd rs1 imm => encI imm rs1 2 rd 0x03
  | .sw rs2 rs1 imm => encS imm rs2 rs1 2 0x23
  | .beq rs1 rs2 off => encB off rs2 rs1 0 0x63
  | .bne rs1 rs2 off => encB off rs2 rs1 1 0x63
  | .jal rd off => encJ off rd 0x6f

private theorem digit {w m p f : Nat} (A B : Nat) (h : w = A + m * (f + p * B))
    (hA : A < m) (hf : f < p) : w / m % p = f := by
  subst h
  have hm : 0 < m := by omega
  rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hA, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]

/-- Proves `w / m % p = f` from the digits of `w` below and above `f`. Plain `omega`
can't, because it doesn't implement the omega test's dark shadows. -/
local macro "digit " A:term ", " B:term : tactic =>
  `(tactic| exact digit $A $B (by omega) (by omega) (by omega))

/-- Rewrites the digit of width `len` at bit `k` to `f`, inside a larger goal. -/
local macro "rdigit " k:term ", " len:term ", " f:term ", " A:term ", " B:term : tactic =>
  `(tactic| first
    | done
    | (rw [digit (m := 2 ^ $k) (p := 2 ^ $len) (f := $f) $A $B ?_ ?_ ?_] <;> try omega))

private theorem encR_fields (f7 f3 op : Nat) (rs2 rs1 rd : Reg) (h7 : f7 < 128)
    (h3 : f3 < 8) (hop : op < 128) :
    let w := encR f7 rs2 rs1 f3 rd op
    field w 0 7 = op ∧ field w 12 3 = f3 ∧ field w 25 7 = f7 ∧ regAt w 7 = rd ∧
    regAt w 15 = rs1 ∧ regAt w 20 = rs2 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  have hlt : op + rd.val * 128 + f3 * 4096 + rs1.val * 32768 + rs2.val * 1048576 +
    f7 * 33554432 < 2 ^ 32 := by omega
  simp only [field, regAt, encR, BitVec.toNat_ofNat, Fin.ext_iff, Nat.mod_eq_of_lt hlt]
  generalize (rd : Nat) = d at *
  generalize (rs1 : Nat) = r1 at *
  generalize (rs2 : Nat) = r2 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · digit 0, (d + 32 * (f3 + 8 * (r1 + 32 * (r2 + 32 * f7))))
  · digit (op + d * 128), (r1 + 32 * (r2 + 32 * f7))
  · digit (op + d * 128 + f3 * 4096 + r1 * 32768 + r2 * 1048576), 0
  · digit op, (f3 + 8 * (r1 + 32 * (r2 + 32 * f7)))
  · digit (op + d * 128 + f3 * 4096), (r2 + 32 * f7)
  · digit (op + d * 128 + f3 * 4096 + r1 * 32768), f7

private theorem encI_fields (imm : BitVec 12) (rs1 rd : Reg) (f3 op : Nat) (h3 : f3 < 8)
    (hop : op < 128) :
    let w := encI imm rs1 f3 rd op
    field w 0 7 = op ∧ field w 12 3 = f3 ∧ regAt w 7 = rd ∧ regAt w 15 = rs1 ∧
    BitVec.ofNat 12 (field w 20 12) = imm := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  have hlt : op + rd.val * 128 + f3 * 4096 + rs1.val * 32768 + imm.toNat * 1048576 <
    2 ^ 32 := by omega
  simp only [field, regAt, encI, BitVec.toNat_ofNat, Fin.ext_iff, BitVec.toNat_eq,
    Nat.mod_eq_of_lt hlt]
  generalize imm.toNat = n at *
  generalize (rd : Nat) = d at *
  generalize (rs1 : Nat) = r1 at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · digit 0, (d + 32 * (f3 + 8 * (r1 + 32 * n)))
  · digit (op + d * 128), (r1 + 32 * n)
  · digit op, (f3 + 8 * (r1 + 32 * n))
  · digit (op + d * 128 + f3 * 4096), n
  · rdigit 20, 12, n, (op + d * 128 + f3 * 4096 + r1 * 32768), 0

private theorem encS_fields (imm : BitVec 12) (rs2 rs1 : Reg) (f3 op : Nat) (h3 : f3 < 8)
    (hop : op < 128) :
    let w := encS imm rs2 rs1 f3 op
    field w 0 7 = op ∧ field w 12 3 = f3 ∧ regAt w 15 = rs1 ∧ regAt w 20 = rs2 ∧
    BitVec.ofNat 12 (field w 25 7 * 32 + field w 7 5) = imm := by
  have := rs1.isLt; have := rs2.isLt; have := imm.isLt
  have hlt : op + imm.toNat % 32 * 128 + f3 * 4096 + rs1.val * 32768 +
    rs2.val * 1048576 + imm.toNat / 32 * 33554432 < 2 ^ 32 := by omega
  simp only [field, regAt, encS, BitVec.toNat_ofNat, Fin.ext_iff, BitVec.toNat_eq,
    Nat.mod_eq_of_lt hlt]
  generalize imm.toNat = n at *
  generalize (rs1 : Nat) = r1 at *
  generalize (rs2 : Nat) = r2 at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · digit 0, (n % 32 + 32 * (f3 + 8 * (r1 + 32 * (r2 + 32 * (n / 32)))))
  · digit (op + n % 32 * 128), (r1 + 32 * (r2 + 32 * (n / 32)))
  · digit (op + n % 32 * 128 + f3 * 4096), (r2 + 32 * (n / 32))
  · digit (op + n % 32 * 128 + f3 * 4096 + r1 * 32768), (n / 32)
  · rdigit 25, 7, n / 32, (op + n % 32 * 128 + f3 * 4096 + r1 * 32768 + r2 * 1048576), 0
    rdigit 7, 5, n % 32, op, (f3 + 8 * (r1 + 32 * (r2 + 32 * (n / 32))))

private theorem encB_fields (off : BitVec 12) (rs2 rs1 : Reg) (f3 op : Nat) (h3 : f3 < 8)
    (hop : op < 128) :
    let w := encB off rs2 rs1 f3 op
    field w 0 7 = op ∧ field w 12 3 = f3 ∧ regAt w 15 = rs1 ∧ regAt w 20 = rs2 ∧
    BitVec.ofNat 12
      (field w 31 1 * 2048 + field w 7 1 * 1024 + field w 25 6 * 16 + field w 8 4) = off := by
  have := rs1.isLt; have := rs2.isLt; have := off.isLt
  have hlt : op + off.toNat / 1024 % 2 * 128 + off.toNat % 16 * 256 + f3 * 4096 +
    rs1.val * 32768 + rs2.val * 1048576 + off.toNat / 16 % 64 * 33554432 +
    off.toNat / 2048 * 2147483648 < 2 ^ 32 := by omega
  simp only [field, regAt, encB, BitVec.toNat_ofNat, Fin.ext_iff, BitVec.toNat_eq,
    Nat.mod_eq_of_lt hlt]
  generalize off.toNat = n at *
  generalize (rs1 : Nat) = r1 at *
  generalize (rs2 : Nat) = r2 at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · digit 0, (n / 1024 % 2 + 2 * (n % 16 + 16 * (f3 + 8 * (r1 + 32 * (r2 + 32 *
      (n / 16 % 64 + 64 * (n / 2048)))))))
  · digit (op + n / 1024 % 2 * 128 + n % 16 * 256), (r1 + 32 * (r2 + 32 * (n / 16 % 64 +
      64 * (n / 2048))))
  · digit (op + n / 1024 % 2 * 128 + n % 16 * 256 + f3 * 4096), (r2 + 32 * (n / 16 % 64 +
      64 * (n / 2048)))
  · digit (op + n / 1024 % 2 * 128 + n % 16 * 256 + f3 * 4096 + r1 * 32768), (n / 16 % 64 +
      64 * (n / 2048))
  · rdigit 31, 1, n / 2048, (op + n / 1024 % 2 * 128 + n % 16 * 256 + f3 * 4096 +
      r1 * 32768 + r2 * 1048576 + n / 16 % 64 * 33554432), 0
    rdigit 7, 1, n / 1024 % 2, op, (n % 16 + 16 * (f3 + 8 * (r1 + 32 * (r2 + 32 *
      (n / 16 % 64 + 64 * (n / 2048))))))
    rdigit 25, 6, n / 16 % 64, (op + n / 1024 % 2 * 128 + n % 16 * 256 + f3 * 4096 +
      r1 * 32768 + r2 * 1048576), (n / 2048)
    rdigit 8, 4, n % 16, (op + n / 1024 % 2 * 128), (f3 + 8 * (r1 + 32 * (r2 + 32 *
      (n / 16 % 64 + 64 * (n / 2048)))))

private theorem encU_fields (imm : BitVec 20) (rd : Reg) (op : Nat) (hop : op < 128) :
    let w := encU imm rd op
    field w 0 7 = op ∧ regAt w 7 = rd ∧ BitVec.ofNat 20 (field w 12 20) = imm := by
  have := rd.isLt; have := imm.isLt
  have hlt : op + rd.val * 128 + imm.toNat * 4096 < 2 ^ 32 := by omega
  simp only [field, regAt, encU, BitVec.toNat_ofNat, Fin.ext_iff, BitVec.toNat_eq,
    Nat.mod_eq_of_lt hlt]
  generalize imm.toNat = n at *
  generalize (rd : Nat) = d at *
  refine ⟨?_, ?_, ?_⟩
  · digit 0, (d + 32 * n)
  · digit op, n
  · rdigit 12, 20, n, (op + d * 128), 0

private theorem encJ_fields (off : BitVec 20) (rd : Reg) (op : Nat) (hop : op < 128) :
    let w := encJ off rd op
    field w 0 7 = op ∧ regAt w 7 = rd ∧
    BitVec.ofNat 20
      (field w 31 1 * 524288 + field w 12 8 * 2048 + field w 20 1 * 1024 + field w 21 10) =
      off := by
  have := rd.isLt; have := off.isLt
  have hlt : op + rd.val * 128 + off.toNat / 2048 % 256 * 4096 +
    off.toNat / 1024 % 2 * 1048576 + off.toNat % 1024 * 2097152 +
    off.toNat / 524288 * 2147483648 < 2 ^ 32 := by omega
  simp only [field, regAt, encJ, BitVec.toNat_ofNat, Fin.ext_iff, BitVec.toNat_eq,
    Nat.mod_eq_of_lt hlt]
  generalize off.toNat = n at *
  generalize (rd : Nat) = d at *
  refine ⟨?_, ?_, ?_⟩
  · digit 0, (d + 32 * (n / 2048 % 256 + 256 * (n / 1024 % 2 + 2 * (n % 1024 + 1024 *
      (n / 524288)))))
  · digit op, (n / 2048 % 256 + 256 * (n / 1024 % 2 + 2 * (n % 1024 + 1024 * (n / 524288))))
  · have : n / 1024 = n / 2048 * 2 + n / 1024 % 2 := by
      rw [show n / 2048 = n / 1024 / 2 by rw [Nat.div_div_eq_div_mul]]; omega
    have : n / 2048 = n / 524288 * 256 + n / 2048 % 256 := by
      rw [show n / 524288 = n / 2048 / 256 by rw [Nat.div_div_eq_div_mul]]; omega
    rdigit 31, 1, n / 524288, (op + d * 128 + n / 2048 % 256 * 4096 +
      n / 1024 % 2 * 1048576 + n % 1024 * 2097152), 0
    rdigit 12, 8, n / 2048 % 256, (op + d * 128), (n / 1024 % 2 + 2 * (n % 1024 + 1024 *
      (n / 524288)))
    rdigit 20, 1, n / 1024 % 2, (op + d * 128 + n / 2048 % 256 * 4096), (n % 1024 + 1024 *
      (n / 524288))
    rdigit 21, 10, n % 1024, (op + d * 128 + n / 2048 % 256 * 4096 + n / 1024 % 2 * 1048576),
      (n / 524288)

/-- Decoding an encoded instruction gives the instruction back.

Each case hides the encoded word behind a variable before unfolding `decode`, so
the kernel checks the proof from the field lemmas instead of trying to evaluate
`Nat` division on symbolic values. -/
theorem decode_encode (i : Instr) : decode (encode i) = some i := by
  cases i with
  | lui rd imm =>
    obtain ⟨h0, h1, h2⟩ :=
      encU_fields imm rd 0x37 (by decide)
    simp only [encode]
    generalize encU _ _ _ = w at *
    simp only [decode, h0, h1, h2]
  | jal rd off =>
    obtain ⟨h0, h1, h2⟩ :=
      encJ_fields off rd 0x6f (by decide)
    simp only [encode]
    generalize encJ _ _ _ = w at *
    simp only [decode, h0, h1, h2]
  | addi rd rs1 imm =>
    obtain ⟨h0, h1, h2, h3, h4⟩ :=
      encI_fields imm rs1 rd 0 0x13 (by decide) (by decide)
    simp only [encode]
    generalize encI _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4]
  | lw rd rs1 imm =>
    obtain ⟨h0, h1, h2, h3, h4⟩ :=
      encI_fields imm rs1 rd 2 0x03 (by decide) (by decide)
    simp only [encode]
    generalize encI _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4]
  | sw rs2 rs1 imm =>
    obtain ⟨h0, h1, h2, h3, h4⟩ :=
      encS_fields imm rs2 rs1 2 0x23 (by decide) (by decide)
    simp only [encode]
    generalize encS _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4]
  | beq rs1 rs2 off =>
    obtain ⟨h0, h1, h2, h3, h4⟩ :=
      encB_fields off rs2 rs1 0 0x63 (by decide) (by decide)
    simp only [encode]
    generalize encB _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4]
  | bne rs1 rs2 off =>
    obtain ⟨h0, h1, h2, h3, h4⟩ :=
      encB_fields off rs2 rs1 1 0x63 (by decide) (by decide)
    simp only [encode]
    generalize encB _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4]
  | add rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x00 0 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]
  | sub rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x20 0 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]
  | sll rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x00 1 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]
  | sltu rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x00 3 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]
  | xor rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x00 4 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]
  | srl rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x00 5 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]
  | or rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x00 6 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]
  | and rd rs1 rs2 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      encR_fields 0x00 7 0x33 rs2 rs1 rd (by decide) (by decide)
        (by decide)
    simp only [encode]
    generalize encR _ _ _ _ _ _ = w at *
    simp only [decode, h0, h1, h2, h3, h4, h5]

end VerifiedFw.RiscV
