import C3BootProofs.Proofs.ShaTools
import C3BootProofs.Proofs.Sha256LoopBlocks
import C3BootProofs.Proofs.ShrWide12
import C3BootProofs.Spec.Der

/-!
# `Der::tlv`, as compiled

`c3_verify::der::Der::tlv` reads the element at the front of the reader's
unread bytes, a leaf with no frame. It stores `Ok(Tlv)` or `Err(Error)` at
`out` and, on success, moves the reader past the element.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem tlv_at_0 : fetchRel derTlvCode 0x0 = some (.load .lw a4 a1 0xC, 2) := by decide
theorem tlv_at_2 : fetchRel derTlvCode 0x2 = some (.branch .beq a4 x0 0x5C, 2) := by decide
theorem tlv_at_4 : fetchRel derTlvCode 0x4 = some (.load .lw a3 a1 0x8, 2) := by decide
theorem tlv_at_6 : fetchRel derTlvCode 0x6 = some (.load .lbu (7 : Fin 32) a3 0x0, 4) := by decide
theorem tlv_at_a : fetchRel derTlvCode 0xA = some (.aluImm .and a5 (7 : Fin 32) 0x1F, 4) := by decide
theorem tlv_at_e : fetchRel derTlvCode 0xE = some (.aluImm .add a2 x0 0x1F, 2) := by decide
theorem tlv_at_10 : fetchRel derTlvCode 0x10 = some (.branch .bne a5 a2 0x10, 4) := by decide
theorem tlv_at_14 : fetchRel derTlvCode 0x14 = some (.aluImm .add a1 x0 0x14, 2) := by decide
theorem tlv_at_16 : fetchRel derTlvCode 0x16 = some (.store .sw a0 x0 0x0, 4) := by decide
theorem tlv_at_1a : fetchRel derTlvCode 0x1A = some (.store .sb a0 a1 0x4, 4) := by decide
theorem tlv_at_1e : fetchRel derTlvCode 0x1E = some (.jalr x0 ra 0x0, 2) := by decide
theorem tlv_at_20 : fetchRel derTlvCode 0x20 = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem tlv_at_22 : fetchRel derTlvCode 0x22 = some (.branch .beq a4 a2 0x3C, 4) := by decide
theorem tlv_at_26 : fetchRel derTlvCode 0x26 = some (.load .lb a2 a3 0x1, 4) := by decide
theorem tlv_at_2a : fetchRel derTlvCode 0x2A = some (.aluImm .add (5 : Fin 32) a3 0x2, 4) := by decide
theorem tlv_at_2e : fetchRel derTlvCode 0x2E = some (.aluImm .add a6 a4 0xFFFFFFFE, 4) := by decide
theorem tlv_at_32 : fetchRel derTlvCode 0x32 = some (.aluImm .and a5 a2 0xFF, 4) := by decide
theorem tlv_at_36 : fetchRel derTlvCode 0x36 = some (.branch .blt a2 x0 0x16, 4) := by decide
theorem tlv_at_3a : fetchRel derTlvCode 0x3A = some (.alu .add (17 : Fin 32) x0 (5 : Fin 32), 2) := by decide
theorem tlv_at_3c : fetchRel derTlvCode 0x3C = some (.branch .bltu a6 a5 0x22, 4) := by decide
theorem tlv_at_40 : fetchRel derTlvCode 0x40 = some (.alu .sub a6 a6 a5, 4) := by decide
theorem tlv_at_44 : fetchRel derTlvCode 0x44 = some (.branch .bgeu a4 a6 0x24, 4) := by decide
theorem tlv_at_48 : fetchRel derTlvCode 0x48 = some (.aluImm .add a1 x0 0x6, 2) := by decide
theorem tlv_at_4a : fetchRel derTlvCode 0x4A = some (.jal x0 0xFFFFFFCC, 2) := by decide
theorem tlv_at_4c : fetchRel derTlvCode 0x4C = some (.aluImm .and (6 : Fin 32) a5 0x7F, 4) := by decide
theorem tlv_at_50 : fetchRel derTlvCode 0x50 = some (.aluImm .add a2 (6 : Fin 32) 0xFFFFFFFB, 4) := by decide
theorem tlv_at_54 : fetchRel derTlvCode 0x54 = some (.aluImm .add a5 x0 0xFFFFFFFB, 2) := by decide
theorem tlv_at_56 : fetchRel derTlvCode 0x56 = some (.branch .bgeu a5 a2 0xFFFFFFBE, 4) := by decide
theorem tlv_at_5a : fetchRel derTlvCode 0x5A = some (.branch .bgeu a6 (6 : Fin 32) 0x2C, 4) := by decide
theorem tlv_at_5e : fetchRel derTlvCode 0x5E = some (.store .sw a0 x0 0x0, 4) := by decide
theorem tlv_at_62 : fetchRel derTlvCode 0x62 = some (.store .sb a0 x0 0x4, 4) := by decide
theorem tlv_at_66 : fetchRel derTlvCode 0x66 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tlv_at_68 : fetchRel derTlvCode 0x68 = some (.alu .add a2 (17 : Fin 32) a5, 4) := by decide
theorem tlv_at_6c : fetchRel derTlvCode 0x6C = some (.alu .sub a4 a4 a6, 4) := by decide
theorem tlv_at_70 : fetchRel derTlvCode 0x70 = some (.store .sw a1 a2 0x8, 2) := by decide
theorem tlv_at_72 : fetchRel derTlvCode 0x72 = some (.store .sw a1 a6 0xC, 4) := by decide
theorem tlv_at_76 : fetchRel derTlvCode 0x76 = some (.store .sw a0 (17 : Fin 32) 0x0, 4) := by decide
theorem tlv_at_7a : fetchRel derTlvCode 0x7A = some (.store .sw a0 a5 0x4, 2) := by decide
theorem tlv_at_7c : fetchRel derTlvCode 0x7C = some (.store .sw a0 a3 0x8, 2) := by decide
theorem tlv_at_7e : fetchRel derTlvCode 0x7E = some (.store .sw a0 a4 0xC, 2) := by decide
theorem tlv_at_80 : fetchRel derTlvCode 0x80 = some (.store .sb a0 (7 : Fin 32) 0x10, 4) := by decide
theorem tlv_at_84 : fetchRel derTlvCode 0x84 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tlv_at_86 : fetchRel derTlvCode 0x86 = some (.load .lbu a2 (5 : Fin 32) 0x0, 4) := by decide
theorem tlv_at_8a : fetchRel derTlvCode 0x8A = some (.branch .beq a2 x0 0xFFFFFF8A, 2) := by decide
theorem tlv_at_8c : fetchRel derTlvCode 0x8C = some (.aluImm .add a5 x0 0x0, 2) := by decide
theorem tlv_at_8e : fetchRel derTlvCode 0x8E = some (.alu .add (17 : Fin 32) (5 : Fin 32) (6 : Fin 32), 4) := by decide
theorem tlv_at_92 : fetchRel derTlvCode 0x92 = some (.alu .sub a6 a6 (6 : Fin 32), 4) := by decide
theorem tlv_at_96 : fetchRel derTlvCode 0x96 = some (.branch .beq (6 : Fin 32) x0 0x1A, 4) := by decide
theorem tlv_at_9a : fetchRel derTlvCode 0x9A = some (.aluImm .srl a2 a5 0x18, 4) := by decide
theorem tlv_at_9e : fetchRel derTlvCode 0x9E = some (.branch .bne a2 x0 0xFFFFFFAA, 2) := by decide
theorem tlv_at_a0 : fetchRel derTlvCode 0xA0 = some (.load .lbu a2 (5 : Fin 32) 0x0, 4) := by decide
theorem tlv_at_a4 : fetchRel derTlvCode 0xA4 = some (.aluImm .sll a5 a5 0x8, 2) := by decide
theorem tlv_at_a6 : fetchRel derTlvCode 0xA6 = some (.alu .or a5 a5 a2, 2) := by decide
theorem tlv_at_a8 : fetchRel derTlvCode 0xA8 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x1, 2) := by decide
theorem tlv_at_aa : fetchRel derTlvCode 0xAA = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem tlv_at_ac : fetchRel derTlvCode 0xAC = some (.branch .bne (6 : Fin 32) x0 0xFFFFFFEE, 4) := by decide
theorem tlv_at_b0 : fetchRel derTlvCode 0xB0 = some (.aluImm .add a2 x0 0x7F, 4) := by decide
theorem tlv_at_b4 : fetchRel derTlvCode 0xB4 = some (.branch .bgeu a2 a5 0xFFFFFF60, 4) := by decide
theorem tlv_at_b8 : fetchRel derTlvCode 0xB8 = some (.jal x0 0xFFFFFF84, 2) := by decide
end

section Lb

variable {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine} {off : Nat}
  {f : Fin 32 → Word}

theorem St.lb (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd rs1 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.load .lb rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧
      St M base m1 off' (upd f rd ((M (f rs1 + o)).signExtend 32)) := by
  refine ⟨_, ?_, s.write (v := (M (f rs1 + o)).signExtend 32) (rd := rd) hn⟩
  have ha : aligned (loadSize .lb) (reg m rs1 + o) = true := by
    unfold aligned loadSize; rw [Nat.mod_one]; rfl
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.mem]
  unfold exec
  simp only [ha, Bool.not_true]
  rfl

end Lb

theorem CodeIn.runBlock {base : Word} {code : List Nat} :
    ∀ (is : List BInstr) {M : Word → BitVec 8} {f : Fin 32 → Word}, CodeIn M base code →
      BlockOk base code.length is (M, f) → CodeIn (runBlock is (M, f)).1 base code
  | [], _, _, hc, _ => hc
  | i :: is, _, _, hc, hok => CodeIn.runBlock is (CodeIn.run i hc hok.1) hok.2

/-- The byte the compiled code stores for each error: `Error`'s
discriminant. -/
def derErrByte : DerError → BitVec 8
  | .truncated => 0
  | .badDer => 0x14
  | .overflow => 6

/-- Memory after `Der::tlv` with the result at `out` and the reader at `d`,
whose unread bytes start at `rp` and number `rl`. -/
def derTlvMem (M : Word → BitVec 8) (out d rp rl : Word) : Except DerError DerTlv → Word → BitVec 8
  | .error e => memStore8 (memStore32 M out 0) (out + 4) (derErrByte e)
  | .ok t =>
    memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
      (d + 8) (rp + BitVec.ofNat 32 (t.header + t.len))) (d + 0xC) (rl - BitVec.ofNat 32 (t.header + t.len)))
      out (rp + BitVec.ofNat 32 t.header)) (out + 4) (BitVec.ofNat 32 t.len)) (out + 8) rp)
      (out + 0xC) (BitVec.ofNat 32 (t.header + t.len))) (out + 0x10) (BitVec.ofNat 8 t.tag)

/-- The error exit at 0x16, with `Error`'s discriminant in `a1`. -/
theorem tlv_exit16 {M : Word → BitVec 8} {P out retAddr : Word} {n : Machine} (s : St M P n 0x16 (reg n))
    (hc : CodeIn M P derTlvCode) (ha0 : reg n a0 = out) (hra : reg n ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0) (sOC : Sep out 17 P derTlvCode.length) :
    ∃ n', Steps n n' ∧ n'.pc = retAddr ∧
      n'.mem = memStore8 (memStore32 M out 0) (out + 4) ((reg n a1).extractLsb' 0 8) ∧ ∀ r, reg n' r = reg n r := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.sw hc tlv_at_16 (off' := 0x1A) (by decide) (by rw [ha0, add_lit_zero]; exact hout)
  rw [ha0, add_lit_zero, hz] at u1
  have hc1 := CodeIn.store32 (v := 0) hc (sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h)
  obtain ⟨n2, d2, u2⟩ := u1.sb hc1 tlv_at_1a (off' := 0x1E) (by decide)
  rw [ha0] at u2
  have hc2 := CodeIn.store8 (v := (reg n a1).extractLsb' 0 8) hc1 (sOC.sub (c := 4) (l := 1) (by decide))
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc2 tlv_at_1e
  exact ⟨n3, .cons d1 (.cons d2 (.single d3)), by rw [pc3, hra, add_lit_zero, hret], mem3, regs3⟩

/-- The `Truncated` exit at 0x5E. -/
theorem tlv_exit5e {M : Word → BitVec 8} {P out retAddr : Word} {n : Machine} (s : St M P n 0x5E (reg n))
    (hc : CodeIn M P derTlvCode) (ha0 : reg n a0 = out) (hra : reg n ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0) (sOC : Sep out 17 P derTlvCode.length) :
    ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = memStore8 (memStore32 M out 0) (out + 4) 0 ∧
      ∀ r, reg n' r = reg n r := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.sw hc tlv_at_5e (off' := 0x62) (by decide) (by rw [ha0, add_lit_zero]; exact hout)
  rw [ha0, add_lit_zero, hz] at u1
  have hc1 := CodeIn.store32 (v := 0) hc (sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h)
  obtain ⟨n2, d2, u2⟩ := u1.sb hc1 tlv_at_62 (off' := 0x66) (by decide)
  rw [ha0, hz] at u2
  have hc2 := CodeIn.store8 (v := (0 : Word).extractLsb' 0 8) hc1 (sOC.sub (c := 4) (l := 1) (by decide))
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc2 tlv_at_66
  exact ⟨n3, .cons d1 (.cons d2 (.single d3)), by rw [pc3, hra, add_lit_zero, hret], mem3, regs3⟩

/-- From 0x68 to the return: move the reader past the element and store
`Ok(Tlv)`. -/
def tlvOk : List BInstr :=
  [.alu .add a2 (17 : Fin 32) a5, .alu .sub a4 a4 a6, .sw a1 a2 0x8, .sw a1 a6 0xC, .sw a0 (17 : Fin 32) 0x0,
   .sw a0 a5 0x4, .sw a0 a3 0x8, .sw a0 a4 0xC, .sb a0 (7 : Fin 32) 0x10]

section
set_option maxRecDepth 20000
theorem tlvOk_end : blockEnd derTlvCode 0x68 tlvOk = some 0x84 := by decide
end

set_option maxRecDepth 20000 in
/-- The success exit at 0x68. -/
theorem tlv_exit68 {M : Word → BitVec 8} {P out d retAddr : Word} {n : Machine} (s : St M P n 0x68 (reg n))
    (hc : CodeIn M P derTlvCode) (ha0 : reg n a0 = out) (ha1 : reg n a1 = d) (hra : reg n ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0) (hd : d.toNat % 4 = 0)
    (sOC : Sep out 17 P derTlvCode.length) (sDC : Sep (d + 8) 8 P derTlvCode.length) :
    ∃ n', Steps n n' ∧ n'.pc = retAddr ∧
      n'.mem = memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
        (d + 8) (reg n 17 + reg n a5)) (d + 0xC) (reg n a6)) out (reg n 17)) (out + 4) (reg n a5))
        (out + 8) (reg n a3)) (out + 0xC) (reg n a4 - reg n a6)) (out + 0x10) ((reg n 7).extractLsb' 0 8) ∧
      ∀ r, r ≠ a2 → r ≠ a4 → reg n' r = reg n r := by
  have hz := s.zero
  have e8 : d + 8 = d + 0x8 := rfl
  have ok : BlockOk P derTlvCode.length tlvOk (M, reg n) := by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, tlvOk, upd_app, ↓reduceIte, and_true, true_and]
    rw [ha0, ha1, add_lit_zero]
    refine ⟨⟨aligned_add hd (k := 8) (by decide), sDC.sub (c := 0) (l := 4) (by decide) |> fun h => by
        rwa [add_ofNat_zero] at h⟩,
      ⟨aligned_add hd (k := 0xC) (by decide), ?_⟩,
      ⟨hout, sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h⟩,
      ⟨aligned_add hout (k := 4) (by decide), sOC.sub (c := 4) (l := 4) (by decide)⟩,
      ⟨aligned_add hout (k := 8) (by decide), sOC.sub (c := 8) (l := 4) (by decide)⟩,
      ⟨aligned_add hout (k := 0xC) (by decide), sOC.sub (c := 0xC) (l := 4) (by decide)⟩,
      sOC.sub (c := 0x10) (l := 1) (by decide)⟩
    rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl]
    exact sDC.sub (c := 4) (l := 4) (by decide)
  obtain ⟨n1, c1, u1⟩ := St.block tlvOk s hc tlvOk_end ok
  have hc1 := CodeIn.runBlock tlvOk hc ok
  obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr hc1 tlv_at_84
  refine ⟨n2, c1.trans (.single d2), ?_, ?_, fun r h2 h4 => ?_⟩
  · rw [pc2]; simp only [runBlock, BInstr.run, tlvOk]; simp +decide only [upd_app, ↓reduceIte]
    rw [hra, add_lit_zero, hret]
  · rw [mem2]; simp only [runBlock, BInstr.run, tlvOk]; simp +decide only [upd_app, ↓reduceIte]
    rw [ha0, ha1, add_lit_zero]; rfl
  · rw [regs2]; simp only [runBlock, BInstr.run, tlvOk]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h4, ite_false]

theorem upd_ne' {f : Fin 32 → Word} {rd r : Fin 32} {v : Word} (h : r ≠ rd) (hz : f 0 = 0) :
    upd f rd v r = f r := updz hz h

/-- The join at 0x3C: the element's contents start at `a7` and need `a5`
bytes, and `a6` bytes follow the length field. -/
theorem tlv_join {M : Word → BitVec 8} {P out d retAddr : Word} {n : Machine} (s : St M P n 0x3C (reg n))
    (hc : CodeIn M P derTlvCode) (ha0 : reg n a0 = out) (ha1 : reg n a1 = d) (hra : reg n ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0) (hd : d.toNat % 4 = 0)
    (sOC : Sep out 17 P derTlvCode.length) (sDC : Sep (d + 8) 8 P derTlvCode.length)
    (hrem : (reg n a6).toNat ≤ (reg n a4).toNat) :
    ∃ n', Steps n n' ∧ n'.pc = retAddr ∧
      n'.mem = (if (reg n a6).toNat < (reg n a5).toNat then memStore8 (memStore32 M out 0) (out + 4) 0 else
        memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
          (d + 8) (reg n 17 + reg n a5)) (d + 0xC) (reg n a6 - reg n a5)) out (reg n 17)) (out + 4) (reg n a5))
          (out + 8) (reg n a3)) (out + 0xC) (reg n a4 - (reg n a6 - reg n a5))) (out + 0x10)
          ((reg n 7).extractLsb' 0 8)) ∧
      ∀ r, r ≠ a2 → r ≠ a4 → r ≠ a6 → reg n' r = reg n r := by
  by_cases hlt : (reg n a6).toNat < (reg n a5).toNat
  · obtain ⟨n1, d1, u1⟩ := s.taken hc 0x5E tlv_at_3c (by decide) (decide_eq_true hlt)
    obtain ⟨n2, c2, pc2, mem2, k2⟩ := tlv_exit5e u1.self hc (by rw [u1.regs, ha0]) (by rw [u1.regs, hra]) hret hout sOC
    exact ⟨n2, .cons d1 c2, pc2, by rw [mem2, ite_eq_left hlt], fun r _ _ _ => by rw [k2, u1.regs]⟩
  · obtain ⟨n1, d1, u1⟩ := s.notTaken hc 0x40 tlv_at_3c (by decide) (decide_eq_false hlt)
    obtain ⟨n2, d2, u2⟩ := u1.alu hc tlv_at_40 (off' := 0x44) (by decide)
    have hle : (reg n a6 - reg n a5).toNat ≤ (reg n a4).toNat := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; omega)]; omega
    obtain ⟨n3, d3, u3⟩ := u2.taken hc 0x68 tlv_at_44 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]
      show (!decide ((reg n a4).toNat < (reg n a6 - reg n a5).toNat)) = true
      rw [decide_eq_false (by omega)]; rfl)
    have g3 : ∀ r, reg n3 r = upd (reg n) a6 (aluEval .sub (reg n a6) (reg n a5)) r := u3.regs
    obtain ⟨n4, c4, pc4, mem4, k4⟩ := tlv_exit68 u3.self hc (by rw [g3, upd_ne (by decide) (by decide), ha0])
      (by rw [g3, upd_ne (by decide) (by decide), ha1]) (by rw [g3, upd_ne (by decide) (by decide), hra])
      hret hout hd sOC sDC
    refine ⟨n4, .cons d1 (.cons d2 (.cons d3 c4)), pc4, ?_, fun r h2 h4 h6 => by
      rw [k4 r h2 h4, g3, upd_ne' h6 s.zero]⟩
    rw [mem4, ite_eq_right hlt]
    simp only [g3, upd_app]
    simp +decide only [↓reduceIte]
    rfl

/-- A big-endian value of `bs`, continuing from `acc`. -/
def beFold (acc : Nat) (bs : Bytes) : Nat := bs.foldl (fun a b => a * 256 + b) acc

theorem memBytes_zero (M : Word → BitVec 8) (p : Word) : memBytes M p 0 = [] := rfl

theorem memBytes_succ (M : Word → BitVec 8) (p : Word) (k : Nat) :
    memBytes M p (k + 1) = (M p).toNat :: memBytes M (p + 1) k := by
  unfold memBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, add_ofNat_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  show (M (p + BitVec.ofNat 32 (i + 1))).toNat = (M (p + 1 + BitVec.ofNat 32 i)).toNat
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_comm]

/-- One round of the long-form length, from 0x9A. -/
def tlvLen : List BInstr :=
  [.lbu a2 (5 : Fin 32) 0x0, .aluImm .sll a5 a5 0x8, .alu .or a5 a5 a2, .aluImm .add (5 : Fin 32) (5 : Fin 32) 0x1,
   .aluImm .add (6 : Fin 32) (6 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem tlvLen_end : blockEnd derTlvCode 0xA0 tlvLen = some 0xAC := by decide
end

set_option maxRecDepth 20000 in
/-- **The long-form length loop**, from 0x9A with `k` length bytes left at
`p`: `a5` gets their big-endian value after `acc`, and the loop leaves at
0xB0. The overflow check never fires, since at most four bytes remain. -/
theorem tlv_loop {M : Word → BitVec 8} {P : Word} (hc : CodeIn M P derTlvCode) :
    ∀ k, ∀ {n : Machine} {acc : Nat} {p : Word}, 1 ≤ k → St M P n 0x9A (reg n) →
      reg n 6 = BitVec.ofNat 32 k → reg n 5 = p → reg n a5 = BitVec.ofNat 32 acc → (acc + 1) * 256 ^ k ≤ 2 ^ 32 →
      ∃ n', Steps n n' ∧ St M P n' 0xB0 (reg n') ∧ reg n' a5 = BitVec.ofNat 32 (beFold acc (memBytes M p k)) ∧
        (∀ r, r ≠ a2 → r ≠ a5 → r ≠ 5 → r ≠ 6 → reg n' r = reg n r)
  | 0, _, _, _, hk, _, _, _, _, _ => absurd hk (by decide)
  | k + 1, n, acc, p, _, s, r6, r5, ra5, hacc => by
    have hz := s.zero
    have hpow : 256 ≤ 256 ^ (k + 1) := by
      rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0 < 256))
    have h24 : acc < 2 ^ 24 := by
      have := Nat.mul_le_mul_left (acc + 1) hpow
      omega
    obtain ⟨n1, d1, u1⟩ := s.aluImm hc tlv_at_9a (off' := 0x9E) (by decide)
    have e2 : aluEval .srl (reg n a5) 0x18 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [srl_nat _ _ (by decide), ra5, ofNat_tn (by omega)]
      show acc / 2 ^ 24 = 0
      exact Nat.div_eq_of_lt h24
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hc 0xA0 tlv_at_9e (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [e2]; rfl)
    have g2 : ∀ r, reg n2 r = upd (reg n) a2 (aluEval .srl (reg n a5) 0x18) r := u2.regs
    obtain ⟨n3, c3, u3⟩ := St.block tlvLen u2.self hc tlvLen_end (by simp [BlockOk, BInstr.ok, tlvLen])
    simp only [runBlock, BInstr.run, tlvLen] at u3
    have g3 : ∀ r, reg n3 r = _ := u3.regs
    have hb : (M p).toNat < 256 := (M p).isLt
    have v5 : aluEval .or (aluEval .sll (BitVec.ofNat 32 acc) 0x8) ((M p).zeroExtend 32) =
        BitVec.ofNat 32 (acc * 256 + (M p).toNat) := by
      apply BitVec.eq_of_toNat_eq
      have hs : (aluEval .sll (BitVec.ofNat 32 acc) 0x8).toNat = acc * 256 := by
        rw [sll_nat _ _ (by decide), ofNat_tn (by omega)]
        show acc * 2 ^ 8 % 2 ^ 32 = acc * 256
        exact Nat.mod_eq_of_lt (by omega)
      have hz8 : ((M p).zeroExtend 32 : Word).toNat = (M p).toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      rw [or_nat _ _ (i := 8) (by rw [hs]; omega) (by rw [hz8]; exact hb), hs, hz8, ofNat_tn (by omega)]
    have a5v : reg n3 a5 = BitVec.ofNat 32 (acc * 256 + (M p).toNat) := by
      rw [g3]; simp +decide only [upd_app, ↓reduceIte]; simp only [g2]; simp +decide only [upd_app, ↓reduceIte]
      rw [r5, ra5, add_lit_zero]; exact v5
    have t5 : reg n3 5 = p + 1 := by
      rw [g3]; simp +decide only [upd_app, ↓reduceIte]; simp only [g2]; simp +decide only [upd_app, ↓reduceIte]
      rw [r5]; rfl
    have hk32 : k + 1 < 2 ^ 32 := by
      have h1 : 256 ^ (k + 1) ≤ 2 ^ 32 := by
        have := Nat.le_mul_of_pos_left (256 ^ (k + 1)) (by omega : 0 < acc + 1); omega
      have h2 : k + 1 < 256 ^ (k + 1) := Nat.lt_pow_self (by decide)
      omega
    have t6 : reg n3 6 = BitVec.ofNat 32 k := by
      rw [g3]; simp +decide only [upd_app, ↓reduceIte]; simp only [g2]; simp +decide only [upd_app, ↓reduceIte]
      rw [r6]; apply BitVec.eq_of_toNat_eq
      rw [ev_add, BitVec.toNat_add, ofNat_tn hk32, ofNat_tn (by omega)]
      show (k + 1 + 4294967295) % 2 ^ 32 = k
      omega
    have k3 : ∀ r, r ≠ a2 → r ≠ a5 → r ≠ 5 → r ≠ 6 → reg n3 r = reg n r := fun r h2 h5 h5' h6 => by
      rw [g3]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h2, h5, h5', h6, ite_false]; rw [g2]; simp only [upd_app, h0, h2, ite_false]
    have hfold : beFold acc (memBytes M p (k + 1)) = beFold (acc * 256 + (M p).toNat) (memBytes M (p + 1) k) := by
      rw [memBytes_succ]; rfl
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc 0xB0 tlv_at_ac (by decide) (by rw [t6, u3.self.zero]; decide)
      refine ⟨n4, .cons d1 (.cons d2 (c3.trans (.single d4))), u4.self, ?_, fun r h2 h5 h5' h6 => ?_⟩
      · rw [u4.regs, a5v, hfold]; rfl
      · rw [u4.regs, k3 r h2 h5 h5' h6]
    · obtain ⟨n4, d4, u4⟩ := u3.self.taken hc 0x9A tlv_at_ac (by decide) (by
        rw [t6, u3.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk this)
      have hacc' : (acc * 256 + (M p).toNat + 1) * 256 ^ k ≤ 2 ^ 32 := by
        have : (acc * 256 + (M p).toNat + 1) * 256 ^ k ≤ (acc + 1) * 256 ^ (k + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, ← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨n5, c5, u5, a55, k5⟩ := tlv_loop hc k (by omega) u4.self (by rw [u4.regs, t6]) (by rw [u4.regs, t5])
        (by rw [u4.regs, a5v]) hacc'
      refine ⟨n5, .cons d1 (.cons d2 (c3.trans (.cons d4 c5))), u5, by rw [a55, hfold], fun r h2 h5 h5' h6 => ?_⟩
      rw [k5 r h2 h5 h5' h6, u4.regs, k3 r h2 h5 h5' h6]

theorem tlv_tagb : ∀ b : BitVec 8, branchTaken .bne (aluEval .and (b.zeroExtend 32) 0x1F) 0x1F = !decide (b.toNat % 32 = 31) := by
  decide

theorem tlv_sgnb : ∀ b : BitVec 8, branchTaken .blt (b.signExtend 32) 0 = decide (128 ≤ b.toNat) := by decide

theorem tlv_lowb : ∀ b : BitVec 8, aluEval .and (b.signExtend 32) 0xFF = BitVec.ofNat 32 b.toNat := by decide

theorem tlv_cntb : ∀ b : BitVec 8, 128 ≤ b.toNat →
    branchTaken .bgeu 0xFFFFFFFB (aluEval .add (aluEval .and (BitVec.ofNat 32 b.toNat) 0x7F) 0xFFFFFFFB) =
      decide (b.toNat % 128 = 0 ∨ 4 < b.toNat % 128) := by decide

theorem tlv_cnt7 : ∀ b : BitVec 8, aluEval .and (BitVec.ofNat 32 b.toNat) 0x7F = BitVec.ofNat 32 (b.toNat % 128) := by
  decide

theorem tlv_zext : ∀ b : BitVec 8, (b.zeroExtend 32 : Word).extractLsb' 0 8 = b := by decide

theorem tlv_tag8 : ∀ b : BitVec 8, BitVec.ofNat 8 b.toNat = b := by decide

theorem memBytes_mem_lt {M : Word → BitVec 8} {p : Word} {n : Nat} : ∀ b ∈ memBytes M p n, b < 256 := by
  intro b hb
  unfold memBytes at hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  exact (M (p + BitVec.ofNat 32 i)).isLt

theorem memBytes_take' {M : Word → BitVec 8} {p : Word} {n k : Nat} (h : k ≤ n) :
    (memBytes M p n).take k = memBytes M p k := by
  unfold memBytes
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem beFold_lt : ∀ (bs : Bytes) (acc : Nat), (∀ b ∈ bs, b < 256) → beFold acc bs < (acc + 1) * 256 ^ bs.length
  | [], acc, _ => by show acc < (acc + 1) * 1; omega
  | b :: bs, acc, hb => by
    have hb0 := hb b List.mem_cons_self
    have ih := beFold_lt bs (acc * 256 + b) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    show beFold (acc * 256 + b) bs < _
    have : (acc * 256 + b + 1) * 256 ^ bs.length ≤ (acc + 1) * 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ bs.length) 256, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    simp only [List.length_cons]; omega

theorem derLongLen_ok : ∀ (bs : Bytes) (acc : Nat), (∀ b ∈ bs, b < 256) → (acc + 1) * 256 ^ bs.length ≤ 2 ^ 32 →
    derLongLen acc bs = .ok (beFold acc bs)
  | [], _, _, _ => rfl
  | b :: bs, acc, hb, h => by
    have hb0 := hb b List.mem_cons_self
    simp only [List.length_cons] at h
    have h1 : (acc * 256 + b + 1) * 256 ^ bs.length ≤ 2 ^ 32 := by
      have : (acc * 256 + b + 1) * 256 ^ bs.length ≤ (acc + 1) * 256 ^ (bs.length + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ bs.length) 256, ← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
      omega
    have h2 : acc * 256 + b < u32Limit := by
      have : 1 ≤ 256 ^ bs.length := Nat.pow_pos (by decide)
      have := Nat.mul_le_mul_left (acc * 256 + b + 1) this
      show _ < 2 ^ 32; omega
    simp only [derLongLen, ite_eq_left h2]
    exact derLongLen_ok bs _ (fun x hx => hb x (List.mem_cons_of_mem _ hx)) h1

/-- The registers `Der::tlv` may write. -/
def tlvClob (r : Fin 32) : Bool := r.val ∈ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17]

theorem tlv_keep {g h : Fin 32 → Word} {rd : Fin 32} {v : Word} (h0 : h 0 = 0) (hrd : tlvClob rd = true)
    (hg : ∀ r, tlvClob r = false → g r = h r) : ∀ r, tlvClob r = false → upd g rd v r = h r := fun r hr => by
  have hne : r ≠ rd := fun e => by rw [e, hrd] at hr; exact Bool.noConfusion hr
  by_cases hr0 : r.val = 0
  · have : r = 0 := Fin.ext hr0
    subst this; simp [upd]; exact h0.symm
  · simp only [upd_app, hr0, hne, ite_false]; exact hg r hr

/-- From 0x4 to the tag check at 0x10. -/
def tlvTag : List BInstr :=
  [.lw a3 a1 0x8, .lbu (7 : Fin 32) a3 0x0, .aluImm .and a5 (7 : Fin 32) 0x1F, .aluImm .add a2 x0 0x1F]

/-- From 0x2A to the form check at 0x36. -/
def tlvFirst : List BInstr :=
  [.aluImm .add (5 : Fin 32) a3 0x2, .aluImm .add a6 a4 0xFFFFFFFE, .aluImm .and a5 a2 0xFF]

/-- From 0x4C to the count check at 0x56. -/
def tlvCount : List BInstr :=
  [.aluImm .and (6 : Fin 32) a5 0x7F, .aluImm .add a2 (6 : Fin 32) 0xFFFFFFFB, .aluImm .add a5 x0 0xFFFFFFFB]

/-- From 0x8C to the loop's entry check at 0x96. -/
def tlvLong : List BInstr :=
  [.aluImm .add a5 x0 0x0, .alu .add (17 : Fin 32) (5 : Fin 32) (6 : Fin 32), .alu .sub a6 a6 (6 : Fin 32)]

section
set_option maxRecDepth 20000
theorem tlvTag_end : blockEnd derTlvCode 0x4 tlvTag = some 0x10 := by decide
theorem tlvFirst_end : blockEnd derTlvCode 0x2A tlvFirst = some 0x36 := by decide
theorem tlvCount_end : blockEnd derTlvCode 0x4C tlvCount = some 0x56 := by decide
theorem tlvLong_end : blockEnd derTlvCode 0x8C tlvLong = some 0x96 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Der::tlv`**: with the reader at `d`, whose unread bytes
start at `rp` and number `rl`, it stores `derTlv` of those bytes at `out`
and, on success, moves the reader past the element. -/
theorem derTlv_correct (m : Machine) {base out d retAddr : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base derTlvCode) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0)
    (hd : d.toNat % 4 = 0) (sOC : Sep out 17 base derTlvCode.length) (sDC : Sep (d + 8) 8 base derTlvCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      m'.mem = derTlvMem m.mem out d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
        (derTlv (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) ∧
      ∀ r, tlvClob r = false → reg m' r = reg m r := by
  obtain ⟨rp, hrp⟩ : ∃ rp, memLoad32 m.mem (d + 8) = rp := ⟨_, rfl⟩
  obtain ⟨rl, hrl⟩ : ∃ rl, memLoad32 m.mem (d + 0xC) = rl := ⟨_, rfl⟩
  rw [hrp, hrl]
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have K0 : ∀ r, tlvClob r = false → reg m r = reg m r := fun _ _ => rfl
  obtain ⟨n1, d1, u1⟩ := s0.lw hc tlv_at_0 (off' := 2) (by decide)
    (by rw [ha1]; exact aligned_add hd (k := 0xC) (by decide))
  rw [ha1, hrl] at u1
  have K1 := tlv_keep (v := rl) (rd := a4) hz (by decide) K0
  by_cases hl0 : rl = 0
  · obtain ⟨n2, d2, u2⟩ := u1.taken hc 0x5E tlv_at_2 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [hl0]; rfl)
    obtain ⟨n3, c3, pc3, mem3, k3⟩ := tlv_exit5e u2.self hc (by rw [u2.regs, upd_ne (by decide) (by decide), ha0])
      (by rw [u2.regs, upd_ne (by decide) (by decide), hra]) hret hout sOC
    refine ⟨n3, .cons d1 (.cons d2 c3), pc3, by rw [mem3, hl0]; rfl, fun r hr => ?_⟩
    rw [k3, u2.regs]; exact K1 r hr
  obtain ⟨n2, d2, u2⟩ := u1.notTaken hc 0x4 tlv_at_2 (by decide) (by
    simp only [upd_app]; simp +decide only [↓reduceIte]
    simp only [branchTaken]; exact beq_false_of_ne hl0)
  obtain ⟨n3, c3, u3⟩ := St.block tlvTag u2 hc tlvTag_end (by
    simp only [BlockOk, BInstr.ok, tlvTag]; simp +decide only [upd_app, ↓reduceIte]
    rw [ha1]; exact ⟨aligned_add hd (k := 8) (by decide), trivial⟩)
  simp only [runBlock, BInstr.run, tlvTag] at u3
  have g3 : ∀ r, reg n3 r = _ := u3.regs
  have v3 : reg n3 a3 = rp ∧ reg n3 7 = (m.mem rp).zeroExtend 32 ∧
      reg n3 a5 = aluEval .and ((m.mem rp).zeroExtend 32) 0x1F ∧ reg n3 a2 = 0x1F ∧ reg n3 a4 = rl ∧
      reg n3 a1 = d ∧ reg n3 a0 = out ∧ reg n3 ra = retAddr := by
    simp +decide only [g3, upd_app, ↓reduceIte]
    simp only [ha1, hrp, add_lit_zero, ha0, hra]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨v3a3, v37, v3a5, v3a2, v3a4, v3a1, v3a0, v3ra⟩ := v3
  have K3 : ∀ r, tlvClob r = false → reg n3 r = reg m r := fun r hr => by
    rw [g3]; exact tlv_keep hz (by decide) (tlv_keep hz (by decide) (tlv_keep hz (by decide)
      (tlv_keep hz (by decide) K1))) r hr
  obtain ⟨j, hj⟩ : ∃ j, rl.toNat = j + 1 := ⟨rl.toNat - 1, by
    have : rl.toNat ≠ 0 := fun h => hl0 (BitVec.eq_of_toNat_eq h); omega⟩
  have hL1 : memBytes m.mem rp rl.toNat = (m.mem rp).toNat :: memBytes m.mem (rp + 1) j := by
    rw [hj, memBytes_succ]
  rw [hL1]
  have z3 : reg n3 x0 = 0 := u3.zero
  by_cases htag : (m.mem rp).toNat % 32 = 31
  · obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc 0x14 tlv_at_10 (by decide) (by
      rw [v3a5, v3a2, tlv_tagb, htag]; rfl)
    obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc tlv_at_14 (off' := 0x16) (by decide)
    obtain ⟨n6, c6, pc6, mem6, k6⟩ := tlv_exit16 u5.self hc
      (by rw [u5.regs, upd_ne (by decide) (by decide), u4.regs, v3a0])
      (by rw [u5.regs, upd_ne (by decide) (by decide), u4.regs, v3ra]) hret hout sOC
    refine ⟨n6, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 c6)))), pc6, ?_, fun r hr => ?_⟩
    · rw [mem6, u5.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u4.regs, z3]
      simp only [derTlv, htag, ↓reduceIte]; rfl
    · rw [k6, u5.regs]; exact tlv_keep hz (by decide) (fun r hr => by rw [u4.regs, K3 r hr]) r hr
  obtain ⟨n4, d4, u4⟩ := u3.self.taken hc 0x20 tlv_at_10 (by decide) (by
    rw [v3a5, v3a2, tlv_tagb]; simp [htag])
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc tlv_at_20 (off' := 0x22) (by decide)
  have e4 : reg n4 = reg n3 := funext u4.regs
  have g5 : ∀ r, reg n5 r = upd (reg n3) a2 (aluEval .add (reg n3 x0) 1) r := fun r => by rw [u5.regs, e4]
  have K5 : ∀ r, tlvClob r = false → reg n5 r = reg m r := fun r hr => by
    rw [g5]; exact tlv_keep hz (by decide) K3 r hr
  have g5' : ∀ r, r ≠ a2 → reg n5 r = reg n3 r := fun r h => by rw [g5, upd_ne' h u3.self.zero]
  by_cases hj0 : j = 0
  · subst hj0
    obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0x5E tlv_at_22 (by decide) (by
      rw [g5' a4 (by decide), g5, upd_app]; simp +decide only [↓reduceIte]; rw [z3, v3a4]
      show (rl == aluEval .add 0 1) = true
      have : rl = 1 := BitVec.eq_of_toNat_eq (by rw [hj]; rfl)
      rw [this]; rfl)
    obtain ⟨n7, c7, pc7, mem7, k7⟩ := tlv_exit5e u6.self hc (by rw [u6.regs, g5' a0 (by decide), v3a0])
      (by rw [u6.regs, g5' ra (by decide), v3ra]) hret hout sOC
    refine ⟨n7, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 c7))))), pc7, ?_, fun r hr => ?_⟩
    · rw [mem7]; simp only [memBytes_zero, derTlv, htag, ↓reduceIte]; rfl
    · rw [k7, u6.regs, K5 r hr]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hL2 : memBytes m.mem (rp + 1) (i + 1) = (m.mem (rp + 1)).toNat :: memBytes m.mem (rp + 2) i := by
    rw [memBytes_succ, show rp + 1 + 1 = rp + 2 by rw [BitVec.add_assoc]; rfl]
  rw [hL2]
  have hrl2 : (rl + 0xFFFFFFFE).toNat = i := by
    rw [BitVec.toNat_add, hj]; show (i + 1 + 1 + 4294967294) % 2 ^ 32 = i
    have := rl.isLt; omega
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0x26 tlv_at_22 (by decide) (by
    rw [g5' a4 (by decide), g5, upd_app]; simp +decide only [↓reduceIte]; rw [z3, v3a4]
    show (rl == aluEval .add 0 1) = false
    exact beq_false_of_ne fun h => by
      have := congrArg BitVec.toNat h; rw [hj] at this
      have h1 : (aluEval .add 0 1 : Word).toNat = 1 := rfl
      omega)
  obtain ⟨n7, d7, u7⟩ := u6.self.lb hc tlv_at_26 (off' := 0x2A) (by decide)
  have e6 : reg n6 = reg n5 := funext u6.regs
  rw [e6, g5' a3 (by decide), v3a3] at u7
  obtain ⟨n8, c8, u8⟩ := St.block tlvFirst u7 hc tlvFirst_end (by simp [BlockOk, BInstr.ok, tlvFirst])
  simp only [runBlock, BInstr.run, tlvFirst] at u8
  have g8 : ∀ r, reg n8 r = _ := u8.regs
  have v8 : reg n8 5 = rp + 2 ∧ reg n8 a6 = rl + 0xFFFFFFFE ∧
      reg n8 a5 = BitVec.ofNat 32 (m.mem (rp + 1)).toNat ∧ reg n8 a2 = (m.mem (rp + 1)).signExtend 32 ∧
      reg n8 a3 = rp ∧ reg n8 a4 = rl ∧ reg n8 7 = (m.mem rp).zeroExtend 32 ∧ reg n8 a1 = d ∧ reg n8 a0 = out ∧
      reg n8 ra = retAddr := by
    simp +decide only [g8, upd_app, ↓reduceIte]
    simp only [g5' a3 (by decide), g5' a4 (by decide), g5' 7 (by decide), g5' a1 (by decide), g5' a0 (by decide),
      g5' ra (by decide), v3a3, v3a4, v37, v3a1, v3a0, v3ra, tlv_lowb]
    exact ⟨ev_add _ _, ev_add _ _, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  obtain ⟨v85, v8a6, v8a5, v8a2, v8a3, v8a4, v87, v8a1, v8a0, v8ra⟩ := v8
  have K8 : ∀ r, tlvClob r = false → reg n8 r = reg m r := fun r hr => by
    rw [g8]; exact tlv_keep hz (by decide) (tlv_keep hz (by decide) (tlv_keep hz (by decide)
      (tlv_keep hz (by decide) K5))) r hr
  have z8 : reg n8 x0 = 0 := u8.self.zero
  have hb1 := (m.mem (rp + 1)).isLt
  by_cases hshort : (m.mem (rp + 1)).toNat < 128
  · obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hc 0x3A tlv_at_36 (by decide) (by
      rw [v8a2, z8, tlv_sgnb]; exact decide_eq_false (by omega))
    obtain ⟨n10, d10, u10⟩ := u9.self.alu hc tlv_at_3a (off' := 0x3C) (by decide)
    have e9 : reg n9 = reg n8 := funext u9.regs
    have g10 : ∀ r, reg n10 r = upd (reg n8) 17 (aluEval .add (reg n8 x0) (reg n8 5)) r := fun r => by
      rw [u10.regs, e9]
    have g10' : ∀ r, r ≠ 17 → reg n10 r = reg n8 r := fun r h => by rw [g10, upd_ne' h u8.self.zero]
    have v1017 : reg n10 17 = rp + 2 := by rw [g10, upd_app]; simp +decide only [↓reduceIte]; rw [z8, v85]; exact zw _
    obtain ⟨n11, c11, pc11, mem11, k11⟩ := tlv_join u10.self hc (by rw [g10' a0 (by decide), v8a0])
      (by rw [g10' a1 (by decide), v8a1]) (by rw [g10' ra (by decide), v8ra]) hret hout hd sOC sDC
      (by rw [g10' a6 (by decide), g10' a4 (by decide), v8a6, v8a4, hrl2, hj]; omega)
    refine ⟨n11, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans
      (.cons d9 (.cons d10 c11))))))))), pc11, ?_, fun r hr => ?_⟩
    · rw [mem11, v1017, g10' a6 (by decide), g10' a5 (by decide), g10' a3 (by decide), g10' a4 (by decide),
        g10' 7 (by decide), v8a6, v8a5, v8a3, v8a4, v87, hrl2, ofNat_tn (by omega)]
      have hlen : (memBytes m.mem (rp + 2) i).length = i := memBytes_length _ _ _
      by_cases hlt : i < (m.mem (rp + 1)).toNat
      · rw [ite_eq_left hlt]
        simp only [derTlv, htag, hshort, hlen, hlt, ↓reduceIte]; rfl
      · rw [ite_eq_right hlt]
        simp only [derTlv, htag, hshort, hlen, hlt, ↓reduceIte, derTlvMem]
        rw [tlv_zext, tlv_tag8]
        have e1 : rp + 2 + BitVec.ofNat 32 (m.mem (rp + 1)).toNat = rp + BitVec.ofNat 32 (2 + (m.mem (rp + 1)).toNat) := by
          bv_omega
        have e2 : rl + 0xFFFFFFFE - BitVec.ofNat 32 (m.mem (rp + 1)).toNat =
            rl - BitVec.ofNat 32 (2 + (m.mem (rp + 1)).toNat) := by bv_omega
        have e3 : rl - (rl - BitVec.ofNat 32 (2 + (m.mem (rp + 1)).toNat)) =
            BitVec.ofNat 32 (2 + (m.mem (rp + 1)).toNat) := by bv_omega
        rw [e1, e2, e3]; rfl
    · rw [k11 r (fun e => by rw [e] at hr; exact Bool.noConfusion hr) (fun e => by rw [e] at hr; exact Bool.noConfusion hr)
        (fun e => by rw [e] at hr; exact Bool.noConfusion hr), g10, tlv_keep hz (by decide) K8 r hr]
  -- the long form
  have hlong : 128 ≤ (m.mem (rp + 1)).toNat := by omega
  obtain ⟨n9, d9, u9⟩ := u8.self.taken hc 0x4C tlv_at_36 (by decide) (by
    rw [v8a2, z8, tlv_sgnb]; exact decide_eq_true hlong)
  have e9 : reg n9 = reg n8 := funext u9.regs
  obtain ⟨n10, c10, u10⟩ := St.block tlvCount u9.self hc tlvCount_end (by simp [BlockOk, BInstr.ok, tlvCount])
  simp only [runBlock, BInstr.run, tlvCount] at u10
  rw [e9] at u10
  have g10 : ∀ r, reg n10 r = _ := u10.regs
  obtain ⟨cnt, hcnt⟩ : ∃ cnt, (m.mem (rp + 1)).toNat % 128 = cnt := ⟨_, rfl⟩
  have v10 : reg n10 6 = BitVec.ofNat 32 cnt ∧ reg n10 a5 = 0xFFFFFFFB ∧
      reg n10 a2 = aluEval .add (aluEval .and (BitVec.ofNat 32 (m.mem (rp + 1)).toNat) 0x7F) 0xFFFFFFFB := by
    simp +decide only [g10, upd_app, ↓reduceIte]
    rw [v8a5, tlv_cnt7, hcnt]
    exact ⟨rfl, trivial, rfl⟩
  obtain ⟨v106, v10a5, v10a2⟩ := v10
  have g10' : ∀ r, r ≠ 6 → r ≠ a2 → r ≠ a5 → reg n10 r = reg n8 r := fun r h1 h2 h3 => by
    rw [g10]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact z8.symm
    simp only [upd_app, h0, h1, h2, h3, ite_false]
  have K10 : ∀ r, tlvClob r = false → reg n10 r = reg m r := fun r hr => by
    rw [g10]; exact tlv_keep hz (by decide) (tlv_keep hz (by decide) (tlv_keep hz (by decide) K8)) r hr
  have z10 : reg n10 x0 = 0 := u10.self.zero
  -- the bad-DER exit from 0x14, for every check that branches there
  have bad : ∀ {nb : Machine}, St m.mem base nb 0x14 (reg nb) → reg nb a0 = out → reg nb ra = retAddr →
      (∀ r, tlvClob r = false → reg nb r = reg m r) →
      ∃ n', Steps nb n' ∧ n'.pc = retAddr ∧ n'.mem = derTlvMem m.mem out d rp rl (.error .badDer) ∧
        ∀ r, tlvClob r = false → reg n' r = reg m r := by
    intro nb sb hb0 hbra Kb
    obtain ⟨n1, d1, u1⟩ := sb.aluImm hc tlv_at_14 (off' := 0x16) (by decide)
    obtain ⟨n2, c2, pc2, mem2, k2⟩ := tlv_exit16 u1.self hc (by rw [u1.regs, upd_ne (by decide) (by decide), hb0])
      (by rw [u1.regs, upd_ne (by decide) (by decide), hbra]) hret hout sOC
    refine ⟨n2, .cons d1 c2, pc2, ?_, fun r hr => ?_⟩
    · rw [mem2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sb.zero]; rfl
    · rw [k2, u1.regs]; exact tlv_keep hz (by decide) Kb r hr
  have hlen : (memBytes m.mem (rp + 2) i).length = i := memBytes_length _ _ _
  by_cases hbadc : cnt = 0 ∨ 4 < cnt
  · obtain ⟨n11, d11, u11⟩ := u10.self.taken hc 0x14 tlv_at_56 (by decide) (by
      rw [v10a5, v10a2, tlv_cntb _ hlong, hcnt]; exact decide_eq_true hbadc)
    obtain ⟨n12, c12, pc12, mem12, k12⟩ := bad u11.self (by rw [u11.regs, g10' a0 (by decide) (by decide) (by decide), v8a0])
      (by rw [u11.regs, g10' ra (by decide) (by decide) (by decide), v8ra]) (fun r hr => by rw [u11.regs, K10 r hr])
    refine ⟨n12, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans
      (.cons d9 (c10.trans (.cons d11 c12)))))))))), pc12, ?_, k12⟩
    rw [mem12]
    simp only [derTlv, htag, hshort, hcnt, hbadc, ↓reduceIte]
  obtain ⟨n11, d11, u11⟩ := u10.self.notTaken hc 0x5A tlv_at_56 (by decide) (by
    rw [v10a5, v10a2, tlv_cntb _ hlong, hcnt]; exact decide_eq_false hbadc)
  have e11 : reg n11 = reg n10 := funext u11.regs
  have hc4 : 1 ≤ cnt ∧ cnt ≤ 4 := by
    have hn0 : cnt ≠ 0 := fun h => hbadc (.inl h)
    have hn4 : ¬ 4 < cnt := fun h => hbadc (.inr h)
    exact ⟨Nat.pos_of_ne_zero hn0, Nat.le_of_not_lt hn4⟩
  by_cases hshortL : i < cnt
  · obtain ⟨n12, d12, u12⟩ := u11.self.notTaken hc 0x5E tlv_at_5a (by decide) (by
      rw [e11, g10' a6 (by decide) (by decide) (by decide), v8a6, v106]
      show (!decide ((rl + 0xFFFFFFFE).toNat < (BitVec.ofNat 32 cnt).toNat)) = false
      rw [hrl2, ofNat_tn (by omega), decide_eq_true hshortL]; rfl)
    obtain ⟨n13, c13, pc13, mem13, k13⟩ := tlv_exit5e u12.self hc
      (by rw [u12.regs, e11, g10' a0 (by decide) (by decide) (by decide), v8a0])
      (by rw [u12.regs, e11, g10' ra (by decide) (by decide) (by decide), v8ra]) hret hout sOC
    refine ⟨n13, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans
      (.cons d9 (c10.trans (.cons d11 (.cons d12 c13))))))))))), pc13, ?_, fun r hr => by
        rw [k13, u12.regs, e11, K10 r hr]⟩
    rw [mem13]
    have hbc : ¬ (cnt = 0 ∨ 4 < cnt) := hbadc
    simp only [derTlv, htag, hshort, hcnt, hbc, hlen, hshortL, ↓reduceIte]; rfl
  obtain ⟨n12, d12, u12⟩ := u11.self.taken hc 0x86 tlv_at_5a (by decide) (by
    rw [e11, g10' a6 (by decide) (by decide) (by decide), v8a6, v106]
    show (!decide ((rl + 0xFFFFFFFE).toNat < (BitVec.ofNat 32 cnt).toNat)) = true
    rw [hrl2, ofNat_tn (by omega), decide_eq_false hshortL]; rfl)
  have e12 : reg n12 = reg n10 := by rw [← e11]; exact funext u12.regs
  have r10 : ∀ r, r ≠ 6 → r ≠ a2 → r ≠ a5 → reg n12 r = reg n8 r := fun r h1 h2 h3 => by
    rw [e12, g10' r h1 h2 h3]
  obtain ⟨n13, d13, u13⟩ := u12.self.lbu hc tlv_at_86 (off' := 0x8A) (by decide)
  rw [r10 5 (by decide) (by decide) (by decide), v85, add_lit_zero] at u13
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hL3 : memBytes m.mem (rp + 2) (i' + 1) = (m.mem (rp + 2)).toNat :: memBytes m.mem (rp + 2 + 1) i' :=
    memBytes_succ _ _ _
  have hhead : (memBytes m.mem (rp + 2) (i' + 1)).head? = some (m.mem (rp + 2)).toNat := by rw [hL3]; rfl
  have hz12 : reg n12 x0 = 0 := u12.self.zero
  by_cases hb0 : (m.mem (rp + 2)).toNat = 0
  · obtain ⟨n14, d14, u14⟩ := u13.taken hc 0x14 tlv_at_8a (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]
      show ((m.mem (rp + 2)).zeroExtend 32 == 0) = true
      have : m.mem (rp + 2) = 0 := BitVec.eq_of_toNat_eq hb0
      rw [this]; rfl)
    obtain ⟨n15, c15, pc15, mem15, k15⟩ := bad u14.self
      (by rw [u14.regs, upd_ne (by decide) (by decide), r10 a0 (by decide) (by decide) (by decide), v8a0])
      (by rw [u14.regs, upd_ne (by decide) (by decide), r10 ra (by decide) (by decide) (by decide), v8ra])
      (fun r hr => by rw [u14.regs, tlv_keep hz (by decide) (fun r hr => by rw [e12, K10 r hr]) r hr])
    refine ⟨n15, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans
      (.cons d9 (c10.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 c15))))))))))))), pc15, ?_, k15⟩
    rw [mem15]
    have hbc : ¬ (cnt = 0 ∨ 4 < cnt) := hbadc
    simp only [derTlv, htag, hshort, hcnt, hbc, hlen, hshortL, hhead, hb0, ↓reduceIte]
  obtain ⟨n14, d14, u14⟩ := u13.notTaken hc 0x8C tlv_at_8a (by decide) (by
    simp only [upd_app]; simp +decide only [↓reduceIte]
    show ((m.mem (rp + 2)).zeroExtend 32 == 0) = false
    exact beq_false_of_ne fun h => hb0 (by
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.mem (rp + 2)).isLt; omega)] at this))
  have S14 : Steps m n14 := .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans
    (.cons d9 (c10.trans (.cons d11 (.cons d12 (.cons d13 (.single d14)))))))))))))
  obtain ⟨n15, c15, u15⟩ := St.block tlvLong u14 hc tlvLong_end (by simp [BlockOk, BInstr.ok, tlvLong])
  simp only [runBlock, BInstr.run, tlvLong] at u15
  have g15 : ∀ r, reg n15 r = _ := u15.regs
  have r12 : ∀ r, r ≠ 6 → r ≠ a2 → r ≠ a5 → reg n12 r = reg n8 r := r10
  have v15 : reg n15 a5 = BitVec.ofNat 32 0 ∧ reg n15 17 = rp + 2 + BitVec.ofNat 32 cnt ∧
      reg n15 a6 = rl + 0xFFFFFFFE - BitVec.ofNat 32 cnt ∧ reg n15 6 = BitVec.ofNat 32 cnt ∧ reg n15 5 = rp + 2 := by
    simp +decide only [g15, upd_app, ↓reduceIte]
    simp only [r12 5 (by decide) (by decide) (by decide), r12 a6 (by decide) (by decide) (by decide), v85, v8a6,
      e12, v106]
    exact ⟨trivial, rfl, rfl, trivial, trivial⟩
  obtain ⟨v15a5, v1517, v15a6, v156, v155⟩ := v15
  have K15 : ∀ r, tlvClob r = false → reg n15 r = reg m r := fun r hr => by
    rw [g15]; exact tlv_keep hz (by decide) (tlv_keep hz (by decide) (tlv_keep hz (by decide)
      (tlv_keep hz (by decide) (fun r hr => by rw [e12, K10 r hr])))) r hr
  have g15' : ∀ r, r ≠ a5 → r ≠ 17 → r ≠ a6 → r ≠ a2 → r ≠ 6 → reg n15 r = reg n8 r := fun r h1 h2 h3 h4 h6 => by
    rw [g15]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact z8.symm
    simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
    exact r12 r h6 h4 h1
  obtain ⟨n16, d16, u16⟩ := u15.self.notTaken hc 0x9A tlv_at_96 (by decide) (by
    rw [v156, u15.self.zero]
    show (BitVec.ofNat 32 cnt == 0) = false
    exact beq_false_of_ne fun h => by
      have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; change cnt = 0 at this; omega)
  have hpow : (0 + 1) * 256 ^ cnt ≤ 2 ^ 32 := by
    rw [Nat.zero_add, Nat.one_mul]
    rcases (by omega : cnt = 1 ∨ cnt = 2 ∨ cnt = 3 ∨ cnt = 4) with h | h | h | h <;> rw [h] <;> decide
  obtain ⟨n17, c17, u17, a517, k17⟩ := tlv_loop hc cnt hc4.1 u16.self (by rw [u16.regs, v156])
    (by rw [u16.regs, v155]) (by rw [u16.regs, v15a5]) hpow
  obtain ⟨len, hlenv⟩ : ∃ len, beFold 0 (memBytes m.mem (rp + 2) cnt) = len := ⟨_, rfl⟩
  rw [hlenv] at a517
  have hlen32 : len < 2 ^ 32 := by
    rw [← hlenv]
    have := beFold_lt (memBytes m.mem (rp + 2) cnt) 0 memBytes_mem_lt
    rw [memBytes_length] at this; omega
  have hdl : derLongLen 0 ((memBytes m.mem (rp + 2) (i' + 1)).take cnt) = .ok len := by
    rw [memBytes_take' (by omega), derLongLen_ok _ _ memBytes_mem_lt (by rw [memBytes_length]; exact hpow), hlenv]
  have r17 : ∀ r, r ≠ a2 → r ≠ a5 → r ≠ 5 → r ≠ 6 → reg n17 r = reg n15 r := fun r h1 h2 h3 h4 => by
    rw [k17 r h1 h2 h3 h4, u16.regs]
  obtain ⟨n18, d18, u18⟩ := u17.aluImm hc tlv_at_b0 (off' := 0xB4) (by decide)
  have K18 : ∀ r, tlvClob r = false → reg n18 r = reg m r := fun r hr => by
    have h2 : r ≠ a2 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
    have h5 : r ≠ a5 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
    have h5' : r ≠ 5 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
    have h6 : r ≠ 6 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
    rw [u18.regs, upd_ne' h2 u17.zero, r17 r h2 h5 h5' h6, K15 r hr]
  have r18 : ∀ r, r ≠ a2 → r ≠ a5 → r ≠ 5 → r ≠ 6 → r ≠ 17 → r ≠ a6 → reg n18 r = reg n8 r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [u18.regs, upd_ne' h1 u17.zero, r17 r h1 h2 h3 h4, g15' r h2 h5 h6 h1 h4]
  have a518 : reg n18 a5 = BitVec.ofNat 32 len := by rw [u18.regs, upd_ne' (by decide) u17.zero, a517]
  by_cases h128 : len < 0x80
  · obtain ⟨n19, d19, u19⟩ := u18.self.taken hc 0x14 tlv_at_b4 (by decide) (by
      rw [u18.regs, upd_app, a518]; simp +decide only [↓reduceIte]; rw [u17.zero]
      show (!decide ((aluEval .add 0 0x7F : Word).toNat < (BitVec.ofNat 32 len).toNat)) = true
      rw [ofNat_tn hlen32, decide_eq_false (by show ¬ 127 < len; omega)]; rfl)
    obtain ⟨n20, c20, pc20, mem20, k20⟩ := bad u19.self
      (by rw [u19.regs, r18 a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v8a0])
      (by rw [u19.regs, r18 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v8ra])
      (fun r hr => by rw [u19.regs, K18 r hr])
    refine ⟨n20, S14.trans (c15.trans (.cons d16 (c17.trans (.cons d18 (.cons d19 c20))))), pc20, ?_, k20⟩
    rw [mem20]
    have hbc : ¬ (cnt = 0 ∨ 4 < cnt) := hbadc
    simp only [derTlv, htag, hshort, hcnt, hbc, hlen, hshortL, hhead, hdl, h128, ↓reduceIte, ite_self]
  obtain ⟨n19, d19, u19⟩ := u18.self.notTaken hc 0xB8 tlv_at_b4 (by decide) (by
    rw [u18.regs, upd_app, a518]; simp +decide only [↓reduceIte]; rw [u17.zero]
    show (!decide ((aluEval .add 0 0x7F : Word).toNat < (BitVec.ofNat 32 len).toNat)) = false
    rw [ofNat_tn hlen32, decide_eq_true (by show 127 < len; omega)]; rfl)
  obtain ⟨n20, d20, u20⟩ := u19.self.jump hc tlv_at_b8 (off' := 0x3C) (by decide) (by
    rw [u19.self.pc, show base + BitVec.ofNat 32 0xB8 + 0xFFFFFF84 = base + BitVec.ofNat 32 0x3C by
      rw [BitVec.add_assoc]; rfl]
    exact even_bit0 (even_at base hP 0x3C (by decide)))
  have e20 : reg n20 = reg n18 := by rw [← funext u19.regs]; exact funext u20.regs
  have hsub : (rl + 0xFFFFFFFE - BitVec.ofNat 32 cnt).toNat = i' + 1 - cnt := by
    rw [BitVec.toNat_sub, hrl2, ofNat_tn (by omega)]; omega
  have rr : ∀ r, r ≠ a2 → r ≠ a5 → r ≠ 5 → r ≠ 6 → reg n20 r = reg n15 r := fun r h1 h2 h3 h4 => by
    rw [e20, u18.regs, upd_ne' h1 u17.zero, r17 r h1 h2 h3 h4]
  obtain ⟨n21, c21, pc21, mem21, k21⟩ := tlv_join u20.self hc
    (by rw [e20, r18 a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v8a0])
    (by rw [e20, r18 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v8a1])
    (by rw [e20, r18 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v8ra])
    hret hout hd sOC sDC
    (by rw [rr a6 (by decide) (by decide) (by decide) (by decide), v15a6, hsub,
        e20, r18 a4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v8a4, hj]; omega)
  refine ⟨n21, S14.trans (c15.trans (.cons d16 (c17.trans (.cons d18 (.cons d19 (.cons d20 c21)))))), pc21, ?_,
    fun r hr => ?_⟩
  · rw [mem21, rr a6 (by decide) (by decide) (by decide) (by decide), rr 17 (by decide) (by decide) (by decide)
      (by decide), v15a6, v1517, e20, a518,
      r18 a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r18 a4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r18 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v8a3, v8a4, v87, hsub,
      ofNat_tn hlen32]
    have hbc : ¬ (cnt = 0 ∨ 4 < cnt) := hbadc
    have h128' : ¬ len < 128 := h128
    by_cases hlt : i' + 1 - cnt < len
    · rw [ite_eq_left hlt]
      simp only [derTlv, htag, hshort, hcnt, hbc, hlen, hshortL, hhead, Option.some.injEq, hb0, hdl, h128', hlt, ↓reduceIte]; rfl
    · rw [ite_eq_right hlt]
      simp only [derTlv, htag, hshort, hcnt, hbc, hlen, hshortL, hhead, Option.some.injEq, hb0, hdl, h128', hlt, ↓reduceIte, derTlvMem]
      rw [tlv_zext, tlv_tag8]
      have e1 : rp + 2 + BitVec.ofNat 32 cnt + BitVec.ofNat 32 len = rp + BitVec.ofNat 32 (2 + cnt + len) := by
        bv_omega
      have e2 : rl + 0xFFFFFFFE - BitVec.ofNat 32 cnt - BitVec.ofNat 32 len = rl - BitVec.ofNat 32 (2 + cnt + len) := by
        bv_omega
      have e3 : rl - (rl - BitVec.ofNat 32 (2 + cnt + len)) = BitVec.ofNat 32 (2 + cnt + len) := by bv_omega
      have e4 : rp + 2 + BitVec.ofNat 32 cnt = rp + BitVec.ofNat 32 (2 + cnt) := by bv_omega
      rw [e1, e2, e3, e4]
  · have h1 : r ≠ a2 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
    have h4 : r ≠ a4 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
    have h6 : r ≠ a6 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
    rw [k21 r h1 h4 h6, e20, K18 r hr]

end C3.RV32
