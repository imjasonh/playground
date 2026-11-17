import C3BootProofs.Proofs.ImageParseCur
import C3BootProofs.Proofs.Parse

/-!
# `image::parse`'s calls

Each lemma runs one call from `image::parse` through the callee's theorem:
the reader is at `G + 0x18`, and every separation the callee needs comes from
`IEnv`.
-/

namespace C3.RV32.Cur

open C3.Image

set_option maxRecDepth 20000

/-- A call from `image::parse` to `Reader::magic`. -/
theorem ip_magic {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {k imm o : Word} (s : St Mx P m off f)
    (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFFD2E)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x18) (ha1 : f a1 = k)
    (hrp : memLoad32 Mx (G + 0x18) = ptr) (hrl : memLoad32 Mx (G + 0x18 + 4) = len) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = magicResult Mx (G + 0x18) k ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep R 48 x 1 → m'.mem x = magicMem Mx (G + 0x18) x := by
  obtain ⟨e32, -, -, e48, e50, -, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFFD2E).toNat % 2 = 0 := even_at P env.hP 0xFFFFFD2E (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have W0 : P + 0xFFFFFD2E = ipWindow P + BitVec.ofNat 32 0 := (add_ofNat_zero _).symm
  have WA : P + 0xFFFFFD2E + 0x1BC = ipWindow P + BitVec.ofNat 32 0x1BC := rfl
  have WB : P + 0xFFFFFD2E + 0x1BC + 0xFFFFFF96 = ipWindow P + BitVec.ofNat 32 0x152 := by
    rw [BitVec.add_assoc (P + 0xFFFFFD2E) 0x1BC 0xFFFFFF96]; rfl
  have R0 : R = R + BitVec.ofNat 32 0 := (add_ofNat_zero R).symm
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := Cur.readerMagic_correct m1 (P + 0xFFFFFD2E)
    (P + BitVec.ofNat 32 (off + 8)) (G + 0x18) k
    (fun i hi => by rw [mem1]; exact code.magic i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFFD2E + 0x1BC = P + 0xFFFFFEEA by rw [BitVec.add_assoc]; rfl]
                    exact code.array4 i hi)
    (fun i hi => by
      rw [mem1, show P + 0xFFFFFD2E + 0x1BC + 0xFFFFFF96 = P + 0xFFFFFE80 by simp only [BitVec.add_assoc]; rfl]
      exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact env.hG)
    (aligned_add env.hG (k := 0x18) (by decide))
    (by rw [mem1, hrp, hrl]; exact env.hbuf)
    (by rw [sp1, e32, W0, R0]; exact env.stack_code 0 48 (by omega) 0 _ (by decide))
    (by rw [sp1, e32, WA, R0]; exact env.stack_code 0 48 (by omega) 0x1BC _ (by decide))
    (by rw [sp1, e32, WB, R0]; exact env.stack_code 0 48 (by omega) 0x152 _ (by decide))
    (by rw [e50, W0]; exact env.stack_code 0x50 4 (by omega) 0 _ (by decide))
    (by rw [e50, WA]; exact env.stack_code 0x50 4 (by omega) 0x1BC _ (by decide))
    (by rw [e50, WB]; exact env.stack_code 0x50 4 (by omega) 0x152 _ (by decide))
    (by rw [sp1, e32, e48]
        have := env.stack_stack 0x48 12 0 48 (by omega) (by omega) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, sp1, e32, R0]; exact env.stack_buf 0 48 (by omega))
    (by rw [mem1, hrp, hrl, e50]; exact env.stack_buf 0x50 4 (by omega))
  rw [mem1] at a02 mem2
  rw [sp1, e32] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h6 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5 h6, r1 r h7]

/-- A call from `image::parse` to `Reader::version_1`. -/
theorem ip_version {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx P m off f)
    (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFFD80)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x18)
    (hrp : memLoad32 Mx (G + 0x18) = ptr) (hrl : memLoad32 Mx (G + 0x18 + 4) = len) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = version1Result Mx (G + 0x18) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 16) 32 x 1 → m'.mem x = u16Mem Mx (G + 0x18) x := by
  obtain ⟨-, e16, -, e48, e50, -, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFFD80).toNat % 2 = 0 := even_at P env.hP 0xFFFFFD80 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WV : P + 0xFFFFFD80 = ipWindow P + BitVec.ofNat 32 0x52 := ip_wq P _ 0x52 (by decide)
  have WU : P + 0xFFFFFD80 + 0x126 = ipWindow P + BitVec.ofNat 32 0x178 := by
    rw [BitVec.add_assoc]; exact ip_wq P _ 0x178 (by decide)
  have WB : P + 0xFFFFFD80 + 0x126 + 0xFFFFFFDA = ipWindow P + BitVec.ofNat 32 0x152 := by
    rw [BitVec.add_assoc (P + 0xFFFFFD80) 0x126 0xFFFFFFDA, BitVec.add_assoc P]
    exact ip_wq P _ 0x152 (by decide)
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerVersion1_correct m1 (P + 0xFFFFFD80)
    (P + BitVec.ofNat 32 (off + 8)) (G + 0x18)
    (fun i hi => by rw [mem1]; exact code.version i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFFD80 + 0x126 = P + 0xFFFFFEA6 by
                      rw [BitVec.add_assoc]; rfl]; exact code.u16 i hi)
    (fun i hi => by
      rw [mem1, show P + 0xFFFFFD80 + 0x126 + 0xFFFFFFDA = P + 0xFFFFFE80 by simp only [BitVec.add_assoc]; rfl]
      exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact env.hG) (aligned_add env.hG (k := 0x18) (by decide))
    (by rw [mem1, hrp, hrl]; exact env.hbuf)
    (by rw [sp1, e16, WV]; exact env.stack_code 16 32 (by omega) 0x52 _ (by decide))
    (by rw [sp1, e16, WU]; exact env.stack_code 16 32 (by omega) 0x178 _ (by decide))
    (by rw [sp1, e16, WB]; exact env.stack_code 16 32 (by omega) 0x152 _ (by decide))
    (by rw [e50, WV]; exact env.stack_code 0x50 4 (by omega) 0x52 _ (by decide))
    (by rw [e50, WU]; exact env.stack_code 0x50 4 (by omega) 0x178 _ (by decide))
    (by rw [e50, WB]; exact env.stack_code 0x50 4 (by omega) 0x152 _ (by decide))
    (by rw [sp1, e16, e48]; exact env.stack_stack 0x48 12 16 32 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e16]; exact env.stack_buf 16 32 (by omega))
    (by rw [mem1, hrp, hrl, e50]; exact env.stack_buf 0x50 4 (by omega))
  rw [mem1] at a02 mem2
  rw [sp1, e16] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `image::parse` to `Reader::u16`. -/
theorem ip_u16 {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx P m off f)
    (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFFEA6)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x18)
    (hrp : memLoad32 Mx (G + 0x18) = ptr) (hrl : memLoad32 Mx (G + 0x18 + 4) = len) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = u16Result Mx (G + 0x18) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 → m'.mem x = u16Mem Mx (G + 0x18) x := by
  obtain ⟨-, -, e32, e48, e50, -, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFFEA6).toNat % 2 = 0 := even_at P env.hP 0xFFFFFEA6 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WU : P + 0xFFFFFEA6 = ipWindow P + BitVec.ofNat 32 0x178 := ip_wq P _ 0x178 (by decide)
  have WB : P + 0xFFFFFEA6 + 0xFFFFFFDA = ipWindow P + BitVec.ofNat 32 0x152 := by
    rw [BitVec.add_assoc]; exact ip_wq P _ 0x152 (by decide)
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerU16_correct m1 (P + 0xFFFFFEA6)
    (P + BitVec.ofNat 32 (off + 8)) (G + 0x18)
    (fun i hi => by rw [mem1]; exact code.u16 i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFFEA6 + 0xFFFFFFDA = P + 0xFFFFFE80 by
                      rw [BitVec.add_assoc]; rfl]; exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact env.hG) (aligned_add env.hG (k := 0x18) (by decide))
    (by rw [mem1, hrp, hrl]; exact env.hbuf)
    (by rw [sp1, e32, WU]; exact env.stack_code 32 16 (by omega) 0x178 _ (by decide))
    (by rw [sp1, e32, WB]; exact env.stack_code 32 16 (by omega) 0x152 _ (by decide))
    (by rw [e50, WU]; exact env.stack_code 0x50 4 (by omega) 0x178 _ (by decide))
    (by rw [e50, WB]; exact env.stack_code 0x50 4 (by omega) 0x152 _ (by decide))
    (by rw [sp1, e32, e48]; exact env.stack_stack 0x48 12 32 16 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e32]; exact env.stack_buf 32 16 (by omega))
    (by rw [mem1, hrp, hrl, e50]; exact env.stack_buf 0x50 4 (by omega))
  rw [mem1] at a02 mem2
  rw [sp1, e32] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `image::parse` to `Reader::u8`. -/
theorem ip_u8 {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx P m off f)
    (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFFDAA)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x18)
    (hrp : memLoad32 Mx (G + 0x18) = ptr) (hrl : memLoad32 Mx (G + 0x18 + 4) = len) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = (u8Result Mx (G + 0x18)).1 ∧ reg m' a1 = (u8Result Mx (G + 0x18)).2 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 → m'.mem x = reservedMem Mx (G + 0x18) 1 x := by
  obtain ⟨-, -, e32, e48, e50, -, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFFDAA).toNat % 2 = 0 := even_at P env.hP 0xFFFFFDAA (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WU : P + 0xFFFFFDAA = ipWindow P + BitVec.ofNat 32 0x7C := ip_wq P _ 0x7C (by decide)
  have WB : P + 0xFFFFFDAA + 0xD6 = ipWindow P + BitVec.ofNat 32 0x152 := by
    rw [BitVec.add_assoc]; exact ip_wq P _ 0x152 (by decide)
  obtain ⟨m2, c2, pc2, sp2, a02, a12, fr2, mem2⟩ := readerU8_correct m1 (P + 0xFFFFFDAA)
    (P + BitVec.ofNat 32 (off + 8)) (G + 0x18)
    (fun i hi => by rw [mem1]; exact code.u8 i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFFDAA + 0xD6 = P + 0xFFFFFE80 by
                      rw [BitVec.add_assoc]; rfl]; exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact env.hG) (aligned_add env.hG (k := 0x18) (by decide))
    (by rw [mem1, hrp, hrl]; exact env.hbuf)
    (by rw [sp1, e32, WU]; exact env.stack_code 32 16 (by omega) 0x7C _ (by decide))
    (by rw [sp1, e32, WB]; exact env.stack_code 32 16 (by omega) 0x152 _ (by decide))
    (by rw [e50, WU]; exact env.stack_code 0x50 4 (by omega) 0x7C _ (by decide))
    (by rw [e50, WB]; exact env.stack_code 0x50 4 (by omega) 0x152 _ (by decide))
    (by rw [sp1, e32, e48]; exact env.stack_stack 0x48 12 32 16 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e32]; exact env.stack_buf 32 16 (by omega))
    (by rw [mem1, hrp, hrl, e50]; exact env.stack_buf 0x50 4 (by omega))
  rw [mem1] at a02 a12 mem2
  rw [sp1, e32] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, a12,
    fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `image::parse` to `Reader::reserved(n)`. -/
theorem ip_reserved {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o n : Word} (s : St Mx P m off f)
    (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFFDE4)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x18) (ha1 : f a1 = n) (hn : n ≠ 0)
    (hrp : memLoad32 Mx (G + 0x18) = ptr) (hrl : memLoad32 Mx (G + 0x18 + 4) = len) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = reservedResult Mx (G + 0x18) n ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 → m'.mem x = reservedMem Mx (G + 0x18) n x := by
  obtain ⟨-, -, e32, e48, e50, -, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFFDE4).toNat % 2 = 0 := even_at P env.hP 0xFFFFFDE4 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WR : P + 0xFFFFFDE4 = ipWindow P + BitVec.ofNat 32 0xB6 := ip_wq P _ 0xB6 (by decide)
  have WB : P + 0xFFFFFDE4 + 0x9C = ipWindow P + BitVec.ofNat 32 0x152 := by
    rw [BitVec.add_assoc]; exact ip_wq P _ 0x152 (by decide)
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerReserved_correct m1 (P + 0xFFFFFDE4)
    (P + BitVec.ofNat 32 (off + 8)) (G + 0x18) n
    (fun i hi => by rw [mem1]; exact code.reserved i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFFDE4 + 0x9C = P + 0xFFFFFE80 by
                      rw [BitVec.add_assoc]; rfl]; exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) hn
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact env.hG) (aligned_add env.hG (k := 0x18) (by decide))
    (by rw [mem1, hrp, hrl]; exact env.hbuf)
    (by rw [sp1, e32, WR]; exact env.stack_code 32 16 (by omega) 0xB6 _ (by decide))
    (by rw [sp1, e32, WB]; exact env.stack_code 32 16 (by omega) 0x152 _ (by decide))
    (by rw [e50, WR]; exact env.stack_code 0x50 4 (by omega) 0xB6 _ (by decide))
    (by rw [e50, WB]; exact env.stack_code 0x50 4 (by omega) 0x152 _ (by decide))
    (by rw [sp1, e32, e48]; exact env.stack_stack 0x48 12 32 16 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e32]; exact env.stack_buf 32 16 (by omega))
    (by rw [mem1, hrp, hrl, e50]; exact env.stack_buf 0x50 4 (by omega))
  rw [mem1] at a02 mem2
  rw [sp1, e32] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `image::parse` to `Reader::u32`, with the result at `G + c`. -/
theorem ip_u32 {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (c : Nat) (hc0 : 0x24 ≤ c)
    (hc1 : c + 8 ≤ 0x12C) (hc4 : c % 4 = 0) (s : St Mx P m off f) (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x434)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + BitVec.ofNat 32 c) (ha1 : f a1 = G + 0x18)
    (hrp : memLoad32 Mx (G + 0x18) = ptr) (hrl : memLoad32 Mx (G + 0x18 + 4) = len) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep R 48 x 1 → m'.mem x = u32Mem Mx (G + BitVec.ofNat 32 c) (G + 0x18) x := by
  obtain ⟨e0, -, -, e48, e50, -, -⟩ := env.r_eqs
  have hev : (P + 0x434).toNat % 2 = 0 := even_at P env.hP 0x434 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WU : P + 0x434 = ipWindow P + BitVec.ofNat 32 0x706 := ip_wq P _ 0x706 (by decide)
  have WA : P + 0x434 + 0xFFFFFAB6 = ipWindow P + BitVec.ofNat 32 0x1BC := by
    rw [BitVec.add_assoc]; exact ip_wq P _ 0x1BC (by decide)
  have WB : P + 0x434 + 0xFFFFFAB6 + 0xFFFFFF96 = ipWindow P + BitVec.ofNat 32 0x152 := by
    rw [BitVec.add_assoc (P + 0x434), BitVec.add_assoc P]; exact ip_wq P _ 0x152 (by decide)
  have R0 : R = R + BitVec.ofNat 32 0 := (add_ofNat_zero R).symm
  have eO : G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x30 + c) := env.g_ofs c
  obtain ⟨m2, c2, pc2, sp2, fr2, mem2⟩ := Cur.readerU32_correct m1 (P + 0x434)
    (P + BitVec.ofNat 32 (off + 8)) (G + BitVec.ofNat 32 c) (G + 0x18)
    (fun i hi => by rw [mem1]; exact code.u32 i hi)
    (fun i hi => by rw [mem1, show P + 0x434 + 0xFFFFFAB6 = P + 0xFFFFFEEA by rw [BitVec.add_assoc]; rfl]
                    exact code.array4 i hi)
    (fun i hi => by
      rw [mem1, show P + 0x434 + 0xFFFFFAB6 + 0xFFFFFF96 = P + 0xFFFFFE80 by simp only [BitVec.add_assoc]; rfl]
      exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact env.hG)
    (aligned_add env.hG hc4) (aligned_add env.hG (k := 0x18) (by decide))
    (by rw [mem1, hrp, hrl]; exact env.hbuf)
    (by rw [sp1, e0, WU, R0]; exact env.stack_code 0 48 (by omega) 0x706 _ (by decide))
    (by rw [sp1, e0, WA, R0]; exact env.stack_code 0 48 (by omega) 0x1BC _ (by decide))
    (by rw [sp1, e0, WB, R0]; exact env.stack_code 0 48 (by omega) 0x152 _ (by decide))
    (by rw [eO, WU]; exact env.stack_code (0x30 + c) 8 (by omega) 0x706 _ (by decide))
    (by rw [e50, WU]; exact env.stack_code 0x50 4 (by omega) 0x706 _ (by decide))
    (by rw [e50, WA]; exact env.stack_code 0x50 4 (by omega) 0x1BC _ (by decide))
    (by rw [e50, WB]; exact env.stack_code 0x50 4 (by omega) 0x152 _ (by decide))
    (by rw [sp1, e0, e48]
        have := env.stack_stack 0x48 12 0 48 (by omega) (by omega) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [sp1, e0, eO]
        have := env.stack_stack (0x30 + c) 8 0 48 (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, sp1, e0]
        have := env.stack_buf 0 48 (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, e50]; exact env.stack_buf 0x50 4 (by omega))
  rw [mem1] at mem2
  rw [sp1, e0] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `image::parse` to `Segment::physical`, with the result at
`G + 0x124`. -/
theorem ip_physical {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o addr : Word} {k : BitVec 8}
    (s : St Mx P m off f) (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x484)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : f a0 = G + 0x124) (ha1 : f a1 = addr) (ha2 : f a2 = k.zeroExtend 32) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧
      m'.mem = physMem Mx (G + 0x124) k addr ∧
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → reg m' r = f r) := by
  obtain ⟨-, -, -, -, -, -, e154⟩ := env.r_eqs
  have hev : (P + 0x484).toNat % 2 = 0 := even_at P env.hP 0x484 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have WP : P + 0x484 = ipWindow P + BitVec.ofNat 32 0x756 := ip_wq P _ 0x756 (by decide)
  obtain ⟨m2, c2, pc2, mem2, fr2⟩ := segmentPhysical_correct m1 (P + 0x484)
    (P + BitVec.ofNat 32 (off + 8)) (G + 0x124) addr k
    (fun i hi => by rw [mem1]; exact code.physical i hi) hev pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (aligned_add env.hG (k := 0x124) (by decide))
    (by rw [e154, WP]; exact env.stack_code 0x154 8 (by omega) 0x756 _ (by decide))
  rw [mem1] at mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2, fun r q1 q2 q3 q4 q5 => ?_⟩
  rw [fr2 r q1 q2 q3 q4, r1 r q5]

/-- `image::parse`'s call to `memcpy` that copies the 256-byte segment array
at `G + 0x24` to `out`. -/
theorem ip_memcpy {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word}
    (s : St Mx P m off f) (code : ICode Mx P)
    (h1 : fetchRel imageParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel imageParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xB5E6)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : f a0 = out) (ha1 : f a1 = G + 0x24) (ha2 : f a2 = 0x100) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧
      m'.mem = copyWords Mx out (G + 0x24) 64 ∧ reg m' a0 = out ∧
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 → r ≠ ra →
        reg m' r = f r) := by
  obtain ⟨-, -, -, -, -, e54, -⟩ := env.r_eqs
  have hev : (P + 0xB5E6).toNat % 2 = 0 := even_at P env.hP 0xB5E6 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := ip_reg1 regs1 s.zero
  have WB : P + 0xB5E6 + 8 = ipWindow P + BitVec.ofNat 32 0xB8C0 := by
    rw [BitVec.add_assoc]; exact ip_wq P _ 0xB8C0 (by decide)
  have O0 : out = out + BitVec.ofNat 32 0 := (add_ofNat_zero out).symm
  obtain ⟨m2, c2, pc2, mem2, a02, fr2⟩ := memcpy_aligned m1 (P + 0xB5E6)
    (P + BitVec.ofNat 32 (off + 8)) out (G + 0x24) 64
    (fun i hi => by rw [mem1]; exact code.stub i hi)
    (fun i hi => by rw [mem1, show P + 0xB5E6 + 8 = P + 0xB5EE by rw [BitVec.add_assoc]; rfl]
                    exact code.body i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]; rfl) (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by decide) (by have := env.hwrap; omega) (by decide) env.hout
    (aligned_add env.hG (k := 0x24) (by decide))
    (by rw [e54]; exact env.hOS.sub (c := 0) (l := 256) (by omega) |>.subR (c := 0x54) (l := 256) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h)
    (by rw [WB, O0]; exact env.hOW.sub (c := 0) (l := 256) (by omega) |>.subR (c := 0xB8C0) (l := _)
          (by decide))
  rw [mem1] at mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2, a02,
    fun r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 => ?_⟩
  rw [fr2 r q1 q2 q3 q4 q5 q6 q7 q8 q9, r1 r q10]

end C3.RV32.Cur
