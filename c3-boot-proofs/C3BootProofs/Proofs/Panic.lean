import C3BootProofs.Proofs.Parse
import C3BootProofs.Image.BootloaderData6

/-!
# Panics, as compiled

Every Rust panic in the image ends in `c3_bootloader::halt`: the panic
entry points push a frame and call `core::panicking::panic_fmt`, which calls
`rust_begin_unwind`, which calls `halt(0xEF)`. `halt` calls the ROM's
`printf` with its return address at a `pause; j .-4` loop.

`Panics m` says the machine reaches that ROM call with the return address at
the loop and the panic code intact. `haltLoop_stays` says that once at the
loop, the machine never leaves it and changes neither memory nor registers.
The ROM's `printf` is outside the image; these theorems don't say it
returns, only that if it returns, nothing after it runs but the loop. So no
panic returns to its caller.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem hlt_at_0 : fetchRel haltCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem hlt_at_e : fetchRel haltCode 0xE = some (.auipc ra 0xFFC49000, 4) := by decide
theorem hlt_at_12 : fetchRel haltCode 0x12 = some (.jalr ra ra 0x3EC, 4) := by decide
theorem hlt_at_16 : fetchRel haltCode 0x16 = some (.fence, 4) := by decide
theorem hlt_at_1a : fetchRel haltCode 0x1A = some (.jal x0 0xFFFFFFFC, 2) := by decide
theorem unw_at_0 : fetchRel beginUnwindCode 0x0 = some (.aluImm .add a0 x0 0xEF, 4) := by decide
theorem unw_at_4 : fetchRel beginUnwindCode 0x4 = some (.auipc ra 0x0, 4) := by decide
theorem unw_at_8 : fetchRel beginUnwindCode 0x8 = some (.jalr ra ra 0x2B0, 4) := by decide
theorem pfm_at_8 : fetchRel panicFmtCode 0x8 = some (.auipc ra 0x7000, 4) := by decide
theorem pfm_at_c : fetchRel panicFmtCode 0xC = some (.jalr ra ra 0x7BE, 4) := by decide
theorem afi_at_8 : fetchRel assertFailedInnerCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem afi_at_c : fetchRel assertFailedInnerCode 0xC = some (.jalr ra ra 0x8, 4) := by decide
theorem cpn_at_8 : fetchRel corePanicCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem cpn_at_c : fetchRel corePanicCode 0xC = some (.jalr ra ra 0xFFFFFFBE, 4) := by decide
theorem pbc_at_8 : fetchRel panicBoundsCheckCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem pbc_at_c : fetchRel panicBoundsCheckCode 0xC = some (.jalr ra ra 0xFFFFFFAE, 4) := by decide
theorem exf_at_8 : fetchRel expectFailedCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem exf_at_c : fetchRel expectFailedCode 0xC = some (.jalr ra ra 0xFFFFFF9E, 4) := by decide
theorem uwf_at_8 : fetchRel unwrapFailedCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem uwf_at_c : fetchRel unwrapFailedCode 0xC = some (.jalr ra ra 0xFFFFFF8E, 4) := by decide
theorem lmf_at_8 : fetchRel lenMismatchFailCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem lmf_at_c : fetchRel lenMismatchFailCode 0xC = some (.jalr ra ra 0xFFFFFF7E, 4) := by decide
theorem sif_at_8 : fetchRel sliceIndexFailCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem sif_at_c : fetchRel sliceIndexFailCode 0xC = some (.jalr ra ra 0xFFFFFFCE, 4) := by decide
theorem afz_at_12 : fetchRel assertFailedUsizeCode 0x12 = some (.auipc ra 0x0, 4) := by decide
theorem afz_at_16 : fetchRel assertFailedUsizeCode 0x16 = some (.jalr ra ra 0xFFFFFFCE, 4) := by decide
theorem afb_at_0 : fetchRel assertFailedU8Code 0x0 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem afb_at_2 : fetchRel assertFailedU8Code 0x2 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem afb_at_6 : fetchRel assertFailedU8Code 0x6 = some (.jalr ra ra 0xFFFFFA22, 4) := by decide
theorem exu_at_0 : fetchRel expectUsizeCode 0x0 = some (.load .lbu a1 a0 0x0, 4) := by decide
theorem exu_at_4 : fetchRel expectUsizeCode 0x4 = some (.branch .bne a1 x0 0x6, 2) := by decide
theorem exu_at_6 : fetchRel expectUsizeCode 0x6 = some (.load .lw a0 a0 0x4, 2) := by decide
theorem exu_at_8 : fetchRel expectUsizeCode 0x8 = some (.jalr x0 ra 0x0, 2) := by decide
theorem exu_at_a : fetchRel expectUsizeCode 0xA = some (.aluImm .add a0 x0 0x8, 2) := by decide
theorem exu_at_c : fetchRel expectUsizeCode 0xC = some (.auipc ra 0xC000, 4) := by decide
theorem exu_at_10 : fetchRel expectUsizeCode 0x10 = some (.jalr ra ra 0x5D2, 4) := by decide
theorem ext_at_0 : fetchRel expectTagCode 0x0 = some (.load .lw a1 a0 0x0, 2) := by decide
theorem ext_at_2 : fetchRel expectTagCode 0x2 = some (.aluImm .add a2 x0 0xFFFFFFFF, 2) := by decide
theorem ext_at_4 : fetchRel expectTagCode 0x4 = some (.branch .bne a1 a2 0xA, 4) := by decide
theorem ext_at_8 : fetchRel expectTagCode 0x8 = some (.load .lbu a0 a0 0x4, 4) := by decide
theorem ext_at_c : fetchRel expectTagCode 0xC = some (.jalr x0 ra 0x0, 2) := by decide
theorem ext_at_e : fetchRel expectTagCode 0xE = some (.aluImm .add a0 x0 0xB, 2) := by decide
theorem ext_at_10 : fetchRel expectTagCode 0x10 = some (.auipc ra 0xA000, 4) := by decide
theorem ext_at_14 : fetchRel expectTagCode 0x14 = some (.jalr ra ra 0xFFFFFEAA, 4) := by decide

def pushFrame : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sw sp ra 0xC, .sw sp (8 : Fin 32) 0x8, .aluImm .add (8 : Fin 32) sp 0x10]

def hltA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sw sp ra 0xC, .alu .add a1 x0 a0, .lui a0 0x3FCC6000, .aluImm .add a0 a0 0x6AE]

def afzA : List BInstr := pushFrame ++ [.alu .add a1 x0 a2, .lui a0 (img% hi20 (svRekorLeafAddress + 0x1)), .aluImm .add a0 a0 (img% lo12 (svRekorLeafAddress + 0x1))]

theorem hltA_end : blockEnd haltCode 0 hltA = some 0xE := by decide
theorem pfm_end : blockEnd panicFmtCode 0 pushFrame = some 8 := by decide
theorem afi_end : blockEnd assertFailedInnerCode 0 pushFrame = some 8 := by decide
theorem cpn_end : blockEnd corePanicCode 0 pushFrame = some 8 := by decide
theorem pbc_end : blockEnd panicBoundsCheckCode 0 pushFrame = some 8 := by decide
theorem exf_end : blockEnd expectFailedCode 0 pushFrame = some 8 := by decide
theorem uwf_end : blockEnd unwrapFailedCode 0 pushFrame = some 8 := by decide
theorem lmf_end : blockEnd lenMismatchFailCode 0 pushFrame = some 8 := by decide
theorem sif_end : blockEnd sliceIndexFailCode 0 pushFrame = some 8 := by decide
theorem afz_end : blockEnd assertFailedUsizeCode 0 afzA = some 0x12 := by decide
end

/-- The image's panic code: `halt`, `rust_begin_unwind`, and the panic
entry points, with their load addresses. -/
def panicFns : List (Nat × List Nat) :=
  [(haltAddress, haltCode), (beginUnwindAddress, beginUnwindCode), (panicFmtAddress, panicFmtCode),
    (assertFailedInnerAddress, assertFailedInnerCode), (corePanicAddress, corePanicCode),
    (panicBoundsCheckAddress, panicBoundsCheckCode), (expectFailedAddress, expectFailedCode),
    (unwrapFailedAddress, unwrapFailedCode), (lenMismatchFailAddress, lenMismatchFailCode),
    (sliceIndexFailAddress, sliceIndexFailCode), (assertFailedUsizeAddress, assertFailedUsizeCode),
    (assertFailedU8Address, assertFailedU8Code)]

/-- `M` holds the panic code where the image loads it. -/
def PanicCode (M : Word → BitVec 8) : Prop := ∀ p ∈ panicFns, CodeIn M (BitVec.ofNat 32 p.1) p.2

/-- The end of the ESP32-C3's data RAM, below every address the panic code
loads at. -/
def dramEnd : Nat := 0x3FCE0000

theorem panicFns_hi : ∀ p ∈ panicFns, dramEnd ≤ p.1 ∧ p.1 + p.2.length < 2 ^ 32 := by decide

theorem PanicCode.code {M : Word → BitVec 8} (h : PanicCode M) {a : Nat} {code : List Nat}
    (hm : (a, code) ∈ panicFns) : CodeIn M (BitVec.ofNat 32 a) code := h _ hm

theorem PanicCode.store32 {M : Word → BitVec 8} {a v : Word} (h : PanicCode M) (ha : a.toNat + 4 ≤ dramEnd) :
    PanicCode (memStore32 M a v) := fun p hp => by
  have hb := panicFns_hi p hp
  refine (h p hp).store32 (sep_of_le ?_ ?_) <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] <;> omega

theorem PanicCode.store8 {M : Word → BitVec 8} {a : Word} {v : BitVec 8} (h : PanicCode M)
    (ha : a.toNat + 1 ≤ dramEnd) : PanicCode (memStore8 M a v) := fun p hp => by
  have hb := panicFns_hi p hp
  refine (h p hp).store8 (sep_of_le ?_ ?_) <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] <;> omega

/-- `sp` is word-aligned in data RAM, with `k` bytes of data RAM below it. -/
def Room (sp : Word) (k : Nat) : Prop := sp.toNat % 4 = 0 ∧ 0x3FC80000 + k ≤ sp.toNat ∧ sp.toNat ≤ dramEnd

theorem Room.frame {S : Word} {k : Nat} (h : Room S (k + 16)) : Room (S + 0xFFFFFFF0) k := by
  obtain ⟨h0, h1, h2⟩ := h
  have e : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl]; unfold dramEnd at h2; omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [e] <;> unfold dramEnd at * <;> omega

theorem Room.slot {S : Word} {k : Nat} (h : Room S k) {o : Nat} (hk : 16 ≤ k) (ho : o + 4 ≤ 16) :
    (S + 0xFFFFFFF0 + BitVec.ofNat 32 o).toNat + 4 ≤ dramEnd := by
  obtain ⟨_, h1, h2⟩ := h
  unfold dramEnd at h2 ⊢
  rw [BitVec.toNat_add, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl,
    BitVec.toNat_ofNat]
  omega

theorem Room.sep {S B : Word} {k l : Nat} (h : Room S k) {o : Nat} (hk : 16 ≤ k) (ho : o + 4 ≤ 16)
    (hB : dramEnd ≤ B.toNat) (hBl : B.toNat + l ≤ 2 ^ 32) : Sep (S + 0xFFFFFFF0 + BitVec.ofNat 32 o) 4 B l :=
  sep_of_le (by have := h.slot hk ho; omega) hBl

def haltBase : Word := BitVec.ofNat 32 haltAddress

/-- The ROM's `printf`, which `halt` calls. -/
def romPrintfEntry : Word := 0x40000040

/-- The machine is entering the ROM's `printf` from `halt`, so that it
returns into the loop at `halt + 0x16`, with the panic code in memory. -/
def Halting (m : Machine) : Prop := m.pc = romPrintfEntry ∧ reg m ra = haltBase + 0x16 ∧ PanicCode m.mem

/-- From `m`, the machine reaches the ROM call in `halt`. -/
def Panics (m : Machine) : Prop := ∃ m', Steps m m' ∧ Halting m'

theorem Panics.of_steps {m m' : Machine} (h : Steps m m') (hp : Panics m') : Panics m :=
  let ⟨m'', h', hh⟩ := hp; ⟨m'', h.trans h', hh⟩

section Step

variable {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine} {off : Nat}
  {f : Fin 32 → Word}

theorem St.fence (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {len : Word} {off' : Nat} (hf : fetchRel code off = some (.fence, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧ St M base m1 off' f := by
  refine ⟨Arch.setPc m (m.pc + len), ?_, ?_, by simp [s.mem], fun r => by simp only [reg_setPc, s.regs]⟩
  · rw [step_code (s.codeAt hc) s.pc hf]; rfl
  · simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hn]

end Step

theorem haltCode_in {M : Word → BitVec 8} (h : PanicCode M) : CodeIn M haltBase haltCode :=
  h.code (by decide)

/-- **The loop after the ROM call in `halt` never exits**: from either of
its two instructions, every run stays on them, with memory and registers
unchanged. -/
theorem haltLoop_stays {m : Machine} (hc : CodeIn m.mem haltBase haltCode)
    (hpc : m.pc = haltBase + 0x16 ∨ m.pc = haltBase + 0x1A) {m' : Machine} (h : Steps m m') :
    (m'.pc = haltBase + 0x16 ∨ m'.pc = haltBase + 0x1A) ∧ m'.mem = m.mem ∧ ∀ r, reg m' r = reg m r := by
  induction h with
  | refl => exact ⟨hpc, rfl, fun _ => rfl⟩
  | @cons s s1 s2 e _ ih =>
    have st : St s.mem haltBase s (if s.pc = haltBase + 0x16 then 0x16 else 0x1A) (reg s) := by
      refine ⟨?_, rfl, fun _ => rfl⟩
      rcases hpc with h | h
      · rw [ite_eq_left h, h]; rfl
      · have : s.pc ≠ haltBase + 0x16 := by rw [h]; decide
        rw [ite_eq_right this, h]; rfl
    obtain ⟨n, en, sn⟩ : ∃ n, step s = some n ∧ St s.mem haltBase n
        (if s.pc = haltBase + 0x16 then 0x1A else 0x16) (reg s) := by
      by_cases hp : s.pc = haltBase + 0x16
      · rw [ite_eq_left hp] at st ⊢; exact st.fence hc hlt_at_16 (by decide)
      · rw [ite_eq_right hp] at st ⊢
        refine st.jump hc hlt_at_1a (by decide) ?_
        rw [st.pc, BitVec.add_assoc]; exact even_bit0 (by decide)
    rw [en, Option.some.injEq] at e
    subst e
    have hpc1 : n.pc = haltBase + 0x16 ∨ n.pc = haltBase + 0x1A := by
      rw [sn.pc]; by_cases hp : s.pc = haltBase + 0x16
      · rw [ite_eq_left hp]; exact .inr rfl
      · rw [ite_eq_right hp]; exact .inl rfl
    obtain ⟨p2, m2, r2⟩ := ih (by rw [sn.mem]; exact hc) hpc1
    exact ⟨p2, by rw [m2, sn.mem], fun r => by rw [r2, sn.regs]⟩

set_option maxRecDepth 20000 in
/-- **`halt`** stores its return address in a 16-byte frame and calls the
ROM's `printf`. -/
theorem halt_panics (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = haltBase)
    (hR : Room (reg m sp) 16) : Panics m := by
  have hc := haltCode_in hP
  have st0 : St m.mem haltBase m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR
  obtain ⟨mA, cA, uA⟩ := St.block hltA st0 hc hltA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, hltA, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hS]
    repeat' apply And.intro
    all_goals first | exact True.intro | (refine aligned_add (aligned_add hR.1 ?_) ?_ <;> decide) |
      exact hR.sep (o := 0xC) (by decide) (by decide) (by decide) (by decide))
  simp only [runBlock, BInstr.run, hltA] at uA
  have hPA : PanicCode mA.mem := by
    rw [uA.mem]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS]
    exact hP.store32 (hR.slot (o := 0xC) (by decide) (by decide))
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := uA.self.callRa (by rw [← uA.mem]; exact haltCode_in hPA) hlt_at_e hlt_at_12
    (cb := romPrintfEntry) (by decide) (by decide)
  refine ⟨n1, cA.trans c1, pc1, ?_, by rw [mem1, ← uA.mem]; exact hPA⟩
  rw [regs1]; simp +decide only [upd_app, ↓reduceIte]

theorem unwindCode_in {M : Word → BitVec 8} (h : PanicCode M) :
    CodeIn M (BitVec.ofNat 32 beginUnwindAddress) beginUnwindCode := h.code (by decide)

/-- **`rust_begin_unwind`** calls `halt(0xEF)`. -/
theorem beginUnwind_panics (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = BitVec.ofNat 32 beginUnwindAddress)
    (hR : Room (reg m sp) 16) : Panics m := by
  have hc := unwindCode_in hP
  have st0 : St m.mem (BitVec.ofNat 32 beginUnwindAddress) m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨m1, e1, s1⟩ := st0.aluImm hc unw_at_0 (off' := 4) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s1.self.callRa hc unw_at_4 unw_at_8 (cb := haltBase) (by decide)
    (by decide)
  refine Panics.of_steps (.cons e1 c1) (halt_panics n1 (by rw [mem1]; exact hP) pc1 ?_)
  rw [regs1, upd_ne (by decide) (by decide), s1.regs]
  simp +decide only [upd_app, ↓reduceIte]; exact hR

/-- The shape of most panic entry points: push a 16-byte frame, saving `ra`
and `s0`, and call `T`. If `T` panics with 16 fewer bytes of stack, so does
the entry point. -/
theorem frame_panics {m : Machine} {B T imm o : Word} {code : List Nat} {k : Nat}
    (hcB : ∀ M, PanicCode M → CodeIn M B code) (hP : PanicCode m.mem) (hpc : m.pc = B)
    (hB : dramEnd ≤ B.toNat) (hBl : B.toNat + code.length ≤ 2 ^ 32) (hR : Room (reg m sp) (k + 16))
    (he : blockEnd code 0 pushFrame = some 8)
    (h1 : fetchRel code 8 = some (.auipc ra imm, 4)) (h2 : fetchRel code (8 + 4) = some (.jalr ra ra o, 4))
    (hT : B + BitVec.ofNat 32 8 + imm + o = T) (hTe : T.toNat % 2 = 0)
    (hTp : ∀ m', m'.pc = T → PanicCode m'.mem → Room (reg m' sp) k → Panics m') : Panics m := by
  have hc := hcB _ hP
  have st0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR
  have h16 : 16 ≤ k + 16 := by omega
  have sC : Sep (S + 0xFFFFFFF0 + 0xC) 4 B code.length := hR.sep (o := 0xC) h16 (by decide) hB hBl
  have s8 : Sep (S + 0xFFFFFFF0 + 0x8) 4 B code.length := hR.sep (o := 0x8) h16 (by decide) hB hBl
  have aC : (S + 0xFFFFFFF0 + 0xC).toNat % 4 = 0 := aligned_add (aligned_add hR.1 (k := 0xFFFFFFF0) (by decide)) (k := 0xC) (by decide)
  have a8 : (S + 0xFFFFFFF0 + 0x8).toNat % 4 = 0 := aligned_add (aligned_add hR.1 (k := 0xFFFFFFF0) (by decide)) (k := 0x8) (by decide)
  obtain ⟨mA, cA, uA⟩ := St.block pushFrame st0 hc he (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, pushFrame, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hS]
    exact ⟨True.intro, ⟨aC, sC⟩, a8, s8⟩)
  simp only [runBlock, BInstr.run, pushFrame] at uA
  have hPA : PanicCode mA.mem := by
    rw [uA.mem]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS]
    exact (hP.store32 (hR.slot (o := 0xC) h16 (by decide))).store32 (hR.slot (o := 0x8) h16 (by decide))
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := uA.self.callRa (by rw [← uA.mem]; exact hcB _ hPA) h1 h2 hT hTe
  refine Panics.of_steps (cA.trans c1) (hTp n1 pc1 (by rw [mem1, ← uA.mem]; exact hPA) ?_)
  rw [regs1, upd_ne (by decide) (by decide), uA.regs]
  simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS]; exact hR.frame

/-- **`core::panicking::panic_fmt`** calls `rust_begin_unwind`. -/
theorem panicFmt_panics (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = BitVec.ofNat 32 panicFmtAddress)
    (hR : Room (reg m sp) 32) : Panics m :=
  frame_panics (k := 16) (fun _ h => h.code (by decide)) hP hpc (by decide) (by decide) hR pfm_end pfm_at_8 pfm_at_c
    (by decide) (by decide) fun m' hp hP' hR' => beginUnwind_panics m' hP' hp hR'

/-- Each of these panic entry points pushes a frame and calls `panic_fmt`. -/
theorem viaFmt_panics {m : Machine} {a : Nat} {code : List Nat} {imm o : Word} (hm : (a, code) ∈ panicFns)
    (hP : PanicCode m.mem) (hpc : m.pc = BitVec.ofNat 32 a) (hR : Room (reg m sp) 48)
    (ha : dramEnd ≤ a ∧ a + code.length < 2 ^ 32) (he : blockEnd code 0 pushFrame = some 8)
    (h1 : fetchRel code 8 = some (.auipc ra imm, 4)) (h2 : fetchRel code (8 + 4) = some (.jalr ra ra o, 4))
    (hT : BitVec.ofNat 32 a + BitVec.ofNat 32 8 + imm + o = BitVec.ofNat 32 panicFmtAddress) : Panics m := by
  have hn : (BitVec.ofNat 32 a).toNat = a := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  exact frame_panics (k := 32) (fun _ h => h.code hm) hP hpc (by rw [hn]; exact ha.1) (by rw [hn]; omega) hR he h1 h2
    hT (by decide) fun m' hp hP' hR' => panicFmt_panics m' hP' hp hR'

/-- **`core::panicking::assert_failed_inner`** panics. -/
theorem assertFailedInner_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 assertFailedInnerAddress) (hR : Room (reg m sp) 48) : Panics m :=
  viaFmt_panics (by decide) hP hpc hR (by decide) afi_end afi_at_8 afi_at_c (by decide)

/-- **`core::panicking::panic`** panics. -/
theorem corePanic_panics (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = BitVec.ofNat 32 corePanicAddress)
    (hR : Room (reg m sp) 48) : Panics m :=
  viaFmt_panics (by decide) hP hpc hR (by decide) cpn_end cpn_at_8 cpn_at_c (by decide)

/-- **`core::panicking::panic_bounds_check`** panics. -/
theorem panicBoundsCheck_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 panicBoundsCheckAddress) (hR : Room (reg m sp) 48) : Panics m :=
  viaFmt_panics (by decide) hP hpc hR (by decide) pbc_end pbc_at_8 pbc_at_c (by decide)

/-- **`core::option::expect_failed`** panics. -/
theorem expectFailed_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 expectFailedAddress) (hR : Room (reg m sp) 48) : Panics m :=
  viaFmt_panics (by decide) hP hpc hR (by decide) exf_end exf_at_8 exf_at_c (by decide)

/-- **`core::result::unwrap_failed`** panics. -/
theorem unwrapFailed_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 unwrapFailedAddress) (hR : Room (reg m sp) 48) : Panics m :=
  viaFmt_panics (by decide) hP hpc hR (by decide) uwf_end uwf_at_8 uwf_at_c (by decide)

/-- **`core::slice::copy_from_slice_impl::len_mismatch_fail`** panics. -/
theorem lenMismatchFail_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 lenMismatchFailAddress) (hR : Room (reg m sp) 48) : Panics m :=
  viaFmt_panics (by decide) hP hpc hR (by decide) lmf_end lmf_at_8 lmf_at_c (by decide)

/-- **`core::slice::index::slice_index_fail`** panics. -/
theorem sliceIndexFail_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 sliceIndexFailAddress) (hR : Room (reg m sp) 48) : Panics m :=
  viaFmt_panics (by decide) hP hpc hR (by decide) sif_end sif_at_8 sif_at_c (by decide)

set_option maxRecDepth 20000 in
/-- **`core::panicking::assert_failed::<usize, usize>`** pushes a frame, sets
up `assert_failed_inner`'s arguments, and calls it. -/
theorem assertFailedUsize_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 assertFailedUsizeAddress) (hR : Room (reg m sp) 64) : Panics m := by
  have hc : ∀ M, PanicCode M → CodeIn M (BitVec.ofNat 32 assertFailedUsizeAddress) assertFailedUsizeCode :=
    fun _ h => h.code (by decide)
  have st0 : St m.mem (BitVec.ofNat 32 assertFailedUsizeAddress) m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR
  have h16 : 16 ≤ 48 + 16 := by omega
  have sC : Sep (S + 0xFFFFFFF0 + 0xC) 4 (BitVec.ofNat 32 assertFailedUsizeAddress) assertFailedUsizeCode.length :=
    hR.sep (o := 0xC) h16 (by decide) (by decide) (by decide)
  have s8 : Sep (S + 0xFFFFFFF0 + 0x8) 4 (BitVec.ofNat 32 assertFailedUsizeAddress) assertFailedUsizeCode.length :=
    hR.sep (o := 0x8) h16 (by decide) (by decide) (by decide)
  have aC : (S + 0xFFFFFFF0 + 0xC).toNat % 4 = 0 := aligned_add (aligned_add hR.1 (k := 0xFFFFFFF0) (by decide)) (k := 0xC) (by decide)
  have a8 : (S + 0xFFFFFFF0 + 0x8).toNat % 4 = 0 := aligned_add (aligned_add hR.1 (k := 0xFFFFFFF0) (by decide)) (k := 0x8) (by decide)
  obtain ⟨mA, cA, uA⟩ := St.block afzA st0 (hc _ hP) afz_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, afzA, pushFrame, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte, and_true]
    simp only [ev_add]; rw [hS]
    exact ⟨True.intro, ⟨aC, sC⟩, a8, s8⟩)
  simp only [runBlock, BInstr.run, afzA, pushFrame, List.cons_append, List.nil_append] at uA
  have hPA : PanicCode mA.mem := by
    rw [uA.mem]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS]
    exact (hP.store32 (hR.slot (o := 0xC) h16 (by decide))).store32 (hR.slot (o := 0x8) h16 (by decide))
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := uA.self.callRa (by rw [← uA.mem]; exact hc _ hPA) afz_at_12 afz_at_16
    (cb := BitVec.ofNat 32 assertFailedInnerAddress) (by decide) (by decide)
  refine Panics.of_steps (cA.trans c1) (assertFailedInner_panics n1 (by rw [mem1, ← uA.mem]; exact hPA) pc1 ?_)
  rw [regs1, upd_ne (by decide) (by decide), uA.regs]
  simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS]; exact hR.frame

/-- **`core::panicking::assert_failed::<u8, u8>`** calls
`assert_failed_inner` with no frame of its own. -/
theorem assertFailedU8_panics (m : Machine) (hP : PanicCode m.mem)
    (hpc : m.pc = BitVec.ofNat 32 assertFailedU8Address) (hR : Room (reg m sp) 48) : Panics m := by
  have hc : CodeIn m.mem (BitVec.ofNat 32 assertFailedU8Address) assertFailedU8Code := hP.code (by decide)
  have st0 : St m.mem (BitVec.ofNat 32 assertFailedU8Address) m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨m1, e1, s1⟩ := st0.aluImm hc afb_at_0 (off' := 2) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s1.self.callRa hc afb_at_2 afb_at_6
    (cb := BitVec.ofNat 32 assertFailedInnerAddress) (by decide) (by decide)
  refine Panics.of_steps (.cons e1 c1) (assertFailedInner_panics n1 (by rw [mem1]; exact hP) pc1 ?_)
  rw [regs1, upd_ne (by decide) (by decide), s1.regs]
  simp +decide only [upd_app, ↓reduceIte]; exact hR

theorem pn_bne_zext0 : ∀ b : BitVec 8, branchTaken .bne (b.zeroExtend 32) 0 = !decide (b = 0) := by decide

/-- **`Result<usize, TryFromIntError>::expect`** on the result at `p`:
with tag byte 0 it returns the `usize` at `p + 4`; otherwise it panics. -/
theorem expectUsize_correct (m : Machine) {p retAddr : Word} (hP : PanicCode m.mem)
    (hc : CodeIn m.mem (BitVec.ofNat 32 expectUsizeAddress) expectUsizeCode)
    (hpc : m.pc = BitVec.ofNat 32 expectUsizeAddress) (ha0 : reg m a0 = p) (hp : p.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hR : Room (reg m sp) 48) :
    (m.mem p = 0 → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = memLoad32 m.mem (p + 4) ∧ m'.mem = m.mem ∧
      ∀ q, q ≠ a0 → q ≠ a1 → reg m' q = reg m q) ∧
    (m.mem p ≠ 0 → Panics m) := by
  have st0 : St m.mem (BitVec.ofNat 32 expectUsizeAddress) m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, e1, s1⟩ := st0.lbu hc exu_at_0 (off' := 4) (by decide)
  have A1 : upd (reg m) a1 ((m.mem (reg m a0 + 0x0)).zeroExtend 32) a1 = (m.mem p).zeroExtend 32 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ha0, add_lit_zero]
  have Z : upd (reg m) a1 ((m.mem (reg m a0 + 0x0)).zeroExtend 32) 0 = 0 := rfl
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨m2, e2, s2⟩ := s1.notTaken hc 6 exu_at_4 (by decide) (by rw [A1, Z, pn_bne_zext0, h0]; rfl)
    obtain ⟨m3, e3, s3⟩ := s2.lw hc exu_at_6 (off' := 8) (by decide) (by
      rw [updz hz (by decide), ha0]; exact aligned_add hp (by decide))
    obtain ⟨m4, e4, pc4, mem4, regs4⟩ := s3.jalr hc exu_at_8
    refine ⟨m4, .cons e1 (.cons e2 (.cons e3 (.single e4))), ?_, ?_, mem4, fun q h1 h2 => ?_⟩
    · rw [pc4]; simp +decide only [upd_app, ↓reduceIte]; rw [hra, add_lit_zero, hret]
    · rw [regs4]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]
    · rw [regs4, updz (by rfl) h1, updz hz h2]
  · obtain ⟨m2, e2, s2⟩ := s1.taken hc 0xA exu_at_4 (by decide) (by rw [A1, Z, pn_bne_zext0, decide_eq_false h0]; rfl)
    obtain ⟨m3, e3, s3⟩ := s2.aluImm hc exu_at_a (off' := 0xC) (by decide)
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s3.self.callRa hc exu_at_c exu_at_10
      (cb := BitVec.ofNat 32 unwrapFailedAddress) (by decide) (by decide)
    refine Panics.of_steps (.cons e1 (.cons e2 (.cons e3 c1)))
      (unwrapFailed_panics n1 (by rw [mem1]; exact hP) pc1 ?_)
    rw [regs1, upd_ne (by decide) (by decide), s3.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact hR

/-- **`Result<Tag, sec1::Error>::expect`** on the result at `p`: when the
word at `p` is 0xFFFFFFFF (`Ok`), it returns the tag byte at `p + 4`;
otherwise it panics. -/
theorem expectTag_correct (m : Machine) {p retAddr : Word} (hP : PanicCode m.mem)
    (hc : CodeIn m.mem (BitVec.ofNat 32 expectTagAddress) expectTagCode)
    (hpc : m.pc = BitVec.ofNat 32 expectTagAddress) (ha0 : reg m a0 = p) (hp : p.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hR : Room (reg m sp) 48) :
    (memLoad32 m.mem p = 0xFFFFFFFF → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (m.mem (p + 4)).zeroExtend 32 ∧ m'.mem = m.mem ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m' q = reg m q) ∧
    (memLoad32 m.mem p ≠ 0xFFFFFFFF → Panics m) := by
  have st0 : St m.mem (BitVec.ofNat 32 expectTagAddress) m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, e1, s1⟩ := st0.lw hc ext_at_0 (off' := 2) (by decide) (by rw [ha0, add_lit_zero]; exact hp)
  obtain ⟨m2, e2, s2⟩ := s1.aluImm hc ext_at_2 (off' := 4) (by decide)
  have B : ∀ b : Bool, (memLoad32 m.mem p = 0xFFFFFFFF ↔ b = false) →
      branchTaken .bne (upd (upd (reg m) a1 (memLoad32 m.mem (reg m a0 + 0x0))) a2
        (aluEval .add (upd (reg m) a1 (memLoad32 m.mem (reg m a0 + 0x0)) x0) 0xFFFFFFFF) a1)
        (upd (upd (reg m) a1 (memLoad32 m.mem (reg m a0 + 0x0))) a2
        (aluEval .add (upd (reg m) a1 (memLoad32 m.mem (reg m a0 + 0x0)) x0) 0xFFFFFFFF) a2) = b := by
    intro b hb
    simp +decide only [upd_app, ↓reduceIte]; rw [ha0, add_lit_zero]
    rw [show aluEval .add (0 : Word) 0xFFFFFFFF = 0xFFFFFFFF from rfl]
    show (memLoad32 m.mem p != 0xFFFFFFFF) = b
    cases b
    · rw [hb.mpr rfl]; rfl
    · have : memLoad32 m.mem p ≠ 0xFFFFFFFF := fun h => by simpa using hb.mp h
      simpa using this
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨m3, e3, s3⟩ := s2.notTaken hc 8 ext_at_4 (by decide) (B false ⟨fun _ => rfl, fun _ => h0⟩)
    obtain ⟨m4, e4, s4⟩ := s3.lbu hc ext_at_8 (off' := 0xC) (by decide)
    obtain ⟨m5, e5, pc5, mem5, regs5⟩ := s4.jalr hc ext_at_c
    refine ⟨m5, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.single e5)))), ?_, ?_, mem5, fun q h1 h2 h3 => ?_⟩
    · rw [pc5]; simp +decide only [upd_app, ↓reduceIte]; rw [hra, add_lit_zero, hret]
    · rw [regs5]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]
    · rw [regs5, updz (by rfl) h1, updz (by rfl) h3, updz hz h2]
  · obtain ⟨m3, e3, s3⟩ := s2.taken hc 0xE ext_at_4 (by decide) (B true ⟨fun h => absurd h h0, fun h => nomatch h⟩)
    obtain ⟨m4, e4, s4⟩ := s3.aluImm hc ext_at_e (off' := 0x10) (by decide)
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s4.self.callRa hc ext_at_10 ext_at_14
      (cb := BitVec.ofNat 32 unwrapFailedAddress) (by decide) (by decide)
    refine Panics.of_steps (.cons e1 (.cons e2 (.cons e3 (.cons e4 c1))))
      (unwrapFailed_panics n1 (by rw [mem1]; exact hP) pc1 ?_)
    rw [regs1, upd_ne (by decide) (by decide), s4.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact hR

end C3.RV32
