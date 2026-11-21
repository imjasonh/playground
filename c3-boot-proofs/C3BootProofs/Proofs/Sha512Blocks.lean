import C3BootProofs.Proofs.Sha512Compress
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.Sha2Update

/-!
# SHA-512's block helpers, as compiled

`Sha512VarCore::finalize_variable_core` compresses its last blocks through a
closure that copies one 128-byte block to the stack and calls `compress512`
on it. `Sha512::update` compresses whole blocks through another closure,
which adds the block count to the 128-bit count after the state and tail
calls `compress512`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fb5_at_0 : fetchRel sha512FinBlockCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF70, 2) := by decide
theorem fb5_at_2 : fetchRel sha512FinBlockCode 0x2 = some (.store .sw sp ra 0x8C, 2) := by decide
theorem fb5_at_4 : fetchRel sha512FinBlockCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x88, 2) := by decide
theorem fb5_at_6 : fetchRel sha512FinBlockCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fb5_at_8 : fetchRel sha512FinBlockCode 0x8 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem fb5_at_a : fetchRel sha512FinBlockCode 0xA = some (.aluImm .add a2 x0 0x80, 4) := by decide
theorem fb5_at_e : fetchRel sha512FinBlockCode 0xE = some (.auipc ra 0x4000, 4) := by decide
theorem fb5_at_12 : fetchRel sha512FinBlockCode 0x12 = some (.jalr ra ra 0xFFFFFDEC, 4) := by decide
theorem fb5_at_16 : fetchRel sha512FinBlockCode 0x16 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem fb5_at_18 : fetchRel sha512FinBlockCode 0x18 = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem fb5_at_1a : fetchRel sha512FinBlockCode 0x1A = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem fb5_at_1c : fetchRel sha512FinBlockCode 0x1C = some (.auipc ra 0x4000, 4) := by decide
theorem fb5_at_20 : fetchRel sha512FinBlockCode 0x20 = some (.jalr ra ra 0xFFFFF832, 4) := by decide
theorem fb5_at_24 : fetchRel sha512FinBlockCode 0x24 = some (.load .lw ra sp 0x8C, 2) := by decide
theorem fb5_at_26 : fetchRel sha512FinBlockCode 0x26 = some (.load .lw (8 : Fin 32) sp 0x88, 2) := by decide
theorem fb5_at_28 : fetchRel sha512FinBlockCode 0x28 = some (.aluImm .add sp sp 0x90, 2) := by decide
theorem fb5_at_2a : fetchRel sha512FinBlockCode 0x2A = some (.jalr x0 ra 0x0, 2) := by decide
theorem ub5_at_0 : fetchRel sha384UpdateBlocksCode 0x0 = some (.load .lw a3 a0 0x40, 2) := by decide
theorem ub5_at_2 : fetchRel sha384UpdateBlocksCode 0x2 = some (.load .lw a4 a0 0x44, 2) := by decide
theorem ub5_at_4 : fetchRel sha384UpdateBlocksCode 0x4 = some (.load .lw (5 : Fin 32) a0 0x48, 4) := by decide
theorem ub5_at_8 : fetchRel sha384UpdateBlocksCode 0x8 = some (.load .lw a6 a0 0x4C, 4) := by decide
theorem ub5_at_c : fetchRel sha384UpdateBlocksCode 0xC = some (.alu .add (17 : Fin 32) a3 a2, 4) := by decide
theorem ub5_at_10 : fetchRel sha384UpdateBlocksCode 0x10 = some (.alu .sltu a3 (17 : Fin 32) a3, 4) := by decide
theorem ub5_at_14 : fetchRel sha384UpdateBlocksCode 0x14 = some (.alu .add a5 a4 a3, 4) := by decide
theorem ub5_at_18 : fetchRel sha384UpdateBlocksCode 0x18 = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem ub5_at_1c : fetchRel sha384UpdateBlocksCode 0x1C = some (.alu .and a3 a3 a4, 2) := by decide
theorem ub5_at_1e : fetchRel sha384UpdateBlocksCode 0x1E = some (.alu .add a3 a3 (5 : Fin 32), 2) := by decide
theorem ub5_at_20 : fetchRel sha384UpdateBlocksCode 0x20 = some (.alu .sltu a4 a3 (5 : Fin 32), 4) := by decide
theorem ub5_at_24 : fetchRel sha384UpdateBlocksCode 0x24 = some (.store .sw a0 (17 : Fin 32) 0x40, 4) := by decide
theorem ub5_at_28 : fetchRel sha384UpdateBlocksCode 0x28 = some (.store .sw a0 a5 0x44, 2) := by decide
theorem ub5_at_2a : fetchRel sha384UpdateBlocksCode 0x2A = some (.alu .add a4 a4 a6, 2) := by decide
theorem ub5_at_2c : fetchRel sha384UpdateBlocksCode 0x2C = some (.store .sw a0 a3 0x48, 2) := by decide
theorem ub5_at_2e : fetchRel sha384UpdateBlocksCode 0x2E = some (.store .sw a0 a4 0x4C, 2) := by decide
theorem ub5_at_30 : fetchRel sha384UpdateBlocksCode 0x30 = some (.auipc (6 : Fin 32) 0xD000, 4) := by decide
theorem ub5_at_34 : fetchRel sha384UpdateBlocksCode 0x34 = some (.jalr x0 (6 : Fin 32) 0x614, 4) := by decide
end

theorem s5Hv_congr {M M' : Word → BitVec 8} {stp : Word}
    (h : ∀ i, i < 64 → M' (stp + BitVec.ofNat 32 i) = M (stp + BitVec.ofNat 32 i)) :
    s5Hv M' stp = s5Hv M stp := by
  have e : ∀ o : Word, o.toNat + 4 ≤ 64 → memLoad32 M' (stp + o) = memLoad32 M (stp + o) := fun o ho =>
    memLoad32_congr fun j hj => by
      have := h (o.toNat + j) (by omega)
      rwa [← add_ofNat_assoc, ofNat_toNat_self] at this
  unfold s5Hv
  rw [e 0x0 (by decide), e 0x4 (by decide), e 0x8 (by decide), e 0xC (by decide), e 0x10 (by decide),
    e 0x14 (by decide), e 0x18 (by decide), e 0x1C (by decide), e 0x20 (by decide), e 0x24 (by decide),
    e 0x28 (by decide), e 0x2C (by decide), e 0x30 (by decide), e 0x34 (by decide), e 0x38 (by decide),
    e 0x3C (by decide)]

/-- Where the single-block closure runs: its code, `memcpy`, and
`compress512` with its callees and round constants where the image puts
them; the 64-byte state at `st`, the 128-byte block at `blk`; and the 0x420 bytes of
stack below `sp0`, which the closure and `compress512` use, apart from the
state, the block, and the constants. -/
structure FB5Env (M : Word → BitVec 8) (st blk sp0 : Word) : Prop where
  cF : CodeIn M (BitVec.ofNat 32 sha512FinBlockAddress) sha512FinBlockCode
  cC : CodeIn M (BitVec.ofNat 32 sha512CompressAddress) sha512CompressCode
  cI : CodeIn M (BitVec.ofNat 32 rangeFromIndexAddress) rangeFromIndexCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cZ : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cK : CodeIn M (BitVec.ofNat 32 sha512KAddress) sha512KData
  hsp : sp0.toNat % 16 = 0
  hspl : 0x420 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hst : st.toNat % 4 = 0
  hstw : st.toNat + 64 ≤ 0x40000000
  hblkw : blk.toNat + 128 ≤ 0x40000000
  sStF : Sep st 64 (sp0 + 0xFFFFFBE0) 0x420
  sBF : Sep blk 128 (sp0 + 0xFFFFFBE0) 0x420
  sKF : Sep (BitVec.ofNat 32 sha512KAddress) 640 (sp0 + 0xFFFFFBE0) 0x420
  sStK : Sep st 64 (BitVec.ofNat 32 sha512KAddress) 640

def fb5Pro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFF70, .sw sp ra 0x8C, .sw sp (8 : Fin 32) 0x88, .alu .add (8 : Fin 32) x0 a0,
    .aluImm .add a0 sp 0x8, .aluImm .add a2 x0 0x80]
def fb5Mid : List BInstr := [.aluImm .add a1 sp 0x8, .aluImm .add a2 x0 0x1, .alu .add a0 x0 (8 : Fin 32)]
def fb5Epi : List BInstr := [.lw ra sp 0x8C, .lw (8 : Fin 32) sp 0x88, .aluImm .add sp sp 0x90]

set_option maxRecDepth 20000 in
theorem fb5Pro_end : blockEnd sha512FinBlockCode 0 fb5Pro = some 0xE := by decide
set_option maxRecDepth 20000 in
theorem fb5Mid_end : blockEnd sha512FinBlockCode 0x16 fb5Mid = some 0x1C := by decide
set_option maxRecDepth 20000 in
theorem fb5Epi_end : blockEnd sha512FinBlockCode 0x24 fb5Epi = some 0x2A := by decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The compiled single-block closure of `Sha512VarCore`'s finalize.**
Called with the state at `st` and a 128-byte block at `blk`, it replaces the
state with SHA-512's compression of the block into it. It returns with `sp`
and the callee-saved registers kept, and changes no memory outside the state
and the 0x420 bytes of stack below `sp`. -/
theorem sha512FinBlock_correct (m : Machine) {st blk sp0 retAddr : Word} (E : FB5Env m.mem st blk sp0)
    (hpc : m.pc = BitVec.ofNat 32 sha512FinBlockAddress) (ha0 : reg m a0 = st) (ha1 : reg m a1 = blk)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 →
        q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
        q ≠ (31 : Fin 32) → reg m' q = reg m q) ∧
      (s5Hv m'.mem st).toList = Sha512.compress (s5Hv m.mem st).toList (memBytes m.mem blk 128) ∧
      ∀ x, Sep (sp0 + 0xFFFFFBE0) 0x420 x 1 → Sep st 64 x 1 → m'.mem x = m.mem x := by
  let Q := BitVec.ofNat 32 sha512FinBlockAddress
  let P := BitVec.ofNat 32 sha512CompressAddress
  let M0 := m.mem
  let R := sp0 + 0xFFFFFBE0
  let G := sp0 + 0xFFFFFF70
  have hspw := E.hspw
  have hspl := E.hspl
  have hRn : R.toNat = sp0.toNat - 0x420 := by
    show (sp0 + 0xFFFFFBE0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFBE0 : Word).toNat = 2 ^ 32 - 0x420 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x420 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hGR : G = R + BitVec.ofNat 32 0x390 := by
    show sp0 + 0xFFFFFF70 = sp0 + 0xFFFFFBE0 + BitVec.ofNat 32 0x390; rw [BitVec.add_assoc]; rfl
  have Gc : ∀ c, G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x390 + c) := fun c => by rw [hGR, add_ofNat_assoc]
  have hGn : G.toNat = sp0.toNat - 0x90 := by rw [hGR, hRc _ (by omega), hRn]; omega
  have hGa : G.toNat % 16 = 0 := by rw [hGn]; have := E.hsp; omega
  have hGa4 : G.toNat % 4 = 0 := by omega
  have Rd : ∀ c l, c + l ≤ 0x420 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk => data_code (by rw [hRc _ (by omega)]; omega) hb hbk
  have Rx : ∀ c l, c + l ≤ 0x420 → ∀ x, Sep R 0x420 x 1 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) h
  have sK := E.sKF
  have sStF := E.sStF
  have sBF := E.sBF
  -- Memory that agrees with `M0` outside the stack area keeps the code and constants.
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x420 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (a := R) (n := 0x420) (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have kX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x420 x 1 → My x = M0 x) →
      CodeIn My (BitVec.ofNat 32 sha512KAddress) sha512KData := fun My h i hi => by
    have hi' : i < 640 := by rw [show sha512KData.length = 640 from rfl] at hi; exact hi
    rw [h _ (sK.sub (c := i) (l := 1) (by omega)).symm]; exact E.cK i hi
  -- The prologue.
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  have slotP : ∀ (o : Nat), o + 4 ≤ 0x90 → o % 4 = 0 →
      (G + BitVec.ofNat 32 o).toNat % 4 = 0 ∧ Sep (G + BitVec.ofNat 32 o) 4 Q sha512FinBlockCode.length :=
    fun o h2 h3 => ⟨aligned_add hGa4 h3, by rw [Gc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide)⟩
  obtain ⟨n1, c1, u1⟩ := St.block fb5Pro st0 E.cF fb5Pro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fb5Pro, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hsp]
    exact ⟨True.intro, slotP 0x8C (by omega) (by omega), slotP 0x88 (by omega) (by omega)⟩)
  let M1 := memStore32 (memStore32 M0 (G + BitVec.ofNat 32 0x8C) retAddr) (G + BitVec.ofNat 32 0x88) (reg m s0)
  have eM1 : (runBlock fb5Pro (M0, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, fb5Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp, hra]; rfl
  have M1R : ∀ x, Sep R 0x420 x 1 → M1 x = M0 x := fun x hx => by
    show memStore32 (memStore32 M0 _ _) _ _ x = _
    rw [memStore32_get_sep (by rw [Gc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (by rw [Gc]; exact Rx _ _ (by omega) x hx)]
  have R1 : ∀ q, reg n1 q = (runBlock fb5Pro (M0, reg m)).2 q := u1.regs
  have u1' : St M1 Q n1 0xE (reg n1) := ⟨u1.pc, by rw [u1.mem, eM1], fun _ => rfl⟩
  have hc1 := codeX M1 M1R _ _ E.cF (by decide) (by decide)
  have K1 : ∀ q, q ≠ sp → q ≠ s0 → q ≠ a0 → q ≠ a2 → reg n1 q = reg m q := fun q h2 h8 h10 h12 => by
    rw [R1]; simp only [runBlock, BInstr.run, fb5Pro]
    rw [updz (by simp [upd]) h12, updz (by simp [upd]) h10, updz (by simp [upd]) h8, updz hz h2]
  have sp1 : reg n1 sp = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, fb5Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp]
  have s01 : reg n1 s0 = st := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, fb5Pro, upd_app, ↓reduceIte]; simp only [ev_add]
    exact (BitVec.zero_add _).trans ha0
  -- `memcpy` of the block to `G + 8`.
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc1 fb5_at_e fb5_at_12
    (show Q + BitVec.ofNat 32 0xE + 0x4000 + 0xFFFFFDEC = BitVec.ofNat 32 memcpyStubAddress by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  have eF : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x380 := by rw [hGR, BitVec.add_assoc]; rfl
  have hF : (G + 0xFFFFFFF0).toNat = R.toNat + 0x380 := by rw [eF, hRc _ (by omega)]
  have hG8 : (G + BitVec.ofNat 32 8).toNat = R.toNat + 0x398 := by rw [Gc, hRc _ (by omega)]
  obtain ⟨n3, c3, pc3, sp3, _, mem3, K3⟩ := memcpy_correct n2 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 (0xE + 8)) (G + BitVec.ofNat 32 8) blk 128
    (fun i hi => by show n2.mem _ = _; rw [mem2]; exact codeX M1 M1R _ _ E.cMS (by decide) (by decide) i hi)
    (by decide) pc2
    (by rw [r2 a0 (by decide), R1]; simp +decide only [runBlock, BInstr.run, fb5Pro, upd_app, ↓reduceIte]
        simp only [ev_add]; rw [hsp]; rfl)
    (by rw [r2 a1 (by decide), K1 a1 (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [r2 a2 (by decide), R1]; simp +decide only [runBlock, BInstr.run, fb5Pro, upd_app, ↓reduceIte]; try rfl)
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at Q (by decide) _ (by omega)))
    (by
      rw [mem2, r2 sp (by decide), sp1]
      exact { code := codeX M1 M1R _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by rw [hG8]; omega) (by decide) (by decide)
              hFC := data_code (by rw [hF]; omega) (by decide) (by decide)
              hdF := by
                rw [eF, Gc]
                exact sep_offsets R (c := 0x398) (n := 128) (d := 0x380) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
              hsF := by rw [eF]; exact sBF.subR (c := 0x380) (l := 16) (by omega)
              hsep := by rw [Gc]; exact (sBF.subR (c := 0x398) (l := 128) (by omega)).symm
              hF := by rw [hF, hRn]; have := E.hsp; omega
              hFw := by rw [hF]; omega
              hdw := by rw [hG8]; omega
              hsw := by have := E.hblkw; omega })
  rw [mem2, r2 sp (by decide), sp1, eF] at mem3
  obtain ⟨M3, hM3⟩ : ∃ M3, n3.mem = M3 := ⟨_, rfl⟩
  rw [hM3] at mem3
  have k3 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ sp →
      reg n3 q = reg n2 q := K3
  have M3R : ∀ x, Sep R 0x420 x 1 → M3 x = M0 x := fun x hx => by
    rw [mem3 x (Rx _ _ (by omega) x hx), copyBytes_sep (by rw [Gc]; exact Rx _ _ (by omega) x hx) (Nat.le_refl _),
      M1R x hx]
  have hc3 := codeX M3 M3R _ _ E.cF (by decide) (by decide)
  have u3 : St M3 Q n3 0x16 (reg n3) := ⟨by rw [pc3], hM3, fun _ => rfl⟩
  obtain ⟨n4, c4, u4⟩ := St.block fb5Mid u3 hc3 fb5Mid_end (by simp [BlockOk, BInstr.ok, fb5Mid])
  have R4 : ∀ q, reg n4 q = (runBlock fb5Mid (M3, reg n3)).2 q := u4.regs
  have u4' : St M3 Q n4 0x1C (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
  have k31 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ sp → q ≠ ra →
      reg n3 q = reg n1 q := fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 => by
    rw [k3 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14, r2 q h15]
  have sp3' : reg n3 sp = G := by rw [sp3, r2 sp (by decide), sp1]
  have s03 : reg n3 s0 = st := by
    rw [k31 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s01]
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n4 q = reg n3 q := fun q h0 h1 h2 => by
    rw [R4]; simp only [runBlock, BInstr.run, fb5Mid]
    rw [updz (by simp [upd]) h0, updz (by simp [upd]) h2, updz u3.zero h1]
  obtain ⟨n5, c5, pc5, mem5, regs5⟩ := u4'.callRa hc3 fb5_at_1c fb5_at_20
    (show Q + BitVec.ofNat 32 0x1C + 0x4000 + 0xFFFFF832 = P by decide) (by decide)
  have r5 : ∀ q, q ≠ ra → reg n5 q = reg n4 q := fun q h => by rw [regs5]; exact updz u4'.zero h
  have eRG : G + 0xFFFFFC70 = R := by rw [hGR, BitVec.add_assoc]; exact BitVec.add_zero R
  have env5 : S5Env n5.mem P G st (G + BitVec.ofNat 32 8) 1 := by
    rw [mem5]
    exact { hP := by decide
            code := codeX M3 M3R _ _ E.cC (by decide) (by decide)
            idx := by
              rw [show P + 0xFFFFFFEA = BitVec.ofNat 32 rangeFromIndexAddress by decide]
              exact codeX M3 M3R _ _ E.cI (by decide) (by decide)
            stub := by
              rw [show P + 0x5AC = BitVec.ofNat 32 memcpyStubAddress by decide]
              exact codeX M3 M3R _ _ E.cMS (by decide) (by decide)
            body := by
              rw [show P + 0x5B4 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
              exact codeX M3 M3R _ _ E.cMB (by decide) (by decide)
            mset := by
              rw [show P + 0x544 = BitVec.ofNat 32 memsetAddress by decide]
              exact codeX M3 M3R _ _ E.cZ (by decide) (by decide)
            kdata := kX M3 M3R
            hsp := hGa4
            hS := by rw [hGn]; omega
            hstp := E.hst
            hwbp := by rw [hG8]; omega
            sC := by rw [eRG]; have := Rd 0 0x390 (by omega) P sha512CompressCode.length (by decide) (by decide)
                     rwa [add_ofNat_zero] at this
            sI := by rw [eRG]; have := Rd 0 0x390 (by omega) (P + 0xFFFFFFEA) rangeFromIndexCode.length (by decide) (by decide)
                     rwa [add_ofNat_zero] at this
            sU := by rw [eRG]; have := Rd 0 0x390 (by omega) (P + 0x5AC) memcpyStubCode.length (by decide) (by decide)
                     rwa [add_ofNat_zero] at this
            sB := by rw [eRG]; have := Rd 0 0x390 (by omega) (P + 0x5B4) memcpyBodyCode.length (by decide) (by decide)
                     rwa [add_ofNat_zero] at this
            sZ := by rw [eRG]; have := Rd 0 0x390 (by omega) (P + 0x544) memsetCode.length (by decide) (by decide)
                     rwa [add_ofNat_zero] at this
            sK := by rw [eRG]; have := sK.symm.sub (c := 0) (l := 0x390) (by omega); rwa [add_ofNat_zero] at this
            stC := data_code E.hstw (by decide) (by decide)
            stI := data_code E.hstw (by decide) (by decide)
            stU := data_code E.hstw (by decide) (by decide)
            stB := data_code E.hstw (by decide) (by decide)
            stZ := data_code E.hstw (by decide) (by decide)
            stK := E.sStK
            stF := by rw [eRG]; have := sStF.subR (c := 0) (l := 0x390) (by omega); rwa [add_ofNat_zero] at this
            bF := by
              rw [Gc, eRG]
              have := sep_offsets R (c := 0x398) (n := 128 * 1) (d := 0) (k := 0x390) (Or.inr (by omega)) (by omega)
                (by omega)
              rwa [add_ofNat_zero] at this
            bSt := by rw [Gc]; exact sStF.symm.sub (c := 0x398) (l := 128 * 1) (by omega) }
  obtain ⟨n6, c6, pc6, sp6, K6, st6, fr6⟩ := s5Compress_correct n5 (retAddr := Q + BitVec.ofNat 32 (0x1C + 8)) env5 pc5
    (by rw [r5 a0 (by decide), R4]; simp +decide only [runBlock, BInstr.run, fb5Mid, upd_app, ↓reduceIte]
        simp only [ev_add]; exact (BitVec.zero_add _).trans s03)
    (by rw [r5 a1 (by decide), R4]; simp +decide only [runBlock, BInstr.run, fb5Mid, upd_app, ↓reduceIte]
        simp only [ev_add]; rw [sp3']; rfl)
    (by rw [r5 a2 (by decide), R4]; simp +decide only [runBlock, BInstr.run, fb5Mid, upd_app, ↓reduceIte]; try rfl)
    (by rw [regs5]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at Q (by decide) _ (by omega)))
    (by rw [r5 sp (by decide), k4 sp (by decide) (by decide) (by decide), sp3'])
  rw [mem5, eRG] at fr6
  rw [mem5] at st6
  obtain ⟨M6, hM6⟩ : ∃ M6, n6.mem = M6 := ⟨_, rfl⟩
  rw [hM6] at fr6 st6
  -- The saved registers survive.
  have slot : ∀ o, (o = 0x88 ∨ o = 0x8C) → memLoad32 M6 (G + BitVec.ofNat 32 o) = memLoad32 M1 (G + BitVec.ofNat 32 o) := by
    intro o ho
    have ho' : o = 0x88 ∨ o = 0x8C := ho
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc, Gc]
    rw [fr6 _ (sep_offsets R (c := 0) (n := 0x390) (d := 0x390 + (o + j)) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        |> fun h => by rwa [add_ofNat_zero] at h) (sStF.subR (c := 0x390 + (o + j)) (l := 1) (by omega)),
      mem3 _ (sep_offsets R (c := 0x380) (n := 16) (d := 0x390 + (o + j)) (k := 1) (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (by
        rw [Gc]
        exact sep_offsets R (c := 0x398) (n := 128) (d := 0x390 + (o + j)) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)) (Nat.le_refl _)]
  have l8C : memLoad32 M6 (G + BitVec.ofNat 32 0x8C) = retAddr := by
    rw [slot 0x8C (Or.inr rfl)]
    show memLoad32 (memStore32 (memStore32 M0 _ _) _ _) _ = _
    rw [memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have l88 : memLoad32 M6 (G + BitVec.ofNat 32 0x88) = reg m s0 := by
    rw [slot 0x88 (Or.inl rfl)]
    show memLoad32 (memStore32 (memStore32 M0 _ _) _ _) _ = _
    rw [memLoad32_store32_same]
  have hc6 : CodeIn M6 Q sha512FinBlockCode := fun i hi => by
    rw [fr6 _ ((data_code (a := R) (n := 0x390) (by rw [hRn]; omega) (by decide) (by decide)).subR (c := i) (l := 1)
        hi) ((data_code (a := st) (n := 64) E.hstw (by decide) (by decide)).subR (c := i) (l := 1) hi)]
    exact hc3 i hi
  have u6 : St M6 Q n6 0x24 (reg n6) := ⟨by rw [pc6], hM6, fun _ => rfl⟩
  have sp6' : reg n6 sp = G := sp6
  obtain ⟨n7, c7, u7⟩ := St.block fb5Epi u6 hc6 fb5Epi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fb5Epi, upd_app, ↓reduceIte, and_true]
    rw [sp6']
    exact ⟨aligned_add hGa4 (k := 0x8C) (by decide), aligned_add hGa4 (k := 0x88) (by decide)⟩)
  have R7 : ∀ q, reg n7 q = (runBlock fb5Epi (M6, reg n6)).2 q := u7.regs
  have u7' : St M6 Q n7 0x2A (reg n7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7'.jalr hc6 fb5_at_2a
  have ra7 : reg n7 ra = retAddr := by
    rw [R7]; simp +decide only [runBlock, BInstr.run, fb5Epi, upd_app, ↓reduceIte]; rw [sp6']; exact l8C
  have k7 : ∀ q, q ≠ ra → q ≠ s0 → q ≠ sp → reg n7 q = reg n6 q := fun q h1 h8 h2 => by
    rw [R7]; simp only [runBlock, BInstr.run, fb5Epi]
    rw [updz (by simp [upd]) h2, updz (by simp [upd]) h8, updz u6.zero h1]
  have s07 : reg n7 s0 = reg m s0 := by
    rw [R7]; simp +decide only [runBlock, BInstr.run, fb5Epi, upd_app, ↓reduceIte]; rw [sp6']; exact l88
  have sp7 : reg n7 sp = sp0 := by
    rw [R7]; simp +decide only [runBlock, BInstr.run, fb5Epi, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp6']
    show sp0 + 0xFFFFFF70 + 0x90 = sp0
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hblk : memBytes M3 (G + BitVec.ofNat 32 8) 128 = memBytes M0 blk 128 := by
    unfold memBytes; apply List.map_congr_left; intro i hi; have hi := List.mem_range.mp hi
    show (M3 (G + BitVec.ofNat 32 8 + BitVec.ofNat 32 i)).toNat = (M0 (blk + BitVec.ofNat 32 i)).toNat
    rw [mem3 _ (by
        rw [Gc, add_ofNat_assoc]
        exact sep_offsets R (c := 0x380) (n := 16) (d := 0x390 + 8 + i) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)),
      copyBytes_in hi (by omega), M1R _ (sBF.sub (c := i) (l := 1) (by omega)).symm]
  have hstate : s5Hv M3 st = s5Hv M0 st := s5Hv_congr fun i hi => M3R _ (sStF.sub (c := i) (l := 1) (by omega)).symm
  have hbl : blockList128 M3 (G + BitVec.ofNat 32 8) 1 = [memBytes M3 (G + BitVec.ofNat 32 8) 128] := by
    unfold blockList128
    rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, show 128 * 0 = 0 from rfl, add_ofNat_zero]
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.single d8))))))), ?_,
    by rw [regs8, sp7], fun q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_,
    fun x hx hy => ?_⟩
  · rw [pc8, ra7, add_lit_zero, hret]
  · rw [regs8]
    by_cases qr : q = ra
    · subst qr; rw [ra7, hra]
    by_cases q8 : q = s0
    · subst q8; exact s07
    by_cases q2 : q = sp
    · subst q2; rw [sp7, hsp]
    rw [k7 q qr q8 q2, K6 q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r5 q qr,
      k4 q q10 q11 q12, k31 q q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 qr, K1 q q2 q8 q10 q12]
  · rw [mem8, st6, hbl, hblk, hstate, List.foldl_cons, List.foldl_nil]
  · rw [mem8, fr6 x (by have := hx.sub (c := 0) (l := 0x390) (by omega); rwa [add_ofNat_zero] at this) hy,
      M3R x hx]

set_option maxRecDepth 40000 in
/-- `compress512`'s environment survives a store outside everything it uses. -/
theorem S5Env.store32 {M : Word → BitVec 8} {P sp0 stp bp a v : Word} {n : Nat}
    (env : S5Env M P sp0 stp bp n) (hC : Sep a 4 P sha512CompressCode.length)
    (hI : Sep a 4 (P + 0xFFFFFFEA) rangeFromIndexCode.length) (hU : Sep a 4 (P + 0x5AC) memcpyStubCode.length)
    (hB : Sep a 4 (P + 0x5B4) memcpyBodyCode.length) (hZ : Sep a 4 (P + 0x544) memsetCode.length)
    (hK : Sep a 4 (BitVec.ofNat 32 sha512KAddress) 640) : S5Env (memStore32 M a v) P sp0 stp bp n :=
  { env with
    code := env.code.store32 hC
    idx := env.idx.store32 hI
    stub := env.stub.store32 hU
    body := env.body.store32 hB
    mset := env.mset.store32 hZ
    kdata := env.kdata.store32 hK }

def ub5Blk : List BInstr :=
  [.lw a3 a0 0x40, .lw a4 a0 0x44, .lw (5 : Fin 32) a0 0x48, .lw a6 a0 0x4C, .alu .add (17 : Fin 32) a3 a2,
    .alu .sltu a3 (17 : Fin 32) a3, .alu .add a5 a4 a3, .alu .sltu a4 a5 a4, .alu .and a3 a3 a4,
    .alu .add a3 a3 (5 : Fin 32), .alu .sltu a4 a3 (5 : Fin 32), .sw a0 (17 : Fin 32) 0x40, .sw a0 a5 0x44,
    .alu .add a4 a4 a6, .sw a0 a3 0x48, .sw a0 a4 0x4C]

set_option maxRecDepth 20000 in
theorem ub5Blk_end : blockEnd sha384UpdateBlocksCode 0 ub5Blk = some 0x30 := by decide

theorem ub5_sltu_self (x : Word) : aluEval .sltu x x = 0 := by
  show (if x.ult x then (1 : Word) else 0) = 0
  exact ite_eq_right (by simp only [BitVec.ult, decide_eq_true_eq]; exact Nat.lt_irrefl _)

theorem ub5_add_zero (x : Word) : aluEval .add x 0 = x := BitVec.add_zero x
theorem ub5_zero_add (x : Word) : aluEval .add 0 x = x := BitVec.zero_add x
theorem ub5_and_zero (x : Word) : aluEval .and 0 x = 0 := BitVec.zero_and

theorem ub5_nocarry {lo : Word} {n : Nat} (h : lo.toNat + n < 2 ^ 32) :
    aluEval .sltu (aluEval .add lo (BitVec.ofNat 32 n)) lo = 0 := by
  show (if (lo + BitVec.ofNat 32 n).ult lo then (1 : Word) else 0) = 0
  refine ite_eq_right ?_
  simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat, decide_eq_true_eq]
  rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The block helper of SHA-512's `update`.** Called with the state at
`st`, the 128-bit block count after it at `st + 0x40`, and `n` blocks at
`bp`, it adds `n` to the count and compresses the blocks into the state, as
`s5Compress_correct` says, then returns. It changes no memory outside
`compress512`'s frame and the 0x50 bytes at `st`. -/
theorem sha384UpdateBlocks_correct (m : Machine) {st bp sp0 retAddr : Word} {n : Nat}
    (hcode : CodeIn m.mem (BitVec.ofNat 32 sha384UpdateBlocksAddress) sha384UpdateBlocksCode)
    (hpc : m.pc = BitVec.ofNat 32 sha384UpdateBlocksAddress)
    (env : S5Env m.mem (BitVec.ofNat 32 sha512CompressAddress) sp0 st bp n)
    (ha0 : reg m a0 = st) (ha1 : reg m a1 = bp) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hcnt : (memLoad32 m.mem (st + 0x40)).toNat + n < 2 ^ 32)
    (cC : Sep (st + 0x40) 16 (BitVec.ofNat 32 sha512CompressAddress) sha512CompressCode.length)
    (cI : Sep (st + 0x40) 16 (BitVec.ofNat 32 sha512CompressAddress + 0xFFFFFFEA) rangeFromIndexCode.length)
    (cS : Sep (st + 0x40) 16 (BitVec.ofNat 32 sha512CompressAddress + 0x5AC) memcpyStubCode.length)
    (cY : Sep (st + 0x40) 16 (BitVec.ofNat 32 sha512CompressAddress + 0x5B4) memcpyBodyCode.length)
    (cZ : Sep (st + 0x40) 16 (BitVec.ofNat 32 sha512CompressAddress + 0x544) memsetCode.length)
    (cK : Sep (st + 0x40) 16 (BitVec.ofNat 32 sha512KAddress) 640)
    (cF : Sep (st + 0x40) 16 (sp0 + 0xFFFFFC70) 0x390) (cB : Sep bp (128 * n) (st + 0x40) 16)
    (cU : Sep (st + 0x40) 16 (BitVec.ofNat 32 sha384UpdateBlocksAddress) sha384UpdateBlocksCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) →
        q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ (17 : Fin 32) →
        q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      (s5Hv m'.mem st).toList = (blockList128 m.mem bp n).foldl Sha512.compress (s5Hv m.mem st).toList ∧
      memLoad32 m'.mem (st + 0x40) = memLoad32 m.mem (st + 0x40) + BitVec.ofNat 32 n ∧
      memLoad32 m'.mem (st + 0x44) = memLoad32 m.mem (st + 0x44) ∧
      memLoad32 m'.mem (st + 0x48) = memLoad32 m.mem (st + 0x48) ∧
      memLoad32 m'.mem (st + 0x4C) = memLoad32 m.mem (st + 0x4C) ∧
      ∀ x, Sep (sp0 + 0xFFFFFC70) 0x390 x 1 → Sep st 0x50 x 1 → m'.mem x = m.mem x := by
  let B := BitVec.ofNat 32 sha384UpdateBlocksAddress
  let P := BitVec.ofNat 32 sha512CompressAddress
  have s0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := s0.zero
  have sub4 : ∀ (o : Nat), o + 4 ≤ 16 → ∀ {b : Word} {l : Nat}, Sep (st + 0x40) 16 b l →
      Sep (st + BitVec.ofNat 32 (0x40 + o)) 4 b l := fun o ho b l h => by
    have := h.sub (c := o) (l := 4) ho
    rwa [show st + (0x40 : Word) = st + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc] at this
  have al : ∀ k, k % 4 = 0 → (st + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k hk => aligned_add env.hstp hk
  obtain ⟨n1, c1, u1⟩ := St.block ub5Blk s0 hcode ub5Blk_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ub5Blk, upd_app, ↓reduceIte, and_true, true_and]
    rw [ha0]
    exact ⟨al 64 (by decide), al 68 (by decide), al 72 (by decide), al 76 (by decide),
      ⟨al 64 (by decide), sub4 0 (by omega) cU⟩, ⟨al 68 (by decide), sub4 4 (by omega) cU⟩,
      ⟨al 72 (by decide), sub4 8 (by omega) cU⟩, al 76 (by decide), sub4 12 (by omega) cU⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 (memStore32 (memStore32 m.mem (st + BitVec.ofNat 32 (0x40 + 0))
      (memLoad32 m.mem (st + 0x40) + BitVec.ofNat 32 n)) (st + BitVec.ofNat 32 (0x40 + 4)) (memLoad32 m.mem (st + 0x44)))
      (st + BitVec.ofNat 32 (0x40 + 8)) (memLoad32 m.mem (st + 0x48))) (st + BitVec.ofNat 32 (0x40 + 12))
      (memLoad32 m.mem (st + 0x4C)) = M1 := ⟨_, rfl⟩
  have eM1 : (runBlock ub5Blk (m.mem, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, ub5Blk, upd_app, ↓reduceIte]
    rw [ha0, ha2]
    simp only [ub5_nocarry hcnt, ub5_add_zero, ub5_sltu_self, ub5_and_zero, ub5_zero_add]
    rw [← hM1]; rfl
  have R1 : ∀ q, reg n1 q = (runBlock ub5Blk (m.mem, reg m)).2 q := u1.regs
  have u1' : St M1 B n1 0x30 (reg n1) := ⟨u1.pc, by rw [u1.mem, eM1], fun _ => rfl⟩
  have K1 : ∀ q, q ≠ a3 → q ≠ a4 → q ≠ (5 : Fin 32) → q ≠ a6 → q ≠ (17 : Fin 32) → q ≠ a5 →
      reg n1 q = reg m q := fun q h3 h4 h5 h6 h7 h15 => by
    rw [R1]; refine runBlock_reg _ _ _ q hz ?_
    simp only [ub5Blk, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    simp [h3, h4, h5, h6, h7, h15]
  have hc1 : CodeIn M1 B sha384UpdateBlocksCode := by
    rw [← hM1]
    exact (((hcode.store32 (sub4 0 (by omega) cU)).store32 (sub4 4 (by omega) cU)).store32 (sub4 8 (by omega) cU)).store32
      (sub4 12 (by omega) cU)
  obtain ⟨n2, d2, u2⟩ := u1'.auipc hc1 ub5_at_30 (off' := 0x34) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc1 ub5_at_34
  have hP : n3.pc = P := by rw [pc3]; simp +decide only [upd, ite_false, ite_true]; decide
  have r3 : ∀ q, q ≠ (6 : Fin 32) → reg n3 q = reg n1 q := fun q h6 => by rw [regs3]; exact updz u1'.zero h6
  have r3m : ∀ q, q ≠ a3 → q ≠ a4 → q ≠ (5 : Fin 32) → q ≠ a6 → q ≠ (17 : Fin 32) → q ≠ a5 → q ≠ (6 : Fin 32) →
      reg n3 q = reg m q := fun q h3 h4 h5 h6 h7 h15 h16 => by rw [r3 q h16, K1 q h3 h4 h5 h6 h7 h15]
  have env3 : S5Env n3.mem P sp0 st bp n := by
    rw [mem3, ← hM1]
    exact (((env.store32 (sub4 0 (by omega) cC) (sub4 0 (by omega) cI) (sub4 0 (by omega) cS) (sub4 0 (by omega) cY)
      (sub4 0 (by omega) cZ) (sub4 0 (by omega) cK)).store32 (sub4 4 (by omega) cC) (sub4 4 (by omega) cI)
      (sub4 4 (by omega) cS) (sub4 4 (by omega) cY) (sub4 4 (by omega) cZ) (sub4 4 (by omega) cK)).store32
      (sub4 8 (by omega) cC) (sub4 8 (by omega) cI) (sub4 8 (by omega) cS) (sub4 8 (by omega) cY)
      (sub4 8 (by omega) cZ) (sub4 8 (by omega) cK)).store32 (sub4 12 (by omega) cC) (sub4 12 (by omega) cI)
      (sub4 12 (by omega) cS) (sub4 12 (by omega) cY) (sub4 12 (by omega) cZ) (sub4 12 (by omega) cK)
  obtain ⟨m', c', pc', sp', K', wst, fr⟩ := s5Compress_correct n3 env3 hP
    (by rw [r3m a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha0])
    (by rw [r3m a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [r3m a2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha2])
    (by rw [r3m ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hra]) hret
    (by rw [r3m sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp])
  rw [mem3] at wst fr
  -- `M1` differs from `m.mem` only in the count.
  have M1o : ∀ x, Sep (st + 0x40) 16 x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1, memStore32_get_sep (sub4 12 (by omega) hx), memStore32_get_sep (sub4 8 (by omega) hx),
      memStore32_get_sep (sub4 4 (by omega) hx), memStore32_get_sep (sub4 0 (by omega) hx)]
  have hst : s5Hv M1 st = s5Hv m.mem st := s5Hv_congr fun i hi => M1o _ (by
    rw [show st + (0x40 : Word) = st + BitVec.ofNat 32 0x40 from rfl]
    exact sep_offsets st (c := 0x40) (n := 16) (d := i) (k := 1) (Or.inr (by omega)) (by omega) (by omega))
  have hbl : blockList128 M1 bp n = blockList128 m.mem bp n := by
    unfold blockList128; apply List.map_congr_left; intro j hj; have hj := List.mem_range.mp hj
    apply memBytes_congr; intro i hi
    rw [add_ofNat_assoc]
    exact M1o _ (cB.sub (c := 128 * j + i) (l := 1) (by omega)).symm
  have cnt : ∀ o, o + 4 ≤ 16 → memLoad32 m'.mem (st + BitVec.ofNat 32 (0x40 + o)) =
      memLoad32 M1 (st + BitVec.ofNat 32 (0x40 + o)) := fun o ho => by
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    apply fr
    · have := cF.symm.subR (c := o + j) (l := 1) (by omega)
      rwa [show st + (0x40 : Word) = st + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc,
        show 0x40 + (o + j) = 0x40 + o + j by omega] at this
    · exact sep_offsets st (c := 0) (n := 64) (d := 0x40 + o + j) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        |> fun h => by rwa [add_ofNat_zero] at h
  have sp4 : ∀ c d, (c + 4 ≤ d ∨ d + 4 ≤ c) → c < 16 → d < 16 →
      Sep (st + BitVec.ofNat 32 (0x40 + c)) 4 (st + BitVec.ofNat 32 (0x40 + d)) 4 := fun c d h hc hd =>
    sep_offsets st (Or.imp (fun h => by omega) (fun h => by omega) h) (by omega) (by omega)
  refine ⟨m', c1.trans (.cons d2 (.cons d3 c')), pc', sp',
    fun q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, ?_, ?_, ?_, ?_, fun x hF hx => ?_⟩
  · rw [K' q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r3m q q13 q14 q5 q16 q17 q15 q6]
  · rw [wst, hbl, hst]
  · show memLoad32 m'.mem (st + BitVec.ofNat 32 (0x40 + 0)) = _
    rw [cnt 0 (by omega), ← hM1, memLoad32_store32_sep (sp4 12 0 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (sp4 8 0 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (sp4 4 0 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · show memLoad32 m'.mem (st + BitVec.ofNat 32 (0x40 + 4)) = _
    rw [cnt 4 (by omega), ← hM1, memLoad32_store32_sep (sp4 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (sp4 8 4 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · show memLoad32 m'.mem (st + BitVec.ofNat 32 (0x40 + 8)) = _
    rw [cnt 8 (by omega), ← hM1, memLoad32_store32_sep (sp4 12 8 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · show memLoad32 m'.mem (st + BitVec.ofNat 32 (0x40 + 12)) = _
    rw [cnt 12 (by omega), ← hM1, memLoad32_store32_same]
  · rw [fr x hF (by have := hx.sub (c := 0) (l := 64) (by omega); rwa [add_ofNat_zero] at this),
      M1o x (hx.sub (c := 0x40) (l := 16) (by omega))]

end C3.RV32
