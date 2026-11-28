import C3BootProofs.Proofs.Sha2OneShot

/-!
# `c3_crypto::sha::Sha256::finish`, as compiled

`finish` takes the hasher by value: it copies the hasher's 0x68 bytes into
its frame with `memcpy` and calls `finalize` on the copy, which writes the
digest to the output.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem shf_at_e : fetchRel shaFinishCode 0xE = some (.auipc ra 0x10000, 4) := by decide
theorem shf_at_12 : fetchRel shaFinishCode 0x12 = some (.jalr ra ra 0xFFFFFD20, 4) := by decide
theorem shf_at_1a : fetchRel shaFinishCode 0x1A = some (.auipc ra 0x0, 4) := by decide
theorem shf_at_1e : fetchRel shaFinishCode 0x1E = some (.jalr ra ra 0x10, 4) := by decide
theorem shf_at_28 : fetchRel shaFinishCode 0x28 = some (.jalr x0 ra 0x0, 2) := by decide

def fiA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFF90, .sw sp ra 0x6C, .sw sp (8 : Fin 32) 0x68, .alu .add (8 : Fin 32) x0 a0,
    .alu .add a0 x0 sp, .aluImm .add a2 x0 0x68]

def fiB : List BInstr := [.alu .add a1 x0 sp, .alu .add a0 x0 (8 : Fin 32)]

def fiC : List BInstr := [.lw ra sp 0x6C, .lw (8 : Fin 32) sp 0x68, .aluImm .add sp sp 0x70]

theorem fiA_end : blockEnd shaFinishCode 0 fiA = some 0xE := by decide
theorem fiB_end : blockEnd shaFinishCode 0x16 fiB = some 0x1A := by decide
theorem fiC_end : blockEnd shaFinishCode 0x22 fiC = some 0x28 := by decide
end

/-- Where `finish` runs: its code and `finalize`'s callees', the hasher at
`S`, the output at `out`, and 0x200 bytes of stack below `sp0`, all below
0x40000000; the hasher, the output, and the round constants are each apart
from the stack. -/
structure FinishEnv (M : Word → BitVec 8) (S out sp0 : Word) : Prop where
  cX : CodeIn M (BitVec.ofNat 32 shaFinishAddress) shaFinishCode
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cBlk : CodeIn M (BitVec.ofNat 32 shaFinBlockAddress) shaFinBlockCode
  cMs : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hSw : S.toNat + 0x68 ≤ 0x40000000
  hsp : sp0.toNat % 16 = 0
  hspl : 0x200 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hOw : out.toNat + 32 ≤ 0x40000000
  sSF : Sep S 0x68 (sp0 + 0xFFFFFE00) 0x200
  sOF : Sep out 32 (sp0 + 0xFFFFFE00) 0x200
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFE00) 0x200

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `Sha256::finish`.** Called with the hasher at `S`
holding `msg` and an output at `out`, it writes FIPS 180-4's SHA-256 digest
of `msg` to the 32 bytes at `out`. It returns to `retAddr` with `sp`
restored and the callee-saved registers kept, and changes no memory outside
the output and 0x200 bytes of stack below `sp`. -/
theorem shaFinish_correct (m : Machine) {S out sp0 retAddr : Word} {msg : Bytes}
    (E : FinishEnv m.mem S out sp0) (hpc : m.pc = BitVec.ofNat 32 shaFinishAddress)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = S) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (H : HasherAt m.mem S msg) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
        r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
        r ≠ (31 : Fin 32) → reg m' r = reg m r) ∧
      memBytes m'.mem out 32 = sha256 msg ∧
      ∀ x, Sep (sp0 + 0xFFFFFE00) 0x200 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  let Q := BitVec.ofNat 32 shaFinishAddress
  let M0 := m.mem
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFE00 = R := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFF90 = F := ⟨_, rfl⟩
  have sSF := E.sSF; have sOF := E.sOF; have sKF := E.sKF
  rw [hR] at sSF sOF sKF ⊢
  have hspw := E.hspw
  have hspl := E.hspl
  have hOw := E.hOw
  have hSw := E.hSw
  have hRn : R.toNat = sp0.toNat - 0x200 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFE00 : Word).toNat = 2 ^ 32 - 0x200 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x200 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFR : F = R + BitVec.ofNat 32 0x190 := by rw [← hF, ← hR, BitVec.add_assoc]; rfl
  have Fc : ∀ c, F + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x190 + c) := fun c => by rw [hFR, add_ofNat_assoc]
  have hFn : F.toNat = sp0.toNat - 0x70 := by rw [hFR, hRc _ (by omega), hRn]; omega
  have hFc : ∀ c, c ≤ 0x70 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc => by
    rw [Fc, hRc _ (by omega), hFn, hRn]; omega
  have hFa : F.toNat % 16 = 0 := by rw [hFn]; have := E.hsp; omega
  have hFa4 : F.toNat % 4 = 0 := by omega
  have Rx : ∀ c l, c + l ≤ 0x200 → ∀ x, Sep R 0x200 x 1 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) h
  have Rd : ∀ c l, c + l ≤ 0x200 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk =>
    data_code (by rw [hRc _ (by omega)]; omega) hb hbk
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x200 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  -- The frame, `ra` and `s0` saved in it, and `memcpy`'s arguments.
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  have eF : aluEval .add (reg m sp) 0xFFFFFF90 = F := by rw [hsp, ← hF]; rfl
  have a6C : (F + 0x6C).toNat % 4 = 0 := aligned_add hFa4 (k := 0x6C) (by decide)
  have a68 : (F + 0x68).toNat % 4 = 0 := aligned_add hFa4 (k := 0x68) (by decide)
  have s6C : Sep (F + 0x6C) 4 Q shaFinishCode.length := by
    rw [show F + (0x6C : Word) = F + BitVec.ofNat 32 0x6C from rfl, Fc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide)
  have s68 : Sep (F + 0x68) 4 Q shaFinishCode.length := by
    rw [show F + (0x68 : Word) = F + BitVec.ofNat 32 0x68 from rfl, Fc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide)
  obtain ⟨m1, c1, u1⟩ := St.block fiA st0 E.cX fiA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fiA, upd_app, ↓reduceIte, and_true]
    rw [eF]; exact ⟨True.intro, ⟨a6C, s6C⟩, a68, s68⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 M0 (F + 0x6C) (reg m ra)) (F + 0x68) (reg m s0) = M1 := ⟨_, rfl⟩
  have eM1 : (runBlock fiA (M0, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, fiA, upd_app, ↓reduceIte]; rw [eF, ← hM1]
  have RA : ∀ q, reg m1 q = (runBlock fiA (M0, reg m)).2 q := u1.regs
  have u1' : St M1 Q m1 0xE (reg m1) := ⟨u1.pc, by rw [u1.mem, eM1], fun _ => rfl⟩
  have M1R : ∀ x, Sep R 0x200 x 1 → M1 x = M0 x := fun x hx => by
    rw [← hM1, memStore32_get_sep (show Sep (F + 0x68) 4 x 1 by
        rw [show F + (0x68 : Word) = F + BitVec.ofNat 32 0x68 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0x6C) 4 x 1 by
        rw [show F + (0x6C : Word) = F + BitVec.ofNat 32 0x6C from rfl, Fc]; exact Rx _ _ (by omega) x hx)]
  have cM1 := codeX M1 M1R
  have cX1 := cM1 _ _ E.cX (by decide) (by decide)
  have sp1 : reg m1 sp = F := by rw [RA]; simp +decide only [runBlock, BInstr.run, fiA, upd_app, ↓reduceIte]; exact eF
  have s0_1 : reg m1 s0 = out := by
    rw [RA]; simp +decide only [runBlock, BInstr.run, fiA, upd_app, ↓reduceIte]; rw [ha0]; exact BitVec.zero_add _
  have a0_1 : reg m1 a0 = F := by
    rw [RA]; simp +decide only [runBlock, BInstr.run, fiA, upd_app, ↓reduceIte]; rw [eF]; exact BitVec.zero_add _
  have a1_1 : reg m1 a1 = S := by rw [RA]; simp +decide only [runBlock, BInstr.run, fiA, upd_app, ↓reduceIte]; exact ha1
  have a2_1 : reg m1 a2 = BitVec.ofNat 32 0x68 := by
    rw [RA]; simp +decide only [runBlock, BInstr.run, fiA, upd_app, ↓reduceIte]; try rfl
  have K1 : ∀ q, q ≠ sp → q ≠ s0 → q ≠ a0 → q ≠ a2 → reg m1 q = reg m q := fun q h1 h2 h3 h4 => by
    rw [RA]; simp only [runBlock, BInstr.run, fiA]
    rw [updz (by simp [upd]) h4, updz (by simp [upd]) h3, updz (by simp [upd]) h2, updz hz h1]
  -- `memcpy` of the hasher into the frame.
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa cX1 shf_at_e shf_at_12 (cb := BitVec.ofNat 32 memcpyStubAddress)
    (by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg m1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  have sp2 : reg n2 sp = F := by rw [r2 sp (by decide), sp1]
  have eF16 : F + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x180 := by rw [hFR, BitVec.add_assoc]; rfl
  have hF16 : (F + 0xFFFFFFF0).toNat = R.toNat + 0x180 := by rw [eF16, hRc _ (by omega)]
  have hSF : Sep S 0x68 F 0x68 := by rw [hFR]; exact sSF.subR (c := 0x190) (l := 0x68) (by omega)
  obtain ⟨n3, c3, pc3, sp3, _, mem3, K3⟩ := memcpy_correct n2 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 (0xE + 8)) F S 0x68
    (fun i hi => by show n2.mem _ = _; rw [mem2]; exact cM1 _ _ E.cMS (by decide) (by decide) i hi) (by decide) pc2
    (by rw [r2 a0 (by decide), a0_1]) (by rw [r2 a1 (by decide), a1_1]) (by rw [r2 a2 (by decide), a2_1])
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (by decide)
    (by
      rw [mem2, sp2]
      exact { code := cM1 _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by rw [hFn]; omega) (by decide) (by decide)
              hFC := data_code (by rw [hF16, hRn]; omega) (by decide) (by decide)
              hdF := by
                rw [eF16, hFR]
                have h := sep_offsets R (c := 0x190) (n := 0x68) (d := 0x180) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
                exact h
              hsF := by rw [eF16]; exact sSF.subR (c := 0x180) (l := 16) (by omega)
              hsep := hSF.symm
              hF := by rw [hF16, hRn]; have := E.hsp; omega
              hFw := by rw [hF16, hRn]; omega
              hdw := by rw [hFn]; omega
              hsw := by omega })
  rw [mem2, sp2, eF16] at mem3
  obtain ⟨MC, hMC⟩ : ∃ MC, n3.mem = MC := ⟨_, rfl⟩
  rw [hMC] at mem3
  have MCR : ∀ x, Sep R 0x200 x 1 → MC x = M0 x := fun x hx => by
    rw [mem3 x (Rx _ _ (by omega) x hx), copyBytes_sep (by rw [hFR]; exact Rx _ _ (by omega) x hx) (Nat.le_refl _),
      M1R x hx]
  have HC : HasherAt MC F msg := H.copy fun i hi => by
    rw [← add_ofNat_zero F] at ⊢
    rw [add_ofNat_zero, mem3 (F + BitVec.ofNat 32 i) (by
        rw [Fc]
        exact sep_offsets R (c := 0x180) (n := 16) (d := 0x190 + i) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)),
      copyBytes_in hi (by omega), M1R _ (sSF.sub (c := i) (l := 1) (by omega)).symm]
  have cMC := codeX MC MCR
  have cXC := cMC _ _ E.cX (by decide) (by decide)
  have u3 : St MC Q n3 0x16 (reg n3) := ⟨by rw [pc3], hMC, fun _ => rfl⟩
  have k3 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n3 r = reg n2 r := K3
  have sp3' : reg n3 sp = F := by rw [sp3, sp2]
  have s0_3 : reg n3 s0 = out := by
    rw [k3 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r2 s0 (by decide), s0_1]
  -- `finalize` of the copy.
  obtain ⟨n4, c4, u4⟩ := St.block fiB u3 cXC fiB_end (by simp [BlockOk, BInstr.ok, fiB])
  have RB : ∀ q, reg n4 q = (runBlock fiB (MC, reg n3)).2 q := u4.regs
  have u4' : St MC Q n4 0x1A (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n5, c5, pc5, mem5, regs5⟩ := u4'.callRa cXC shf_at_1a shf_at_1e (cb := BitVec.ofNat 32 shaFinalizeAddress)
    (by decide) (by decide)
  have r5 : ∀ q, q ≠ ra → reg n5 q = reg n4 q := fun q h => by rw [regs5]; exact updz u4'.zero h
  have KB : ∀ q, q ≠ a0 → q ≠ a1 → reg n4 q = reg n3 q := fun q h1 h2 => by
    rw [RB]; simp only [runBlock, BInstr.run, fiB]; rw [updz (by simp [upd]) h1, updz u3.zero h2]
  have eR : F + 0xFFFFFE70 = R := by rw [hFR, BitVec.add_assoc]; exact BitVec.add_zero R
  obtain ⟨n6, c6, pc6, sp6, K6, out6, fr6⟩ := shaFinalize_correct n5 (S := F) (out := out) (sp0 := F)
    (retAddr := Q + BitVec.ofNat 32 (0x1A + 8)) (msg := msg)
    { cF := by rw [mem5]; exact cMC _ _ E.cF (by decide) (by decide)
      cZ := by rw [mem5]; exact cMC _ _ E.cZ (by decide) (by decide)
      cBlk := by rw [mem5]; exact cMC _ _ E.cBlk (by decide) (by decide)
      cMs := by rw [mem5]; exact cMC _ _ E.cMs (by decide) (by decide)
      cMS := by rw [mem5]; exact cMC _ _ E.cMS (by decide) (by decide)
      cMB := by rw [mem5]; exact cMC _ _ E.cMB (by decide) (by decide)
      cC := by rw [mem5]; exact cMC _ _ E.cC (by decide) (by decide)
      cI := by rw [mem5]; exact cMC _ _ E.cI (by decide) (by decide)
      cK := fun i hi => by
        have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
        rw [mem5, MCR _ (sKF.sub (c := i) (l := 1) (by omega)).symm]; exact E.cK i hi
      hS := hFa4
      hSw := by rw [hFn]; omega
      hsp := hFa
      hspl := by rw [hFn]; omega
      hspw := by rw [hFn]; omega
      hOw := hOw
      sSF := by
        rw [eR, hFR]
        exact sep_offsets R (c := 0x190) (n := 0x68) (d := 0) (k := 0x190) (Or.inr (by omega)) (by omega) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h
      sOF := by rw [eR]; have h := sOF.subR (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h
      sOS := by rw [hFR]; exact sOF.subR (c := 0x190) (l := 0x68) (by omega)
      sKS := by rw [hFR]; exact sKF.subR (c := 0x190) (l := 0x68) (by omega)
      sKF := by rw [eR]; have h := sKF.subR (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h }
    pc5
    (by rw [r5 a0 (by decide), RB]; simp +decide only [runBlock, BInstr.run, fiB, upd_app, ↓reduceIte]
        rw [s0_3]; exact BitVec.zero_add _)
    (by rw [r5 a1 (by decide), RB]; simp +decide only [runBlock, BInstr.run, fiB, upd_app, ↓reduceIte]
        rw [sp3']; exact BitVec.zero_add _)
    (by rw [regs5]; simp +decide only [upd_app, ↓reduceIte]) (by decide)
    (by rw [r5 sp (by decide), KB sp (by decide) (by decide), sp3']) (by rw [mem5]; exact HC)
  rw [eR, mem5] at fr6
  obtain ⟨MF, hMF⟩ : ∃ MF, n6.mem = MF := ⟨_, rfl⟩
  rw [hMF] at fr6 out6
  -- The saved `ra` and `s0` survive in the frame.
  have slot : ∀ k, 0x68 ≤ k → k < 0x70 → MF (F + BitVec.ofNat 32 k) = M1 (F + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have rk : F + BitVec.ofNat 32 k = R + BitVec.ofNat 32 (0x190 + k) := Fc k
    rw [fr6 _ (by
        rw [rk]
        exact sep_offsets R (c := 0) (n := 0x190) (d := 0x190 + k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h)
        (by
          exact sep_offsets F (c := 0) (n := 0x68) (d := k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
            |> fun h => by rwa [add_ofNat_zero] at h)
        (by rw [rk]; exact sOF.subR (c := 0x190 + k) (l := 1) (by omega)),
      mem3 _ (by rw [rk]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (by
        exact sep_offsets F (c := 0) (n := 0x68) (d := k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h) (Nat.le_refl _)]
  have ldS : ∀ c, 0x68 ≤ c → c + 4 ≤ 0x70 → memLoad32 MF (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact slot _ (by omega) (by omega)
  have vRa : memLoad32 MF (F + 0x6C) = reg m ra := by
    rw [show F + (0x6C : Word) = F + BitVec.ofNat 32 0x6C from rfl, ldS 0x6C (by omega) (by omega), ← hM1]
    show memLoad32 (memStore32 (memStore32 M0 (F + 0x6C) (reg m ra)) (F + 0x68) (reg m s0)) (F + 0x6C) = _
    rw [memLoad32_store32_sep (a := F + 0x68) (b := F + 0x6C)
      (sep_offsets F (c := 0x68) (n := 4) (d := 0x6C) (k := 4) (Or.inl (by omega)) (by omega) (by omega)),
      memLoad32_store32_same]
  have vS0 : memLoad32 MF (F + 0x68) = reg m s0 := by
    rw [show F + (0x68 : Word) = F + BitVec.ofNat 32 0x68 from rfl, ldS 0x68 (by omega) (by omega), ← hM1]
    show memLoad32 (memStore32 (memStore32 M0 (F + 0x6C) (reg m ra)) (F + 0x68) (reg m s0)) (F + 0x68) = _
    rw [memLoad32_store32_same]
  have cMF : CodeIn MF Q shaFinishCode := fun i hi => by
    have hx : Sep R 0x200 (Q + BitVec.ofNat 32 i) 1 :=
      (data_code (a := R) (n := 0x200) (b := Q) (l := shaFinishCode.length) (by rw [hRn]; omega) (by decide)
        (by decide)).subR (c := i) (l := 1) (by omega)
    rw [fr6 _ (hx.sub (c := 0) (l := 0x190) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
        (by rw [hFR]; exact Rx _ _ (by omega) _ hx)
        ((data_code (b := Q) (l := shaFinishCode.length) hOw (by decide) (by decide)).subR (c := i) (l := 1)
          (by omega)), MCR _ hx]
    exact E.cX i hi
  -- The epilogue.
  have u6 : St MF Q n6 0x22 (reg n6) := ⟨by rw [pc6], hMF, fun _ => rfl⟩
  have sp6' : reg n6 sp = F := sp6
  obtain ⟨n7, c7, u7⟩ := St.block fiC u6 cMF fiC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fiC, upd_app, ↓reduceIte, and_true]
    rw [sp6']; exact ⟨a6C, a68⟩)
  have RC : ∀ q, reg n7 q = (runBlock fiC (MF, reg n6)).2 q := u7.regs
  have u7' : St MF Q n7 0x28 (reg n7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7'.jalr cMF shf_at_28
  have ra7 : reg n7 ra = retAddr := by
    rw [RC]; simp +decide only [runBlock, BInstr.run, fiC, upd_app, ↓reduceIte]; rw [sp6', vRa, hra]
  have sp7 : reg n7 sp = sp0 := by
    rw [RC]; simp +decide only [runBlock, BInstr.run, fiC, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp6', ← hF]
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have s0_7 : reg n7 s0 = reg m s0 := by
    rw [RC]; simp +decide only [runBlock, BInstr.run, fiC, upd_app, ↓reduceIte]; rw [sp6', vS0]
  have k6 : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
      r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
      r ≠ (31 : Fin 32) → reg n6 r = reg n5 r := K6
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.single d8))))))), ?_, ?_,
    fun r q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, fun x hx hy => ?_⟩
  · rw [pc8, ra7, add_lit_zero, hret]
  · rw [regs8, sp7]
  · rw [regs8]
    by_cases q1 : r = ra
    · subst q1; rw [ra7, hra]
    by_cases q2 : r = sp
    · subst q2; rw [sp7, hsp]
    by_cases q8 : r = s0
    · subst q8; exact s0_7
    rw [RC]; simp only [runBlock, BInstr.run, fiC]
    rw [updz (by simp [upd]) q2, updz (by simp [upd]) q8, updz u6.zero q1,
      k6 r q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r5 r q1, KB r q10 q11,
      k3 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r2 r q1, K1 r q2 q8 q10 q12]
  · rw [mem8]; exact out6
  · rw [mem8, fr6 x (by have h := hx.sub (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h)
      (by rw [hFR]; exact Rx _ _ (by omega) x hx) hy, MCR x hx]

end C3.RV32
