import C3BootProofs.Proofs.Sha2Parts
import C3BootProofs.Spec.Merkle

/-!
# `c3_verify::merkle::node_hash`, as compiled

`node_hash` writes three slice descriptors on its stack (the image's one
byte `0x01`, then the 32-byte left and right hashes) and calls
`sha256_parts`, so it computes RFC 6962's interior node hash.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem nh_at_22 : fetchRel merkleNodeHashCode 0x22 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem nh_at_26 : fetchRel merkleNodeHashCode 0x26 = some (.jalr ra ra 0x56, 4) := by decide
theorem nh_at_2e : fetchRel merkleNodeHashCode 0x2E = some (.jalr x0 ra 0x0, 2) := by decide

def nhA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFE0, .sw sp ra 0x1C, .lui a3 0x3FCC4000, .aluImm .add a3 a3 0x7D7, .aluImm .add a4 x0 0x1,
    .aluImm .add a5 x0 0x20, .sw sp a3 0x4, .sw sp a4 0x8, .sw sp a1 0xC, .sw sp a5 0x10, .sw sp a2 0x14,
    .sw sp a5 0x18, .aluImm .add a1 sp 0x4, .aluImm .add a2 x0 0x3]

def nhC : List BInstr := [.lw ra sp 0x1C, .aluImm .add sp sp 0x20]

theorem nhA_end : blockEnd merkleNodeHashCode 0 nhA = some 0x22 := by decide
theorem nhC_end : blockEnd merkleNodeHashCode 0x2A nhC = some 0x2E := by decide
end

/-- Where `node_hash` runs: its code, the prefix byte, and `sha256_parts`'s
callees; the left and right hashes, the output, and 0x290 bytes of stack
below `sp0`, all below 0x40000000; the hashes, the output, the prefix byte,
the initial hash value, and the round constants each apart from the stack. -/
structure NodeEnv (M : Word → BitVec 8) (out L Rt sp0 : Word) : Prop where
  cN : CodeIn M (BitVec.ofNat 32 merkleNodeHashAddress) merkleNodeHashCode
  cPre : CodeIn M (BitVec.ofNat 32 merklePrefixAddress) merklePrefixData
  cX : CodeIn M (BitVec.ofNat 32 sha256PartsAddress) sha256PartsCode
  cIV : CodeIn M (BitVec.ofNat 32 shaIVAddress) shaIVData
  cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cUBlk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cFBlk : CodeIn M (BitVec.ofNat 32 shaFinBlockAddress) shaFinBlockCode
  cMs : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hsp : sp0.toNat % 16 = 0
  hspl : 0x290 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hOw : out.toNat + 32 ≤ 0x40000000
  hLw : L.toNat + 32 ≤ 0x40000000
  hRw : Rt.toNat + 32 ≤ 0x40000000
  sOF : Sep out 32 (sp0 + 0xFFFFFD70) 0x290
  sLF : Sep L 32 (sp0 + 0xFFFFFD70) 0x290
  sRF : Sep Rt 32 (sp0 + 0xFFFFFD70) 0x290
  sPF : Sep (BitVec.ofNat 32 merklePrefixAddress) 1 (sp0 + 0xFFFFFD70) 0x290
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFD70) 0x290
  sIF : Sep (BitVec.ofNat 32 shaIVAddress) 32 (sp0 + 0xFFFFFD70) 0x290

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `c3_crypto::merkle::node_hash`.** Called with the 32-byte
hashes at `L` and `Rt` and a 32-byte output at `out`, it writes RFC 6962's
interior node hash of the two to `out`. It returns to `retAddr` with `sp`
restored and the callee-saved registers kept, and changes no memory outside
the output and 0x290 bytes of stack below `sp`. -/
theorem merkleNodeHash_correct (m : Machine) {out L Rt sp0 retAddr : Word}
    (E : NodeEnv m.mem out L Rt sp0) (hpc : m.pc = BitVec.ofNat 32 merkleNodeHashAddress)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = L) (ha2 : reg m a2 = Rt)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
        r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
        r ≠ (31 : Fin 32) → reg m' r = reg m r) ∧
      memBytes m'.mem out 32 = nodeHash (memBytes m.mem L 32) (memBytes m.mem Rt 32) ∧
      ∀ x, Sep (sp0 + 0xFFFFFD70) 0x290 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  let Q := BitVec.ofNat 32 merkleNodeHashAddress
  let M0 := m.mem
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFD70 = R := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFE0 = G := ⟨_, rfl⟩
  have sOF := E.sOF; have sLF := E.sLF; have sRF := E.sRF; have sPF := E.sPF; have sKF := E.sKF
  have sIF := E.sIF
  rw [hR] at sOF sLF sRF sPF sKF sIF ⊢
  have hspw := E.hspw
  have hspl := E.hspl
  have hRn : R.toNat = sp0.toNat - 0x290 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFD70 : Word).toNat = 2 ^ 32 - 0x290 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x290 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hGR : G = R + BitVec.ofNat 32 0x270 := by rw [← hG, ← hR, BitVec.add_assoc]; rfl
  have Gc : ∀ c, G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x270 + c) := fun c => by rw [hGR, add_ofNat_assoc]
  have hGn : G.toNat = sp0.toNat - 0x20 := by rw [hGR, hRc _ (by omega), hRn]; omega
  have hGa : G.toNat % 16 = 0 := by rw [hGn]; have := E.hsp; omega
  have hGa4 : G.toNat % 4 = 0 := by omega
  have Rx : ∀ c l, c + l ≤ 0x290 → ∀ x, Sep R 0x290 x 1 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) h
  have Rd : ∀ c l, c + l ≤ 0x290 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk =>
    data_code (by rw [hRc _ (by omega)]; omega) hb hbk
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x290 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  -- The frame: `ra`, then the three slice descriptors.
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  have eG : aluEval .add (reg m sp) 0xFFFFFFE0 = G := by rw [hsp, ← hG]; rfl
  have slot : ∀ c, c + 4 ≤ 0x20 → c % 4 = 0 →
      (G + BitVec.ofNat 32 c).toNat % 4 = 0 ∧ Sep (G + BitVec.ofNat 32 c) 4 Q merkleNodeHashCode.length :=
    fun c h1 h2 => ⟨aligned_add hGa4 h2, by rw [Gc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide)⟩
  obtain ⟨m1, c1, u1⟩ := St.block nhA st0 E.cN nhA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, nhA, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add]; rw [hsp, hG]
    exact ⟨slot 0x1C (by omega) (by omega), slot 4 (by omega) (by omega), slot 8 (by omega) (by omega),
      slot 0xC (by omega) (by omega), slot 0x10 (by omega) (by omega), slot 0x14 (by omega) (by omega),
      slot 0x18 (by omega) (by omega)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M0
      (G + BitVec.ofNat 32 0x1C) (reg m ra)) (G + BitVec.ofNat 32 0x4) (BitVec.ofNat 32 merklePrefixAddress))
      (G + BitVec.ofNat 32 0x8) 1) (G + BitVec.ofNat 32 0xC) L) (G + BitVec.ofNat 32 0x10) 0x20)
      (G + BitVec.ofNat 32 0x14) Rt) (G + BitVec.ofNat 32 0x18) 0x20 = M1 := ⟨_, rfl⟩
  have eM1 : (runBlock nhA (M0, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, nhA, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [hsp, hG, ha1, ha2, ← hM1]; rfl
  have RA : ∀ q, reg m1 q = (runBlock nhA (M0, reg m)).2 q := u1.regs
  have u1' : St M1 Q m1 0x22 (reg m1) := ⟨u1.pc, by rw [u1.mem, eM1], fun _ => rfl⟩
  have M1R : ∀ x, Sep R 0x290 x 1 → M1 x = M0 x := fun x hx => by
    have g : ∀ c, c + 4 ≤ 0x20 → Sep (G + BitVec.ofNat 32 c) 4 x 1 := fun c h => by
      rw [Gc]; exact Rx _ _ (by omega) x hx
    rw [← hM1, memStore32_get_sep (g 0x18 (by omega)), memStore32_get_sep (g 0x14 (by omega)),
      memStore32_get_sep (g 0x10 (by omega)), memStore32_get_sep (g 0xC (by omega)),
      memStore32_get_sep (g 0x8 (by omega)), memStore32_get_sep (g 0x4 (by omega)),
      memStore32_get_sep (g 0x1C (by omega))]
  have so : ∀ c d, c < 0x20 → d < 0x20 → c + 4 ≤ d ∨ d + 4 ≤ c →
      Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 :=
    fun c d hc hd h => sep_offsets G h (by omega) (by omega)
  -- The descriptors, as `sha256_parts` reads them.
  have d0 : memLoad32 M1 (G + BitVec.ofNat 32 4) = BitVec.ofNat 32 merklePrefixAddress := by
    rw [← hM1, memLoad32_store32_sep (so 0x18 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x14 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x10 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0xC 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x8 4 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have d1 : memLoad32 M1 (G + BitVec.ofNat 32 8) = 1 := by
    rw [← hM1, memLoad32_store32_sep (so 0x18 8 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x14 8 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x10 8 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0xC 8 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have d2 : memLoad32 M1 (G + BitVec.ofNat 32 0xC) = L := by
    rw [← hM1, memLoad32_store32_sep (so 0x18 0xC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x14 0xC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x10 0xC (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have d3 : memLoad32 M1 (G + BitVec.ofNat 32 0x10) = 0x20 := by
    rw [← hM1, memLoad32_store32_sep (so 0x18 0x10 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x14 0x10 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have d4 : memLoad32 M1 (G + BitVec.ofNat 32 0x14) = Rt := by
    rw [← hM1, memLoad32_store32_sep (so 0x18 0x14 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have d5 : memLoad32 M1 (G + BitVec.ofNat 32 0x18) = 0x20 := by rw [← hM1, memLoad32_store32_same]
  have eP : ∀ c, G + 0x4 + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (4 + c) := fun c => add_ofNat_assoc G 4 c
  have pp0 : partPtr M1 (G + 0x4) 0 = BitVec.ofNat 32 merklePrefixAddress := by
    unfold partPtr; rw [eP]; exact d0
  have pl0 : partLen M1 (G + 0x4) 0 = 1 := by
    unfold partLen; rw [eP]; show (memLoad32 M1 (G + BitVec.ofNat 32 8)).toNat = 1; rw [d1]; rfl
  have pp1 : partPtr M1 (G + 0x4) 1 = L := by unfold partPtr; rw [eP]; exact d2
  have pl1 : partLen M1 (G + 0x4) 1 = 32 := by
    unfold partLen; rw [eP]; show (memLoad32 M1 (G + BitVec.ofNat 32 0x10)).toNat = 32; rw [d3]; rfl
  have pp2 : partPtr M1 (G + 0x4) 2 = Rt := by unfold partPtr; rw [eP]; exact d4
  have pl2 : partLen M1 (G + 0x4) 2 = 32 := by
    unfold partLen; rw [eP]; show (memLoad32 M1 (G + BitVec.ofNat 32 0x18)).toNat = 32; rw [d5]; rfl
  have pre : memBytes M1 (BitVec.ofNat 32 merklePrefixAddress) 1 = [1] := by
    unfold memBytes
    show [(M1 (BitVec.ofNat 32 merklePrefixAddress + BitVec.ofNat 32 0)).toNat] = [1]
    rw [M1R _ (sPF.sub (c := 0) (l := 1) (by omega)).symm]
    show [(m.mem _).toNat] = [1]
    rw [E.cPre 0 (by decide)]; rfl
  have bL : memBytes M1 L 32 = memBytes M0 L 32 :=
    memBytes_congr fun i hi => M1R _ (sLF.sub (c := i) (l := 1) (by omega)).symm
  have bR : memBytes M1 Rt 32 = memBytes M0 Rt 32 :=
    memBytes_congr fun i hi => M1R _ (sRF.sub (c := i) (l := 1) (by omega)).symm
  have hParts : partsBytes M1 (G + 0x4) 3 = 0x01 :: memBytes M0 L 32 ++ memBytes M0 Rt 32 := by
    show (([] ++ memBytes M1 (partPtr M1 (G + 0x4) 0) (partLen M1 (G + 0x4) 0)) ++
      memBytes M1 (partPtr M1 (G + 0x4) 1) (partLen M1 (G + 0x4) 1)) ++
      memBytes M1 (partPtr M1 (G + 0x4) 2) (partLen M1 (G + 0x4) 2) = _
    rw [pp0, pl0, pp1, pl1, pp2, pl2, pre, bL, bR, List.nil_append, List.singleton_append, List.cons_append]
  -- `sha256_parts` over them.
  have cM1 := codeX M1 M1R
  have cN1 := cM1 _ _ E.cN (by decide) (by decide)
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa cN1 nh_at_22 nh_at_26 (cb := BitVec.ofNat 32 sha256PartsAddress)
    (by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg m1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  have eG2 : G + 0xFFFFFD90 = R := by rw [hGR, BitVec.add_assoc]; exact BitVec.add_zero R
  have sGG : ∀ {b : Word} {l : Nat}, Sep b l R 0x290 → Sep b l (G + 0xFFFFFD90) 0x270 := fun h => by
    rw [eG2]; exact h.subR (c := 0) (l := 0x270) (by omega) |> fun h' => by rwa [add_ofNat_zero] at h'
  obtain ⟨n3, c3, pc3, sp3, K3, out3, fr3⟩ := sha256Parts_correct n2 (out := out) (P := G + 0x4) (sp0 := G) (k := 3)
    (retAddr := Q + BitVec.ofNat 32 (0x22 + 8))
    (by
      rw [mem2]
      exact { cX := cM1 _ _ E.cX (by decide) (by decide)
              cIV := fun i hi => by
                have hi' : i < 32 := by rw [show shaIVData.length = 32 from rfl] at hi; exact hi
                rw [M1R _ (sIF.sub (c := i) (l := 1) (by omega)).symm]; exact E.cIV i hi
              cU := cM1 _ _ E.cU (by decide) (by decide)
              cUBlk := cM1 _ _ E.cUBlk (by decide) (by decide)
              cF := cM1 _ _ E.cF (by decide) (by decide)
              cZ := cM1 _ _ E.cZ (by decide) (by decide)
              cFBlk := cM1 _ _ E.cFBlk (by decide) (by decide)
              cMs := cM1 _ _ E.cMs (by decide) (by decide)
              cMS := cM1 _ _ E.cMS (by decide) (by decide)
              cMB := cM1 _ _ E.cMB (by decide) (by decide)
              cC := cM1 _ _ E.cC (by decide) (by decide)
              cI := cM1 _ _ E.cI (by decide) (by decide)
              cK := fun i hi => by
                have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
                rw [M1R _ (sKF.sub (c := i) (l := 1) (by omega)).symm]; exact E.cK i hi
              hsp := hGa
              hspl := by rw [hGn]; omega
              hspw := by rw [hGn]; omega
              hOw := E.hOw
              hP := aligned_add hGa4 (k := 4) (by decide)
              hPw := by
                rw [show G + (0x4 : Word) = G + BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat, hGn]
                omega
              sPF := by
                rw [eG2, show G + (0x4 : Word) = G + BitVec.ofNat 32 4 from rfl, Gc]
                exact sep_offsets R (c := 0x270 + 4) (n := 8 * 3) (d := 0) (k := 0x270) (Or.inr (by omega)) (by omega)
                  (by omega) |> fun h => by rwa [add_ofNat_zero] at h
              hlen := by rw [hParts]; simp only [List.length_cons, List.length_append, memBytes_length]; omega
              parts := fun i hi => by
                rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
                · rw [pp0, pl0]
                  exact ⟨by decide, by decide, sGG sPF⟩
                · rw [pp1, pl1]
                  exact ⟨by decide, E.hLw, sGG sLF⟩
                · rw [pp2, pl2]
                  exact ⟨by decide, E.hRw, sGG sRF⟩
              sOF := sGG sOF
              sKF := sGG sKF
              sIF := sGG sIF })
    pc2 (by rw [r2 a0 (by decide), RA]; simp +decide only [runBlock, BInstr.run, nhA, upd_app, ↓reduceIte]; exact ha0)
    (by rw [r2 a1 (by decide), RA]; simp +decide only [runBlock, BInstr.run, nhA, upd_app, ↓reduceIte]
        simp only [ev_add]; rw [hsp, hG])
    (by rw [r2 a2 (by decide), RA]; simp +decide only [runBlock, BInstr.run, nhA, upd_app, ↓reduceIte]; try rfl)
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (by decide)
    (by rw [r2 sp (by decide), RA]; simp +decide only [runBlock, BInstr.run, nhA, upd_app, ↓reduceIte]
        simp only [ev_add]; rw [hsp, hG])
  rw [mem2, hParts] at out3
  rw [mem2, eG2] at fr3
  obtain ⟨MF, hMF⟩ : ∃ MF, n3.mem = MF := ⟨_, rfl⟩
  rw [hMF] at out3 fr3
  have fG : ∀ x, Sep R 0x270 x 1 → Sep out 32 x 1 → MF x = M1 x := fr3
  have vRa : memLoad32 MF (G + BitVec.ofNat 32 0x1C) = reg m ra := by
    have e : memLoad32 MF (G + BitVec.ofNat 32 0x1C) = memLoad32 M1 (G + BitVec.ofNat 32 0x1C) :=
      memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact fG _ (by
          rw [Gc]
          exact sep_offsets R (c := 0) (n := 0x270) (d := 0x270 + (0x1C + j)) (k := 1) (Or.inl (by omega)) (by omega)
            (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
        (by rw [Gc]; exact sOF.subR (c := 0x270 + (0x1C + j)) (l := 1) (by omega))
    rw [e, ← hM1, memLoad32_store32_sep (so 0x18 0x1C (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x14 0x1C (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x10 0x1C (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0xC 0x1C (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x8 0x1C (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 4 0x1C (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have MFR : ∀ x, Sep R 0x290 x 1 → Sep out 32 x 1 → MF x = M0 x := fun x hx hy => by
    rw [fG x (hx.sub (c := 0) (l := 0x270) (by omega) |> fun h => by rwa [add_ofNat_zero] at h) hy, M1R x hx]
  have cNF : CodeIn MF Q merkleNodeHashCode := fun i hi => by
    have hx : Sep R 0x290 (Q + BitVec.ofNat 32 i) 1 :=
      (data_code (a := R) (n := 0x290) (b := Q) (l := merkleNodeHashCode.length) (by rw [hRn]; omega) (by decide)
        (by decide)).subR (c := i) (l := 1) (by omega)
    rw [MFR _ hx ((data_code (b := Q) (l := merkleNodeHashCode.length) E.hOw (by decide) (by decide)).subR (c := i)
      (l := 1) (by omega))]
    exact E.cN i hi
  -- The epilogue.
  have u3 : St MF Q n3 0x2A (reg n3) := ⟨by rw [pc3], hMF, fun _ => rfl⟩
  have sp3' : reg n3 sp = G := by
    rw [sp3]
  obtain ⟨n4, c4, u4⟩ := St.block nhC u3 cNF nhC_end (by
    simp +decide only [BlockOk, BInstr.ok, nhC, and_true]
    rw [sp3']; exact aligned_add hGa4 (k := 0x1C) (by decide))
  have RC : ∀ q, reg n4 q = (runBlock nhC (MF, reg n3)).2 q := u4.regs
  have u4' : St MF Q n4 0x2E (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4'.jalr cNF nh_at_2e
  have ra4 : reg n4 ra = retAddr := by
    rw [RC]; simp +decide only [runBlock, BInstr.run, nhC, upd_app, ↓reduceIte]; rw [sp3']; exact vRa.trans hra
  have sp4 : reg n4 sp = sp0 := by
    rw [RC]; simp +decide only [runBlock, BInstr.run, nhC, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp3', ← hG]
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have k3 : ∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
      r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
      r ≠ (31 : Fin 32) → reg n3 r = reg n2 r := fun r _ => K3 r
  refine ⟨n5, c1.trans (c2.trans (c3.trans (c4.trans (.single d5)))), ?_, ?_,
    fun r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, fun x hx hy => ?_⟩
  · rw [pc5, ra4, add_lit_zero, hret]
  · rw [regs5, sp4]
  · rw [regs5]
    by_cases q1 : r = ra
    · subst q1; rw [ra4, hra]
    by_cases q2 : r = sp
    · subst q2; rw [sp4, hsp]
    rw [RC]; simp only [runBlock, BInstr.run, nhC]
    rw [updz (by simp [upd]) q2, updz u3.zero q1, k3 r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
      r2 r q1, RA]
    simp only [runBlock, BInstr.run, nhA]
    rw [updz (by simp [upd]) q12, updz (by simp [upd]) q11, updz (by simp [upd]) q15, updz (by simp [upd]) q14,
      updz (by simp [upd]) q13, updz (by simp [upd]) q13, updz hz q2]
  · rw [mem5, out3]; rfl
  · rw [mem5, MFR x hx hy]

end C3.RV32
