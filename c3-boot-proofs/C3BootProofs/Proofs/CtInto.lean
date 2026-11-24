import C3BootProofs.Proofs.CondSelect
import C3BootProofs.Proofs.DerTlv
import C3BootProofs.Image.BootloaderData2
import C3BootProofs.Image.BootloaderData5

/-!
# `CtOption<AffinePoint>` into `ctutils::CtOption`, as compiled

The conversion unwraps the `subtle` option with `unwrap_or`, defaulting to
the identity point in the image's read-only data, and copies the choice
byte after the point. So the result holds the point when the choice is 1 and
the identity otherwise, followed by the same choice.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem cia_at_0 : fetchRel ctIntoAffine384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem cia_at_2 : fetchRel ctIntoAffine384Code 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem cia_at_4 : fetchRel ctIntoAffine384Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem cia_at_6 : fetchRel ctIntoAffine384Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem cia_at_8 : fetchRel ctIntoAffine384Code 0x8 = some (.load .lbu (9 : Fin 32) a1 0x64, 4) := by decide
theorem cia_at_c : fetchRel ctIntoAffine384Code 0xC = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem cia_at_e : fetchRel ctIntoAffine384Code 0xE = some (.lui a2 0x3FCC4000, 4) := by decide
theorem cia_at_12 : fetchRel ctIntoAffine384Code 0x12 = some (.aluImm .add a2 a2 0x3C8, 4) := by decide
theorem cia_at_16 : fetchRel ctIntoAffine384Code 0x16 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem cia_at_1a : fetchRel ctIntoAffine384Code 0x1A = some (.jalr ra ra 0xFFFFFEDC, 4) := by decide
theorem cia_at_1e : fetchRel ctIntoAffine384Code 0x1E = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0x64, 4) := by decide
theorem cia_at_22 : fetchRel ctIntoAffine384Code 0x22 = some (.load .lw ra sp 0xC, 2) := by decide
theorem cia_at_24 : fetchRel ctIntoAffine384Code 0x24 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem cia_at_26 : fetchRel ctIntoAffine384Code 0x26 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem cia_at_28 : fetchRel ctIntoAffine384Code 0x28 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem cia_at_2a : fetchRel ctIntoAffine384Code 0x2A = some (.jalr x0 ra 0x0, 2) := by decide
theorem cib_at_0 : fetchRel ctIntoAffine256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem cib_at_2 : fetchRel ctIntoAffine256Code 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem cib_at_4 : fetchRel ctIntoAffine256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem cib_at_6 : fetchRel ctIntoAffine256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem cib_at_8 : fetchRel ctIntoAffine256Code 0x8 = some (.load .lbu (9 : Fin 32) a1 0x44, 4) := by decide
theorem cib_at_c : fetchRel ctIntoAffine256Code 0xC = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem cib_at_e : fetchRel ctIntoAffine256Code 0xE = some (.lui a2 0x3FCC4000, 4) := by decide
theorem cib_at_12 : fetchRel ctIntoAffine256Code 0x12 = some (.aluImm .add a2 a2 0x42C, 4) := by decide
theorem cib_at_16 : fetchRel ctIntoAffine256Code 0x16 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem cib_at_1a : fetchRel ctIntoAffine256Code 0x1A = some (.jalr ra ra 0x1EA, 4) := by decide
theorem cib_at_1e : fetchRel ctIntoAffine256Code 0x1E = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0x44, 4) := by decide
theorem cib_at_22 : fetchRel ctIntoAffine256Code 0x22 = some (.load .lw ra sp 0xC, 2) := by decide
theorem cib_at_24 : fetchRel ctIntoAffine256Code 0x24 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem cib_at_26 : fetchRel ctIntoAffine256Code 0x26 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem cib_at_28 : fetchRel ctIntoAffine256Code 0x28 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem cib_at_2a : fetchRel ctIntoAffine256Code 0x2A = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem code_hi {b : Word} {l i : Nat} (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) (hi : i < l) :
    0x40000000 ≤ (b + BitVec.ofNat 32 i).toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Code that a memory keeps above `0x40000000`. -/
theorem CodeIn.hi {M M' : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M b code)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) (hb : 0x40000000 ≤ b.toNat)
    (hbl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn M' b code := fun i hi => by
  rw [h _ (code_hi hb hbl hi)]; exact hc i hi

def ciaPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sw sp ra 0xC, .sw sp (8 : Fin 32) 0x8, .sw sp (9 : Fin 32) 0x4,
    .lbu (9 : Fin 32) a1 0x64, .alu .add (8 : Fin 32) x0 a0, .lui a2 0x3FCC4000, .aluImm .add a2 a2 0x3C8]
def ciaEpi : List BInstr :=
  [.lw ra sp 0xC, .lw (8 : Fin 32) sp 0x8, .lw (9 : Fin 32) sp 0x4, .aluImm .add sp sp 0x10]

set_option maxRecDepth 20000 in
theorem ciaPro_end : blockEnd ctIntoAffine384Code 0 ciaPro = some 0x16 := by decide
set_option maxRecDepth 20000 in
theorem ciaEpi_end : blockEnd ctIntoAffine384Code 0x22 ciaEpi = some 0x2A := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The compiled conversion of `CtOption<AffinePoint<NistP384>>` into
`ctutils::CtOption`**, from the option at `s` to `out`: the 0x61 bytes of
the point are `s`'s when its choice byte is 1 and the identity's otherwise,
as `unwrapOr384_correct` says, and the choice byte follows at `out + 0x64`.
It changes no memory outside the result and 0x90 bytes of stack below
`sp`. -/
theorem ctIntoAffine384_correct (m : Machine) {out s sp0 retAddr : Word}
    (hc : CodeIn m.mem (BitVec.ofNat 32 ctIntoAffine384Address) ctIntoAffine384Code)
    (env : UOEnv m.mem (BitVec.ofNat 32 unwrapOr384Address) (sp0 + 0xFFFFFFF0) out s (img% p384AffineIdentityAddress))
    (hpc : m.pc = BitVec.ofNat 32 ctIntoAffine384Address) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = s) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hch : m.mem (s + 0x64) = 0 ∨ m.mem (s + 0x64) = 1)
    (hspl : 0x90 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000) (how : out.toNat + 0x65 ≤ 0x40000000)
    (sOW : Sep out 0x65 (sp0 + 0xFFFFFFF0) 16) (sSW : Sep s 0x65 (sp0 + 0xFFFFFFF0) 16)
    (sDW : Sep (img% p384AffineIdentityAddress : Word) 0x61 (sp0 + 0xFFFFFFF0) 16) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 12 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x64) = 1 then memLoad32 m.mem (s + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem ((img% p384AffineIdentityAddress) + BitVec.ofNat 32 (4 * i))) ∧
      (∀ i, i < 12 → memLoad32 m'.mem (out + 0x30 + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x64) = 1 then memLoad32 m.mem (s + 0x30 + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem ((img% p384AffineIdentityAddress) + 0x30 + BitVec.ofNat 32 (4 * i))) ∧
      m'.mem (out + 0x60) = (if m.mem (s + 0x64) = 1 then m.mem (s + 0x60) else m.mem ((img% p384AffineIdentityAddress) + 0x60)) ∧
      m'.mem (out + 0x64) = m.mem (s + 0x64) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF70) 0x90 y 1 → Sep out 0x65 y 1 → m'.mem y = m.mem y := by
  let Q := BitVec.ofNat 32 ctIntoAffine384Address
  let P := BitVec.ofNat 32 unwrapOr384Address
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hG] at env sOW sSW sDW
  have hGn : G.toNat = sp0.toNat - 16 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl]; omega
  have hGa : G.toNat % 4 = 0 := env.hsp
  have hGc : ∀ c, c ≤ 16 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hQn : Q.toNat = (img% ctIntoAffine384Address) := by decide
  have st0 : St m.mem Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  have slotP : ∀ (o : Nat), o + 4 ≤ 16 → o % 4 = 0 →
      (G + BitVec.ofNat 32 o).toNat % 4 = 0 ∧ Sep (G + BitVec.ofNat 32 o) 4 Q ctIntoAffine384Code.length :=
    fun o h2 h3 => ⟨aligned_add hGa h3, sep_of_le (by rw [hGc _ (by omega), hQn]; omega) (by rw [hQn]; decide)⟩
  obtain ⟨n1, c1, u1⟩ := St.block ciaPro st0 hc ciaPro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ciaPro, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add]; rw [hsp, hG]
    exact ⟨slotP 0xC (by omega) (by omega), slotP 8 (by omega) (by omega), slotP 4 (by omega) (by omega)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 (memStore32 m.mem (G + 0xC) retAddr)
      (G + 8) (reg m (8 : Fin 32))) (G + 4) (reg m (9 : Fin 32)) = M1 := ⟨_, rfl⟩
  have eM1 : (runBlock ciaPro (m.mem, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, ciaPro, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [hsp, hG, hra, hM1]
  have M1o : ∀ x, Sep G 16 x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1]
    show memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _ x = _
    rw [memStore32_get_sep (hx.sub (c := 4) (l := 4) (by omega)), memStore32_get_sep (hx.sub (c := 8) (l := 4)
      (by omega)), memStore32_get_sep (hx.sub (c := 0xC) (l := 4) (by omega))]
  have M1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M1 x = m.mem x := fun x hx =>
    M1o x (sep_of_le (by omega) (by have := x.isLt; omega))
  have R1 : ∀ q, reg n1 q = (runBlock ciaPro (m.mem, reg m)).2 q := u1.regs
  have u1' : St M1 Q n1 0x16 (reg n1) := ⟨u1.pc, by rw [u1.mem, eM1], fun _ => rfl⟩
  have hc1 : CodeIn M1 Q ctIntoAffine384Code := hc.hi M1hi (by decide) (by decide)
  have sp1 : reg n1 sp = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, ciaPro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp, hG]
  have s01 : reg n1 s0 = out := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, ciaPro, upd_app, ↓reduceIte]; simp only [ev_add]
    exact (BitVec.zero_add _).trans ha0
  have hb : M1 (s + 0x64) = m.mem (s + 0x64) := M1o _ (sSW.sub (c := 0x64) (l := 1) (by omega)).symm
  have s11 : reg n1 s1 = (m.mem (s + 0x64)).zeroExtend 32 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, ciaPro, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [ha1, hsp, hG, hra, hM1, hb]
  have a21 : reg n1 a2 = (img% p384AffineIdentityAddress) := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, ciaPro, upd_app, ↓reduceIte]
  have K1 : ∀ q, q ≠ sp → q ≠ s0 → q ≠ s1 → q ≠ a2 → reg n1 q = reg m q := fun q h2 h8 h9 h12 => by
    rw [R1]; simp only [runBlock, BInstr.run, ciaPro]
    rw [updz (by simp [upd]) h12, updz (by simp [upd]) h12, updz (by simp [upd]) h8, updz (by simp [upd]) h9,
      updz hz h2]
  have env1 : UOEnv M1 P G out s (img% p384AffineIdentityAddress) :=
    { env with
      cod := env.cod.hi M1hi (by decide) (by decide)
      cs := env.cs.hi M1hi (by decide) (by decide)
      stub := env.stub.hi M1hi (by decide) (by decide)
      body := env.body.hi M1hi (by decide) (by decide)
      cta := env.cta.hi M1hi (by decide) (by decide)
      sca := env.sca.hi M1hi (by decide) (by decide) }
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc1 cia_at_16 cia_at_1a
    (show Q + BitVec.ofNat 32 0x16 + 0xFFFFE000 + 0xFFFFFEDC = P by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  obtain ⟨n3, c3, pc3, sp3, w1, w2, b60, keep3, fr3⟩ := unwrapOr384_correct n2
    (retAddr := Q + BitVec.ofNat 32 (0x16 + 8)) (by rw [mem2]; exact env1) pc2
    (by rw [r2 sp (by decide), sp1]) (by rw [r2 a0 (by decide), K1 a0 (by decide) (by decide) (by decide) (by decide), ha0])
    (by rw [r2 a1 (by decide), K1 a1 (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [r2 a2 (by decide), a21]) (by rw [mem2, hb]; exact hch)
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at Q (by decide) _ (by omega)))
  rw [mem2] at w1 w2 b60 fr3
  obtain ⟨M2, hM2⟩ : ∃ M2, n3.mem = M2 := ⟨_, rfl⟩
  rw [hM2] at w1 w2 b60 fr3
  have eGF : G + 0xFFFFFF80 = sp0 + 0xFFFFFF70 := by rw [← hG, BitVec.add_assoc]; rfl
  rw [eGF] at fr3
  have hFn : (sp0 + 0xFFFFFF70).toNat = sp0.toNat - 0x90 := by
    rw [BitVec.toNat_add, show (0xFFFFFF70 : Word).toNat = 4294967152 from rfl]; omega
  have hc2 : CodeIn M2 Q ctIntoAffine384Code := fun i hi => by
    rw [fr3 _ ((sep_of_le (b := Q) (k := ctIntoAffine384Code.length) (by rw [hFn, hQn]; omega)
        (by rw [hQn]; decide)).subR (c := i) (l := 1) hi)
      ((sep_of_le (b := Q) (k := ctIntoAffine384Code.length) (by rw [hQn]; omega) (by rw [hQn]; decide)).subR
        (c := i) (l := 1) hi)]
    exact hc1 i hi
  have u3 : St M2 Q n3 0x1E (reg n3) := ⟨by rw [pc3], hM2, fun _ => rfl⟩
  have k3 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg m q := fun q hq => by
    obtain ⟨hq', hn⟩ := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧
        (q ≠ ra ∧ q ≠ sp ∧ q ≠ s0 ∧ q ≠ s1 ∧ q ≠ a2)) q hq
    rw [keep3 q hq', r2 q hn.1, K1 q hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2]
  have s03 : reg n3 s0 = out := by
    rw [keep3 s0 (by decide), r2 s0 (by decide), s01]
  have s13 : reg n3 s1 = (m.mem (s + 0x64)).zeroExtend 32 := by
    rw [keep3 s1 (by decide), r2 s1 (by decide), s11]
  obtain ⟨n4, d4, u4⟩ := u3.sb hc2 cia_at_1e (off' := 0x22) (by decide)
  rw [s03, s13, tlv_zext] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore8 M2 (out + 0x64) (m.mem (s + 0x64)) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  have sO64 : ∀ {b : Word} {l : Nat}, Sep out 0x65 b l → Sep (out + 0x64) 1 b l := fun h => h.sub (c := 0x64) (l := 1) (by omega)
  have hc3 : CodeIn M3 Q ctIntoAffine384Code := by
    rw [← hM3]; exact hc2.store8 (sep_of_le (by
      show (out + BitVec.ofNat 32 0x64).toNat + 1 ≤ Q.toNat
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hQn]; omega) (by rw [hQn]; decide))
  have sp3' : reg n3 sp = G := by rw [sp3]
  obtain ⟨n5, c5, u5⟩ := St.block ciaEpi u4 hc3 ciaEpi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ciaEpi, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp3']
    exact ⟨aligned_add hGa (k := 0xC) (by decide), aligned_add hGa (k := 8) (by decide),
      aligned_add hGa (k := 4) (by decide)⟩)
  have sl : ∀ c, c + 4 ≤ 16 → memLoad32 M3 (G + BitVec.ofNat 32 c) = memLoad32 M1 (G + BitVec.ofNat 32 c) :=
    fun c hc => by
      rw [← hM3, memLoad32_store8_sep ((sO64 sOW).subR (c := c) (l := 4) hc)]
      apply memLoad32_congr; intro j hj; rw [add_ofNat_assoc]
      refine fr3 _ (sep_of_le (by rw [hFn, hGc _ (by omega)]; omega) (by rw [hGc _ (by omega)]; omega)) ?_
      have := (sOW.sub (c := 0) (l := 0x61) (by omega)).subR (c := c + j) (l := 1) (by omega)
      rwa [add_ofNat_zero] at this
  have s4C : ∀ c d, c + 4 ≤ d ∨ d + 4 ≤ c → c < 16 → d < 16 →
      Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 := fun c d h hc hd =>
    sep_offsets G h (by omega) (by omega)
  have l1C : memLoad32 M1 (G + BitVec.ofNat 32 0xC) = retAddr := by
    rw [← hM1]
    show memLoad32 (memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _) _ = _
    rw [memLoad32_store32_sep (s4C 4 0xC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (s4C 8 0xC (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have l18 : memLoad32 M1 (G + BitVec.ofNat 32 8) = reg m s0 := by
    rw [← hM1]
    show memLoad32 (memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _) _ = _
    rw [memLoad32_store32_sep (s4C 4 8 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have l14 : memLoad32 M1 (G + BitVec.ofNat 32 4) = reg m s1 := by
    rw [← hM1]
    show memLoad32 (memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _) _ = _
    rw [memLoad32_store32_same]
  have R5 : ∀ q, reg n5 q = (runBlock ciaEpi (M3, reg n3)).2 q := u5.regs
  have u5' : St M3 Q n5 0x2A (reg n5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5'.jalr hc3 cia_at_2a
  have ra5 : reg n5 ra = retAddr := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, ciaEpi, upd_app, ↓reduceIte]; rw [sp3']
    exact (sl 0xC (by omega)).trans l1C
  have s05 : reg n5 s0 = reg m s0 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, ciaEpi, upd_app, ↓reduceIte]; rw [sp3']
    exact (sl 8 (by omega)).trans l18
  have s15 : reg n5 s1 = reg m s1 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, ciaEpi, upd_app, ↓reduceIte]; rw [sp3']
    exact (sl 4 (by omega)).trans l14
  have sp5 : reg n5 sp = sp0 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, ciaEpi, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp3', ← hG]
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have k5 : ∀ q, q ≠ ra → q ≠ s0 → q ≠ s1 → q ≠ sp → reg n5 q = reg n3 q := fun q h1 h8 h9 h2 => by
    rw [R5]; exact runBlock_reg _ _ _ q u3.zero (by
      simp only [ciaEpi, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h1, h8, h9, h2])
  -- From `M1`'s and `M3`'s view back to `m.mem`.
  have L1s : ∀ c, c + 4 ≤ 0x65 → memLoad32 M1 (s + BitVec.ofNat 32 c) = memLoad32 m.mem (s + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact M1o _ (sSW.sub (c := c + j) (l := 1) (by omega)).symm
  have L1d : ∀ c, c + 4 ≤ 0x61 → memLoad32 M1 ((img% p384AffineIdentityAddress : Word) + BitVec.ofNat 32 c) =
      memLoad32 m.mem ((img% p384AffineIdentityAddress : Word) + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact M1o _ (sDW.sub (c := c + j) (l := 1) (by omega)).symm
  have L3 : ∀ c, c + 4 ≤ 0x64 → memLoad32 M3 (out + BitVec.ofNat 32 c) = memLoad32 M2 (out + BitVec.ofNat 32 c) :=
    fun c hc => by
      rw [← hM3]; exact memLoad32_store8_sep (sep_offsets out (c := 0x64) (n := 1) (d := c) (k := 4) (Or.inr (by omega))
        (by omega) (by omega))
  refine ⟨n6, c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (.single d6))))), ?_, by rw [regs6, sp5],
    fun i hi => ?_, fun i hi => ?_, ?_, ?_, fun q hq => ?_, fun y hy hy' => ?_⟩
  · rw [pc6, ra5, add_lit_zero, hret]
  · rw [mem6, L3 _ (by omega), w1 i hi, hb, L1s _ (by omega), L1d _ (by omega)]
  · rw [mem6, show out + (0x30 : Word) + BitVec.ofNat 32 (4 * i) = out + BitVec.ofNat 32 (0x30 + 4 * i) from
      add_ofNat_assoc out 0x30 (4 * i), L3 _ (by omega),
      show out + BitVec.ofNat 32 (0x30 + 4 * i) = out + (0x30 : Word) + BitVec.ofNat 32 (4 * i) from
      (add_ofNat_assoc out 0x30 (4 * i)).symm, w2 i hi, hb,
      show s + (0x30 : Word) + BitVec.ofNat 32 (4 * i) = s + BitVec.ofNat 32 (0x30 + 4 * i) from
      add_ofNat_assoc s 0x30 (4 * i), L1s _ (by omega),
      show (img% p384AffineIdentityAddress : Word) + 0x30 + BitVec.ofNat 32 (4 * i) = (img% p384AffineIdentityAddress : Word) + BitVec.ofNat 32 (0x30 + 4 * i)
      from add_ofNat_assoc _ 0x30 (4 * i), L1d _ (by omega)]
  · rw [mem6, ← hM3, memStore8_ne (show out + (0x60 : Word) ≠ out + 0x64 from add_ofNat_ne out (by decide) (by decide)
      (by decide)), b60, hb, M1o (s + 0x60) (sSW.sub (c := 0x60) (l := 1) (by omega)).symm,
      M1o ((img% p384AffineIdentityAddress : Word) + 0x60) (sDW.sub (c := 0x60) (l := 1) (by omega)).symm]
  · rw [mem6, ← hM3, memStore8_same]
  · rw [regs6]
    by_cases q1 : q = ra
    · subst q1; rw [ra5, hra]
    by_cases q8 : q = s0
    · subst q8; exact s05
    by_cases q9 : q = s1
    · subst q9; exact s15
    have q2 : q ≠ sp := fun e => by subst e; revert hq; decide
    rw [k5 q q1 q8 q9 q2]
    exact k3 q (by
      revert hq q1 q8 q9 q2
      revert q
      decide)
  · rw [mem6, ← hM3, memStore8_ne (fun e => hy' 0x64 (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)),
      fr3 y (hy.sub (c := 0) (l := 0x80) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
        (hy'.sub (c := 0) (l := 0x61) (by omega) |> fun h => by rwa [add_ofNat_zero] at h),
      M1o y (by rw [← hG]; have := hy.sub (c := 0x80) (l := 16) (by omega)
                rwa [show sp0 + (0xFFFFFF70 : Word) + BitVec.ofNat 32 0x80 = sp0 + 0xFFFFFFF0 by
                  rw [BitVec.add_assoc]; rfl] at this)]

def cibPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sw sp ra 0xC, .sw sp (8 : Fin 32) 0x8, .sw sp (9 : Fin 32) 0x4,
    .lbu (9 : Fin 32) a1 0x44, .alu .add (8 : Fin 32) x0 a0, .lui a2 0x3FCC4000, .aluImm .add a2 a2 0x42C]
def cibEpi : List BInstr :=
  [.lw ra sp 0xC, .lw (8 : Fin 32) sp 0x8, .lw (9 : Fin 32) sp 0x4, .aluImm .add sp sp 0x10]

set_option maxRecDepth 20000 in
theorem cibPro_end : blockEnd ctIntoAffine256Code 0 cibPro = some 0x16 := by decide
set_option maxRecDepth 20000 in
theorem cibEpi_end : blockEnd ctIntoAffine256Code 0x22 cibEpi = some 0x2A := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The compiled conversion of `CtOption<AffinePoint<NistP256>>` into
`ctutils::CtOption`**, from the option at `s` to `out`: the 0x41 bytes of
the point are `s`'s when its choice byte is 1 and the identity's otherwise,
as `unwrapOr256_correct` says, and the choice byte follows at `out + 0x44`.
It changes no memory outside the result and 0x80 bytes of stack below
`sp`. -/
theorem ctIntoAffine256_correct (m : Machine) {out s sp0 retAddr : Word}
    (hc : CodeIn m.mem (BitVec.ofNat 32 ctIntoAffine256Address) ctIntoAffine256Code)
    (env : UO2Env m.mem (BitVec.ofNat 32 unwrapOr256Address) (sp0 + 0xFFFFFFF0) out s (img% p256AffineIdXAddress))
    (hpc : m.pc = BitVec.ofNat 32 ctIntoAffine256Address) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = s) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hch : m.mem (s + 0x44) = 0 ∨ m.mem (s + 0x44) = 1)
    (hspl : 0x80 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000) (how : out.toNat + 0x45 ≤ 0x40000000)
    (sOW : Sep out 0x45 (sp0 + 0xFFFFFFF0) 16) (sSW : Sep s 0x45 (sp0 + 0xFFFFFFF0) 16)
    (sDW : Sep (img% p256AffineIdXAddress : Word) 0x41 (sp0 + 0xFFFFFFF0) 16) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 8 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x44) = 1 then memLoad32 m.mem (s + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem ((img% p256AffineIdXAddress) + BitVec.ofNat 32 (4 * i))) ∧
      (∀ i, i < 8 → memLoad32 m'.mem (out + 0x20 + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x44) = 1 then memLoad32 m.mem (s + 0x20 + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem ((img% p256AffineIdXAddress) + 0x20 + BitVec.ofNat 32 (4 * i))) ∧
      m'.mem (out + 0x40) = (if m.mem (s + 0x44) = 1 then m.mem (s + 0x40) else m.mem ((img% p256AffineIdXAddress) + 0x40)) ∧
      m'.mem (out + 0x44) = m.mem (s + 0x44) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF80) 0x80 y 1 → Sep out 0x45 y 1 → m'.mem y = m.mem y := by
  let Q := BitVec.ofNat 32 ctIntoAffine256Address
  let P := BitVec.ofNat 32 unwrapOr256Address
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hG] at env sOW sSW sDW
  have hGn : G.toNat = sp0.toNat - 16 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl]; omega
  have hGa : G.toNat % 4 = 0 := env.hsp
  have hGc : ∀ c, c ≤ 16 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hQn : Q.toNat = (img% ctIntoAffine256Address) := by decide
  have st0 : St m.mem Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  have slotP : ∀ (o : Nat), o + 4 ≤ 16 → o % 4 = 0 →
      (G + BitVec.ofNat 32 o).toNat % 4 = 0 ∧ Sep (G + BitVec.ofNat 32 o) 4 Q ctIntoAffine256Code.length :=
    fun o h2 h3 => ⟨aligned_add hGa h3, sep_of_le (by rw [hGc _ (by omega), hQn]; omega) (by rw [hQn]; decide)⟩
  obtain ⟨n1, c1, u1⟩ := St.block cibPro st0 hc cibPro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, cibPro, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add]; rw [hsp, hG]
    exact ⟨slotP 0xC (by omega) (by omega), slotP 8 (by omega) (by omega), slotP 4 (by omega) (by omega)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 (memStore32 m.mem (G + 0xC) retAddr)
      (G + 8) (reg m (8 : Fin 32))) (G + 4) (reg m (9 : Fin 32)) = M1 := ⟨_, rfl⟩
  have eM1 : (runBlock cibPro (m.mem, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, cibPro, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [hsp, hG, hra, hM1]
  have M1o : ∀ x, Sep G 16 x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1]
    show memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _ x = _
    rw [memStore32_get_sep (hx.sub (c := 4) (l := 4) (by omega)), memStore32_get_sep (hx.sub (c := 8) (l := 4)
      (by omega)), memStore32_get_sep (hx.sub (c := 0xC) (l := 4) (by omega))]
  have M1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M1 x = m.mem x := fun x hx =>
    M1o x (sep_of_le (by omega) (by have := x.isLt; omega))
  have R1 : ∀ q, reg n1 q = (runBlock cibPro (m.mem, reg m)).2 q := u1.regs
  have u1' : St M1 Q n1 0x16 (reg n1) := ⟨u1.pc, by rw [u1.mem, eM1], fun _ => rfl⟩
  have hc1 : CodeIn M1 Q ctIntoAffine256Code := hc.hi M1hi (by decide) (by decide)
  have sp1 : reg n1 sp = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, cibPro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp, hG]
  have s01 : reg n1 s0 = out := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, cibPro, upd_app, ↓reduceIte]; simp only [ev_add]
    exact (BitVec.zero_add _).trans ha0
  have hb : M1 (s + 0x44) = m.mem (s + 0x44) := M1o _ (sSW.sub (c := 0x44) (l := 1) (by omega)).symm
  have s11 : reg n1 s1 = (m.mem (s + 0x44)).zeroExtend 32 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, cibPro, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [ha1, hsp, hG, hra, hM1, hb]
  have a21 : reg n1 a2 = (img% p256AffineIdXAddress) := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, cibPro, upd_app, ↓reduceIte]
  have K1 : ∀ q, q ≠ sp → q ≠ s0 → q ≠ s1 → q ≠ a2 → reg n1 q = reg m q := fun q h2 h8 h9 h12 => by
    rw [R1]; simp only [runBlock, BInstr.run, cibPro]
    rw [updz (by simp [upd]) h12, updz (by simp [upd]) h12, updz (by simp [upd]) h8, updz (by simp [upd]) h9,
      updz hz h2]
  have env1 : UO2Env M1 P G out s (img% p256AffineIdXAddress) :=
    { env with
      cod := env.cod.hi M1hi (by decide) (by decide)
      cs := env.cs.hi M1hi (by decide) (by decide)
      stub := env.stub.hi M1hi (by decide) (by decide)
      body := env.body.hi M1hi (by decide) (by decide)
      sca := env.sca.hi M1hi (by decide) (by decide) }
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc1 cib_at_16 cib_at_1a
    (show Q + BitVec.ofNat 32 0x16 + 0xFFFFD000 + 0x1EA = P by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  obtain ⟨n3, c3, pc3, sp3, w1, w2, b60, keep3, fr3⟩ := unwrapOr256_correct n2
    (retAddr := Q + BitVec.ofNat 32 (0x16 + 8)) (by rw [mem2]; exact env1) pc2
    (by rw [r2 sp (by decide), sp1]) (by rw [r2 a0 (by decide), K1 a0 (by decide) (by decide) (by decide) (by decide), ha0])
    (by rw [r2 a1 (by decide), K1 a1 (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [r2 a2 (by decide), a21]) (by rw [mem2, hb]; exact hch)
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at Q (by decide) _ (by omega)))
  rw [mem2] at w1 w2 b60 fr3
  obtain ⟨M2, hM2⟩ : ∃ M2, n3.mem = M2 := ⟨_, rfl⟩
  rw [hM2] at w1 w2 b60 fr3
  have eGF : G + 0xFFFFFF90 = sp0 + 0xFFFFFF80 := by rw [← hG, BitVec.add_assoc]; rfl
  rw [eGF] at fr3
  have hFn : (sp0 + 0xFFFFFF80).toNat = sp0.toNat - 0x80 := by
    rw [BitVec.toNat_add, show (0xFFFFFF80 : Word).toNat = 4294967168 from rfl]; omega
  have hc2 : CodeIn M2 Q ctIntoAffine256Code := fun i hi => by
    rw [fr3 _ ((sep_of_le (b := Q) (k := ctIntoAffine256Code.length) (by rw [hFn, hQn]; omega)
        (by rw [hQn]; decide)).subR (c := i) (l := 1) hi)
      ((sep_of_le (b := Q) (k := ctIntoAffine256Code.length) (by rw [hQn]; omega) (by rw [hQn]; decide)).subR
        (c := i) (l := 1) hi)]
    exact hc1 i hi
  have u3 : St M2 Q n3 0x1E (reg n3) := ⟨by rw [pc3], hM2, fun _ => rfl⟩
  have k3 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg m q := fun q hq => by
    obtain ⟨hq', hn⟩ := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧
        (q ≠ ra ∧ q ≠ sp ∧ q ≠ s0 ∧ q ≠ s1 ∧ q ≠ a2)) q hq
    rw [keep3 q hq', r2 q hn.1, K1 q hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2]
  have s03 : reg n3 s0 = out := by
    rw [keep3 s0 (by decide), r2 s0 (by decide), s01]
  have s13 : reg n3 s1 = (m.mem (s + 0x44)).zeroExtend 32 := by
    rw [keep3 s1 (by decide), r2 s1 (by decide), s11]
  obtain ⟨n4, d4, u4⟩ := u3.sb hc2 cib_at_1e (off' := 0x22) (by decide)
  rw [s03, s13, tlv_zext] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore8 M2 (out + 0x44) (m.mem (s + 0x44)) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  have sO64 : ∀ {b : Word} {l : Nat}, Sep out 0x45 b l → Sep (out + 0x44) 1 b l := fun h => h.sub (c := 0x44) (l := 1) (by omega)
  have hc3 : CodeIn M3 Q ctIntoAffine256Code := by
    rw [← hM3]; exact hc2.store8 (sep_of_le (by
      show (out + BitVec.ofNat 32 0x44).toNat + 1 ≤ Q.toNat
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hQn]; omega) (by rw [hQn]; decide))
  have sp3' : reg n3 sp = G := by rw [sp3]
  obtain ⟨n5, c5, u5⟩ := St.block cibEpi u4 hc3 cibEpi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, cibEpi, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp3']
    exact ⟨aligned_add hGa (k := 0xC) (by decide), aligned_add hGa (k := 8) (by decide),
      aligned_add hGa (k := 4) (by decide)⟩)
  have sl : ∀ c, c + 4 ≤ 16 → memLoad32 M3 (G + BitVec.ofNat 32 c) = memLoad32 M1 (G + BitVec.ofNat 32 c) :=
    fun c hc => by
      rw [← hM3, memLoad32_store8_sep ((sO64 sOW).subR (c := c) (l := 4) hc)]
      apply memLoad32_congr; intro j hj; rw [add_ofNat_assoc]
      refine fr3 _ (sep_of_le (by rw [hFn, hGc _ (by omega)]; omega) (by rw [hGc _ (by omega)]; omega)) ?_
      have := (sOW.sub (c := 0) (l := 0x41) (by omega)).subR (c := c + j) (l := 1) (by omega)
      rwa [add_ofNat_zero] at this
  have s4C : ∀ c d, c + 4 ≤ d ∨ d + 4 ≤ c → c < 16 → d < 16 →
      Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 := fun c d h hc hd =>
    sep_offsets G h (by omega) (by omega)
  have l1C : memLoad32 M1 (G + BitVec.ofNat 32 0xC) = retAddr := by
    rw [← hM1]
    show memLoad32 (memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _) _ = _
    rw [memLoad32_store32_sep (s4C 4 0xC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (s4C 8 0xC (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have l18 : memLoad32 M1 (G + BitVec.ofNat 32 8) = reg m s0 := by
    rw [← hM1]
    show memLoad32 (memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _) _ = _
    rw [memLoad32_store32_sep (s4C 4 8 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  have l14 : memLoad32 M1 (G + BitVec.ofNat 32 4) = reg m s1 := by
    rw [← hM1]
    show memLoad32 (memStore32 (memStore32 (memStore32 m.mem (G + BitVec.ofNat 32 0xC) _) (G + BitVec.ofNat 32 8) _)
      (G + BitVec.ofNat 32 4) _) _ = _
    rw [memLoad32_store32_same]
  have R5 : ∀ q, reg n5 q = (runBlock cibEpi (M3, reg n3)).2 q := u5.regs
  have u5' : St M3 Q n5 0x2A (reg n5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5'.jalr hc3 cib_at_2a
  have ra5 : reg n5 ra = retAddr := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, cibEpi, upd_app, ↓reduceIte]; rw [sp3']
    exact (sl 0xC (by omega)).trans l1C
  have s05 : reg n5 s0 = reg m s0 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, cibEpi, upd_app, ↓reduceIte]; rw [sp3']
    exact (sl 8 (by omega)).trans l18
  have s15 : reg n5 s1 = reg m s1 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, cibEpi, upd_app, ↓reduceIte]; rw [sp3']
    exact (sl 4 (by omega)).trans l14
  have sp5 : reg n5 sp = sp0 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, cibEpi, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp3', ← hG]
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have k5 : ∀ q, q ≠ ra → q ≠ s0 → q ≠ s1 → q ≠ sp → reg n5 q = reg n3 q := fun q h1 h8 h9 h2 => by
    rw [R5]; exact runBlock_reg _ _ _ q u3.zero (by
      simp only [cibEpi, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h1, h8, h9, h2])
  -- From `M1`'s and `M3`'s view back to `m.mem`.
  have L1s : ∀ c, c + 4 ≤ 0x45 → memLoad32 M1 (s + BitVec.ofNat 32 c) = memLoad32 m.mem (s + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact M1o _ (sSW.sub (c := c + j) (l := 1) (by omega)).symm
  have L1d : ∀ c, c + 4 ≤ 0x41 → memLoad32 M1 ((img% p256AffineIdXAddress : Word) + BitVec.ofNat 32 c) =
      memLoad32 m.mem ((img% p256AffineIdXAddress : Word) + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact M1o _ (sDW.sub (c := c + j) (l := 1) (by omega)).symm
  have L3 : ∀ c, c + 4 ≤ 0x44 → memLoad32 M3 (out + BitVec.ofNat 32 c) = memLoad32 M2 (out + BitVec.ofNat 32 c) :=
    fun c hc => by
      rw [← hM3]; exact memLoad32_store8_sep (sep_offsets out (c := 0x44) (n := 1) (d := c) (k := 4) (Or.inr (by omega))
        (by omega) (by omega))
  refine ⟨n6, c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (.single d6))))), ?_, by rw [regs6, sp5],
    fun i hi => ?_, fun i hi => ?_, ?_, ?_, fun q hq => ?_, fun y hy hy' => ?_⟩
  · rw [pc6, ra5, add_lit_zero, hret]
  · rw [mem6, L3 _ (by omega), w1 i hi, hb, L1s _ (by omega), L1d _ (by omega)]
  · rw [mem6, show out + (0x20 : Word) + BitVec.ofNat 32 (4 * i) = out + BitVec.ofNat 32 (0x20 + 4 * i) from
      add_ofNat_assoc out 0x20 (4 * i), L3 _ (by omega),
      show out + BitVec.ofNat 32 (0x20 + 4 * i) = out + (0x20 : Word) + BitVec.ofNat 32 (4 * i) from
      (add_ofNat_assoc out 0x20 (4 * i)).symm, w2 i hi, hb,
      show s + (0x20 : Word) + BitVec.ofNat 32 (4 * i) = s + BitVec.ofNat 32 (0x20 + 4 * i) from
      add_ofNat_assoc s 0x20 (4 * i), L1s _ (by omega),
      show (img% p256AffineIdXAddress : Word) + 0x20 + BitVec.ofNat 32 (4 * i) = (img% p256AffineIdXAddress : Word) + BitVec.ofNat 32 (0x20 + 4 * i)
      from add_ofNat_assoc _ 0x20 (4 * i), L1d _ (by omega)]
  · rw [mem6, ← hM3, memStore8_ne (show out + (0x40 : Word) ≠ out + 0x44 from add_ofNat_ne out (by decide) (by decide)
      (by decide)), b60, hb, M1o (s + 0x40) (sSW.sub (c := 0x40) (l := 1) (by omega)).symm,
      M1o ((img% p256AffineIdXAddress : Word) + 0x40) (sDW.sub (c := 0x40) (l := 1) (by omega)).symm]
  · rw [mem6, ← hM3, memStore8_same]
  · rw [regs6]
    by_cases q1 : q = ra
    · subst q1; rw [ra5, hra]
    by_cases q8 : q = s0
    · subst q8; exact s05
    by_cases q9 : q = s1
    · subst q9; exact s15
    have q2 : q ≠ sp := fun e => by subst e; revert hq; decide
    rw [k5 q q1 q8 q9 q2]
    exact k3 q (by
      revert hq q1 q8 q9 q2
      revert q
      decide)
  · rw [mem6, ← hM3, memStore8_ne (fun e => hy' 0x44 (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)),
      fr3 y (hy.sub (c := 0) (l := 0x70) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
        (hy'.sub (c := 0) (l := 0x41) (by omega) |> fun h => by rwa [add_ofNat_zero] at h),
      M1o y (by rw [← hG]; have := hy.sub (c := 0x70) (l := 16) (by omega)
                rwa [show sp0 + (0xFFFFFF80 : Word) + BitVec.ofNat 32 0x70 = sp0 + 0xFFFFFFF0 by
                  rw [BitVec.add_assoc]; rfl] at this)]

end C3.RV32
