import C3BootProofs.Proofs.P256ScalarBody
import C3BootProofs.Proofs.P256ScalarPro

/-!
# P-256's `<Scalar as Mul>::mul`

The compiled function saves its registers, multiplies the operands with
`widening_mul_fixed::<8, 8>` into 16 limbs in its frame, reduces them with
`barrett_reduce` (with 18 calls of `borrowing_sub`), stores the result, and
restores its registers. `psm_pro`, `wideMul_correct`, `psm_body`, and
`psm_epi` prove those parts; this file joins them.
-/

namespace C3.RV32

open C3.Image

/-- Limb `i` of `x` for `i < 16`, and zero past them: `barrett_reduce`'s
input when `x` is the product of the operands. -/
def psmProd (x : Nat) (i : Nat) : Nat := if i < 16 then x / 2 ^ (32 * i) % 2 ^ 32 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
/-- **The compiled `<Scalar as Mul>::mul` of the p256 crate**, called with the
result at `out` and the operands at `ap` and `bp`: limb `j` of `out` is limb
`j` of `barrett_reduce` of the operands' product, as the Rust source computes
it. It returns with `sp` and the callee-saved registers as they were, and
changes no memory outside its and its callees' 0x100 bytes of stack and the
result. -/
theorem p256ScalarMul_correct (m : Machine) {P G out ap bp retAddr : Word} (env : PSMEnv m.mem P G out ap bp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + 0x100) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x100 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ j, j < 8 → (memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * j))).toNat =
        psmOut (psmProd (accV m.mem ap 8 * accV m.mem bp 8)) j) ∧
      ∀ x, Sep G 0x100 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x60 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have hFn : F.toNat = G.toNat + 0x60 := by
    rw [← hF, BitVec.toNat_add, show (0x60 : Word).toNat = 0x60 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x60 + c) := fun c => by rw [← hF]; exact psmF_ofs G c
  have hFG : F + 0xFFFFFFA0 = G := by
    rw [← hF, BitVec.add_assoc, show (0x60 : Word) + 0xFFFFFFA0 = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]
  have hF4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x5C := by
    rw [← hF, BitVec.add_assoc]; rfl
  have hF2C : F + 0x2C = G + BitVec.ofNat 32 0x8C := by rw [← hF, BitVec.add_assoc]; rfl
  have inF : ∀ {b : Word} {k : Nat}, Sep G 0x100 b k → Sep F 0xA0 b k := fun h => by
    rw [← hF]; exact h.sub (c := 0x60) (l := 0xA0) (by decide)
  have g60 : ∀ {b : Word} {k : Nat}, Sep G 0x100 b k → Sep (F + 0xFFFFFFA0) 0x60 b k := fun h => by
    rw [hFG]; have := h.sub (c := 0) (l := 0x60) (by decide); rwa [add_ofNat_zero] at this
  have g4 : ∀ {b : Word} {k : Nat}, Sep G 0x100 b k → Sep (F + 0xFFFFFFFC) 4 b k := fun h => by
    rw [hF4]; exact h.sub (c := 0x5C) (l := 4) (by decide)
  have gO : ∀ {b : Word} {k : Nat}, Sep G 0x100 b k → Sep (F + 0x2C) 64 b k := fun h => by
    rw [hF2C]; exact h.sub (c := 0x8C) (l := 64) (by decide)
  -- the prologue
  obtain ⟨n, M, cP, stP, frP, slP, outP, spP, a0P, a1P, a2P, kP⟩ :=
    psm_pro m env hF hpc hsp ha0 ha1 ha2
  have cM : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x100 b code.length → CodeIn M b code :=
    fun hc hs i hi => by rw [frP _ ((inF hs).subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hcM := cM env.code env.sGC
  -- the call of `widening_mul_fixed::<8, 8>`
  have hev : (P + 0xFFFFB24E).toNat % 2 = 0 := even_at P env.hP 0xFFFFB24E (by decide)
  obtain ⟨t4, c4, pc4, mem4, regs4⟩ := stP.callRa hcM psm_at_20 psm_at_24 (cb := P + 0xFFFFB24E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) hev
  have r4 := PEnv.reg1 regs4 stP.zero
  have wenv : WMEnv t4.mem (P + 0xFFFFB24E) F (F + 0x2C) ap bp := by
    rw [mem4]
    exact ⟨hev, cM env.wm env.sGW, cM env.mset env.sGM, cM env.stub env.sGU, cM env.body env.sGB, hFa,
      fr_al' hFa (by decide), env.hap, env.hbp, by omega,
      by rw [BitVec.toNat_add, show (0x2C : Word).toNat = 0x2C from rfl, Nat.mod_eq_of_lt (by omega)]; omega,
      g60 env.sGW, g60 env.sGM, g60 env.sGU, g60 env.sGB, gO env.sGW, gO env.sGU, gO env.sGB,
      by
        rw [hF2C, hFG]
        have := sep_offsets G (c := 0x8C) (n := 64) (d := 0) (k := 0x60) (.inr (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this,
      (g60 env.sAG.symm).symm, (g60 env.sBG.symm).symm⟩
  obtain ⟨t5, c5, pc5, sp5, k5, prod5, fr5⟩ := wideMul_correct t4 wenv pc4
    (by rw [r4 _ (by decide), a0P]) (by rw [r4 _ (by decide), a1P]) (by rw [r4 _ (by decide), a2P])
    (by rw [regs4]; simp [upd]) (even_clear _ (even_at P env.hP (0x20 + 8) (by decide)))
    (by rw [r4 _ (by decide), spP])
  rw [mem4] at prod5 fr5
  have t5M : ∀ x, Sep G 0x100 x 1 → t5.mem x = M x := fun x hx => fr5 x (g60 hx) (gO hx)
  have c5M : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x100 b code.length → CodeIn t5.mem b code :=
    fun hc hs i hi => by rw [t5M _ (hs.subR (c := i) (l := 1) (by omega))]; exact cM hc hs i hi
  have hc5 := c5M env.code env.sGC
  have slot5 : ∀ c, c + 4 ≤ 0x2C ∨ 0x2C + 64 ≤ c → c + 4 ≤ 0xA0 →
      memLoad32 t5.mem (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      refine fr5 _ ?_ ?_
      · rw [hFG, fG]
        have := sep_offsets G (c := 0) (n := 0x60) (d := 0x60 + (c + j)) (k := 1) (.inl (by omega)) (by decide)
          (by omega)
        rwa [add_ofNat_zero] at this
      · exact sep_offsets F (c := 0x2C) (n := 64) (d := c + j) (k := 1) (by omega) (by decide) (by omega)
  have e28 : memLoad32 t5.mem (F + 0x28) = out := by
    rw [show F + 0x28 = F + BitVec.ofNat 32 0x28 from rfl, slot5 0x28 (.inl (by decide)) (by decide)]; exact outP
  -- the body
  have st5 : St t5.mem P t5 0x28 (reg t5) := ⟨pc5, rfl, fun _ => rfl⟩
  obtain ⟨n1, M1, c1, w1, fr1, ks0, ks1, ks2, ks3, ks4, ks5, ks6, ks7, ks8, ks9, ks10, ks11, ks12, houts, sp1,
      g3_1, g4_1⟩ :=
    psm_body (outp := out) st5 hc5 (by rw [sp5]) e28
      hFa env.hout env.hP (inF env.sGC) (g4 env.sGC) env.sOC (inF env.sOG.symm).symm (g4 env.sOG.symm).symm
      (c5M env.bs env.sGBs) (inF env.sGBs) (g4 env.sGBs) env.sOBs
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at houts
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, -⟩ := houts
  have hc1 : CodeIn M1 P p256ScalarMulCode := fun i hi => by
    have hs := env.sGC.subR (c := i) (l := 1) (by omega)
    rw [fr1 _ (inF hs) (g4 hs) (env.sOC.subR (c := i) (l := 1) (by omega))]; exact hc5 i hi
  -- the epilogue
  have hsl : ∀ r o, (r, o) ∈ psmPs → memLoad32 M1 (F + o) = reg m r := fun r o h => by
    have hr : o.toNat % 4 = 0 ∧ 0x6C ≤ o.toNat ∧ o.toNat + 4 ≤ 0xA0 := psmPs_range (r, o) h
    have e : memLoad32 t5.mem (F + o) = memLoad32 M (F + o) := by
      have := slot5 o.toNat (.inr (by omega)) hr.2.2; rwa [ofNat_toNat_self] at this
    rw [← slP r o h, ← e]
    simp only [psmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | exact ks0 | exact ks1 | exact ks2 | exact ks3 | exact ks4 | exact ks5 | exact ks6 | exact ks7 |
      exact ks8 | exact ks9 | exact ks10 | exact ks11 | exact ks12
  obtain ⟨n2, c2, pc2, sp2, mem2, rs2, ks2'⟩ := psm_epi (v := reg m) w1 hc1 hFa sp1 hsl
  -- the product's limbs
  have prodEq : psmIn t5.mem F = psmProd (accV m.mem ap 8 * accV m.mem bp 8) := funext fun i => by
    unfold psmIn psmProd
    by_cases hi : i < 16
    · rw [ite_eq_left hi, ite_eq_left hi]
      have hX : accV t5.mem (F + 0x2C) 16 = accV m.mem ap 8 * accV m.mem bp 8 := by
        rw [← limbVal_wordsAt, prod5, limbVal_wordsAt, limbVal_wordsAt]
        have opnd : ∀ {b : Word}, Sep b 32 G 0x100 → accV M b 8 = accV m.mem b 8 := fun hb =>
          accV_congr 8 fun i hi => memLoad32_congr fun j hj => frP _ (by
            have := (inF hb.symm).subR (c := 4 * i + j) (l := 1) (by omega)
            rwa [← add_ofNat_assoc] at this)
        rw [opnd env.sAG, opnd env.sBG]
      rw [← hX, accV_digit t5.mem (F + 0x2C) 16 i hi, show (0x2C : Word) = BitVec.ofNat 32 0x2C from rfl,
        add_ofNat_assoc]
    · rw [ite_eq_right hi, ite_eq_right hi]
  rw [prodEq] at o0 o1 o2 o3 o4 o5 o6 o7
  have pass : ∀ q : Fin 32, q.val ∈ [3, 4] → reg n2 q = reg m q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∉ [3, 4] → q ≠ r := fun r hr e => hr (e ▸ hq)
    rw [ks2' q (by revert hq; revert q; decide) (nq _ (by decide))]
    rcases (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq; omega : q.val = 3 ∨ q.val = 4) with h | h
    · have : q = 3 := Fin.ext h
      subst this
      rw [g3_1, k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), r4 _ (by decide), kP _ (by decide)]
    · have : q = 4 := Fin.ext h
      subst this
      rw [g4_1, k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), r4 _ (by decide), kP _ (by decide)]
  refine ⟨n2, cP.trans (c4.trans (c5.trans (c1.trans c2))), ?_, ?_, fun q hq => ?_, fun j hj => ?_,
    fun x hx ho => ?_⟩
  · rw [pc2, hra, hret]
  · rw [sp2, ← hF, BitVec.add_assoc]; rfl
  · have hmem : q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q = (24 : Fin 32) ∨
        q = (25 : Fin 32) ∨ q = (26 : Fin 32) ∨ q = (27 : Fin 32) ∨ q.val ∈ [3, 4] := by
      revert hq; revert q; decide
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · exact rs2 _ 0x9C (by decide)
    · exact rs2 _ 0x98 (by decide)
    · exact rs2 _ 0x94 (by decide)
    · exact rs2 _ 0x90 (by decide)
    · exact rs2 _ 0x8C (by decide)
    · exact rs2 _ 0x88 (by decide)
    · exact rs2 _ 0x84 (by decide)
    · exact rs2 _ 0x80 (by decide)
    · exact rs2 _ 0x7C (by decide)
    · exact rs2 _ 0x78 (by decide)
    · exact rs2 _ 0x74 (by decide)
    · exact rs2 _ 0x70 (by decide)
    · exact rs2 _ 0x6C (by decide)
    · exact pass q h
  · rw [mem2]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact o0
    · exact o1
    · exact o2
    · exact o3
    · exact o4
    · exact o5
    · exact o6
    · exact o7
  · rw [mem2, fr1 x (inF hx) (g4 hx) ho, t5M x hx, frP x (inF hx)]

end C3.RV32
