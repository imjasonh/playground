import C3BootProofs.Proofs.FeAdd
import C3BootProofs.Proofs.FeSub
import C3BootProofs.Proofs.AsProjective

/-!
# `EdwardsPoint::as_projective_niels`, as compiled

`as_projective_niels` turns the extended point `(X, Y, Z, T)` into the
projective Niels point `(Y + X, Y - X, Z, 2d T)`: the proved field `add` and
`sub`, a 40-byte `memcpy` of `Z`, and a tail call to the proved `mul` with
the constant `2d` that the image keeps at `edwardsD2Address`.
-/

namespace C3.RV32

open C3.Image

abbrev apnPs : List (Fin 32 × Word) := [(ra, 0xC), ((8 : Fin 32), 0x8), ((9 : Fin 32), 0x4), ((18 : Fin 32), 0x0)]

/-- The instructions from 0xA to 0x16: the point in `s0`, the result in `s1`,
`Y` in `s2`, and `add`'s operands. -/
def apnArgs : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a1, .alu .add (9 : Fin 32) x0 a0, .aluImm .add (18 : Fin 32) a1 0x28,
   .alu .add a1 x0 (18 : Fin 32), .alu .add a2 x0 (8 : Fin 32)]

section
set_option maxRecDepth 20000
theorem apn_at_0 : fetchRel asProjNielsCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem apn_at_2 : fetchRel asProjNielsCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem apn_at_4 : fetchRel asProjNielsCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem apn_at_6 : fetchRel asProjNielsCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem apn_at_8 : fetchRel asProjNielsCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x0, 2) := by decide
theorem apn_at_a : fetchRel asProjNielsCode 0xA = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem apn_at_c : fetchRel asProjNielsCode 0xC = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem apn_at_e : fetchRel asProjNielsCode 0xE = some (.aluImm .add (18 : Fin 32) a1 0x28, 4) := by decide
theorem apn_at_12 : fetchRel asProjNielsCode 0x12 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem apn_at_14 : fetchRel asProjNielsCode 0x14 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem apn_at_16 : fetchRel asProjNielsCode 0x16 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem apn_at_1a : fetchRel asProjNielsCode 0x1A = some (.jalr ra ra 0x564, 4) := by decide
theorem apn_at_1e : fetchRel asProjNielsCode 0x1E = some (.aluImm .add a0 (9 : Fin 32) 0x28, 4) := by decide
theorem apn_at_22 : fetchRel asProjNielsCode 0x22 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem apn_at_24 : fetchRel asProjNielsCode 0x24 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem apn_at_26 : fetchRel asProjNielsCode 0x26 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem apn_at_2a : fetchRel asProjNielsCode 0x2A = some (.jalr ra ra 0x5A2, 4) := by decide
theorem apn_at_2e : fetchRel asProjNielsCode 0x2E = some (.aluImm .add a1 (8 : Fin 32) 0x50, 4) := by decide
theorem apn_at_32 : fetchRel asProjNielsCode 0x32 = some (.aluImm .add a0 (9 : Fin 32) 0x50, 4) := by decide
theorem apn_at_36 : fetchRel asProjNielsCode 0x36 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem apn_at_3a : fetchRel asProjNielsCode 0x3A = some (.auipc ra 0x4000, 4) := by decide
theorem apn_at_3e : fetchRel asProjNielsCode 0x3E = some (.jalr ra ra 0x2C8, 4) := by decide
theorem apn_at_42 : fetchRel asProjNielsCode 0x42 = some (.aluImm .add a1 (8 : Fin 32) 0x78, 4) := by decide
theorem apn_at_46 : fetchRel asProjNielsCode 0x46 = some (.aluImm .add a0 (9 : Fin 32) 0x78, 4) := by decide
theorem apn_at_4a : fetchRel asProjNielsCode 0x4A = some (.lui a2 0x3FCC5000, 4) := by decide
theorem apn_at_4e : fetchRel asProjNielsCode 0x4E = some (.aluImm .add a2 a2 0xFFFFFA94, 4) := by decide
theorem apn_at_52 : fetchRel asProjNielsCode 0x52 = some (.load .lw ra sp 0xC, 2) := by decide
theorem apn_at_54 : fetchRel asProjNielsCode 0x54 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem apn_at_56 : fetchRel asProjNielsCode 0x56 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem apn_at_58 : fetchRel asProjNielsCode 0x58 = some (.load .lw (18 : Fin 32) sp 0x0, 2) := by decide
theorem apn_at_5a : fetchRel asProjNielsCode 0x5A = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem apn_at_5c : fetchRel asProjNielsCode 0x5C = some (.auipc (6 : Fin 32) 0xFFFFD000, 4) := by decide
theorem apn_at_60 : fetchRel asProjNielsCode 0x60 = some (.jalr x0 (6 : Fin 32) 0x1AA, 4) := by decide
theorem apnSave_end : blockEnd asProjNielsCode 2 (saveBlock apnPs) = some 0xA := by decide
theorem apnArgs_end : blockEnd asProjNielsCode 0xA apnArgs = some 0x16 := by decide
theorem apnRestore_end : blockEnd asProjNielsCode 0x52 (restoreBlock apnPs) = some 0x5A := by decide
end

/-- `2d`'s address in the image. -/
abbrev apnD : Word := (img% edwardsD2Address)

/-- Where `as_projective_niels` runs: its code and its callees', the 0x140
bytes of stack below `sp0` that the tail call to `mul` uses, the 160-byte
result at `out`, the 160-byte point at `ip`, and `2d`'s 40 bytes, apart from
what each must not touch. -/
structure APNEnv (M : Word → BitVec 8) (P sp0 out ip : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P asProjNielsCode
  add : CodeIn M (P + 0xFFFFE57A) feAddCode
  addS : CodeIn M (P + 0xFFFFE57A + 0x5D88) memcpyStubCode
  addB : CodeIn M (P + 0xFFFFE57A + 0x5D90) memcpyBodyCode
  sub : CodeIn M (P + 0xFFFFE5C8) feSubCode
  subR : CodeIn M (P + 0xFFFFE5C8 + 0xFFFFF72E) feReduceCode
  mcs : CodeIn M (P + 0x4302) memcpyStubCode
  mcb : CodeIn M (P + 0x430A) memcpyBodyCode
  mul : CodeIn M (P + 0xFFFFD206) feMulCode
  mulR : CodeIn M (P + 0xFFFFD206 + 0xAF0) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x140 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hip : ip.toNat % 4 = 0
  how : out.toNat + 0xA0 < 2 ^ 32
  hiw : ip.toNat + 0xA0 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFEC0) 0x140 P asProjNielsCode.length
  sGA : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xFFFFE57A) feAddCode.length
  sGAS : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xFFFFE57A + 0x5D88) memcpyStubCode.length
  sGAB : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xFFFFE57A + 0x5D90) memcpyBodyCode.length
  sGS : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xFFFFE5C8) feSubCode.length
  sGSR : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xFFFFE5C8 + 0xFFFFF72E) feReduceCode.length
  sGU : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0x4302) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0x430A) memcpyBodyCode.length
  sGM : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xFFFFD206) feMulCode.length
  sGMR : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xFFFFD206 + 0xAF0) feReduceCode.length
  sOC : Sep out 0xA0 P asProjNielsCode.length
  sOA : Sep out 0xA0 (P + 0xFFFFE57A) feAddCode.length
  sOAB : Sep out 0xA0 (P + 0xFFFFE57A + 0x5D90) memcpyBodyCode.length
  sOS : Sep out 0xA0 (P + 0xFFFFE5C8) feSubCode.length
  sOSR : Sep out 0xA0 (P + 0xFFFFE5C8 + 0xFFFFF72E) feReduceCode.length
  sOU : Sep out 0xA0 (P + 0x4302) memcpyStubCode.length
  sOB : Sep out 0xA0 (P + 0x430A) memcpyBodyCode.length
  sOM : Sep out 0xA0 (P + 0xFFFFD206) feMulCode.length
  sOMR : Sep out 0xA0 (P + 0xFFFFD206 + 0xAF0) feReduceCode.length
  sOG : Sep out 0xA0 (sp0 + 0xFFFFFEC0) 0x140
  sIG : Sep ip 0xA0 (sp0 + 0xFFFFFEC0) 0x140
  sIO : Sep ip 0xA0 out 0xA0
  sDG : Sep apnD 40 (sp0 + 0xFFFFFEC0) 0x140
  sDO : Sep apnD 40 out 0xA0

theorem apnSubExt {x y x' y' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) (hy : ∀ i, i < 10 → y i = y' i) :
    feSubSpec x y = feSubSpec x' y' := by
  unfold feSubSpec
  rw [hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide), hx 5 (by decide),
    hx 6 (by decide), hx 7 (by decide), hx 8 (by decide), hx 9 (by decide), hy 0 (by decide), hy 1 (by decide),
    hy 2 (by decide), hy 3 (by decide), hy 4 (by decide), hy 5 (by decide), hy 6 (by decide), hy 7 (by decide),
    hy 8 (by decide), hy 9 (by decide)]

theorem apnCopyIn {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  unfold copyBytes
  rw [add_sub_toNat dst (by omega), ite_eq_left hi, BitVec.add_comm dst, BitVec.add_sub_cancel]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `EdwardsPoint::as_projective_niels`**: from the extended
point at `ip`, it stores at `out` the limbs of `Y + X` as `add` computes
them, `Y - X` as `sub` does, a copy of `Z`, and `T · 2d` as `mul` does. -/
theorem asProjNiels_correct (m : Machine) {P sp0 out ip retAddr : Word} (env : APNEnv m.mem P sp0 out ip)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ip)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ i, i < 10 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (ip + 0x28 + BitVec.ofNat 32 (4 * i)) + memLoad32 m.mem (ip + BitVec.ofNat 32 (4 * i))) ∧
      (wordsAt m'.mem (out + 0x28) 10).map BitVec.toNat =
        feSubSpec (fun i => memLoad32 m.mem (ip + 0x28 + BitVec.ofNat 32 (4 * i)))
          (fun i => memLoad32 m.mem (ip + BitVec.ofNat 32 (4 * i))) ∧
      (∀ j, j < 40 → m'.mem (out + 0x50 + BitVec.ofNat 32 j) = m.mem (ip + 0x50 + BitVec.ofNat 32 j)) ∧
      (wordsAt m'.mem (out + 0x78) 10).map BitVec.toNat = feMulAt m.mem (ip + 0x78) apnD ∧
      ∀ x, Sep (sp0 + 0xFFFFFEC0) 0x140 x 1 → Sep out 0xA0 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFEC0 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGA := env.sGA; have sGAS := env.sGAS; have sGAB := env.sGAB; have sGS := env.sGS
  have sGSR := env.sGSR; have sGU := env.sGU; have sGB := env.sGB; have sGM := env.sGM; have sGMR := env.sGMR
  have sOG := env.sOG; have sIG := env.sIG; have sDG := env.sDG
  rw [hG] at sGC sGA sGAS sGAB sGS sGSR sGU sGB sGM sGMR sOG sIG sDG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hGF : G + BitVec.ofNat 32 0x130 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFEC0) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x130) (by decide)
  have hGw : G.toNat + 0x140 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFEC0 : Word).toNat = 4294966976 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x130 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x10 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x130 + k) := fun k => by
    rw [← hGF, add_ofNat_assoc]
  have gw : G.toNat + 0x140 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x140 → d + k ≤ 0x140 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cInG : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x140 b code'.length → (∀ x, Sep G 0x140 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x140 b code'.length → Sep out 0xA0 b code'.length →
      (∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs ho hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have slotC : ∀ (o : Word), o.toNat + 4 ≤ 0x10 → ∀ {b : Word} {l : Nat}, Sep G 0x140 b l → Sep (F + o) 4 b l := by
    intro o h b l hs
    rw [← ofNat_toNat_self o, eFk]; exact hs.sub (c := 0x130 + o.toNat) (l := 4) (by omega)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod apn_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock apnPs) u1 env.cod apnSave_end (saveBlock_ok _ apnPs _ fun p hp => by
    rw [sp1]
    simp only [apnPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨aligned_add hFa (by decide), slotC _ (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0)) apnPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep G 0x140 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside apnPs fun p hp => by
      simp only [apnPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ apnPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [apnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have hcS : CodeIn Msv P asProjNielsCode := cInG env.cod sGC frSv
  obtain ⟨m3, c3, u3⟩ := St.block apnArgs u2.self hcS apnArgs_end (by simp [BlockOk, BInstr.ok, apnArgs])
  simp only [runBlock, BInstr.run, apnArgs] at u3
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp3 : reg m3 sp = F := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.regs]; exact sp1
  have v3 : reg m3 8 = ip ∧ reg m3 9 = out ∧ reg m3 18 = ip + 0x28 ∧ reg m3 a1 = ip + 0x28 ∧ reg m3 a2 = ip ∧
      reg m3 a0 = out := by
    simp +decide only [u3.regs, upd_app, ↓reduceIte]
    rw [u2.self.zero, r2 a1 (by decide), r2 a0 (by decide), ha1, ha0]
    exact ⟨zw ip, zw out, rfl, zw _, (zw _).trans (zw _), rfl⟩
  obtain ⟨v38, v39, v318, v3a1, v3a2, v3a0⟩ := v3
  have k3 : ∀ q, q.val ≠ 0 → q ≠ sp → q ≠ 8 → q ≠ 9 → q ≠ 18 → q ≠ a1 → q ≠ a2 → reg m3 q = reg m q :=
    fun q hv hs h8 h9 h18 h1 h2 => by
      rw [u3.regs, upd_ne hv h2, upd_ne hv h1, upd_ne hv h18, upd_ne hv h9, upd_ne hv h8, r2 q hs]
  -- `add(out, Y, X)`
  obtain ⟨n4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS apn_at_16 apn_at_1a (cb := P + 0xFFFFE57A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE57A (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have hOw := env.how; have hIw := env.hiw
  have z0 : ∀ {b : Word} {n : Nat} {c : Word} {k : Nat}, Sep (b + BitVec.ofNat 32 0) n c k → Sep b n c k := fun h => by
    rwa [add_ofNat_zero] at h
  have aenv : FeAddEnv n4.mem (P + 0xFFFFE57A) (G + BitVec.ofNat 32 0xE0) out (ip + 0x28) ip := by
    rw [mem4]
    exact ⟨even_at P env.hP 0xFFFFE57A (by decide), cInG env.add sGA frSv, cInG env.addS sGAS frSv,
      cInG env.addB sGAB frSv, aligned_add hGa (k := 0xE0) (by decide),
      by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, env.hip, by omega,
      by rw [BitVec.toNat_add, show (0x28 : Word).toNat = 0x28 from rfl]; omega,
      sGA.sub (by decide), sGAS.sub (by decide), sGAB.sub (by decide),
      z0 (env.sOA.sub (c := 0) (l := 40) (by decide)), z0 (env.sOAB.sub (c := 0) (l := 40) (by decide)),
      z0 ((sOG.sub (c := 0) (l := 40) (by decide)).subR (c := 0xE0) (l := 0x50) (by decide)),
      (sIG.sub (c := 0x28) (l := 40) (by decide)).subR (c := 0xE0) (l := 0x50) (by decide),
      z0 ((sIG.sub (c := 0) (l := 40) (by decide)).subR (c := 0xE0) (l := 0x50) (by decide))⟩
  obtain ⟨n5, c5, pc5, sp5, k5, w5, f5⟩ := feAdd_correct n4 aenv pc4 (by rw [r4 a0 (by decide), v3a0])
    (by rw [r4 a1 (by decide), v3a1]) (by rw [r4 a2 (by decide), v3a2]) (by rw [regs4]; simp +decide [upd])
    (even_clear _ (even_at P env.hP (0x16 + 8) (by decide)))
    (by rw [r4 sp (by decide), sp3, ← hGF, BitVec.add_assoc]; rfl)
  rw [mem4] at w5 f5
  -- the operand's words stay as they were
  have ipM : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → M x = m.mem x) →
      ∀ c j, c + j < 0xA0 → M (ip + BitVec.ofNat 32 c + BitVec.ofNat 32 j) = m.mem (ip + BitVec.ofNat 32 c + BitVec.ofNat 32 j) :=
    fun hM c j h => by
      rw [add_ofNat_assoc]
      exact hM _ (sIG.sub (c := c + j) (l := 1) (by omega)).symm (env.sIO.sub (c := c + j) (l := 1) (by omega)).symm
  have ipW : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → M x = m.mem x) →
      ∀ c i, c + 4 * i + 4 ≤ 0xA0 → memLoad32 M (ip + BitVec.ofNat 32 c + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (ip + BitVec.ofNat 32 c + BitVec.ofNat 32 (4 * i)) := fun hM c i h =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact ipM hM c (4 * i + j) (by omega)
  have frS' : ∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → Msv x = m.mem x := fun x hx _ => frSv x hx
  have w5' : ∀ i, i < 10 → memLoad32 n5.mem (out + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (ip + 0x28 + BitVec.ofNat 32 (4 * i)) + memLoad32 m.mem (ip + BitVec.ofNat 32 (4 * i)) :=
    fun i hi => by
      rw [w5 i hi]
      have h0 := ipW frS' 0 i (by omega); rw [add_ofNat_zero] at h0
      have h1 : memLoad32 Msv (ip + 0x28 + BitVec.ofNat 32 (4 * i)) =
          memLoad32 m.mem (ip + 0x28 + BitVec.ofNat 32 (4 * i)) := ipW frS' 0x28 i (by omega)
      rw [h1, h0]
  have n5G : ∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → n5.mem x = m.mem x := fun x hx ho => by
    rw [f5 x (hx.sub (c := 0xE0) (l := 0x50) (by decide)) (z0 (ho.sub (c := 0) (l := 40) (by decide))), frSv x hx]
  have slot5 : ∀ k, k < 0x10 → n5.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) := fun k hk => by
    rw [f5 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
      (by rw [eFk]; exact z0 ((sOG.sub (c := 0) (l := 40) (by decide)).subR (c := 0x130 + k) (l := 1) (by omega)))]
  have K5 : ∀ q, feMKeep q = true → q ≠ ra → reg n5 q = reg m3 q := fun q hk hr => by rw [k5 q hk, r4 q hr]
  have hc5 := cIn env.cod sGC env.sOC n5G
  have u5 : St n5.mem P n5 0x1E (reg n5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  -- `sub(out + 0x28, Y, X)`
  obtain ⟨n6, c6, u6⟩ := St.block [.aluImm .add a0 (9 : Fin 32) 0x28, .alu .add a1 x0 (18 : Fin 32),
    .alu .add a2 x0 (8 : Fin 32)] u5 hc5 (off' := 0x26) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  obtain ⟨n7, c7, pc7, mem7, regs7⟩ := u6.self.callRa hc5 apn_at_26 apn_at_2a (cb := P + 0xFFFFE5C8)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE5C8 (by decide))
  have r7 := PEnv.reg1 regs7 u6.self.zero
  have senv : FeSubEnv n7.mem (P + 0xFFFFE5C8) (G + BitVec.ofNat 32 0x80) (out + 0x28) (ip + 0x28) ip := by
    rw [mem7]
    exact ⟨even_at P env.hP 0xFFFFE5C8 (by decide), cIn env.sub sGS env.sOS n5G, cIn env.subR sGSR env.sOSR n5G,
      aligned_add hGa (k := 0x80) (by decide), by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega,
      aligned_add env.hip (k := 0x28) (by decide), env.hip, aligned_add env.hout (k := 0x28) (by decide),
      sGS.sub (by decide), sGSR.sub (by decide), env.sOS.sub (c := 0x28) (l := 40) (by decide),
      (sOG.sub (c := 0x28) (l := 40) (by decide)).subR (c := 0x80) (l := 0xB0) (by decide),
      (sIG.sub (c := 0x28) (l := 40) (by decide)).subR (c := 0x80) (l := 0xB0) (by decide),
      z0 ((sIG.sub (c := 0) (l := 40) (by decide)).subR (c := 0x80) (l := 0xB0) (by decide))⟩
  have sp5 : reg n5 sp = F := by rw [sp5, ← hGF, BitVec.add_assoc]; rfl
  obtain ⟨n8, c8, pc8, sp8, k8, w8, f8⟩ := feSub_correct n7 senv pc7
    (by rw [r7 a0 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [K5 9 (by decide) (by decide), v39]; rfl)
    (by rw [r7 a1 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [K5 18 (by decide) (by decide), v318]; exact zw _)
    (by rw [r7 a2 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [K5 8 (by decide) (by decide), v38]; exact zw _)
    (by rw [regs7]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x26 + 8) (by decide)))
    (by rw [r7 sp (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [sp5, ← hGF, BitVec.add_assoc]; rfl)
  rw [mem7] at w8 f8
  have w8' : (wordsAt n8.mem (out + 0x28) 10).map BitVec.toNat =
      feSubSpec (fun i => memLoad32 m.mem (ip + 0x28 + BitVec.ofNat 32 (4 * i)))
        (fun i => memLoad32 m.mem (ip + BitVec.ofNat 32 (4 * i))) := by
    rw [w8]
    exact apnSubExt (fun i hi => ipW n5G 0x28 i (by omega)) (fun i hi => by
      have := ipW n5G 0 i (by omega); rwa [add_ofNat_zero] at this)
  have sp8' : reg n8 sp = F := by rw [sp8, ← hGF, BitVec.add_assoc]; rfl
  have n8G : ∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → n8.mem x = m.mem x := fun x hx ho => by
    rw [f8 x (hx.sub (c := 0x80) (l := 0xB0) (by decide)) (ho.sub (c := 0x28) (l := 40) (by decide)), n5G x hx ho]
  have hc8 := cIn env.cod sGC env.sOC n8G
  have slot8 : ∀ k, k < 0x10 → n8.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) := fun k hk => by
    rw [f8 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
      (by rw [eFk]; exact (sOG.sub (c := 0x28) (l := 40) (by decide)).subR (c := 0x130 + k) (l := 1) (by omega)),
      slot5 k hk]
  have out8 : ∀ t, t < 40 → n8.mem (out + BitVec.ofNat 32 t) = n5.mem (out + BitVec.ofNat 32 t) := fun t ht =>
    f8 _ ((sOG.sub (c := t) (l := 1) (by omega)).symm.sub (c := 0x80) (l := 0xB0) (by decide))
      (sep_offsets out (c := 0x28) (n := 40) (d := t) (k := 1) (.inr (by omega)) (by decide) (by omega))
  have K8 : ∀ q, feMKeep q = true → q ≠ ra → q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n8 q = reg n5 q :=
    fun q hk hr hv h0 h1 h2 => by rw [k8 q hk, r7 q hr, u6.regs, upd_ne hv h2, upd_ne hv h1, upd_ne hv h0]
  have u8 : St n8.mem P n8 0x2E (reg n8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  -- `memcpy(out + 0x50, Z, 40)`
  obtain ⟨n9, c9, u9⟩ := St.block [.aluImm .add a1 (8 : Fin 32) 0x50, .aluImm .add a0 (9 : Fin 32) 0x50,
    .aluImm .add a2 x0 0x28] u8 hc8 (off' := 0x3A) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u9
  obtain ⟨n10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc8 apn_at_3a apn_at_3e (cb := P + 0x4302)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x4302 (by decide))
  have r10 := PEnv.reg1 regs10 u9.self.zero
  have s8_8 : reg n8 8 = ip := by
    rw [K8 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K5 8 (by decide) (by decide), v38]
  have s9_8 : reg n8 9 = out := by
    rw [K8 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K5 9 (by decide) (by decide), v39]
  have sp10 : reg n10 sp = F := by
    rw [r10 sp (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp8'
  have eSc : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x120 := by rw [← hGF, BitVec.add_assoc]; rfl
  obtain ⟨n11, c11, pc11, sp11, a011, f11, k11⟩ := memcpy_correct n10 (P + 0x4302) (P + BitVec.ofNat 32 (0x3A + 8))
    (out + 0x50) (ip + 0x50) 40 (by show CodeIn n10.mem _ _; rw [mem10]; exact cIn env.mcs sGU env.sOU n8G)
    (even_at P env.hP 0x4302 (by decide)) pc10
    (by rw [r10 a0 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s9_8]; rfl)
    (by rw [r10 a1 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s8_8]; rfl)
    (by rw [r10 a2 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs10]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x3A + 8) (by decide)))
    (by
      rw [mem10, sp10, eSc, show P + 0x4302 + 8 = P + 0x430A by rw [BitVec.add_assoc]; rfl]
      exact ⟨cIn env.mcb sGB env.sOB n8G, env.sOB.sub (c := 0x50) (l := 40) (by decide),
        sGB.sub (c := 0x120) (l := 16) (by decide),
        (sOG.sub (c := 0x50) (l := 40) (by decide)).subR (c := 0x120) (l := 16) (by decide),
        (sIG.sub (c := 0x50) (l := 40) (by decide)).subR (c := 0x120) (l := 16) (by decide),
        ((env.sIO.sub (c := 0x50) (l := 40) (by decide)).subR (c := 0x50) (l := 40) (by decide)).symm,
        aligned_add hGa (k := 0x120) (by decide), by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega,
        by rw [BitVec.toNat_add, show (0x50 : Word).toNat = 0x50 from rfl]; omega,
        by rw [BitVec.toNat_add, show (0x50 : Word).toNat = 0x50 from rfl]; omega⟩)
  rw [sp10, eSc] at f11
  rw [mem10] at f11
  have n11G : ∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → n11.mem x = m.mem x := fun x hx ho => by
    rw [f11 x (hx.sub (c := 0x120) (l := 16) (by decide)),
      copyBytes_sep (dst := out + 0x50) (n := 40) (ho.sub (c := 0x50) (l := 40) (by decide)) (Nat.le_refl _), n8G x hx ho]
  have hc11 := cIn env.cod sGC env.sOC n11G
  have outS : ∀ t, t < 0xA0 → Sep (G + BitVec.ofNat 32 0x120) 16 (out + BitVec.ofNat 32 t) 1 := fun t ht =>
    ((sOG.sub (c := t) (l := 1) (by omega)).symm.sub (c := 0x120) (l := 16) (by decide))
  have slot11 : ∀ k, k < 0x10 → n11.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) := fun k hk => by
    rw [f11 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega)),
      copyBytes_sep (dst := out + 0x50) (n := 40)
        (by rw [eFk]; exact (sOG.sub (c := 0x50) (l := 40) (by decide)).subR (c := 0x130 + k) (l := 1) (by omega))
        (Nat.le_refl _), slot8 k hk]
  have out11 : ∀ t, t < 0x50 → n11.mem (out + BitVec.ofNat 32 t) = n8.mem (out + BitVec.ofNat 32 t) := fun t ht => by
    rw [f11 _ (outS t (by omega)), copyBytes_sep (dst := out + 0x50) (n := 40)
      (sep_offsets out (c := 0x50) (n := 40) (d := t) (k := 1) (.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _)]
  have z11 : ∀ j, j < 40 → n11.mem (out + 0x50 + BitVec.ofNat 32 j) = m.mem (ip + 0x50 + BitVec.ofNat 32 j) :=
    fun j hj => by
      rw [show out + 0x50 + BitVec.ofNat 32 j = out + BitVec.ofNat 32 (0x50 + j) by rw [← add_ofNat_assoc]; rfl,
        f11 _ (outS _ (by omega)), ← add_ofNat_assoc, show out + BitVec.ofNat 32 0x50 = out + 0x50 from rfl,
        apnCopyIn hj (by decide)]
      exact ipM n8G 0x50 j (by omega)
  have u11 : St n11.mem P n11 0x42 (reg n11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have K11 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n11 q = reg n8 q :=
    fun q hq => by
      have h : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧
          q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ sp ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 := by
        revert hq; revert q; decide
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
      rw [k11 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14, r10 q h15, u9.regs, upd_ne h16 h2, upd_ne h16 h17,
        upd_ne h16 h1]
  -- `mul(out + 0x78, T, 2d)`, as a tail call
  obtain ⟨n12, c12, u12⟩ := St.block [.aluImm .add a1 (8 : Fin 32) 0x78, .aluImm .add a0 (9 : Fin 32) 0x78,
    .lui a2 (img% hi20 edwardsD2Address), .aluImm .add a2 a2 (img% lo12 edwardsD2Address)] u11 hc11 (off' := 0x52) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u12
  simp +decide only [upd_app, ↓reduceIte] at u12
  have sp11' : reg n11 sp = F := by rw [sp11, sp10]
  have hpsp : ∀ p ∈ apnPs, p.1 ≠ sp := by decide
  have rsp12 : upd (upd (upd (upd (reg n11) a1 (aluEval .add (reg n11 8) 0x78)) a0 (aluEval .add (reg n11 9) 0x78)) a2
      (img% hi20 edwardsD2Address)) a2 (aluEval .add (img% hi20 edwardsD2Address) (img% lo12 edwardsD2Address)) sp = F := by simp +decide only [upd_app, ↓reduceIte]; exact sp11'
  obtain ⟨n13, c13, u13⟩ := St.block (restoreBlock apnPs) u12 hc11 apnRestore_end
    (restoreBlock_ok n11.mem F apnPs _ rsp12 hpsp fun q hq => by
      simp only [apnPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run n11.mem F apnPs _ rsp12 hpsp] at u13
  obtain ⟨n14, d14, u14⟩ := u13.aluImm hc11 apn_at_5a (off' := 0x5C) (by decide)
  obtain ⟨n15, d15, u15⟩ := u14.self.auipc hc11 apn_at_5c (off' := 0x60) (by decide)
  obtain ⟨n16, d16, pc16, mem16, regs16⟩ := u15.self.jalr hc11 apn_at_60
  have slotW : ∀ r o, (r, o) ∈ apnPs → memLoad32 n11.mem (F + o) = reg m r := fun r o h => by
    have ho : o.toNat + 4 ≤ 0x10 := by
      simp only [apnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, slot11 _ (by omega)]
  obtain ⟨R, hR⟩ : ∃ R, restoreRegs n11.mem F (upd (upd (upd (upd (reg n11) a1 (aluEval .add (reg n11 8) 0x78)) a0
      (aluEval .add (reg n11 9) 0x78)) a2 (img% hi20 edwardsD2Address)) a2 (aluEval .add (img% hi20 edwardsD2Address) (img% lo12 edwardsD2Address))) apnPs = R := ⟨_, rfl⟩
  rw [hR] at u14
  have rrG : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs n11.mem F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have rr : ∀ q, (∀ p ∈ apnPs, p.1 ≠ q) → q.val ≠ 0 → R q = upd (upd (upd (upd (reg n11) a1
      (aluEval .add (reg n11 8) 0x78)) a0 (aluEval .add (reg n11 9) 0x78)) a2 (img% hi20 edwardsD2Address)) a2
      (aluEval .add (img% hi20 edwardsD2Address) (img% lo12 edwardsD2Address)) q := fun q h h0 => by rw [← hR]; exact rrG _ _ q h0 h
  have Rsv : ∀ r o, (r, o) ∈ apnPs → R r = reg m r := fun r o hm => by
    rw [← hR]
    simp only [apnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  have Rsp : R sp = F := by rw [rr sp hpsp (by decide)]; exact rsp12
  have ra0 : R a0 = out + 0x78 := by
    rw [rr a0 (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [K11 9 (by decide), s9_8]; rfl
  have ra1 : R a1 = ip + 0x78 := by
    rw [rr a1 (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [K11 8 (by decide), s8_8]; rfl
  have ra2 : R a2 = apnD := by rw [rr a2 (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
  have g16 : ∀ q, q ≠ sp → q ≠ t1 → reg n16 q = R q := fun q hs ht => by
    rw [regs16, u15.regs, updz u14.self.zero ht, u14.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this
      rw [upd_zero, ← hR]; simp only [restoreRegs, upd_zero]
    rw [upd_ne h0 hs]
  have pc16' : n16.pc = P + 0xFFFFD206 := by
    rw [pc16, u15.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0x5C + 0xFFFFD000 + 0x1AA = P + 0xFFFFD206 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P env.hP 0xFFFFD206 (by decide))
  have sp16 : reg n16 sp = sp0 := by
    rw [regs16, u15.regs, upd_ne (by decide) (by decide), u14.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [ev_add, Rsp, eS]
  have n16G : ∀ x, Sep G 0x140 x 1 → Sep out 0xA0 x 1 → n16.mem x = m.mem x := fun x hx ho => by
    rw [mem16, n11G x hx ho]
  have menv : FeMEnv n16.mem (P + 0xFFFFD206) sp0 (out + 0x78) (ip + 0x78) apnD := by
    refine ⟨even_at P env.hP 0xFFFFD206 (by decide), cIn env.mul sGM env.sOM n16G, cIn env.mulR sGMR env.sOMR n16G,
      env.hsp, env.hS, aligned_add env.hout (k := 0x78) (by decide), aligned_add env.hip (k := 0x78) (by decide),
      by decide, by rw [hG]; exact sGM, by rw [hG]; exact sGMR, env.sOM.sub (c := 0x78) (l := 40) (by decide),
      env.sOMR.sub (c := 0x78) (l := 40) (by decide), by rw [hG]; exact sOG.sub (c := 0x78) (l := 40) (by decide),
      by rw [hG]; exact sIG.sub (c := 0x78) (l := 40) (by decide), by rw [hG]; exact sDG⟩
  obtain ⟨mf, cf, pcf, spf, kf, wf, ff⟩ := feMul_correct n16 menv pc16'
    (by rw [g16 a0 (by decide) (by decide), ra0]) (by rw [g16 a1 (by decide) (by decide), ra1])
    (by rw [g16 a2 (by decide) (by decide), ra2]) (by rw [g16 ra (by decide) (by decide), Rsv ra 0xC (by decide), hra])
    hret sp16
  rw [hG] at ff
  have outF : ∀ t, t < 0x78 → mf.mem (out + BitVec.ofNat 32 t) = n11.mem (out + BitVec.ofNat 32 t) := fun t ht => by
    rw [ff _ (sOG.sub (c := t) (l := 1) (by omega)).symm
      (sep_offsets out (c := 0x78) (n := 40) (d := t) (k := 1) (.inr (by omega)) (by decide) (by omega)), mem16]
  refine ⟨mf, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (.cons d14 (.cons d15 (.cons d16 cf))))))))))))))), pcf, spf, fun q hq => ?_,
    fun i hi => ?_, ?_, fun j hj => ?_, ?_, fun x hx ho => ?_⟩
  · have hk : feMKeep q = true := by revert hq; revert q; decide
    rw [kf q hk, g16 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)]
    by_cases hr : q = ra
    · subst hr; exact Rsv ra 0xC (by decide)
    by_cases h8 : q = 8
    · subst h8; exact Rsv 8 0x8 (by decide)
    by_cases h9 : q = 9
    · subst h9; exact Rsv 9 0x4 (by decide)
    by_cases h18 : q = 18
    · subst h18; exact Rsv 18 0x0 (by decide)
    have h : (∀ p ∈ apnPs, p.1 ≠ q) ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ sp ∧
        q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      revert hq hr h8 h9 h18; revert q; decide
    obtain ⟨hp, h0, ha0', ha1', ha2', hs, hl⟩ := h
    rw [rr q hp h0, upd_ne h0 ha2', upd_ne h0 ha2', upd_ne h0 ha0', upd_ne h0 ha1', K11 q hl,
      K8 q hk hr h0 ha0' ha1' ha2', K5 q hk hr, k3 q h0 hs h8 h9 h18 ha1' ha2']
  · rw [← w5' i hi]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, outF _ (by omega), out11 _ (by omega), out8 _ (by omega)]
  · rw [← w8']
    congr 1
    exact wordsAt_bytes fun t ht => by
      rw [show out + 0x28 + BitVec.ofNat 32 t = out + BitVec.ofNat 32 (0x28 + t) by rw [← add_ofNat_assoc]; rfl,
        outF _ (by omega), out11 _ (by omega)]
  · rw [show out + 0x50 + BitVec.ofNat 32 j = out + BitVec.ofNat 32 (0x50 + j) by rw [← add_ofNat_assoc]; rfl,
      outF _ (by omega), ← z11 j hj, ← add_ofNat_assoc]; rfl
  · exact wf.trans (feMulAt_congr (fun t ht => by
        rw [mem16, show ip + 0x78 + BitVec.ofNat 32 t = ip + BitVec.ofNat 32 (0x78 + t) by
          rw [← add_ofNat_assoc]; rfl]
        exact n11G _ (sIG.sub (c := 0x78 + t) (l := 1) (by omega)).symm
          (env.sIO.sub (c := 0x78 + t) (l := 1) (by omega)).symm)
      (fun t ht => n16G _ (sDG.sub (c := t) (l := 1) (by omega)).symm (env.sDO.sub (c := t) (l := 1) (by omega)).symm))
  · rw [ff x hx (ho.sub (c := 0x78) (l := 40) (by decide)), n16G x hx ho]

end C3.RV32
