import C3BootProofs.Proofs.Pv384DI
import C3BootProofs.Proofs.Pv384B

/-!
# `p384_verify_prehash`

The stages composed, from the entry to the return: the result is
`pvModel` of the inputs, or the function panics exactly when `pvModel` is
`none`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

instance (M : Word → BitVec 8) (pk rp sp' : Word) : Decidable (PvCk1 M pk rp sp') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (M : Word → BitVec 8) (rp sp' : Word) : Decidable (PvCk2 M rp sp') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The inverse of `s` the model computes. -/
def pvW (M : Word → BitVec 8) (sp' : Word) : Iv := ivLoop 0x376 (ivInit (beNat (memBytes M sp' 48) * 2 ^ 384 % n384))

/-- The sum `u1·G + u2·Q` the model computes. -/
def pvSumM (M : Word → BitVec 8) (pk ph : Word) (len : Nat) (rp sp' : Word) : Option Pt :=
  pvSum (Fs.fsVal M pk 1 * 2 ^ 384 % p384) (Fs.fsVal M pk 0x31 * 2 ^ 384 % p384)
    (beNat (memBytes M rp 48) * 2 ^ 384 % n384) (beNat (memBytes M ph (min len 48)) * 2 ^ 384 % n384)
    (pvInv (pvW M sp'))

/-- What `p384_verify_prehash` returns for the key at `pk`, the `len`-byte
prehash at `ph`, and `r` and `s` at `rp` and `sp'`, or `none` when it
panics. -/
def pvModel (M : Word → BitVec 8) (pk ph : Word) (len : Nat) (rp sp' : Word) : Option Word :=
  if PvCk1 M pk rp sp' ∧ PvCk2 M rp sp' then
    if (pvW M sp').f.natAbs = 1 then
      (pvSumM M pk ph len rp sp').map fun P => pvH (beNat (memBytes M rp 48) * 2 ^ 384 % n384) P.1 P.2.2
    else none
  else some 0

/-- What the model's inversions must leave for the proof to apply: the
inverse of `s` below `n`, and the inverse of `Z` below `p`. -/
structure PvSide (M : Word → BitVec 8) (pk ph : Word) (len : Nat) (rp sp' : Word) : Prop where
  w : PvCk1 M pk rp sp' → PvCk2 M rp sp' → (pvW M sp').f.natAbs = 1 → pvInv (pvW M sp') < n384
  z : PvCk1 M pk rp sp' → PvCk2 M rp sp' → (pvW M sp').f.natAbs = 1 → ∀ P, pvSumM M pk ph len rp sp' = some P →
    hvOk P.2.2 → hvInv (hvLoop 15 (hvInit P.2.2)) < p384

/-- `M'` agrees with `M` outside the frame and the saves. -/
def PvOut (B : Word) (M M' : Word → BitVec 8) : Prop := ∀ x, Sep (B + 0xFFFFFE60) 0x2340 x 1 → M' x = M x

theorem PvOut.of_pvR {B : Word} {M M' M'' : Word → BitVec 8} (h : PvOut B M M') (h' : ∀ x, PvR B x → M'' x = M' x) :
    PvOut B M M'' := fun x hx => by
  rw [h' x (by have := hx.sub (c := 0) (l := 0x230C) (by decide); rwa [add_ofNat_zero] at this), h x hx]

theorem PvOut.bytes {B p : Word} {M M' : Word → BitVec 8} (h : PvOut B M M') {k : Nat}
    (hp : Sep p k (B + 0xFFFFFE60) 0x2340) : memBytes M' p k = memBytes M p k :=
  memBytes_congr fun i hi => h _ (by
    have := (hp.sub (c := i) (l := 1) (by omega)).symm; exact this)

theorem PvOut.bytes' {B p : Word} {M M' : Word → BitVec 8} (h : PvOut B M M') {k k' : Nat}
    (hp : Sep p k (B + 0xFFFFFE60) 0x2340) (hk : k' ≤ k) : memBytes M' p k' = memBytes M p k' :=
  memBytes_congr fun i hi => h _ (by
    have := (hp.sub (c := i) (l := 1) (by omega)).symm; exact this)

theorem fsVal_out {B pk : Word} {M M' : Word → BitVec 8} (h : PvOut B M M')
    (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x2340) {o : Nat} (ho : o + 48 ≤ 0x61) :
    Fs.fsVal M' pk o = Fs.fsVal M pk o := by
  unfold Fs.fsVal; rw [h.bytes (sPK.sub (c := o) (l := 48) ho)]

theorem pvOut_hi {B : Word} (F : Fr B 0x21A0) {x : Word} (hx : 0x40000000 ≤ x.toNat) :
    Sep (B + 0xFFFFFE60) 0x2340 x 1 := by
  have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have := F.lo; have := F.hi
  exact sep_of_le (by rw [hb]; omega) (by have := x.isLt; omega)

theorem PvEnv7.out {B : Word} {M M' : Word → BitVec 8} (E : PvEnv7 M) (F : Fr B 0x21A0) (h : PvOut B M M') :
    PvEnv7 M' :=
  have hh : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x := fun x hx => h x (pvOut_hi F hx)
  ⟨⟨⟨⟨⟨⟨E.E.E.E.E.E.C.hi hh, E.E.E.E.E.E.D.of F h, E.E.E.E.E.E.C2.hi hh, E.E.E.E.E.E.D2.of F h⟩,
    E.E.E.E.E.C3.hi hh, E.E.E.E.E.D3.of F h⟩, E.E.E.E.C4.hi hh⟩, E.E.E.C5.hi hh⟩, E.E.C6.hi hh⟩,
    E.C7.hi hh, F.dataIn h E.aid (by decide) (by decide)⟩

theorem pvR_save {B : Word} (F : Fr B 0x21A0) {c : Nat} (h1 : 0x216C ≤ c) (h2 : c + 1 ≤ 0x21A0) :
    PvR B (B + BitVec.ofNat 32 c) := by
  have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have := F.lo; have := F.hi
  have hc : (B + BitVec.ofNat 32 c).toNat = B.toNat + c := F.at c (by omega)
  exact sep_of_le (by rw [hb, hc]; omega) (by rw [hc]; omega)

theorem sep_frame {B p : Word} {k : Nat} (h : Sep p k (B + 0xFFFFFE60) 0x2340) : Sep p k (B + 0xFFFFFE60) 0x230C := by
  have := h.subR (c := 0) (l := 0x230C) (by decide); rwa [add_ofNat_zero] at this

theorem pvCk1_out {B pk rp sp' : Word} {M M' : Word → BitVec 8} (F : Fr B 0x21A0) (h : PvOut B M M')
    (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x2340) (sR : Sep rp 48 (B + 0xFFFFFE60) 0x2340)
    (sS : Sep sp' 48 (B + 0xFFFFFE60) 0x2340) : PvCk1 M' pk rp sp' ↔ PvCk1 M pk rp sp' := by
  have sI : Sep ISRN 48 (B + 0xFFFFFE60) 0x2340 := by
    have := F.dsep.subR (c := 0x270) (l := 48) (by decide); exact this.symm
  have e1 : ∀ o, o + 48 ≤ 0x61 → Fs.fsVal M' pk o = Fs.fsVal M pk o := fun o ho => by
    unfold Fs.fsVal; rw [h.bytes (sPK.sub (c := o) (l := 48) ho)]
  have e0 : M' pk = M pk := h pk (by
    have := (sPK.sub (c := 0) (l := 1) (by decide)).symm; rwa [add_ofNat_zero] at this)
  unfold PvCk1 Fs.FsOk
  rw [h.bytes sR, h.bytes sS, h.bytes sI, e1 1 (by decide), e1 0x31 (by decide), e0]

theorem pvCk2_out {B rp sp' : Word} {M M' : Word → BitVec 8} (h : PvOut B M M')
    (sR : Sep rp 48 (B + 0xFFFFFE60) 0x2340) (sS : Sep sp' 48 (B + 0xFFFFFE60) 0x2340) :
    PvCk2 M' rp sp' ↔ PvCk2 M rp sp' := by
  unfold PvCk2; rw [h.bytes sR, h.bytes sS]

set_option exponentiation.threshold 600 in
set_option maxHeartbeats 64000000 in
/-- **`p384_verify_prehash`**, from its entry to its return: the result is
`pvModel` of the inputs, or it panics exactly when `pvModel` is `none`. It
returns with `sp`, `ra`, `s0` to `s11`, `gp`, and `tp` as they were, and
changes no memory outside its frame. -/
theorem p384VerifyPrehash_correct (m : Machine) {B pk ph rp sp' retAddr : Word} {len : Nat}
    (E : PvEnv7 m.mem) (F : Fr B 0x21A0) (hpc : m.pc = PV) (hsp : reg m sp = B + 0x21A0)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = ph) (ha2 : reg m a2 = BitVec.ofNat 32 len) (ha3 : reg m a3 = rp)
    (ha4 : reg m a4 = sp') (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x2340) (hPK : pk.toNat + 0x61 ≤ 0x40000000)
    (sR : Sep rp 48 (B + 0xFFFFFE60) 0x2340) (sS : Sep sp' 48 (B + 0xFFFFFE60) 0x2340)
    (sph : Sep ph len (B + 0xFFFFFE60) 0x2340) (hph : ph.toNat + len < 2 ^ 32)
    (side : PvSide m.mem pk ph len rp sp') :
    (pvModel m.mem pk ph len rp sp' = none ∧ Panics m) ∨
    (∃ v, pvModel m.mem pk ph len rp sp' = some v ∧
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = B + 0x21A0 ∧
        (∀ k, k < 13 → reg m' (savedReg k) = reg m (savedReg k)) ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ reg m' a0 = v ∧
        PvOut B m.mem m'.mem) := by
  have s : St m.mem PV m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have E1 := E.E.E.E.E.E
  obtain ⟨n1, c1, s1, sp1, r1_8, r1_20, r1_19, r1_9, r1_21, r1_a0, r1_a1, r1_a2, r1_a3, k1⟩ := pv_pro E1.C F s hsp
  have O1 : PvOut B m.mem (pvSaves m.mem B m) := fun x hx => pvSaves_out (by
    have := hx.sub (c := 0x230C) (l := 0x34) (by decide)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 0x230C = BitVec.ofNat 32 0x216C from rfl] at this)
  have m1 : n1.mem = pvSaves m.mem B m := s1.mem
  have E1' : PvEnv7 n1.mem := by rw [m1]; exact E.out F O1
  -- the epilogue, from any exit at 0x130
  have fin : ∀ {n : Machine} {v : Word}, Steps m n → St n.mem PV n 0x130 (reg n) → reg n sp = B + 0x420 →
      reg n a0 = v → reg n (3 : Fin 32) = reg m (3 : Fin 32) → reg n (4 : Fin 32) = reg m (4 : Fin 32) →
      (∀ x, PvR B x → n.mem x = n1.mem x) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = B + 0x21A0 ∧
        (∀ k, k < 13 → reg m' (savedReg k) = reg m (savedReg k)) ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ reg m' a0 = v ∧
        PvOut B m.mem m'.mem := fun {n v} c sn spn an r3 r4 frn => by
    have On : PvOut B m.mem n.mem := (m1 ▸ O1).of_pvR frn
    have hS : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x219C - 4 * k)) = reg m (savedReg k) :=
      fun k hk => by
        rw [← pvSaves_read k hk, ← m1]
        exact memLoad32_congr fun j hj => by
          rw [add_ofNat_assoc]; exact frn _ (pvR_save F (by omega) (by omega))
    obtain ⟨m', c', pc', mem', sp', sv', a0', r3', r4'⟩ := pv_epi (E.out F On).E.E.E.E.E.C F sn spn hS
      (by rw [show reg m (savedReg 0) = retAddr from hra]; exact hret)
    exact ⟨m', c.trans c', by rw [pc']; exact hra, sp', sv', by rw [r3', r3], by rw [r4', r4], by rw [a0', an],
      by rw [mem']; exact On⟩
  have O1' : PvOut B m.mem n1.mem := m1 ▸ O1
  have sRf := sep_frame sR
  have sSf := sep_frame sS
  -- the first checks
  obtain ⟨n2, c2, fr2, sp2, k2, h2⟩ := pv_stA1 (E.out F O1).E.E.E.E.E.C (E.out F O1).E.E.E.E.E.D F s1 sp1
    (by rw [r1_a0, ha3]) r1_a1 r1_a2 r1_a3 (by rw [r1_8, ha0]) (by rw [r1_21, ha4]) (sep_frame sPK) hPK
  rw [← m1] at fr2
  have O2 : PvOut B m.mem n2.mem := O1'.of_pvR fr2
  have hc1 := pvCk1_out (pk := pk) (rp := rp) (sp' := sp') F O1 sPK sR sS
  rcases h2 with ⟨s2, a2, nc1⟩ | ⟨s2, ok1, C2, D2, a2_bc, a2_ec, b2_11c⟩
  · refine .inr ⟨0, by rw [pvModel, ite_eq_right (fun h => nc1 (hc1.2 h.1))], fin (c1.trans c2) s2 sp2 a2
      (by rw [k2 3 (by decide), k1 3 (by decide)]) (by rw [k2 4 (by decide), k1 4 (by decide)]) fr2⟩
  have hk1 : PvCk1 m.mem pk rp sp' := hc1.1 ok1
  -- the other checks
  obtain ⟨n3, c3, fr3, sp3, k3, h3⟩ := pv_stA2 C2 D2 F s2 sp2 (by rw [k2 9 (by decide), r1_9, ha3])
    (by rw [k2 21 (by decide), r1_21, ha4]) sRf sSf
  have O3 : PvOut B m.mem n3.mem := O2.of_pvR fr3
  have hc2 := pvCk2_out (rp := rp) (sp' := sp') O2 sR sS
  rcases h3 with ⟨s3, a3, nc2⟩ | ⟨s3, ok2, -, -, a3_58, a3_88, a3_270, a3_17a4, r3_18, r3_8⟩
  · refine .inr ⟨0, by rw [pvModel, ite_eq_right (fun h => nc2 (hc2.2 h.2))], fin (c1.trans (c2.trans c3)) s3 sp3 a3
      (by rw [k3 3 (by decide), k2 3 (by decide), k1 3 (by decide)])
      (by rw [k3 4 (by decide), k2 4 (by decide), k1 4 (by decide)]) fun x hx => by rw [fr3 x hx, fr2 x hx]⟩
  have hk2 : PvCk2 m.mem rp sp' := hc2.1 ok2
  rw [a2_bc, fsVal_out O1 sPK (by decide)] at a3_58
  rw [a2_ec, fsVal_out O1 sPK (by decide)] at a3_88
  rw [O2.bytes sR] at a3_270
  rw [O2.bytes sS] at a3_17a4
  have b3 : (n2.mem (B + 0x420 + BitVec.ofNat 32 0x11C)).zeroExtend 32 = BitVec.ofNat 32 0 := by rw [b2_11c]; rfl
  -- stage B
  obtain ⟨n4, t4, s4, E4, f4, g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25,
      g4_26, g4_27, a4_58, a4_88, a4_120, a4_150, a4_180, a4_1b0, a4_1e0, a4_210, a4_270, a4_3f0, a4_420, a4_d50,
      a4_e10, a4_e40, a4_1294, a4_12c4, a4_12f4, a4_1714, a4_17a4, b4_1744, w4_e70, w4_e74⟩ :=
    pv_stB F (E.out F O3).E.E.E.E.E s3 sp3 r3_8 (by rw [r3_18, b3])
      (by rw [k3 19 (by decide), k2 19 (by decide), r1_19, ha2]) (by rw [k3 20 (by decide), k2 20 (by decide), r1_20, ha1])
      a3_58 a3_88 a3_270 a3_17a4 hk2.2.2.1 hk2.1 hk2.2.2.2 hk2.2.1 hph (sep_frame sph)
  have O4 : PvOut B m.mem n4.mem := O3.of_pvR f4
  rw [O3.bytes' sph (Nat.min_le_left _ _)] at a4_210
  -- stage C
  rcases pv_stC F (E.out F O4).E.E.E.E s4 g4_2 g4_8 g4_9 g4_18 g4_19 g4_20 g4_21 g4_22 g4_23 g4_24 a4_120 a4_150
      a4_180 a4_1b0 a4_1e0 (by rw [a4_210, O4.bytes' sph (Nat.min_le_left _ _)]) a4_d50 a4_e10 a4_e40 a4_1714 b4_1744
      w4_e70 w4_e74 with
    ⟨hf, n5, t5, s5, E5, f5, g5_2, g5_3, g5_4, g5_9, g5_18, g5_25, a5_120, a5_150, a5_180, a5_1b0, a5_1e0, a5_210,
      a5_e10⟩ | ⟨hnf, hp⟩
  rotate_left
  · exact .inl ⟨by rw [pvModel, ite_eq_left ⟨hk1, hk2⟩, ite_eq_right (show ¬(pvW m.mem sp').f.natAbs = 1 from hnf)], Panics.of_steps (c1.trans (c2.trans (c3.trans t4))) hp⟩
  have O5 : PvOut B m.mem n5.mem := O4.of_pvR f5
  rw [O4.bytes' sph (Nat.min_le_left _ _)] at a5_210
  -- stages D to I
  have hQ : PtLt (Fs.fsVal m.mem pk 1 * 2 ^ 384 % p384, Fs.fsVal m.mem pk 0x31 * 2 ^ 384 % p384,
      dataVal p384MontOneData 0 12) :=
    ⟨Nat.mod_lt _ p384_pos, Nat.mod_lt _ p384_pos, by show dataVal p384MontOneData 0 12 < p384; unfold p384; decide⟩
  rcases pv_stDI F (E.out F O5) s5 g5_2 g5_18 g5_25 a5_120 a5_150 a5_180 a5_1b0 a5_1e0 a5_210 a5_e10
      (side.w hk1 hk2 hf) hQ (side.z hk1 hk2 hf) with ⟨hn, hp⟩ | ⟨P, hP, n6, t6, s6, E6, f6, sp6, r36, r46, a6⟩
  · refine .inl ⟨?_, Panics.of_steps (c1.trans (c2.trans (c3.trans (t4.trans t5)))) hp⟩
    rw [pvModel, ite_eq_left ⟨hk1, hk2⟩, ite_eq_left (show (pvW m.mem sp').f.natAbs = 1 from hf), show pvSumM m.mem pk ph len rp sp' = none from hn]; rfl
  · refine .inr ⟨_, ?_, fin (c1.trans (c2.trans (c3.trans (t4.trans (t5.trans t6))))) s6 sp6 a6
      (by rw [r36, g5_3, g4_3, k3 3 (by decide), k2 3 (by decide), k1 3 (by decide)])
      (by rw [r46, g5_4, g4_4, k3 4 (by decide), k2 4 (by decide), k1 4 (by decide)])
      fun x hx => by rw [f6 x hx, f5 x hx, f4 x hx, fr3 x hx, fr2 x hx]⟩
    rw [pvModel, ite_eq_left ⟨hk1, hk2⟩, ite_eq_left (show (pvW m.mem sp').f.natAbs = 1 from hf), show pvSumM m.mem pk ph len rp sp' = some P from hP]; rfl

end C3.RV32.Pv
