import C3BootProofs.Proofs.AcceptTargetsTail
import C3BootProofs.Proofs.SvSpecAux

/-!
# The hex of `trusted_root.json`'s digest

From 0xB28: the SHA-256 digest of the trusted root, written out as 64
lowercase hex digits at `sp + 0x1870` and copied to `sp + 0x1ED0`, where
`act_tail` reads it.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

/-- One hex digit, as `hexBytes` writes it. -/
def actHd (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

theorem act_hex_len (b : Bytes) : (hexBytes b).length = 2 * b.length := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    simp only [hexBytes, List.flatMap_cons, List.length_append, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil] at ih ⊢
    omega

theorem act_hex_get (b : Bytes) (k : Nat) (hk : k < b.length) :
    (hexBytes b).getD (2 * k) 0 = actHd (b.getD k 0 / 16) ∧
      (hexBytes b).getD (2 * k + 1) 0 = actHd (b.getD k 0 % 16) := by
  induction b generalizing k with
  | nil => simp at hk
  | cons x b ih =>
    have e : hexBytes (x :: b) = actHd (x / 16) :: actHd (x % 16) :: hexBytes b := by
      simp only [hexBytes, List.flatMap_cons, List.map_cons, List.map_nil, actHd]; rfl
    rw [e]
    cases k with
    | zero => simp
    | succ k =>
      have := ih k (by simp at hk; omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, show 2 * k + 2 + 1 = 2 * k + 1 + 2 by omega]
      simpa using this

theorem act_z0 (x : Word) : x + 0 = x := BitVec.add_zero x

theorem act_hd_at : ∀ d, d < 16 → (byteAt acHexDigitsData d).toNat = actHd d := by decide

theorem act_ofNat_ne {H : Word} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) :
    H + BitVec.ofNat 32 a ≠ H + BitVec.ofNat 32 b := fun e => by
  have e2 := congrArg (fun y => (y - H).toNat) e
  simp only [BitVec.add_comm H, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e2
  exact h e2

theorem act_sne {x H : Word} {n j : Nat} (h : Sep x 1 H n) (hj : j < n) : x ≠ H + BitVec.ofNat 32 j := by
  have := h 0 (by decide) j hj
  simpa using this

theorem act_srl4 (b : BitVec 8) : aluEval .srl (b.zeroExtend 32) 0x4 = BitVec.ofNat 32 (b.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [aluEval]
  rw [show (0x4 : Word).toNat % 32 = 4 from rfl]
  simp only [BitVec.toNat_ushiftRight, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem act_and15 : ∀ n, n < 256 → n &&& 15 = n % 16 := by decide

theorem act_andF (b : BitVec 8) : aluEval .and (b.zeroExtend 32) 0xF = BitVec.ofNat 32 (b.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [aluEval, BitVec.toNat_and, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [show (0xF : Word).toNat = 15 from rfl, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32),
    act_and15 _ b.isLt, Nat.mod_eq_of_lt (by omega : b.toNat % 16 < 2 ^ 32)]

theorem act_lbu_low (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]; omega

theorem act_dec (n : Nat) (h : n < 2 ^ 32) :
    BitVec.ofNat 32 (n + 1) + (0xFFFFFFFF : Word) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
  omega

section
variable {Q : Word → (Word → BitVec 8) → (Fin 32 → Word) → Prop}

/-- What the hex loop keeps of the registers. -/
def ActHexRegs (f0 f : Fin 32 → Word) : Prop :=
  ∀ r : Fin 32, r.val ≠ 8 → r.val ≠ 10 → r.val ≠ 11 → r.val ≠ 13 → r.val ≠ 14 → f r = f0 r

theorem act_hr_upd {f0 f : Fin 32 → Word} {rd : Fin 32} {v : Word} (h00 : f0 0 = 0) (hR : ActHexRegs f0 f)
    (hrd : rd.val = 8 ∨ rd.val = 10 ∨ rd.val = 11 ∨ rd.val = 13 ∨ rd.val = 14 := by decide) :
    ActHexRegs f0 (upd f rd v) := by
  intro r h8 h10 h11 h13 h14
  unfold upd
  split
  · rename_i h; rw [show r = 0 from Fin.ext h]; exact h00.symm
  · rw [if_neg (fun e => by subst e; omega)]; exact hR r h8 h10 h11 h13 h14

/-- **The hex loop**, from 0xB7E with `k < 32` digits done: the digest
`dig` at `D`, the digit table at 0x3FCC49A0, and the `2k` hex digits so
far at `H`. -/
theorem act_hex_loop {D H : Word} {dig : Bytes} {M0 : Word → BitVec 8} {f0 : Fin 32 → Word}
    (hdl : dig.length = 32)
    (hD : ∀ i, i < 32 → (M0 (D + BitVec.ofNat 32 i)).toNat = dig.getD i 0)
    (hT : ∀ i, i < 16 → M0 (BitVec.ofNat 32 0x3FCC49A0 + BitVec.ofNat 32 i) = byteAt acHexDigitsData i)
    (sD : Sep H 64 D 32) (sT : Sep H 64 (BitVec.ofNat 32 0x3FCC49A0) 16)
    (sC : Sep H 64 AC bootMainClosure0Code.length) (h12 : f0 a2 = BitVec.ofNat 32 0x3FCC49A0)
    (h00 : f0 0 = 0)
    (K : ∀ M' f', (∀ x, Sep x 1 H 64 → M' x = M0 x) → memBytes M' H 64 = hexBytes dig → ActHexRegs f0 f' →
      WP bootMainClosure0Code AC Q M' 0xBA4 f') :
    ∀ k, k < 32 → ∀ M f, (∀ x, Sep x 1 H 64 → M x = M0 x) →
      (∀ j, j < 2 * k → (M (H + BitVec.ofNat 32 j)).toNat = (hexBytes dig).getD j 0) →
      f a0 = BitVec.ofNat 32 (32 - k) → f 8 = D + BitVec.ofNat 32 k →
      f a1 = H + BitVec.ofNat 32 (2 * k + 1) → ActHexRegs f0 f →
      WP bootMainClosure0Code AC Q M 0xB7E f := by
  intro k
  induction h : 32 - k generalizing k with
  | zero => intro hk; exfalso; omega
  | succ n ih =>
    intro hk M f hM hJ ha0 hs0 ha1 hR
    have h12' : f a2 = BitVec.ofNat 32 0x3FCC49A0 :=
      (hR a2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
    have hbx : M (D + BitVec.ofNat 32 k) = M0 (D + BitVec.ofNat 32 k) :=
      hM _ fun i hi j hj => by
        have := (sD j hj k (by omega)).symm
        rw [show i = 0 by omega]; simpa using this
    obtain ⟨b, hb⟩ : ∃ b, M (D + BitVec.ofNat 32 k) = b := ⟨_, rfl⟩
    have hbv : b.toNat = dig.getD k 0 := by rw [← hb, hbx]; exact hD k hk
    have hT' : ∀ i, i < 16 → M (BitVec.ofNat 32 0x3FCC49A0 + BitVec.ofNat 32 i) = byteAt acHexDigitsData i :=
      fun i hi => by
        rw [hM _ fun i' hi' j hj => by
          have := (sT j hj i (by omega)).symm
          rw [show i' = 0 by omega]; simpa using this]
        exact hT i hi
    have hb16 : b.toNat / 16 < 16 := by have := b.isLt; omega
    have hb16' : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    refine WP.lbu ac_at_b7e ?_; wn
    refine WP.aluImm ac_at_b82 ?_; wn
    refine WP.aluImm ac_at_b84 ?_; wn
    refine WP.aluImm ac_at_b88 ?_; wn
    refine WP.alu ac_at_b8a ?_; wn
    refine WP.alu ac_at_b8c ?_; wn
    refine WP.lbu ac_at_b8e ?_; wn
    refine WP.lbu ac_at_b92 ?_; wn
    have e0 : f 8 + 0x0 = D + BitVec.ofNat 32 k := by rw [hs0]; exact BitVec.add_zero _
    have eH : ∀ d, d < 16 → BitVec.ofNat 32 d + f a2 + 0x0 = BitVec.ofNat 32 0x3FCC49A0 + BitVec.ofNat 32 d :=
      fun d _ => by rw [h12', act_z0, BitVec.add_comm]
    have v1 : M (BitVec.ofNat 32 (b.toNat / 16) + f a2 + 0x0) = byteAt acHexDigitsData (b.toNat / 16) := by
      rw [eH _ hb16]; exact hT' _ hb16
    have v2 : M (BitVec.ofNat 32 (b.toNat % 16) + f a2 + 0x0) = byteAt acHexDigitsData (b.toNat % 16) := by
      rw [eH _ hb16']; exact hT' _ hb16'
    have a1e : f a1 + 0xFFFFFFFF = H + BitVec.ofNat 32 (2 * k) := by
      have e : BitVec.ofNat 32 (2 * k + 1) + (0xFFFFFFFF : Word) = BitVec.ofNat 32 (2 * k) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
        omega
      rw [ha1, BitVec.add_assoc, e]
    have a1e' : f a1 + 0x0 = H + BitVec.ofNat 32 (2 * k + 1) := by rw [ha1]; exact BitVec.add_zero _
    have sH : ∀ j, j < 64 → Sep (H + BitVec.ofNat 32 j) 1 AC bootMainClosure0Code.length := fun j hj i hi j' hj' => by
      rw [show i = 0 by omega]; simpa using sC j hj j' hj'
    refine WP.sb ac_at_b96 (by act_r; rw [a1e]; exact sH _ (by omega)) ?_; wn
    refine WP.sb ac_at_b9a (by act_r; rw [a1e']; exact sH _ (by omega)) ?_; wn
    refine WP.aluImm ac_at_b9e ?_; wn
    refine WP.aluImm ac_at_ba0 ?_; wn
    rw [e0, hb]
    simp only [act_srl4, act_andF, ev_add]
    rw [v1, v2, a1e, a1e', act_lbu_low, act_lbu_low]
    have hM' : ∀ x, Sep x 1 H 64 → memStore8 (memStore8 M (H + BitVec.ofNat 32 (2 * k))
        (byteAt acHexDigitsData (b.toNat / 16))) (H + BitVec.ofNat 32 (2 * k + 1))
        (byteAt acHexDigitsData (b.toNat % 16)) x = M0 x := fun x hx => by
      rw [memStore8_ne (act_sne hx (by omega)), memStore8_ne (act_sne hx (by omega))]; exact hM x hx
    have hg := act_hex_get dig k (by omega)
    rw [← hbv] at hg
    have hJ' : ∀ j, j < 2 * (k + 1) → (memStore8 (memStore8 M (H + BitVec.ofNat 32 (2 * k))
        (byteAt acHexDigitsData (b.toNat / 16))) (H + BitVec.ofNat 32 (2 * k + 1))
        (byteAt acHexDigitsData (b.toNat % 16)) (H + BitVec.ofNat 32 j)).toNat = (hexBytes dig).getD j 0 := by
      intro j hj
      by_cases e1 : j = 2 * k + 1
      · rw [e1, memStore8_same, act_hd_at _ hb16', hg.2]
      rw [memStore8_ne (act_ofNat_ne (by omega) (by omega) e1)]
      by_cases e2 : j = 2 * k
      · rw [e2, memStore8_same, act_hd_at _ hb16, hg.1]
      rw [memStore8_ne (act_ofNat_ne (by omega) (by omega) e2)]
      exact hJ j (by omega)
    have hR' : ActHexRegs f0 (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd f a3 (b.zeroExtend 32)) 8 (f 8 + 1)) a4
        (BitVec.ofNat 32 (b.toNat / 16))) a3 (BitVec.ofNat 32 (b.toNat % 16))) a4
        (BitVec.ofNat 32 (b.toNat / 16) + f a2)) a3 (BitVec.ofNat 32 (b.toNat % 16) + f a2)) a4
        ((byteAt acHexDigitsData (b.toNat / 16)).zeroExtend 32)) a3
        ((byteAt acHexDigitsData (b.toNat % 16)).zeroExtend 32)) a1 (f a1 + 2)) a0 (f a0 + 0xFFFFFFFF)) := by
      repeat apply act_hr_upd h00
      exact hR
    have hn : f a0 + 0xFFFFFFFF = BitVec.ofNat 32 n := by rw [ha0, act_dec n (by omega)]
    refine WP.branch ac_at_ba2 (fun hb2 => ?_) (fun hb2 => ?_)
    · wn
      have hn0 : n ≠ 0 := by
        revert hb2; act_r; rw [hn]; intro hb2 e; subst e; simp [branchTaken] at hb2
      refine ih (k + 1) (by omega) (by omega) _ _ hM' hJ' (by act_r; exact hn)
        (by act_r; rw [hs0, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc])
        (by act_r; rw [ha1, show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc,
          show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]) hR'
    · wn
      have h0 : n = 0 := by
        revert hb2; act_r; rw [hn]; intro hb2; simp only [branchTaken] at hb2
        have := congrArg BitVec.toNat (bne_eq_false_iff_eq.mp hb2)
        rw [BitVec.toNat_ofNat] at this; simp at this; omega
      refine K _ _ hM' ?_ hR'
      refine List.ext_getElem (by rw [act_hex_len, hdl]; simp [memBytes]) fun j h1 h2 => ?_
      simp only [memBytes, List.getElem_map, List.getElem_range]
      rw [hJ' j (by simp [memBytes] at h1; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
end

/-- `M'` is `M` outside the frame below `sp` and the slots at
`sp + 0x1860`. -/
def ActKeep (B : Word) (M M' : Word → BitVec 8) : Prop :=
  ∀ x, Sep x 1 B 0x3A50 → Sep x 1 (acSlot B 0x1860) 0x6B0 → M' x = M x

theorem ActKeep.trans {B : Word} {M M' M'' : Word → BitVec 8} (h1 : ActKeep B M M') (h2 : ActKeep B M' M'') :
    ActKeep B M M'' := fun x a b => (h2 x a b).trans (h1 x a b)

theorem ActKeep.out {B Bf : Word} {M M' : Word → BitVec 8} (h : ActKeep B M M') :
    ∀ x, ActOut B Bf x → M' x = M x := fun x hx => h x hx.1 hx.2.2.2.2.1

theorem act_ks {B x : Word} (hx : Sep x 1 (acSlot B 0x1860) 0x6B0) (c l : Nat) (h : c + l ≤ 0x6B0) :
    Sep x 1 (B + BitVec.ofNat 32 (0x52B0 + c)) l := by
  have := hx.subR (c := c) (l := l) h
  rwa [add_ofNat_assoc] at this

section
variable {romBase : Word} {romCode : List Nat} {B Bf : Word} {M0 M M' : Word → BitVec 8}

theorem ActX.sB0 (X : ActX romBase romCode B Bf M0) {a n : Nat} (ha : a + n ≤ 0x5A70) (h : 0x3A50 ≤ a) :
    Sep (B + BitVec.ofNat 32 a) n B 0x3A50 := by
  have := X.ss (b := 0) (k := 0x3A50) ha (by decide) (Or.inr h)
  rwa [show B + BitVec.ofNat 32 0 = B from BitVec.add_zero B] at this

theorem ActX.sS (X : ActX romBase romCode B Bf M0) {a n : Nat} (ha : a + n ≤ 0x5A70)
    (h : a + n ≤ 0x52B0 ∨ 0x5960 ≤ a) : Sep (B + BitVec.ofNat 32 a) n (acSlot B 0x1860) 0x6B0 :=
  X.ss ha (by decide) (by omega)

theorem ActKeep.ld (X : ActX romBase romCode B Bf M0) (h : ActKeep B M M') {c : Nat} (h0 : c + 4 ≤ 0x5A70)
    (h1 : 0x3A50 ≤ c) (h2 : c + 4 ≤ 0x52B0 ∨ 0x5960 ≤ c) :
    memLoad32 M' (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    exact h _ (X.sB0 (by omega) (by omega)) (X.sS (by omega) (by omega))

theorem ActKeep.bytes (X : ActX romBase romCode B Bf M0) (h : ActKeep B M M') {c n : Nat} (h0 : c + n ≤ 0x5A70)
    (h1 : 0x3A50 ≤ c) (h2 : c + n ≤ 0x52B0 ∨ 0x5960 ≤ c) :
    memBytes M' (B + BitVec.ofNat 32 c) n = memBytes M (B + BitVec.ofNat 32 c) n :=
  memBytes_congr fun i hi => by
    rw [add_ofNat_assoc]
    exact h _ (X.sB0 (by omega) (by omega)) (X.sS (by omega) (by omega))

theorem ActKeep.bf (X : ActX romBase romCode B Bf M0) (h : ActKeep B M M') {c n : Nat} (h0 : c + n ≤ acBufLen) :
    memBytes M' (Bf + BitVec.ofNat 32 c) n = memBytes M (Bf + BitVec.ofNat 32 c) n :=
  memBytes_congr fun i hi => by
    rw [add_ofNat_assoc]
    have s1 := (X.sbf (a := 0) (n := 0x3A50) (by decide) (c := c + i) (k := 1) (by omega)).symm
    rw [show B + BitVec.ofNat 32 0 = B from BitVec.add_zero B] at s1
    exact h _ s1 (X.sbf (a := 0x52B0) (n := 0x6B0) (by decide) (c := c + i) (k := 1) (by omega)).symm

end

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {M : Word → BitVec 8} {f : Fin 32 → Word}

/-- **The digest of `trusted_root.json`**, from 0xB28. `tufReadDoc`'s
result is at `sp + 0x1870`: an error byte, or the trusted root at
`Bf + 0x4000`. -/
theorem act_hex (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {hiW loW : Word} {val : Nat} {body : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (h18 : memLoad32 M (acSlot B 0x18) = hiW) (h14 : memLoad32 M (acSlot B 0x14) = loW)
    (hval : hiW.toNat * 2 ^ 32 + loW.toNat = val)
    (hres : (memLoad32 M (acSlot B 0x1870) = 0 ∧ (M (acSlot B 0x1874)).toNat < 0x27) ∨
      (memLoad32 M (acSlot B 0x1870) = Bf + 0x4000 ∧
        memLoad32 M (acSlot B 0x1874) = BitVec.ofNat 32 parts.trustedRoot.length ∧
        parts.trustedRoot.length ≤ 0x2800 ∧
        memBytes M (Bf + 0x4000) parts.trustedRoot.length = parts.trustedRoot))
    (hbody : f 9 = 0 → memBytes M (acSlot B 0x351) 64 = body)
    (hspec : val = parts.trustedRoot.length → body = hexBytes (sha256 parts.trustedRoot) →
      verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs6 : f 22 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0xB28 f := by
  have F := X.F
  refine WP.zero fun hz => ?_
  have e560 : f 22 + 0x560 = acSlot B 0x1870 := by rw [hs6]; exact add_ofNat_assoc B _ _
  have e564 : f 22 + 0x564 = acSlot B 0x1874 := by rw [hs6]; exact add_ofNat_assoc B _ _
  refine WP.lw ac_at_b28 (by rw [e560]; exact X.al (by decide) (by decide)) ?_; wn
  rw [e560]
  rcases hres with ⟨h0, he⟩ | ⟨hp, hl, hlen, hdoc⟩
  · rw [h0]
    refine WP.branch ac_at_b2c (fun _ => ?_) (fun hb => ?_)
    · wn; exact act_c0a (hI.put (by decide) _) hr (by act_r; rw [e564]; exact he)
    · exfalso; revert hb; act_r
  have hne : Bf + 0x4000 ≠ 0 := fun e => by
    have h1 : (Bf + BitVec.ofNat 32 0x4000).toNat = Bf.toNat + 0x4000 := X.bfLo (by decide)
    have := congrArg BitVec.toNat e
    rw [show (Bf + 0x4000 : Word) = Bf + BitVec.ofNat 32 0x4000 from rfl, h1] at this
    simp at this
  rw [hp]
  refine WP.branch ac_at_b2c (fun hb => ?_) (fun _ => ?_)
  · exfalso; revert hb; act_r; intro hb; simp only [branchTaken] at hb; exact hne (beq_iff_eq.mp hb)
  wn
  refine WP.lw ac_at_b30 (by act_r; rw [e564]; exact X.al (by decide) (by decide)) ?_; wn
  rw [e564, hl]
  refine WP.lui ac_at_b34 ?_; wn
  refine WP.aluImm ac_at_b36 ?_; wn
  refine WP.alu ac_at_b3a ?_; wn
  refine WP.alu ac_at_b3c ?_; wn
  refine WP.alu ac_at_b3e ?_; wn
  refine WP.lui ac_at_b40 ?_; wn
  refine WP.aluImm ac_at_b42 ?_; wn
  refine WP.alu ac_at_b46 ?_; wn
  have hbl : acBufLen = 0xB954 := rfl
  have hbfl : (Bf + BitVec.ofNat 32 0x4000).toNat = Bf.toNat + 0x4000 := X.bfLo (by decide)
  have := X.bhi
  refine act_sha (c := 0x5818) (p := Bf + 0x4000) (n := parts.trustedRoot.length) X
    (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_b4a ac_at_b4e (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl) (by act_r) (by act_r) (by decide) (by omega)
    (by rw [show (Bf + 0x4000 : Word) = Bf + BitVec.ofNat 32 0x4000 from rfl, hbfl]; omega)
    (X.sbf (a := 0x37E0) (n := 0x270) (by decide) (c := 0x4000) (k := parts.trustedRoot.length) (by omega)).symm
    fun m1 hsh hf1 => ?_
  rw [hdoc] at hsh
  have k1 : ActKeep B M m1.mem := fun x a b => hf1 x (a.subR (c := 0x37E0) (l := 0x270) (by decide))
    (act_ks b 0x568 32 (by decide))
  have hI1 := hI.mem F X.sB k1.out
  wn
  refine WP.lui ac_at_b52 ?_; wn
  refine WP.aluImm ac_at_b54 ?_; wn
  refine WP.alu ac_at_b58 ?_; wn
  refine WP.aluImm ac_at_b5a ?_; wn
  refine WP.aluImm ac_at_b5e ?_; wn
  refine act_ms (dst := B + BitVec.ofNat 32 0x52C0) (n := 64) X (hI1.regs (by act_r) (by act_r) (by act_r))
    ac_at_b60 ac_at_b64 (by decide) (by decide) (by act_r; rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl)
    (by act_r) (by act_r) (X.low (by decide)) fun m2 hm2 => ?_
  have k2 : ActKeep B m1.mem m2.mem := fun x _ b => by
    rw [hm2]; exact fillBytes_sep (act_ks b 0x10 64 (by decide)).symm (Nat.le_refl _)
  have hI2 := hI1.mem F X.sB k2.out
  wn
  refine WP.aluImm ac_at_b68 ?_; wn
  refine WP.lui ac_at_b6c ?_; wn
  refine WP.aluImm ac_at_b6e ?_; wn
  refine WP.alu ac_at_b72 ?_; wn
  refine WP.lui ac_at_b74 ?_; wn
  refine WP.aluImm ac_at_b78 ?_; wn
  refine WP.branch ac_at_b7c (fun hb => ?_) (fun _ => ?_)
  · exfalso; revert hb; act_r
  wn
  have sHD : Sep (B + BitVec.ofNat 32 0x52C0) 64 (B + BitVec.ofNat 32 0x5818) 32 :=
    X.ss (by decide) (by decide) (Or.inl (by decide))
  have sHT : Sep (B + BitVec.ofNat 32 0x52C0) 64 (BitVec.ofNat 32 0x3FCC49A0) 16 :=
    (X.sro (a := 0x52C0) (n := 64) (by decide)).subR (c := 0x9A0) (l := 16) (by decide)
  refine act_hex_loop (D := B + BitVec.ofNat 32 0x5818) (H := B + BitVec.ofNat 32 0x52C0)
    (dig := sha256 parts.trustedRoot) (M0 := m2.mem) (C3.RV32.Sv.sha256_length _)
    (fun i hi => by
      rw [← hsh, memBytes_getD hi, hm2, fillBytes_sep (sHD.subR (c := i) (l := 1) (by omega)) (Nat.le_refl _)])
    (fun i hi => (X.E hI2).hex i (by decide +revert)) sHD sHT
    (X.sc (by decide) (by decide) (by decide)) (by act_r) (by act_r) ?_ 0 (by decide) _ _
    (fun _ _ => rfl) (fun j hj => absurd hj (by omega)) (by act_r)
    (by act_r; rw [act_spc hI.rsp _ 0x5818 rfl, BitVec.add_zero])
    (by act_r; rw [BitVec.add_comm _ (f sp), act_spc hI.rsp _ 0x52C1 rfl, add_ofNat_assoc]) (fun _ _ _ _ _ _ => rfl)
  intro M3 f3 hM3 hhx hR
  have k3 : ActKeep B m2.mem M3 := fun x _ b => hM3 x (act_ks b 0x10 64 (by decide))
  have hsp3 : f3 sp = f sp := by rw [hR sp (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r
  have hgp3 : f3 3 = f 3 := by rw [hR 3 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r
  have htp3 : f3 4 = f 4 := by rw [hR 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r
  have hI3 := (hI2.mem F X.sB k3.out).regs hsp3 hgp3 htp3
  refine WP.lui ac_at_ba4 ?_; wn
  refine WP.aluImm ac_at_ba6 ?_; wn
  refine WP.alu ac_at_baa ?_; wn
  refine WP.lui ac_at_bac ?_; wn
  refine WP.aluImm ac_at_bae ?_; wn
  refine WP.alu ac_at_bb2 ?_; wn
  refine WP.aluImm ac_at_bb4 ?_; wn
  refine act_mc (dst := B + BitVec.ofNat 32 0x5920) (src := B + BitVec.ofNat 32 0x52C0) (N := 64) X
    (hI3.regs (by act_r) (by act_r) (by act_r)) ac_at_bb8 ac_at_bbc (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm _ (f3 sp), act_spc hI3.rsp _ 0x5920 rfl])
    (by act_r; rw [BitVec.add_comm _ (f3 sp), act_spc hI3.rsp _ 0x52C0 rfl]) (by act_r)
    (X.low (by decide)) (X.low (by decide))
    (X.ss (by decide) (by decide) (Or.inr (by decide))) (X.ss (by decide) (by decide) (Or.inr (by decide)))
    (X.ss (by decide) (by decide) (Or.inr (by decide))) fun m4 hO4 => ?_
  have k4 : ActKeep B M3 m4.mem := fun x a b => by
    rw [hO4 x (a.subR (c := 0x3A40) (l := 16) (by decide))]
    exact copyBytes_sep (act_ks b 0x670 64 (by decide)).symm (Nat.le_refl _)
  have kA : ActKeep B M m4.mem := k1.trans (k2.trans (k3.trans k4))
  wn
  have hbl : acBufLen = 0xB954 := rfl
  refine act_tail X ((hI.mem F X.sB kA.out).regs (by act_r; exact hsp3) (by act_r; exact hgp3) (by act_r; exact htp3))
    ((kA.ld X (c := 0x3A50 + 0x40) (by decide) (by decide) (by decide)).trans hr)
    (fun x hx => (kA.out x hx).trans (hO x hx))
    ((kA.ld X (c := 0x3A50 + 0x18) (by decide) (by decide) (by decide)).trans h18)
    ((kA.ld X (c := 0x3A50 + 0x14) (by decide) (by decide) (by decide)).trans h14) hval
    (by act_r; rw [hR 24 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r) hlen
    ((kA.bf X (c := 0x4000) (n := parts.trustedRoot.length) (by omega)).trans hdoc) ?_
    (fun h9 => (kA.bytes X (c := 0x3A50 + 0x351) (n := 64) (by decide) (by decide) (by decide)).trans
      (hbody (by revert h9; act_r; rw [hR 9 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r; exact id))) hspec
    ((kA.ld X (c := 0x3A50 + 0x20) (by decide) (by decide) (by decide)).trans h20)
    ((kA.ld X (c := 0x3A50 + 0x24) (by decide) (by decide) (by decide)).trans h24)
    ((kA.ld X (c := 0x3A50 + 0x28) (by decide) (by decide) (by decide)).trans h28)
    ((kA.ld X (c := 0x3A50 + 0x2C) (by decide) (by decide) (by decide)).trans h2C)
    (by act_r; rw [hR 18 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r) (by act_r; rw [hR 19 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r; exact hs3) (by act_r; rw [hR 22 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r; exact hs6)
    (by act_r; rw [hR 21 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r; exact hs5) (by act_r; rw [hR 25 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r; exact hs9) (by act_r; rw [hR 27 (by decide) (by decide) (by decide) (by decide) (by decide)]; act_r; exact hs11)
  rw [← hhx]
  refine memBytes_ext fun i hi => ?_
  show m4.mem (B + BitVec.ofNat 32 0x5920 + BitVec.ofNat 32 i) = _
  have hs : Sep (B + BitVec.ofNat 32 0x5920 + BitVec.ofNat 32 i) 1 (B + BitVec.ofNat 32 0x3A40) 16 := by
    rw [add_ofNat_assoc]; exact X.ss (by omega) (by decide) (Or.inr (by omega))
  rw [hO4 _ hs, copyBytes_at hi (by decide)]

end

end C3.RV32.Ac
