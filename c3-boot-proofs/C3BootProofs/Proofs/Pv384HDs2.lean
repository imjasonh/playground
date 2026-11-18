import C3BootProofs.Proofs.Pv384HDs

/-!
# `p384_verify_prehash`: one constant-time divstep

One pass of the constant-time divstep loop at 0xD36, to its branch at
0xEFE, against `dsStep`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

theorem pvR_st32 {B x c v : Word} {M : Word → BitVec 8} (hx : PvR B x) (hc : c.toNat + 4 ≤ 0x1D4C) :
    memStore32 M (B + 0x420 + c) v x = M x := by
  have := pvR_hi (c := c.toNat) (l := 4) hx hc
  rw [ofNat_toNat_self] at this
  exact memStore32_get_sep this

theorem pvR_st8 {B x c : Word} {v : BitVec 8} {M : Word → BitVec 8} (hx : PvR B x) (hc : c.toNat + 1 ≤ 0x1D4C) :
    memStore8 M (B + 0x420 + c) v x = M x := by
  have := pvR_hi (c := c.toNat) (l := 1) hx hc
  rw [ofNat_toNat_self] at this
  exact memStore8_ne (sep1_ne this)

theorem fk_st32 {B c v : Word} {M : Word → BitVec 8} {e : Nat} (hS : (B + 0x420).toNat + 0x1D80 ≤ 2 ^ 32)
    (hc : c.toNat + 4 ≤ 0x1D80) (he : e + 1 ≤ 0x1D80) (h : c.toNat + 4 ≤ e ∨ e + 1 ≤ c.toNat) :
    memStore32 M (B + 0x420 + c) v (B + 0x420 + BitVec.ofNat 32 e) = M (B + 0x420 + BitVec.ofNat 32 e) :=
  memStore32_get_sep (fr_sep hS (by decide) (by decide) hc (by rw [BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h))

theorem fk_st8 {B c : Word} {v : BitVec 8} {M : Word → BitVec 8} {e : Nat} (hS : (B + 0x420).toNat + 0x1D80 ≤ 2 ^ 32)
    (hc : c.toNat + 1 ≤ 0x1D80) (he : e + 1 ≤ 0x1D80) (h : c.toNat + 1 ≤ e ∨ e + 1 ≤ c.toNat) :
    memStore8 M (B + 0x420 + c) v (B + 0x420 + BitVec.ofNat 32 e) = M (B + 0x420 + BitVec.ofNat 32 e) :=
  memStore8_ne (sep1_ne (fr_sep hS (by decide) (by decide) hc (by rw [BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h)))

theorem st32_get {M : Word → BitVec 8} {S a b v : Word} (hS : S.toNat + 0x1D80 ≤ 2 ^ 32)
    (ha : a.toNat + 4 ≤ 0x1D80) (hb : b.toNat + 1 ≤ 0x1D80) (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 1 ≤ a.toNat) :
    memStore32 M (S + a) v (S + b) = M (S + b) :=
  memStore32_get_sep (fr_sep hS (by decide) (by decide) ha hb h)

theorem add_d80 (S : Word) : S + 0xD80 + 0x514 = S + 0x1294 := by rw [BitVec.add_assoc]; rfl

theorem gb01 (g : Word) : g &&& 1 = 0 ∨ g &&& 1 = 1 := by
  have h : (g &&& 1).toNat < 2 := by rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rcases (by omega : (g &&& 1).toNat = 0 ∨ (g &&& 1).toNat = 1) with h | h
  · exact .inl (BitVec.eq_of_toNat_eq h)
  · exact .inr (BitVec.eq_of_toNat_eq h)

theorem zext_trunc01 {g : Word} (h : g = 0 ∨ g = 1) : (g.extractLsb' 0 8).zeroExtend 32 = g := by
  rcases h with rfl | rfl <;> rfl

theorem c1_01 (dl dh : Word) :
    ((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F = 0 ∨
    ((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F = 1 := by
  rw [ct_c1]; split
  · exact .inr rfl
  · exact .inl rfl

theorem and01w {a b : Word} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a &&& b = 0 ∨ a &&& b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem fr_al {B c : Word} (FS : Fr (B + 0x420) 0x1D80) (hc : c.toNat % 4 = 0) (hc' : c.toNat < 0x1D80) :
    (B + 0x420 + c).toNat % 4 = 0 := by
  have := FS.al; have := FS.hi; rw [BitVec.toNat_add]; omega

theorem fr_code {B c : Word} (FS : Fr (B + 0x420) 0x1D80) {n : Nat} (hc : c.toNat + n ≤ 0x1D80) :
    Sep (B + 0x420 + c) n PV p384VerifyPrehashCode.length := by
  have := FS.hi
  have e : (B + 0x420 + c).toNat = (B + 0x420).toNat + c.toNat := by rw [BitVec.toNat_add]; omega
  exact sep_of_le (by rw [e, show PV.toNat = p384VerifyPrehashAddress from rfl]; unfold p384VerifyPrehashAddress; omega)
    (by rw [show PV.toNat = p384VerifyPrehashAddress from rfl]; decide)

/-- The block side conditions: aligned stores to the frame, apart from the code. -/
macro "ct_ok" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first
    | exact fr_al (by assumption) (by decide) (by decide)
    | exact fr_code (by assumption) (by decide)))

theorem mask01 {g : Word} (h : g = 0 ∨ g = 1) : (0 : Word) - g = if g = 1 then 0xFFFFFFFF else 0 := by
  rcases h with rfl | rfl <;> rfl

theorem mask01' {g : Word} (h : g = 0 ∨ g = 1) :
    (if g.ult 1 then (1 : Word) else 0) + 0xFFFFFFFF = if g = 1 then 0xFFFFFFFF else 0 := by
  rcases h with rfl | rfl <;> rfl

theorem and_mask (x : Word) (c : Prop) [Decidable c] :
    x &&& (if c then 0xFFFFFFFF else 0) = if c then x else 0 := by
  split
  · exact BitVec.and_allOnes
  · exact BitVec.and_zero

theorem w64_mask (x xh : Word) (c : Prop) [Decidable c] :
    W64 (x &&& (if c then 0xFFFFFFFF else 0)) (xh &&& (if c then 0xFFFFFFFF else 0)) = if c then W64 x xh else 0 := by
  rw [and_mask, and_mask]; split <;> rfl

theorem w64_sel {c : Word} (hc : c = 0 ∨ c = 1) (a1 a2 a3 a4 : Word) :
    W64 (if c = 1 then a3 else a1) (if c = 1 then a4 else a2) = if c = 1 then W64 a3 a4 else W64 a1 a2 := by
  split <;> rfl

theorem gb_one {g : Word} : (g &&& 1 = 1) ↔ g.toNat % 2 = 1 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod] at this; exact this
  · intro h; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod]; exact h

theorem kld {B c : Word} {M M' : Word → BitVec 8} (K : PvKeep B M M' 0 0) (hc : c.toNat + 4 ≤ 0x1D4C) :
    memLoad32 M' (B + 0x420 + c) = memLoad32 M (B + 0x420 + c) := by
  rw [← ofNat_toNat_self c]
  exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact K _ (by omega) (by omega)

theorem kfk {B : Word} {M M' : Word → BitVec 8} (K : PvKeep B M M' 0 0) {e : Nat} (he : e + 1 ≤ 0x1D4C) :
    M' (B + 0x420 + BitVec.ofNat 32 e) = M (B + 0x420 + BitVec.ofNat 32 e) := K e he (by omega)

/-- The constant-time divstep's choice: `g` odd and `δ > 0`. -/
abbrev ctC3 (gl dl dh : Word) : Word := (gl &&& 1) &&& (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F)

/-- The constant-time divstep's other choice: `δ > 0`. -/
abbrev ctC1 (dl dh : Word) : Word := (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F)

/-- The `f` the constant-time divstep adds to `g` when `g` is odd. -/
abbrev ctMk (gl : Word) : Word := if gl &&& 1 = 1 then 0xFFFFFFFF else 0

set_option maxHeartbeats 64000000 in
/-- The first half of a constant-time divstep, from 0xD36 to the fifth
select at 0xE36: the new `δ`, `f`, `g`, and `u` stored, and the candidates
for `v` in the argument registers. -/
theorem ct_partA {B : Word} {m : Machine} {n : Nat} {dl dh fl fh gl gh ul uh vl vh ql qh rl rh : Word}
    (F : Fr B 0x21A0) (E : PvEnv3 m.mem)
    (st : St m.mem PV m 0xD36 (reg m)) (hsp : reg m sp = B + 0x420) (h8 : reg m (8 : Fin 32) = B + 0x420 + 0xD80)
    (hcnt : reg m a4 = BitVec.ofNat 32 (n + 1))
    (hdl : memLoad32 m.mem (B + 0x420 + 0x40) = dl) (hfl : memLoad32 m.mem (B + 0x420 + 0x50) = fl)
    (hfh : memLoad32 m.mem (B + 0x420 + 0x48) = fh) (hgl : memLoad32 m.mem (B + 0x420 + 0x44) = gl)
    (hgh : memLoad32 m.mem (B + 0x420 + 0x4C) = gh) (hql : memLoad32 m.mem (B + 0x420 + 0x54) = ql)
    (hdh : reg m (24 : Fin 32) = dh) (hul : reg m (23 : Fin 32) = ul) (huh : reg m (26 : Fin 32) = uh)
    (hvl : reg m (20 : Fin 32) = vl) (hvh : reg m (25 : Fin 32) = vh) (hqh : reg m (18 : Fin 32) = qh)
    (hrl : reg m (22 : Fin 32) = rl) (hrh : reg m (13 : Fin 32) = rh) :
    ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      (∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
        m'.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e)) ∧
      St m'.mem PV m' 0xE36 (reg m') ∧ reg m' sp = B + 0x420 ∧
      reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      reg m' a0 = ctC3 gl dl dh ∧ reg m' a1 = vl ∧ reg m' a2 = vh ∧ reg m' a3 = rl ∧ reg m' a4 = rh ∧
      reg m' (8 : Fin 32) = vh ∧ reg m' (18 : Fin 32) = ql ∧ reg m' (19 : Fin 32) = vl ∧
      reg m' (21 : Fin 32) = rh ∧ reg m' (22 : Fin 32) = rl ∧ reg m' (23 : Fin 32) = ul ∧
      reg m' (25 : Fin 32) = qh ∧ reg m' (26 : Fin 32) = uh ∧ reg m' (27 : Fin 32) = gl &&& 1 ∧
      memLoad32 m'.mem (B + 0x420 + 0x3C) = BitVec.ofNat 32 (n + 1) ∧
      memLoad32 m'.mem (B + 0x420 + 0x24) = ctC1 dl dh ∧
      W64 (memLoad32 m'.mem (B + 0x420 + 0x40)) (memLoad32 m'.mem (B + 0x420 + 0x38)) =
        (if ctC3 gl dl dh = 1 then (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64 else (W64 dl dh + 2) % 2 ^ 64) ∧
      W64 (memLoad32 m'.mem (B + 0x420 + 0x50)) (memLoad32 m'.mem (B + 0x420 + 0x48)) =
        (if ctC3 gl dl dh = 1 then W64 gl gh else W64 fl fh) ∧
      W64 (memLoad32 m'.mem (B + 0x420 + 0x44)) (memLoad32 m'.mem (B + 0x420 + 0x4C)) =
        asr64 (if ctC3 gl dl dh = 1 then (W64 gl gh + 2 ^ 64 - W64 (fl &&& ctMk gl) (fh &&& ctMk gl)) % 2 ^ 64
          else (W64 (fl &&& ctMk gl) (fh &&& ctMk gl) + W64 gl gh) % 2 ^ 64) ∧
      W64 (memLoad32 m'.mem (B + 0x420 + 0x2C)) (memLoad32 m'.mem (B + 0x420 + 0x34)) =
        2 * (if ctC3 gl dl dh = 1 then W64 ql qh else W64 ul uh) % 2 ^ 64 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hS : (B + 0x420).toNat + 0x1D80 ≤ 2 ^ 32 := by have := FS.hi; omega
  have gb01' := gb01 gl
  have c101 := c1_01 dl dh
  have c301 := and01w gb01' c101
  have hz := st.zero
  -- segment 1, to the first select at 0xDAA
  obtain ⟨n1, c1, u1⟩ := st.block ctS1 E.E.C.self ctS1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS1, upd, ↓reduceIte, hsp, h8, add_d80, and_true, true_and]
    ct_ok)
  have s1 : St n1.mem PV n1 0xDAA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = (runBlock ctS1 (m.mem, reg m)).1 := u1.mem
  have b1 : ∀ q : Fin 32, reg n1 q = (runBlock ctS1 (m.mem, reg m)).2 q := u1.regs
  have r27 : reg n1 (27 : Fin 32) = gl &&& 1 := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, hgl]
  have r21 : reg n1 (21 : Fin 32) = gl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, hgl]
  have r19 : reg n1 (19 : Fin 32) = vl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, hvl, hz]
    exact BitVec.zero_add _
  have r18 : reg n1 (18 : Fin 32) = rl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, hrl, hz]
    exact BitVec.zero_add _
  have r22 : reg n1 (22 : Fin 32) = fh := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfh
  have r20 : reg n1 (20 : Fin 32) = fl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfl
  have r23 : reg n1 (23 : Fin 32) = ul := by
    rw [b1, runBlock_reg _ _ _ _ hz (by decide), hul]
  have r26 : reg n1 (26 : Fin 32) = uh := by
    rw [b1, runBlock_reg _ _ _ _ hz (by decide), huh]
  have r24 : reg n1 (24 : Fin 32) = (gl &&& (1 : Word)) &&& (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) -
      (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]
    rw [hgl, hdl, hdh]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have r10 : reg n1 a0 = reg n1 (24 : Fin 32) := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hz]
    exact BitVec.zero_add _
  have q11 : W64 (reg n1 a1) (reg n1 a2) = (W64 dl dh + 2) % 2 ^ 64 := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]
    rw [hdl, hdh]; exact w64_add2 _ _
  have q13 : W64 (reg n1 a3) (reg n1 a4) = (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64 := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]
    rw [hdl, hdh]; exact w64_2sub _ _
  have r8 : reg n1 (8 : Fin 32) = fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, st32_get hS, memStore8_same]
    rw [hfl, hgl, zext_trunc01 (gb01 gl), mask01 (gb01 gl)]
  have r25 : reg n1 (25 : Fin 32) = fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, st32_get hS, memStore8_same]
    rw [hfh, hgl, zext_trunc01 (gb01 gl), mask01' (gb01 gl)]
  have w30 : memLoad32 n1.mem (B + 0x420 + 0x30) = vh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hvh
  have w28 : memLoad32 n1.mem (B + 0x420 + 0x28) = rh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hrh
  have w3c : memLoad32 n1.mem (B + 0x420 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hcnt
  have w1c : memLoad32 n1.mem (B + 0x420 + 0x1C) = qh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hqh
  have w24 : memLoad32 n1.mem (B + 0x420 + 0x24) = ((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) -
      (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]
    rw [hdl, hdh]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have w40 : memLoad32 n1.mem (B + 0x420 + 0x40) = dl := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hdl
  have w44 : memLoad32 n1.mem (B + 0x420 + 0x44) = gl := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hgl
  have w48 : memLoad32 n1.mem (B + 0x420 + 0x48) = fh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfh
  have w4c : memLoad32 n1.mem (B + 0x420 + 0x4C) = gh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hgh
  have w50 : memLoad32 n1.mem (B + 0x420 + 0x50) = fl := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfl
  have w54 : memLoad32 n1.mem (B + 0x420 + 0x54) = ql := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hql
  have fr1 : ∀ x, PvR B x → n1.mem x = m.mem x := fun x hx => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := decide) only [pvR_st32 hx, pvR_st8 hx]
  have fk1 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n1.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctS1, upd, ↓reduceIte, aluEval, hsp, h8, add_d80, hz]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st32 hS, fk_st8 hS]
  -- the first select: `δ`
  have E1 : PvEnv3 n1.mem := E.fr F fr1
  have sp1 : reg n1 sp = B + 0x420 := by rw [b1, runBlock_reg _ _ _ _ hz (by decide), hsp]
  have c3 : reg n1 a0 = 0 ∨ reg n1 a0 = 1 := by rw [r10, r24]; exact c301
  obtain ⟨n2, P2, K2, k2, v20, v21⟩ := pv_si F E1 s1 pv_at_daa pv_at_dae (by decide) (by decide) sp1 c3
  have q2 : W64 (reg n2 a0) (reg n2 a1) = if reg n1 a0 = 1 then (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64
      else (W64 dl dh + 2) % 2 ^ 64 := by
    rw [v20, v21, w64_sel c3, q11, q13]
  have E2 : PvEnv3 n2.mem := E1.fr F P2.fr
  have r2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n1 q := P2.regs
  -- segment 2, to the second select at 0xDC4: store `δ`, select `f`
  have sp2 : reg n2 sp = B + 0x420 := by rw [r2 _ (by decide), sp1]
  obtain ⟨n3, c3', u3⟩ := P2.st.block ctS2 E2.E.C.self ctS2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS2, upd, ↓reduceIte, sp2, and_true, true_and]; ct_ok)
  have m3 : n3.mem = (runBlock ctS2 (n2.mem, reg n2)).1 := u3.mem
  have b3 : ∀ q : Fin 32, reg n3 q = (runBlock ctS2 (n2.mem, reg n2)).2 q := u3.regs
  have s3 : St n3.mem PV n3 0xDC4 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have z2 := P2.st.zero
  have w40_3 : memLoad32 n3.mem (B + 0x420 + 0x40) = reg n2 a0 := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have w38_3 : memLoad32 n3.mem (B + 0x420 + 0x38) = reg n2 a1 := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have w30_3 : memLoad32 n3.mem (B + 0x420 + 0x30) = vh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w30
  have w28_3 : memLoad32 n3.mem (B + 0x420 + 0x28) = rh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w28
  have w3c_3 : memLoad32 n3.mem (B + 0x420 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w3c
  have w1c_3 : memLoad32 n3.mem (B + 0x420 + 0x1C) = qh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w1c
  have w24_3 : memLoad32 n3.mem (B + 0x420 + 0x24) = ((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w24
  have w44_3 : memLoad32 n3.mem (B + 0x420 + 0x44) = gl := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w44
  have w48_3 : memLoad32 n3.mem (B + 0x420 + 0x48) = fh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w48
  have w4c_3 : memLoad32 n3.mem (B + 0x420 + 0x4C) = gh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w4c
  have w50_3 : memLoad32 n3.mem (B + 0x420 + 0x50) = fl := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w50
  have w54_3 : memLoad32 n3.mem (B + 0x420 + 0x54) = ql := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K2 (by decide)]; exact w54
  have fr3 : ∀ x, PvR B x → n3.mem x = m.mem x := fun x hx => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [pvR_st32 hx]; rw [P2.fr x hx, fr1 x hx]
  have fk3 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n3.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st32 hS]
    rw [kfk K2 he, fk1 e he h1 h2]
  have r3_10 : reg n3 a0 = reg n1 a0 := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), ← r10]; exact BitVec.zero_add _
  have r3_11 : reg n3 a1 = fl := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r20]; exact BitVec.zero_add _
  have r3_12 : reg n3 a2 = fh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r22]; exact BitVec.zero_add _
  have r3_13 : reg n3 a3 = gl := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r21]; exact BitVec.zero_add _
  have r3_14 : reg n3 a4 = gh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, z2, sp2]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K2 (by decide), w4c]; exact BitVec.zero_add _
  have r3_22 : reg n3 (22 : Fin 32) = rl := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r18]; exact BitVec.zero_add _
  -- the second select: `f`
  have E3 : PvEnv3 n3.mem := E.fr F fr3
  have sp3 : reg n3 sp = B + 0x420 := by rw [b3, runBlock_reg _ _ _ _ z2 (by decide), sp2]
  obtain ⟨n4, P4, K4, k4, v40, v41⟩ := pv_si F E3 s3 pv_at_dc4 pv_at_dc8 (by decide) (by decide) sp3
    (by rw [r3_10]; exact c3)
  have q4 : W64 (reg n4 a0) (reg n4 a1) = if reg n1 a0 = 1 then W64 gl gh else W64 fl fh := by
    rw [v40, v41, r3_10, w64_sel c3, r3_13, r3_14, r3_11, r3_12]
  have E4 : PvEnv3 n4.mem := E3.fr F P4.fr
  have r4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n3 q := P4.regs
  have r3k : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 19, 20, 21, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q := fun q hq => by
    rw [b3, runBlock_reg _ _ _ _ z2 (by revert hq; revert q; decide)]
  have r3_9 : reg n3 (9 : Fin 32) = gh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctS2, upd, ↓reduceIte, aluEval, z2, sp2]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K2 (by decide), w4c]
  -- segment 3, to the third select at 0xDEE: store `f`, and both candidates for `g`
  have sp4 : reg n4 sp = B + 0x420 := by rw [r4 _ (by decide), sp3]
  have z4 := P4.st.zero
  have mk := gb01 gl
  obtain ⟨n5, c5, u5⟩ := P4.st.block ctS3 E4.E.C.self ctS3_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS3, upd, ↓reduceIte, sp4, and_true, true_and]; ct_ok)
  have m5 : n5.mem = (runBlock ctS3 (n4.mem, reg n4)).1 := u5.mem
  have b5 : ∀ q : Fin 32, reg n5 q = (runBlock ctS3 (n4.mem, reg n4)).2 q := u5.regs
  have s5 : St n5.mem PV n5 0xDEE (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have e4_8 : reg n4 (8 : Fin 32) = fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r8]
  have e4_25 : reg n4 (25 : Fin 32) = fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r25]
  have e4_21 : reg n4 (21 : Fin 32) = gl := by rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r21]
  have e4_20 : reg n4 (20 : Fin 32) = fl := by rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r20]
  have e4_9 : reg n4 (9 : Fin 32) = gh := by rw [r4 _ (by decide), r3_9]
  have e4_24 : reg n4 (24 : Fin 32) = reg n1 a0 := by rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r10]
  have w50_5 : memLoad32 n5.mem (B + 0x420 + 0x50) = reg n4 a0 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have w48_5 : memLoad32 n5.mem (B + 0x420 + 0x48) = reg n4 a1 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have q5a : W64 (reg n5 a1) (reg n5 a2) = (W64 (fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0))
      (fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0)) + W64 gl gh) % 2 ^ 64 := by
    rw [b5, b5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval]
    rw [e4_8, e4_21, e4_25, e4_9]; exact w64_add _ _ _ _
  have q5b : W64 (reg n5 a3) (reg n5 a4) = (W64 gl gh + 2 ^ 64 - W64 (fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0))
      (fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0))) % 2 ^ 64 := by
    rw [b5, b5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval]
    rw [e4_8, e4_21, e4_25, e4_9]; exact w64_sub _ _ _ _
  have r5_10 : reg n5 a0 = reg n1 a0 := by
    rw [b5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, z4]
    rw [e4_24]; exact BitVec.zero_add _
  have r5k : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n4 q := fun q hq => by
    rw [b5, runBlock_reg _ _ _ _ z4 (by revert hq; revert q; decide)]
  have w40_5 : memLoad32 n5.mem (B + 0x420 + 0x40) = reg n2 a0 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w40_3
  have w38_5 : memLoad32 n5.mem (B + 0x420 + 0x38) = reg n2 a1 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w38_3
  have w30_5 : memLoad32 n5.mem (B + 0x420 + 0x30) = vh := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w30_3
  have w28_5 : memLoad32 n5.mem (B + 0x420 + 0x28) = rh := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w28_3
  have w3c_5 : memLoad32 n5.mem (B + 0x420 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w3c_3
  have w1c_5 : memLoad32 n5.mem (B + 0x420 + 0x1C) = qh := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w1c_3
  have w24_5 : memLoad32 n5.mem (B + 0x420 + 0x24) = (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w24_3
  have w54_5 : memLoad32 n5.mem (B + 0x420 + 0x54) = ql := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K4 (by decide)]; exact w54_3
  have fr5 : ∀ x, PvR B x → n5.mem x = m.mem x := fun x hx => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [pvR_st32 hx, pvR_st8 hx]; rw [P4.fr x hx, fr3 x hx]
  have fk5 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n5.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctS3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st32 hS, fk_st8 hS]
    rw [kfk K4 he, fk3 e he h1 h2]
  -- the third select: `g` before the shift
  have E5 : PvEnv3 n5.mem := E.fr F fr5
  have sp5 : reg n5 sp = B + 0x420 := by rw [b5, runBlock_reg _ _ _ _ z4 (by decide), sp4]
  obtain ⟨n6, P6, K6, k6, v60, v61⟩ := pv_si F E5 s5 pv_at_dee pv_at_df2 (by decide) (by decide) sp5
    (by rw [r5_10]; exact c3)
  have q6 : W64 (reg n6 a0) (reg n6 a1) = if reg n1 a0 = 1 then W64 (reg n5 a3) (reg n5 a4) else W64 (reg n5 a1) (reg n5 a2) := by
    rw [v60, v61, r5_10, w64_sel c3]
  have E6 : PvEnv3 n6.mem := E5.fr F P6.fr
  have r6 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n5 q := P6.regs
  -- segment 4, to the fourth select at 0xE12: store `g`, select `u` or `q`
  have sp6 : reg n6 sp = B + 0x420 := by rw [r6 _ (by decide), sp5]
  have z6 := P6.st.zero
  obtain ⟨n7, c7, u7⟩ := P6.st.block ctS4 E6.E.C.self ctS4_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS4, upd, ↓reduceIte, sp6, and_true, true_and]; ct_ok)
  have m7 : n7.mem = (runBlock ctS4 (n6.mem, reg n6)).1 := u7.mem
  have b7 : ∀ q : Fin 32, reg n7 q = (runBlock ctS4 (n6.mem, reg n6)).2 q := u7.regs
  have s7 : St n7.mem PV n7 0xE12 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have e6 : ∀ q : Fin 32, q.val ∈ [8, 19, 20, 21, 23, 24, 26] → reg n6 q = reg n1 q := fun q hq => by
    rw [r6 q (by revert hq; revert q; decide), r5k q (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide),
      r3k q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have g7 : W64 (memLoad32 n7.mem (B + 0x420 + 0x44)) (memLoad32 n7.mem (B + 0x420 + 0x4C)) =
      asr64 (W64 (reg n6 a0) (reg n6 a1)) := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [BitVec.or_comm]; exact w64_asr _ _
  have r7_10 : reg n7 a0 = reg n1 a0 := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, z6]
    rw [e6 _ (by decide), r10]; exact BitVec.zero_add _
  have r7_11 : reg n7 a1 = ul := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, z6]
    rw [e6 _ (by decide), r23]; exact BitVec.zero_add _
  have r7_12 : reg n7 a2 = uh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, z6]
    rw [e6 _ (by decide), r26]; exact BitVec.zero_add _
  have r7_18 : reg n7 (18 : Fin 32) = ql := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K6 (by decide), w54_5]
  have r7_13 : reg n7 a3 = ql := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6, z6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K6 (by decide), w54_5]; exact BitVec.zero_add _
  have r7_25 : reg n7 (25 : Fin 32) = qh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K6 (by decide), w1c_5]
  have r7_14 : reg n7 a4 = qh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6, z6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K6 (by decide), w1c_5]; exact BitVec.zero_add _
  have r7k : ∀ q : Fin 32, q.val ∈ [8, 19, 20, 21, 22, 23, 24, 26, 27] → reg n7 q = reg n6 q := fun q hq => by
    rw [b7, runBlock_reg _ _ _ _ z6 (by revert hq; revert q; decide)]
  have w40_7 : memLoad32 n7.mem (B + 0x420 + 0x40) = reg n2 a0 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w40_5
  have w38_7 : memLoad32 n7.mem (B + 0x420 + 0x38) = reg n2 a1 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w38_5
  have w50_7 : memLoad32 n7.mem (B + 0x420 + 0x50) = reg n4 a0 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w50_5
  have w48_7 : memLoad32 n7.mem (B + 0x420 + 0x48) = reg n4 a1 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w48_5
  have w30_7 : memLoad32 n7.mem (B + 0x420 + 0x30) = vh := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w30_5
  have w28_7 : memLoad32 n7.mem (B + 0x420 + 0x28) = rh := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w28_5
  have w3c_7 : memLoad32 n7.mem (B + 0x420 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w3c_5
  have w24_7 : memLoad32 n7.mem (B + 0x420 + 0x24) = (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K6 (by decide)]; exact w24_5
  have fr7 : ∀ x, PvR B x → n7.mem x = m.mem x := fun x hx => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [pvR_st32 hx, pvR_st8 hx]; rw [P6.fr x hx, fr5 x hx]
  have fk7 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n7.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctS4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st32 hS, fk_st8 hS]
    rw [kfk K6 he, fk5 e he h1 h2]
  -- the fourth select: `u` or `q`
  have E7 : PvEnv3 n7.mem := E.fr F fr7
  have sp7 : reg n7 sp = B + 0x420 := by rw [b7, runBlock_reg _ _ _ _ z6 (by decide), sp6]
  obtain ⟨n8, P8, K8, k8, v80, v81⟩ := pv_si F E7 s7 pv_at_e12 pv_at_e16 (by decide) (by decide) sp7
    (by rw [r7_10]; exact c3)
  have q8 : W64 (reg n8 a0) (reg n8 a1) = if reg n1 a0 = 1 then W64 ql qh else W64 ul uh := by
    rw [v80, v81, r7_10, w64_sel c3, r7_13, r7_14, r7_11, r7_12]
  have E8 : PvEnv3 n8.mem := E7.fr F P8.fr
  have r8' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n7 q := P8.regs
  -- segment 5, to the fifth select at 0xE36: store `u`, select `v` or `r`
  have sp8 : reg n8 sp = B + 0x420 := by rw [r8' _ (by decide), sp7]
  have z8 := P8.st.zero
  obtain ⟨n9, c9, u9⟩ := P8.st.block ctS5 E8.E.C.self ctS5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS5, upd, ↓reduceIte, sp8, and_true, true_and]; ct_ok)
  have m9 : n9.mem = (runBlock ctS5 (n8.mem, reg n8)).1 := u9.mem
  have b9 : ∀ q : Fin 32, reg n9 q = (runBlock ctS5 (n8.mem, reg n8)).2 q := u9.regs
  have s9 : St n9.mem PV n9 0xE36 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have u9 : W64 (memLoad32 n9.mem (B + 0x420 + 0x2C)) (memLoad32 n9.mem (B + 0x420 + 0x34)) =
      2 * W64 (reg n8 a0) (reg n8 a1) % 2 ^ 64 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    exact w64_shl1 _ _
  have e8 : ∀ q : Fin 32, q.val ∈ [19, 22, 24] → reg n8 q = reg n6 q := fun q hq => by
    rw [r8' q (by revert hq; revert q; decide), r7k q (by revert hq; revert q; decide)]
  have r9_10 : reg n9 a0 = reg n1 a0 := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, z8]
    rw [e8 _ (by decide), e6 _ (by decide), r10]; exact BitVec.zero_add _
  have r9_11 : reg n9 a1 = vl := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, z8]
    rw [e8 _ (by decide), e6 _ (by decide), r19]; exact BitVec.zero_add _
  have r9_8 : reg n9 (8 : Fin 32) = vh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K8 (by decide), w30_7]
  have r9_12 : reg n9 a2 = vh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8, z8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K8 (by decide), w30_7]; exact BitVec.zero_add _
  have r9_13 : reg n9 a3 = rl := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, z8]
    rw [e8 _ (by decide), r6 _ (by decide), r5k _ (by decide), r4 _ (by decide), r3_22]; exact BitVec.zero_add _
  have r9_21 : reg n9 (21 : Fin 32) = rh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K8 (by decide), w28_7]
  have r9_14 : reg n9 a4 = rh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8, z8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K8 (by decide), w28_7]; exact BitVec.zero_add _
  have r9k : ∀ q : Fin 32, q.val ∈ [9, 18, 19, 20, 22, 23, 24, 25, 26, 27] → reg n9 q = reg n8 q := fun q hq => by
    rw [b9, runBlock_reg _ _ _ _ z8 (by revert hq; revert q; decide)]
  have w40_9 : memLoad32 n9.mem (B + 0x420 + 0x40) = reg n2 a0 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]; exact w40_7
  have w38_9 : memLoad32 n9.mem (B + 0x420 + 0x38) = reg n2 a1 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]; exact w38_7
  have w50_9 : memLoad32 n9.mem (B + 0x420 + 0x50) = reg n4 a0 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]; exact w50_7
  have w48_9 : memLoad32 n9.mem (B + 0x420 + 0x48) = reg n4 a1 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]; exact w48_7
  have w3c_9 : memLoad32 n9.mem (B + 0x420 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]; exact w3c_7
  have w24_9 : memLoad32 n9.mem (B + 0x420 + 0x24) = (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]; exact w24_7
  have w44_9 : memLoad32 n9.mem (B + 0x420 + 0x44) = memLoad32 n7.mem (B + 0x420 + 0x44) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]
  have w4c_9 : memLoad32 n9.mem (B + 0x420 + 0x4C) = memLoad32 n7.mem (B + 0x420 + 0x4C) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K8 (by decide)]
  have fr9 : ∀ x, PvR B x → n9.mem x = m.mem x := fun x hx => by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [pvR_st32 hx, pvR_st8 hx]; rw [P8.fr x hx, fr7 x hx]
  have fk9 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n9.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctS5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st32 hS, fk_st8 hS]
    rw [kfk K8 he, fk7 e he h1 h2]
  have e9 : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → reg n9 q = reg m q := fun q hq => by
    rw [b9, runBlock_reg _ _ _ _ z8 (by revert hq; revert q; decide), r8' q (by revert hq; revert q; decide),
      b7, runBlock_reg _ _ _ _ z6 (by revert hq; revert q; decide), r6 q (by revert hq; revert q; decide),
      b5, runBlock_reg _ _ _ _ z4 (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide),
      r3k q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide),
      b1, runBlock_reg _ _ _ _ hz (by revert hq; revert q; decide)]
  have e9' : ∀ q : Fin 32, q.val ∈ [19, 22, 23, 26, 27] → reg n9 q = reg n6 q := fun q hq => by
    rw [r9k q (by revert hq; revert q; decide), r8' q (by revert hq; revert q; decide),
      r7k q (by revert hq; revert q; decide)]
  have e5' : ∀ q : Fin 32, q.val ∈ [19, 22, 23, 26, 27] → reg n6 q = reg n3 q := fun q hq => by
    rw [r6 q (by revert hq; revert q; decide), r5k q (by revert hq; revert q; decide),
      r4 q (by revert hq; revert q; decide)]
  have e2' : ∀ q : Fin 32, q.val ∈ [19, 23, 26, 27] → reg n3 q = reg n1 q := fun q hq => by
    rw [r3k q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have hc3 : reg n1 a0 = ctC3 gl dl dh := by rw [r10, r24]; rfl
  refine ⟨n9, c1.trans (P2.steps.trans (c3'.trans (P4.steps.trans (c5.trans (P6.steps.trans (c7.trans
    (P8.steps.trans c9))))))), E.fr F fr9, fr9, fk9, s9, by rw [b9, runBlock_reg _ _ _ _ z8 (by decide), sp8],
    e9 _ (by decide), e9 _ (by decide), by rw [r9_10, hc3], r9_11, r9_12, r9_13, r9_14, r9_8,
    by rw [r9k _ (by decide), r8' _ (by decide), r7_18], by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r19],
    r9_21, by rw [e9' _ (by decide), e5' _ (by decide), r3_22],
    by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r23],
    by rw [r9k _ (by decide), r8' _ (by decide), r7_25],
    by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r26],
    by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r27], w3c_9, w24_9, ?_, ?_, ?_, ?_⟩
  · rw [w40_9, w38_9, q2, hc3]
  · rw [w50_9, w48_9, q4, hc3]
  · rw [w44_9, w4c_9, g7, q6, q5a, q5b, hc3]
  · rw [u9, q8, hc3]

end C3.RV32.Pv
