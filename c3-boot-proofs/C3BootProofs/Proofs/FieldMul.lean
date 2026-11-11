import C3BootProofs.Proofs.FieldMontRed
import C3BootProofs.Image.BootloaderV0

/-! # `FieldElement::multiply`, end to end -/

namespace C3.RV32

open C3.ImageV0

set_option exponentiation.threshold 600 in
/-- What `sub_inner` makes of the reduction's output: the Montgomery product,
`R · 2^256 ≡ A · B (mod p)`, and below `p` when `A · B < p · 2^256`, as it is
when both operands are below `p`. -/
theorem mont_out {L AB q : Nat} (hAB : AB < 2 ^ 512) (hq : q < 2 ^ 256) (h : L * 2 ^ 256 = AB + q * p256) :
    (subRes L * 2 ^ 256) % p256 = AB % p256 ∧ (AB < p256 * 2 ^ 256 → subRes L < p256) := by
  unfold subRes
  rw [show p256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951 from rfl] at h ⊢
  rw [show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936
    from rfl] at hq h ⊢
  rw [show (2 : Nat) ^ 512 = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
    from rfl] at hAB
  by_cases hl : L < 115792089210356248762697446949407573530086143415290314195533631308867097853951
  · have e : L % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = L := Nat.mod_eq_of_lt (by omega)
    rw [ite_eq_left hl, e]; constructor <;> omega
  · have hL : L < 115792089237316195423570985008687907853269984665640564039457584007913129639936 + 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by omega
    have e : (L - 115792089210356248762697446949407573530086143415290314195533631308867097853951) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = L - 115792089210356248762697446949407573530086143415290314195533631308867097853951 := Nat.mod_eq_of_lt (by omega)
    rw [ite_eq_right hl, e]; constructor <;> omega

/-- Where `FieldElement::multiply` runs: its code at `P`, the code of
`widening_mul_fixed::<8, 8>` and `sub_inner` and their helpers where the
image puts them relative to it, the 0x130 bytes of stack below `sp0` that it
and its callees use, apart from all that code, the 8-word result at `res`,
and the 8-word operands at `ap` and `bp`. -/
structure FMEnv (M : Word → BitVec 8) (P sp0 res ap bp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P fieldMulCode
  wmcode : CodeIn M (P + 0xFFFFBEE4) wideMulCode
  wmsave : CodeIn M (P + 0xFFFFBEE4 + 0x1242A) wideMulSaveCode
  wmrestore : CodeIn M (P + 0xFFFFBEE4 + 0x1241A) wideMulRestoreCode
  mset : CodeIn M (P + 0xFFFFBEE4 + 0x129E4) memsetCode
  stub : CodeIn M (P + 0xFFFFBEE4 + 0x12A4C) memcpyStubCode
  body : CodeIn M (P + 0xFFFFBEE4 + 0x12A54) memcpyBodyCode
  sicode : CodeIn M (P + 0x3FC) subInnerCode
  bsub : CodeIn M (siBsub (P + 0x3FC)) borrowingSubCode
  sisave : CodeIn M (P + 0x3FC + 0xDC34) subInnerSaveCode
  sirestore : CodeIn M (P + 0x3FC + 0xDE3E) subInnerRestoreCode
  hsp : sp0.toNat % 4 = 0
  hres : res.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hS : 0x130 ≤ sp0.toNat
  hwr : res.toNat + 32 ≤ 2 ^ 32
  sC : Sep (sp0 + 0xFFFFFED0) 0x130 P fieldMulCode.length
  sW : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0xFFFFBEE4) wideMulCode.length
  sWs : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0xFFFFBEE4 + 0x1242A) wideMulSaveCode.length
  sWr : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0xFFFFBEE4 + 0x1241A) wideMulRestoreCode.length
  sM : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0xFFFFBEE4 + 0x129E4) memsetCode.length
  sU : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0xFFFFBEE4 + 0x12A4C) memcpyStubCode.length
  sB : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0xFFFFBEE4 + 0x12A54) memcpyBodyCode.length
  sI : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0x3FC) subInnerCode.length
  sIb : Sep (sp0 + 0xFFFFFED0) 0x130 (siBsub (P + 0x3FC)) borrowingSubCode.length
  sIs : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0x3FC + 0xDC34) subInnerSaveCode.length
  sIr : Sep (sp0 + 0xFFFFFED0) 0x130 (P + 0x3FC + 0xDE3E) subInnerRestoreCode.length
  sRS : Sep res 32 (sp0 + 0xFFFFFED0) 0x130
  sRC : Sep res 32 P fieldMulCode.length
  sAS : Sep ap 32 (sp0 + 0xFFFFFED0) 0x130
  sBS : Sep bp 32 (sp0 + 0xFFFFFED0) 0x130

/-- `FieldElement::multiply`'s frame: 0xD0 bytes below `sp0`, the top of the
0x130 bytes its environment keeps apart. -/
theorem fm_frame (sp0 : Word) : sp0 + 0xFFFFFF30 = sp0 + 0xFFFFFED0 + BitVec.ofNat 32 0x60 := by
  rw [BitVec.add_assoc]; rfl

/-- The registers `FieldElement::multiply` saves in its frame, at their
offsets from its `sp`. -/
abbrev fmPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0xCC), ((8 : Fin 32), BitVec.ofNat 32 0xC8), ((9 : Fin 32), BitVec.ofNat 32 0xC4),
   ((18 : Fin 32), BitVec.ofNat 32 0xC0), ((19 : Fin 32), BitVec.ofNat 32 0xBC),
   ((20 : Fin 32), BitVec.ofNat 32 0xB8), ((21 : Fin 32), BitVec.ofNat 32 0xB4),
   ((22 : Fin 32), BitVec.ofNat 32 0xB0), ((23 : Fin 32), BitVec.ofNat 32 0xAC)]

theorem wordsAt_congr {M M' : Word → BitVec 8} {b : Word} {n : Nat}
    (h : ∀ i, i < n → memLoad32 M' (b + BitVec.ofNat 32 (4 * i)) = memLoad32 M (b + BitVec.ofNat 32 (4 * i))) :
    wordsAt M' b n = wordsAt M b n := by
  unfold wordsAt
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The registers `FieldElement::multiply` keeps from entry to the call of
`sub_inner`. -/
def fmKeep (q : Fin 32) : Bool := q.val ∉ [1, 2, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 28]

set_option maxHeartbeats 8000000 in
/-- `FieldElement::multiply` to 0x20: save the callee-saved registers in a
0xD0-byte frame and call `widening_mul_fixed::<8, 8>`, which leaves the
product at the frame's base. -/
theorem fm_pro (m : Machine) {P sp0 res ap bp : Word} (env : FMEnv m.mem P sp0 res ap bp) (hpc : m.pc = P)
    (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x20 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ fmPs → memLoad32 M (sp0 + 0xFFFFFF30 + o) = reg m r) ∧
      limbVal (wordsAt M (sp0 + 0xFFFFFF30) 16) = limbVal (wordsAt m.mem ap 8) * limbVal (wordsAt m.mem bp 8) ∧
      reg n sp = sp0 + 0xFFFFFF30 ∧ reg n (18 : Fin 32) = res ∧ ∀ q, fmKeep q = true → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hS := env.hS
  have hG : (sp0 + 0xFFFFFF30).toNat = sp0.toNat - 0xD0 := by
    rw [BitVec.toNat_add]; have : (0xFFFFFF30 : Word).toNat = 4294967088 := rfl
    have := sp0.isLt; omega
  have hGa : (sp0 + 0xFFFFFF30).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF30) (by decide)
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFED0) 0x130 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- the frame's top: the save slots at 0xAC to 0xCF, 0x60 + 0xAC bytes into the 0x130
  have slotS : ∀ c, 0xAC ≤ c → c + 4 ≤ 0xD0 → ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 →
      Sep (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 x hx => by
    rw [fm_frame, add_ofNat_assoc]; exact hx.sub (by omega)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code fm_at_0 (off' := 2) (by decide)
  obtain ⟨f1, hf1⟩ : ∃ f1, upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF30) = f1 := ⟨_, rfl⟩
  rw [hf1] at u1
  have f1sp : f1 sp = sp0 + 0xFFFFFF30 := by rw [← hf1]; simp +decide [upd, hsp]; rfl
  have f1q : ∀ q, q ≠ sp → f1 q = reg m q := fun q h => by
    rw [← hf1]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h]
  have F1 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → m.mem x = m.mem x := fun _ _ => rfl
  obtain ⟨m2, d2, u2⟩ := u1.sw (codeS env.code env.sC F1) fm_at_2 (off' := 0x4) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xCC) (by decide))
  rw [f1sp, show (0xCC : Word) = BitVec.ofNat 32 0xCC from rfl] at u2
  obtain ⟨M2, hM2⟩ : ∃ M, memStore32 m.mem (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xCC) (f1 ra) = M := ⟨_, rfl⟩
  rw [hM2] at u2
  have F2 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2, memStore32_get_sep (slotS 0xCC (by decide) (by decide) x hx), F1 x hx]
  obtain ⟨m3, d3, u3⟩ := u2.sw (codeS env.code env.sC F2) fm_at_4 (off' := 0x6) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xC8) (by decide))
  rw [f1sp, show (0xC8 : Word) = BitVec.ofNat 32 0xC8 from rfl] at u3
  obtain ⟨M3, hM3⟩ : ∃ M, memStore32 M2 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xC8) (f1 (8 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM3] at u3
  have F3 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (slotS 0xC8 (by decide) (by decide) x hx), F2 x hx]
  obtain ⟨m4, d4, u4⟩ := u3.sw (codeS env.code env.sC F3) fm_at_6 (off' := 0x8) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xC4) (by decide))
  rw [f1sp, show (0xC4 : Word) = BitVec.ofNat 32 0xC4 from rfl] at u4
  obtain ⟨M4, hM4⟩ : ∃ M, memStore32 M3 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xC4) (f1 (9 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM4] at u4
  have F4 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, memStore32_get_sep (slotS 0xC4 (by decide) (by decide) x hx), F3 x hx]
  obtain ⟨m5, d5, u5⟩ := u4.sw (codeS env.code env.sC F4) fm_at_8 (off' := 0xA) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xC0) (by decide))
  rw [f1sp, show (0xC0 : Word) = BitVec.ofNat 32 0xC0 from rfl] at u5
  obtain ⟨M5, hM5⟩ : ∃ M, memStore32 M4 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xC0) (f1 (18 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM5] at u5
  have F5 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5, memStore32_get_sep (slotS 0xC0 (by decide) (by decide) x hx), F4 x hx]
  obtain ⟨m6, d6, u6⟩ := u5.sw (codeS env.code env.sC F5) fm_at_a (off' := 0xC) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xBC) (by decide))
  rw [f1sp, show (0xBC : Word) = BitVec.ofNat 32 0xBC from rfl] at u6
  obtain ⟨M6, hM6⟩ : ∃ M, memStore32 M5 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xBC) (f1 (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM6] at u6
  have F6 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M6 x = m.mem x := fun x hx => by
    rw [← hM6, memStore32_get_sep (slotS 0xBC (by decide) (by decide) x hx), F5 x hx]
  obtain ⟨m7, d7, u7⟩ := u6.sw (codeS env.code env.sC F6) fm_at_c (off' := 0xE) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xB8) (by decide))
  rw [f1sp, show (0xB8 : Word) = BitVec.ofNat 32 0xB8 from rfl] at u7
  obtain ⟨M7, hM7⟩ : ∃ M, memStore32 M6 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xB8) (f1 (20 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM7] at u7
  have F7 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M7 x = m.mem x := fun x hx => by
    rw [← hM7, memStore32_get_sep (slotS 0xB8 (by decide) (by decide) x hx), F6 x hx]
  obtain ⟨m8, d8, u8⟩ := u7.sw (codeS env.code env.sC F7) fm_at_e (off' := 0x10) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xB4) (by decide))
  rw [f1sp, show (0xB4 : Word) = BitVec.ofNat 32 0xB4 from rfl] at u8
  obtain ⟨M8, hM8⟩ : ∃ M, memStore32 M7 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xB4) (f1 (21 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM8] at u8
  have F8 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8, memStore32_get_sep (slotS 0xB4 (by decide) (by decide) x hx), F7 x hx]
  obtain ⟨m9, d9, u9⟩ := u8.sw (codeS env.code env.sC F8) fm_at_10 (off' := 0x12) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xB0) (by decide))
  rw [f1sp, show (0xB0 : Word) = BitVec.ofNat 32 0xB0 from rfl] at u9
  obtain ⟨M9, hM9⟩ : ∃ M, memStore32 M8 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xB0) (f1 (22 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM9] at u9
  have F9 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M9 x = m.mem x := fun x hx => by
    rw [← hM9, memStore32_get_sep (slotS 0xB0 (by decide) (by decide) x hx), F8 x hx]
  obtain ⟨m10, d10, u10⟩ := u9.sw (codeS env.code env.sC F9) fm_at_12 (off' := 0x14) (by decide)
    (by rw [f1sp]; exact aligned_add hGa (k := 0xAC) (by decide))
  rw [f1sp, show (0xAC : Word) = BitVec.ofNat 32 0xAC from rfl] at u10
  obtain ⟨M10, hM10⟩ : ∃ M, memStore32 M9 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xAC) (f1 (23 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM10] at u10
  have F10 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M10 x = m.mem x := fun x hx => by
    rw [← hM10, memStore32_get_sep (slotS 0xAC (by decide) (by decide) x hx), F9 x hx]
  have slots : ∀ r o, (r, o) ∈ fmPs → memLoad32 M10 (sp0 + 0xFFFFFF30 + o) = reg m r := by
    intro r o h
    simp only [fmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [← hM10, ← hM9, ← hM8, ← hM7, ← hM6, ← hM5, ← hM4, ← hM3, ← hM2]
      simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
      exact f1q _ (by decide)
  have cM := codeS env.code env.sC F10
  have z1 : f1 0 = 0 := u1.zero
  obtain ⟨m11, d11, u11⟩ := u10.alu cM fm_at_14 (off' := 0x16) (by decide)
  obtain ⟨m12, d12, u12⟩ := u11.alu cM fm_at_16 (off' := 0x18) (by decide)
  obtain ⟨f12, hf12⟩ : ∃ f, upd (upd f1 (18 : Fin 32) (aluEval .add (f1 x0) (f1 a0))) a0
      (aluEval .add (upd f1 (18 : Fin 32) (aluEval .add (f1 x0) (f1 a0)) x0)
        (upd f1 (18 : Fin 32) (aluEval .add (f1 x0) (f1 a0)) sp)) = f := ⟨_, rfl⟩
  rw [hf12] at u12
  have g0 : f12 a0 = sp0 + 0xFFFFFF30 := by
    rw [← hf12]; simp +decide only [upd, ↓reduceIte, f1sp]; exact BitVec.zero_add _
  have g18 : f12 (18 : Fin 32) = res := by
    rw [← hf12]; simp +decide only [upd, ↓reduceIte, z1]; rw [f1q _ (by decide), ha0]; exact BitVec.zero_add _
  have gq : ∀ q, q ≠ a0 → q ≠ (18 : Fin 32) → f12 q = f1 q := fun q h0 h18 => by
    rw [← hf12]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, z1]
    · simp [upd, hq, h0, h18]
  have hev : (P + 0xFFFFBEE4).toNat % 2 = 0 := even_at P env.hP 0xFFFFBEE4 (by decide)
  obtain ⟨m13, c13, pc13, mem13, regs13⟩ := u12.callRa cM fm_at_18 fm_at_1c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) hev
  have r13 := PEnv.reg1 regs13 u12.zero
  have sAlias : sp0 + 0xFFFFFF30 + 0xFFFFFFA0 = sp0 + 0xFFFFFED0 := by rw [BitVec.add_assoc]; rfl
  have base0 : ∀ {a : Word} {n : Nat} {b : Word} {k : Nat}, Sep (a + BitVec.ofNat 32 0) n b k → Sep a n b k :=
    fun h => by rwa [add_ofNat_zero] at h
  have base0r : ∀ {a : Word} {n : Nat} {b : Word} {k : Nat}, Sep a n (b + BitVec.ofNat 32 0) k → Sep a n b k :=
    fun h => by rwa [add_ofNat_zero] at h
  have top : ∀ {b : Word} {k : Nat}, Sep (sp0 + 0xFFFFFED0) 0x130 b k →
      Sep (sp0 + 0xFFFFFF30 + 0xFFFFFFA0) 0x60 b k := fun h => by
    rw [sAlias]; exact base0 (h.sub (c := 0) (l := 0x60) (by decide))
  have outS : ∀ {b : Word} {k : Nat}, Sep (sp0 + 0xFFFFFED0) 0x130 b k → Sep (sp0 + 0xFFFFFF30) 64 b k :=
    fun h => by rw [fm_frame]; exact h.sub (c := 0x60) (l := 64) (by decide)
  have wenv : WMEnv m13.mem (P + 0xFFFFBEE4) (sp0 + 0xFFFFFF30) (sp0 + 0xFFFFFF30) ap bp := by
    rw [mem13]
    exact ⟨hev, codeS env.wmcode env.sW F10, codeS env.wmsave env.sWs F10, codeS env.wmrestore env.sWr F10,
      codeS env.mset env.sM F10, codeS env.stub env.sU F10, codeS env.body env.sB F10, hGa, hGa, env.hap,
      env.hbp, by omega, by have := sp0.isLt; omega, top env.sW, top env.sWs, top env.sWr, top env.sM,
      top env.sU, top env.sB, outS env.sW, outS env.sWr, outS env.sU, outS env.sB,
      by
        rw [sAlias, fm_frame]
        exact base0r (sep_offsets (sp0 + 0xFFFFFED0) (c := 0x60) (n := 64) (d := 0) (k := 0x60)
          (.inr (by decide)) (by decide) (by decide)),
      by rw [sAlias]; exact base0r (env.sAS.subR (c := 0) (l := 0x60) (by decide)),
      by rw [sAlias]; exact base0r (env.sBS.subR (c := 0) (l := 0x60) (by decide))⟩
  obtain ⟨m14, c14, pc14, sp14, regs14, prod14, frame14⟩ := wideMul_correct m13 wenv pc13
    (by rw [r13 a0 (by decide), g0]) (by rw [r13 a1 (by decide), gq a1 (by decide) (by decide), f1q a1 (by decide), ha1])
    (by rw [r13 a2 (by decide), gq a2 (by decide) (by decide), f1q a2 (by decide), ha2])
    (by rw [regs13]; simp +decide [upd]) (even_clear _ (even_at P env.hP 0x20 (by decide)))
    (by rw [r13 sp (by decide), gq sp (by decide) (by decide), f1sp])
  rw [mem13] at prod14 frame14
  have inS : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → m14.mem x = M10 x := fun x hx =>
    frame14 x (top hx) (outS hx)
  have keepTop : ∀ c, 0x40 ≤ c → c < 0xD0 →
      m14.mem (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) = M10 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) :=
    fun c h1 h2 => frame14 _
      (by
        rw [sAlias, fm_frame, add_ofNat_assoc]
        exact base0 (sep_offsets (sp0 + 0xFFFFFED0) (c := 0) (n := 0x60) (d := 0x60 + c) (k := 1)
          (.inl (by omega)) (by decide) (by omega)))
      (base0 (sep_offsets (sp0 + 0xFFFFFF30) (c := 0) (n := 64) (d := c) (k := 1) (.inl (by omega))
        (by decide) (by omega)))
  have opnd : ∀ {b : Word}, Sep b 32 (sp0 + 0xFFFFFED0) 0x130 → wordsAt M10 b 8 = wordsAt m.mem b 8 :=
    fun hb => wordsAt_congr fun i hi => memLoad32_congr fun j hj => F10 _ (by
      have := hb.symm.subR (c := 4 * i + j) (l := 1) (by omega)
      rwa [← add_ofNat_assoc] at this)
  refine ⟨m14, m14.mem, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 (.cons d12 (c13.trans c14)))))))))))),
    ⟨by rw [pc14], rfl, fun _ => rfl⟩, fun x hx => (inS x hx).trans (F10 x hx), ?_, ?_, sp14, ?_, ?_⟩
  · intro r o h
    rw [← slots r o h]
    simp only [fmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact keepTop _ (by omega) (by omega)
  · rw [prod14, opnd env.sAS, opnd env.sBS]
  · rw [regs14 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), r13 _ (by decide), g18]
  · intro q hq
    have k := fun r (hr : fmKeep r = false) => bkeep_ne hq hr
    rw [regs14 q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl)
      (k t0 rfl) (k t1 rfl) (k 7 rfl) (k 28 rfl), r13 q (k ra rfl), gq q (k a0 rfl) (k 18 rfl), f1q q (k sp rfl)]

theorem wordsAt9 (M : Word → BitVec 8) (b : Word) :
    wordsAt M b 9 = [memLoad32 M (b + BitVec.ofNat 32 (4 * 0)), memLoad32 M (b + BitVec.ofNat 32 (4 * 1)),
      memLoad32 M (b + BitVec.ofNat 32 (4 * 2)), memLoad32 M (b + BitVec.ofNat 32 (4 * 3)),
      memLoad32 M (b + BitVec.ofNat 32 (4 * 4)), memLoad32 M (b + BitVec.ofNat 32 (4 * 5)),
      memLoad32 M (b + BitVec.ofNat 32 (4 * 6)), memLoad32 M (b + BitVec.ofNat 32 (4 * 7)),
      memLoad32 M (b + BitVec.ofNat 32 (4 * 8))] := rfl

/-- The registers the end of `FieldElement::multiply`, with `sub_inner`, leaves alone. -/
def fmKeep2 (q : Fin 32) : Bool := q.val ∉ [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23]

set_option maxHeartbeats 8000000 in
/-- The end of `FieldElement::multiply`, from 0x28C: store the reduction's nine
words and the modulus, call `sub_inner`, copy its result to `res`, restore
the callee-saved registers, and return. -/
theorem fm_epi {P sp0 res ap bp : Word} {M0 Mx : Word → BitVec 8} {n : Machine} {v : Fin 32 → Word}
    (env : FMEnv M0 P sp0 res ap bp) (s : St Mx P n 0x28C (reg n))
    (hfr : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → Mx x = M0 x)
    (hsl : ∀ r o, (r, o) ∈ fmPs → memLoad32 Mx (sp0 + 0xFFFFFF30 + o) = v r)
    (rsp : reg n sp = sp0 + 0xFFFFFF30) (r18 : reg n (18 : Fin 32) = res) (r19 : reg n (19 : Fin 32) = 0xFFFFFFFF) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧
      limbVal (wordsAt n'.mem res 8) = subRes (limbVal [reg n (7 : Fin 32), reg n (6 : Fin 32), reg n (5 : Fin 32),
        reg n a5, reg n a4, reg n a0, reg n a1, reg n a2, reg n a3]) ∧
      (∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → Sep res 32 x 1 → n'.mem x = M0 x) ∧
      reg n' sp = sp0 ∧ (∀ r o, (r, o) ∈ fmPs → reg n' r = v r) ∧ ∀ q, fmKeep2 q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hS := env.hS
  have hG : (sp0 + 0xFFFFFF30).toNat = sp0.toNat - 0xD0 := by
    rw [BitVec.toNat_add]; have : (0xFFFFFF30 : Word).toNat = 4294967088 := rfl
    have := sp0.isLt; omega
  have hGa : (sp0 + 0xFFFFFF30).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF30) (by decide)
  have codeX : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code →
      Sep (sp0 + 0xFFFFFED0) 0x130 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc hs hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inG : ∀ c, 0x64 ≤ c → c + 4 ≤ 0xAC → ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 →
      Sep (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 x hx => by
    rw [fm_frame, add_ofNat_assoc]; exact hx.sub (by omega)
  have F0 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → Mx x = M0 x := hfr
  obtain ⟨e1, x1, t1⟩ := s.sw (codeX env.code env.sC F0) fm_at_28c (off' := 0x28E) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x64) (by decide))
  rw [rsp, show (0x64 : Word) = BitVec.ofNat 32 0x64 from rfl] at t1
  obtain ⟨N1, hN1⟩ : ∃ M, memStore32 Mx (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x64) (reg n (7 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hN1] at t1
  have F1 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N1 x = M0 x := fun x hx => by
    rw [← hN1, memStore32_get_sep (inG 0x64 (by decide) (by decide) x hx), F0 x hx]
  obtain ⟨e2, x2, t2⟩ := t1.sw (codeX env.code env.sC F1) fm_at_28e (off' := 0x290) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x68) (by decide))
  rw [rsp, show (0x68 : Word) = BitVec.ofNat 32 0x68 from rfl] at t2
  obtain ⟨N2, hN2⟩ : ∃ M, memStore32 N1 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x68) (reg n (6 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hN2] at t2
  have F2 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N2 x = M0 x := fun x hx => by
    rw [← hN2, memStore32_get_sep (inG 0x68 (by decide) (by decide) x hx), F1 x hx]
  obtain ⟨e3, x3, t3⟩ := t2.sw (codeX env.code env.sC F2) fm_at_290 (off' := 0x292) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x6C) (by decide))
  rw [rsp, show (0x6C : Word) = BitVec.ofNat 32 0x6C from rfl] at t3
  obtain ⟨N3, hN3⟩ : ∃ M, memStore32 N2 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x6C) (reg n (5 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hN3] at t3
  have F3 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N3 x = M0 x := fun x hx => by
    rw [← hN3, memStore32_get_sep (inG 0x6C (by decide) (by decide) x hx), F2 x hx]
  obtain ⟨e4, x4, t4⟩ := t3.sw (codeX env.code env.sC F3) fm_at_292 (off' := 0x294) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x70) (by decide))
  rw [rsp, show (0x70 : Word) = BitVec.ofNat 32 0x70 from rfl] at t4
  obtain ⟨N4, hN4⟩ : ∃ M, memStore32 N3 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x70) (reg n a5) = M := ⟨_, rfl⟩
  rw [hN4] at t4
  have F4 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N4 x = M0 x := fun x hx => by
    rw [← hN4, memStore32_get_sep (inG 0x70 (by decide) (by decide) x hx), F3 x hx]
  obtain ⟨e5, x5, t5⟩ := t4.sw (codeX env.code env.sC F4) fm_at_294 (off' := 0x296) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x74) (by decide))
  rw [rsp, show (0x74 : Word) = BitVec.ofNat 32 0x74 from rfl] at t5
  obtain ⟨N5, hN5⟩ : ∃ M, memStore32 N4 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x74) (reg n a4) = M := ⟨_, rfl⟩
  rw [hN5] at t5
  have F5 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N5 x = M0 x := fun x hx => by
    rw [← hN5, memStore32_get_sep (inG 0x74 (by decide) (by decide) x hx), F4 x hx]
  obtain ⟨e6, x6, t6⟩ := t5.sw (codeX env.code env.sC F5) fm_at_296 (off' := 0x298) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x78) (by decide))
  rw [rsp, show (0x78 : Word) = BitVec.ofNat 32 0x78 from rfl] at t6
  obtain ⟨N6, hN6⟩ : ∃ M, memStore32 N5 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x78) (reg n a0) = M := ⟨_, rfl⟩
  rw [hN6] at t6
  have F6 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N6 x = M0 x := fun x hx => by
    rw [← hN6, memStore32_get_sep (inG 0x78 (by decide) (by decide) x hx), F5 x hx]
  obtain ⟨e7, x7, t7⟩ := t6.sw (codeX env.code env.sC F6) fm_at_298 (off' := 0x29A) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x7C) (by decide))
  rw [rsp, show (0x7C : Word) = BitVec.ofNat 32 0x7C from rfl] at t7
  obtain ⟨N7, hN7⟩ : ∃ M, memStore32 N6 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x7C) (reg n a1) = M := ⟨_, rfl⟩
  rw [hN7] at t7
  have F7 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N7 x = M0 x := fun x hx => by
    rw [← hN7, memStore32_get_sep (inG 0x7C (by decide) (by decide) x hx), F6 x hx]
  obtain ⟨e8, x8, t8⟩ := t7.sw (codeX env.code env.sC F7) fm_at_29a (off' := 0x29C) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x80) (by decide))
  rw [rsp, show (0x80 : Word) = BitVec.ofNat 32 0x80 from rfl] at t8
  obtain ⟨N8, hN8⟩ : ∃ M, memStore32 N7 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x80) (reg n a2) = M := ⟨_, rfl⟩
  rw [hN8] at t8
  have F8 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N8 x = M0 x := fun x hx => by
    rw [← hN8, memStore32_get_sep (inG 0x80 (by decide) (by decide) x hx), F7 x hx]
  obtain ⟨e9, x9, t9⟩ := t8.sw (codeX env.code env.sC F8) fm_at_29c (off' := 0x29E) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x84) (by decide))
  rw [rsp, show (0x84 : Word) = BitVec.ofNat 32 0x84 from rfl] at t9
  obtain ⟨N9, hN9⟩ : ∃ M, memStore32 N8 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x84) (reg n a3) = M := ⟨_, rfl⟩
  rw [hN9] at t9
  have F9 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N9 x = M0 x := fun x hx => by
    rw [← hN9, memStore32_get_sep (inG 0x84 (by decide) (by decide) x hx), F8 x hx]
  obtain ⟨e10, x10, t10⟩ := t9.sw (codeX env.code env.sC F9) fm_at_29e (off' := 0x2A0) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x88) (by decide))
  rw [rsp, show (0x88 : Word) = BitVec.ofNat 32 0x88 from rfl] at t10
  obtain ⟨N10, hN10⟩ : ∃ M, memStore32 N9 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x88) (reg n (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hN10] at t10
  have F10 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N10 x = M0 x := fun x hx => by
    rw [← hN10, memStore32_get_sep (inG 0x88 (by decide) (by decide) x hx), F9 x hx]
  obtain ⟨e11, x11, t11⟩ := t10.sw (codeX env.code env.sC F10) fm_at_2a0 (off' := 0x2A2) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x8C) (by decide))
  rw [rsp, show (0x8C : Word) = BitVec.ofNat 32 0x8C from rfl] at t11
  obtain ⟨N11, hN11⟩ : ∃ M, memStore32 N10 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x8C) (reg n (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hN11] at t11
  have F11 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N11 x = M0 x := fun x hx => by
    rw [← hN11, memStore32_get_sep (inG 0x8C (by decide) (by decide) x hx), F10 x hx]
  obtain ⟨e12, x12, t12⟩ := t11.sw (codeX env.code env.sC F11) fm_at_2a2 (off' := 0x2A4) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x90) (by decide))
  rw [rsp, show (0x90 : Word) = BitVec.ofNat 32 0x90 from rfl] at t12
  obtain ⟨N12, hN12⟩ : ∃ M, memStore32 N11 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x90) (reg n (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hN12] at t12
  have F12 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N12 x = M0 x := fun x hx => by
    rw [← hN12, memStore32_get_sep (inG 0x90 (by decide) (by decide) x hx), F11 x hx]
  obtain ⟨e13, x13, t13⟩ := t12.sw (codeX env.code env.sC F12) fm_at_2a4 (off' := 0x2A6) (by decide)
    (by rw [rsp]; exact aligned_add hGa (k := 0x94) (by decide))
  rw [rsp, show (0x94 : Word) = BitVec.ofNat 32 0x94 from rfl] at t13
  obtain ⟨N13, hN13⟩ : ∃ M, memStore32 N12 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x94) (reg n x0) = M := ⟨_, rfl⟩
  rw [hN13] at t13
  have F13 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N13 x = M0 x := fun x hx => by
    rw [← hN13, memStore32_get_sep (inG 0x94 (by decide) (by decide) x hx), F12 x hx]
  obtain ⟨e14, x14, t14⟩ := t13.aluImm (codeX env.code env.sC F13) fm_at_2a6 (off' := 0x2A8) (by decide)
  obtain ⟨f2, hf2⟩ : ∃ f, upd (reg n) a0 (aluEval .add (reg n x0) 1) = f := ⟨_, rfl⟩
  rw [hf2] at t14
  have f2sp : f2 sp = sp0 + 0xFFFFFF30 := by rw [← hf2]; simp +decide only [upd, ↓reduceIte, rsp]
  have f2q : ∀ q, q ≠ a0 → f2 q = reg n q := fun q h => by
    rw [← hf2]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h]
  obtain ⟨e15, x15, t15⟩ := t14.sw (codeX env.code env.sC F13) fm_at_2a8 (off' := 0x2AA) (by decide)
    (by rw [f2sp]; exact aligned_add hGa (k := 0x98) (by decide))
  rw [f2sp, show (0x98 : Word) = BitVec.ofNat 32 0x98 from rfl] at t15
  obtain ⟨N15, hN15⟩ : ∃ M, memStore32 N13 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x98) (f2 x0) = M := ⟨_, rfl⟩
  rw [hN15] at t15
  have F15 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N15 x = M0 x := fun x hx => by
    rw [← hN15, memStore32_get_sep (inG 0x98 (by decide) (by decide) x hx), F13 x hx]
  obtain ⟨e16, x16, t16⟩ := t15.sw (codeX env.code env.sC F15) fm_at_2aa (off' := 0x2AC) (by decide)
    (by rw [f2sp]; exact aligned_add hGa (k := 0x9C) (by decide))
  rw [f2sp, show (0x9C : Word) = BitVec.ofNat 32 0x9C from rfl] at t16
  obtain ⟨N16, hN16⟩ : ∃ M, memStore32 N15 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x9C) (f2 x0) = M := ⟨_, rfl⟩
  rw [hN16] at t16
  have F16 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N16 x = M0 x := fun x hx => by
    rw [← hN16, memStore32_get_sep (inG 0x9C (by decide) (by decide) x hx), F15 x hx]
  obtain ⟨e17, x17, t17⟩ := t16.sw (codeX env.code env.sC F16) fm_at_2ac (off' := 0x2AE) (by decide)
    (by rw [f2sp]; exact aligned_add hGa (k := 0xA0) (by decide))
  rw [f2sp, show (0xA0 : Word) = BitVec.ofNat 32 0xA0 from rfl] at t17
  obtain ⟨N17, hN17⟩ : ∃ M, memStore32 N16 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xA0) (f2 a0) = M := ⟨_, rfl⟩
  rw [hN17] at t17
  have F17 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N17 x = M0 x := fun x hx => by
    rw [← hN17, memStore32_get_sep (inG 0xA0 (by decide) (by decide) x hx), F16 x hx]
  obtain ⟨e18, x18, t18⟩ := t17.sw (codeX env.code env.sC F17) fm_at_2ae (off' := 0x2B0) (by decide)
    (by rw [f2sp]; exact aligned_add hGa (k := 0xA4) (by decide))
  rw [f2sp, show (0xA4 : Word) = BitVec.ofNat 32 0xA4 from rfl] at t18
  obtain ⟨N18, hN18⟩ : ∃ M, memStore32 N17 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xA4) (f2 (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hN18] at t18
  have F18 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N18 x = M0 x := fun x hx => by
    rw [← hN18, memStore32_get_sep (inG 0xA4 (by decide) (by decide) x hx), F17 x hx]
  obtain ⟨e19, x19, t19⟩ := t18.sw (codeX env.code env.sC F18) fm_at_2b0 (off' := 0x2B2) (by decide)
    (by rw [f2sp]; exact aligned_add hGa (k := 0xA8) (by decide))
  rw [f2sp, show (0xA8 : Word) = BitVec.ofNat 32 0xA8 from rfl] at t19
  obtain ⟨N19, hN19⟩ : ∃ M, memStore32 N18 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0xA8) (f2 x0) = M := ⟨_, rfl⟩
  rw [hN19] at t19
  have F19 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → N19 x = M0 x := fun x hx => by
    rw [← hN19, memStore32_get_sep (inG 0xA8 (by decide) (by decide) x hx), F18 x hx]
  have cC := codeX env.code env.sC F19
  obtain ⟨e20, x20, t20⟩ := t19.aluImm cC fm_at_2b2 (off' := 0x2B4) (by decide)
  obtain ⟨e21, x21, t21⟩ := t20.aluImm cC fm_at_2b4 (off' := 0x2B6) (by decide)
  obtain ⟨e22, x22, t22⟩ := t21.aluImm cC fm_at_2b6 (off' := 0x2B8) (by decide)
  obtain ⟨f3, hf3⟩ : ∃ f, upd (upd (upd f2 a0 (aluEval .add (f2 sp) 0x40)) a1
      (aluEval .add (upd f2 a0 (aluEval .add (f2 sp) 0x40) sp) 0x64)) a2
      (aluEval .add (upd (upd f2 a0 (aluEval .add (f2 sp) 0x40)) a1
        (aluEval .add (upd f2 a0 (aluEval .add (f2 sp) 0x40) sp) 0x64) sp) 0x88) = f := ⟨_, rfl⟩
  rw [hf3] at t22
  have f3a0 : f3 a0 = sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x40 := by rw [← hf3]; simp +decide only [upd, ↓reduceIte, f2sp]; rfl
  have f3a1 : f3 a1 = sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x64 := by rw [← hf3]; simp +decide only [upd, ↓reduceIte, f2sp]; rfl
  have f3a2 : f3 a2 = sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x88 := by rw [← hf3]; simp +decide only [upd, ↓reduceIte, f2sp]; rfl
  have f3q : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → f3 q = f2 q := fun q h0 h1 h2 => by
    rw [← hf3]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, t19.zero]
    · simp [upd, hq, h0, h1, h2]
  have lpw : wordsAt N19 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x64) 9 = [reg n (7 : Fin 32), reg n (6 : Fin 32),
      reg n (5 : Fin 32), reg n a5, reg n a4, reg n a0, reg n a1, reg n a2, reg n a3] := by
    rw [wordsAt9, add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 1),
      add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 4),
      add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 7),
      add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x64 (4 * 8)]
    rw [← hN19, ← hN18, ← hN17, ← hN16, ← hN15, ← hN13, ← hN12, ← hN11, ← hN10, ← hN9, ← hN8, ← hN7, ← hN6, ← hN5, ← hN4, ← hN3, ← hN2, ← hN1]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have f2a0 : f2 a0 = 1 := by rw [← hf2]; simp +decide only [upd, ↓reduceIte, hz]
  have f2x0 : f2 x0 = 0 := t19.zero
  have rpw : wordsAt N19 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x88) 9 = pLimbs := by
    rw [wordsAt9, add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 1),
      add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 4),
      add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 7),
      add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x88 (4 * 8)]
    rw [← hN19, ← hN18, ← hN17, ← hN16, ← hN15, ← hN13, ← hN12, ← hN11, ← hN10, ← hN9, ← hN8, ← hN7, ← hN6, ← hN5, ← hN4, ← hN3, ← hN2, ← hN1]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
    rw [f2a0, f2x0, f2q _ (by decide), r19, hz]
    rfl
  have siA : sp0 + 0xFFFFFF30 + 0xFFFFFFCC = sp0 + 0xFFFFFED0 + BitVec.ofNat 32 0x2C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have inS : ∀ c, (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) = sp0 + 0xFFFFFED0 + BitVec.ofNat 32 (0x60 + c) := fun c => by
    rw [fm_frame, add_ofNat_assoc]
  have wrapC : ∀ c, c + 36 ≤ 0xD0 → (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c).toNat + 36 ≤ 2 ^ 32 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  have hsi : (P + 0x3FC).toNat % 2 = 0 := even_at P env.hP 0x3FC (by decide)
  have senv : SIEnv N19 (P + 0x3FC) (sp0 + 0xFFFFFF30) (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x40) (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x64)
      (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x88) :=
    ⟨hsi, codeX env.sicode env.sI F19, codeX env.bsub env.sIb F19, codeX env.sisave env.sIs F19,
      codeX env.sirestore env.sIr F19, hGa, aligned_add hGa (by decide), aligned_add hGa (by decide),
      aligned_add hGa (by decide), by omega,
      by rw [siA]; exact env.sI.sub (by decide), by rw [siA]; exact env.sIb.sub (by decide),
      by rw [siA]; exact env.sIs.sub (by decide), by rw [siA]; exact env.sIr.sub (by decide),
      by rw [inS]; exact env.sI.sub (by decide), by rw [inS]; exact env.sIr.sub (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      ⟨wrapC 0x40 (by decide), wrapC 0x64 (by decide), wrapC 0x88 (by decide)⟩, rpw⟩
  obtain ⟨e23, c23, pc23, mem23, regs23⟩ := t22.callRa cC fm_at_2b8 fm_at_2bc
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) hsi
  have r23 := PEnv.reg1 regs23 t22.zero
  rw [← mem23] at senv
  obtain ⟨e24, c24, pc24, sp24, regs24, val24, mask24, frame24⟩ := subInner_correct e23 senv pc23
    (by rw [r23 a0 (by decide), f3a0]) (by rw [r23 a1 (by decide), f3a1]) (by rw [r23 a2 (by decide), f3a2])
    (by rw [regs23]; simp +decide [upd]) (even_clear _ (even_at P env.hP 0x2C0 (by decide)))
    (by rw [r23 sp (by decide), f3q sp (by decide) (by decide) (by decide), f2sp])
  rw [mem23, lpw] at val24
  rw [mem23] at frame24
  have s24 : St e24.mem P e24 0x2C0 (reg e24) := ⟨by rw [pc24], rfl, fun _ => rfl⟩
  have F24 : ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → e24.mem x = M0 x := fun x hx =>
    (frame24 x (by rw [siA]; exact hx.sub (by decide)) (by rw [inS]; exact hx.sub (by decide))).trans (F19 x hx)
  have cc24 := codeX env.code env.sC F24
  have k24 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ t0 → q ≠ ra →
      reg e24 q = f2 q := fun q h0 h1 h2 h3 h4 h5 ht hr => by
    rw [regs24 q h0 h1 h2 h3 h4 h5 ht, r23 q hr, f3q q h0 h1 h2]
  have sp24' : reg e24 sp = sp0 + 0xFFFFFF30 := sp24
  have g18 : reg e24 (18 : Fin 32) = res := by
    rw [k24 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      f2q _ (by decide), r18]
  obtain ⟨g0, y0, h0, hy0, w0⟩ := s24.lwG cc24 fm_at_2c0 (off' := 0x2C2) (by decide)
    (by rw [sp24']; exact aligned_add hGa (k := 0x40) (by decide))
  rw [sp24'] at hy0
  obtain ⟨g1, y1, h1, hy1, w1⟩ := w0.lwG cc24 fm_at_2c2 (off' := 0x2C4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, sp24']; exact aligned_add hGa (k := 0x44) (by decide))
  simp +decide only [upd, ↓reduceIte, sp24'] at hy1
  obtain ⟨g2, y2, h2, hy2, w2⟩ := w1.lwG cc24 fm_at_2c4 (off' := 0x2C6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, sp24']; exact aligned_add hGa (k := 0x48) (by decide))
  simp +decide only [upd, ↓reduceIte, sp24'] at hy2
  obtain ⟨g3, y3, h3, hy3, w3⟩ := w2.lwG cc24 fm_at_2c6 (off' := 0x2C8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, sp24']; exact aligned_add hGa (k := 0x4C) (by decide))
  simp +decide only [upd, ↓reduceIte, sp24'] at hy3
  obtain ⟨g4, y4, h4, hy4, w4⟩ := w3.lwG cc24 fm_at_2c8 (off' := 0x2CA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, sp24']; exact aligned_add hGa (k := 0x50) (by decide))
  simp +decide only [upd, ↓reduceIte, sp24'] at hy4
  obtain ⟨g5, y5, h5, hy5, w5⟩ := w4.lwG cc24 fm_at_2ca (off' := 0x2CC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, sp24']; exact aligned_add hGa (k := 0x54) (by decide))
  simp +decide only [upd, ↓reduceIte, sp24'] at hy5
  obtain ⟨g6, y6, h6, hy6, w6⟩ := w5.lwG cc24 fm_at_2cc (off' := 0x2CE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, sp24']; exact aligned_add hGa (k := 0x58) (by decide))
  simp +decide only [upd, ↓reduceIte, sp24'] at hy6
  obtain ⟨g7, y7, h7, hy7, w7⟩ := w6.lwG cc24 fm_at_2ce (off' := 0x2D0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, sp24']; exact aligned_add hGa (k := 0x5C) (by decide))
  simp +decide only [upd, ↓reduceIte, sp24'] at hy7
  obtain ⟨f4, hf4⟩ : ∃ f, upd (upd (upd (upd (upd (upd (upd (upd (reg e24) a0 y0) a1 y1) a2 y2) a3 y3) a4 y4) a5 y5)
      (9 : Fin 32) y6) (8 : Fin 32) y7 = f := ⟨_, rfl⟩
  rw [hf4] at w7
  have f4y0 : f4 a0 = y0 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4y1 : f4 a1 = y1 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4y2 : f4 a2 = y2 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4y3 : f4 a3 = y3 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4y4 : f4 a4 = y4 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4y5 : f4 a5 = y5 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4y6 : f4 (9 : Fin 32) = y6 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4y7 : f4 (8 : Fin 32) = y7 := by rw [← hf4]; simp +decide only [upd, ↓reduceIte]
  have f4_18 : f4 (18 : Fin 32) = res := by rw [← hf4]; simp +decide only [upd, ↓reduceIte, g18]
  have f4q : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) →
      f4 q = reg e24 q := fun q h0 h1 h2 h3 h4 h5 h9 h8 => by
    rw [← hf4]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, s24.zero]
    · simp [upd, hq, h0, h1, h2, h3, h4, h5, h9, h8]
  obtain ⟨z0, j0, q0⟩ := w7.sw cc24 fm_at_2d0 (off' := 0x2D4) (by decide)
    (by rw [f4_18, add_lit_zero]; exact env.hres)
  rw [f4_18, f4y0, show (0 : Word) = BitVec.ofNat 32 0 from rfl] at q0
  have cR0 := CodeIn.store32 (v := y0) cc24 (env.sRC.sub (c := 0) (l := 4) (by decide))
  obtain ⟨z1, j1, q1⟩ := q0.alu cR0 fm_at_2d4 (off' := 0x2D6) (by decide)
  obtain ⟨f5, hf5⟩ : ∃ f, upd f4 a0 (aluEval .add (f4 x0) (f4 (18 : Fin 32))) = f := ⟨_, rfl⟩
  rw [hf5] at q1
  have f5a0 : f5 a0 = res := by
    have z := w7.zero
    rw [← hf5]; simp +decide only [upd, ↓reduceIte, f4_18, z]; exact BitVec.zero_add _
  have f5q : ∀ q, q ≠ a0 → f5 q = f4 q := fun q h => by
    rw [← hf5]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, w7.zero]
    · simp [upd, hq, h]
  obtain ⟨z2, j2, q2⟩ := q1.sw cR0 fm_at_2d6 (off' := 0x2D8) (by decide)
    (by rw [f5a0]; exact aligned_add env.hres (k := 0x4) (by decide))
  rw [f5a0, f5q _ (by decide), f4y1, show (0x4 : Word) = BitVec.ofNat 32 0x4 from rfl] at q2
  have cR1 := CodeIn.store32 (v := y1) cR0 (env.sRC.sub (c := 0x4) (l := 4) (by decide))
  obtain ⟨z3, j3, q3⟩ := q2.sw cR1 fm_at_2d8 (off' := 0x2DA) (by decide)
    (by rw [f5a0]; exact aligned_add env.hres (k := 0x8) (by decide))
  rw [f5a0, f5q _ (by decide), f4y2, show (0x8 : Word) = BitVec.ofNat 32 0x8 from rfl] at q3
  have cR2 := CodeIn.store32 (v := y2) cR1 (env.sRC.sub (c := 0x8) (l := 4) (by decide))
  obtain ⟨z4, j4, q4⟩ := q3.sw cR2 fm_at_2da (off' := 0x2DC) (by decide)
    (by rw [f5a0]; exact aligned_add env.hres (k := 0xC) (by decide))
  rw [f5a0, f5q _ (by decide), f4y3, show (0xC : Word) = BitVec.ofNat 32 0xC from rfl] at q4
  have cR3 := CodeIn.store32 (v := y3) cR2 (env.sRC.sub (c := 0xC) (l := 4) (by decide))
  obtain ⟨z5, j5, q5⟩ := q4.sw cR3 fm_at_2dc (off' := 0x2DE) (by decide)
    (by rw [f5a0]; exact aligned_add env.hres (k := 0x10) (by decide))
  rw [f5a0, f5q _ (by decide), f4y4, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl] at q5
  have cR4 := CodeIn.store32 (v := y4) cR3 (env.sRC.sub (c := 0x10) (l := 4) (by decide))
  obtain ⟨z6, j6, q6⟩ := q5.sw cR4 fm_at_2de (off' := 0x2E0) (by decide)
    (by rw [f5a0]; exact aligned_add env.hres (k := 0x14) (by decide))
  rw [f5a0, f5q _ (by decide), f4y5, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl] at q6
  have cR5 := CodeIn.store32 (v := y5) cR4 (env.sRC.sub (c := 0x14) (l := 4) (by decide))
  obtain ⟨z7, j7, q7⟩ := q6.sw cR5 fm_at_2e0 (off' := 0x2E2) (by decide)
    (by rw [f5a0]; exact aligned_add env.hres (k := 0x18) (by decide))
  rw [f5a0, f5q _ (by decide), f4y6, show (0x18 : Word) = BitVec.ofNat 32 0x18 from rfl] at q7
  have cR6 := CodeIn.store32 (v := y6) cR5 (env.sRC.sub (c := 0x18) (l := 4) (by decide))
  obtain ⟨z8, j8, q8⟩ := q7.sw cR6 fm_at_2e2 (off' := 0x2E4) (by decide)
    (by rw [f5a0]; exact aligned_add env.hres (k := 0x1C) (by decide))
  rw [f5a0, f5q _ (by decide), f4y7, show (0x1C : Word) = BitVec.ofNat 32 0x1C from rfl] at q8
  have cR7 := CodeIn.store32 (v := y7) cR6 (env.sRC.sub (c := 0x1C) (l := 4) (by decide))
  obtain ⟨Mr, hMr⟩ : ∃ M, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 e24.mem (res + BitVec.ofNat 32 0) y0) (res + BitVec.ofNat 32 0x4) y1) (res + BitVec.ofNat 32 0x8) y2) (res + BitVec.ofNat 32 0xC) y3) (res + BitVec.ofNat 32 0x10) y4) (res + BitVec.ofNat 32 0x14) y5) (res + BitVec.ofNat 32 0x18) y6) (res + BitVec.ofNat 32 0x1C) y7 = M := ⟨_, rfl⟩
  rw [hMr] at q8 cR7
  have resF : ∀ x, Sep res 32 x 1 → Mr x = e24.mem x := fun x hx => by
    rw [← hMr]
    simp only [memStore32_get_sep (hx.sub (c := 0x1C) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 0x18) (l := 4) (by decide)),
      memStore32_get_sep (hx.sub (c := 0x14) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 0x10) (l := 4) (by decide)),
      memStore32_get_sep (hx.sub (c := 0xC) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 0x8) (l := 4) (by decide)),
      memStore32_get_sep (hx.sub (c := 0x4) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide))]
  have slotByte : ∀ c, 0xAC ≤ c → c < 0xD0 → Mr (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) = N19 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) :=
    fun c h1 h2 => (resF _ (by rw [inS]; exact env.sRS.subR (c := 0x60 + c) (l := 1) (by omega))).trans
      (frame24 _ (by rw [siA, inS]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega))
        (by rw [inS, inS]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega)))
  have slotW : ∀ c, 0xAC ≤ c → c + 4 ≤ 0xD0 →
      memLoad32 Mr (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) = memLoad32 N19 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr (M := N19) (M' := Mr) fun j hj => by
      rw [add_ofNat_assoc]; exact slotByte _ (by omega) (by omega)
  have slotv : ∀ r o, (r, o) ∈ fmPs → memLoad32 Mr (sp0 + 0xFFFFFF30 + o) = v r := by
    intro r o h
    rw [← hsl r o h]
    simp only [fmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [slotW _ (by decide) (by decide)]
      rw [← hN19, ← hN18, ← hN17, ← hN16, ← hN15, ← hN13, ← hN12, ← hN11, ← hN10, ← hN9, ← hN8, ← hN7, ← hN6, ← hN5, ← hN4, ← hN3, ← hN2, ← hN1]
      simp (disch := decide) only [memLoad32_store32_off]
  have f5sp : f5 sp = sp0 + 0xFFFFFF30 := by
    rw [f5q _ (by decide), f4q _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), sp24']
  have cF : CodeIn Mr P fieldMulCode := cR7
  obtain ⟨b0, u0, l0, hu0, p0⟩ := q8.lwG cF fm_at_2e4 (off' := 0x2E6) (by decide)
    (by rw [f5sp]; exact aligned_add hGa (k := 0xCC) (by decide))
  rw [f5sp] at hu0
  have vu0 : u0 = v ra := by rw [← hu0]; exact slotv _ (BitVec.ofNat 32 0xCC) (by simp)
  obtain ⟨b1, u1, l1, hu1, p1⟩ := p0.lwG cF fm_at_2e6 (off' := 0x2E8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xC8) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu1
  have vu1 : u1 = v (8 : Fin 32) := by rw [← hu1]; exact slotv _ (BitVec.ofNat 32 0xC8) (by simp)
  obtain ⟨b2, u2, l2, hu2, p2⟩ := p1.lwG cF fm_at_2e8 (off' := 0x2EA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xC4) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu2
  have vu2 : u2 = v (9 : Fin 32) := by rw [← hu2]; exact slotv _ (BitVec.ofNat 32 0xC4) (by simp)
  obtain ⟨b3, u3, l3, hu3, p3⟩ := p2.lwG cF fm_at_2ea (off' := 0x2EC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xC0) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu3
  have vu3 : u3 = v (18 : Fin 32) := by rw [← hu3]; exact slotv _ (BitVec.ofNat 32 0xC0) (by simp)
  obtain ⟨b4, u4, l4, hu4, p4⟩ := p3.lwG cF fm_at_2ec (off' := 0x2EE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xBC) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu4
  have vu4 : u4 = v (19 : Fin 32) := by rw [← hu4]; exact slotv _ (BitVec.ofNat 32 0xBC) (by simp)
  obtain ⟨b5, u5, l5, hu5, p5⟩ := p4.lwG cF fm_at_2ee (off' := 0x2F0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xB8) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu5
  have vu5 : u5 = v (20 : Fin 32) := by rw [← hu5]; exact slotv _ (BitVec.ofNat 32 0xB8) (by simp)
  obtain ⟨b6, u6, l6, hu6, p6⟩ := p5.lwG cF fm_at_2f0 (off' := 0x2F2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xB4) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu6
  have vu6 : u6 = v (21 : Fin 32) := by rw [← hu6]; exact slotv _ (BitVec.ofNat 32 0xB4) (by simp)
  obtain ⟨b7, u7, l7, hu7, p7⟩ := p6.lwG cF fm_at_2f2 (off' := 0x2F4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xB0) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu7
  have vu7 : u7 = v (22 : Fin 32) := by rw [← hu7]; exact slotv _ (BitVec.ofNat 32 0xB0) (by simp)
  obtain ⟨b8, u8, l8, hu8, p8⟩ := p7.lwG cF fm_at_2f4 (off' := 0x2F6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, f5sp]; exact aligned_add hGa (k := 0xAC) (by decide))
  simp +decide only [upd, ↓reduceIte, f5sp] at hu8
  have vu8 : u8 = v (23 : Fin 32) := by rw [← hu8]; exact slotv _ (BitVec.ofNat 32 0xAC) (by simp)
  obtain ⟨b9, l9, p9⟩ := p8.aluImm cF fm_at_2f6 (off' := 0x2F8) (by decide)
  obtain ⟨b10, l10, pc10, mem10, regs10⟩ := p9.jalr cF fm_at_2f8
  have outw : wordsAt e24.mem (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x40) 8 = [y0, y1, y2, y3, y4, y5, y6, y7] := by
    unfold wordsAt
    simp only [List.range, List.range.loop, List.map]
    rw [add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 1), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 4), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF30) 0x40 (4 * 7)]
    rw [← hy0, ← hy1, ← hy2, ← hy3, ← hy4, ← hy5, ← hy6, ← hy7]
    rfl
  have resw : wordsAt Mr res 8 = [y0, y1, y2, y3, y4, y5, y6, y7] := by
    unfold wordsAt
    simp only [List.range, List.range.loop, List.map]
    rw [← hMr]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  refine ⟨b10, (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 (.cons x6 (.cons x7 (.cons x8 (.cons x9 (.cons x10 (.cons x11 (.cons x12 (.cons x13 (.cons x14 (.cons x15 (.cons x16 (.cons x17 (.cons x18 (.cons x19 (.cons x20 (.cons x21 (.cons x22 (c23.trans (c24.trans (.cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons j0 (.cons j1 (.cons j2 (.cons j3 (.cons j4 (.cons j5 (.cons j6 (.cons j7 (.cons j8 (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7 (.cons l8 (.cons l9 (.single l10)))))))))))))))))))))))))))))))))))))))))))))))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc10]; simp +decide only [upd, ↓reduceIte]; rw [vu0, add_lit_zero]
  · rw [outw] at val24; rw [mem10, resw]; exact val24
  · intro x hS hR; rw [mem10]; exact (resF x hR).trans (F24 x hS)
  · rw [regs10]; simp +decide only [upd, ↓reduceIte, aluEval, f5sp]
    rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · intro r o h
    rw [regs10]
    simp only [fmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp +decide only [upd, ↓reduceIte] <;>
    first | exact vu0 | exact vu1 | exact vu2 | exact vu3 | exact vu4 | exact vu5 | exact vu6 | exact vu7 | exact vu8
  · intro q hq
    have k := fun r (hr : fmKeep2 r = false) => bkeep_ne hq hr
    rw [regs10]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, k ra rfl, k sp rfl, k 8 rfl, k 9 rfl, k 18 rfl, k 19 rfl, k 20 rfl, k 21 rfl, k 22 rfl, k 23 rfl]
      rw [f5q q (k a0 rfl), f4q q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k 9 rfl) (k 8 rfl),
        k24 q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k t0 rfl) (k ra rfl), f2q q (k a0 rfl)]

theorem fm_regs : ∀ q : Fin 32, q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
    q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q = sp ∨
    q = a0 ∨ q = a1 ∨ q = a2 ∨ q = a3 ∨ q = a4 ∨ q = a5 ∨ q = a6 ∨ q = a7 ∨ q = t0 ∨ q = t1 ∨ q = (7 : Fin 32) ∨
    q = (28 : Fin 32) ∨ q = (29 : Fin 32) ∨ q = (30 : Fin 32) ∨ q = (31 : Fin 32) ∨
    (fmKeep2 q = true ∧ fmRedKeep q = true ∧ fmKeep q = true) := by decide

set_option exponentiation.threshold 600 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `FieldElement::multiply`**, called with the result at `res`
and the operands at `ap` and `bp`: the Montgomery product. The 8 words it
stores at `res`, times `2^256`, are the product of the operands modulo `p`,
and below `p` when that product is below `p · 2^256`, as it is when both
operands are below `p`. It returns with `sp` and every register but `a0`
through `a7` and `t0` through `t6` as they were, and changes no memory outside
the 0x130 bytes of stack below `sp` and the result. -/
theorem fieldMul_correct (m : Machine) {P sp0 res ap bp retAddr : Word}
    (env : FMEnv m.mem P sp0 res ap bp) (hpc : m.pc = P) (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      (limbVal (wordsAt m'.mem res 8) * 2 ^ 256) % p256 =
        (limbVal (wordsAt m.mem ap 8) * limbVal (wordsAt m.mem bp 8)) % p256 ∧
      (limbVal (wordsAt m.mem ap 8) * limbVal (wordsAt m.mem bp 8) < p256 * 2 ^ 256 →
        limbVal (wordsAt m'.mem res 8) < p256) ∧
      ∀ x, Sep (sp0 + 0xFFFFFED0) 0x130 x 1 → Sep res 32 x 1 → m'.mem x = m.mem x := by
  obtain ⟨n1, M1, c1, s1, hF1, hsl1, prod1, sp1, r18, keep1⟩ := fm_pro m env hpc ha0 ha1 ha2 hsp
  have cM1 : CodeIn M1 P fieldMulCode := fun i hi => by
    rw [hF1 _ (env.sC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  obtain ⟨n2, c2, s2, ⟨q, hq, hL⟩, r19, keep2⟩ :=
    fm_red s1 cM1 sp1 (aligned_add env.hsp (k := 0xFFFFFF30) (by decide))
  obtain ⟨n3, c3, pc3, val3, frame3, sp3, regs3, keep3⟩ := fm_epi (v := reg m) env s2 hF1 hsl1
    (by rw [keep2 _ rfl, sp1]) (by rw [keep2 _ rfl, r18]) r19
  have hA := limbVal_lt (wordsAt m.mem ap 8)
  have hB := limbVal_lt (wordsAt m.mem bp 8)
  rw [wordsAt_length] at hA hB
  have hAB : limbVal (wordsAt m.mem ap 8) * limbVal (wordsAt m.mem bp 8) < 2 ^ 512 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt hA hB
    rw [← Nat.pow_add] at h
    exact h
  rw [prod1] at hL
  obtain ⟨e1, e2⟩ := mont_out hAB hq hL
  refine ⟨n3, c1.trans (c2.trans c3), by rw [pc3, hra, hret], sp3, ?_, by rw [val3]; exact e1,
    fun h => by rw [val3]; exact e2 h, fun x hS hR => frame3 x hS hR⟩
  intro r q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3 qt4 qt5 qt6
  rcases fm_regs r with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | ⟨k3, k2, k1⟩
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xCC) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xC8) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xC4) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xC0) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xBC) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xB8) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xB4) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xB0) (by simp)
  · subst h; exact regs3 _ (BitVec.ofNat 32 0xAC) (by simp)
  · subst h; rw [sp3, hsp]
  · exact absurd h q0
  · exact absurd h q1
  · exact absurd h q2
  · exact absurd h q3
  · exact absurd h q4
  · exact absurd h q5
  · exact absurd h q6
  · exact absurd h q7
  · exact absurd h qt0
  · exact absurd h qt1
  · exact absurd h qt2
  · exact absurd h qt3
  · exact absurd h qt4
  · exact absurd h qt5
  · exact absurd h qt6
  · rw [keep3 r k3, keep2 r k2, keep1 r k1]

end C3.RV32
