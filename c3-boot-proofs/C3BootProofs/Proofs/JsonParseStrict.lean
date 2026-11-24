import C3BootProofs.Proofs.JsonParseKeys

/-!
# `json::parse`: the strict key check

In strict mode, `parse` walks a closed object's members with the cursor at
`F + 0x90`. For each key, it copies that cursor to `F + 0x9C` and walks the
rest of the object, and `slice_ne` clears `s1` when a later key equals it
(`keysUnique`). A cleared `s1` fails the parse with error `0x20`.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem pa_low {s F : Word} (hF : s + BitVec.ofNat 32 164 = F) : F + 0xFFFFFFEC = s + BitVec.ofNat 32 144 := by
  rw [← hF, BitVec.add_assoc]; rfl

theorem pa_and (u : Bool) (e : Prop) [d : Decidable e] :
    aluEval .and (modeW u) (if e then 0 else 1) = modeW (u && decide (¬e)) := by
  cases hd : decide e with
  | true =>
    have h := of_decide_eq_true hd
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), decide_eq_false (fun h' => h' h)]; cases u <;> rfl
  | false =>
    have h := of_decide_eq_false hd
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), decide_eq_true h]; cases u <;> rfl

theorem pa_and1 (u : Bool) : aluEval .and (modeW u) (BitVec.ofNat 32 1) = modeW u := by cases u <;> rfl

theorem pa_ad_eq (b : Word) : b + 0xFFFFFFEA + 0xFFFFF372 = b + 0xFFFFF372 + 0xFFFFFFEA := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem pa_ad_es (b : Word) : b + 0xFFFFFFEA + 0xFFFFDF1C = b + 0xFFFFF372 + 0xFFFFF616 + 0xFFFFF57E := by
  simp only [BitVec.add_assoc]; rfl

theorem pa_ad_mm (b : Word) : b + 0xFFFFFFEA + 0xB2DA = b + 0xFFFFF372 + 0xFFFFF616 + 0xC93C := by
  simp only [BitVec.add_assoc]; rfl

theorem pa_st {M : Word → BitVec 8} {F v : Word} {d e : Nat} (hde : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d + 4 ≤ 2 ^ 32)
    (he : e + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M (F + BitVec.ofNat 32 d) v) (F + BitVec.ofNat 32 e) = memLoad32 M (F + BitVec.ofNat 32 e) :=
  memLoad32_store32_sep (sep_offsets F hde hd he)

section
variable {M0 Mp : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 : Fin 32 → Word}
  {stk : List (Bool × Nat)}

/-- The strict check's inner walk at `0x20E`, by fuel. `s1` holds whether
the key at `s0` and `s2`, the `kl` bytes at `kp` of the object `o`, differs
from each key the cursor at `F + 0x9C` has passed. `hend` continues at
`0x236` when the walk reaches the closing brace. -/
theorem pa_uniq (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (hsl : st + l ≤ n) {o : Bytes}
    (ho : slice (memBytes M0 p n) st l = o) {kp kl a : Nat} (hkk : kp + kl ≤ l) {w8 : Word} {f0 : Fin 32 → Word}
    (hf0 : f0 0 = 0) {K : Except Nat Bool → Except Nat (Nat × Nat)} (hK : ∀ e, K (.error e) = .error e)
    (hend : ∀ (u : Bool) (M' : Word → BitVec 8) (g : Fin 32 → Word), FInv M0 Mp s F n stk M' →
      memLoad32 M' (F + 0x90) = p + BitVec.ofNat 32 st → memLoad32 M' (F + 0x94) = BitVec.ofNat 32 l →
      memLoad32 M' (F + 0x98) = BitVec.ofNat 32 a → memLoad32 M' (F + 8) = w8 → memLoad32 M' (F + 0xC) = out →
      PRegs g g0 F p n false → g 9 = modeW u → (∀ x, x ∉ kE → g x = f0 x) →
      WP jsonParseCode base (PPost M0 s p out g0 (K (.ok u))) M' 0x236 g) :
    ∀ k (u : Bool) pos (M : Word → BitVec 8) (f : Fin 32 → Word), l - pos < k → pos < 2 ^ 32 →
      FInv M0 Mp s F n stk M → memLoad32 M (F + 0x90) = p + BitVec.ofNat 32 st →
      memLoad32 M (F + 0x94) = BitVec.ofNat 32 l → memLoad32 M (F + 0x98) = BitVec.ofNat 32 a →
      memLoad32 M (F + 0x9C) = p + BitVec.ofNat 32 st → memLoad32 M (F + 0xA0) = BitVec.ofNat 32 l →
      memLoad32 M (F + 0xA4) = BitVec.ofNat 32 pos → memLoad32 M (F + 8) = w8 → memLoad32 M (F + 0xC) = out →
      PRegs f g0 F p n false → f 8 = p + BitVec.ofNat 32 st + BitVec.ofNat 32 kp → f 18 = BitVec.ofNat 32 kl →
      f 9 = modeW u → (∀ x, x ∉ kE → f x = f0 x) →
      WP jsonParseCode base (PPost M0 s p out g0 (K (keysUnique o (slice o kp kl) k u pos))) M 0x20E f := by
  have hlen : o.length = l := by rw [← ho]; unfold slice; rw [memBytes_slice hsl, memBytes_length]
  obtain ⟨hq0, hqn⟩ := E.qnz hsl
  have hn := E.hn
  have kb : ∀ {M : Word → BitVec 8} {a b : Nat}, a + b ≤ l → Out M0 M s 404 →
      memBytes M (p + BitVec.ofNat 32 st + BitVec.ofNat 32 a) b = slice o a b := by
    intro M a b hab hO
    rw [← ho]; unfold slice
    rw [memBytes_slice hsl, memBytes_slice hab, hO.bytes ((E.sepq hsl).subR hab)]
  have hlo : ∀ {a : Word} {k : Nat}, Sep s 404 a k → Sep (F + 0xFFFFFFEC) 0x14 a k := fun h => by
    rw [pa_low E.hF]; exact h.sub (by decide)
  intro k
  induction k with
  | zero => intro _ _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
  intro u pos M f hk hpos hFI hm90 hm94 hm98 hm9C hmA0 hmA4 hm8 hmC hR hs0 hs2 hs1 hkp
  have hfr := hR.fr
  refine WP.zero fun hz => ?_
  refine WP.aluImm pa_at_20e ?_; wn
  refine WP.aluImm pa_at_210 ?_; wn
  refine pa_nm E (off := 0x212) (cc := 0x9C) (st := st) (l := l) (pos := pos) (c := false) pa_at_212 pa_at_216
    (by simp only [BitVec.add_assoc]; rfl) (by decide) (Or.inr rfl) hFI (by pregs hR, E.z0)
    (by (try rsimp); rw [hR.sp, ev_add]) (by (try rsimp); rw [hR.sp, ev_add]; try rfl) hm9C
    (by rw [BitVec.add_assoc]; exact hmA0) (by rw [BitVec.add_assoc]; exact hmA4) hsl hpos
    fun m2 hFI2 hMR hkeep => ?_
  rw [ho] at hMR
  obtain ⟨M1, hOa, hM⟩ := hMR
  generalize m2.mem = M2 at hFI2 hM hkeep
  have hC2 : memLoad32 M2 (F + 0xC) = out := (hkeep 0xC (Or.inl (by decide))).trans hmC
  have h82 : memLoad32 M2 (F + 8) = w8 := (hkeep 8 (Or.inl (by decide))).trans hm8
  have h902 : memLoad32 M2 (F + 0x90) = p + BitVec.ofNat 32 st :=
    (hkeep 0x90 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm90
  have h942 : memLoad32 M2 (F + 0x94) = BitVec.ofNat 32 l :=
    (hkeep 0x94 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm94
  have h982 : memLoad32 M2 (F + 0x98) = BitVec.ofNat 32 a :=
    (hkeep 0x98 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm98
  have h9C2 : memLoad32 M2 (F + 0x9C) = p + BitVec.ofNat 32 st :=
    (hkeep 0x9C (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm9C
  have hA02 : memLoad32 M2 (F + 0xA0) = BitVec.ofNat 32 l :=
    (hkeep 0xA0 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hmA0
  have hc2 : ParseCode M2 base := E.code.out hFI2.1 E.sep
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pa_at_21a ?_; wn
  generalize hnm : nextMember o pos = r at hM
  rcases r with _ | _ | ⟨kp', kl', vp, vl, a'⟩
  · obtain ⟨-, t1, t2⟩ := hM
    refine WP.branch pa_at_21e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.lbu pa_at_2bc ?_; wn
    have hk' : K (keysUnique o (slice o kp kl) (k + 1) u pos) = .error 0x20 := by
      simp only [keysUnique, hnm, hK]
    rw [hk']
    exact pa_2c0 E (by (try rsimp); exact hR.sp) hC2
      (by (try rsimp); rw [hR.sp, show F + 0xA9 = F + 0xA8 + 1 by rw [BitVec.add_assoc]; rfl, t2]; rfl)
      hFI2.1 hFI2.2.1 (by keepz E.z0)
  · obtain ⟨-, t1, t2⟩ := hM
    refine WP.branch pa_at_21e (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw pa_at_220 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xAC) (by decide)) ?_; wn
    refine WP.branch pa_at_222 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb)
      rw [hR.sp, show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl, t2] at eb
      exact absurd eb (by decide)
    have hk' : keysUnique o (slice o kp kl) (k + 1) u pos = .ok u := by simp only [keysUnique, hnm]
    rw [hk']
    exact hend u M2 _ hFI2 h902 h942 h982 h82 hC2 (by pregs hR, E.z0) (by (try rsimp); exact hs1)
      (by keepz hf0)
  obtain ⟨-, t1, tkq, tkl, -, -, ta⟩ := hM
  obtain ⟨hpl, hpa, hkk', han, -⟩ := nextMember_lt hnm
  rw [hlen] at hpl hkk' han
  have tkq' : memLoad32 M2 (F + 0xAC) = p + BitVec.ofNat 32 st + BitVec.ofNat 32 kp' := by
    rw [show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl]; exact tkq
  have tkl' : memLoad32 M2 (F + 0xB0) = BitVec.ofNat 32 kl' := by
    rw [show F + 0xB0 = F + 0xA8 + 8 by rw [BitVec.add_assoc]; rfl]; exact tkl
  have ta' : memLoad32 M2 (F + 0xA4) = BitVec.ofNat 32 a' := by
    rw [show F + 0xA4 = F + BitVec.ofNat 32 0x9C + 8 by rw [BitVec.add_assoc]; rfl]; exact ta
  refine WP.branch pa_at_21e (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_220 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xAC) (by decide)) ?_; wn
  refine WP.branch pa_at_222 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb)
    rw [hR.sp, tkq', nx_q0 hq0 (n := l + 1) (by omega) (by omega)] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_224 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xB0) (by decide)) ?_; wn
  refine WP.alu pa_at_226 ?_; wn
  refine WP.alu pa_at_228 ?_; wn
  refine WP.callSliceNe (tb := base + 0xFFFFFFEA) (p := p + BitVec.ofNat 32 st + BitVec.ofNat 32 kp')
    (q := p + BitVec.ofNat 32 st + BitVec.ofNat 32 kp) (pl := kl') (ql := kl) pa_at_22a pa_at_22e
    (by simp only [BitVec.add_assoc]; rfl) (even_at base E.hb _ (by decide)) (by decide) hc2.ne
    (by rw [pa_ad_eq]; exact hc2.get.eq) (by rw [pa_ad_es]; exact hc2.get.ri.es)
    (by rw [pa_ad_mm]; exact hc2.get.ri.mc) (by (try rsimp); rw [hR.sp]; exact tkq')
    (by (try rsimp); rw [hR.sp]; exact tkl') (by (try rsimp); (try simp only [ev0]); exact hs0)
    (by (try rsimp); (try simp only [ev0]); exact hs2) (by omega) (by omega)
    (by (try rsimp); rw [hR.sp]; exact E.halF) (by (try rsimp); rw [hR.sp]; exact hlo E.sep.ne)
    (by (try rsimp); rw [hR.sp, pa_ad_eq]; exact hlo E.sep.get.eq)
    (by (try rsimp); rw [hR.sp, pa_ad_es]; exact hlo E.sep.get.ri.es)
    (by (try rsimp); rw [hR.sp, pa_ad_mm]; exact hlo E.sep.get.ri.mc)
    (by (try rsimp); rw [hR.sp]; exact hlo ((E.sepq hsl).subR hkk'))
    (by (try rsimp); rw [hR.sp]; exact hlo ((E.sepq hsl).subR hkk))
    (by (try rsimp); rw [hR.sp]; exact hlo E.sep.parse) fun m3 ha0 hO => ?_
  rw [kb hkk' hFI2.1, kb hkk hFI2.1] at ha0
  have hO' : Out M2 m3.mem (s + BitVec.ofNat 32 144) 20 := by
    (try rsimp at hO); rw [hR.sp, pa_low E.hF] at hO; exact hO
  have hk3 : ∀ d, d + 4 ≤ 0x100 → memLoad32 m3.mem (F + BitVec.ofNat 32 d) = memLoad32 M2 (F + BitVec.ofNat 32 d) :=
    fun d hd => hO'.load32 ((E.below (d := d) (w := 4) (by omega)).symm.sub (by decide))
  have hFI3 := hFI2.out E.hF hO' (Or.inl (by decide))
  refine WP.alu pa_at_232 ?_; wn
  refine WP.jal pa_at_234 (by decide) ?_; wn
  have hk' : keysUnique o (slice o kp kl) (k + 1) u pos =
      keysUnique o (slice o kp kl) k (u && decide (slice o kp' kl' ≠ slice o kp kl)) a' := by
    simp only [keysUnique, hnm]
  rw [hk']
  exact ih _ a' m3.mem _ (by omega) (by omega) hFI3 ((hk3 0x90 (by decide)).trans h902)
    ((hk3 0x94 (by decide)).trans h942) ((hk3 0x98 (by decide)).trans h982) ((hk3 0x9C (by decide)).trans h9C2)
    ((hk3 0xA0 (by decide)).trans hA02) ((hk3 0xA4 (by decide)).trans ta') ((hk3 8 (by decide)).trans h82)
    ((hk3 0xC (by decide)).trans hC2) (by pregs hR, E.z0) (by (try rsimp); exact hs0) (by (try rsimp); exact hs2)
    (by (try rsimp); rw [ha0, hs1, pa_and]) (by keepz hf0)

/-- The strict check's copy of the cursor at `F + 0x90` to `F + 0x9C`. -/
theorem pa_cp (E : PaEnv M0 base s p out n g0 Mp F) {M : Word → BitVec 8} (hFI : FInv M0 Mp s F n stk M)
    (v1 v2 v3 : Word) :
    FInv M0 Mp s F n stk (memStore32 (memStore32 (memStore32 M (F + 0x9C) v1) (F + 0xA0) v2) (F + 0xA4) v3) ∧
    (∀ d, d + 4 ≤ 0x9C ∨ 0xA8 ≤ d ∧ d + 4 ≤ 0x100 →
      memLoad32 (memStore32 (memStore32 (memStore32 M (F + 0x9C) v1) (F + 0xA0) v2) (F + 0xA4) v3)
        (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d)) ∧
    memLoad32 (memStore32 (memStore32 (memStore32 M (F + 0x9C) v1) (F + 0xA0) v2) (F + 0xA4) v3) (F + 0x9C) = v1 ∧
    memLoad32 (memStore32 (memStore32 (memStore32 M (F + 0x9C) v1) (F + 0xA0) v2) (F + 0xA4) v3) (F + 0xA0) = v2 ∧
    memLoad32 (memStore32 (memStore32 (memStore32 M (F + 0x9C) v1) (F + 0xA0) v2) (F + 0xA4) v3) (F + 0xA4) = v3 := by
  refine ⟨((hFI.outF E.hF (d := 0x9C) (out_store32 _ _ _) (Or.inr ⟨by decide, by decide⟩)).outF E.hF (d := 0xA0)
    (out_store32 _ _ _) (Or.inr ⟨by decide, by decide⟩)).outF E.hF (d := 0xA4) (out_store32 _ _ _)
    (Or.inr ⟨by decide, by decide⟩), fun d hd => ?_, ?_, ?_, ?_⟩
  · have hs : ∀ e, 0x9C ≤ e → e + 4 ≤ 0xA8 → d + 4 ≤ e ∨ e + 4 ≤ d := fun e h1 h2 => by
      rcases hd with h | ⟨h, -⟩
      exact Or.inl (by omega)
      exact Or.inr (by omega)
    have h1 := hs 0xA4 (by decide) (by decide)
    have h2 := hs 0xA0 (by decide) (by decide)
    have h3 := hs 0x9C (by decide) (by decide)
    have hd4 : d + 4 ≤ 2 ^ 32 := by omega
    exact ((pa_st (d := 0xA4) (Or.symm h1) (by decide) hd4).trans (pa_st (d := 0xA0) (Or.symm h2) (by decide) hd4)).trans
      (pa_st (d := 0x9C) (Or.symm h3) (by decide) hd4)
  · exact ((pa_st (d := 0xA4) (e := 0x9C) (Or.inr (by decide)) (by decide) (by decide)).trans
      (pa_st (d := 0xA0) (e := 0x9C) (Or.inr (by decide)) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)
  · exact (pa_st (d := 0xA4) (e := 0xA0) (Or.inr (by decide)) (by decide) (by decide)).trans
      (memLoad32_store32_same _ _ _)
  · exact memLoad32_store32_same _ _ _

/-- The strict key check at `0x1BC`, by fuel. The cursor at `F + 0x90`
walks the object `o`, the `l` bytes at `st`. `hok` continues at `0x252`
once no key repeats. -/
theorem pa_strict (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (hsl : st + l ≤ n) {o : Bytes}
    (ho : slice (memBytes M0 p n) st l = o) {R : Except Nat (Nat × Nat)} {w8 : Word} {f0 : Fin 32 → Word}
    (hf0 : f0 0 = 0)
    (hok : ∀ (M' : Word → BitVec 8) (g : Fin 32 → Word), FInv M0 Mp s F n stk M' → memLoad32 M' (F + 8) = w8 →
      memLoad32 M' (F + 0xC) = out → PRegs g g0 F p n false → (∀ x, x ∉ kE → g x = f0 x) →
      WP jsonParseCode base (PPost M0 s p out g0 R) M' 0x252 g) :
    ∀ k pos (M : Word → BitVec 8) (f : Fin 32 → Word), l - pos < k → pos < 2 ^ 32 →
      FInv M0 Mp s F n stk M → memLoad32 M (F + 0x90) = p + BitVec.ofNat 32 st →
      memLoad32 M (F + 0x94) = BitVec.ofNat 32 l → memLoad32 M (F + 0x98) = BitVec.ofNat 32 pos →
      memLoad32 M (F + 8) = w8 → memLoad32 M (F + 0xC) = out → PRegs f g0 F p n false →
      (∀ x, x ∉ kE → f x = f0 x) →
      WP jsonParseCode base (PPost M0 s p out g0 (keysThen (keysStrict o k pos) R)) M 0x1BC f := by
  have hlen : o.length = l := by rw [← ho]; unfold slice; rw [memBytes_slice hsl, memBytes_length]
  obtain ⟨hq0, hqn⟩ := E.qnz hsl
  have hn := E.hn
  intro k
  induction k with
  | zero => intro _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
  intro pos M f hk hpos hFI hm90 hm94 hm98 hm8 hmC hR hkp
  have hfr := hR.fr
  refine WP.zero fun hz => ?_
  refine WP.alu pa_at_1bc ?_; wn
  refine WP.alu pa_at_1be ?_; wn
  refine WP.aluImm pa_at_1c0 ?_; wn
  refine WP.aluImm pa_at_1c2 ?_; wn
  refine pa_nm E (off := 0x1C4) (cc := 0x90) (st := st) (l := l) (pos := pos) (c := false) pa_at_1c4 pa_at_1c8
    (by simp only [BitVec.add_assoc]; rfl) (by decide) (Or.inl rfl) hFI (by pregs hR, E.z0)
    (by (try rsimp); rw [hR.sp, ev_add]) (by (try rsimp); rw [hR.sp, ev_add]; try rfl) hm90
    (by rw [BitVec.add_assoc]; exact hm94) (by rw [BitVec.add_assoc]; exact hm98) hsl hpos
    fun m2 hFI2 hMR hkeep => ?_
  rw [ho] at hMR
  obtain ⟨M1, hOa, hM⟩ := hMR
  generalize m2.mem = M2 at hFI2 hM hkeep
  have hC2 : memLoad32 M2 (F + 0xC) = out := (hkeep 0xC (Or.inl (by decide))).trans hmC
  have h82 : memLoad32 M2 (F + 8) = w8 := (hkeep 8 (Or.inl (by decide))).trans hm8
  have h902 : memLoad32 M2 (F + 0x90) = p + BitVec.ofNat 32 st :=
    (hkeep 0x90 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm90
  have h942 : memLoad32 M2 (F + 0x94) = BitVec.ofNat 32 l :=
    (hkeep 0x94 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm94
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pa_at_1cc ?_; wn
  generalize hnm : nextMember o pos = r at hM
  rcases r with _ | _ | ⟨kp, kl, vp, vl, a⟩
  · obtain ⟨-, t1, t2⟩ := hM
    refine WP.branch pa_at_1d0 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.lbu pa_at_2bc ?_; wn
    have hk' : keysThen (keysStrict o (k + 1) pos) R = .error 0x20 := by
      simp only [keysStrict, hnm, keysThen]
    rw [hk']
    exact pa_2c0 E (by (try rsimp); exact hR.sp) hC2
      (by (try rsimp); rw [hR.sp, show F + 0xA9 = F + 0xA8 + 1 by rw [BitVec.add_assoc]; rfl, t2]; rfl)
      hFI2.1 hFI2.2.1 (by keepz E.z0)
  · obtain ⟨-, t1, t2⟩ := hM
    refine WP.branch pa_at_1d0 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw pa_at_1d2 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xAC) (by decide)) ?_; wn
    refine WP.branch pa_at_1d4 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb)
      rw [hR.sp, show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl, t2] at eb
      exact absurd eb (by decide)
    have hk' : keysThen (keysStrict o (k + 1) pos) R = R := by
      simp only [keysStrict, hnm, keysThen]
    rw [hk']
    exact hok M2 _ hFI2 h82 hC2 (by pregs hR, E.z0) (by keepz hf0)
  obtain ⟨-, t1, tkq, tkl, -, -, ta⟩ := hM
  obtain ⟨hpl, hpa, hkk, han, -⟩ := nextMember_lt hnm
  rw [hlen] at hpl hkk han
  have tkq' : memLoad32 M2 (F + 0xAC) = p + BitVec.ofNat 32 st + BitVec.ofNat 32 kp := by
    rw [show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl]; exact tkq
  have tkl' : memLoad32 M2 (F + 0xB0) = BitVec.ofNat 32 kl := by
    rw [show F + 0xB0 = F + 0xA8 + 8 by rw [BitVec.add_assoc]; rfl]; exact tkl
  have ta' : memLoad32 M2 (F + 0x98) = BitVec.ofNat 32 a := by
    rw [show F + 0x98 = F + BitVec.ofNat 32 0x90 + 8 by rw [BitVec.add_assoc]; rfl]; exact ta
  refine WP.branch pa_at_1d0 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_1d2 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xAC) (by decide)) ?_; wn
  refine WP.branch pa_at_1d4 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb)
    rw [hR.sp, tkq', nx_q0 hq0 (n := l + 1) (by omega) (by omega)] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_1d6 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xB0) (by decide)) ?_; wn
  refine WP.branch pa_at_1d8 (fun _ => ?_) (fun eb => ?_) <;> wn
  rotate_left
  · exfalso; (try rsimp at eb); rw [hR.s3] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_200 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0x90) (by decide)) ?_; wn
  refine WP.lw pa_at_202 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0x94) (by decide)) ?_; wn
  refine WP.lw pa_at_204 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0x98) (by decide)) ?_; wn
  refine WP.sw pa_at_206 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0x9C) (by decide))
    (by (try rsimp); rw [hR.sp]; exact E.sepF E.sep.parse (d := 0x9C) (w := 4) (by decide)) ?_; wn
  refine WP.sw pa_at_208 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xA0) (by decide))
    (by (try rsimp); rw [hR.sp]; exact E.sepF E.sep.parse (d := 0xA0) (w := 4) (by decide)) ?_; wn
  refine WP.sw pa_at_20a (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xA4) (by decide))
    (by (try rsimp); rw [hR.sp]; exact E.sepF E.sep.parse (d := 0xA4) (w := 4) (by decide)) ?_; wn
  refine WP.aluImm pa_at_20c ?_; wn
  have hk' : keysStrict o (k + 1) pos = (match keysUnique o (slice o kp kl) (l + 1) true a with
      | .error e => .error e
      | .ok u => if u then keysStrict o k a else .error 0x20) := by
    simp only [keysStrict, hnm, hlen]; rfl
  rw [hk', hR.sp]
  obtain ⟨hFI3, hk3, h9C3, hA03, hA43⟩ := pa_cp E hFI2 (memLoad32 M2 (F + 0x90)) (memLoad32 M2 (F + 0x94))
    (memLoad32 M2 (F + 0x98))
  refine pa_uniq E hsl ho hkk hf0 (a := a) (w8 := w8) (stk := stk)
    (K := fun r => keysThen (match r with
      | .error e => .error e
      | .ok u => if u then keysStrict o k a else .error 0x20) R) (fun _ => rfl) ?_ (l + 1) true a _ _
    (by omega) (by omega) hFI3 ((hk3 0x90 (Or.inl (by decide))).trans h902)
    ((hk3 0x94 (Or.inl (by decide))).trans h942) ((hk3 0x98 (Or.inl (by decide))).trans ta')
    (h9C3.trans h902) (hA03.trans h942) (hA43.trans ta') ((hk3 8 (Or.inl (by decide))).trans h82)
    ((hk3 0xC (Or.inl (by decide))).trans hC2) (by pregs hR, E.z0)
    (by (try rsimp); rw [tkq']) (by (try rsimp); rw [tkl']) (by (try rsimp); (try simp only [ev0]); try rfl)
    (by keepz hf0)
  intro u M' g hFI' hm90' hm94' hm98' hm8' hmC' hR' hs1 hkp'
  have hfr' := hR'.fr
  refine WP.zero fun hz' => ?_
  refine WP.aluImm pa_at_236 ?_; wn
  cases u
  · refine WP.branch pa_at_238 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hs1] at eb; exact absurd eb (by decide)
    refine WP.jal pa_at_23a (by decide) ?_; wn
    refine WP.aluImm pa_at_328 ?_; wn
    refine WP.jal pa_at_32c (by decide) ?_; wn
    exact pa_2c0 E (by (try rsimp); exact hR'.sp) hmC' (by (try rsimp); (try simp only [ev0]); try decide)
      hFI'.1 hFI'.2.1 (by keepz E.z0)
  · refine WP.branch pa_at_238 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hs1] at eb; exact absurd eb (by decide)
    exact ih a M' _ (by omega) (by omega) hFI' hm90' hm94' hm98' hm8' hmC' (by pregs hR', E.z0) (by keepz hf0)

end

end C3.RV32
