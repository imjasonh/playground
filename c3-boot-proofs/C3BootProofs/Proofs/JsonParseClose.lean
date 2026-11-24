import C3BootProofs.Proofs.JsonParseStrict

/-!
# `json::parse`: closing an object

At a closing `}`, `parse` reopens the object's bytes with `members`, copies
the cursor to `F + 0x90`, and runs the key check of its mode (`checkKeys`).
-/

namespace C3.RV32

open C3.Image C3.Json

theorem pc_rb : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFA3) 0 = (b.toNat == 93) := by decide

theorem pc_cb : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFF83) 0 = !(b.toNat == 125) := by decide

theorem pc_cm : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFD4) 0 = !(b.toNat == 44) := by decide

theorem ck_none {c : Bool} {q : Word} {o : Bytes} (h : curOpen 123 q o = none) : checkKeys c o = .error 0x21 := by
  unfold checkKeys
  refine ite_eq_left_of_eq_true _ _ (eq_true ?_)
  unfold curOpen at h
  split at h
  · exact Or.inl ‹_›
  · split at h
    · exact Or.inr ‹_›
    · nomatch h

theorem ck_some {q q' : Word} {o : Bytes} {l k : Nat} (h : curOpen 123 q o = some (q', l, k)) :
    q' = q ∧ l = o.length ∧ k = skipWs o 1 ∧ ¬(o.length = 0 ∨ o.getD 0 0 ≠ 123) := by
  unfold curOpen at h
  split at h
  · nomatch h
  · rename_i h1
    split at h
    · nomatch h
    · rename_i h2
      cases h
      exact ⟨rfl, rfl, rfl, fun h' => h'.elim h1 h2⟩

section
variable {M0 Mp : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 : Fin 32 → Word}
  {stk : List (Bool × Nat)}

theorem pa_lowkeep (E : PaEnv M0 base s p out n g0 Mp F) {M M' : Word → BitVec 8}
    (hO : Out M M' (s + BitVec.ofNat 32 148) 16) {d : Nat} (hd : 164 + d + 4 ≤ 2 ^ 32) :
    memLoad32 M' (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) :=
  (hO.widen (k := 164) (by decide)).load32 (E.below hd).symm

theorem pa_fkeep {M M' : Word → BitVec 8} {a k d : Nat} (hO : Out M M' (F + BitVec.ofNat 32 a) k)
    (h : a + k ≤ d ∨ d + 4 ≤ a) (ha : a + k ≤ 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) :
    memLoad32 M' (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) :=
  hO.load32 (sep_offsets F h ha hd)

/-- The key check at `0x1BC` from the start of the object `o`, the `l`
bytes at `st`, once `o` opens with `{`. `hok` continues at `0x252`. -/
theorem pa_keys (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (hsl : st + l ≤ n) {o : Bytes}
    (ho : slice (memBytes M0 p n) st l = o) (hl0 : ¬(o.length = 0 ∨ o.getD 0 0 ≠ 123)) {c : Bool}
    {R : Except Nat (Nat × Nat)} {w8 : Word} {f f1 : Fin 32 → Word} {M : Word → BitVec 8}
    (hok : ∀ (M' : Word → BitVec 8) (g : Fin 32 → Word), FInv M0 Mp s F n stk M' → memLoad32 M' (F + 8) = w8 →
      memLoad32 M' (F + 0xC) = out → PRegs g g0 F p n c → (∀ x, x ∉ kE → g x = f1 x) →
      WP jsonParseCode base (PPost M0 s p out g0 R) M' 0x252 g)
    (hFI : FInv M0 Mp s F n stk M) (h90 : memLoad32 M (F + 0x90) = p + BitVec.ofNat 32 st)
    (h94 : memLoad32 M (F + 0x94) = BitVec.ofNat 32 l)
    (h98 : memLoad32 M (F + 0x98) = BitVec.ofNat 32 (skipWs o 1))
    (h8 : memLoad32 M (F + 8) = w8) (hC : memLoad32 M (F + 0xC) = out) (hR : PRegs f g0 F p n c)
    (hs0 : f 8 = 0) (hff : ∀ x, x ∉ kE → f x = f1 x) :
    WP jsonParseCode base (PPost M0 s p out g0 (keysThen (checkKeys c o) R)) M 0x1BC f := by
  have hlen : o.length = l := by rw [← ho]; unfold slice; rw [memBytes_slice hsl, memBytes_length]
  have hsk := skipWs_le o 1
  have hf1 : f1 0 = 0 := by rw [← hff 0 (by decide), hR.fr 0 (by decide), E.z0]
  have hn := E.hn
  unfold checkKeys
  rw [ite_eq_right_of_eq_false _ _ (eq_false hl0)]
  cases c
  · exact pa_strict E hsl ho hf1 hok (o.length + 1) (skipWs o 1) M f (by omega) (by omega) hFI h90 h94 h98 h8 hC
      hR hff
  · exact pa_canon E hsl ho hf1 hok (o.length + 1) none (skipWs o 1) M f (by omega) (by omega) hs0
      (fun _ _ h => nomatch h) hFI h90 h94 h98 h8 hC hR hff

/-- A closing `}` at `0x18C`, with the object's start `st` in `a1` and its
length `l` in `a2`. `hok` continues at `0x252` once the keys pass. -/
theorem pa_obj (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (hsl : st + l ≤ n) {c : Bool}
    {R : Except Nat (Nat × Nat)} {f : Fin 32 → Word} {M : Word → BitVec 8}
    (hok : ∀ (M' : Word → BitVec 8) (g : Fin 32 → Word), FInv M0 Mp s F n stk M' →
      memLoad32 M' (F + 8) = f 26 → memLoad32 M' (F + 0xC) = out → PRegs g g0 F p n c →
      (∀ x, x ∉ kE → g x = f x) → WP jsonParseCode base (PPost M0 s p out g0 R) M' 0x252 g)
    (hFI : FInv M0 Mp s F n stk M) (hC : memLoad32 M (F + 0xC) = out) (hR : PRegs f g0 F p n c)
    (ha1 : f a1 = BitVec.ofNat 32 st) (ha2 : f a2 = BitVec.ofNat 32 l) :
    WP jsonParseCode base (PPost M0 s p out g0 (keysThen (checkKeys c (slice (memBytes M0 p n) st l)) R))
      M 0x18C f := by
  have hfr := hR.fr
  have hn := E.hn
  obtain ⟨hq0, hqn⟩ := E.qnz hsl
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  have hFA8 : F + 0xA8 = s + BitVec.ofNat 32 332 := by rw [← E.hF, BitVec.add_assoc]; rfl
  have m1 : Sep (F + 0xA8) 12 (s + BitVec.ofNat 32 148) 16 := by
    rw [hFA8]; exact sep_offsets s (c := 332) (n := 12) (d := 148) (k := 16) (Or.inr (by decide)) (by decide)
      (by decide)
  refine WP.zero fun hz => ?_
  refine WP.alu pa_at_18c ?_; wn
  refine WP.aluImm pa_at_18e ?_; wn
  refine WP.callMembers (tb := base + 0xFFFFF372 + 0xA6) (out := F + 0xA8) (s := s + BitVec.ofNat 32 148)
    (p := p + BitVec.ofNat 32 st) (n := l) pa_at_190 pa_at_194 (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) (by decide)
    hc1.get.me (by rw [gt_ad_sw]; exact hc1.get.ri.sw) (by (try rsimp); rw [hR.sp, ev_add])
    (by (try rsimp); rw [ha1, hR.s7, ev_add, BitVec.add_comm]) (by (try rsimp); exact ha2)
    (by (try rsimp); rw [hR.sp, ← E.hF, BitVec.add_assoc]; rfl) (by omega)
    (aligned_add E.hal (k := 148) (by decide)) (E.alF (d := 0xA8) (by decide))
    (E.sep.get.me.sub (by decide)) (by rw [gt_ad_sw]; exact E.sep.get.ri.sw.sub (by decide))
    ((E.sepq hsl).sub (by decide)) m1 (E.sepF E.sep.get.me (d := 0xA8) (w := 12) (by decide))
    (E.sep.parse.sub (by decide)) (E.sepF E.sep.parse (d := 0xA8) (w := 12) (by decide)) fun m2 hCR => ?_
  rw [E.slice hsl hFI.1] at hCR
  generalize hO : slice (memBytes M0 p n) st l = o at hCR ⊢
  obtain ⟨Ma, hOa, hCR⟩ := hCR
  generalize m2.mem = M2 at hCR
  have hFI2 : FInv M0 Mp s F n stk M2 :=
    (hFI.out E.hF hOa (Or.inl (by decide))).outF E.hF (d := 0xA8) hCR.out (Or.inr ⟨by decide, by decide⟩)
  have hC2 : memLoad32 M2 (F + 0xC) = out :=
    ((pa_fkeep (d := 0xC) hCR.out (Or.inr (by decide)) (by decide) (by decide)).trans
      (pa_lowkeep E hOa (by decide))).trans hC
  refine WP.zero fun hz2 => ?_
  refine WP.lw pa_at_198 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xA8) (by decide)) ?_; wn
  refine WP.lbu pa_at_19a ?_; wn
  rcases hco : curOpen 123 (p + BitVec.ofNat 32 st) o with _ | ⟨q, l', k'⟩ <;> rw [hco] at hCR
  · obtain ⟨-, t1, t2⟩ := hCR
    rw [ck_none hco]
    change WP _ _ (PPost M0 s p out g0 (.error 0x21)) _ _ _
    have t2' : M2 (F + 0xAC) = 0x21 := by
      rw [show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch pa_at_19e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.aluImm pa_at_246 ?_; wn
    refine WP.alu pa_at_24a ?_; wn
    refine WP.branch pa_at_24c (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hR.sp, t2'] at eb; exact absurd eb (by decide)
    refine WP.jal pa_at_250 (by decide) ?_; wn
    exact pa_2c0 E (by (try rsimp); exact hR.sp) hC2 (by (try rsimp); rw [hR.sp, t2']; rfl) hFI2.1 hFI2.2.1
      (by keepz E.z0)
  obtain ⟨hq, hl', hk', hl0⟩ := ck_some hco
  have hlen : o.length = l := by rw [← hO]; unfold slice; rw [memBytes_slice hsl, memBytes_length]
  rw [hq, hl', hk', hlen] at hCR
  obtain ⟨-, t1, t2, t3⟩ := hCR
  have t2' : memLoad32 M2 (F + 0xAC) = BitVec.ofNat 32 l := by
    rw [show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
  have t3' : memLoad32 M2 (F + 0xB0) = BitVec.ofNat 32 (skipWs o 1) := by
    rw [show F + 0xB0 = F + 0xA8 + 8 by rw [BitVec.add_assoc]; rfl]; exact t3
  have hq00 := nx_q0 hq0 (n := 1) (pos := 0) (by omega) (by omega)
  rw [add_ofNat_zero] at hq00
  refine WP.branch pa_at_19e (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hR.sp, t1, hq00] at eb; exact absurd eb (by decide)
  refine WP.sw pa_at_1a0 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 8) (by decide))
    (by (try rsimp); rw [hR.sp]; exact E.sepF E.sep.parse (d := 8) (w := 4) (by decide)) ?_; wn
  refine WP.aluImm pa_at_1a2 ?_; wn
  refine WP.aluImm pa_at_1a4 ?_; wn
  refine WP.aluImm pa_at_1a8 ?_; wn
  (try rsimp); rw [hR.sp]
  have hFI3 : FInv M0 Mp s F n stk (memStore32 M2 (F + 8) (f 26)) :=
    hFI2.outF E.hF (d := 8) (out_store32 _ _ _) (Or.inl (by decide))
  have hc3 : ParseCode (memStore32 M2 (F + 8) (f 26)) base := E.code.out hFI3.1 E.sep
  have hFt : ∀ d : Nat, 164 + d < 404 → (F + BitVec.ofNat 32 d).toNat = s.toNat + 164 + d := fun d hd => by
    have := E.hsw
    rw [← E.hF, add_ofNat_assoc, toNat_add_lt (by omega)]; omega
  have E2 : McEnv (memStore32 M2 (F + 8) (f 26)) (base + 0xFFFFF372 + 0xBFDA + 8) (F + 0x95) (F + 0xAD)
      (s + BitVec.ofNat 32 148) 7 := by
    refine ⟨by rw [gt_ad_mc]; exact hc3.get.mc, ?_, by rw [gt_ad_mc]; exact E.sep.get.mc.sub (by decide), ?_, ?_,
      ?_, aligned_add E.hal (k := 148) (by decide), ?_, ?_, ?_⟩
    · rw [gt_ad_mc]; exact E.sepF E.sep.get.mc (d := 0x95) (w := 7) (by decide)
    · show Sep (F + BitVec.ofNat 32 0x95) 7 _ 16
      rw [← E.hF, add_ofNat_assoc]
      exact sep_offsets s (c := 313) (n := 7) (d := 148) (k := 16) (Or.inr (by decide)) (by decide) (by decide)
    · show Sep (F + BitVec.ofNat 32 0xAD) 7 _ 16
      rw [← E.hF, add_ofNat_assoc]
      exact sep_offsets s (c := 337) (n := 7) (d := 148) (k := 16) (Or.inr (by decide)) (by decide) (by decide)
    · exact sep_offsets F (c := 0x95) (n := 7) (d := 0xAD) (k := 7) (Or.inl (by decide)) (by decide) (by decide)
    · have := E.hsw; rw [toNat_add_lt (by omega)]; omega
    · show (F + BitVec.ofNat 32 0x95).toNat + 7 < 2 ^ 32
      have := E.hsw; rw [hFt 0x95 (by decide)]; omega
    · show (F + BitVec.ofNat 32 0xAD).toNat + 7 < 2 ^ 32
      have := E.hsw; rw [hFt 0xAD (by decide)]; omega
  refine WP.callMemcpy (tb := base + 0xFFFFF372 + 0xBFDA) (dst := F + 0x95) (src := F + 0xAD)
    (F := s + BitVec.ofNat 32 148) (N := 7) pa_at_1ac pa_at_1b0 (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) (by decide) hc3.get.stub E2
    (by (try rsimp); (try rw [hR.sp]); rw [ev_add]) (by (try rsimp); (try rw [hR.sp]); rw [ev_add])
    (by (try rsimp); (try simp only [ev0, ev_mv hz2]); try rfl)
    (by (try rsimp); (try rw [hR.sp]); rw [← E.hF, BitVec.add_assoc]; rfl) (E.sep.parse.sub (by decide))
    (E.sepF E.sep.parse (d := 0x95) (w := 7) (by decide)) fun m3 hO3 => ?_
  generalize m3.mem = M3 at hO3
  refine WP.aluImm pa_at_1b4 ?_; wn
  refine WP.sw pa_at_1b6 (by (try rsimp); (try rw [hR.sp]); exact E.alF (d := 0x90) (by decide))
    (by (try rsimp); (try rw [hR.sp]); exact E.sepF E.sep.parse (d := 0x90) (w := 4) (by decide)) ?_; wn
  refine WP.sb pa_at_1b8 (by (try rsimp); (try rw [hR.sp]); exact E.sepF E.sep.parse (d := 0x94) (w := 1) (by decide))
    ?_; wn
  (try rsimp); (try rw [hR.sp]); rw [t1, ri_ze]
  have oC : Out (memStore32 M2 (F + 8) (f 26)) (copyBytes (memStore32 M2 (F + 8) (f 26)) (F + 0x95) (F + 0xAD) 7)
      (F + 0x95) 7 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have hFI5 : FInv M0 Mp s F n stk
      (memStore8 (memStore32 M3 (F + 0x90) (p + BitVec.ofNat 32 st)) (F + 0x94) (M2 (F + 0xAC))) :=
    (((hFI3.outF E.hF (d := 0x95) oC (Or.inr ⟨by decide, by decide⟩)).out E.hF hO3 (Or.inl (by decide))).outF E.hF
      (d := 0x90) (out_store32 _ _ _) (Or.inr ⟨by decide, by decide⟩)).outF E.hF (d := 0x94) (out_store8 _ _ _)
      (Or.inr ⟨by decide, by decide⟩)
  have k5 : ∀ d, d + 4 ≤ 0x90 →
      memLoad32 (memStore8 (memStore32 M3 (F + 0x90) (p + BitVec.ofNat 32 st)) (F + 0x94) (M2 (F + 0xAC)))
        (F + BitVec.ofNat 32 d) = memLoad32 (memStore32 M2 (F + 8) (f 26)) (F + BitVec.ofNat 32 d) := fun d hd =>
    (pa_fkeep (a := 0x94) (k := 1) (out_store8 _ _ _) (Or.inr (by omega)) (by decide) (by omega)).trans
      ((pa_fkeep (a := 0x90) (k := 4) (out_store32 _ _ _) (Or.inr (by omega)) (by decide) (by omega)).trans
        ((pa_lowkeep E hO3 (by omega)).trans
          (pa_fkeep (a := 0x95) (k := 7) oC (Or.inr (by omega)) (by decide) (by omega))))
  have h8 := (k5 8 (by decide)).trans (memLoad32_store32_same _ _ _)
  have hC5 := (k5 0xC (by decide)).trans
    ((pa_fkeep (a := 8) (k := 4) (out_store32 _ _ _) (Or.inl (by decide)) (by decide) (by decide)).trans hC2)
  have h90 : memLoad32 (memStore8 (memStore32 M3 (F + 0x90) (p + BitVec.ofNat 32 st)) (F + 0x94) (M2 (F + 0xAC)))
      (F + 0x90) = p + BitVec.ofNat 32 st :=
    (memLoad32_store8_sep (sep_offsets F (c := 0x94) (n := 1) (d := 0x90) (k := 4) (Or.inr (by decide)) (by decide)
      (by decide))).trans (memLoad32_store32_same _ _ _)
  generalize hM5 : memStore8 (memStore32 M3 (F + 0x90) (p + BitVec.ofNat 32 st)) (F + 0x94) (M2 (F + 0xAC)) = M5
    at hFI5 h8 hC5 h90
  have hcp : ∀ c, 0x95 ≤ c → c < 0x9C → M5 (F + BitVec.ofNat 32 c) = M2 (F + BitVec.ofNat 32 (c + 24)) := by
    intro c hc1 hc2
    rw [← hM5, memStore8_ne ?_]
    · rw [out_store32 _ _ _ _ ?_, hO3 _ ?_]
      · have := copyBytes_at (M := memStore32 M2 (F + 8) (f 26)) (dst := F + BitVec.ofNat 32 0x95)
          (src := F + BitVec.ofNat 32 0xAD) (N := 7) (i := c - 0x95) (by omega) (by decide)
        rw [add_ofNat_assoc, add_ofNat_assoc, show 0x95 + (c - 0x95) = c by omega,
          show 0xAD + (c - 0x95) = c + 24 by omega] at this
        refine this.trans ?_
        exact out_store32 _ _ _ _ (sep_offsets F (c := c + 24) (n := 1) (d := 8) (k := 4) (Or.inr (by omega))
          (by omega) (by decide))
      · rw [← E.hF, add_ofNat_assoc]
        exact sep_offsets s (c := 164 + c) (n := 1) (d := 148) (k := 16) (Or.inr (by omega)) (by omega) (by decide)
      · exact sep_offsets F (c := c) (n := 1) (d := 0x90) (k := 4) (Or.inr (by omega)) (by omega) (by decide)
    · exact sep_byte0 (sep_offsets F (c := c) (n := 1) (d := 0x94) (k := 1) (Or.inr (by omega)) (by omega)
        (by decide)) (by decide)
  have h94 : memLoad32 M5 (F + 0x94) = BitVec.ofNat 32 l := by
    rw [← t2']
    refine memLoad32_shift fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [add_ofNat_zero, add_ofNat_zero, ← hM5, memStore8_same]
    · show M5 (F + BitVec.ofNat 32 0x94 + BitVec.ofNat 32 j) = M2 (F + BitVec.ofNat 32 0xAC + BitVec.ofNat 32 j)
      rw [add_ofNat_assoc, add_ofNat_assoc, hcp (0x94 + j) (by omega) (by omega),
        show 0x94 + j + 24 = 0xAC + j by omega]
  have h98 : memLoad32 M5 (F + 0x98) = BitVec.ofNat 32 (skipWs o 1) := by
    rw [← t3']
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 0x98 + BitVec.ofNat 32 j) = M2 (F + BitVec.ofNat 32 0xB0 + BitVec.ofNat 32 j)
    rw [add_ofNat_assoc, add_ofNat_assoc, hcp (0x98 + j) (by omega) (by omega), show 0x98 + j + 24 = 0xB0 + j by omega]
  exact pa_keys E hsl hO hl0 (f1 := f) hok hFI5 h90 h94 h98 h8 hC5 (by pregs hR, E.z0)
    (by (try rsimp); (try simp only [ev0]); try rfl) (by keepz hz)

end

end C3.RV32
