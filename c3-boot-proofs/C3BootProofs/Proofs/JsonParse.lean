import C3BootProofs.Proofs.JsonParseOuter
import C3BootProofs.Proofs.JsonParseEnd

/-!
# `json::parse` from its entry

The prologue, the loop at `0x24` that clears the 16 stack entries, and
the start position: `0` in canonical mode, or the position after leading
whitespace. Then `pa_loop` runs with `d.length + 1` passes of fuel, which
is `parseModel`.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem pz_m4 (F : Word) (i : Nat) :
    F + BitVec.ofNat 32 (0x14 + 8 * i) + 0xFFFFFFFC = F + BitVec.ofNat 32 (0x10 + 8 * i) := by
  show F + BitVec.ofNat 32 (0x14 + 8 * i) + BitVec.ofNat 32 0xFFFFFFFC = _
  rw [add_ofNat_assoc]
  exact congrArg (F + ·) (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega))

theorem pz_p8 (F : Word) (i : Nat) :
    aluEval .add (F + BitVec.ofNat 32 (0x14 + 8 * i)) 0x8 = F + BitVec.ofNat 32 (0x14 + 8 * (i + 1)) := by
  show F + BitVec.ofNat 32 (0x14 + 8 * i) + BitVec.ofNat 32 8 = _
  rw [add_ofNat_assoc]; rfl

theorem pz_mode (c : Bool) : branchTaken .beq (modeW c) 0 = !c := by cases c <;> rfl

theorem pz_bne {j : Nat} (hj : j < 2 ^ 32) : branchTaken .bne (BitVec.ofNat 32 j) 0 = !decide (j = 0) :=
  br_bne hj (by decide)

section
variable {M0 Mp : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 f : Fin 32 → Word}

theorem PaEnv.offF (E : PaEnv M0 base s p out n g0 Mp F) (d : Nat) :
    s + BitVec.ofNat 32 (164 + d) = F + BitVec.ofNat 32 d := by
  rw [← add_ofNat_assoc, E.hF]

/-- The loop at `0x2A` with `a0 = j` entries left to clear: it keeps
`FInv` with an empty stack and every register but `a0` and `a1`. -/
theorem pa_zero {Q : Post} (E : PaEnv M0 base s p out n g0 Mp F) {fr : Fin 32 → Word}
    (k : ∀ (M' : Word → BitVec 8) (g : Fin 32 → Word), FInv M0 Mp s F n [] M' →
      (∀ x, x ≠ a0 → x ≠ a1 → g x = fr x) → WP jsonParseCode base Q M' 0x38 g) :
    ∀ (j : Nat) (M : Word → BitVec 8) (f : Fin 32 → Word), j + 1 ≤ 16 → FInv M0 Mp s F n [] M →
      f a0 = BitVec.ofNat 32 (j + 1) → f a1 = F + BitVec.ofNat 32 (0x14 + 8 * (15 - j)) →
      (∀ x, x ≠ a0 → x ≠ a1 → f x = fr x) → WP jsonParseCode base Q M 0x2A f := by
  intro j
  induction j with
  | zero =>
    intro M f hj hFI h0 h1 hfr
    refine WP.zero fun hz => ?_
    refine WP.sw jpa_at_2a (by (try rsimp); rw [h1, pz_m4]; exact E.alF (by decide))
      (by (try rsimp); rw [h1, pz_m4]; exact E.sepF E.sep.parse (by decide)) ?_; wn
    refine WP.sb jpa_at_2e (by (try rsimp); rw [h1, add_lit_zero]; exact E.sepF E.sep.parse (by decide)) ?_; wn
    refine WP.aluImm jpa_at_32 ?_; wn
    refine WP.aluImm jpa_at_34 ?_; wn
    have hA : FInv M0 Mp s F n [] (memStore32 M (F + BitVec.ofNat 32 (0x10 + 8 * (15 - 0))) (f x0)) := by
      refine FInv.out0 E.hF (c := 164 + (0x10 + 8 * (15 - 0))) (k := 4) hFI ?_ (by decide)
      rw [E.offF]; exact out_store32 _ _ _
    have hFI2 : FInv M0 Mp s F n [] (memStore8 (memStore32 M (F + BitVec.ofNat 32 (0x10 + 8 * (15 - 0)))
        (f x0)) (F + BitVec.ofNat 32 (0x14 + 8 * (15 - 0))) ((f x0).extractLsb' 0 8)) := by
      refine FInv.out0 E.hF (c := 164 + (0x14 + 8 * (15 - 0))) (k := 1) hA ?_ (by decide)
      rw [E.offF]; exact out_store8 _ _ _
    refine WP.branch jpa_at_36 (fun eb => ?_) (fun _ => ?_) <;> wn
    · (try rsimp at eb); (try rw [show f x0 = 0 from hz] at eb); rw [h0, pc_dec, pz_bne (by decide)] at eb
      exact absurd eb (by decide)
    rw [h1, pz_m4, add_lit_zero]
    refine k _ _ hFI2 (fun x h0' h1' => ?_)
    rw [upd_ne0 (G := upd f a1 _) (by rfl) h0', upd_ne0 hz h1']; exact hfr x h0' h1'
  | succ j ih =>
    intro M f hj hFI h0 h1 hfr
    refine WP.zero fun hz => ?_
    refine WP.sw jpa_at_2a (by (try rsimp); rw [h1, pz_m4]; exact E.alF (by omega))
      (by (try rsimp); rw [h1, pz_m4]; exact E.sepF E.sep.parse (by omega)) ?_; wn
    refine WP.sb jpa_at_2e (by (try rsimp); rw [h1, add_lit_zero]; exact E.sepF E.sep.parse (by omega)) ?_; wn
    refine WP.aluImm jpa_at_32 ?_; wn
    refine WP.aluImm jpa_at_34 ?_; wn
    have hA : FInv M0 Mp s F n [] (memStore32 M (F + BitVec.ofNat 32 (0x10 + 8 * (15 - (j + 1)))) (f x0)) := by
      refine FInv.out0 E.hF (c := 164 + (0x10 + 8 * (15 - (j + 1)))) (k := 4) hFI ?_ (by omega)
      rw [E.offF]; exact out_store32 _ _ _
    have hFI2 : FInv M0 Mp s F n [] (memStore8 (memStore32 M (F + BitVec.ofNat 32 (0x10 + 8 * (15 - (j + 1))))
        (f x0)) (F + BitVec.ofNat 32 (0x14 + 8 * (15 - (j + 1)))) ((f x0).extractLsb' 0 8)) := by
      refine FInv.out0 E.hF (c := 164 + (0x14 + 8 * (15 - (j + 1)))) (k := 1) hA ?_ (by omega)
      rw [E.offF]; exact out_store8 _ _ _
    refine WP.branch jpa_at_36 (fun eb => ?_) (fun eb => ?_) <;> wn
    · rw [h1, pz_m4, add_lit_zero]
      refine ih _ _ (by omega) hFI2 (by (try rsimp); rw [h0, pc_dec]) ?_ ?_
      · (try rsimp); (try rw [h1]); rw [pz_p8, show 15 - (j + 1) + 1 = 15 - j by omega]
      · intro x h0' h1'; rw [upd_ne0 (G := upd f a1 _) (by rfl) h0', upd_ne0 hz h1']; exact hfr x h0' h1'
    · (try rsimp at eb); (try rw [show f x0 = 0 from hz] at eb); rw [h0, pc_dec, pz_bne (by omega),
        show decide (j + 1 = 0) = false from decide_eq_false (Nat.succ_ne_zero j)] at eb
      exact absurd eb (by decide)

/-- `0x50`: the loop's registers, then `pa_loop` with `d.length + 1` passes
from the start position `s10`. -/
theorem pa_50 (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {M : Word → BitVec 8}
    (hFI : FInv M0 Mp s F n [] M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out)
    (h26 : f 26 = BitVec.ofNat 32 (wsIn c (memBytes M0 p n) 0)) :
    WP jsonParseCode base (PPost M0 s p out g0 (parseModel c (memBytes M0 p n))) M 0x50 f := by
  have hdl : (memBytes M0 p n).length = n := memBytes_length _ _ _
  have hst : wsIn c (memBytes M0 p n) 0 ≤ n := by have := wsIn_le c (memBytes M0 p n) 0; omega
  refine WP.zero fun hz => ?_
  refine WP.aluImm jpa_at_50 ?_; wn
  refine WP.aluImm jpa_at_52 ?_; wn
  refine WP.aluImm jpa_at_54 ?_; wn
  refine WP.aluImm jpa_at_58 ?_; wn
  refine WP.alu jpa_at_5a ?_; wn
  unfold parseModel; rw [hdl]
  exact pa_loop E hst (n + 1) (Nat.le_refl _) _ _ [] _ hFI (by pregs hR, E.z0)
    (by (try rsimp); exact h18) (by (try rsimp); rw [hR.s8]; exact pc_inc n) (by (try rsimp); (try simp only [ev0, ev_mv hz]); (try rfl))
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h26) hst (by (try rsimp); (try simp only [ev0, ev_mv hz]); (try rfl)) (by (try rsimp); exact h26)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); (try rw [Nat.sub_self]); (try rfl))

/-- `0x38`: the start position, `0` in canonical mode or past the leading
whitespace otherwise. -/
theorem pa_start (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {M : Word → BitVec 8}
    (hFI : FInv M0 Mp s F n [] M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out) :
    WP jsonParseCode base (PPost M0 s p out g0 (parseModel c (memBytes M0 p n))) M 0x38 f := by
  have hn := E.hn
  have hd : memBytes M p n = memBytes M0 p n := hFI.1.bytes E.sP
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  refine WP.zero fun hz => ?_
  refine WP.branch jpa_at_38 (fun eb => ?_) (fun eb => ?_) <;> wn
  · rw [hR.s3, show f x0 = 0 from hz, pz_mode] at eb
    cases c
    · refine WP.alu jpa_at_40 ?_; wn
      refine WP.alu jpa_at_42 ?_; wn
      refine WP.aluImm jpa_at_44 ?_; wn
      refine WP.callSkipWs (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0x288) (p := p) (n := n) (q := 0)
        jpa_at_46 jpa_at_4a (by simp only [BitVec.add_assoc]; rfl)
        (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
        hc1.get.ri.sw (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s7)
        (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s8)
        (by (try rsimp); (try simp only [ev0, ev_mv hz]); (try rfl)) (by omega) (by decide) fun m2 h0 => ?_
      refine WP.alu jpa_at_4e ?_; wn
      exact pa_50 E hFI (by pregs hR, E.z0) (by (try rsimp); exact h18)
        (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0, hd]; rfl)
    · exact absurd eb (by decide)
  rw [hR.s3, show f x0 = 0 from hz, pz_mode] at eb
  cases c
  · exact absurd eb (by decide)
  refine WP.aluImm jpa_at_3c ?_; wn
  refine WP.jal jpa_at_3e (by decide) ?_; wn
  exact pa_50 E hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); (try simp only [ev0, ev_mv hz]); (try rfl))

end

/-- `parse` from its entry, as a `WP`. -/
theorem pa_wp {M0 : Word → BitVec 8} {base s p out : Word} {n : Nat} {f : Fin 32 → Word} {c : Bool}
    (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = modeW c)
    (hsp : f sp = s + BitVec.ofNat 32 404) (hret : f ra &&& ~~~1 = f ra) (hb : base.toNat % 2 = 0)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hsw : s.toNat + 404 < 2 ^ 32) (hn : n < 2 ^ 31)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hcode : ParseCode M0 base) (hps : ParseSep s 404 base)
    (hSp : Sep s 404 p n) (hso : Sep out 8 s 404) (hsc : Sep out 8 base jsonParseCode.length) :
    WP jsonParseCode base (PPost M0 s p out f (parseModel c (memBytes M0 p n))) M0 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFF10 = s + 164 := by rw [hsp, ev_add, BitVec.add_assoc]; rfl
  refine WP.aluImm jpa_at_0 ?_; wn
  rw [esp]
  generalize hF : s + 164 = F
  have hF' : s + BitVec.ofNat 32 164 = F := hF
  obtain ⟨hO1, hv⟩ := jpa_pro M0 F f
  have E : PaEnv M0 base s p out n f (paM1 M0 F f) F :=
    ⟨hF', hb, hal, halo, hn, hp0, hpn, hsw, hcode, hps, hSp, hso, hsc, hv,
      by rw [hsp, ← hF', add_ofNat_assoc], hret, hz⟩
  refine WP.sw jpa_at_2 (by rsimp; exact E.alF (d := 0xEC) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xEC) (by decide)) ?_; wn
  refine WP.sw jpa_at_4 (by rsimp; exact E.alF (d := 0xE8) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xE8) (by decide)) ?_; wn
  refine WP.sw jpa_at_6 (by rsimp; exact E.alF (d := 0xE4) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xE4) (by decide)) ?_; wn
  refine WP.sw jpa_at_8 (by rsimp; exact E.alF (d := 0xE0) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xE0) (by decide)) ?_; wn
  refine WP.sw jpa_at_a (by rsimp; exact E.alF (d := 0xDC) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xDC) (by decide)) ?_; wn
  refine WP.sw jpa_at_c (by rsimp; exact E.alF (d := 0xD8) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xD8) (by decide)) ?_; wn
  refine WP.sw jpa_at_e (by rsimp; exact E.alF (d := 0xD4) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xD4) (by decide)) ?_; wn
  refine WP.sw jpa_at_10 (by rsimp; exact E.alF (d := 0xD0) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xD0) (by decide)) ?_; wn
  refine WP.sw jpa_at_12 (by rsimp; exact E.alF (d := 0xCC) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xCC) (by decide)) ?_; wn
  refine WP.sw jpa_at_14 (by rsimp; exact E.alF (d := 0xC8) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xC8) (by decide)) ?_; wn
  refine WP.sw jpa_at_16 (by rsimp; exact E.alF (d := 0xC4) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xC4) (by decide)) ?_; wn
  refine WP.sw jpa_at_18 (by rsimp; exact E.alF (d := 0xC0) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xC0) (by decide)) ?_; wn
  refine WP.sw jpa_at_1a (by rsimp; exact E.alF (d := 0xBC) (by decide))
    (by rsimp; exact E.sepF E.sep.parse (d := 0xBC) (by decide)) ?_; wn
  change WP jsonParseCode base _ (paM1 M0 F f) 0x1C _
  have hFI : FInv M0 (paM1 M0 F f) s F n [] (paM1 M0 F f) :=
    ⟨Out.upK hF' hO1 (by decide), Slots.refl _ _ _, StkInv.nil _⟩
  refine WP.alu jpa_at_1c ?_; wn
  refine WP.alu jpa_at_1e ?_; wn
  refine WP.alu jpa_at_20 ?_; wn
  refine WP.alu jpa_at_22 ?_; wn
  refine WP.aluImm jpa_at_24 ?_; wn
  refine WP.aluImm jpa_at_26 ?_; wn
  refine WP.branch jpa_at_28 (fun eb => ?_) (fun _ => ?_) <;> wn
  · (try rsimp at eb); (try simp only [ev0, ev_mv hz] at eb); try exact absurd eb (by decide)
  refine pa_zero E (fun M' g hFI' hg => ?_) 15 _ _ (by decide) hFI (by (try rsimp); (try simp only [ev0, ev_mv hz]); try rfl)
    (by (try rsimp); rfl) (fun _ _ _ => rfl)
  have ne : ∀ x, x ∉ paE → x ≠ a0 ∧ x ≠ a1 := fun x hx =>
    ⟨fun h => hx (by rw [h]; decide), fun h => hx (by rw [h]; decide)⟩
  refine pa_start E hFI' ⟨?_, ?_, ?_, ?_, fun x hx => ?_⟩ ?_
  · rw [hg sp (by decide) (by decide)]; rsimp
  · rw [hg 19 (by decide) (by decide)]; (try rsimp); (try simp only [ev0, ev_mv hz]); exact h3
  · rw [hg 23 (by decide) (by decide)]; (try rsimp); (try simp only [ev0, ev_mv hz]); exact h1
  · rw [hg 24 (by decide) (by decide)]; (try rsimp); (try simp only [ev0, ev_mv hz]); exact h2
  · rw [hg x (ne x hx).1 (ne x hx).2]; revert x
    (repeat (first | refine keepUpd0 hz (by decide) ?_ | refine keepClob (by decide) ?_)); exact fun _ _ => rfl
  · rw [hg 18 (by decide) (by decide)]; (try rsimp); (try simp only [ev0, ev_mv hz]); exact h0

/-- `json::parse(doc, mode)` on the `n` bytes at `p`, with `out` in `a0`,
`modeW c` in `a3` (`c` is canonical mode), and `sp = s + 404`, returns with
`out` holding `parseModel c doc` moved to an address by `fieldRes p`: the
start and length of the one JSON value that `doc` holds, or the error byte
`0x20`.

It changes memory only in the 404 bytes at `s` and the 8 bytes at `out`, and
keeps every register outside `jClob`. `ParseCode` says where the code and its
callees are, and `ParseSep` keeps the frame apart from them.

Callers (the TUF and trusted-root checks) reason about the result through
`parseModel`, the position-level model in `JsonParseModel`, which reads the
document in one pass with a stack of at most 16 open containers and, in
canonical mode, runs `checkKeys` on each object as it closes. By
`parseModel_ok`, an `.ok (a, l)` result is a value at `a` whose `l` bytes
lie within the document with only whitespace after them, and in canonical
mode it is the whole document. -/
theorem jsonParse_correct (m : Machine) {base retAddr out s p : Word} {n : Nat} {c : Bool}
    (hb : base.toNat % 2 = 0) (hc : ParseCode m.mem base) (hpc : m.pc = base) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (ha3 : reg m a3 = modeW c)
    (hsp : reg m sp = s + BitVec.ofNat 32 404) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hsw : s.toNat + 404 < 2 ^ 32) (hn : n < 2 ^ 31)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hps : ParseSep s 404 base) (hSp : Sep s 404 p n)
    (hso : Sep out 8 s 404) (hsc : Sep out 8 base jsonParseCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      FieldResF m.mem m'.mem out s 404 (fieldRes p (parseModel c (memBytes m.mem p n))) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (pa_wp ha0 ha1 ha2 ha3 hsp (by rw [hra]; exact hret) hb hal halo
    hsw hn hp0 hpn hc hps hSp hso hsc) hb hc.parse hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
