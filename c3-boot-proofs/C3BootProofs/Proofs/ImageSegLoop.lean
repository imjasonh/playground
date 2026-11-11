import C3BootProofs.Proofs.ImageCheck

/-!
# `image::parse`: the segment loop

`lp_loop` runs the loop at offset 0x188 to its exit at 0x2E8, by induction
on the segments left: each pass reads a segment with `lp_read` and checks
and stores it with `lp_check`, as `readSegsW` does.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

theorem segL_kind {M : Word → BitVec 8} {ptr len pos a o p : Word} {k : BitVec 8} {s : SegW}
    (h : segL M ptr len pos k a o = .ok (s, p)) : s.kind = k := by
  unfold segL rdU32 rdB at h
  revert h
  rcases bytesResult ptr len pos 4 with _ | ⟨q, e⟩
  · intro h; cases h
  · intro h; cases h; rfl

theorem segO_kind {M : Word → BitVec 8} {ptr len pos a p : Word} {k : BitVec 8} {s : SegW}
    (h : segO M ptr len pos k a = .ok (s, p)) : s.kind = k := by
  unfold segO rdU32 rdB at h
  revert h
  rcases bytesResult ptr len pos 4 with _ | ⟨q, e⟩
  · intro h; cases h
  · intro h; exact segL_kind h

theorem segA_kind {M : Word → BitVec 8} {ptr len pos p : Word} {k : BitVec 8} {s : SegW}
    (h : segA M ptr len pos k = .ok (s, p)) : s.kind = k := by
  unfold segA rdU32 rdB at h
  revert h
  rcases bytesResult ptr len pos 4 with _ | ⟨q, e⟩
  · intro h; cases h
  · intro h; exact segO_kind h

/-- `read_segment` only returns kinds 0 through 3. -/
theorem readSegW_kind {M : Word → BitVec 8} {ptr len pos p : Word} {s : SegW}
    (h : readSegW M ptr len pos = .ok (s, p)) : (3 : BitVec 8).ult s.kind = false := by
  unfold readSegW rdU8 rdB at h
  revert h
  rcases bytesResult ptr len pos 1 with _ | ⟨q, e⟩
  · intro h; cases h
  · intro h
    change (if (3 : BitVec 8).ult (M q - 1) = true then Except.error 9
      else Except.bind (rdRes M ptr len 3 e) fun pos => segA M ptr len pos (M q - 1)) = _ at h
    by_cases hk : (3 : BitVec 8).ult (M q - 1) = true
    · rw [ite_eq_left hk] at h; cases h
    · rw [ite_eq_right hk] at h
      unfold rdRes rdB at h
      revert h
      rcases bytesResult ptr len e 3 with _ | ⟨q2, e2⟩
      · intro h; cases h
      · intro h
        change Except.bind (if allZero M q2 (3 : Word).toNat = true then .ok e2 else .error 4)
          (fun pos => segA M ptr len pos (M q - 1)) = _ at h
        by_cases hz : allZero M q2 (3 : Word).toNat = true
        · rw [ite_eq_left hz] at h
          rw [segA_kind h]; exact Bool.eq_false_iff.mpr hk
        · rw [ite_eq_right hz] at h; cases h

section Run

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}
  {sv cnt : BitVec 8} {entry : Word}

/-- `LInv` holds after a write to `a0`. -/
theorem LInv.withA0 {segs : List SegW} {pos prev : Word}
    (li : LInv R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Mx g) (v : Word) :
    LInv R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Mx (upd g a0 v) :=
  { li with
    inv := li.inv.setR a0
    s2 := by rw [updz li.inv.zero (by decide), li.s2]
    s11 := by rw [updz li.inv.zero (by decide), li.s11]
    s8 := by rw [updz li.inv.zero (by decide), li.s8]
    s9 := by rw [updz li.inv.zero (by decide), li.s9]
    s5 := by rw [updz li.inv.zero (by decide), li.s5] }

theorem loop_exit : ∀ c : BitVec 8, c.toNat ≤ 16 →
    aluEval .add (aluEval .add (c.zeroExtend 32 <<< 4) (BitVec.ofNat 32 (0x100 - 16 * c.toNat))) 0xFFFFFF00 = 0 := by
  decide

theorem loop_more : ∀ c : BitVec 8, ∀ i, i < 16 → i < c.toNat → c.toNat ≤ 16 →
    aluEval .add (aluEval .add (c.zeroExtend 32 <<< 4) (BitVec.ofNat 32 (0x100 - 16 * i))) 0xFFFFFF00 ≠ 0 := by
  decide

theorem s8_ne0 : ∀ i, i < 16 → BitVec.ofNat 32 (0x100 - 16 * i) ≠ 0 := by decide

end Run

/-- What the loop at `m`, with `segs` read, does with the rest, given what
`readSegsW` decides. -/
def LpPost (P R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry : Word) (segs : List SegW) (m : Machine) :
    Except (BitVec 8) (List SegW × Word × Word) → Prop
  | .error e => IErrDone R G out M0 f0 e m
  | .ok (rest, pos, prev) => ∃ m' My g, Steps m m' ∧ St My P m' 0x2E8 g ∧
      LInv R G ptr len out ilen M0 f0 sv cnt entry (segs ++ rest) pos prev My g ∧
      (segs ++ rest).length = cnt.toNat

section Run

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}
  {sv cnt : BitVec 8} {entry : Word}

/-- **The segment loop**, from offset 0x188 with `segs` read and `n` left. -/
theorem lp_loop (env : IEnv P R G ptr len out) (code0 : ICode M0 P) :
    ∀ n (segs : List SegW) (pos prev : Word) {Mx : Word → BitVec 8} {g : Fin 32 → Word} {m : Machine},
      segs.length + n = cnt.toNat →
      LInv R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Mx g → St Mx P m 0x188 g →
      LpPost P R G ptr len out ilen M0 f0 sv cnt entry segs m (readSegsW M0 ptr len ilen n pos prev)
  | n, segs, pos, prev, Mx, g, m, hn, li, st => by
    have hc := (li.inv.code env code0).parse
    have hz := li.inv.zero
    obtain ⟨m1, d1, u1⟩ := st.alu hc ip_at_188 (off' := 0x18C) (by decide)
    obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_18c (off' := 0x190) (by decide)
    have v2 : upd (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32)))) a0
        (aluEval .add (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32))) a0) 0xFFFFFF00) a0 =
        aluEval .add (aluEval .add (cnt.zeroExtend 32 <<< 4) (BitVec.ofNat 32 (0x100 - 16 * segs.length)))
          0xFFFFFF00 := by
      rw [upd_a0, upd_a0, li.s11, show g (24 : Fin 32) = g s8 from rfl, li.s8]
    have li2 := (li.withA0 (aluEval .add (g s11) (g (24 : Fin 32)))).withA0
      (aluEval .add (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32))) a0) 0xFFFFFF00)
    have pre : Steps m m2 := .cons d1 (.single d2)
    match n with
    | 0 =>
      obtain ⟨m3, d3, u3⟩ := u2.taken hc 0x2E8 ip_at_190 (by decide)
        (by rw [v2, show upd (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32)))) a0
          (aluEval .add (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32))) a0) 0xFFFFFF00) x0 = 0 from rfl,
          show segs.length = cnt.toNat by omega, loop_exit cnt li.hc]; rfl)
      show LpPost P R G ptr len out ilen M0 f0 sv cnt entry segs m (.ok ([], pos, prev))
      exact ⟨m3, Mx, _, pre.trans (.single d3), u3, by rw [List.append_nil]; exact li2,
        by rw [List.append_nil]; omega⟩
    | n + 1 =>
      have hi : segs.length < cnt.toNat := by omega
      have hi16 : segs.length < 16 := Nat.lt_of_lt_of_le hi li.hc
      obtain ⟨m3, d3, u3⟩ := u2.notTaken hc 0x194 ip_at_190 (by decide)
        (by rw [v2, show upd (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32)))) a0
          (aluEval .add (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32))) a0) 0xFFFFFF00) x0 = 0 from rfl]
            exact bne_iff_ne.mpr (loop_more cnt segs.length hi16 hi li.hc) |> fun h => by
              simpa [branchTaken] using h)
      obtain ⟨m4, d4, u4⟩ := u3.notTaken hc 0x198 ip_at_194 (by decide)
        (by rw [li2.s8, show upd (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32)))) a0
          (aluEval .add (upd g a0 (aluEval .add (g s11) (g (24 : Fin 32))) a0) 0xFFFFFF00) x0 = 0 from rfl]
            exact Bool.eq_false_iff.mpr fun h => s8_ne0 _ hi16 (beq_iff_eq.mp h))
      have rd := lp_read env code0 li2.inv u4 li.pos
      have pre4 : Steps m m4 := pre.trans (.cons d3 (.single d4))
      unfold readSegsW
      revert rd
      cases h : readSegW M0 ptr len pos with
      | error e => intro rd; exact IErrDone.pre pre4 rd
      | ok sp =>
        obtain ⟨s, pos1⟩ := sp
        rintro ⟨m5, My, g5, c5, u5, rinv, rpos, rfr, rho, rhl, rhs7, rhs6, rkeep⟩
        have ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Mx _ s pos1 My g5 :=
          ⟨li2, hi, rinv, rpos, rfr, fun r hr => rkeep r (nl hr a0) (nl hr a1) (nl hr a2) (nl hr a3)
            (nl hr a4) (nl hr a5) (nl hr ra) (nl hr s6) (nl hr s7), readSegW_kind h⟩
        have ck := lp_check env code0 ctx u5 rhl rho rhs7 rhs6
        show LpPost P R G ptr len out ilen M0 f0 sv cnt entry segs m (Except.bind (checkSegW ilen prev s)
          fun prev => Except.bind (readSegsW M0 ptr len ilen n pos1 prev) fun r =>
            match r with | (rest, pos, prev) => pure (s :: rest, pos, prev))
        revert ck
        cases hck : checkSegW ilen prev s with
        | error e => intro ck; exact IErrDone.pre (pre4.trans c5) ck
        | ok prev1 =>
          rintro ⟨m6, M6, g6, c6, u6, li6⟩
          have ih := lp_loop env code0 n (segs ++ [s]) pos1 prev1 (by simp; omega) li6 u6
          show LpPost P R G ptr len out ilen M0 f0 sv cnt entry segs m
            (Except.bind (readSegsW M0 ptr len ilen n pos1 prev1) fun r =>
              match r with | (rest, pos, prev) => pure (s :: rest, pos, prev))
          revert ih
          cases hr : readSegsW M0 ptr len ilen n pos1 prev1 with
          | error e => intro ih; exact IErrDone.pre ((pre4.trans c5).trans c6) ih
          | ok rp =>
            obtain ⟨rest, pos2, prev2⟩ := rp
            rintro ⟨m7, M7, g7, c7, u7, li7, hl7⟩
            show LpPost P R G ptr len out ilen M0 f0 sv cnt entry segs m (.ok (s :: rest, pos2, prev2))
            refine ⟨m7, M7, g7, ((pre4.trans c5).trans c6).trans c7, u7, ?_, ?_⟩
            · rw [show segs ++ s :: rest = segs ++ [s] ++ rest by simp]; exact li7
            · rw [show segs ++ s :: rest = segs ++ [s] ++ rest by simp]; exact hl7

end Run

end C3.RV32
