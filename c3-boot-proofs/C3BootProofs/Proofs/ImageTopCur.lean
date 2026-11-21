import C3BootProofs.Proofs.ImageFinalCur

/-! # `image::parse`, end to end

`imageParse_correct` composes the stages: the header (`ip_header`), the
segment array's setup (`ip_setup`), the segment loop (`lp_loop`), the end check
(`od_setup`), the overlap loops (`ov_outer`), and the entry-point check with
the copy out (`en_start`). From the call, the compiled function either returns
the error byte that `imgW` decides, or writes the header and segments that
`imgW` decides into the result. -/

namespace C3.RV32.Cur

open C3.Image

variable {M : Word → BitVec 8} {ptr len ilen : Word}

variable {P R G out : Word}

/-- **The compiled `image::parse`**, called on the `len` bytes at `ptr`, an image
of `ilen` bytes, and the result at `out`, returns to its caller with the
callee-saved registers and the memory outside its frame and the result as they
were. The result holds `imgW`'s error byte and the error marker, or the
segments, the header's fields, and the success marker. -/
theorem imageParse_correct (m : Machine) (env : IEnv P R G ptr len out) (code : ICode m.mem P)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ptr) (ha2 : reg m a2 = len)
    (ha3 : reg m a3 = ilen) (hsp : reg m sp = G + 0x160) :
    match imgW m.mem ptr len ilen with
    | .error e => IErrDone R G out m.mem (reg m) e m
    | .ok (sv, entry, cnt, segs) => IOkDone R G out ilen m.mem (reg m) sv entry cnt segs m := by
  have H := ip_header m env code hpc ha0 ha1 ha2 ha3 hsp
  unfold imgW
  cases hh : hdrW m.mem ptr len ilen with
  | error e => rw [hh] at H; exact H
  | ok r =>
    obtain ⟨sv, cnt, entry, pos⟩ := r
    obtain ⟨hc1, hc16⟩ : 1 ≤ cnt.toNat ∧ cnt.toNat ≤ 16 := hdrW_cnt hh
    rw [hh] at H
    obtain ⟨m1, Mx, g, c1, st1, inv1, hpos, h2, -, -, hent, hcw⟩ := H
    obtain ⟨m2, My, g2, c2, st2, li⟩ := ip_setup env code inv1 st1 hpos h2 hent hcw hc16
    have L := lp_loop env code cnt.toNat [] pos _ (Nat.zero_add _) li st2
    rw [ok_bind_eq]
    dsimp only
    cases hr : readSegsW m.mem ptr len ilen cnt.toNat pos (BitVec.zeroExtend 32 cnt <<< 4 + 20) with
    | error e =>
      rw [hr] at L
      exact IErrDone.pre (c1.trans c2) L
    | ok q =>
      obtain ⟨segs, pos', prev⟩ := q
      rw [hr] at L
      obtain ⟨m3, Mz, g3, c3, st3, li3, hl3⟩ := L
      rw [List.nil_append] at li3 hl3
      rw [ok_bind_eq]
      dsimp only
      rcases od_setup env code li3 st3 hl3 hc1 with ⟨hp, er⟩ | ⟨hp, m4, Mw, g4, c4, st4, oi⟩
      · rw [ite_eq_left (by rw [bne_iff_ne]; exact hp)]
        exact IErrDone.pre ((c1.trans c2).trans c3) er
      · rw [ite_eq_right (by rw [hp, bne_iff_ne]; exact fun h => h rfl)]
        have O := ov_outer env code (cnt.toNat - 1) 0 (by omega) oi st4
        rw [List.drop_zero] at O
        cases ho : overlapW segs with
        | error e =>
          rw [ho] at O
          exact IErrDone.pre (((c1.trans c2).trans c3).trans c4) O
        | ok u =>
          rw [ho] at O
          obtain ⟨m5, Mv, g5, c5, st5, b5⟩ := O
          have pre := (((c1.trans c2).trans c3).trans c4).trans c5
          have E := en_start env code b5 st5
          cases he : entryW entry segs with
          | error e =>
            rw [he] at E
            exact IErrDone.pre pre E
          | ok u' =>
            rw [he] at E
            obtain ⟨n', c6, rest⟩ := E
            exact ⟨n', pre.trans c6, rest⟩

end C3.RV32.Cur
