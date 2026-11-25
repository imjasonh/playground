import C3BootProofs.Proofs.TufRoleKeysDecode

/-!
# The `keyids` loop of `RoleKeys::read`

The loop at 0x1E6 reads one key ID per pass with `next_element` and `str`,
copies it to the next slot of the `RoleKeys` at `F + 0x18`, looks it up in
the `keys` object with `get`, decodes the key that names, and at 0x6F4
writes the key's tag and bytes to the slot and raises the count. `RkI` is
the state at 0x1E6 after the entries `es`.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- The `RoleKeys` result after the threshold `t` and the entries `es`
already in the slots, and the loop's result `r` for the rest. -/
def rkThen (r : Except Nat (List RkEntry)) (t : Nat) (es : List RkEntry) : Except Nat (Nat × List RkEntry) :=
  match r with
  | .error e => .error e
  | .ok es' => .ok (t, es ++ es')

/-- The state at 0x1E6: the frame, the `RoleKeys` at `F + 0x18` with the
entries `es`, the cursor over the `AN` bytes at `AP` at `pos`, and the
registers that hold the slot pointers, the `keys` object, and the count. -/
structure RkI (M1 : Word → BitVec 8) (s out F : Word) (g0 : Fin 32 → Word) (t : Nat) (AP KQ : Word)
    (AN KL : Nat) (es : List RkEntry) (pos : Nat) (Mk : Word → BitVec 8) (g : Fin 32 → Word) : Prop where
  hO : Out M1 Mk s 3004
  hB : RkAt Mk (F + 0x18) t es
  c0 : memLoad32 Mk (F + 0xA6C) = AP
  c1 : memLoad32 Mk (F + 0xA70) = BitVec.ofNat 32 AN
  c2 : memLoad32 Mk (F + 0xA74) = BitVec.ofNat 32 pos
  hsp : g sp = F
  h27 : g 27 = out
  h19 : g 19 = F + BitVec.ofNat 32 (0x330 + 64 * es.length)
  h20 : g 20 = F + BitVec.ofNat 32 (0x530 + 4 * es.length)
  h21 : g 21 = KQ
  h18 : g 18 = BitVec.ofNat 32 KL
  h23 : g 23 = 9
  h24 : g 24 = F + 0xA6C
  h25 : g 25 = F + BitVec.ofNat 32 (0x19 + 98 * es.length)
  h26 : g 26 = BitVec.ofNat 32 (es.length + 1)
  hz : g 0 = 0
  hfr : ∀ x, x ∉ rkE → g x = g0 x

theorem rk_nr {o c l : Nat} (h : ¬(c ≤ o ∧ o < c + l)) : o < c ∨ c + l ≤ o := by
  by_cases h1 : o < c
  · exact Or.inl h1
  · exact Or.inr (Nat.le_of_not_lt fun h2 => h ⟨Nat.le_of_not_lt h1, h2⟩)

theorem rk_ra (F : Word) (o : Nat) : F + 0x18 + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (0x18 + o) :=
  add_ofNat_assoc F 0x18 o

theorem rk_w32 (M : Word → BitVec 8) (a : Word) (o : Nat) :
    w32 (fun j => M (a + BitVec.ofNat 32 j)) o = memLoad32 M (a + BitVec.ofNat 32 o) := by
  unfold w32 memLoad32
  rw [show a + BitVec.ofNat 32 o + 3 = a + BitVec.ofNat 32 (o + 3) from add_ofNat_assoc a o 3,
    show a + BitVec.ofNat 32 o + 2 = a + BitVec.ofNat 32 (o + 2) from add_ofNat_assoc a o 2,
    show a + BitVec.ofNat 32 o + 1 = a + BitVec.ofNat 32 (o + 1) from add_ofNat_assoc a o 1]

theorem rk_byte {M : Word → BitVec 8} {q : Word} {n j : Nat} {L : Bytes} (h : memBytes M q n = L) (hj : j < n) :
    M (q + BitVec.ofNat 32 j) = BitVec.ofNat 8 (L.getD j 0) := by
  subst h
  rw [memBytes_getD hj]
  exact ((BitVec.ofNat_toNat 8 _).trans (BitVec.setWidth_eq _)).symm

theorem rk_inc {F : Word} {c d e : Nat} (h : c + d = e) :
    F + BitVec.ofNat 32 c + BitVec.ofNat 32 d = F + BitVec.ofNat 32 e := by
  subst h; exact add_ofNat_assoc _ _ _

theorem rk_m1 (F : Word) (i : Nat) :
    F + BitVec.ofNat 32 (0x19 + 98 * i) + 0xFFFFFFFF = F + BitVec.ofNat 32 (0x18 + 98 * i) := by
  rw [show 0x19 + 98 * i = (0x18 + 98 * i) + 1 by omega, ← add_ofNat_assoc, BitVec.add_assoc,
    show (BitVec.ofNat 32 1 : Word) + 0xFFFFFFFF = 0 by decide]
  exact BitVec.add_zero _

theorem rk_dcE : ∀ x : Fin 32, x ∈ rkDc → x ∈ rkE := by decide

section
variable {a kv : Bytes} {k pos t : Nat} {es : List RkEntry}

theorem rkm_none (h : nextElement a pos = none) : rkThen (rkLoop a kv k pos) t es = .error 0x20 := by
  rw [rkLoop]; simp only [h]; rfl

theorem rkm_end (h : nextElement a pos = some none) : rkThen (rkLoop a kv k pos) t es = .ok (t, es) := by
  rw [rkLoop]; simp only [h, rkThen, List.append_nil]

theorem rkm_str {ep el nx : Nat} (h : nextElement a pos = some (some (ep, el, nx)))
    (hs : strBody (slice a ep el) = none) : rkThen (rkLoop a kv k pos) t es = .error 0x21 := by
  rw [rkLoop]; simp only [h, hs]; rfl

theorem rkm_k0 {ep el nx : Nat} {id : Bytes} (h : nextElement a pos = some (some (ep, el, nx)))
    (hs : strBody (slice a ep el) = some id) : rkThen (rkLoop a kv 0 pos) t es = .error 0x21 := by
  rw [rkLoop]; simp only [h, hs]; rfl

theorem rkm_long {ep el nx : Nat} {id : Bytes} (h : nextElement a pos = some (some (ep, el, nx)))
    (hs : strBody (slice a ep el) = some id) (hl : 64 < id.length) :
    rkThen (rkLoop a kv (k + 1) pos) t es = .error 0x21 := by
  rw [rkLoop]; simp only [h, hs, hl, ↓reduceIte]; rfl

theorem rkm_get {ep el nx e : Nat} {id : Bytes} (h : nextElement a pos = some (some (ep, el, nx)))
    (hs : strBody (slice a ep el) = some id) (hl : ¬64 < id.length) (hg : objGet kv id = .error e) :
    rkThen (rkLoop a kv (k + 1) pos) t es = .error e := by
  rw [rkLoop]; simp only [h, hs, hl, ↓reduceIte, hg]; rfl

theorem rkm_step {ep el nx : Nat} {id : Bytes} {v : Option (Nat × Nat)}
    (h : nextElement a pos = some (some (ep, el, nx))) (hs : strBody (slice a ep el) = some id)
    (hl : ¬64 < id.length) (hg : objGet kv id = .ok v) :
    rkThen (rkLoop a kv (k + 1) pos) t es =
      rkThen (rkLoop a kv k nx) t (es ++ [(id, v.bind fun x => rkDecode (slice kv x.1 x.2))]) := by
  rw [rkLoop]; simp only [h, hs, hl, ↓reduceIte, hg]
  cases rkLoop a kv k nx <;> simp only [rkThen, List.append_assoc, List.singleton_append]

end

section
variable {M0 M1 Md M : Word → BitVec 8} {s out F P : Word} {N : Nat} {g0 : Fin 32 → Word}

/-- A byte of the frame at `F + c` that `decode_key` leaves alone. -/
theorem RkEnv.wB (E : RkEnv M0 M1 s out F P N g0) (h : RkW s Md M) {c : Nat}
    (hc : (24 ≤ c ∧ c < 1368) ∨ (2668 ≤ c ∧ c < 2680)) :
    M (F + BitVec.ofNat 32 c) = Md (F + BitVec.ofNat 32 c) := by
  have hw := E.hsw
  have hc' : 24 ≤ c ∧ c < 2680 := by rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩
  have hs1 : Sep (F + BitVec.ofNat 32 c) 1 s 328 := by
    rw [E.Fc]; exact (tex_sepS (n := 328) (d := 304 + c) (k := 1) (by omega) (by omega)).symm
  have hs2 : Sep (F + BitVec.ofNat 32 c) 1 (s + BitVec.ofNat 32 1672) 1300 := by
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact E.fs (Or.inl (by omega)) (by omega) (by omega)
    · exact E.fs (Or.inr (by omega)) (by omega) (by omega)
  have hs3 : Sep (F + BitVec.ofNat 32 c) 1 (s + BitVec.ofNat 32 2984) 20 :=
    E.fs (Or.inl (by omega)) (by omega) (by omega)
  exact h _ hs1 hs2 hs3

/-- The tail at 0x6F4: write the key's tag and bytes to slot `es.length`,
raise the count, and go back to 0x1E6. -/
theorem rk_tail (E : RkEnv M0 M1 s out F P N g0) {Q : Post} {t AN KL nx : Nat} {AP KQ : Word}
    {es : List RkEntry} {id : Bytes} {key : Option (Nat × Bytes)} {Mk : Word → BitVec 8} {gL : Fin 32 → Word}
    (hi : es.length < 8) (hid : id.length ≤ 64) (hB : RkAt Mk (F + 0x18) t es) (hOd : Out M1 Md s 3004)
    (hKb : ∀ o < 0x540, ¬(0x318 + 64 * es.length ≤ o ∧ o < 0x318 + 64 * es.length + id.length) →
      ¬(0x518 + 4 * es.length ≤ o ∧ o < 0x518 + 4 * es.length + 4) →
      Md (F + BitVec.ofNat 32 (0x18 + o)) = Mk (F + BitVec.ofNat 32 (0x18 + o)))
    (hids : ∀ j < id.length,
      Md (F + BitVec.ofNat 32 (0x330 + 64 * es.length) + BitVec.ofNat 32 j) = BitVec.ofNat 8 (id.getD j 0))
    (hlen : memLoad32 Md (F + BitVec.ofNat 32 (0x530 + 4 * es.length)) = BitVec.ofNat 32 id.length)
    (hc0 : memLoad32 Md (F + 0xA6C) = AP) (hc1 : memLoad32 Md (F + 0xA70) = BitVec.ofNat 32 AN)
    (hc2 : memLoad32 Md (F + 0xA74) = BitVec.ofNat 32 nx)
    (hsp : gL sp = F) (h27 : gL 27 = out) (h19 : gL 19 = F + BitVec.ofNat 32 (0x330 + 64 * es.length))
    (h20 : gL 20 = F + BitVec.ofNat 32 (0x530 + 4 * es.length)) (h21 : gL 21 = KQ)
    (h18 : gL 18 = BitVec.ofNat 32 KL) (h24 : gL 24 = F + 0xA6C)
    (h25 : gL 25 = F + BitVec.ofNat 32 (0x19 + 98 * es.length))
    (h26 : gL 26 = BitVec.ofNat 32 (es.length + 1)) (hz : gL 0 = 0) (hfr : ∀ x, x ∉ rkE → gL x = g0 x)
    (hK : ∀ Mf g, RkI M1 s out F g0 t AP KQ AN KL (es ++ [(id, key)]) nx Mf g →
      WP tufRoleKeysReadCode TRK Q Mf 0x1E6 g) :
    RkK Q s F gL Md key := by
  intro g M hk g23 hW htag hKB
  have r25 : g 25 = F + BitVec.ofNat 32 (0x19 + 98 * es.length) := by rw [hk 25 (by decide)]; exact h25
  have rsp : g sp = F := by rw [hk sp (by decide)]; exact hsp
  have hO0 : Out M1 M s 3004 := hOd.trans hW.outer
  refine WP.sb rkr_at_6f4 (by rw [r25, rk_m1]; exact E.cF (by omega)) ?_
  rw [r25, rk_m1, htag]
  have hO2 : Out M1 (memStore8 M (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) (rkTag key)) s 3004 :=
    hO0.trans (E.outF (out_store8 _ _ _) (by omega))
  have hcd := E.code hO2
  refine WP.aluImm rkr_at_6f8 ?_; wn
  refine WP.aluImm rkr_at_6fc ?_; wn
  refine WP.alu rkr_at_700 ?_; wn
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 (0x19 + 98 * es.length)) (src := F + 0x55C)
    (F := s + BitVec.ofNat 32 288) (N := 0x61)
    rkr_at_702 rkr_at_706 (by decide) (by decide) (by decide) hcd.tps.bms
    (E.mcFF hcd (c := 0x19 + 98 * es.length) (d := 0x55C) (n := 0x61) (Or.inl (by omega)) (by omega) (by decide)
      (by omega) (by decide))
    (by rsimp; rw [ev0]; exact r25) (by rsimp; rw [rsp]; rfl) (by rsimp; try rfl)
    (by rsimp; rw [rsp]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (by omega)) fun m4 hm4 => ?_
  wn
  refine WP.sw rkr_at_70a (by rsimp; rw [rsp]; exact E.alF (c := 0x550) (by decide))
    (by rsimp; rw [rsp]; exact E.cF (c := 0x550) (by decide)) ?_
  wn
  refine WP.aluImm rkr_at_70e ?_; wn
  refine WP.aluImm rkr_at_710 ?_; wn
  refine WP.aluImm rkr_at_714 ?_; wn
  refine WP.aluImm rkr_at_716 ?_; wn
  refine WP.jal rkr_at_71a (by decide) ?_; wn
  refine hK _ _ ?_
  have r26 : g 26 = BitVec.ofNat 32 (es.length + 1) := by rw [hk 26 (by decide)]; exact h26
  have hfrg : ∀ x, x ∉ rkE → g x = g0 x := fun x hx => (hk x (fun h => hx (rk_dcE x h))).trans (hfr x hx)
  have hz' : g 0 = 0 := by rw [hk 0 (by decide)]; exact hz
  rw [rsp, r26]
  have hM : ∀ c, 0x18 ≤ c → c < 0xAC0 → (c < 0x18 + 98 * es.length ∨ 0x18 + 98 * es.length + 98 ≤ c) →
      (c < 0x550 ∨ 0x554 ≤ c) →
      memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + BitVec.ofNat 32 c) =
        M (F + BitVec.ofNat 32 c) := by
    intro c h1 h2 h3 h4
    have s1 : Sep (F + BitVec.ofNat 32 c) 1 (F + BitVec.ofNat 32 0x550) 4 := by
      rcases h4 with h4 | h4
      · exact rk_ff F (Or.inl (by omega)) (by omega) (by decide)
      · exact rk_ff F (Or.inr (by omega)) (by omega) (by decide)
    have s2 : Sep (F + BitVec.ofNat 32 (0x19 + 98 * es.length)) 0x61 (F + BitVec.ofNat 32 c) 1 := by
      rcases h3 with h3 | h3
      · exact rk_ff F (Or.inr (by omega)) (by omega) (by omega)
      · exact rk_ff F (Or.inl (by omega)) (by omega) (by omega)
    have s3 : Sep (F + BitVec.ofNat 32 c) 1 (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) 1 := by
      rcases h3 with h3 | h3
      · exact rk_ff F (Or.inl (by omega)) (by omega) (by omega)
      · exact rk_ff F (Or.inr (by omega)) (by omega) (by omega)
    rw [out_store32 _ (F + 1360) _ _ s1, hm4 _ (E.fs (Or.inr (by omega)) (by omega) (by decide)), copyBytes_sep s2 (Nat.le_refl _),
      out_store8 _ _ _ _ s3]
  have hT : memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) =
      rkTag key := by
    have s1 : Sep (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) 1 (F + BitVec.ofNat 32 0x550) 4 :=
      rk_ff F (Or.inl (by omega)) (by omega) (by decide)
    have s2 : Sep (F + BitVec.ofNat 32 (0x19 + 98 * es.length)) 0x61 (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) 1 :=
      rk_ff F (Or.inr (by omega)) (by omega) (by omega)
    rw [out_store32 _ (F + 1360) _ _ s1, hm4 _ (E.fs (Or.inr (by omega)) (by omega) (by decide)), copyBytes_sep s2 (Nat.le_refl _),
      memStore8_same]
  have hKy : ∀ j < 0x61,
      memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + BitVec.ofNat 32 (0x19 + 98 * es.length) + BitVec.ofNat 32 j) =
        memStore8 M (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) (rkTag key) (F + 0x55C + BitVec.ofNat 32 j) := by
    intro j hj
    rw [rk_inc (c := 0x19 + 98 * es.length) (d := j) rfl]
    have s1 : Sep (F + BitVec.ofNat 32 (0x19 + 98 * es.length + j)) 1 (F + BitVec.ofNat 32 0x550) 4 :=
      rk_ff F (Or.inl (by omega)) (by omega) (by decide)
    rw [out_store32 _ (F + 1360) _ _ s1, hm4 _ (E.fs (Or.inr (by omega)) (by omega) (by decide)),
      ← rk_inc (F := F) (c := 0x19 + 98 * es.length) (d := j) rfl, copyBytes_at hj (by decide)]
  have hMo : ∀ o < 0x540, (o < 98 * es.length ∨ 98 * es.length + 98 ≤ o) → (o < 0x538 ∨ 0x538 + 4 ≤ o) →
      memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + BitVec.ofNat 32 (0x18 + o)) =
        Md (F + BitVec.ofNat 32 (0x18 + o)) := by
    intro o ho h3 h4
    have h3' : 0x18 + o < 0x18 + 98 * es.length ∨ 0x18 + 98 * es.length + 98 ≤ 0x18 + o := by
      rcases h3 with h3 | h3
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have h4' : 0x18 + o < 0x550 ∨ 0x554 ≤ 0x18 + o := by
      rcases h4 with h4 | h4
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [hM _ (by omega) (by omega) h3' h4', E.wB hW (Or.inl ⟨by omega, by omega⟩)]
  have hCur : ∀ c, 0xA6C ≤ c → c + 4 ≤ 0xA78 →
      memLoad32 (memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1))) (F + BitVec.ofNat 32 c) =
        memLoad32 Md (F + BitVec.ofNat 32 c) := by
    intro c h1 h2
    refine memLoad32_congr fun j hj => ?_
    rw [add_ofNat_assoc, hM _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
      E.wB hW (Or.inr ⟨by omega, by omega⟩)]
  have hOf : Out M1 (memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1))) s 3004 := by
    have hcp : Out (memStore8 M (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) (rkTag key))
        (copyBytes (memStore8 M (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) (rkTag key))
          (F + BitVec.ofNat 32 (0x19 + 98 * es.length)) (F + 0x55C) 0x61)
        (F + BitVec.ofNat 32 (0x19 + 98 * es.length)) 0x61 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
    exact ((hO2.trans (E.outF hcp (by omega))).trans (hm4.widen (by decide))).trans
      (E.outF (c := 0x550) (out_store32 m4.mem (F + 1360) _) (by decide))
  have hlen' : (es ++ [(id, key)]).length = es.length + 1 := by
    rw [List.length_append, List.length_singleton]
  refine ⟨hOf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show RkB (fun o => memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + 0x18 + BitVec.ofNat 32 o)) t _
    refine RkB.push hB hi hid (fun o ho n1 n2 n3 n4 => ?_) (fun j hj => ?_) ?_ ?_ ?_
    · show _ = Mk (F + 0x18 + BitVec.ofNat 32 o)
      rw [rk_ra, hMo o ho (rk_nr n3) (rk_nr n4), hKb o ho n1 n2]
    · show memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + 0x18 + BitVec.ofNat 32 _) = _
      rw [rk_ra, hMo _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
        ← rk_inc (show 0x330 + 64 * es.length + j = 0x18 + (0x318 + 64 * es.length + j) by omega)]
      exact hids j hj
    · rw [rk_w32, rk_ra, show 0x18 + (0x518 + 4 * es.length) = 0x530 + 4 * es.length by omega, ← hlen]
      refine memLoad32_congr fun j hj => ?_
      rw [add_ofNat_assoc,
        show 0x530 + 4 * es.length + j = 0x18 + (0x518 + 4 * es.length + j) by omega,
        hMo _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    · rcases key with _ | ⟨kt, kb⟩
      · show memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + 0x18 + BitVec.ofNat 32 _) = _
        rw [rk_ra, hT]; rfl
      · obtain ⟨hkl, hkb⟩ := hKB
        refine ⟨?_, hkl, fun j hj => ?_⟩
        · show memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + 0x18 + BitVec.ofNat 32 _) = _
          rw [rk_ra, hT]; rfl
        · show memStore32 m4.mem (F + 1360) (BitVec.ofNat 32 (es.length + 1)) (F + 0x18 + BitVec.ofNat 32 _) = _
          rw [rk_ra, ← rk_inc (show 0x19 + 98 * es.length + j = 0x18 + (98 * es.length + 1 + j) by omega),
            hKy j (by omega)]
          have s1 : Sep (F + 0x55C + BitVec.ofNat 32 j) 1 (F + BitVec.ofNat 32 (0x18 + 98 * es.length)) 1 := by
            rw [show F + 0x55C + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x55C + j) from add_ofNat_assoc F 0x55C j]
            exact rk_ff F (Or.inr (by omega)) (by omega) (by omega)
          rw [out_store8 _ _ _ _ s1]
          exact rk_byte hkb hj
    · rw [rk_w32, rk_ra]
      exact memLoad32_store32_same _ _ _
  · exact (hCur 0xA6C (by decide) (by decide)).trans hc0
  · exact (hCur 0xA70 (by decide) (by decide)).trans hc1
  · exact (hCur 0xA74 (by decide) (by decide)).trans hc2
  · rsimp; exact rsp
  · rsimp; rw [hk 27 (by decide)]; exact h27
  · rsimp; rw [ev_add, hk 19 (by decide), h19, hlen']
    exact rk_inc (d := 64) (by omega)
  · rsimp; rw [ev_add, hk 20 (by decide), h20, hlen']; exact rk_inc (d := 4) (by omega)
  · rsimp; rw [hk 21 (by decide)]; exact h21
  · rsimp; rw [hk 18 (by decide)]; exact h18
  · rsimp; exact g23
  · rsimp; rw [hk 24 (by decide)]; exact h24
  · rsimp; rw [ev_add, r25, hlen']; exact rk_inc (d := 98) (by omega)
  · rsimp; rw [hlen']; exact (BitVec.ofNat_add _ _).symm
  · rsimp <;> exact hz'
  · keepz E.hz0


theorem rk_cnt {n : Nat} (h : n < 2 ^ 31) : branchTaken .beq (BitVec.ofNat 32 (n + 1)) 9 = decide (n + 1 = 9) :=
  br_beq (by omega) (by decide)

theorem rk_len {n : Nat} (h : n < 2 ^ 32) : branchTaken .bgeu (BitVec.ofNat 32 n) 0x41 = !decide (n < 65) :=
  br_bgeu h (by decide)

/-- `copy_from_slice` from bytes outside the frame into the frame. -/
theorem RkEnv.mcFX (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} (hc : RkCode M) {c n : Nat} {q : Word}
    (hc0 : 16 ≤ c) (hcn : c + n ≤ 0xAC0) (hq : Sep s 3056 q n) (hqw : q.toNat + n ≤ 0x40000000) :
    McEnv M BMB (F + BitVec.ofNat 32 c) q (s + BitVec.ofNat 32 288) n := by
  have hd : Sep (F + BitVec.ofNat 32 c) n q n := by rw [E.Fc]; exact hq.sub (by omega)
  exact ⟨hc.tps.bmb, E.lowF hcn (by decide) (by decide), E.lowS (by decide) (by decide) (by decide),
    E.fs (Or.inr (by omega)) hcn (by decide), (hq.sub (c := 288) (l := 16) (by decide)).symm, hd,
    E.alS (by decide), by have := E.wS (d := 288) (k := 16) (by decide); omega,
    by have := E.wF hcn; omega, by omega⟩

set_option maxHeartbeats 4000000 in
/-- From 0x20A, after `next_element` found the element at `ep`: the key ID,
its copy into slot `es.length`, and its key in `keys`. -/
theorem rk_20a (E : RkEnv M0 M1 s out F P N g0) {t AN KL k ep el nx : Nat} {AP KQ : Word}
    {es : List RkEntry} {Mk M2 : Word → BitVec 8} {g : Fin 32 → Word}
    (hA0 : AP.toNat ≠ 0) (hAN : AP.toNat + AN ≤ 0x40000000) (hAS : Sep s 3056 AP AN)
    (hK0 : KQ.toNat ≠ 0) (hKN : KQ.toNat + KL ≤ 0x40000000) (hKS : Sep s 3056 KQ KL)
    (hk8 : es.length + k = 8)
    (hne : nextElement (memBytes M0 AP AN) ep = some (some (ep, el, nx)))
    (hel : ep + el ≤ AN)
    (hB : RkAt Mk (F + 0x18) t es) (hO2 : Out M1 M2 s 3004)
    (hKp : ∀ c, 0x18 ≤ c → c < 0x75C → M2 (F + BitVec.ofNat 32 c) = Mk (F + BitVec.ofNat 32 c))
    (hc0 : memLoad32 M2 (F + 0xA6C) = AP) (hc1 : memLoad32 M2 (F + 0xA70) = BitVec.ofNat 32 AN)
    (hc2 : memLoad32 M2 (F + 0xA74) = BitVec.ofNat 32 nx)
    (t3 : memLoad32 M2 (F + 0x764) = BitVec.ofNat 32 el)
    (ha1 : g a1 = AP + BitVec.ofNat 32 ep)
    (hsp : g sp = F) (h27 : g 27 = out) (h19 : g 19 = F + BitVec.ofNat 32 (0x330 + 64 * es.length))
    (h20 : g 20 = F + BitVec.ofNat 32 (0x530 + 4 * es.length)) (h21 : g 21 = KQ)
    (h18 : g 18 = BitVec.ofNat 32 KL) (h23 : g 23 = 9) (h24 : g 24 = F + 0xA6C)
    (h25 : g 25 = F + BitVec.ofNat 32 (0x19 + 98 * es.length))
    (h26 : g 26 = BitVec.ofNat 32 (es.length + 1)) (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    (ih : ∀ k', k = k' + 1 → ∀ es' Mf g', es'.length + k' = 8 →
      RkI M1 s out F g0 t AP KQ AN KL es' nx Mf g' →
      WP tufRoleKeysReadCode TRK
        (rkQ M0 s out g0 (rkThen (rkLoop (memBytes M0 AP AN) (memBytes M0 KQ KL) k' nx) t es')) Mf 0x1E6 g') :
    WP tufRoleKeysReadCode TRK
      (rkQ M0 s out g0 (rkThen (rkLoop (memBytes M0 AP AN) (memBytes M0 KQ KL) k ep) t es)) M2 0x20A g := by
  have hsl : slice (memBytes M0 AP AN) ep el = memBytes M0 (AP + BitVec.ofNat 32 ep) el :=
    tuf_memBytes_drop_take hel
  have hSe : Sep s 3056 (AP + BitVec.ofNat 32 ep) el := hAS.subR hel
  refine WP.lw rkr_at_20a (by rw [hsp]; exact E.alF (c := 0x764) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_20e ?_; wn
  have hc2' := E.code hO2
  refine WP.callStr (tb := TPM_JS) (out := F + 0x75C) (p := AP + BitVec.ofNat 32 ep) (n := el)
    rkr_at_212 rkr_at_216 (by decide) (by decide) (by decide) hc2'.pm.str (by rsimp; rw [ev_add, hsp])
    (by rsimp; exact ha1) (by rsimp; rw [hsp, t3]) (by omega)
    (E.alF (c := 0x75C) (by decide)) (E.lowF (by decide) (by decide) (by decide)) (E.cF (by decide))
    fun m3 hS => ?_
  wn
  rw [E.bytes hO2 hSe, tex_strRes] at hS
  generalize m3.mem = M3 at hS
  have hO3 : Out M1 M3 s 3004 := hO2.trans (E.outF (c := 0x75C) (l := 8) hS.out (by decide))
  refine WP.lw rkr_at_21a (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
  rcases hsb : strBody (memBytes M0 (AP + BitVec.ofNat 32 ep) el) with _ | id <;> rw [hsb] at hS <;>
    simp only [Option.map_none, Option.map_some] at hS
  · obtain ⟨-, s1, s2⟩ := hS
    refine WP.branch rkr_at_21e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, s1] at eb; exact absurd eb (by decide)
    rw [rkm_str hne (by rw [hsl]; exact hsb)]
    exact rk_8e4 E hO3 (by rsimp; exact h27) (by rsimp; exact hsp)
      (by rw [show F + 0x760 = F + 0x75C + 4 by rw [BitVec.add_assoc]; rfl]; exact s2) (by keepz E.hz0)
  obtain ⟨hfs3, s1, s2⟩ := hS
  obtain ⟨hid1, hidl⟩ := rk_strB hsb
  have hq' : AP + BitVec.ofNat 32 ep + 1 = AP + BitVec.ofNat 32 (ep + 1) := add_ofNat_assoc AP ep 1
  have hq0 := nx_q0 hA0 (n := AN) (pos := ep + 1) (by omega) (by omega)
  have hsb' : strBody (slice (memBytes M0 AP AN) ep el) = some id := by rw [hsl]; exact hsb
  refine WP.branch rkr_at_21e (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, s1, hq', hq0] at eb; exact absurd eb (by decide)
  refine WP.branch rkr_at_222 (fun eb => ?_) (fun eb => ?_) <;> wn
  · (try rsimp at eb); rw [h26, h23, rk_cnt (by omega)] at eb
    have hk0 : k = 0 := by have := of_decide_eq_true eb; omega
    subst hk0
    rw [rkm_k0 hne hsb']
    exact rk_930 E hO3 (by rsimp; exact h27) (by rsimp; exact hsp) (by keepz E.hz0)
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
    (try rsimp at eb); rw [h26, h23, rk_cnt (by omega)] at eb; have := of_decide_eq_false eb; omega⟩
  refine WP.lw rkr_at_226 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_22a ?_; wn
  have s2' : memLoad32 M3 (F + 0x760) = BitVec.ofNat 32 id.length := by
    rw [show F + 0x760 = F + 0x75C + 4 by rw [BitVec.add_assoc]; rfl]; exact s2
  by_cases hl : 64 < id.length
  · refine WP.branch rkr_at_22e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, s2', ev0, rk_len (by omega)] at eb; have := not_dec_false eb; omega
    rw [rkm_long hne hsb' hl]
    exact rk_930 E hO3 (by rsimp; exact h27) (by rsimp; exact hsp) (by keepz E.hz0)
  refine WP.branch rkr_at_22e (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, s2', ev0, rk_len (by omega)] at eb; exact (not_dec_true eb) (by omega)
  refine WP.alu rkr_at_232 ?_; wn
  refine WP.alu rkr_at_234 ?_; wn
  refine WP.alu rkr_at_236 ?_; wn
  refine WP.alu rkr_at_238 ?_; wn
  have hSq : Sep s 3056 (AP + BitVec.ofNat 32 ep + 1) id.length := by rw [hq']; exact hAS.subR (by omega)
  have hqw : (AP + BitVec.ofNat 32 ep + 1).toNat + id.length ≤ 0x40000000 := by
    rw [hq', tex_toNat (by omega)]; omega
  have hc3 := E.code hO3
  refine WP.callCfs (dst := F + BitVec.ofNat 32 (0x330 + 64 * es.length)) (src := AP + BitVec.ofNat 32 ep + 1)
    (F := s + BitVec.ofNat 32 288) (N := id.length) rkr_at_23a rkr_at_23e (by decide) (by decide)
    hc3.tps.bcw hc3.tps.bms (E.mcFX hc3 (by omega) (by omega) hSq hqw) (by rsimp; rw [ev0]; exact h19)
    (by rsimp; rw [ev0, hsp, s2']) (by rsimp; rw [ev0, hsp, s1]) (by rsimp; rw [ev0, hsp, s2'])
    (by rsimp; rw [hsp]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (by omega)) fun m4 hm4 => ?_
  wn
  refine WP.sw rkr_at_242 (by rsimp; rw [h20, add_lit_zero]; exact E.alF (by omega))
    (by rsimp; rw [h20, add_lit_zero]; exact E.cF (by omega)) ?_
  wn
  have e5 : memStore32 m4.mem (g 20 + 0) (memLoad32 M3 (g sp + 1888)) =
      memStore32 m4.mem (F + BitVec.ofNat 32 (0x530 + 4 * es.length)) (BitVec.ofNat 32 id.length) := by
    rw [h20, add_lit_zero, hsp, s2']
  rw [e5]
  have hO4 : Out M1 m4.mem s 3004 := by
    have hcp : Out M3 (copyBytes M3 (F + BitVec.ofNat 32 (0x330 + 64 * es.length)) (AP + BitVec.ofNat 32 ep + 1)
        id.length) (F + BitVec.ofNat 32 (0x330 + 64 * es.length)) id.length :=
      fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
    exact (hO3.trans (E.outF hcp (by omega))).trans (hm4.widen (by decide))
  have hO5 : Out M1 (memStore32 m4.mem (F + BitVec.ofNat 32 (0x530 + 4 * es.length)) (BitVec.ofNat 32 id.length))
      s 3004 := hO4.trans (E.outF (out_store32 _ _ _) (by omega))
  have hl5 : memLoad32 (memStore32 m4.mem (F + BitVec.ofNat 32 (0x530 + 4 * es.length))
      (BitVec.ofNat 32 id.length)) (F + BitVec.ofNat 32 (0x530 + 4 * es.length)) = BitVec.ofNat 32 id.length :=
    memLoad32_store32_same _ _ _
  generalize hM5 : memStore32 m4.mem (F + BitVec.ofNat 32 (0x530 + 4 * es.length)) (BitVec.ofNat 32 id.length) = M5
    at hO5 hl5 ⊢
  refine WP.aluImm rkr_at_246 ?_; wn
  refine WP.alu rkr_at_24a ?_; wn
  refine WP.alu rkr_at_24c ?_; wn
  refine WP.alu rkr_at_24e ?_; wn
  refine WP.alu rkr_at_250 ?_; wn
  have hc5 := E.code hO5
  have hPS := tpm_parseSep E.hsw E.hro
  have hgs : GetSep (s + BitVec.ofNat 32 76) 228 TPM_JG := by
    have := (hPS.sub (c := 76) (l := 228) (by decide)).get
    rwa [show TPM_JP + 0xFFFFF372 = TPM_JG by decide] at this
  refine WP.callGet (tb := TPM_JG) (p := KQ) (kq := AP + BitVec.ofNat 32 ep + 1) (out := F + 0x75C)
    (s := s + BitVec.ofNat 32 76) (n := KL) (kl := id.length) rkr_at_252 rkr_at_256 (by decide) (by decide)
    (by decide) hc5.pm.get (by rsimp; rw [ev_add, hsp]) (by rsimp; rw [ev0]; exact h21) (by rsimp; rw [ev0]; exact h18)
    (by rsimp; rw [ev0, hsp, s1]) (by rsimp; rw [ev0, hsp, s2'])
    (by rsimp; rw [hsp]; exact (E.sp 76 (by decide)).symm) (E.alS (by decide)) (E.alF (c := 0x75C) (by decide))
    (by have := E.wS (d := 76) (k := 228) (by decide); omega) (by omega) hK0 (by omega) hgs
    (hKS.sub (by decide)) (hSq.sub (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.cS (by decide)) (E.cF (by decide)) fun m6 hG => ?_
  wn
  rw [E.bytes hO5 hKS, E.bytes hO5 hSq, hid1] at hG
  generalize m6.mem = M6 at hG
  obtain ⟨Mb, hOb, hGR⟩ := hG
  have hO6 : Out M1 M6 s 3004 :=
    hO5.trans ((Out.upK rfl hOb (by decide)).trans (E.outF (c := 0x75C) (l := 12) hGR.out (by decide)))
  have hch : ∀ x, Sep x 1 (F + 0x75C) 12 → Sep x 1 (s + BitVec.ofNat 32 76) 228 →
      Sep x 1 (F + BitVec.ofNat 32 (0x530 + 4 * es.length)) 4 → Sep x 1 (s + BitVec.ofNat 32 288) 16 →
      M6 x = copyBytes M3 (F + BitVec.ofNat 32 (0x330 + 64 * es.length)) (AP + BitVec.ofNat 32 ep + 1)
        id.length x := by
    intro x h1 h2 h3 h4
    rw [hGR.out x h1, hOb x h2, ← hM5, out_store32 _ _ _ x h3, hm4 x h4]
  have hfb : ∀ c, 0x18 ≤ c → c < 0xAC0 → (c + 1 ≤ 0x75C ∨ 0x768 ≤ c) →
      (c + 1 ≤ 0x330 + 64 * es.length ∨ 0x330 + 64 * es.length + id.length ≤ c) →
      (c + 1 ≤ 0x530 + 4 * es.length ∨ 0x534 + 4 * es.length ≤ c) → M6 (F + BitVec.ofNat 32 c) = M2 (F + BitVec.ofNat 32 c) := by
    intro c h0 h1 h2 h3 h4
    rw [hch _ (rk_ff F h2 (by omega) (by decide)) (E.fs (Or.inr (by omega)) (by omega) (by decide))
      (rk_ff F (by rcases h4 with h | h; exact Or.inl h; exact Or.inr (by omega)) (by omega) (by omega)) (E.fs (Or.inr (by omega)) (by omega) (by decide)),
      copyBytes_sep (rk_ff F (c := 0x330 + 64 * es.length) (n := id.length) (d := c) (k := 1)
        (by rcases h3 with h | h; exact Or.inr h; exact Or.inl h) (by omega) (by omega)) (Nat.le_refl _)]
    refine hfs3 _ (rk_ff F (d := 0x75C) (k := 8) ?_ (by omega) (by decide))
    rcases h2 with h | h; exact Or.inl h; exact Or.inr (by omega)
  have hKb6 : ∀ o < 0x540, ¬(0x318 + 64 * es.length ≤ o ∧ o < 0x318 + 64 * es.length + id.length) →
      ¬(0x518 + 4 * es.length ≤ o ∧ o < 0x518 + 4 * es.length + 4) →
      M6 (F + BitVec.ofNat 32 (0x18 + o)) = Mk (F + BitVec.ofNat 32 (0x18 + o)) := by
    intro o ho n1 n2
    have r1 := rk_nr n1
    have r2 := rk_nr n2
    rw [hfb _ (by omega) (by omega) (Or.inl (by omega))
      (by rcases r1 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      (by rcases r2 with h | h; exact Or.inl (by omega); exact Or.inr (by omega)), hKp _ (by omega) (by omega)]
  have hids6 : ∀ j < id.length,
      M6 (F + BitVec.ofNat 32 (0x330 + 64 * es.length) + BitVec.ofNat 32 j) = BitVec.ofNat 8 (id.getD j 0) := by
    intro j hj
    have ea : F + BitVec.ofNat 32 (0x330 + 64 * es.length) + BitVec.ofNat 32 j =
        F + BitVec.ofNat 32 (0x330 + 64 * es.length + j) := add_ofNat_assoc _ _ _
    rw [hch _ (by rw [ea]; exact rk_ff F (d := 0x75C) (k := 12) (Or.inl (by omega)) (by omega) (by decide))
      (by rw [ea]; exact E.fs (Or.inr (by omega)) (by omega) (by decide))
      (by rw [ea]; exact rk_ff F (Or.inl (by omega)) (by omega) (by omega))
      (by rw [ea]; exact E.fs (Or.inr (by omega)) (by omega) (by decide)),
      copyBytes_at hj (by omega), E.agree hO3 _ (sep_pt hSq hj)]
    exact rk_byte hid1 hj
  have hlen6 : memLoad32 M6 (F + BitVec.ofNat 32 (0x530 + 4 * es.length)) = BitVec.ofNat 32 id.length :=
    (hGR.out.load32 (rk_ff F (c := 0x75C) (n := 12) (Or.inr (by omega)) (by decide) (by omega))).trans
      ((hOb.load32 (E.fs (Or.inr (by omega)) (by omega) (by decide)).symm).trans hl5)
  have hcw : ∀ c, 0xA6C ≤ c → c + 4 ≤ 0xA78 →
      memLoad32 M6 (F + BitVec.ofNat 32 c) = memLoad32 M2 (F + BitVec.ofNat 32 c) := by
    intro c h1 h2
    refine memLoad32_congr fun j hj => ?_
    rw [add_ofNat_assoc]
    exact hfb _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hc0' : memLoad32 M6 (F + 0xA6C) = AP := (hcw 0xA6C (by decide) (by decide)).trans hc0
  have hc1' : memLoad32 M6 (F + 0xA70) = BitVec.ofNat 32 AN := (hcw 0xA70 (by decide) (by decide)).trans hc1
  have hc2' : memLoad32 M6 (F + 0xA74) = BitVec.ofNat 32 nx := (hcw 0xA74 (by decide) (by decide)).trans hc2
  have hlk : ∀ key : Option (Nat × Bytes), (es ++ [(id, key)]).length + k = 8 := fun _ => by
    simp only [List.length_append, List.length_singleton]; omega
  refine WP.lbu rkr_at_25a ?_; wn
  rcases hg : objGet (memBytes M0 KQ KL) id with e | v <;> rw [hg] at hGR <;>
    simp only [getRes, Except.map] at hGR
  · obtain ⟨-, b0, b1⟩ := hGR
    refine WP.branch rkr_at_25e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, b0] at eb; exact absurd eb (by decide)
    rw [rkm_get hne hsb' hl hg]
    exact rk_94e E hO6 (by rsimp; exact h27) (by rsimp; exact hsp)
      (by rw [show F + 0x75D = F + 0x75C + 1 by rw [BitVec.add_assoc]; rfl]; exact b1) (by keepz E.hz0)
  rcases v with _ | ⟨vp, vl⟩ <;> simp only [Option.map_none, Option.map_some] at hGR
  · obtain ⟨-, b0, b1⟩ := hGR
    have b1' : memLoad32 M6 (F + 0x760) = 0 := by
      rw [show F + 0x760 = F + 0x75C + 4 by rw [BitVec.add_assoc]; rfl]; exact b1
    refine WP.branch rkr_at_25e (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, b0] at eb; exact absurd eb (by decide)
    refine WP.lw rkr_at_262 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
    refine WP.aluImm rkr_at_266 ?_; wn
    refine WP.branch rkr_at_26a (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, b1'] at eb; exact absurd eb (by decide)
    rw [rkm_step hne hsb' hl hg]
    exact rk_tail (key := none) E (by omega) (by omega) hB hO6 hKb6 hids6 hlen6 hc0' hc1' hc2'
      (by rsimp; exact hsp) (by rsimp; exact h27) (by rsimp; exact h19) (by rsimp; exact h20)
      (by rsimp; exact h21) (by rsimp; exact h18) (by rsimp; exact h24) (by rsimp; exact h25)
      (by rsimp; exact h26) (by rsimp) (by keepz E.hz0)
      (fun Mf g' hI => ih k rfl _ Mf g' (hlk none) hI) _ _ (fun _ _ => rfl) (by rsimp; exact h23) RkW.refl
      (by rsimp) trivial
  · obtain ⟨-, b0, b1, b2⟩ := hGR
    have hv := objGet_val hg
    rw [memBytes_length] at hv
    have b1' : memLoad32 M6 (F + 0x760) = KQ + BitVec.ofNat 32 vp := by
      rw [show F + 0x760 = F + 0x75C + 4 by rw [BitVec.add_assoc]; rfl]; exact b1
    have b2' : memLoad32 M6 (F + 0x764) = BitVec.ofNat 32 vl := by
      rw [show F + 0x764 = F + 0x75C + 8 by rw [BitVec.add_assoc]; rfl]; exact b2
    have hv0 := nx_q0 hK0 (n := KL) (pos := vp) (by omega) hv.1
    refine WP.branch rkr_at_25e (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, b0] at eb; exact absurd eb (by decide)
    refine WP.lw rkr_at_262 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
    refine WP.aluImm rkr_at_266 ?_; wn
    refine WP.branch rkr_at_26a (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, b1', hv0] at eb; exact absurd eb (by decide)
    have hkey : (some (vp, vl)).bind (fun x => rkDecode (slice (memBytes M0 KQ KL) x.1 x.2)) =
        rkDecode (memBytes M0 (KQ + BitVec.ofNat 32 vp) vl) := by
      show rkDecode (slice (memBytes M0 KQ KL) vp vl) = _
      rw [show slice (memBytes M0 KQ KL) vp vl = _ from tuf_memBytes_drop_take hv.2]
    rw [rkm_step hne hsb' hl hg, hkey]
    have hvt : (KQ + BitVec.ofNat 32 vp).toNat = KQ.toNat + vp := tex_toNat (by omega)
    exact rk_26e E hO6 RkW.refl (by rsimp) (by rsimp; exact hsp) (by rsimp; exact h24)
      (fun _ _ => rfl) (by rsimp; rw [hsp, b1']) (by rsimp) (by rsimp; exact h23) b2'
      (by rw [hvt]; omega) (by rw [hvt]; omega) (hKS.subR hv.2)
      (rk_tail E (by omega) (by omega) hB hO6 hKb6 hids6 hlen6 hc0' hc1' hc2'
        (by rsimp; exact hsp) (by rsimp; exact h27) (by rsimp; exact h19) (by rsimp; exact h20)
        (by rsimp; exact h21) (by rsimp; exact h18) (by rsimp; exact h24) (by rsimp; exact h25)
        (by rsimp; exact h26) (by rsimp) (by keepz E.hz0)
        (fun Mf g' hI => ih k rfl _ Mf g' (hlk _) hI))


set_option maxHeartbeats 4000000 in
/-- One pass of the loop at 0x1E6, given the passes after it. -/
theorem rk_1e6 (E : RkEnv M0 M1 s out F P N g0) {t AN KL k pos : Nat} {AP KQ : Word}
    {es : List RkEntry} {Mk : Word → BitVec 8} {g : Fin 32 → Word}
    (hA0 : AP.toNat ≠ 0) (hAN : AP.toNat + AN ≤ 0x40000000) (hAS : Sep s 3056 AP AN)
    (hK0 : KQ.toNat ≠ 0) (hKN : KQ.toNat + KL ≤ 0x40000000) (hKS : Sep s 3056 KQ KL)
    (hk8 : es.length + k = 8) (hpos : pos ≤ AN) (hI : RkI M1 s out F g0 t AP KQ AN KL es pos Mk g)
    (ih : ∀ k', k = k' + 1 → ∀ nx, nx ≤ AN → ∀ es' Mf g', es'.length + k' = 8 →
      RkI M1 s out F g0 t AP KQ AN KL es' nx Mf g' →
      WP tufRoleKeysReadCode TRK
        (rkQ M0 s out g0 (rkThen (rkLoop (memBytes M0 AP AN) (memBytes M0 KQ KL) k' nx) t es')) Mf 0x1E6 g') :
    WP tufRoleKeysReadCode TRK
      (rkQ M0 s out g0 (rkThen (rkLoop (memBytes M0 AP AN) (memBytes M0 KQ KL) k pos) t es)) Mk 0x1E6 g := by
  obtain ⟨hO, hB, c0, c1, c2, hsp, h27, h19, h20, h21, h18, h23, h24, h25, h26, -, hfr⟩ := hI
  have hc := E.code hO
  have hPS := tpm_parseSep E.hsw E.hro
  have e8 : F + 0xA6C + 8 = F + BitVec.ofNat 32 0xA74 := by rw [BitVec.add_assoc]; rfl
  refine WP.aluImm rkr_at_1e6 ?_; wn
  refine WP.aluImm rkr_at_1ea ?_; wn
  refine WP.aluImm rkr_at_1ee ?_; wn
  refine WP.callNextElement (tb := TPM_JNE) (out := F + 0x75C) (c := F + 0xA6C)
    (s := s + BitVec.ofNat 32 156) (p := AP) (n := AN) (pos := pos) rkr_at_1f2 rkr_at_1f6 (by decide)
    (by decide) (by decide) hc.pm.ne hc.pm.ri (by rsimp; rw [ev_add, hsp])
    (by rsimp; rw [ev_add, ev_add, hsp, BitVec.add_assoc]; rfl)
    (by rsimp; rw [hsp]; exact (E.sp 156 (by decide)).symm) (E.alS (by decide))
    (E.alF (c := 0x75C) (by decide)) (E.alF (c := 0xA6C) (by decide)) c0
    (by rw [BitVec.add_assoc]; exact c1) (by rw [BitVec.add_assoc]; exact c2)
    (by omega) (by omega) hA0 (by omega)
    (by rw [show TPM_JNE + 0xFFFFF7E0 = TPM_JG + 0xFFFFF616 by decide]; exact hPS.2.ri.sub (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (hAS.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (rk_ff F (c := 0x75C) (n := 12) (d := 0xA6C) (k := 12) (Or.inl (by decide)) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.cS (by decide)) (E.cF (by decide)) (E.cF (by decide)) fun m2 hR => ?_
  wn
  rw [E.bytes hO hAS] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hER⟩ := hR
  have hE2 : ∀ c, 0x18 ≤ c → c < 0xAC0 → (c + 1 ≤ 0x75C ∨ 0x768 ≤ c) → (c + 1 ≤ 0xA74 ∨ 0xA78 ≤ c) →
      M2 (F + BitVec.ofNat 32 c) = Mk (F + BitVec.ofNat 32 c) := by
    intro c h0 h1 h2 h3
    have h2' : c + 1 ≤ 0x75C ∨ 0x75C + 12 ≤ c := by rcases h2 with h | h; exact Or.inl h; exact Or.inr (by omega)
    have h3' : c + 1 ≤ 0xA74 ∨ 0xA74 + 4 ≤ c := by rcases h3 with h | h; exact Or.inl h; exact Or.inr (by omega)
    have s3 : Sep (F + BitVec.ofNat 32 c) 1 (F + 0xA6C + 8) 4 := by
      rw [e8]; exact rk_ff F (d := 0xA74) (k := 4) h3' (by omega) (by decide)
    rw [hER.out (rk_ff F (d := 0x75C) (k := 12) h2' (by omega) (by decide)) s3,
      hOa _ (E.fs (Or.inr (by omega)) (by omega) (by decide))]
  have hO2 : Out M1 M2 s 3004 := by
    refine hO.trans fun x hx => ?_
    have hx1 : Sep x 1 (F + 0x75C) 12 := by
      have := hx.subR (c := 304 + 0x75C) (l := 12) (by decide)
      rw [← E.Fc] at this; exact this
    have hx2 : Sep x 1 (F + 0xA6C + 8) 4 := by
      have := hx.subR (c := 304 + 0xA74) (l := 4) (by decide)
      rw [← E.Fc] at this; rw [e8]; exact this
    rw [hER.out hx1 hx2, hOa x (hx.subR (c := 156) (l := 148) (by decide))]
  have hKp : ∀ c, 0x18 ≤ c → c < 0x75C → M2 (F + BitVec.ofNat 32 c) = Mk (F + BitVec.ofNat 32 c) :=
    fun c h0 h1 => hE2 c h0 (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hcw : ∀ c, 0xA6C ≤ c → c + 4 ≤ 0xA74 →
      memLoad32 M2 (F + BitVec.ofNat 32 c) = memLoad32 Mk (F + BitVec.ofNat 32 c) := by
    intro c h1 h2
    refine memLoad32_congr fun j hj => ?_
    rw [add_ofNat_assoc]
    exact hE2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  have hc0 : memLoad32 M2 (F + 0xA6C) = AP := (hcw 0xA6C (by decide) (by decide)).trans c0
  have hc1 : memLoad32 M2 (F + 0xA70) = BitVec.ofNat 32 AN := (hcw 0xA70 (by decide) (by decide)).trans c1
  refine WP.lbu rkr_at_1fa ?_; wn
  rcases hne : nextElement (memBytes M0 AP AN) pos with _ | _ | ⟨ep, el, nx⟩ <;> rw [hne] at hER <;>
    simp only [elemRes, Option.map_none, Option.map_some] at hER
  · obtain ⟨-, t1, t2⟩ := hER
    refine WP.branch rkr_at_1fe (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    rw [rkm_none hne]
    exact rk_94e E hO2 (by rsimp; exact h27) (by rsimp; exact hsp)
      (by rw [show F + 0x75D = F + 0x75C + 1 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
  · obtain ⟨-, t1, t2⟩ := hER
    refine WP.branch rkr_at_1fe (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw rkr_at_202 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
    refine WP.branch rkr_at_206 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb)
      rw [hsp, show F + 0x760 = F + 0x75C + 4 by rw [BitVec.add_assoc]; rfl, t2] at eb; exact absurd eb (by decide)
    rw [rkm_end hne]
    refine rk_954 E hO2 (by rsimp; exact h27) (by rsimp; exact hsp) (by keepz E.hz0) ?_
    refine RkB.congr (b' := fun o => M2 (F + 0x18 + BitVec.ofNat 32 o)) hB fun o ho => ?_
    show M2 (F + 0x18 + BitVec.ofNat 32 o) = Mk (F + 0x18 + BitVec.ofNat 32 o)
    rw [rk_ra]; exact hKp _ (by omega) (by omega)
  · obtain ⟨-, t1, t2, t3, t4⟩ := hER
    obtain ⟨rfl, hpx, hel, hle, hxN⟩ := nextElement_lt hne
    rw [memBytes_length] at hle hxN
    have t2' : memLoad32 M2 (F + 0x760) = AP + BitVec.ofNat 32 ep := by
      rw [show F + 0x760 = F + 0x75C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    have t3' : memLoad32 M2 (F + 0x764) = BitVec.ofNat 32 el := by
      rw [show F + 0x764 = F + 0x75C + 8 by rw [BitVec.add_assoc]; rfl]; exact t3
    have hq0 := nx_q0 hA0 (n := AN) (pos := ep) (by omega) (by omega)
    refine WP.branch rkr_at_1fe (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw rkr_at_202 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
    refine WP.branch rkr_at_206 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, t2', hq0] at eb; exact absurd eb (by decide)
    exact rk_20a E hA0 hAN hAS hK0 hKN hKS hk8 hne hle hB hO2 hKp hc0 hc1 (by rw [show F + 0xA74 = F + 0xA6C + 8 by rw [BitVec.add_assoc]; rfl]; exact t4) t3'
      (by rsimp; rw [hsp, t2']) (by rsimp; exact hsp) (by rsimp; exact h27) (by rsimp; exact h19)
      (by rsimp; exact h20) (by rsimp; exact h21) (by rsimp; exact h18) (by rsimp; exact h23)
      (by rsimp; exact h24) (by rsimp; exact h25) (by rsimp; exact h26) (by keepz E.hz0)
      (fun k' h => ih k' h nx hxN)

/-- The loop at 0x1E6 after the entries `es`, with `k` passes left. -/
theorem rk_loop (E : RkEnv M0 M1 s out F P N g0) {t AN KL : Nat} {AP KQ : Word}
    (hA0 : AP.toNat ≠ 0) (hAN : AP.toNat + AN ≤ 0x40000000) (hAS : Sep s 3056 AP AN)
    (hK0 : KQ.toNat ≠ 0) (hKN : KQ.toNat + KL ≤ 0x40000000) (hKS : Sep s 3056 KQ KL) :
    ∀ k pos (es : List RkEntry) Mk g, es.length + k = 8 → pos ≤ AN →
      RkI M1 s out F g0 t AP KQ AN KL es pos Mk g →
      WP tufRoleKeysReadCode TRK
        (rkQ M0 s out g0 (rkThen (rkLoop (memBytes M0 AP AN) (memBytes M0 KQ KL) k pos) t es)) Mk 0x1E6 g := by
  intro k
  induction k with
  | zero =>
    intro pos es Mk g hk hp hI
    exact rk_1e6 E hA0 hAN hAS hK0 hKN hKS hk hp hI fun k' h => absurd h (by omega)
  | succ k ih =>
    intro pos es Mk g hk hp hI
    exact rk_1e6 E hA0 hAN hAS hK0 hKN hKS hk hp hI fun k' h nx hnx es' Mf g' hk' hI' => by
      cases h; exact ih nx es' Mf g' hk' hnx hI'

end

end C3.RV32
