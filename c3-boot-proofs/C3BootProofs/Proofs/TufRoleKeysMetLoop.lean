import C3BootProofs.Proofs.TufRoleKeysMetVer
import C3BootProofs.Proofs.TufRoleKeysLoop

/-!
# `met`'s loop over the key slots

The loop head is at 0x78. Before slot `j`, the frame words at `F + 0x10`
to `F + 0x24` hold the message, the count `c` of keys that checked, `4 c`,
and the signatures, the word at `F + 0xC` points past the `c` counted slot
numbers at `F + 0x28`, and those slot numbers name distinct keys, each with
a signature that checks.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- The frame words at the loop head, for the counted slots `cs`. -/
def RmHM (Mk : Word → BitVec 8) (F MP SP : Word) (ML SL : Nat) (cs : List Nat) : Prop :=
  memLoad32 Mk (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML ∧ memLoad32 Mk (F + BitVec.ofNat 32 0x14) = MP ∧
    memLoad32 Mk (F + BitVec.ofNat 32 0x18) = BitVec.ofNat 32 cs.length ∧
    memLoad32 Mk (F + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 (4 * cs.length) ∧
    memLoad32 Mk (F + BitVec.ofNat 32 0x20) = BitVec.ofNat 32 SL ∧ memLoad32 Mk (F + BitVec.ofNat 32 0x24) = SP ∧
    memLoad32 Mk (F + BitVec.ofNat 32 0xC) = F + BitVec.ofNat 32 (0x28 + 4 * cs.length) ∧ cs.length ≤ 8 ∧
    ∀ m, m < cs.length →
      memLoad32 Mk (F + BitVec.ofNat 32 (0x28 + 4 * m)) = BitVec.ofNat 32 (cs.getD m 0) ∧ cs.getD m 0 < 8

theorem RmHM.low {Mz Mk : Word → BitVec 8} {F MP SP : Word} {ML SL : Nat} {cs : List Nat}
    (h : RmHM Mz F MP SP ML SL cs) (hL : RmLow Mz Mk F) : RmHM Mk F MP SP ML SL cs := by
  obtain ⟨h10, h14, h18, h1c, h20, h24, hc, hc8, hs⟩ := h
  refine ⟨(hL.load (c := 4) (by decide)).trans h10, (hL.load (c := 8) (by decide)).trans h14,
    (hL.load (c := 0xC) (by decide)).trans h18, (hL.load (c := 0x10) (by decide)).trans h1c,
    (hL.load (c := 0x14) (by decide)).trans h20, (hL.load (c := 0x18) (by decide)).trans h24, ?_, hc8,
    fun m hm => ?_⟩
  · have := hL.load (c := 0) (by decide)
    rw [Nat.add_zero] at this
    exact this.trans hc
  · have := hL.load (c := 0x1C + 4 * m) (by omega)
    rw [show 0xC + (0x1C + 4 * m) = 0x28 + 4 * m by omega] at this
    exact ⟨this.trans (hs m hm).1, (hs m hm).2⟩

end C3.RV32

namespace C3.Json

/-- The keys of the counted slots `cs`, as memory holds them. -/
def rmKs (es : List RkEntry) (cs : List Nat) : List (Nat × Bytes) :=
  cs.map fun m => match rmKeyAt es m with
    | some k => (k.1, nb k.2)
    | none => (0, [])

/-- The counted slots name distinct keys, and each slot's key ID has a
first signature in `a` that checks over `msg` with the slot's key. -/
def RmSnd (a msg : Bytes) (es : List RkEntry) (cs : List Nat) : Prop :=
  (rmKs es cs).Nodup ∧ ∀ m ∈ cs, m < es.length ∧ ∃ k sig, rmKeyAt es m = some k ∧
    metLookup a (nb (es.getD m ([], none)).1) = some (some sig) ∧ sigOkT (k.1, nb k.2) msg sig = true

theorem rm_snd0 {a msg : Bytes} {es : List RkEntry} : RmSnd a msg es [] :=
  ⟨List.nodup_nil, fun _ h => nomatch h⟩

theorem rm_sndS {a msg : Bytes} {es : List RkEntry} {cs : List Nat} {i ti : Nat} {ki sig : Bytes}
    (hS : RmSnd a msg es cs) (hi : i < es.length) (hki : rmKeyAt es i = some (ti, ki))
    (hl : metLookup a (nb (es.getD i ([], none)).1) = some (some sig)) (hok : sigOkT (ti, nb ki) msg sig = true)
    (hpd : RV32.RmPd es cs ti ki cs.length) : RmSnd a msg es (cs ++ [i]) := by
  obtain ⟨hnd, hall⟩ := hS
  have hks : rmKs es (cs ++ [i]) = rmKs es cs ++ [(ti, nb ki)] := by
    unfold rmKs; rw [List.map_append, List.map_cons, List.map_nil, hki]
  refine ⟨?_, fun m hm => ?_⟩
  · rw [hks, List.nodup_append]
    refine ⟨hnd, List.nodup_cons.mpr ⟨(fun h => nomatch h), List.nodup_nil⟩, fun x hx y hy => ?_⟩
    rw [List.mem_singleton] at hy; subst hy
    unfold rmKs at hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨-, k, sg, hk, -⟩ := hall m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_iff_getElem.mp hm
    have hg : cs.getD m' 0 = cs[m'] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']; rfl
    rw [← hg] at hk ⊢
    rw [hk]
    exact hpd m' hm' k hk
  · rcases List.mem_append.mp hm with hm | hm
    · exact hall m hm
    · rw [List.mem_singleton] at hm; subst hm
      exact ⟨hi, _, sig, hki, hl, hok⟩

/-- At least `t` counted slots: `MetSound` on the entries as memory holds
them. -/
theorem rm_sound {a msg : Bytes} {es : List RkEntry} {cs : List Nat} {t : Nat} (hS : RmSnd a msg es cs)
    (ht : t ≤ cs.length) : MetSound a msg t (es.map nbE) := by
  refine ⟨rmKs es cs, hS.1, by unfold rmKs; rw [List.length_map]; exact ht, fun k hk => ?_⟩
  unfold rmKs at hk
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hk
  obtain ⟨hml, k0, sig, hk0, hlk, hok⟩ := hS.2 m hm
  rw [hk0]
  refine ⟨nb (es.getD m ([], none)).1, sig, ?_, hlk, hok⟩
  have hg : es.getD m ([], none) = es[m] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hml]; rfl
  unfold rmKeyAt at hk0
  rw [hg] at hk0 ⊢
  have : nbE es[m] = (nb es[m].1, some (k0.1, nb k0.2)) := by unfold nbE; rw [hk0]; rfl
  rw [← this]
  exact List.mem_map_of_mem (List.getElem_mem hml)

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- Slot `j`'s key ID and its length. -/
theorem rm_slotId {M0 : Word → BitVec 8} {R : Word} {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es)
    {j : Nat} (hj8 : j < 8) :
    memBytes M0 (R + BitVec.ofNat 32 (0x318 + 64 * j)) (es.getD j ([], none)).1.length =
        nb (es.getD j ([], none)).1 ∧
      memLoad32 M0 (R + BitVec.ofNat 32 (0x518 + 4 * j)) = BitVec.ofNat 32 (es.getD j ([], none)).1.length ∧
      (es.getD j ([], none)).1.length ≤ 64 := by
  obtain ⟨hl, hb, hw, -⟩ := hR.2.2.2 j hj8
  refine ⟨rm_nbPre fun jj hjj => ?_, ?_, hl⟩
  · rw [add_ofNat_assoc]; exact hb jj (by omega)
  · rw [← rk_w32]; exact hw


/-- The state at the loop head 0x78 before slot `j`, with the counted
slots `cs`. -/
def RmHd (M0 M1 : Word → BitVec 8) (s F R MP SP : Word) (ML SL : Nat) (g0 : Fin 32 → Word) (es : List RkEntry)
    (cs : List Nat) (j : Nat) (Mk : Word → BitVec 8) (g : Fin 32 → Word) : Prop :=
  Out M1 Mk s 0x38EC ∧ RmHM Mk F MP SP ML SL cs ∧ RmSnd (memBytes M0 SP SL) (memBytes M0 MP ML) es cs ∧
    g sp = F ∧ g 0 = 0 ∧ (∀ x, x ∉ rkE → g x = g0 x) ∧ g 19 = R ∧ g 20 = BitVec.ofNat 32 es.length ∧
    g 23 = BitVec.ofNat 32 j ∧ g 13 = SP ∧ g 12 = BitVec.ofNat 32 SL ∧ g 14 = R + BitVec.ofNat 32 0x518 ∧
    g 15 = BitVec.ofNat 32 0x62 ∧ g 8 = BitVec.ofNat 32 0x40 ∧ cs.length ≤ j ∧ j ≤ es.length

section
variable {M0 M1 : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word} {S : Prop} {H : Post}

/-- From 0x2C0: reload `a2` to `a5` and `s0`, and go to the loop head. -/
theorem rm_2c0 (E : RmBase M0 M1 s F R MP SP ML SL g0) {es : List RkEntry} {cs : List Nat} {j : Nat}
    {Mz Mk : Word → BitVec 8} {g : Fin 32 → Word} (hO : Out M1 Mk s 0x38EC) (hLo : RmLow Mz Mk F)
    (hHM : RmHM Mz F MP SP ML SL cs) (hS : RmSnd (memBytes M0 SP SL) (memBytes M0 MP ML) es cs)
    (hsp : g sp = F) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) (h19 : g 19 = R)
    (h20 : g 20 = BitVec.ofNat 32 es.length) (h23 : g 23 = BitVec.ofNat 32 j) (hcj : cs.length ≤ j)
    (hjn : j ≤ es.length)
    (IH : ∀ Mk' g', RmHd M0 M1 s F R MP SP ML SL g0 es cs j Mk' g' →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x78 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x2C0 g := by
  have hH := hHM.low hLo
  have h20m := hH.2.2.2.2.1
  have h24m := hH.2.2.2.2.2.1
  refine WP.aluImm rkm_at_2c0 ?_; wn
  refine WP.lw rkm_at_2c4 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x24) (by decide)) ?_; wn
  refine WP.lw rkm_at_2c6 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x20) (by decide)) ?_; wn
  refine WP.aluImm rkm_at_2c8 ?_; wn
  refine WP.aluImm rkm_at_2cc ?_; wn
  refine WP.jal rkm_at_2d0 (by decide) ?_; wn
  refine IH Mk _ ⟨hO, hH, hS, by rsimp; exact hsp, by rsimp; (try exact hz), by keepz E.hz0, by rsimp; exact h19,
    by rsimp; exact h20, by rsimp; exact h23, ?_, ?_, ?_, ?_, ?_, hcj, hjn⟩
  · rsimp; rw [hsp]; exact h24m
  · rsimp; rw [hsp]; exact h20m
  · rsimp; rw [h19]; rfl
  · (try rsimp) <;> (try rw [hz]) <;> rfl
  · (try rsimp) <;> (try rw [hz]) <;> rfl

theorem rm_ld {M : Word → BitVec 8} (F : Word) {c d : Nat} {v : Word} (h : c + 4 ≤ d ∨ d + 4 ≤ c)
    (hc : c + 4 ≤ 0x1F0) (hd : d + 4 ≤ 0x1F0) :
    memLoad32 (memStore32 M (F + BitVec.ofNat 32 c) v) (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (rm_ff F h hc hd)

theorem rm_ne8 : ∀ c, c < 8 → branchTaken .beq (BitVec.ofNat 32 c) 8 = false := by decide

theorem rm_sll2 : ∀ c, c < 8 → aluEval .sll (BitVec.ofNat 32 c + 1) 2 = BitVec.ofNat 32 (4 * (c + 1)) := by decide

theorem rm_sw {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
    {f : Fin 32 → Word} {rs1 rs2 : Fin 32} {o l A V : Word} (h : fetchRel code off = some (.store .sw rs1 rs2 o, l))
    (hA : f rs1 + o = A) (hV : f rs2 = V) (ha : A.toNat % 4 = 0) (hs : Sep A 4 base code.length)
    (k : WP code base Q (memStore32 M A V) (off + l.toNat) f) : WP code base Q M off f := by
  subst hA hV; exact WP.sw h ha hs k

theorem rm_ld4 {M : Word → BitVec 8} {F : Word} {c d : Nat} {v1 v2 v3 v4 : Word} (hc : c < 8)
    (hd1 : d + 4 ≤ 0x1F0) (h1 : 0xC + 4 ≤ d ∨ d + 4 ≤ 0xC) (h2 : 0x18 + 4 ≤ d ∨ d + 4 ≤ 0x18)
    (h3 : 0x1C + 4 ≤ d ∨ d + 4 ≤ 0x1C) (h4 : 0x28 + 4 * c + 4 ≤ d ∨ d + 4 ≤ 0x28 + 4 * c) :
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M (F + BitVec.ofNat 32 (0x28 + 4 * c)) v1)
      (F + BitVec.ofNat 32 0x1C) v2) (F + BitVec.ofNat 32 0x18) v3) (F + BitVec.ofNat 32 0xC) v4)
      (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) := by
  rw [rm_ld F (c := 0xC) (d := d) h1 (by decide) hd1, rm_ld F (c := 0x18) (d := d) h2 (by decide) hd1,
    rm_ld F (c := 0x1C) (d := d) h3 (by decide) hd1, rm_ld F (c := 0x28 + 4 * c) (d := d) h4 (by omega) hd1]

theorem RmBase.st (E : RmBase M0 M1 s F R MP SP ML SL g0) {Ma : Word → BitVec 8} {d : Nat} {v : Word}
    (hO : Out M1 Ma s 0x38EC) (hd : d + 4 ≤ 0x1BC) : Out M1 (memStore32 Ma (F + BitVec.ofNat 32 d) v) s 0x38EC :=
  hO.trans (Out.upK (E.Fc d).symm (out_store32 _ _ _) (by omega))

theorem rm_gL {cs : List Nat} {i m : Nat} (hm : m < cs.length) : (cs ++ [i]).getD m 0 = cs.getD m 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

theorem rm_gR {cs : List Nat} {i : Nat} : (cs ++ [i]).getD cs.length 0 = i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl

/-- From 0x314, after a check: when `a0` is nonzero, count slot `i`. -/
theorem rm_314 (E : RmBase M0 M1 s F R MP SP ML SL g0) {es : List RkEntry} {cs : List Nat} {i : Nat}
    {Mz Mk : Word → BitVec 8} {g : Fin 32 → Word} (hO : Out M1 Mk s 0x38EC) (hLo : RmLow Mz Mk F)
    (hHM : RmHM Mz F MP SP ML SL cs) (hS : RmSnd (memBytes M0 SP SL) (memBytes M0 MP ML) es cs)
    (hsp : g sp = F) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) (h19 : g 19 = R)
    (h20 : g 20 = BitVec.ofNat 32 es.length) (h22 : g 22 = BitVec.ofNat 32 i) (h23 : g 23 = BitVec.ofNat 32 (i + 1))
    (hcj : cs.length ≤ i) (hin : i < es.length) (hn8 : es.length ≤ 8)
    (hok : g 10 ≠ 0 → RmSnd (memBytes M0 SP SL) (memBytes M0 MP ML) es (cs ++ [i]))
    (IH : ∀ cs' Mk' g', RmHd M0 M1 s F R MP SP ML SL g0 es cs' (i + 1) Mk' g' →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x78 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x314 g := by
  have hH := hHM.low hLo
  obtain ⟨h10m, h14m, h18m, h1cm, h20m, h24m, hcm, hc8, hsm⟩ := hH
  refine WP.aluImm rkm_at_314 ?_; wn
  refine WP.lw rkm_at_318 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x24) (by decide)) ?_; wn
  refine WP.lw rkm_at_31a (by (try rsimp); rw [hsp]; exact E.alF (c := 0x20) (by decide)) ?_; wn
  refine WP.aluImm rkm_at_31c ?_; wn
  refine WP.aluImm rkm_at_320 ?_; wn
  refine WP.branch rkm_at_324 (fun eb => ?_) (fun eb => ?_) <;> wn
  · refine IH cs Mk _ ⟨hO, hHM.low hLo, hS, by rsimp; exact hsp, by rsimp; (try exact hz), by keepz E.hz0,
      by rsimp; exact h19, by rsimp; exact h20, by rsimp; exact h23, ?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
    · rsimp; rw [hsp]; exact h24m
    · rsimp; rw [hsp]; exact h20m
    · rsimp; rw [h19]; rfl
    · (try rsimp) <;> (try rw [hz]) <;> rfl
    · (try rsimp) <;> (try rw [hz]) <;> rfl
  have hS' := hok (fun h => by (try rsimp at eb); rw [h] at eb; exact absurd eb (by decide))
  refine WP.lw rkm_at_328 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
  refine WP.aluImm rkm_at_32a ?_; wn
  refine WP.branch rkm_at_32c (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp] at eb
    change branchTaken .beq (memLoad32 Mk (F + BitVec.ofNat 32 0x18)) (aluEval .add 0 8) = true at eb
    rw [h18m, ev0, rm_ne8 _ (by omega)] at eb; exact absurd eb (by decide)
  refine WP.lw rkm_at_330 (by (try rsimp); rw [hsp]; exact E.alF (c := 0xC) (by decide)) ?_; wn
  refine rm_sw rkm_at_332 (A := F + BitVec.ofNat 32 (0x28 + 4 * cs.length)) (V := BitVec.ofNat 32 i)
    (by (try rsimp); rw [hsp, add_lit_zero]; exact hcm) (by (try rsimp); exact h22)
    (E.alF (by omega)) (E.cF (by omega)) ?_; wn
  refine WP.aluImm rkm_at_336 ?_; wn
  refine WP.lw rkm_at_338 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x1C) (by decide)) ?_; wn
  refine WP.aluImm rkm_at_33a ?_; wn
  refine rm_sw rkm_at_33c (A := F + BitVec.ofNat 32 0x1C) (V := BitVec.ofNat 32 (4 * (cs.length + 1)))
    (by (try rsimp); rw [hsp]; rfl) ?_ (E.alF (by decide)) (E.cF (by decide)) ?_
  · (try rsimp); rw [hsp]
    change memLoad32 _ (F + BitVec.ofNat 32 0x1C) + BitVec.ofNat 32 4 = _
    rw [rm_ld F (c := 0x28 + 4 * cs.length) (d := 0x1C) (by omega) (by omega) (by decide), h1cm, ofNat_add_ofNat]
    exact congrArg _ (by omega)
  wn
  refine WP.aluImm rkm_at_33e ?_; wn
  refine WP.jal rkm_at_340 (by decide) ?_; wn
  refine rm_sw rkm_at_70 (A := F + BitVec.ofNat 32 0x18) (V := BitVec.ofNat 32 (cs.length + 1))
    (by (try rsimp); rw [hsp]; rfl) ?_ (E.alF (by decide)) (E.cF (by decide)) ?_
  · (try rsimp); rw [hsp, ev_add]
    change memLoad32 Mk (F + BitVec.ofNat 32 0x18) + BitVec.ofNat 32 1 = _
    rw [h18m, ofNat_add_ofNat]
  wn
  refine WP.aluImm rkm_at_72 ?_; wn
  refine WP.alu rkm_at_74 ?_; wn
  refine rm_sw rkm_at_76 (A := F + BitVec.ofNat 32 0xC) (V := F + BitVec.ofNat 32 (0x28 + 4 * (cs.length + 1)))
    (by (try rsimp); rw [hsp]; rfl) ?_ (E.alF (by decide)) (E.cF (by decide)) ?_
  · (try rsimp); rw [hsp, ev_add, ev_add, ev_add]
    change aluEval .sll (memLoad32 Mk (F + BitVec.ofNat 32 0x18) + 1) 2 + (F + BitVec.ofNat 32 0x28) = _
    rw [h18m, rm_sll2 _ (by omega), BitVec.add_comm, add_ofNat_assoc]
  wn
  have hl : (cs ++ [i]).length = cs.length + 1 := by rw [List.length_append]; rfl
  have hc7 : cs.length < 8 := by omega
  refine IH (cs ++ [i]) _ _ ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, fun m hm => ?_⟩, hS', by rsimp; exact hsp,
    by rsimp; (try exact hz), by keepz E.hz0, by rsimp; exact h19, by rsimp; exact h20, by rsimp; exact h23, ?_, ?_,
    ?_, ?_, ?_, by omega, by omega⟩
  · exact E.st (E.st (E.st (E.st hO (by omega)) (by decide)) (by decide)) (by decide)
  · rw [rm_ld4 hc7 (by decide) (by omega) (by omega) (by omega) (by omega)]; exact h10m
  · rw [rm_ld4 hc7 (by decide) (by omega) (by omega) (by omega) (by omega)]; exact h14m
  · rw [hl, rm_ld F (c := 0xC) (d := 0x18) (by decide) (by decide) (by decide), memLoad32_store32_same]
  · rw [hl, rm_ld F (c := 0xC) (d := 0x1C) (by decide) (by decide) (by decide),
      rm_ld F (c := 0x18) (d := 0x1C) (by decide) (by decide) (by decide), memLoad32_store32_same]
  · rw [rm_ld4 hc7 (by decide) (by omega) (by omega) (by omega) (by omega)]; exact h20m
  · rw [rm_ld4 hc7 (by decide) (by omega) (by omega) (by omega) (by omega)]; exact h24m
  · rw [hl, memLoad32_store32_same]
  · rw [hl] at hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · rw [rm_gL hm, rm_ld4 hc7 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hsm m hm
    · rw [rm_gR, rm_ld F (c := 0xC) (d := 0x28 + 4 * cs.length) (by omega) (by decide) (by omega),
        rm_ld F (c := 0x18) (d := 0x28 + 4 * cs.length) (by omega) (by decide) (by omega),
        rm_ld F (c := 0x1C) (d := 0x28 + 4 * cs.length) (by omega) (by decide) (by omega), memLoad32_store32_same]
      exact ⟨rfl, by omega⟩
  · rsimp; rw [hsp]; exact h24m
  · rsimp; rw [hsp]; exact h20m
  · rsimp; rw [h19]; rfl
  · (try rsimp) <;> (try rw [hz]) <;> rfl
  · (try rsimp) <;> (try rw [hz]) <;> rfl

theorem rm_geN : ∀ n, n ≤ 8 → branchTaken .bgeu (BitVec.ofNat 32 n) (BitVec.ofNat 32 n) = true := by decide

theorem rm_sltuN : ∀ n, n ≤ 8 → aluEval .sltu (BitVec.ofNat 32 n) (BitVec.ofNat 32 n) = 0 := by decide

theorem rm_thr {lo hi : Word} {c : Nat} (hc : c ≤ 8)
    (h : aluEval .and (aluEval .xor (aluEval .sltu (BitVec.ofNat 32 c) lo) 0xFFFFFFFF) (aluEval .sltu hi 1) ≠ 0) :
    hi.toNat * 2 ^ 32 + lo.toNat ≤ c := by
  change ((if (BitVec.ofNat 32 c).ult lo then (1 : Word) else 0) ^^^ 0xFFFFFFFF) &&&
    (if hi.ult 1 then (1 : Word) else 0) ≠ 0 at h
  by_cases h1 : (BitVec.ofNat 32 c).ult lo = true
  · rw [if_pos h1] at h; exact absurd h (by split <;> decide)
  · by_cases h2 : hi.ult 1 = true
    · rw [BitVec.ult, decide_eq_true_eq] at h1 h2
      rw [BitVec.toNat_ofNat] at h1
      have : c % 2 ^ 32 = c := Nat.mod_eq_of_lt (by omega)
      have : hi.toNat < 1 := h2
      omega
    · rw [Bool.not_eq_true] at h2; rw [h2] at h; exact absurd h (by split <;> decide)

/-- The loop's exit, from 0x78 after the last slot: the count against the
threshold, then the epilogue. -/
theorem rm_exit (E : RmBase M0 M1 s F R MP SP ML SL g0) {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es)
    {cs : List Nat} {Mk : Word → BitVec 8} {g : Fin 32 → Word}
    (hd : RmHd M0 M1 s F R MP SP ML SL g0 es cs es.length Mk g) :
    WP tufRoleKeysMetCode TRM
      (rmQ H M0 s g0 (MetSound (memBytes M0 SP SL) (memBytes M0 MP ML) t (es.map nbE))) Mk 0x78 g := by
  obtain ⟨hO, hHM, hS, hsp, hz, hfr, h19, h20, h23, -, -, -, -, -, hcj, -⟩ := hd
  have hn8 := hR.1
  have hal := E.halR
  have hw : ∀ c, c + 4 ≤ 0x540 → memLoad32 Mk (R + BitVec.ofNat 32 c) = memLoad32 M0 (R + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => E.agree hO _ (sep_pt (E.hSR.subR hc) hj)
  refine WP.alu rkm_at_78 ?_; wn
  refine WP.branch rkm_at_7a (fun _ => ?_) (fun eb => ?_) <;> wn
  rotate_left
  · exfalso; (try rsimp at eb); rw [h23, h20, rm_geN _ hn8] at eb; exact absurd eb (by decide)
  refine WP.lw rkm_at_354 (by (try rsimp); rw [h19]; exact aligned_add hal (k := 0x310) (by decide)) ?_; wn
  refine WP.lw rkm_at_358 (by (try rsimp); rw [h19]; exact aligned_add hal (k := 0x314) (by decide)) ?_; wn
  refine WP.lw rkm_at_35c (by (try rsimp); rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
  refine WP.alu rkm_at_35e ?_; wn
  refine WP.aluImm rkm_at_362 ?_; wn
  refine WP.aluImm rkm_at_366 ?_; wn
  refine WP.alu rkm_at_36a ?_; wn
  refine rm_epi (by rsimp; exact hsp) (E.saved hO) E.hsp0 E.hret (by have := E.halF; omega) E.hz0
    (by keepz E.hz0) (E.agree hO) (fun _ h26 => ?_)
    fun h => absurd (by
      have h0 : aluEval .add (0 : Word) (BitVec.ofNat 32 es.length) = BitVec.ofNat 32 es.length := BitVec.zero_add _
      (try rsimp); rw [h23, h20, show g x0 = 0 from hz, h0]; exact rm_sltuN _ hn8) h
  refine rm_sound hS ?_
  (try rsimp at h26)
  rw [hsp, h19] at h26
  change aluEval .and (aluEval .xor (aluEval .sltu (memLoad32 Mk (F + BitVec.ofNat 32 0x18))
    (memLoad32 Mk (R + BitVec.ofNat 32 0x310))) 0xFFFFFFFF)
    (aluEval .sltu (memLoad32 Mk (R + BitVec.ofNat 32 0x314)) 1) ≠ 0 at h26
  rw [hHM.2.2.1, hw 0x310 (by decide), hw 0x314 (by decide), ← rk_w32, ← rk_w32] at h26
  have := rm_thr (by omega) h26
  rw [hR.2.1] at this
  exact this

/-- From 0xAA, slot `j` with a key and its key ID's length in `s9`: look up
the ID's signature, check that no counted slot has the same key, decode
the signature, check it, and count the slot when it checks. -/
theorem rm_body (E : RmEnv M0 M1 s F R MP SP ML SL g0) (hH : ∀ m, Halting m → rmQ H M0 s g0 S m.pc m.mem (reg m))
    {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es) (hw : RkWf es) {cs : List Nat} {j ti : Nat} {ki : Bytes}
    (hj8 : j < 8) (hjn : j < es.length) (hki : rmKeyAt es j = some (ti, ki)) {Mk : Word → BitVec 8}
    {g : Fin 32 → Word} (hO : Out M1 Mk s 0x38EC) (hHM : RmHM Mk F MP SP ML SL cs)
    (hS : RmSnd (memBytes M0 SP SL) (memBytes M0 MP ML) es cs) (hcj : cs.length ≤ j) (hsp : g sp = F)
    (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) (h19 : g 19 = R) (h20 : g 20 = BitVec.ofNat 32 es.length)
    (h22 : g 22 = BitVec.ofNat 32 j) (h23 : g 23 = BitVec.ofNat 32 (j + 1))
    (h24 : g 24 = (BitVec.ofNat 8 ti).zeroExtend 32)
    (h25 : g 25 = BitVec.ofNat 32 (es.getD j ([], none)).1.length) (h27 : g 27 = R + BitVec.ofNat 32 (98 * j))
    (h13 : g 13 = SP) (h12 : g 12 = BitVec.ofNat 32 SL)
    (IH : ∀ cs' Mk' g', RmHd M0 M1 s F R MP SP ML SL g0 es cs' (j + 1) Mk' g' →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x78 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0xAA g := by
  have hn8 := hR.1
  obtain ⟨hid, -, hIL⟩ := rm_slotId hR hj8
  refine rm_open E.toRmBase hsp hj8 hjn (by omega) hIL h19 h20 h22 h25 h13 h12 hz hfr hO (RmLow.refl Mk F)
    (fun Mk1 g1 hO1 hL1 hr hz1 hf1 _ => ?_) (fun Mk1 g1 q l hO1 hL1 hr hz1 hf1 h25' h8' hql hlk => ?_)
  · obtain ⟨r1, -, r19, r20, -, -, r23, -, -, -⟩ := hr
    exact rm_2c0 E.toRmBase hO1 hL1 hHM hS r1 hz1 hf1 r19 r20 (r23.trans h23) (by omega) (by omega) (IH cs)
  obtain ⟨r1, r18, r19, r20, -, r22, r23, r24, -, r27⟩ := hr
  rw [hid] at hlk
  refine rm_dup E.toRmBase hR hw hj8 hki r1 r18 r19 (r27.trans h27) (W8 := BitVec.ofNat 32 l) hHM.2.2.2.2.2.2.2.1
    hHM.2.2.2.2.2.2.2.2 hHM.2.2.2.1 (fun Mk2 g2 hD hK2 hz2 hf2 => ?_) (fun Mk2 g2 hD hK2 hz2 hf2 hpd => ?_) hf1
    ⟨hO1, hL1, h8'⟩
  · exact rm_2c0 E.toRmBase hD.1 hD.2.1 hHM hS ((hK2 sp (by decide)).trans r1) hz2 hf2
      ((hK2 19 (by decide)).trans r19) ((hK2 20 (by decide)).trans r20)
      ((hK2 23 (by decide)).trans (r23.trans h23)) (by omega) (by omega) (IH cs)
  refine rm_hex E.toRmBase ((hK2 sp (by decide)).trans r1) hz2 hf2 ((hK2 25 (by decide)).trans h25') hql
    ⟨hD.1, hD.2.1⟩ hD.2.2 (fun Mk3 g3 hV hK3 hz3 hf3 => ?_)
    (fun Mk3 g3 bs hV hK3 hz3 hf3 h10 h11 hl hp hbl hbm => ?_)
  · exact rm_2c0 E.toRmBase hV.1 hV.2 hHM hS ((hK3 sp (by decide)).trans ((hK2 sp (by decide)).trans r1)) hz3
      hf3 ((hK3 19 (by decide)).trans ((hK2 19 (by decide)).trans r19))
      ((hK3 20 (by decide)).trans ((hK2 20 (by decide)).trans r20))
      ((hK3 23 (by decide)).trans ((hK2 23 (by decide)).trans (r23.trans h23))) (by omega) (by omega) (IH cs)
  refine rm_ver E hH hR hw hj8 hki (G := g3) (fun _ _ => rfl)
    ((hK3 sp (by decide)).trans ((hK2 sp (by decide)).trans r1)) hz3 hf3
    ((hK3 27 (by decide)).trans ((hK2 27 (by decide)).trans (r27.trans h27)))
    ((hK3 24 (by decide)).trans ((hK2 24 (by decide)).trans (r24.trans h24))) h10 h11 hl hp hbl hV hbm hHM.2.1
    hHM.1 (fun Mk4 g4 hV4 hK4 hz4 hf4 => ?_) (fun Mk4 g4 hV4 hK4 hz4 hf4 hsig => ?_)
  · exact rm_2c0 E.toRmBase hV4.1 hV4.2 hHM hS
      ((hK4 sp (by decide)).trans ((hK3 sp (by decide)).trans ((hK2 sp (by decide)).trans r1))) hz4 hf4
      ((hK4 19 (by decide)).trans ((hK3 19 (by decide)).trans ((hK2 19 (by decide)).trans r19)))
      ((hK4 20 (by decide)).trans ((hK3 20 (by decide)).trans ((hK2 20 (by decide)).trans r20)))
      ((hK4 23 (by decide)).trans ((hK3 23 (by decide)).trans ((hK2 23 (by decide)).trans (r23.trans h23))))
      (by omega) (by omega) (IH cs)
  exact rm_314 E.toRmBase hV4.1 hV4.2 hHM hS
    ((hK4 sp (by decide)).trans ((hK3 sp (by decide)).trans ((hK2 sp (by decide)).trans r1))) hz4 hf4
    ((hK4 19 (by decide)).trans ((hK3 19 (by decide)).trans ((hK2 19 (by decide)).trans r19)))
    ((hK4 20 (by decide)).trans ((hK3 20 (by decide)).trans ((hK2 20 (by decide)).trans r20)))
    ((hK4 22 (by decide)).trans ((hK3 22 (by decide)).trans ((hK2 22 (by decide)).trans r22)))
    ((hK4 23 (by decide)).trans ((hK3 23 (by decide)).trans ((hK2 23 (by decide)).trans (r23.trans h23))))
    hcj hjn hn8 (fun h => rm_sndS hS hjn hki hlk (hsig h) hpd) IH

theorem rm_ltN : ∀ n, n ≤ 8 → ∀ j, j < n → branchTaken .bgeu (BitVec.ofNat 32 j) (BitVec.ofNat 32 n) = false := by
  decide

theorem rm_lt7 : ∀ j, j < 8 → branchTaken .bltu 7 (BitVec.ofNat 32 j) = false := by decide

theorem rm_m98 : ∀ j, j < 8 → aluEval .mul (BitVec.ofNat 32 j) (BitVec.ofNat 32 0x62) = BitVec.ofNat 32 (98 * j) := by
  decide

theorem rm_s2 : ∀ j, j < 8 → aluEval .sll (BitVec.ofNat 32 j) 2 = BitVec.ofNat 32 (4 * j) := by decide

theorem rm_le64 : ∀ L, L ≤ 64 → branchTaken .bltu (BitVec.ofNat 32 0x40) (BitVec.ofNat 32 L) = false := by decide

theorem rm_tag : ∀ t, t < 3 →
    branchTaken .beq (aluEval .add ((BitVec.ofNat 8 t).zeroExtend 32) 0xFFFFFF01) 0 = false := by decide

/-- One pass of the loop from 0x78, for slot `j` before the last. -/
theorem rm_iter (E : RmEnv M0 M1 s F R MP SP ML SL g0) (hH : ∀ m, Halting m → rmQ H M0 s g0 S m.pc m.mem (reg m))
    {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es) (hw : RkWf es) {cs : List Nat} {j : Nat}
    {Mk : Word → BitVec 8} {g : Fin 32 → Word} (hd : RmHd M0 M1 s F R MP SP ML SL g0 es cs j Mk g)
    (hjn : j < es.length)
    (IH : ∀ cs' Mk' g', RmHd M0 M1 s F R MP SP ML SL g0 es cs' (j + 1) Mk' g' →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x78 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x78 g := by
  obtain ⟨hO, hHM, hS, hsp, hz, hfr, h19, h20, h23, h13, h12, h14, h15, h8, hcj, -⟩ := hd
  have hn8 := hR.1
  have hj8 : j < 8 := by omega
  have hal := E.halR
  have hb : ∀ c, c + 1 ≤ 0x540 → Mk (R + BitVec.ofNat 32 c) = M0 (R + BitVec.ofNat 32 c) := fun c hc => by
    have := E.agree hO _ (sep_pt (E.hSR.subR hc) (i := 0) (by decide))
    rwa [add_ofNat_zero] at this
  have hw4 : ∀ c, c + 4 ≤ 0x540 → memLoad32 Mk (R + BitVec.ofNat 32 c) = memLoad32 M0 (R + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => E.agree hO _ (sep_pt (E.hSR.subR hc) hj)
  have hx0 : g x0 = 0 := hz
  have e27 : aluEval .add (aluEval .mul (BitVec.ofNat 32 j) (BitVec.ofNat 32 0x62)) R = R + BitVec.ofNat 32 (98 * j) := by
    rw [ev_add, rm_m98 j hj8, BitVec.add_comm]
  refine WP.alu rkm_at_78 ?_; wn
  refine WP.branch rkm_at_7a (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [h23, h20, rm_ltN _ hn8 _ hjn] at eb; exact absurd eb (by decide)
  refine WP.alu rkm_at_7e ?_; wn
  refine WP.aluImm rkm_at_82 ?_; wn
  refine WP.alu rkm_at_86 ?_; wn
  refine WP.aluImm rkm_at_88 ?_; wn
  refine WP.branch rkm_at_8a (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); simp only [hx0, ev0, h23] at eb; rw [rm_lt7 _ hj8] at eb; exact absurd eb (by decide)
  refine WP.lbu rkm_at_8e ?_; wn
  refine WP.aluImm rkm_at_92 ?_; wn
  rw [hx0, ev0, h23, h15, h19, e27, add_lit_zero, hb (98 * j) (by omega)]
  have hjj : aluEval .add (BitVec.ofNat 32 j) 1 = BitVec.ofNat 32 (j + 1) := by rw [ev_add]; exact ofNat_add_ofNat j 1
  rcases rm_slotKey hR hj8 with ⟨hn, hT⟩ | ⟨ti, ki, hki, hT, -⟩
  · rw [hT]
    refine WP.branch rkm_at_96 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); (try rw [hx0] at eb); (try exact absurd eb (by decide))
    refine IH cs Mk _ ⟨hO, hHM, hS, by rsimp; exact hsp, by rsimp; (try exact hz), by keepz E.hz0,
      by rsimp; exact h19, by rsimp; exact h20, by rsimp; exact hjj, by rsimp; exact h13, by rsimp; exact h12,
      by rsimp; exact h14, by rsimp; exact h15, by rsimp; exact h8, by omega, by omega⟩
  rw [hT]
  have ht3 : ti < 3 := by rcases rm_wfAt hw hki with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp only at h <;> omega
  refine WP.branch rkm_at_96 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); (try rw [hx0] at eb); rw [rm_tag ti ht3] at eb; exact absurd eb (by decide)
  obtain ⟨-, hIL, hIL64⟩ := rm_slotId hR hj8
  have eA : aluEval .add (aluEval .sll (BitVec.ofNat 32 j) 2) (R + BitVec.ofNat 32 0x518) + 0 =
      R + BitVec.ofNat 32 (0x518 + 4 * j) := by
    rw [ev_add, rm_s2 j hj8, add_lit_zero, BitVec.add_comm, add_ofNat_assoc]
  refine WP.aluImm rkm_at_98 ?_; wn
  refine WP.alu rkm_at_9c ?_; wn
  refine WP.lw rkm_at_9e (by (try rsimp); rw [h14, eA]; exact aligned_add hal (k := 0x518 + 4 * j) (by omega)) ?_; wn
  refine WP.aluImm rkm_at_a2 ?_; wn
  refine WP.branch rkm_at_a6 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [h8, h14, eA, hw4 _ (by omega), hIL, rm_le64 _ hIL64] at eb
    exact absurd eb (by decide)
  refine rm_body E hH hR hw hj8 hjn hki hO hHM hS hcj (by rsimp; exact hsp) (by rsimp; (try exact hz))
    (by keepz E.hz0) (by rsimp; exact h19) (by rsimp; exact h20) (by rsimp; (try exact h23)) (by rsimp; exact hjj)
    (by rsimp) ?_ (by rsimp) (by rsimp; exact h13) (by rsimp; exact h12) IH
  rsimp; rw [h14, eA, hw4 _ (by omega), hIL]


/-- The loop from 0x78 with `k` slots left, to the return. -/
theorem rm_loop (E : RmEnv M0 M1 s F R MP SP ML SL g0) {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es)
    (hw : RkWf es) (k : Nat) :
    ∀ cs j Mk g, es.length - j = k → RmHd M0 M1 s F R MP SP ML SL g0 es cs j Mk g →
      WP tufRoleKeysMetCode TRM
        (rmQ rmH M0 s g0 (MetSound (memBytes M0 SP SL) (memBytes M0 MP ML) t (es.map nbE))) Mk 0x78 g := by
  induction k with
  | zero =>
    intro cs j Mk g hk hd
    have hjn := hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    obtain rfl : j = es.length := by omega
    exact rm_exit E.toRmBase hR hd
  | succ k ih =>
    intro cs j Mk g hk hd
    exact rm_iter E rmQ_halt hR hw hd (by omega) fun cs' Mk' g' hd' => ih cs' (j + 1) Mk' g' (by omega) hd'

end

end C3.RV32
