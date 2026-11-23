import C3BootProofs.Proofs.SvCosigLoop
import C3BootProofs.Proofs.SvExtListLink

/-!
# The checkpoint's signature lines the code read, as `checkpointSigs`

The code's loop over the signature lines (`sv_cosigStep`): each pass splits
off a line, checks its em dash and space, checks that the text after the
space is canonical base64 a group at a time, and, for a line from the log's
origin, decodes it and keeps the signature whose key hint matches.
-/

namespace C3.RV32.Sv

open C3.Image

theorem splitSpace_cons_ne {b : Nat} {rest : Bytes} (hb : b ≠ 0x20) :
    splitSpace (b :: rest) = (do let (l, r) ← splitSpace rest; pure (b :: l, r)) := by
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | b
  all_goals first | exact absurd rfl hb | rfl

/-- The code's search for the first space as `splitSpace`. -/
theorem splitSpace_search {M : Word → BitVec 8} : ∀ {p : Word} {k n : Nat}, k < n →
    (∀ i, i < k → M (p + BitVec.ofNat 32 i) ≠ 0x20) → M (p + BitVec.ofNat 32 k) = 0x20 →
    splitSpace (memBytes M p n) = some (memBytes M p k, memBytes M (p + BitVec.ofNat 32 (k + 1)) (n - (k + 1)))
  | p, 0, n, hk, _, hs => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [add_ofNat_zero] at hs
    rw [memBytes_succ, hs, show (0x20 : BitVec 8).toNat = 0x20 from rfl, ← add_ofNat_zero p, add_ofNat_assoc,
      add_ofNat_zero, show n' + 1 - (0 + 1) = n' by omega]
    rfl
  | p, k + 1, n, hk, hne, hs => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h0 := hne 0 (by omega)
    rw [add_ofNat_zero] at h0
    have hb : (M p).toNat ≠ 0x20 := fun e => h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    have hp1 : p + 1 = p + BitVec.ofNat 32 1 := rfl
    rw [memBytes_succ, splitSpace_cons_ne hb, hp1,
      splitSpace_search (p := p + BitVec.ofNat 32 1) (k := k) (n := n') (by omega)
        (fun i hi => by rw [add_ofNat_assoc, Nat.add_comm 1 i]; exact hne (i + 1) (by omega))
        (by rw [add_ofNat_assoc, Nat.add_comm 1 k]; exact hs)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [memBytes_succ M p k, hp1, add_ofNat_assoc, show 1 + (k + 1) = k + 1 + 1 by omega,
      show n' - (k + 1) = n' + 1 - (k + 1 + 1) by omega]
    rfl

theorem readExpect_prefix {M : Word → BitVec 8} {p : Word} {n : Nat} {pre : Bytes} (hl : pre.length ≤ n)
    (h : memBytes M p pre.length = pre) :
    readExpect pre (memBytes M p n) = some (memBytes M (p + BitVec.ofNat 32 pre.length) (n - pre.length)) := by
  unfold readExpect
  rw [memBytes_take M p hl, h, beq_iff_eq.mpr rfl, memBytes_length]
  simp only [Bool.true_and, decide_eq_true hl, ↓reduceIte]
  rw [memBytes_dropK' M p hl]

theorem byte_eq {a b : Nat} (ha : a < 256) (hb : b < 256) (h : BitVec.ofNat 8 a = BitVec.ofNat 8 b) : a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem app4_inj {a b c d e f g h : BitVec 8} (H : a ++ b ++ c ++ d = e ++ f ++ g ++ h) :
    a = e ∧ b = f ∧ c = g ∧ d = h := by
  have h1 := congrArg (fun x => x.extractLsb' 0 8) H
  have h2 := congrArg (fun x => x.extractLsb' 8 24) H
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h1 h2
  have h3 := congrArg (fun x => x.extractLsb' 0 8) h2
  have h4 := congrArg (fun x => x.extractLsb' 8 16) h2
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h3 h4
  have h5 := congrArg (fun x => x.extractLsb' 0 8) h4
  have h6 := congrArg (fun x => x.extractLsb' 8 8) h4
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h5 h6
  exact ⟨h6, h5, h3, h1⟩

theorem sha256_lt (msg : Bytes) : ∀ b ∈ sha256 msg, b < 256 := by
  intro b hb
  unfold sha256 at hb
  obtain ⟨w, -, hw⟩ := List.mem_flatMap.mp hb
  have := w.isLt
  simp only [Sha256.wordBytes, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · omega
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)

theorem bind_some_lt {α : Type} {x : Option α} {f : α → Option Bytes} {g : Bytes} (h : x.bind f = some g)
    (hf : ∀ a, f a = some g → ∀ b ∈ g, b < 256) : ∀ b ∈ g, b < 256 := by
  cases x with
  | none => cases h
  | some a => exact hf a h

theorem b64Group_lt {c0 c1 c2 c3 pad : Nat} {g : Bytes} (h : b64Group c0 c1 c2 c3 pad = some g) : ∀ b ∈ g, b < 256 := by
  unfold b64Group at h
  simp only [Option.bind_eq_bind] at h
  refine bind_some_lt h fun _ h => bind_some_lt h fun _ h => ?_
  have fin : ∀ (bits : Nat) (u : Option Unit), (u.bind fun _ => pure (List.take (3 - pad)
      [bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256])) = some g → ∀ b ∈ g, b < 256 := by
    intro bits u hu
    refine bind_some_lt hu fun _ hu => ?_
    rw [Option.pure_def] at hu
    have hu := Option.some.inj hu
    subst hu
    intro b hb
    have := List.mem_of_mem_take hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl <;> exact Nat.mod_lt _ (by decide)
  split at h <;> refine bind_some_lt h fun _ h => ?_ <;> split at h <;> refine bind_some_lt h fun _ h => ?_ <;>
    exact fin _ _ h

theorem base64Decode_lt : ∀ {x bs : Bytes}, base64Decode x = some bs → ∀ b ∈ bs, b < 256
  | [], bs, h => by
    rw [base64Decode.eq_1] at h
    cases h; intro b hb; cases hb
  | [c0, c1, c2, c3], bs, h => by
    rw [base64Decode.eq_2] at h
    exact b64Group_lt h
  | c0 :: c1 :: c2 :: c3 :: hd :: tl, bs, h => by
    rw [base64Decode.eq_3] at h
    cases hg : b64Group c0 c1 c2 c3 0 with
    | none => rw [hg] at h; cases h
    | some g =>
      cases hr : base64Decode (hd :: tl) with
      | none => rw [hg, hr] at h; cases h
      | some r =>
        rw [hg, hr] at h
        cases h
        intro b hb
        rcases List.mem_append.mp hb with h1 | h1
        · exact b64Group_lt hg b h1
        · exact base64Decode_lt hr b h1
  | [a], _, h => by
    rw [base64Decode.eq_4 [a] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h
  | [a, b], _, h => by
    rw [base64Decode.eq_4 [a, b] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h
  | [a, b, c], _, h => by
    rw [base64Decode.eq_4 [a, b, c] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h

theorem le4_take {l l' : Bytes} (hl : 4 ≤ l.length) (hl' : 4 ≤ l'.length) (hb : ∀ x ∈ l, x < 256)
    (hb' : ∀ x ∈ l', x < 256) (h : le4 l 0 = le4 l' 0) : l.take 4 = l'.take 4 := by
  unfold le4 at h
  obtain ⟨e3, e2, e1, e0⟩ := app4_inj h
  match l, l', hl, hl' with
  | a0 :: a1 :: a2 :: a3 :: _, b0 :: b1 :: b2 :: b3 :: _, _, _ =>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
    simp only [List.take_succ_cons, List.take_zero]
    rw [byte_eq (hb _ (by simp)) (hb' _ (by simp)) e0, byte_eq (hb _ (by simp)) (hb' _ (by simp)) e1,
      byte_eq (hb _ (by simp)) (hb' _ (by simp)) e2, byte_eq (hb _ (by simp)) (hb' _ (by simp)) e3]

theorem sub4_toNat {n : Nat} (h4 : 4 ≤ n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n + BitVec.ofNat 32 0xFFFFFFFC).toNat = n - 4 := by
  rw [BitVec.toNat_add, ofNat_toNat_lt hn, ofNat_toNat_lt (by decide)]; omega

theorem zero_add_mul1 (k : Nat) : BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1) = BitVec.ofNat 32 k := by
  rw [Nat.mul_one, BitVec.zero_add]

theorem add_succ_ofNat (p : Word) (k : Nat) : p + (BitVec.ofNat 32 k + BitVec.ofNat 32 0x1) = p + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add_ofNat]

theorem enc_len {n k : Nat} (h4 : 4 ≤ n) (hn : n < 2 ^ 32) (hk : k + 1 ≤ n - 4) :
    ((BitVec.ofNat 32 n + BitVec.ofNat 32 0xFFFFFFFC) - (BitVec.ofNat 32 k + BitVec.ofNat 32 0x1)).toNat = n - 4 - (k + 1) := by
  rw [show BitVec.ofNat 32 k + BitVec.ofNat 32 0x1 = BitVec.ofNat 32 (k + 1) from BitVec.ofNat_add_ofNat .., BitVec.toNat_sub,
    sub4_toNat h4 hn, ofNat_toNat_lt (k := k + 1) (by omega)]; omega

theorem and3_shr2 {x : Word} (h : x &&& BitVec.ofNat 32 0x3 = 0) : x.toNat = 4 * (x >>> 2).toNat := by
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, ofNat_toNat_lt (by decide), show (0 : Word).toNat = 0 from rfl, and3] at h1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem le4_take4 (l : Bytes) : le4 l 0 = le4 (l.take 4) 0 := by
  unfold le4
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  rfl

theorem cosig_cons {origin id L : Bytes} {fuel : Nat} {matched : Option Bytes} (hne : L ≠ []) :
    checkpointSigs origin id (fuel + 1) L matched = (do
      let (line, rest) ← splitLine L
      let afterDash ← readExpect sigLinePrefix line
      let (name, encoded) ← splitSpace afterDash
      require (!name.isEmpty && (base64Decode encoded).isSome && !encoded.isEmpty)
      if name != origin then checkpointSigs origin id fuel rest matched
      else
        let value ← base64Decode encoded
        require (value.length ≤ 96)
        if value.length < 4 || value.take 4 != id then checkpointSigs origin id fuel rest matched
        else
          let sig := value.drop 4
          require (sig.length == 64 && matched.isNone)
          checkpointSigs origin id fuel rest (some sig)) := by
  cases L with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

set_option maxHeartbeats 16000000 in
/-- The code's loop over the signature lines, a run of `k` passes that reads
every byte, as `checkpointSigs`: the flag at bit 0 of the state's tenth word
says whether a signature was kept, and the last word holds it. -/
theorem cosig_chain {M : Word → BitVec 8} {dp B out bp x26 q : Word} {rt : Bytes}
    {w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 : Word}
    {v : Nat → Word} {sgp op ol : Word} {idf : Bytes}
    (hpre : memBytes M (BitVec.ofNat 32 0x3FCC4855) 4 = sigLinePrefix)
    (hw14 : le4 idf 0 = w14) (hidl : 4 ≤ idf.length) (hidb : ∀ x ∈ idf, x < 256) :
    ∀ k {c x21 rl rp dg w8 wc w28 w2c w30 w38 w40 w5c c' x21' rl' rp' dg' w8' wc' w28' w2c' w30' w38' w40' : Word}
      {sg sg' : Bytes} {fuel : Nat} {matched : Option Bytes},
      svChain (sv_cosigStep dp B out bp x26 q rt w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 v sgp op ol M) k
        (c, x21, rl, rp, dg, w8, wc, w28, w2c, w30, w38, w40, w5c, sg)
        (c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', 0, sg') →
      w5c.toNat ≤ fuel → (w30 &&& 1 = 0 → matched = none) → (w30 &&& 1 ≠ 0 → matched = some sg) →
      ∃ m', checkpointSigs (memBytes M w48 w44.toNat) (idf.take 4) fuel (memBytes M w38 w5c.toNat) matched = some m' ∧
        (w30' &&& 1 = 0 → m' = none) ∧ (w30' &&& 1 ≠ 0 → m' = some sg') := by
  intro k
  induction k with
  | zero =>
    intro c x21 rl rp dg w8 wc w28 w2c w30 w38 w40 w5c c' x21' rl' rp' dg' w8' wc' w28' w2c' w30' w38' w40' sg sg'
      fuel matched h _ h0 h1
    cases h
    refine ⟨matched, ?_, h0, h1⟩
    cases fuel <;> rfl
  | succ k ih =>
    intro c x21 rl rp dg w8 wc w28 w2c w30 w38 w40 w5c c' x21' rl' rp' dg' w8' wc' w28' w2c' w30' w38' w40' sg sg'
      fuel matched h hf h0 h1
    obtain ⟨m, hm, hc⟩ := h
    obtain ⟨hne, ix, hix, h4, hpre4, k2, hk2, hsp, c2, pa2, e2, hsp2, ec2, epa2, hc2ne, h3, dg3, pg3, gi3, eg3, hgroups,
      cmsg, cmw30, hcm, hs⟩ := hm
    subst hs
    simp only at hne hix hpre4 hsp hc2ne h3 eg3 hgroups hcm hc
    have hb := nlScan_bound hix
    have hw5 := w5c.isLt
    have hrem : w5c.toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq e)
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hix32 : ix < 2 ^ 32 := by omega
    rw [sub4_toNat h4 hix32] at hk2
    rw [zero_add_mul1] at ec2
    subst ec2
    have hsp' : ∀ i, i < k2 → M (w38 + BitVec.ofNat 32 0x4 + BitVec.ofNat 32 i) ≠ 0x20 := by
      intro i hi
      have := hsp i hi (svIter (fun s => (s.1 + BitVec.ofNat 32 0x1, s.2 + BitVec.ofNat 32 0x1)) i
        (BitVec.ofNat 32 0x0, w38 + BitVec.ofNat 32 0x4)).1
        (svIter (fun s => (s.1 + BitVec.ofNat 32 0x1, s.2 + BitVec.ofNat 32 0x1)) i
        (BitVec.ofNat 32 0x0, w38 + BitVec.ofNat 32 0x4)).2 rfl
      rwa [svIter_add (F := fun s : Word × Word => (s.1 + BitVec.ofNat 32 0x1, s.2 + BitVec.ofNat 32 0x1)) Prod.snd (d := 1)
        (fun _ => rfl), Nat.mul_one] at this
    rw [epa2, Nat.mul_one] at hsp2
    have hL : memBytes M w38 w5c.toNat ≠ [] := by
      intro e
      have := congrArg List.length e
      rw [memBytes_length, List.length_nil] at this
      exact hrem this
    rw [cosig_cons hL, splitLine_scan0 hix]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [readExpect_prefix (pre := sigLinePrefix) (by rw [show sigLinePrefix.length = 4 from rfl]; exact h4)
      (by rw [show sigLinePrefix.length = 4 from rfl, hpre4, hpre])]
    simp only [Option.bind_some, show sigLinePrefix.length = 4 from rfl]
    rw [splitSpace_search (by omega) hsp' hsp2]
    simp only [Option.bind_some]
    have hk2pos : k2 ≠ 0 := fun e => hc2ne (by rw [e]; rfl)
    have hk32 : k2 < 2 ^ 32 := by omega
    have hname_ne : (!List.isEmpty (memBytes M (w38 + BitVec.ofNat 32 0x4) k2)) = true := by
      obtain ⟨n', rfl⟩ : ∃ n', k2 = n' + 1 := ⟨k2 - 1, by omega⟩
      rw [memBytes_succ]; rfl
    have henc : memBytes M ((w38 + BitVec.ofNat 32 0x4) + (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1))
        (((BitVec.ofNat 32 ix + BitVec.ofNat 32 0xFFFFFFFC) - (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1))).toNat =
        memBytes M (w38 + BitVec.ofNat 32 0x4 + BitVec.ofNat 32 (k2 + 1)) (ix - 4 - (k2 + 1)) := by
      rw [add_succ_ofNat, enc_len h4 hix32 hk2]
    have hencne : ¬ (BitVec.ofNat 32 ix + BitVec.ofNat 32 0xFFFFFFFC = BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1) →
        (!List.isEmpty (memBytes M (w38 + BitVec.ofNat 32 0x4 + BitVec.ofNat 32 (k2 + 1)) (ix - 4 - (k2 + 1)))) = true := by
      intro h
      have hn : ix - 4 - (k2 + 1) ≠ 0 := by
        intro e
        apply h
        apply BitVec.eq_of_toNat_eq
        rw [sub4_toNat h4 hix32, show BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1 = BitVec.ofNat 32 (k2 + 1) from
          BitVec.ofNat_add_ofNat .., ofNat_toNat_lt (k := k2 + 1) (by omega)]
        omega
      obtain ⟨n', hn'⟩ : ∃ n', ix - 4 - (k2 + 1) = n' + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hn).symm⟩
      rw [hn', memBytes_succ]; rfl
    have hnamek : memBytes M (w38 + BitVec.ofNat 32 0x4) (BitVec.ofNat 32 k2).toNat =
        memBytes M (w38 + BitVec.ofNat 32 0x4) k2 := by rw [ofNat_toNat_lt hk32]
    have hr' : (BitVec.ofNat 32 w5c.toNat - BitVec.ofNat 32 (ix + 1)).toNat = w5c.toNat - (ix + 1) := by
      rw [BitVec.toNat_sub, ofNat_toNat_lt hw5, ofNat_toNat_lt (k := ix + 1) (by omega)]; omega
    have hfuel : (BitVec.ofNat 32 w5c.toNat - BitVec.ofNat 32 (ix + 1)).toNat ≤ fuel' := by rw [hr']; omega
    rcases hcm with hF | hF | hF | ⟨bs, hbs, hne', hname, -, hle96, hlt4, esg, ew30⟩ |
      ⟨bs, hbs, hne', hname, -, hle96, hnlt4, hle4, hl68, hw30, esg, ew30⟩ | hF |
      ⟨bs, hbs, hne', hname, -, hle96, hnlt4, hnle4, esg, ew30⟩ | ⟨hne', hnname, esg, ew30⟩
    · exact hF.elim
    · exact hF.elim
    · exact hF.elim
    · rw [henc] at hbs
      rw [hnamek] at hname
      subst esg ew30
      obtain ⟨m', hm', hm0, hm1⟩ := ih hc hfuel h0 h1
      rw [hr'] at hm'
      refine ⟨m', ?_, hm0, hm1⟩
      rw [hname_ne, hbs, hencne hne', show (true && (some bs).isSome && true) = true from rfl, require_true]
      simp only [Option.bind_some]
      rw [hname, show (memBytes M w48 w44.toNat != memBytes M w48 w44.toNat) = false by rw [bne, beq_iff_eq.mpr rfl]; rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decide_eq_true (Nat.not_lt.mp hle96), require_true]
      simp only [Option.bind_some]
      rw [decide_eq_true hlt4]
      simp only [Bool.true_or, ↓reduceIte]
      exact hm'
    · rw [henc] at hbs
      rw [hnamek] at hname
      subst esg ew30
      have hmn : matched = none := h0 hw30
      subst hmn
      have htk : bs.take 4 = idf.take 4 := le4_take (by omega) hidl (base64Decode_lt hbs) hidb (hle4.trans hw14.symm)
      obtain ⟨m', hm', hm0, hm1⟩ := ih hc hfuel (fun e => absurd e (by decide)) (fun _ => rfl)
      rw [hr'] at hm'
      refine ⟨m', ?_, hm0, hm1⟩
      rw [hname_ne, hbs, hencne hne', show (true && (some bs).isSome && true) = true from rfl, require_true]
      simp only [Option.bind_some]
      rw [hname, show (memBytes M w48 w44.toNat != memBytes M w48 w44.toNat) = false by rw [bne, beq_iff_eq.mpr rfl]; rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decide_eq_true (Nat.not_lt.mp hle96), require_true]
      simp only [Option.bind_some]
      rw [decide_eq_false hnlt4, htk, show (List.take 4 idf != List.take 4 idf) = false by rw [bne, beq_iff_eq.mpr rfl]; rfl]
      simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      rw [List.length_drop, hl68, show ((68 - 4 == 64) && (none : Option Bytes).isNone) = true from rfl, require_true]
      simp only [Option.bind_some]
      exact hm'
    · exact hF.elim
    · rw [henc] at hbs
      rw [hnamek] at hname
      subst esg ew30
      have hneq : ¬ bs.take 4 = idf.take 4 := fun e => hnle4 (by rw [le4_take4, e, ← le4_take4, hw14])
      have htk : (bs.take 4 != idf.take 4) = true := by rw [bne, beq_false_of_ne hneq]; rfl
      obtain ⟨m', hm', hm0, hm1⟩ := ih hc hfuel h0 h1
      rw [hr'] at hm'
      refine ⟨m', ?_, hm0, hm1⟩
      rw [hname_ne, hbs, hencne hne', show (true && (some bs).isSome && true) = true from rfl, require_true]
      simp only [Option.bind_some]
      rw [hname, show (memBytes M w48 w44.toNat != memBytes M w48 w44.toNat) = false by rw [bne, beq_iff_eq.mpr rfl]; rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decide_eq_true (Nat.not_lt.mp hle96), require_true]
      simp only [Option.bind_some]
      rw [htk, Bool.or_true]
      simp only [↓reduceIte]
      exact hm'
    · rw [hnamek] at hnname
      subst esg ew30
      obtain ⟨m', hm', hm0, hm1⟩ := ih hc hfuel h0 h1
      rw [hr'] at hm'
      refine ⟨m', ?_, hm0, hm1⟩
      have hlen := and3_shr2 h3
      rw [enc_len h4 hix32 hk2] at hlen
      have hdec : (base64Decode (memBytes M (w38 + BitVec.ofNat 32 0x4 + BitVec.ofNat 32 (k2 + 1)) (ix - 4 - (k2 + 1)))).isSome
          = true := by
        have hne0 := hencne hne'
        have hpos : ix - 4 - (k2 + 1) ≠ 0 := by
          intro e
          rw [e, memBytes_zero] at hne0
          exact absurd hne0 (by decide)
        have hN32 : 0 + ((BitVec.ofNat 32 ix + BitVec.ofNat 32 0xFFFFFFFC - (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1)) >>>
            2).toNat < 2 ^ 32 := by omega
        have hg := base64_groups (M := M) _ 0
          (p := (w38 + BitVec.ofNat 32 0x4) + (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1)) (by omega) hN32 (fun i hi => by
            have hgi := hgroups i hi (svIter (fun s : Word × Word × Word => (s.2.1 + BitVec.ofNat 32 0x4, s.2.1 + BitVec.ofNat 32 0x4, s.2.2 + BitVec.ofNat 32 0x1)) i (dg, (w38 + BitVec.ofNat 32 0x4) + (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1), BitVec.ofNat 32 0x0)).1 (svIter (fun s : Word × Word × Word => (s.2.1 + BitVec.ofNat 32 0x4, s.2.1 + BitVec.ofNat 32 0x4, s.2.2 + BitVec.ofNat 32 0x1)) i (dg, (w38 + BitVec.ofNat 32 0x4) + (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1), BitVec.ofNat 32 0x0)).2.1
              (svIter (fun s : Word × Word × Word => (s.2.1 + BitVec.ofNat 32 0x4, s.2.1 + BitVec.ofNat 32 0x4, s.2.2 + BitVec.ofNat 32 0x1)) i (dg, (w38 + BitVec.ofNat 32 0x4) + (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1), BitVec.ofNat 32 0x0)).2.2 rfl
            rw [svIter_add (F := fun s : Word × Word × Word => (s.2.1 + BitVec.ofNat 32 0x4, s.2.1 + BitVec.ofNat 32 0x4,
                s.2.2 + BitVec.ofNat 32 0x1)) (fun s => s.2.1) (d := 4) (fun _ => rfl),
              svIter_add (F := fun s : Word × Word × Word => (s.2.1 + BitVec.ofNat 32 0x4, s.2.1 + BitVec.ofNat 32 0x4,
                s.2.2 + BitVec.ofNat 32 0x1)) (fun s => s.2.2) (d := 1) (fun _ => rfl)] at hgi
            simp only at hgi
            rw [Nat.mul_comm i 4, Nat.mul_one, BitVec.zero_add, show BitVec.ofNat 32 i = BitVec.ofNat 32 (0 + i) by
              rw [Nat.zero_add], ← ofNat_toNat_self ((BitVec.ofNat 32 ix + BitVec.ofNat 32 0xFFFFFFFC -
                (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1)) >>> 2), show ((BitVec.ofNat 32 ix + BitVec.ofNat 32 0xFFFFFFFC -
                (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1)) >>> 2).toNat = 0 + ((BitVec.ofNat 32 ix +
                BitVec.ofNat 32 0xFFFFFFFC - (BitVec.ofNat 32 k2 + BitVec.ofNat 32 0x1)) >>> 2).toNat by rw [Nat.zero_add]] at hgi
            exact hgi)
        rw [add_succ_ofNat, ← hlen] at hg
        exact hg
      rw [hname_ne, hdec, hencne hne', show (true && true && true) = true from rfl, require_true]
      simp only [Option.bind_some]
      rw [show (memBytes M (w38 + BitVec.ofNat 32 0x4) k2 != memBytes M w48 w44.toNat) = true by
        rw [bne, beq_false_of_ne hnname]; rfl]
      simp only [↓reduceIte]
      exact hm'

end C3.RV32.Sv
