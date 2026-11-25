import C3BootProofs.Proofs.AcceptTargetsBody

/-!
# The `hashes` field

Helpers for the calls between 0x836 and 0xA94, and the segment from 0xA46:
`field(hashes)` on the `trusted_root.json` entry, then `field(sha256)`, then
`act_a94`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

/-- `M'` agrees with `M` outside the callees' stacks below `sp` and the `n0`
bytes at `B + c0`. -/
def ActKp (B : Word) (c0 n0 : Nat) (M M' : Word → BitVec 8) : Prop :=
  ∀ x, Sep x 1 B 0x3A50 → Sep x 1 (B + BitVec.ofNat 32 c0) n0 → M' x = M x

theorem act_slice2 (v : Bytes) {a b c d : Nat} (h : c + d ≤ b) : slice (slice v a b) c d = slice v (a + c) d := by
  unfold slice
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega), List.drop_drop]

theorem act_toNat_add {p : Word} {a : Nat} (h : p.toNat + a < 2 ^ 32) : (p + BitVec.ofNat 32 a).toNat = p.toNat + a := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega)]; exact Nat.mod_eq_of_lt h

theorem act_slice_mem {M : Word → BitVec 8} {p : Word} {n a b : Nat} (h : a + b ≤ n) :
    slice (memBytes M p n) a b = memBytes M (p + BitVec.ofNat 32 a) b := memBytes_drop_take h

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {M M' : Word → BitVec 8} {f : Fin 32 → Word}

theorem ActKp.at (X : ActX romBase romCode B Bf M0) {c0 n0 : Nat} (h : ActKp B c0 n0 M M')
    (hc0 : c0 + n0 ≤ 0x5A70) {c : Nat} (h0 : c + 1 ≤ 0x5A70) (h1 : 0x3A50 ≤ c) (h2 : c + 1 ≤ c0 ∨ c0 + n0 ≤ c) :
    M' (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  h _ (X.sB0 h0 h1) (X.ss h0 hc0 h2)

theorem ActKp.ld (X : ActX romBase romCode B Bf M0) {c0 n0 : Nat} (h : ActKp B c0 n0 M M')
    (hc0 : c0 + n0 ≤ 0x5A70) {c : Nat} (h0 : c + 4 ≤ 0x5A70) (h1 : 0x3A50 ≤ c) (h2 : c + 4 ≤ c0 ∨ c0 + n0 ≤ c) :
    memLoad32 M' (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h.at X hc0 (by omega) (by omega) (by omega)

theorem ActKp.bytes (X : ActX romBase romCode B Bf M0) {c0 n0 : Nat} (h : ActKp B c0 n0 M M')
    (hc0 : c0 + n0 ≤ 0x5A70) {c n : Nat} (h0 : c + n ≤ 0x5A70) (h1 : 0x3A50 ≤ c) (h2 : c + n ≤ c0 ∨ c0 + n0 ≤ c) :
    memBytes M' (B + BitVec.ofNat 32 c) n = memBytes M (B + BitVec.ofNat 32 c) n :=
  memBytes_congr fun j hj => by rw [add_ofNat_assoc]; exact h.at X hc0 (by omega) (by omega) (by omega)

/-- A pointer into `Buffers` is `Bf` plus its offset. -/
theorem ActX.inb (X : ActX romBase romCode B Bf M0) {p : Word} {n : Nat} (h1 : Bf.toNat ≤ p.toNat)
    (h2 : p.toNat + n ≤ Bf.toNat + acBufLen) : p = Bf + BitVec.ofNat 32 (p.toNat - Bf.toNat) := by
  have := X.bhi
  apply BitVec.eq_of_toNat_eq; rw [X.bfLo (by omega)]; omega

/-- A stretch of the frame and bytes in `Buffers`. -/
theorem ActX.sfb (X : ActX romBase romCode B Bf M0) {a k : Nat} (ha : a + k ≤ 0x5A70) {p : Word} {n : Nat}
    (h1 : Bf.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ Bf.toNat + acBufLen) : Sep (B + BitVec.ofNat 32 a) k p n := by
  rw [X.inb h1 h2]; exact X.sbf ha (by omega)

theorem ActKp.bf (X : ActX romBase romCode B Bf M0) {c0 n0 : Nat} (h : ActKp B c0 n0 M M')
    (hc0 : c0 + n0 ≤ 0x5A70) {p : Word} {n : Nat} (h1 : Bf.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ Bf.toNat + acBufLen) :
    memBytes M' p n = memBytes M p n := by
  have := X.bhi
  refine memBytes_congr fun j hj => h _ ?_ ?_
  · have s := (X.sfb (a := 0) (k := 0x3A50) (by decide) h1 h2).symm.sub (c := j) (l := 1) (by omega)
    rwa [show B + BitVec.ofNat 32 0 = B from BitVec.add_zero B] at s
  · exact ((X.sfb (a := c0) (k := n0) hc0 h1 h2).symm.sub (c := j) (l := 1) (by omega))

theorem ActKp.out {c0 n0 : Nat} (h : ActKp B c0 n0 M M') (hres : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 c0) n0) :
    ∀ x, ActOut B Bf x → M' x = M x := fun x hx => h x hx.1 (hres x hx)

theorem ActKp.tid (X : ActX romBase romCode B Bf M0) {c0 n0 : Nat} (h : ActKp B c0 n0 M M')
    (hc0 : c0 + n0 ≤ 0x5A70) (h2 : 0x3A50 + 0x350 ≤ c0 ∨ c0 + n0 ≤ 0x3C94) (i : Nat) :
    tufIndexDocSpec M' (acSlot B 0x244) i = tufIndexDocSpec M (acSlot B 0x244) i :=
  act_tid_congr (fun j hj => by rw [add_ofNat_assoc]; exact h.at X hc0 (by omega) (by omega) (by omega)) i

theorem ActKp.doc (X : ActX romBase romCode B Bf M0) {c0 n0 : Nat} (h : ActKp B c0 n0 M M')
    (hc0 : c0 + n0 ≤ 0x5A70) (h2 : 0x3A50 + 0x350 ≤ c0 ∨ c0 + n0 ≤ 0x3C94) {flash : Nat → BitVec 8} {s : Word} {i : Nat} {d : Bytes}
    (hd : ActDoc flash M (acSlot B 0x244) s i d) : ActDoc flash M' (acSlot B 0x244) s i d :=
  fun o l e => hd o l (by rw [← h.tid X hc0 h2]; exact e)

theorem act_fres_kp {c : Nat} {r : Except Nat (Word × Nat)}
    (h : FieldResF M M' (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 0x394C) 260 r) : ActKp B c 8 M M' := by
  obtain ⟨M1, h1, h2⟩ := h
  have ho : ∀ x, Sep x 1 (B + BitVec.ofNat 32 c) 8 → M' x = M1 x := by rcases r with _ | ⟨_, _⟩ <;> exact h2.1
  exact fun x a b => (ho x b).trans (h1 x (a.subR (c := 0x394C) (l := 260) (by decide)))

theorem act_fres_val {out s : Word} {k : Nat} {r : Except Nat (Word × Nat)} (h : FieldResF M M' out s k r) :
    FieldRes M' M' out r := by
  obtain ⟨M1, _, h2⟩ := h
  rcases r with _ | ⟨_, _⟩
  · exact ⟨fun _ _ => rfl, h2.2⟩
  · exact ⟨fun _ _ => rfl, h2.2⟩

/-- A stretch of the frame and the keys `acTargetsKeysData`. -/
theorem ActX.key (X : ActX romBase romCode B Bf M0) {a n o k : Nat} (ha : a + n ≤ 0x5A70) (hk : o + k ≤ 42) :
    Sep (B + BitVec.ofNat 32 a) n (BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 o) k := by
  have s := (X.sro ha).subR (c := 0x20 + o) (l := k) (by unfold roWindowSize; omega)
  have e : BitVec.ofNat 32 roWindowAddress + BitVec.ofNat 32 (0x20 + o) =
      BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 o := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, roWindowAddress, acTargetsKeysAddress]
    omega
  rwa [e] at s

theorem act_keyB (E : AcTargetsEnv romBase romCode M) {o k : Nat} (h : o + k ≤ 42) :
    memBytes M (BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 o) k = (acTargetsKeysData.drop o).take k := by
  have hm : memBytes M (BitVec.ofNat 32 acTargetsKeysAddress) acTargetsKeysData.length = acTargetsKeysData := by
    unfold memBytes
    apply List.ext_getElem
    · rw [List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [E.keys i h2]
      unfold byteAt
      rw [BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
      have hb : ∀ b ∈ acTargetsKeysData, b < 256 := by decide
      exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))
  rw [← memBytes_drop_take (n := acTargetsKeysData.length) h, hm]

end

end C3.RV32.Ac

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {M : Word → BitVec 8} {f : Fin 32 → Word}

theorem act_out_1ed0 : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x5920) 8 := fun x hx => by
  have := act_ks hx.2.2.2.2.1 0x670 8 (by decide); exact this

theorem act_strBody_nil : strBody [] = none := rfl

theorem act_slice_len {v : Bytes} {a b : Nat} (h : a + b ≤ v.length) : (slice v a b).length = b := by
  unfold slice; rw [List.length_take, List.length_drop]; omega

theorem act_w4 (B : Word) (c : Nat) : B + BitVec.ofNat 32 c + 4 = B + BitVec.ofNat 32 (c + 4) :=
  add_ofNat_assoc B c 4

theorem act_spc2 {B : Word} {f : Fin 32 → Word} (h : f sp = B + 0x3A50) (a k : Word) (c : Nat)
    (hc : (0x3A50 + (a + k).toNat) % 2 ^ 32 = c) : f sp + a + k = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc]; exact act_spc h _ c hc

/-- **From 0xA46**: `field(hashes)` on the entry `d` at `E`, `field(sha256)`
on its value, then `act_a94`. -/
theorem act_a46 {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {hiW loW : Word} {val : Nat} {E : Word} {n : Nat} {d : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (h18 : memLoad32 M (acSlot B 0x18) = hiW) (h14 : memLoad32 M (acSlot B 0x14) = loW)
    (hval : hiW.toNat * 2 ^ 32 + loW.toNat = val)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hs0 : f 8 = E) (hs2 : f 18 = BitVec.ofNat 32 n) (hE1 : Bf.toNat + 0x4000 ≤ E.toNat)
    (hE2 : E.toNat + n ≤ Bf.toNat + 0x6800) (hd : memBytes M E n = d)
    (hspec : ∀ p4 l4 p5 l5 body, objField d (ascii!"hashes") = .ok (p4, l4) →
      objField (slice d p4 l4) (ascii!"sha256") = .ok (p5, l5) →
      strBody (slice (slice d p4 l4) p5 l5) = some body → val = parts.trustedRoot.length →
      body = hexBytes (sha256 parts.trustedRoot) → verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs1 : f 9 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0xA46 f := by
  have F := X.F
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  refine WP.zero fun hz => ?_
  refine WP.lui ac_at_a46 ?_; wn
  refine WP.aluImm ac_at_a4a ?_; wn
  refine WP.lui ac_at_a4e ?_; wn
  refine WP.aluImm ac_at_a50 ?_; wn
  refine WP.alu ac_at_a54 ?_; wn
  refine WP.aluImm ac_at_a56 ?_; wn
  refine WP.alu ac_at_a58 ?_; wn
  refine WP.alu ac_at_a5a ?_; wn
  have hE0 : E.toNat ≠ 0 := by omega
  refine act_fld (c := 0x52C0) (p := E) (n := n)
    (kq := BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 0x1E) (kl := 6) X
    (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_a5c ac_at_a60 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm _ (f sp)]; exact act_spc hI.rsp _ _ rfl) (by act_r; exact hs0)
    (by act_r; exact hs2) (by act_r <;> decide) (by act_r <;> decide) (by decide) (by decide) hE0 (by omega)
    (X.sfb (by decide) (by omega) (by omega)) (X.key (by decide) (by decide)) fun m1 hf1 => ?_
  have k1 := act_fres_kp hf1
  have v1 := act_fres_val hf1
  rw [act_keyB (X.E hI) (by decide), hd, show (acTargetsKeysData.drop 0x1E).take 6 = ascii!"hashes" from by decide]
    at v1
  have hI1 := hI.mem F X.sB (k1.out act_out_1870)
  have hd1 : memBytes m1.mem E n = d := by rw [k1.bf X (by decide) (by omega) (by omega), hd]
  wn
  refine WP.lui ac_at_a64 ?_; wn
  refine WP.aluImm ac_at_a66 ?_; wn
  refine WP.alu ac_at_a6a ?_; wn
  have e0 : f 9 + 1376 = B + BitVec.ofNat 32 0x52C0 := by
    rw [hs1, acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  refine WP.lw ac_at_a6e (by act_r; rw [e0]; exact X.al (by decide) (by decide)) ?_; wn
  have L1 : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x52C0 → memLoad32 m1.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => k1.ld X (by decide) (by omega) h1 (Or.inl (by omega))
  have hr1 : memLoad32 m1.mem (acSlot B 0x40) = r := (L1 _ (by decide) (by decide)).trans hr
  have hdl : d.length = n := by rw [← hd, memBytes_length]
  rcases h1 : objField d (ascii!"hashes") with e | ⟨p4, l4⟩
  · rw [h1] at v1
    have he := act_eb_objField _ _ e h1
    obtain ⟨_, hl0, hb4⟩ := v1
    refine WP.branch ac_at_a72 (fun _ => ?_) (fun hb => ?_)
    · wn
      refine act_c0a (hI1.regs (by act_r) (by act_r) (by act_r)) hr1 ?_
      act_r
      rw [act_spc2 hI.rsp _ _ 0x52C4 rfl, ← act_w4, hb4, BitVec.toNat_ofNat]; omega
    · exfalso; revert hb; act_r; rw [e0, hl0]; decide
  rw [h1] at v1
  obtain ⟨_, hq4, hl4⟩ := v1
  obtain ⟨hp4a, hp4b⟩ := objField_val h1
  have hP4 : (E + BitVec.ofNat 32 p4).toNat = E.toNat + p4 := act_toNat_add (by omega)
  refine WP.branch ac_at_a72 (fun hb => ?_) (fun _ => ?_)
  · exfalso; revert hb; act_r; rw [e0, hq4]; simp only [branchTaken]; intro hb
    have := congrArg BitVec.toNat (beq_iff_eq.mp hb); rw [hP4] at this; simp at this; omega
  wn
  refine WP.lw ac_at_a76 (by act_r; rw [act_spc2 hI.rsp _ _ 0x52C4 rfl]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_a7a ?_; wn
  refine WP.aluImm ac_at_a7e ?_; wn
  refine WP.lui ac_at_a82 ?_; wn
  refine WP.aluImm ac_at_a84 ?_; wn
  refine WP.alu ac_at_a88 ?_; wn
  refine WP.aluImm ac_at_a8a ?_; wn
  refine act_fld (c := 0x5920) (p := E + BitVec.ofNat 32 p4) (n := l4)
    (kq := BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 0x24) (kl := 6) X
    (hI1.regs (by act_r) (by act_r) (by act_r)) ac_at_a8c ac_at_a90 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm _ (f sp)]; exact act_spc hI.rsp _ _ rfl) (by act_r; rw [e0, hq4])
    (by act_r; rw [act_spc2 hI.rsp _ _ 0x52C4 rfl, ← act_w4, hl4]) (by act_r <;> decide) (by act_r <;> decide)
    (by decide) (by decide) (by omega) (by omega)
    (X.sfb (by decide) (by omega) (by omega)) (X.key (by decide) (by decide)) fun m2 hf2 => ?_
  have k2 := act_fres_kp hf2
  have v2 := act_fres_val hf2
  have hsl : memBytes m1.mem (E + BitVec.ofNat 32 p4) l4 = slice d p4 l4 := by
    rw [← act_slice_mem (n := n) (by omega), hd1]
  rw [act_keyB (X.E hI1) (by decide), hsl,
    show (acTargetsKeysData.drop 0x24).take 6 = ascii!"sha256" from by decide] at v2
  have hO2 : ∀ x, ActOut B Bf x → m2.mem x = Mi x := fun x hx =>
    (k2.out act_out_1ed0 x hx).trans ((k1.out act_out_1870 x hx).trans (hO x hx))
  have hI2 := hI1.mem F X.sB (k2.out act_out_1ed0)
  have L : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x52C0 →
      memLoad32 m2.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => (k2.ld X (by decide) (by omega) h1 (Or.inl (by omega))).trans (L1 c h1 h2)
  have hdoc2 : ActDoc flash m2.mem (acSlot B 0x244) (f 24) ((memLoad32 m2.mem (acSlot B 0x1C)).toNat + 1)
      parts.trustedRoot := by
    rw [L _ (by decide) (by decide)]; exact k2.doc X (by decide) (Or.inl (by decide)) (k1.doc X (by decide) (Or.inl (by decide)) hdoc)
  have hsl1 : (slice d p4 l4).length = l4 := act_slice_len (by omega)
  wn
  rcases h2 : objField (slice d p4 l4) (ascii!"sha256") with e | ⟨p5, l5⟩
  · rw [h2] at v2
    have he := act_eb_objField _ _ e h2
    obtain ⟨_, hl0, hb4⟩ := v2
    refine act_a94 (q := 0) (l := 0) hROM hR4 hR X (hI2.regs (by act_r) (by act_r) (by act_r))
      ((L _ (by decide) (by decide)).trans hr) hO2 ((L _ (by decide) (by decide)).trans h18)
      ((L _ (by decide) (by decide)).trans h14) hval (by act_r; exact hdoc2) (by act_r; exact hs4)
      (Or.inl ⟨hl0, by rw [show acSlot B 0x1ED4 = B + BitVec.ofNat 32 0x5920 + 4 from (act_w4 _ _).symm, hb4,
        BitVec.toNat_ofNat]; omega⟩)
      (fun body hb => by rw [show memBytes m2.mem 0 0 = [] from rfl, act_strBody_nil] at hb; cases hb)
      ((L _ (by decide) (by decide)).trans h20) ((L _ (by decide) (by decide)).trans h24)
      ((L _ (by decide) (by decide)).trans h28) ((L _ (by decide) (by decide)).trans h2C)
      (by act_r; exact hs3) (by act_r; exact act_spc hI.rsp _ _ rfl) (by act_r; exact hs5) (by act_r; exact hs9)
      (by act_r; exact hs11)
  rw [h2] at v2
  obtain ⟨_, hq5, hl5⟩ := v2
  obtain ⟨hp5a, hp5b⟩ := objField_val h2
  rw [hsl1] at hp5a hp5b
  have hP5 : (E + BitVec.ofNat 32 p4 + BitVec.ofNat 32 p5).toNat = E.toNat + p4 + p5 := by
    rw [act_toNat_add (by omega), hP4]
  refine act_a94 (q := E + BitVec.ofNat 32 p4 + BitVec.ofNat 32 p5) (l := l5) hROM hR4 hR X
    (hI2.regs (by act_r) (by act_r) (by act_r))
    ((L _ (by decide) (by decide)).trans hr) hO2 ((L _ (by decide) (by decide)).trans h18)
    ((L _ (by decide) (by decide)).trans h14) hval (by act_r; exact hdoc2) (by act_r; exact hs4)
    (Or.inr ⟨hq5, by rw [show acSlot B 0x1ED4 = B + BitVec.ofNat 32 0x5920 + 4 from (act_w4 _ _).symm, hl5],
      by rw [hP5]; omega, by rw [hP5]; omega⟩)
    (fun body hb => ?_)
    ((L _ (by decide) (by decide)).trans h20) ((L _ (by decide) (by decide)).trans h24)
    ((L _ (by decide) (by decide)).trans h28) ((L _ (by decide) (by decide)).trans h2C)
    (by act_r; exact hs3) (by act_r; exact act_spc hI.rsp _ _ rfl) (by act_r; exact hs5) (by act_r; exact hs9)
    (by act_r; exact hs11)
  rw [k2.bf X (by decide) (by omega) (by omega), ← act_slice_mem (n := l4) (by omega), hsl] at hb
  exact hspec p4 l4 p5 l5 body h1 h2 hb

theorem act_ures_kp {c : Nat} {r : Option Nat}
    (h : U64ResF M M' (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 0x3A30) 32 r) : ActKp B c 16 M M' := by
  obtain ⟨M1, h1, h2⟩ := h
  exact fun x a b => (h2.outside x b).trans (h1 x (a.subR (c := 0x3A30) (l := 32) (by decide)))

theorem act_ures_val {out s : Word} {k : Nat} {r : Option Nat} (h : U64ResF M M' out s k r) :
    U64Res M' M' out r := by
  obtain ⟨M1, _, h2⟩ := h
  rcases r with _ | _
  · exact ⟨fun _ _ => rfl, h2.2⟩
  · exact ⟨fun _ _ => rfl, h2.2⟩

theorem act_out_1870w : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x52C0) 16 := fun x hx => by
  have := act_ks hx.2.2.2.2.1 0x10 16 (by decide); exact this

theorem act_out_14 : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x3A64) 8 := fun x hx => by
  have := hx.2.1.subR (c := 0) (l := 8) (by decide)
  rwa [add_ofNat_assoc] at this

theorem act_st_kp (w1 w2 : Word) :
    ActKp B 0x3A64 8 M (memStore32 (memStore32 M (B + BitVec.ofNat 32 0x3A64) w1) (B + BitVec.ofNat 32 0x3A68) w2) :=
  fun x _ b => by
    rw [memStore32_get_sep (by have := b.symm.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := b.symm.sub (c := 0) (l := 4) (by decide); rwa [BitVec.add_zero] at this)]

/-- **From 0xA16**: `u64` on the `length` value at `E + p3`, the length
to `sp + 0x14`, then `act_a46`. -/
theorem act_a16 {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {E : Word} {n p3 l3 : Nat} {d : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hs0 : f 8 = E) (hs2 : f 18 = BitVec.ofNat 32 n) (hE1 : Bf.toNat + 0x4000 ≤ E.toNat)
    (hE2 : E.toNat + n ≤ Bf.toNat + 0x6800) (hd : memBytes M E n = d)
    (ha1 : f 11 = E + BitVec.ofNat 32 p3) (h354 : memLoad32 M (acSlot B 0x354) = BitVec.ofNat 32 l3)
    (hp3 : p3 + l3 ≤ n)
    (hspec : ∀ val p4 l4 p5 l5 body, u64Val (slice d p3 l3) = some val →
      objField d (ascii!"hashes") = .ok (p4, l4) →
      objField (slice d p4 l4) (ascii!"sha256") = .ok (p5, l5) →
      strBody (slice (slice d p4 l4) p5 l5) = some body → val = parts.trustedRoot.length →
      body = hexBytes (sha256 parts.trustedRoot) → verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs1 : f 9 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0xA16 f := by
  have F := X.F
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  have hdl : d.length = n := by rw [← hd, memBytes_length]
  refine WP.zero fun hz => ?_
  refine WP.lw ac_at_a16 (by rw [act_spc hI.rsp _ _ rfl]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_a1a ?_; wn
  refine WP.aluImm ac_at_a1c ?_; wn
  refine WP.alu ac_at_a20 ?_; wn
  have hP3 : (E + BitVec.ofNat 32 p3).toNat = E.toNat + p3 := act_toNat_add (by omega)
  refine act_u64 (c := 0x52C0) (p := E + BitVec.ofNat 32 p3) (n := l3) X
    (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_a22 ac_at_a26 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm _ (f sp)]; exact act_spc hI.rsp _ _ rfl) (by act_r; exact ha1)
    (by act_r; rw [act_spc hI.rsp _ _ rfl]; exact h354) (by decide) (by omega)
    (X.sfb (by decide) (by omega) (by omega)) fun m2 hf2 => ?_
  have k2 := act_ures_kp hf2
  have v2 := act_ures_val hf2
  have hsl : memBytes M (E + BitVec.ofNat 32 p3) l3 = slice d p3 l3 := by
    rw [← act_slice_mem (n := n) (by omega), hd]
  rw [hsl] at v2
  have hI2 := hI.mem F X.sB (k2.out act_out_1870w)
  have L : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x52C0 →
      memLoad32 m2.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => k2.ld X (by decide) (by omega) h1 (Or.inl (by omega))
  have e9 : f 9 + 1376 = B + BitVec.ofNat 32 0x52C0 := by
    rw [hs1, acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e9' : f 9 + 1377 = B + BitVec.ofNat 32 0x52C0 + 1 := by
    rw [hs1, acSlot, BitVec.add_assoc, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  wn
  refine WP.lbu ac_at_a2a ?_; wn
  rcases hv : u64Val (slice d p3 l3) with _ | val
  · rw [hv] at v2
    obtain ⟨_, h0, h1⟩ := v2
    refine WP.branch ac_at_a2e (fun _ => ?_) (fun hb => ?_)
    · wn
      refine WP.lbu ac_at_9e0 ?_; wn
      refine WP.jal ac_at_9e4 (by decide) ?_; wn
      refine act_x6a (hI2.regs (by act_r) (by act_r) (by act_r)) ((L _ (by decide) (by decide)).trans hr) ?_
      act_r; rw [e9', h1]; decide
    · exfalso; revert hb; act_r; rw [e9, h0]; decide
  rw [hv] at v2
  obtain ⟨_, h0, h1⟩ := v2
  refine WP.branch ac_at_a2e (fun hb => ?_) (fun _ => ?_)
  · exfalso; revert hb; act_r; rw [e9, h0]; decide
  wn
  refine WP.lui ac_at_a30 ?_; wn
  refine WP.aluImm ac_at_a32 ?_; wn
  refine WP.alu ac_at_a36 ?_; wn
  have e568 : f sp + (4096 + 784) + 1384 = B + BitVec.ofNat 32 0x52C0 + 8 := by
    rw [act_spc2 hI.rsp _ _ 0x52C8 rfl, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e56C : f sp + (4096 + 784) + 1388 = B + BitVec.ofNat 32 0x52C0 + 12 := by
    rw [act_spc2 hI.rsp _ _ 0x52CC rfl, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  refine WP.lw ac_at_a3a (by act_r; rw [act_spc2 hI.rsp _ _ 0x52C8 rfl]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.sw ac_at_a3e (by act_r; rw [act_spc hI.rsp _ 0x3A64 rfl]; exact X.al (by decide) (by decide))
    (by act_r; rw [act_spc hI.rsp _ 0x3A64 rfl]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_a40 (by act_r; rw [act_spc2 hI.rsp _ _ 0x52CC rfl]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.sw ac_at_a44 (by act_r; rw [act_spc hI.rsp _ 0x3A68 rfl]; exact X.al (by decide) (by decide))
    (by act_r; rw [act_spc hI.rsp _ 0x3A68 rfl]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  have es : aluEval AluOp.add (f sp) (aluEval AluOp.add 4096 784) = acSlot B 0x1310 := act_spc hI.rsp _ _ rfl
  rw [es, act_spc hI.rsp 20 0x3A64 rfl, act_spc hI.rsp 24 0x3A68 rfl]
  have K3 := act_st_kp (M := m2.mem) (B := B) (memLoad32 m2.mem (acSlot B 0x1310 + 1384))
    (memLoad32 (memStore32 m2.mem (B + BitVec.ofNat 32 0x3A64) (memLoad32 m2.mem (acSlot B 0x1310 + 1384)))
      (acSlot B 0x1310 + 1388))
  have eA : acSlot B 0x1310 + 1384 = B + BitVec.ofNat 32 0x52C8 := by
    rw [acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have eB : acSlot B 0x1310 + 1388 = B + BitVec.ofNat 32 0x52CC := by
    rw [acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e8 : B + BitVec.ofNat 32 0x52C0 + 8 = B + BitVec.ofNat 32 0x52C8 := by
    rw [BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e12 : B + BitVec.ofNat 32 0x52C0 + 12 = B + BitVec.ofNat 32 0x52CC := by
    rw [BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  rw [e8, e12] at h1
  have L3 : ∀ c, 0x3A6C ≤ c → c + 4 ≤ 0x52C0 → memLoad32 (memStore32 (memStore32 m2.mem (B + BitVec.ofNat 32 0x3A64)
      (memLoad32 m2.mem (acSlot B 0x1310 + 1384))) (B + BitVec.ofNat 32 0x3A68)
      (memLoad32 (memStore32 m2.mem (B + BitVec.ofNat 32 0x3A64) (memLoad32 m2.mem (acSlot B 0x1310 + 1384)))
        (acSlot B 0x1310 + 1388))) (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => (K3.ld X (by decide) (by omega) (by omega) (Or.inr (by omega))).trans (L c (by omega) h2)
  refine act_a46 (hiW := memLoad32 m2.mem (B + BitVec.ofNat 32 0x52CC))
    (loW := memLoad32 m2.mem (B + BitVec.ofNat 32 0x52C8)) (val := val) hROM hR4 hR X
    ((hI2.mem F X.sB (K3.out act_out_14)).regs (by act_r) (by act_r) (by act_r))
    ((L3 _ (by decide) (by decide)).trans hr)
    (fun x hx => (K3.out act_out_14 x hx).trans ((k2.out act_out_1870w x hx).trans (hO x hx)))
    (by rw [show acSlot B 0x18 = B + BitVec.ofNat 32 0x3A68 from rfl, memLoad32_store32_same, eB,
      memLoad32_store32_sep (X.ss (by decide) (by decide) (Or.inl (by decide)))])
    (by rw [show acSlot B 0x14 = B + BitVec.ofNat 32 0x3A64 from rfl,
      memLoad32_store32_sep (X.ss (by decide) (by decide) (Or.inr (by decide))), memLoad32_store32_same, eA]) h1
    (by rw [L3 _ (by decide) (by decide)]; act_r
        exact K3.doc X (by decide) (Or.inr (by decide)) (k2.doc X (by decide) (Or.inl (by decide)) hdoc))
    (by act_r; exact hs4) (by act_r; exact hs0) (by act_r; exact hs2) hE1 hE2
    (by rw [K3.bf X (by decide) (by omega) (by omega), k2.bf X (by decide) (by omega) (by omega), hd])
    (fun p4 l4 p5 l5 body e1 e2 e3 e4 e5 => hspec val p4 l4 p5 l5 body hv e1 e2 e3 e4 e5)
    ((L3 _ (by decide) (by decide)).trans h20) ((L3 _ (by decide) (by decide)).trans h24)
    ((L3 _ (by decide) (by decide)).trans h28) ((L3 _ (by decide) (by decide)).trans h2C)
    (by act_r; exact hs3) (by act_r) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)

/-- **From 0x9F0**: `field(length)` on the entry `d` at `E`, then
`act_a16`. -/
theorem act_9f0 {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {E : Word} {n : Nat} {d : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hs0 : f 8 = E) (h878 : memLoad32 M (acSlot B 0x1878) = BitVec.ofNat 32 n) (hE1 : Bf.toNat + 0x4000 ≤ E.toNat)
    (hE2 : E.toNat + n ≤ Bf.toNat + 0x6800) (hd : memBytes M E n = d)
    (hspec : ∀ p3 l3 val p4 l4 p5 l5 body, objField d (ascii!"length") = .ok (p3, l3) →
      u64Val (slice d p3 l3) = some val →
      objField d (ascii!"hashes") = .ok (p4, l4) →
      objField (slice d p4 l4) (ascii!"sha256") = .ok (p5, l5) →
      strBody (slice (slice d p4 l4) p5 l5) = some body → val = parts.trustedRoot.length →
      body = hexBytes (sha256 parts.trustedRoot) → verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs1 : f 9 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0x9F0 f := by
  have F := X.F
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  have hdl : d.length = n := by rw [← hd, memBytes_length]
  have e9 : f 9 + 1384 = B + BitVec.ofNat 32 0x52C8 := by
    rw [hs1, acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  refine WP.zero fun hz => ?_
  refine WP.lw ac_at_9f0 (by rw [e9]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_9f4 ?_; wn
  refine WP.aluImm ac_at_9f8 ?_; wn
  refine WP.aluImm ac_at_9fc ?_; wn
  refine WP.aluImm ac_at_9fe ?_; wn
  refine WP.alu ac_at_a00 ?_; wn
  refine WP.alu ac_at_a02 ?_; wn
  have hE0 : E.toNat ≠ 0 := by omega
  refine act_fld (c := 0x3DA0) (p := E) (n := n)
    (kq := BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 0x18) (kl := 6) X
    (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_a04 ac_at_a08 (by decide) (by decide)
    (by act_r; exact act_spc hI.rsp _ _ rfl) (by act_r; exact hs0)
    (by act_r; rw [e9]; exact h878) (by act_r <;> decide) (by act_r <;> decide) (by decide) (by decide) hE0 (by omega)
    (X.sfb (by decide) (by omega) (by omega)) (X.key (by decide) (by decide)) fun m1 hf1 => ?_
  have k1 := act_fres_kp hf1
  have v1 := act_fres_val hf1
  rw [act_keyB (X.E hI) (by decide), hd, show (acTargetsKeysData.drop 0x18).take 6 = ascii!"length" from by decide]
    at v1
  have hI1 := hI.mem F X.sB (k1.out act_out_350)
  have L : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x3DA0 →
      memLoad32 m1.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => k1.ld X (by decide) (by omega) h1 (Or.inl (by omega))
  wn
  refine WP.lw ac_at_a0c (by act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl]; exact X.al (by decide) (by decide)) ?_; wn
  rcases h1 : objField d (ascii!"length") with e | ⟨p3, l3⟩
  · rw [h1] at v1
    have he := act_eb_objField _ _ e h1
    obtain ⟨_, hl0, hb4⟩ := v1
    refine WP.branch ac_at_a10 (fun hb => ?_) (fun _ => ?_)
    · exfalso; revert hb; act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl, hl0]; decide
    wn
    refine WP.jal ac_at_a12 (by decide) ?_; wn
    refine act_x66 (hI1.regs (by act_r) (by act_r) (by act_r)) ((L _ (by decide) (by decide)).trans hr) ?_
    rw [show acSlot B 0x354 = B + BitVec.ofNat 32 0x3DA0 + 4 from (act_w4 _ _).symm, hb4, BitVec.toNat_ofNat]
    omega
  rw [h1] at v1
  obtain ⟨_, hq3, hl3⟩ := v1
  obtain ⟨hp3a, hp3b⟩ := objField_val h1
  have hP3 : (E + BitVec.ofNat 32 p3).toNat = E.toNat + p3 := act_toNat_add (by omega)
  refine WP.branch ac_at_a10 (fun _ => ?_) (fun hb => by
    exfalso; revert hb; act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl, hq3]; simp only [branchTaken]; intro hb
    have := congrArg BitVec.toNat (bne_eq_false_iff_eq.mp hb); rw [hP3] at this; simp at this; omega)
  wn
  refine act_a16 (p3 := p3) (l3 := l3) hROM hR4 hR X (hI1.regs (by act_r) (by act_r) (by act_r))
    ((L _ (by decide) (by decide)).trans hr)
    (fun x hx => (k1.out act_out_350 x hx).trans (hO x hx))
    (by act_r; rw [L _ (by decide) (by decide)]
        exact k1.doc X (by decide) (Or.inl (by decide)) hdoc)
    (by act_r; exact hs4) (by act_r; exact hs0) (by act_r; rw [e9]; exact h878) hE1 hE2
    (by rw [k1.bf X (by decide) (by omega) (by omega), hd])
    (by act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl]; exact hq3)
    (by rw [show acSlot B 0x354 = B + BitVec.ofNat 32 0x3DA0 + 4 from (act_w4 _ _).symm]; exact hl3) (by omega)
    (fun val p4 l4 p5 l5 body e1 e2 e3 e4 e5 e6 => hspec p3 l3 val p4 l4 p5 l5 body h1 e1 e2 e3 e4 e5 e6)
    ((L _ (by decide) (by decide)).trans h20) ((L _ (by decide) (by decide)).trans h24)
    ((L _ (by decide) (by decide)).trans h28) ((L _ (by decide) (by decide)).trans h2C)
    (by act_r; exact hs3) (by act_r; exact hs1) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)

theorem act_gres_kp {c : Nat} {r : Except Nat (Option (Word × Nat))}
    (h : GetResF M M' (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 0x396C) 228 r) : ActKp B c 12 M M' := by
  obtain ⟨M1, h1, h2⟩ := h
  exact fun x a b => (h2.out x b).trans (h1 x (a.subR (c := 0x396C) (l := 228) (by decide)))

theorem act_gres_val {out s : Word} {k : Nat} {r : Except Nat (Option (Word × Nat))} (h : GetResF M M' out s k r) :
    GetRes M' M' out r := by
  obtain ⟨M1, _, h2⟩ := h
  rcases r with _ | _ | ⟨_, _⟩
  · exact ⟨fun _ _ => rfl, h2.2⟩
  · exact ⟨fun _ _ => rfl, h2.2⟩
  · exact ⟨fun _ _ => rfl, h2.2⟩

theorem act_out_1870c : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x52C0) 12 := fun x hx => by
  have := act_ks hx.2.2.2.2.1 0x10 12 (by decide); exact this

/-- **From 0x99A**: `field(targets)` on the `signed` value `dS` at `S`,
`get(trusted_root.json)` on it, then `act_9f0`. -/
theorem act_99a {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {S : Word} {sl : Nat} {dS : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hs2 : f 18 = S) (hs0 : f 8 = BitVec.ofNat 32 sl) (hS1 : Bf.toNat + 0x4000 ≤ S.toNat)
    (hS2 : S.toNat + sl ≤ Bf.toNat + 0x6800) (hd : memBytes M S sl = dS)
    (hspec : ∀ p1 l1 p2 l2 p3 l3 val p4 l4 p5 l5 body, objField dS (ascii!"targets") = .ok (p1, l1) →
      objGet (slice dS p1 l1) (ascii!"trusted_root.json") = .ok (some (p2, l2)) →
      objField (slice (slice dS p1 l1) p2 l2) (ascii!"length") = .ok (p3, l3) →
      u64Val (slice (slice (slice dS p1 l1) p2 l2) p3 l3) = some val →
      objField (slice (slice dS p1 l1) p2 l2) (ascii!"hashes") = .ok (p4, l4) →
      objField (slice (slice (slice dS p1 l1) p2 l2) p4 l4) (ascii!"sha256") = .ok (p5, l5) →
      strBody (slice (slice (slice (slice dS p1 l1) p2 l2) p4 l4) p5 l5) = some body →
      val = parts.trustedRoot.length →
      body = hexBytes (sha256 parts.trustedRoot) → verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs1 : f 9 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0x99A f := by
  have F := X.F
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  have hdl : dS.length = sl := by rw [← hd, memBytes_length]
  refine WP.zero fun hz => ?_
  refine WP.lui ac_at_99a ?_; wn
  refine WP.aluImm ac_at_99e ?_; wn
  refine WP.aluImm ac_at_9a2 ?_; wn
  refine WP.aluImm ac_at_9a4 ?_; wn
  refine WP.alu ac_at_9a6 ?_; wn
  refine WP.alu ac_at_9a8 ?_; wn
  have hS0 : S.toNat ≠ 0 := by omega
  refine act_fld (c := 0x3DA0) (p := S) (n := sl)
    (kq := BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 0) (kl := 7) X
    (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_9aa ac_at_9ae (by decide) (by decide)
    (by act_r; exact act_spc hI.rsp _ _ rfl) (by act_r; exact hs2)
    (by act_r; exact hs0) (by act_r <;> decide) (by act_r <;> decide) (by decide) (by decide) hS0 (by omega)
    (X.sfb (by decide) (by omega) (by omega)) (X.key (by decide) (by decide)) fun m1 hf1 => ?_
  have k1 := act_fres_kp hf1
  have v1 := act_fres_val hf1
  rw [act_keyB (X.E hI) (by decide), hd, show (acTargetsKeysData.drop 0).take 7 = ascii!"targets" from by decide]
    at v1
  have hI1 := hI.mem F X.sB (k1.out act_out_350)
  have L1 : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x3DA0 →
      memLoad32 m1.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => k1.ld X (by decide) (by omega) h1 (Or.inl (by omega))
  have hd1 : memBytes m1.mem S sl = dS := by rw [k1.bf X (by decide) (by omega) (by omega), hd]
  wn
  refine WP.lw ac_at_9b2 (by act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl]; exact X.al (by decide) (by decide)) ?_; wn
  rcases h1 : objField dS (ascii!"targets") with e | ⟨p1, l1⟩
  · rw [h1] at v1
    have he := act_eb_objField _ _ e h1
    obtain ⟨_, hl0, hb4⟩ := v1
    refine WP.branch ac_at_9b6 (fun hb => ?_) (fun _ => ?_)
    · exfalso; revert hb; act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl, hl0]; decide
    wn
    refine WP.jal ac_at_9b8 (by decide) ?_; wn
    refine act_x66 (hI1.regs (by act_r) (by act_r) (by act_r)) ((L1 _ (by decide) (by decide)).trans hr) ?_
    rw [show acSlot B 0x354 = B + BitVec.ofNat 32 0x3DA0 + 4 from (act_w4 _ _).symm, hb4, BitVec.toNat_ofNat]
    omega
  rw [h1] at v1
  obtain ⟨_, hq1, hl1⟩ := v1
  obtain ⟨hp1a, hp1b⟩ := objField_val h1
  have hP1 : (S + BitVec.ofNat 32 p1).toNat = S.toNat + p1 := act_toNat_add (by omega)
  refine WP.branch ac_at_9b6 (fun _ => ?_) (fun hb => by
    exfalso; revert hb; act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl, hq1]; simp only [branchTaken]; intro hb
    have := congrArg BitVec.toNat (bne_eq_false_iff_eq.mp hb); rw [hP1] at this; simp at this; omega)
  wn
  refine WP.lw ac_at_9bc (by act_r; rw [act_spc hI.rsp _ 0x3DA4 rfl]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_9c0 ?_; wn
  refine WP.aluImm ac_at_9c4 ?_; wn
  refine WP.lui ac_at_9c8 ?_; wn
  refine WP.aluImm ac_at_9ca ?_; wn
  refine WP.alu ac_at_9ce ?_; wn
  refine WP.aluImm ac_at_9d0 ?_; wn
  refine act_get (c := 0x52C0) (p := S + BitVec.ofNat 32 p1) (n := l1)
    (kq := BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 7) (kl := 0x11) X
    (hI1.regs (by act_r) (by act_r) (by act_r)) ac_at_9d2 ac_at_9d6 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm _ (f sp)]; exact act_spc hI.rsp _ _ rfl)
    (by act_r; rw [act_spc hI.rsp _ 0x3DA0 rfl, hq1])
    (by act_r; rw [act_spc hI.rsp _ 0x3DA4 rfl, show B + BitVec.ofNat 32 0x3DA4 = B + BitVec.ofNat 32 0x3DA0 + 4 from
      (act_w4 _ _).symm, hl1]) (by act_r <;> decide) (by act_r <;> decide)
    (by decide) (by decide) (by omega) (by omega)
    (X.sfb (by decide) (by omega) (by omega)) (X.key (by decide) (by decide)) fun m2 hf2 => ?_
  have k2 := act_gres_kp hf2
  have v2 := act_gres_val hf2
  have hsl : memBytes m1.mem (S + BitVec.ofNat 32 p1) l1 = slice dS p1 l1 := by
    rw [← act_slice_mem (n := sl) (by omega), hd1]
  rw [act_keyB (X.E hI1) (by decide), hsl,
    show (acTargetsKeysData.drop 7).take 0x11 = ascii!"trusted_root.json" from by decide] at v2
  have hI2 := hI1.mem F X.sB (k2.out act_out_1870c)
  have L : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x3DA0 →
      memLoad32 m2.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => (k2.ld X (by decide) (by omega) h1 (Or.inl (by omega))).trans (L1 c h1 h2)
  have hsl1 : (slice dS p1 l1).length = l1 := act_slice_len (by omega)
  have e9 : f 9 + 1376 = B + BitVec.ofNat 32 0x52C0 := by
    rw [hs1, acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e9' : f 9 + 1377 = B + BitVec.ofNat 32 0x52C0 + 1 := by
    rw [hs1, acSlot, BitVec.add_assoc, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e94 : f 9 + 1380 = B + BitVec.ofNat 32 0x52C0 + 4 := by
    rw [hs1, acSlot, BitVec.add_assoc, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e98 : f 9 + 1384 = B + BitVec.ofNat 32 0x52C0 + 8 := by
    rw [hs1, acSlot, BitVec.add_assoc, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  wn
  refine WP.lbu ac_at_9da ?_; wn
  rcases h2 : objGet (slice dS p1 l1) (ascii!"trusted_root.json") with e | _ | ⟨p2, l2⟩
  · rw [h2] at v2
    have he := act_eb_objGet _ _ e h2
    obtain ⟨_, h0, hb1⟩ := v2
    refine WP.branch ac_at_9de (fun hb => ?_) (fun _ => ?_)
    · exfalso; revert hb; act_r; rw [e9, h0]; decide
    wn
    refine WP.lbu ac_at_9e0 ?_; wn
    refine WP.jal ac_at_9e4 (by decide) ?_; wn
    refine act_x6a (hI2.regs (by act_r) (by act_r) (by act_r)) ((L _ (by decide) (by decide)).trans hr) ?_
    act_r; rw [e9', hb1]; exact act_zb _ (by rw [BitVec.toNat_ofNat]; omega)
  · rw [h2] at v2
    obtain ⟨_, h0, hq⟩ := v2
    refine WP.branch ac_at_9de (fun _ => ?_) (fun hb => by exfalso; revert hb; act_r; rw [e9, h0]; decide)
    wn
    refine WP.lw ac_at_9e8 (by act_r; rw [e94, act_w4]; exact X.al (by decide) (by decide)) ?_; wn
    refine WP.branch ac_at_9ec (fun _ => ?_) (fun hb => ?_)
    · wn
      exact act_c02 (hI2.regs (by act_r) (by act_r) (by act_r)) ((L _ (by decide) (by decide)).trans hr)
    · exfalso; revert hb; act_r; rw [e94, hq]; decide
  rw [h2] at v2
  obtain ⟨_, h0, hq, hl⟩ := v2
  obtain ⟨hp2a, hp2b⟩ := objGet_val h2
  rw [hsl1] at hp2a hp2b
  have hP2 : (S + BitVec.ofNat 32 p1 + BitVec.ofNat 32 p2).toNat = S.toNat + p1 + p2 := by
    rw [act_toNat_add (by omega), hP1]
  refine WP.branch ac_at_9de (fun _ => ?_) (fun hb => by exfalso; revert hb; act_r; rw [e9, h0]; decide)
  wn
  refine WP.lw ac_at_9e8 (by act_r; rw [e94, act_w4]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.branch ac_at_9ec (fun hb => by
    exfalso; revert hb; act_r; rw [e94, hq]; simp only [branchTaken]; intro hb
    have := congrArg BitVec.toNat (beq_iff_eq.mp hb); rw [hP2] at this; simp at this; omega) (fun _ => ?_)
  wn
  have e878 : acSlot B 0x1878 = B + BitVec.ofNat 32 0x52C0 + 8 := by
    rw [acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  refine act_9f0 (E := S + BitVec.ofNat 32 p1 + BitVec.ofNat 32 p2) (n := l2) (d := slice (slice dS p1 l1) p2 l2)
    hROM hR4 hR X (hI2.regs (by act_r) (by act_r) (by act_r))
    ((L _ (by decide) (by decide)).trans hr)
    (fun x hx => (k2.out act_out_1870c x hx).trans ((k1.out act_out_350 x hx).trans (hO x hx)))
    (by act_r; rw [L _ (by decide) (by decide)]
        exact k2.doc X (by decide) (Or.inl (by decide)) (k1.doc X (by decide) (Or.inl (by decide)) hdoc))
    (by act_r; exact hs4) (by act_r; rw [e94, hq]) (by rw [e878]; exact hl) (by omega) (by omega)
    (by rw [k2.bf X (by decide) (by omega) (by omega), ← act_slice_mem (n := l1) (by omega), hsl])
    (fun p3 l3 val p4 l4 p5 l5 body e1 e2 e3 e4 e5 e6 e7 =>
      hspec p1 l1 p2 l2 p3 l3 val p4 l4 p5 l5 body h1 h2 e1 e2 e3 e4 e5 e6 e7)
    ((L _ (by decide) (by decide)).trans h20) ((L _ (by decide) (by decide)).trans h24)
    ((L _ (by decide) (by decide)).trans h28) ((L _ (by decide) (by decide)).trans h2C)
    (by act_r; exact hs3) (by act_r; exact hs1) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)

end

end C3.RV32.Ac
