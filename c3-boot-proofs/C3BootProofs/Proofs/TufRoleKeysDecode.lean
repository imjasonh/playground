import C3BootProofs.Proofs.TufRoleKeysTree

/-!
# `tufRoleKeysRead`: the strings of one key object

`decode_key` from 0x26E to the scheme tree at 0x37C: the `keytype` and
`scheme` strings of the key object, the `keyval` object's `public`
string, and the `memset` of `pem_spki`'s buffer.
-/

namespace C3.RV32
open C3.Image C3.Json

set_option maxRecDepth 20000

/-- `rkDecode` after the key type `kt` and the scheme `sc`. -/
def rkDecP (kt sc v : Bytes) : Option (Nat × Bytes) :=
  match objField v (ascii!"keyval") with
  | .error _ => none
  | .ok (vp, vl) =>
    match objField (slice v vp vl) (ascii!"public") with
    | .error _ => none
    | .ok (pp, pl) =>
      match strBody (slice (slice v vp vl) pp pl) with
      | none => none
      | some pub => rkKey kt sc pub

/-- `rkDecode` after the key type `kt`. -/
def rkDecS (kt v : Bytes) : Option (Nat × Bytes) :=
  match objField v (ascii!"scheme") with
  | .error _ => none
  | .ok (sp, sl) =>
    match strBody (slice v sp sl) with
    | none => none
    | some sc => rkDecP kt sc v

theorem rkDecode_kt {v kt : Bytes} {tp tl : Nat} (h1 : objField v (ascii!"keytype") = .ok (tp, tl))
    (h2 : strBody (slice v tp tl) = some kt) : rkDecode v = rkDecS kt v := by
  simp only [rkDecode, h1, h2]; rfl

theorem rkDecS_sc {v kt sc : Bytes} {sp sl : Nat} (h1 : objField v (ascii!"scheme") = .ok (sp, sl))
    (h2 : strBody (slice v sp sl) = some sc) : rkDecS kt v = rkDecP kt sc v := by
  simp only [rkDecS, h1, h2]

/-- The word results of a `field` call in `out`. -/
def RkFR (M : Word → BitVec 8) (out : Word) : Except Nat (Word × Nat) → Prop
  | .error _ => memLoad32 M out = 0
  | .ok (q, l) => memLoad32 M out = q ∧ memLoad32 M (out + 4) = BitVec.ofNat 32 l

/-- The word results of a `str` call in `out`. -/
def RkSR (M : Word → BitVec 8) (out : Word) : Option (Word × Nat) → Prop
  | none => memLoad32 M out = 0
  | some (q, l) => memLoad32 M out = q ∧ memLoad32 M (out + 4) = BitVec.ofNat 32 l

/-- Memory `Mb` agrees with `Ma` outside `field`'s stack, `pem_spki`'s
buffer, and the two result slots at `F + 0xA78`. -/
def RkV (s F : Word) (Ma Mb : Word → BitVec 8) : Prop :=
  ∀ x, Sep x 1 (s + BitVec.ofNat 32 44) 260 → Sep x 1 (F + BitVec.ofNat 32 0x75C) 128 →
    Sep x 1 (F + BitVec.ofNat 32 0xA78) 16 → Mb x = Ma x

theorem RkV.trans {s F : Word} {Ma Mb Mc : Word → BitVec 8} (h1 : RkV s F Ma Mb) (h2 : RkV s F Mb Mc) :
    RkV s F Ma Mc := fun x a b c => (h2 x a b c).trans (h1 x a b c)

theorem rk_strB {M : Word → BitVec 8} {q : Word} {l : Nat} {b : Bytes} (h : strBody (memBytes M q l) = some b) :
    memBytes M (q + 1) b.length = b ∧ b.length + 2 = l := by
  obtain ⟨h2, hb⟩ := tex_body h
  rw [memBytes_length] at h2 hb
  rw [tuf_memBytes_drop_take (show 1 + (l - 2) ≤ l by omega)] at hb
  subst hb
  rw [memBytes_length]
  exact ⟨rfl, by omega⟩

theorem rk_a80 (F : Word) : aluEval .add (aluEval .add F 0x7FF) 0x281 = F + 0xA80 := by
  rw [ev_add, ev_add, BitVec.add_assoc]; rfl

theorem rk_a78 (F : Word) : aluEval .add (aluEval .add F 0x7FF) 0x279 = F + 0xA78 := by
  rw [ev_add, ev_add, BitVec.add_assoc]; rfl

theorem rk_e760 (F : Word) : F + 0x75C + 4 = F + 0x760 := by rw [BitVec.add_assoc]; rfl
theorem rk_eA84 (F : Word) : F + 0xA80 + 4 = F + 0xA84 := by rw [BitVec.add_assoc]; rfl
theorem rk_eA7C (F : Word) : F + 0xA78 + 4 = F + 0xA7C := by rw [BitVec.add_assoc]; rfl
theorem rk_s14 (F : Word) : F + 0xA6C + 0x14 = F + 0xA80 := by rw [BitVec.add_assoc]; rfl
theorem rk_s18 (F : Word) : F + 0xA6C + 0x18 = F + 0xA84 := by rw [BitVec.add_assoc]; rfl
theorem rk_s0C (F : Word) : F + 0xA6C + 0xC = F + 0xA78 := by rw [BitVec.add_assoc]; rfl
theorem rk_s10 (F : Word) : F + 0xA6C + 0x10 = F + 0xA7C := by rw [BitVec.add_assoc]; rfl

theorem rk_p1 (a : Word) (b : Nat) : a + BitVec.ofNat 32 b + 1 = a + BitVec.ofNat 32 (b + 1) :=
  add_ofNat_assoc a b 1

section
variable {M0 M1 Md M : Word → BitVec 8} {s out F P : Word} {N : Nat} {g0 gL : Fin 32 → Word} {Q : Post}

theorem RkEnv.outW (E : RkEnv M0 M1 s out F P N g0) {Ma Mb : Word → BitVec 8} {c l : Nat}
    (h : Out Ma Mb (F + BitVec.ofNat 32 c) l) : Out Ma Mb (s + BitVec.ofNat 32 (304 + c)) l := by
  rw [← E.Fc]; exact h

theorem rkV_outS {Ma Mb : Word → BitVec 8} (h : Out Ma Mb (s + BitVec.ofNat 32 44) 260) : RkV s F Ma Mb :=
  fun x hA _ _ => h x hA

theorem rkV_out {Ma Mb : Word → BitVec 8} {c n : Nat} (h : Out Ma Mb (F + BitVec.ofNat 32 c) n)
    (hr : (0x75C ≤ c ∧ c + n ≤ 0x7DC) ∨ (0xA78 ≤ c ∧ c + n ≤ 0xA88)) : RkV s F Ma Mb := by
  intro x _ hB hC
  refine h x ?_
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := hB.subR (c := c - 0x75C) (l := n) (by omega)
    rwa [add_ofNat_assoc, show 0x75C + (c - 0x75C) = c by omega] at this
  · have := hC.subR (c := c - 0xA78) (l := n) (by omega)
    rwa [add_ofNat_assoc, show 0xA78 + (c - 0xA78) = c by omega] at this

theorem RkV.load (E : RkEnv M0 M1 s out F P N g0) {Ma Mb : Word → BitVec 8} (h : RkV s F Ma Mb) {c : Nat}
    (hc : c + 4 ≤ 0x75C) : memLoad32 Mb (F + BitVec.ofNat 32 c) = memLoad32 Ma (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun _ hj =>
    h _ (sep_pt (E.fs (c := c) (n := 4) (d := 44) (k := 260) (Or.inr (by omega)) (by omega) (by decide)).symm hj)
      (sep_pt (rk_ff F (c := 0x75C) (n := 128) (d := c) (k := 4) (Or.inr hc) (by decide) (by omega)) hj)
      (sep_pt (rk_ff F (c := 0xA78) (n := 16) (d := c) (k := 4) (Or.inr (by omega)) (by decide) (by omega)) hj)

/-- A call to `field` from `decode_key`, with its result in the frame. -/
theorem rk_field (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    {off o n kl : Nat} {hi lo p kq ow : Word} {key : Bytes} {f : Fin 32 → Word}
    (h1 : fetchRel tufRoleKeysReadCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel tufRoleKeysReadCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : TRK + BitVec.ofNat 32 off + hi + lo = TPM_JF) (hev : (off + 8) % 2 = 0)
    (hsp : f sp = F) (h0 : f a0 = F + ow) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (ha3 : f a3 = kq) (ha4 : f a4 = BitVec.ofNat 32 kl) (how : ow = BitVec.ofNat 32 o)
    (hoV : (0x75C ≤ o ∧ o + 8 ≤ 0x7DC) ∨ (0xA78 ≤ o ∧ o + 8 ≤ 0xA88)) (hoa : o % 4 = 0)
    (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpw : p.toNat + n ≤ 0x40000000)
    (hSp : Sep s 3056 p n) (hSk : Sep (s + BitVec.ofNat 32 44) 260 kq kl) (hkey : memBytes M kq kl = key)
    (k : ∀ m2 : Machine, RkW s Md m2.mem → RkV s F M m2.mem →
      RkFR m2.mem (F + ow) (fieldRes p (objField (memBytes M0 p n) key)) →
      WP tufRoleKeysReadCode TRK Q m2.mem (off + 8)
        (clob (upd f ra (TRK + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP tufRoleKeysReadCode TRK Q M off f := by
  subst how
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have ho2 : o + 8 ≤ 0xAC0 := by omega
  have ho : RkWr (304 + o) 8 := by
    rcases hoV with ⟨_, _⟩ | ⟨_, _⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  refine WP.callField (tb := TPM_JF) (out := F + BitVec.ofNat 32 o) (s := s + BitVec.ofNat 32 44) (p := p)
    (kq := kq) (n := n) (kl := kl) h1 h2 htgt (by decide) hev hc.pm.fieldC h0 ha1 ha2 ha3 ha4
    (by rw [hsp]; exact (E.sp 44 (by decide)).symm) (E.alS (by decide)) (E.alF hoa)
    (by have := E.wS (d := 44) (k := 260) (by decide); omega) hkl hp0 (by omega)
    (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSp.sub (by decide)) hSk
    (E.fs (Or.inr (by omega)) ho2 (by decide)) (E.lowF ho2 (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.lowF ho2 (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSp, hkey] at hR
  obtain ⟨Mb, hOb, hFR⟩ := hR
  have hWb : RkW s Md Mb := hW.out hOb (Or.inl (by decide))
  have hVb : RkV s F M Mb := rkV_outS hOb
  rcases hof : objField (memBytes M0 p n) key with e | ⟨a, l⟩ <;> rw [hof] at hFR k <;>
    simp only [fieldRes, Except.map, FieldRes] at hFR k
  · obtain ⟨hOo, t1, -⟩ := hFR
    exact k m2 (hWb.out (E.outW hOo) ho) (hVb.trans (rkV_out hOo hoV)) t1
  · obtain ⟨hOo, t1, t2⟩ := hFR
    exact k m2 (hWb.out (E.outW hOo) ho) (hVb.trans (rkV_out hOo hoV)) ⟨t1, t2⟩

/-- A call to `str` from `decode_key`, with its result in the frame. -/
theorem rk_str (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    {off o n : Nat} {hi lo p ow : Word} {f : Fin 32 → Word}
    (h1 : fetchRel tufRoleKeysReadCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel tufRoleKeysReadCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : TRK + BitVec.ofNat 32 off + hi + lo = TPM_JS) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = F + ow) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (how : ow = BitVec.ofNat 32 o)
    (hoV : (0x75C ≤ o ∧ o + 8 ≤ 0x7DC) ∨ (0xA78 ≤ o ∧ o + 8 ≤ 0xA88)) (hoa : o % 4 = 0)
    (hn : n < 2 ^ 32) (hSp : Sep s 3056 p n)
    (k : ∀ m2 : Machine, RkW s Md m2.mem → RkV s F M m2.mem →
      RkSR m2.mem (F + ow) (strRes p (memBytes M0 p n)) →
      WP tufRoleKeysReadCode TRK Q m2.mem (off + 8)
        (clob (upd f ra (TRK + BitVec.ofNat 32 (off + 8))) m2 strClob)) :
    WP tufRoleKeysReadCode TRK Q M off f := by
  subst how
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have ho2 : o + 8 ≤ 0xAC0 := by omega
  have ho : RkWr (304 + o) 8 := by
    rcases hoV with ⟨_, _⟩ | ⟨_, _⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  refine WP.callStr (tb := TPM_JS) (out := F + BitVec.ofNat 32 o) (p := p) (n := n) h1 h2 htgt (by decide) hev
    hc.pm.str h0 ha1 ha2 hn (E.alF hoa) (E.lowF ho2 (by decide) (by decide)) (E.lowF ho2 (by decide) (by decide))
    fun m2 hR => ?_
  rw [E.bytes hO hSp] at hR
  rcases hs : strRes p (memBytes M0 p n) with _ | ⟨q, l⟩ <;> rw [hs] at hR k <;> simp only [SliceRes] at hR k
  · obtain ⟨hOo, t1, -⟩ := hR
    exact k m2 (hW.out (E.outW hOo) ho) (rkV_out hOo hoV) t1
  · obtain ⟨hOo, t1, t2⟩ := hR
    exact k m2 (hW.out (E.outW hOo) ho) (rkV_out hOo hoV) ⟨t1, t2⟩


/-- From 0x304: the `keyval` object, its `public` string, and the
`memset` of `pem_spki`'s buffer, then the scheme tree. -/
theorem rk_304 (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) {g : Fin 32 → Word}
    (hk : ∀ x, x ∉ rkDc → g x = gL x) {vq ktq scq : Word} {vl : Nat} {kt sc : Bytes}
    (h8 : g 8 = vq) (h9 : g 9 = BitVec.ofNat 32 vl) (h22 : (g 22).extractLsb' 0 8 = 0xFF) (h23 : g 23 = ktq)
    (hv0 : vq.toNat ≠ 0) (hvw : vq.toNat + vl ≤ 0x40000000) (hvS : Sep s 3056 vq vl)
    (hkt : memBytes M0 ktq kt.length = kt) (hSkt : Sep s 3056 ktq kt.length) (hktl : kt.length < 2 ^ 32)
    (hsc : memBytes M0 scq sc.length = sc) (hSsc : Sep s 3056 scq sc.length) (hscl : sc.length < 2 ^ 32)
    (mC : memLoad32 M (F + 0xC) = scq) (m10 : memLoad32 M (F + 0x10) = BitVec.ofNat 32 sc.length)
    (m14 : memLoad32 M (F + 0x14) = BitVec.ofNat 32 kt.length)
    (K : RkK Q s F gL Md (rkDecP kt sc (memBytes M0 vq vl))) :
    WP tufRoleKeysReadCode TRK Q M 0x304 g := by
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have hsp : g sp = F := (hk sp (by decide)).trans hLsp
  have hs8 : g 24 = F + 0xA6C := (hk 24 (by decide)).trans hL24
  refine WP.aluImm rkr_at_304 ?_; wn
  refine WP.aluImm rkr_at_308 ?_; wn
  refine WP.alu rkr_at_30a ?_; wn
  refine WP.alu rkr_at_30c ?_; wn
  refine WP.lui rkr_at_30e ?_; wn
  refine WP.aluImm rkr_at_312 ?_; wn
  refine rk_field (off := 0x316) (o := 0x75C) (ow := 0x75C) (p := vq) (n := vl) (kq := TRK_KV) (kl := 6)
    (key := ascii!"keyval") E hOd hW rkr_at_316 rkr_at_31a (by decide) (by decide) (by rsimp; exact hsp)
    (by rsimp; rw [hsp, ev_add]) (by rsimp; rw [ev0, h8]) (by rsimp; rw [ev0, h9]) (by rsimp; try rfl)
    (by rsimp; try rfl) rfl (Or.inl ⟨by decide, by decide⟩) (by decide) (by decide) hv0 hvw hvS
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) hc.mKv fun m2 hW2 hV2 hR => ?_
  rcases hof : objField (memBytes M0 vq vl) (ascii!"keyval") with e | ⟨kp, kl⟩ <;> rw [hof] at hR <;>
    simp only [fieldRes, Except.map, RkFR] at hR
  · have hm : rkDecP kt sc (memBytes M0 vq vl) = none := by simp only [rkDecP, hof]
    rw [hm] at K
    refine WP.lw rkr_at_31e (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
    refine WP.branch rkr_at_322 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by rkkeep hL0) hW2 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [hsp, hR] at eb; exact absurd eb (by decide)
  obtain ⟨r1, r2⟩ := hR
  rw [rk_e760] at r2
  have hkv := objField_val hof
  rw [memBytes_length] at hkv
  obtain ⟨hkp, hkpl⟩ := hkv
  have hkpN : (vq + BitVec.ofNat 32 kp).toNat = vq.toNat + kp := tex_toNat (by omega)
  refine WP.lw rkr_at_31e (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
  refine WP.branch rkr_at_322 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [hsp, r1, nx_q0 hv0 (by omega) hkp] at eb; exact absurd eb (by decide)
  wn
  refine WP.lw rkr_at_326 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_32a ?_; wn
  refine WP.aluImm rkr_at_32e ?_; wn
  refine WP.aluImm rkr_at_332 ?_; wn
  refine WP.lui rkr_at_334 ?_; wn
  refine WP.aluImm rkr_at_338 ?_; wn
  refine rk_field (off := 0x33C) (o := 0xA80) (ow := 0xA80) (p := vq + BitVec.ofNat 32 kp) (n := kl)
    (kq := TRK_PUB) (kl := 6) (key := ascii!"public") E hOd hW2 rkr_at_33c rkr_at_340 (by decide) (by decide)
    (by rsimp; exact hsp) (by rsimp; rw [hsp, rk_a80]) (by rsimp; rw [hsp, r1]) (by rsimp; rw [hsp, r2])
    (by rsimp; try rfl) (by rsimp; try rfl) rfl (Or.inr ⟨by decide, by decide⟩) (by decide) (by decide)
    (by rw [hkpN]; omega) (by rw [hkpN]; omega) (hvS.subR (by omega))
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.code (hOd.trans hW2.outer)).mPub
    fun m3 hW3 hV3 hR3 => ?_
  have hsl1 : memBytes M0 (vq + BitVec.ofNat 32 kp) kl = slice (memBytes M0 vq vl) kp kl :=
    (tuf_memBytes_drop_take hkpl).symm
  rw [hsl1] at hR3
  rcases hof2 : objField (slice (memBytes M0 vq vl) kp kl) (ascii!"public") with e | ⟨pp, pl⟩ <;>
    rw [hof2] at hR3 <;> simp only [fieldRes, Except.map, RkFR] at hR3
  · have hm : rkDecP kt sc (memBytes M0 vq vl) = none := by simp only [rkDecP, hof, hof2]
    rw [hm] at K
    refine WP.lw rkr_at_344 (by rsimp; rw [hs8, rk_s14]; exact E.alF (c := 0xA80) (by decide)) ?_; wn
    refine WP.branch rkr_at_348 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by rkkeep hL0) hW3 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [hs8, rk_s14, hR3] at eb; exact absurd eb (by decide)
  obtain ⟨r3, r4⟩ := hR3
  rw [rk_eA84] at r4
  have hpv := objField_val hof2
  rw [← hsl1, memBytes_length] at hpv
  obtain ⟨hpp, hppl⟩ := hpv
  refine WP.lw rkr_at_344 (by rsimp; rw [hs8, rk_s14]; exact E.alF (c := 0xA80) (by decide)) ?_; wn
  refine WP.branch rkr_at_348 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb
    rw [hs8, rk_s14, r3, nx_q0 (by rw [hkpN]; omega) (by rw [hkpN]; omega) hpp] at eb
    exact absurd eb (by decide)
  wn
  refine WP.alu rkr_at_34c ?_; wn
  refine WP.lw rkr_at_34e (by rsimp; rw [ev0, hs8, rk_s18]; exact E.alF (c := 0xA84) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_350 ?_; wn
  refine WP.aluImm rkr_at_354 ?_; wn
  have hq2 : vq + BitVec.ofNat 32 kp + BitVec.ofNat 32 pp = vq + BitVec.ofNat 32 (kp + pp) :=
    add_ofNat_assoc _ _ _
  refine rk_str (off := 0x358) (o := 0xA78) (ow := 0xA78) (p := vq + BitVec.ofNat 32 kp + BitVec.ofNat 32 pp)
    (n := pl) E hOd hW3 rkr_at_358 rkr_at_35c (by decide) (by decide) (by rsimp; rw [hsp, rk_a78])
    (by rsimp; rw [hs8, rk_s14, r3]) (by rsimp; rw [ev0, hs8, rk_s18, r4]) rfl (Or.inr ⟨by decide, by decide⟩)
    (by decide) (by omega) (by rw [hq2]; exact hvS.subR (by omega)) fun m4 hW4 hV4 hR4 => ?_
  have hsl2 : memBytes M0 (vq + BitVec.ofNat 32 kp + BitVec.ofNat 32 pp) pl =
      slice (slice (memBytes M0 vq vl) kp kl) pp pl := by
    rw [← hsl1]; exact (tuf_memBytes_drop_take hppl).symm
  rw [hsl2, tex_strRes] at hR4
  rcases hsb : strBody (slice (slice (memBytes M0 vq vl) kp kl) pp pl) with _ | pub <;> rw [hsb] at hR4 <;>
    simp only [Option.map, RkSR] at hR4
  · have hm : rkDecP kt sc (memBytes M0 vq vl) = none := by simp only [rkDecP, hof, hof2, hsb]
    rw [hm] at K
    refine WP.lw rkr_at_360 (by rsimp; rw [ev0, hs8, rk_s0C]; exact E.alF (c := 0xA78) (by decide)) ?_; wn
    refine WP.branch rkr_at_362 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by rkkeep hL0) hW4 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [ev0, hs8, rk_s0C, hR4] at eb; exact absurd eb (by decide)
  obtain ⟨r5, r6⟩ := hR4
  rw [rk_eA7C] at r6
  obtain ⟨hpub0, hpl2⟩ := rk_strB (show strBody (memBytes M0 (vq + BitVec.ofNat 32 kp + BitVec.ofNat 32 pp) pl) =
    some pub by rw [hsl2]; exact hsb)
  have hpq : vq + BitVec.ofNat 32 kp + BitVec.ofNat 32 pp + 1 = vq + BitVec.ofNat 32 (kp + pp + 1) := by
    rw [hq2]; exact rk_p1 _ _
  have hpqN : (vq + BitVec.ofNat 32 (kp + pp + 1)).toNat = vq.toNat + (kp + pp + 1) := tex_toNat (by omega)
  refine WP.lw rkr_at_360 (by rsimp; rw [ev0, hs8, rk_s0C]; exact E.alF (c := 0xA78) (by decide)) ?_; wn
  refine WP.branch rkr_at_362 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb
    rw [ev0, hs8, rk_s0C, r5, hpq, nx_q0 (p := vq) (n := vl) hv0 (by omega) (by omega)] at eb
    exact absurd eb (by decide)
  wn
  refine WP.lw rkr_at_366 (by rsimp; rw [hs8, rk_s10]; exact E.alF (c := 0xA7C) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_36a ?_; wn
  refine WP.aluImm rkr_at_36e ?_; wn
  refine WP.aluImm rkr_at_372 ?_; wn
  refine WP.callMemsetT (tb := TPS_MS) (dst := F + BitVec.ofNat 32 0x75C) (b := 0) (n := 128) rkr_at_374
    rkr_at_378 (by decide) (by decide) (by decide) (E.code (hOd.trans hW4.outer)).tps.ms
    (by rsimp; rw [hsp, ev_add]; try rfl) (by rsimp; try rfl) (by rsimp; try rfl)
    (Nat.lt_of_le_of_lt (E.wF (c := 0x75C) (k := 128) (by decide)) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.cF (by decide)) fun m5 hm5 => ?_
  have hO5 : Out m4.mem m5.mem (F + BitVec.ofNat 32 0x75C) 128 := by
    rw [hm5]; exact fun x hx => fillBytes_sep hx.symm (Nat.le_refl _)
  have hW5 : RkW s Md m5.mem := hW4.out (E.outW hO5) (Or.inr (Or.inl ⟨by decide, by decide⟩))
  have hV : RkV s F M m5.mem := ((hV2.trans hV3).trans hV4).trans (rkV_out hO5 (Or.inl ⟨by decide, by decide⟩))
  have hO5' : Out M1 m5.mem s 3004 := hOd.trans hW5.outer
  have hSpq : Sep s 3056 (vq + BitVec.ofNat 32 (kp + pp + 1)) pub.length := hvS.subR (by omega)
  have hkey : rkDecP kt sc (memBytes M0 vq vl) = rkKey kt sc pub := by simp only [rkDecP, hof, hof2, hsb]
  rw [hkey] at K
  exact RkT.t37c (pq := vq + BitVec.ofNat 32 (kp + pp + 1)) (pl := pub.length)
    ⟨E, hOd, hW5, hL0, hLsp, hL24, by rw [hpqN]; omega, hSpq, by rw [E.bytes hO5' hSpq, ← hpq]; exact hpub0,
      by rw [E.bytes hO5' hSkt]; exact hkt, by rw [E.bytes hO5' hSsc]; exact hsc,
      (hV.load E (c := 0xC) (by decide)).trans mC, (hV.load E (c := 0x10) (by decide)).trans m10,
      (hV.load E (c := 0x14) (by decide)).trans m14, hktl, hscl, K⟩
    (by rkkeep hL0) (by rsimp; rw [ev0, hs8, rk_s0C, r5, hpq]) (by rsimp; rw [hs8, rk_s10, r6])
    (by rsimp; exact h22) (by rsimp; exact h23)


/-- From 0x2B6: the `scheme` string, kept at `F + 0xC`, then 0x304. -/
theorem rk_2b6 (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) {g : Fin 32 → Word}
    (hk : ∀ x, x ∉ rkDc → g x = gL x) {vq ktq : Word} {vl : Nat} {kt : Bytes}
    (h8 : g 8 = vq) (h9 : g 9 = BitVec.ofNat 32 vl) (h22 : (g 22).extractLsb' 0 8 = 0xFF) (h23 : g 23 = ktq)
    (hv0 : vq.toNat ≠ 0) (hvw : vq.toNat + vl ≤ 0x40000000) (hvS : Sep s 3056 vq vl)
    (hkt : memBytes M0 ktq kt.length = kt) (hSkt : Sep s 3056 ktq kt.length) (hktl : kt.length < 2 ^ 32)
    (m14 : memLoad32 M (F + 0x14) = BitVec.ofNat 32 kt.length)
    (K : RkK Q s F gL Md (rkDecS kt (memBytes M0 vq vl))) :
    WP tufRoleKeysReadCode TRK Q M 0x2B6 g := by
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have hsp : g sp = F := (hk sp (by decide)).trans hLsp
  have hs8 : g 24 = F + 0xA6C := (hk 24 (by decide)).trans hL24
  refine WP.aluImm rkr_at_2b6 ?_; wn
  refine WP.aluImm rkr_at_2ba ?_; wn
  refine WP.alu rkr_at_2bc ?_; wn
  refine WP.alu rkr_at_2be ?_; wn
  refine WP.lui rkr_at_2c0 ?_; wn
  refine WP.aluImm rkr_at_2c4 ?_; wn
  refine rk_field (off := 0x2C8) (o := 0x75C) (ow := 0x75C) (p := vq) (n := vl) (kq := TRK_SC) (kl := 6)
    (key := ascii!"scheme") E hOd hW rkr_at_2c8 rkr_at_2cc (by decide) (by decide) (by rsimp; exact hsp)
    (by rsimp; rw [hsp, ev_add]) (by rsimp; rw [ev0, h8]) (by rsimp; rw [ev0, h9]) (by rsimp; try rfl)
    (by rsimp; try rfl) rfl (Or.inl ⟨by decide, by decide⟩) (by decide) (by decide) hv0 hvw hvS
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) hc.mSc fun m2 hW2 hV2 hR => ?_
  rcases hof : objField (memBytes M0 vq vl) (ascii!"scheme") with e | ⟨sp', sl⟩ <;> rw [hof] at hR <;>
    simp only [fieldRes, Except.map, RkFR] at hR
  · have hm : rkDecS kt (memBytes M0 vq vl) = none := by simp only [rkDecS, hof]
    rw [hm] at K
    refine WP.lw rkr_at_2d0 (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
    refine WP.branch rkr_at_2d4 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6f2 hL0 (by rkkeep hL0) hW2 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [hsp, hR] at eb; exact absurd eb (by decide)
  obtain ⟨r1, r2⟩ := hR
  rw [rk_e760] at r2
  have hsv := objField_val hof
  rw [memBytes_length] at hsv
  obtain ⟨hsp', hspl⟩ := hsv
  refine WP.lw rkr_at_2d0 (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
  refine WP.branch rkr_at_2d4 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [hsp, r1, nx_q0 hv0 (by omega) hsp'] at eb; exact absurd eb (by decide)
  wn
  refine WP.lw rkr_at_2d8 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_2dc ?_; wn
  refine WP.aluImm rkr_at_2e0 ?_; wn
  refine rk_str (off := 0x2E4) (o := 0xA80) (ow := 0xA80) (p := vq + BitVec.ofNat 32 sp') (n := sl)
    E hOd hW2 rkr_at_2e4 rkr_at_2e8 (by decide) (by decide) (by rsimp; rw [hsp, rk_a80])
    (by rsimp; rw [hsp, r1]) (by rsimp; rw [hsp, r2]) rfl (Or.inr ⟨by decide, by decide⟩)
    (by decide) (by omega) (hvS.subR (by omega)) fun m3 hW3 hV3 hR3 => ?_
  have hsl : memBytes M0 (vq + BitVec.ofNat 32 sp') sl = slice (memBytes M0 vq vl) sp' sl :=
    (tuf_memBytes_drop_take hspl).symm
  rw [hsl, tex_strRes] at hR3
  rcases hsb : strBody (slice (memBytes M0 vq vl) sp' sl) with _ | sc <;> rw [hsb] at hR3 <;>
    simp only [Option.map, RkSR] at hR3
  · have hm : rkDecS kt (memBytes M0 vq vl) = none := by simp only [rkDecS, hof, hsb]
    rw [hm] at K
    refine WP.lw rkr_at_2ec (by rsimp; rw [hs8, rk_s14]; exact E.alF (c := 0xA80) (by decide)) ?_; wn
    refine WP.branch rkr_at_2f0 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6f2 hL0 (by rkkeep hL0) hW3 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [hs8, rk_s14, hR3] at eb; exact absurd eb (by decide)
  obtain ⟨r5, r6⟩ := hR3
  rw [rk_eA84] at r6
  obtain ⟨hsc0, hsl2⟩ := rk_strB (show strBody (memBytes M0 (vq + BitVec.ofNat 32 sp') sl) = some sc by
    rw [hsl]; exact hsb)
  have hscq : vq + BitVec.ofNat 32 sp' + 1 = vq + BitVec.ofNat 32 (sp' + 1) := rk_p1 _ _
  refine WP.lw rkr_at_2ec (by rsimp; rw [hs8, rk_s14]; exact E.alF (c := 0xA80) (by decide)) ?_; wn
  refine WP.branch rkr_at_2f0 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb
    rw [hs8, rk_s14, r5, hscq, nx_q0 (p := vq) (n := vl) hv0 (by omega) (by omega)] at eb
    exact absurd eb (by decide)
  wn
  refine WP.sw rkr_at_2f4 (by rsimp; rw [hsp]; exact E.alF (c := 0xC) (by decide))
    (by rsimp; rw [hsp]; exact E.cF (by decide)) ?_; wn
  refine WP.aluImm rkr_at_2f6 ?_; wn
  refine WP.aluImm rkr_at_2fa ?_; wn
  refine WP.lw rkr_at_2fe (by rsimp; rw [hsp, rk_a6c, rk_s18]; exact E.alF (c := 0xA84) (by decide)) ?_; wn
  refine WP.sw rkr_at_302 (by rsimp; rw [hsp]; exact E.alF (c := 0x10) (by decide))
    (by rsimp; rw [hsp]; exact E.cF (by decide)) ?_; wn
  rw [rkDecS_sc hof hsb] at K
  have s10C : Sep (F + 0x10) 4 (F + 0xC) 4 := rk_ff F (c := 0x10) (n := 4) (d := 0xC) (k := 4) (Or.inr (by decide))
    (by decide) (by decide)
  have sCA84 : Sep (F + 0xC) 4 (F + 0xA84) 4 := rk_ff F (c := 0xC) (n := 4) (d := 0xA84) (k := 4)
    (Or.inl (by decide)) (by decide) (by decide)
  have s1014 : Sep (F + 0x10) 4 (F + 0x14) 4 := rk_ff F (c := 0x10) (n := 4) (d := 0x14) (k := 4)
    (Or.inl (by decide)) (by decide) (by decide)
  have sC14 : Sep (F + 0xC) 4 (F + 0x14) 4 := rk_ff F (c := 0xC) (n := 4) (d := 0x14) (k := 4)
    (Or.inl (by decide)) (by decide) (by decide)
  refine rk_304 (scq := vq + BitVec.ofNat 32 sp' + 1) (sc := sc) E hOd ?_ hL0 hLsp hL24 ?_ (by rsimp; exact h8)
    (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; exact h23) hv0 hvw hvS hkt hSkt hktl hsc0
    (by rw [hscq]; exact hvS.subR (by omega)) (by omega) ?_ ?_ ?_ K
  · rw [hsp]
    exact (hW3.out (E.outW (c := 0xC) (out_store32 _ _ _)) (Or.inl (by decide))).out
      (E.outW (c := 0x10) (out_store32 _ _ _)) (Or.inl (by decide))
  · refine keepUpd0 hL0 (by decide) ?_
    refine rk_keepS (by rw [hsp, rk_a6c, hL24]) hL0 ?_
    rkkeep hL0
  · rw [hsp, memLoad32_store32_sep s10C, memLoad32_store32_same, hs8, rk_s14, r5]
  · rw [hsp, memLoad32_store32_same, rk_a6c, rk_s18, memLoad32_store32_sep sCA84, r6]
  · rw [hsp, memLoad32_store32_sep s1014, memLoad32_store32_sep sC14]
    exact ((hV2.trans hV3).load E (c := 0x14) (by decide)).trans m14

/-- From 0x26E: the `keytype` string, its length kept at `F + 0x14`,
then 0x2B6. -/
theorem rk_26e (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) {g : Fin 32 → Word}
    (hk : ∀ x, x ∉ rkDc → g x = gL x) {vq : Word} {vl : Nat}
    (h8 : g 8 = vq) (h22 : (g 22).extractLsb' 0 8 = 0xFF) (h23 : g 23 = 9)
    (m764 : memLoad32 M (F + 0x764) = BitVec.ofNat 32 vl)
    (hv0 : vq.toNat ≠ 0) (hvw : vq.toNat + vl ≤ 0x40000000) (hvS : Sep s 3056 vq vl)
    (K : RkK Q s F gL Md (rkDecode (memBytes M0 vq vl))) :
    WP tufRoleKeysReadCode TRK Q M 0x26E g := by
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have hsp : g sp = F := (hk sp (by decide)).trans hLsp
  have hs8 : g 24 = F + 0xA6C := (hk 24 (by decide)).trans hL24
  refine WP.lw rkr_at_26e (by rw [hsp]; exact E.alF (c := 0x764) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_272 ?_; wn
  refine WP.aluImm rkr_at_276 ?_; wn
  refine WP.alu rkr_at_278 ?_; wn
  refine WP.alu rkr_at_27a ?_; wn
  refine WP.lui rkr_at_27c ?_; wn
  refine WP.aluImm rkr_at_280 ?_; wn
  refine rk_field (off := 0x284) (o := 0x75C) (ow := 0x75C) (p := vq) (n := vl) (kq := TRK_KT) (kl := 7)
    (key := ascii!"keytype") E hOd hW rkr_at_284 rkr_at_288 (by decide) (by decide) (by rsimp; exact hsp)
    (by rsimp; rw [hsp, ev_add]) (by rsimp; rw [ev0, h8]) (by rsimp; rw [ev0, hsp, m764]) (by rsimp; try rfl)
    (by rsimp; try rfl) rfl (Or.inl ⟨by decide, by decide⟩) (by decide) (by decide) hv0 hvw hvS
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) hc.mKt fun m2 hW2 hV2 hR => ?_
  rcases hof : objField (memBytes M0 vq vl) (ascii!"keytype") with e | ⟨tp, tl⟩ <;> rw [hof] at hR <;>
    simp only [fieldRes, Except.map, RkFR] at hR
  · have hm : rkDecode (memBytes M0 vq vl) = none := by simp only [rkDecode, hof]
    rw [hm] at K
    refine WP.lw rkr_at_28c (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
    refine WP.branch rkr_at_290 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact K _ _ (by rkkeep hL0) (by rsimp; exact h23) hW2 (by rsimp; exact h22) trivial
    · exfalso; rsimp at eb; rw [hsp, hR] at eb; exact absurd eb (by decide)
  obtain ⟨r1, r2⟩ := hR
  rw [rk_e760] at r2
  have htv := objField_val hof
  rw [memBytes_length] at htv
  obtain ⟨htp, htpl⟩ := htv
  refine WP.lw rkr_at_28c (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
  refine WP.branch rkr_at_290 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [hsp, r1, nx_q0 hv0 (by omega) htp] at eb; exact absurd eb (by decide)
  wn
  refine WP.lw rkr_at_294 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_298 ?_; wn
  refine WP.aluImm rkr_at_29c ?_; wn
  refine rk_str (off := 0x2A0) (o := 0xA80) (ow := 0xA80) (p := vq + BitVec.ofNat 32 tp) (n := tl)
    E hOd hW2 rkr_at_2a0 rkr_at_2a4 (by decide) (by decide) (by rsimp; rw [hsp, rk_a80])
    (by rsimp; rw [hsp, r1]) (by rsimp; rw [hsp, r2]) rfl (Or.inr ⟨by decide, by decide⟩)
    (by decide) (by omega) (hvS.subR (by omega)) fun m3 hW3 hV3 hR3 => ?_
  have hsl : memBytes M0 (vq + BitVec.ofNat 32 tp) tl = slice (memBytes M0 vq vl) tp tl :=
    (tuf_memBytes_drop_take htpl).symm
  rw [hsl, tex_strRes] at hR3
  rcases hsb : strBody (slice (memBytes M0 vq vl) tp tl) with _ | kt <;> rw [hsb] at hR3 <;>
    simp only [Option.map, RkSR] at hR3
  · have hm : rkDecode (memBytes M0 vq vl) = none := by simp only [rkDecode, hof, hsb]
    rw [hm] at K
    refine WP.lw rkr_at_2a8 (by rsimp; rw [hs8, rk_s14]; exact E.alF (c := 0xA80) (by decide)) ?_; wn
    refine WP.branch rkr_at_2ac (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6f2 hL0 (by rkkeep hL0) hW3 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [hs8, rk_s14, hR3] at eb; exact absurd eb (by decide)
  obtain ⟨r5, r6⟩ := hR3
  rw [rk_eA84] at r6
  obtain ⟨hkt0, hktl2⟩ := rk_strB (show strBody (memBytes M0 (vq + BitVec.ofNat 32 tp) tl) = some kt by
    rw [hsl]; exact hsb)
  have hktq : vq + BitVec.ofNat 32 tp + 1 = vq + BitVec.ofNat 32 (tp + 1) := rk_p1 _ _
  refine WP.lw rkr_at_2a8 (by rsimp; rw [hs8, rk_s14]; exact E.alF (c := 0xA80) (by decide)) ?_; wn
  refine WP.branch rkr_at_2ac (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb
    rw [hs8, rk_s14, r5, hktq, nx_q0 (p := vq) (n := vl) hv0 (by omega) (by omega)] at eb
    exact absurd eb (by decide)
  wn
  refine WP.lw rkr_at_2b0 (by rsimp; rw [hs8, rk_s18]; exact E.alF (c := 0xA84) (by decide)) ?_; wn
  refine WP.sw rkr_at_2b4 (by rsimp; rw [hsp]; exact E.alF (c := 0x14) (by decide))
    (by rsimp; rw [hsp]; exact E.cF (by decide)) ?_; wn
  rw [rkDecode_kt hof hsb] at K
  refine rk_2b6 (ktq := vq + BitVec.ofNat 32 tp + 1) (kt := kt) E hOd ?_ hL0 hLsp hL24 (by rkkeep hL0)
    (by rsimp; exact h8) (by rsimp; rw [hsp, m764]) (by rsimp; exact h22) (by rsimp; rw [hs8, rk_s14, r5])
    hv0 hvw hvS hkt0 (by rw [hktq]; exact hvS.subR (by omega)) (by omega) ?_ K
  · rw [hsp]; exact hW3.out (E.outW (c := 0x14) (out_store32 _ _ _)) (Or.inl (by decide))
  · rw [hsp, memLoad32_store32_same, hs8, rk_s18, r6]

end

end C3.RV32
