import C3BootProofs.Proofs.SvLib2

/-!
# `sigstore::verify`: calls to the `Der` readers

Each lemma here takes a call to one `Der` reader from the frame of
`sigstore::verify`, with the result and the reader at offsets of the
frame, to what the generated stages track: which frame bytes the call kept,
the result's words when the read succeeded or failed, and that nothing
outside the stack changed.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- `M'` agrees with `M` on the frame, except for the ranges in `L`. -/
def SvKeepL (B : Word) (M M' : Word → BitVec 8) (L : List (Nat × Nat)) : Prop :=
  ∀ e, e + 1 ≤ 0x1690 → (∀ p ∈ L, e < p.1 ∨ p.1 + p.2 ≤ e) →
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e)

theorem SvKeepL.w32 {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {e : Nat} (K : SvKeepL B M M' L)
    (he : e + 4 ≤ 0x1690) (h : ∀ p ∈ L, e + 4 ≤ p.1 ∨ p.1 + p.2 ≤ e) :
    memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) = memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact K _ (by omega) fun p hp => by have := h p hp; omega

theorem SvKeepL.b8 {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {e : Nat} (K : SvKeepL B M M' L)
    (he : e + 1 ≤ 0x1690) (h : ∀ p ∈ L, e + 1 ≤ p.1 ∨ p.1 + p.2 ≤ e) :
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  K _ he fun p hp => by have := h p hp; omega

theorem SvSaves.keepL {B : Word} {M M' : Word → BitVec 8} {v : Nat → Word} {L : List (Nat × Nat)}
    (V : SvSaves B M v) (K : SvKeepL B M M' L) (h : ∀ p ∈ L, p.1 + p.2 ≤ 0x165C) : SvSaves B M' v := fun k hk => by
  rw [← V k hk, show 0x382C - 4 * k = 0x21A0 + (0x168C - 4 * k) by omega, sv_base]
  exact K.w32 (by omega) fun p hp => by have := h p hp; omega

theorem lit4 (S : Word) (c : Nat) (hc : c + 4 < 2 ^ 32) : S + BitVec.ofNat 32 c + 4 = S + BitVec.ofNat 32 (c + 4) :=
  frame_lit _ (by simpa using hc)
theorem lit8 (S : Word) (c : Nat) (hc : c + 8 < 2 ^ 32) : S + BitVec.ofNat 32 c + 8 = S + BitVec.ofNat 32 (c + 8) :=
  frame_lit _ (by simpa using hc)
theorem lit12 (S : Word) (c : Nat) (hc : c + 12 < 2 ^ 32) :
    S + BitVec.ofNat 32 c + 0xC = S + BitVec.ofNat 32 (c + 12) := frame_lit _ (by simpa using hc)

/-- The words a successful read leaves: the content's address and length,
twice, at the result, and the reader moved past the element. -/
def DerOkW (M : Word → BitVec 8) (B : Word) (oc dc : Nat) (rp rl : Word) (t : DerTlv) : Prop :=
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = rp + BitVec.ofNat 32 t.header ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = BitVec.ofNat 32 t.len ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = rp + BitVec.ofNat 32 t.header ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 12)) = BitVec.ofNat 32 t.len ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp + BitVec.ofNat 32 (t.header + t.len) ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl - BitVec.ofNat 32 (t.header + t.len)

/-- What a failed read leaves: a null address and the error's code. -/
def DerErrW (M : Word → BitVec 8) (B : Word) (oc : Nat) (e : DerError) : Prop :=
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧ M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = derErrByte e

set_option maxHeartbeats 8000000 in
/-- What `derNestedMem` leaves on the frame. -/
theorem dnm_facts {B : Word} {M M' : Word → BitVec 8} {oc dc : Nat} {rp rl : Word} (r : Except DerError DerTlv)
    (ho2 : oc + 16 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 16 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (f : ∀ x, Sep (B + BitVec.ofNat 32 0x2180) 0x20 x 1 →
      M' x = derNestedMem (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r) (B + 0x21A0 + BitVec.ofNat 32 oc)
        rp r x) :
    SvKeepL B M M' [(oc, 16), (dc + 8, 8)] ∧ (∀ t, r = .ok t → DerOkW M' B oc dc rp rl t) ∧
      (∀ e, r = .error e → DerErrW M' B oc e) ∧ (∀ x, SvR B x → M' x = M x) := by
  have fS : ∀ e, e + 1 ≤ 0x1690 → Sep (B + BitVec.ofNat 32 0x2180) 0x20 (B + 0x21A0 + BitVec.ofNat 32 e) 1 :=
    fun e he => by rw [← sv_base]; exact sepS B (by omega) (by omega) (by omega)
  have fS4 : ∀ e, e + 4 ≤ 0x1690 → ∀ j, j < 4 →
      Sep (B + BitVec.ofNat 32 0x2180) 0x20 (B + 0x21A0 + BitVec.ofNat 32 e + BitVec.ofNat 32 j) 1 :=
    fun e he j hj => by rw [add_ofNat_assoc]; exact fS _ (by omega)
  have ld : ∀ e, e + 4 ≤ 0x1690 → memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) =
      memLoad32 (derNestedMem (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r)
        (B + 0x21A0 + BitVec.ofNat 32 oc) rp r) (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun e he => memLoad32_congr fun j hj => f _ (fS4 e he j hj)
  have o4 := lit4 (B + 0x21A0) oc (by omega)
  have o8 := lit8 (B + 0x21A0) oc (by omega)
  have o12 := lit12 (B + 0x21A0) oc (by omega)
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have st : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a + 4 ≤ 0x1690 → e + 1 ≤ 0x1690 → (a + 4 ≤ e ∨ e + 1 ≤ a) →
      memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  have st8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x1690 → e + 1 ≤ 0x1690 → a ≠ e →
      memStore8 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore8_ne (add_ofNat_ne _ (by omega) (by omega) (Ne.symm h))
  have ldst : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a % 4 = 0 → e % 4 = 0 → a + 4 ≤ 0x1690 →
      e + 4 ≤ 0x1690 → memLoad32 (memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v) (B + 0x21A0 + BitVec.ofNat 32 e) =
        if a = e then v else memLoad32 N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 h4 => ld_st_sv h1 h2 (by omega) (by omega)
  refine ⟨fun e he hL => ?_, fun t ht => ?_, fun er he => ?_, fun x hx => ?_⟩
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    rw [f _ (fS e he)]
    cases r with
    | error er =>
      simp only [derNestedMem, derAdvance]
      rw [st _ oc e _ (by omega) he (by omega), o4, st8 _ (oc + 4) e _ (by omega) he (by omega)]
    | ok t =>
      simp only [derNestedMem, derAdvance]
      rw [st _ oc e _ (by omega) he (by omega), o12, st _ (oc + 12) e _ (by omega) he (by omega), o4,
        st _ (oc + 4) e _ (by omega) he (by omega), o8, st _ (oc + 8) e _ (by omega) he (by omega), d12,
        st _ (dc + 12) e _ (by omega) he (by omega), d8, st _ (dc + 8) e _ (by omega) he (by omega)]
  · subst ht
    simp only [DerOkW]
    rw [ld _ (by omega), ld _ (by omega), ld _ (by omega), ld _ (by omega), ld _ (by omega), ld _ (by omega)]
    simp only [derNestedMem, derAdvance]
    rw [o4, o8, o12, d8, d12]
    simp (disch := omega) only [ldst, ite_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp (disch := omega) only [ite_eq_right]
  · subst he
    refine ⟨?_, ?_⟩
    · rw [ld _ (by omega)]; simp only [derNestedMem]; rw [memLoad32_store32_same]
    · rw [f _ (fS _ (by omega))]; simp only [derNestedMem, derAdvance]
      rw [o4, st _ oc (oc + 4) _ (by omega) (by omega) (by omega), memStore8_same]
  · have hx' : ∀ c, c + 1 ≤ 0x1690 → Sep (B + 0x21A0 + BitVec.ofNat 32 c) 1 x 1 := fun c hc => svR_hi hx hc
    have hxF : Sep (B + BitVec.ofNat 32 0x2180) 0x20 x 1 := by
      have := svR_lo (k := 0x20) hx (by decide) (by decide)
      rwa [show B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - 0x20) = B + BitVec.ofNat 32 0x2180 by
        rw [BitVec.add_assoc]; rfl] at this
    have s4 : ∀ (N : Word → BitVec 8) (a : Nat) (v : Word), a + 4 ≤ 0x1690 →
        memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v x = N x := fun N a v ha =>
      memStore32_get_sep (svR_hi hx ha)
    rw [f x hxF]
    cases r with
    | error er =>
      simp only [derNestedMem, derAdvance]
      rw [s4 _ oc _ (by omega), o4, memStore8_ne (sep1_ne (hx' (oc + 4) (by omega)))]
    | ok t =>
      simp only [derNestedMem, derAdvance]
      rw [s4 _ oc _ (by omega), o12, s4 _ (oc + 12) _ (by omega), o4, s4 _ (oc + 4) _ (by omega), o8,
        s4 _ (oc + 8) _ (by omega), d12, s4 _ (dc + 12) _ (by omega), d8, s4 _ (dc + 8) _ (by omega)]

theorem br_beq_t {a b : Word} (h : a = b) : branchTaken .beq a b = true := by simp [branchTaken, h]
theorem br_beq_f {a b : Word} (h : a ≠ b) : branchTaken .beq a b = false := by simp [branchTaken, h]
theorem br_bne_t {a b : Word} (h : a ≠ b) : branchTaken .bne a b = true := by simp [branchTaken, h]
theorem br_bne_f {a b : Word} (h : a = b) : branchTaken .bne a b = false := by simp [branchTaken, h]

/-- Where `sigstore::verify` writes its result: two bytes outside the stack
and the code. -/
structure SvOut (B out : Word) : Prop where
  stk : Sep out 2 (B + 0xFFFFFE60) 0x39D0
  code : Sep out 2 SV sigstoreVerifyCode.length

/-- `sigstore::verify` returned `Err`: from `n0`, the machine reaches the
return address with the stack and the callee-saved registers restored,
`Err`'s discriminant 1 at `out`, and memory outside the stack unchanged
except for the result. -/
def SvErrRet (B out : Word) (v : Nat → Word) (n0 : Machine) : Prop :=
  ∃ n', Steps n0 n' ∧ n'.pc = v 0 ∧ reg n' sp = B + 0x3830 ∧ (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
    reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧ n'.mem out = 1 ∧
    ∀ x, SvR B x → x ≠ out → x ≠ out + 1 → n'.mem x = n0.mem x

/-- **The failing exit**: from a step at 0x966, `sigstore::verify` returns `Err`. -/
theorem sv_fail {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0x966 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have sOS : Sep out 2 (B + BitVec.ofNat 32 0x37FC) 0x34 := by
    have := hO.stk.symm.sub (c := 0x1A0 + 0x37FC) (l := 0x34) (by decide)
    rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x37FC) = B + BitVec.ofNat 32 0x37FC by
      rw [BitVec.add_assoc]; rfl] at this
    exact this.symm
  obtain ⟨n', c', pc', mem', sp', sv', g', t'⟩ := sv_err E.self F s rsp hout V hret sOS hO.code
  refine ⟨n', t.trans c', pc', sp', sv', by rw [g', r3], by rw [t', r4], ?_, fun x hx h0 h1 => ?_⟩
  · rw [mem']; unfold svErrMem
    rw [memStore8_ne (show out ≠ out + 1 by
      have := add_ofNat_ne out (c := 0) (d := 1) (by decide) (by decide) (by decide)
      rwa [add_ofNat_zero] at this), memStore8_same]
  · rw [mem']; unfold svErrMem; rw [memStore8_ne h1, memStore8_ne h0, fR x hx]

/-- The content of an element read from bytes outside the stack is outside it too. -/
theorem SvIn.content {B rp : Word} {M : Word → BitVec 8} {rl tag : Nat} {t : DerTlv} (h : SvIn B rp rl)
    (ht : derElement tag (memBytes M rp rl) = .ok t) : SvIn B (rp + BitVec.ofNat 32 t.header) t.len := by
  have hb := derElement_bound ht
  rw [memBytes_length] at hb
  have e : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.fit; omega
  refine ⟨?_, by rw [e]; have := h.pos; omega, by rw [e]; have := h.fit; omega⟩
  have := h.sep.sub (c := t.header) (l := t.len) (by omega)
  exact this

/-- So are the bytes after it. -/
theorem SvIn.rest {B rp : Word} {M : Word → BitVec 8} {rl tag : Nat} {t : DerTlv} (h : SvIn B rp rl)
    (ht : derElement tag (memBytes M rp rl) = .ok t) :
    SvIn B (rp + BitVec.ofNat 32 (t.header + t.len)) (rl - (t.header + t.len)) := by
  have hb := derElement_bound ht
  rw [memBytes_length] at hb
  have e : (rp + BitVec.ofNat 32 (t.header + t.len)).toNat = rp.toNat + (t.header + t.len) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.fit; omega
  refine ⟨?_, by rw [e]; have := h.pos; omega, by rw [e]; have := h.fit; omega⟩
  exact h.sep.sub (c := t.header + t.len) (l := rl - (t.header + t.len)) (by omega)

/-- A successful read's content address isn't null. -/
theorem SvIn.ok_ne {B rp : Word} {M : Word → BitVec 8} {rl tag : Nat} {t : DerTlv} (h : SvIn B rp rl)
    (ht : derElement tag (memBytes M rp rl) = .ok t) : rp + BitVec.ofNat 32 t.header ≠ 0 := fun e => by
  have := (h.content ht).pos; rw [e] at this; exact absurd this (by decide)

/-- The length left after a read. -/
theorem rest_len {rp rl : Word} {M : Word → BitVec 8} {tag : Nat} {t : DerTlv}
    (ht : derElement tag (memBytes M rp rl.toNat) = .ok t) :
    (rl - BitVec.ofNat 32 (t.header + t.len)).toNat = rl.toNat - (t.header + t.len) := by
  have hb := derElement_bound ht
  rw [memBytes_length] at hb
  have hlt := rl.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show t.header + t.len < 2 ^ 32 by omega)]
  simp only [Nat.reducePow] at hlt ⊢
  omega

/-- **A call to `Der::sequence`**, as the generated stages track it. -/
theorem sv_seqF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derSequenceAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 16 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 16 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 16), (dc + 8, 8)] ∧
      (∀ t, derElement 0x30 (memBytes M rp rl.toNat) = .ok t → DerOkW n'.mem B oc dc rp rl t) ∧
      (∀ e, derElement 0x30 (memBytes M rp rl.toNat) = .error e → DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  obtain ⟨n', c', s', sp', k', f'⟩ := sv_seq F C s h1 h2 hb hev rsp ha0 ha1 ho2 ho3 hd2 hd3 hrp hrl hin
  obtain ⟨K, Ok, Er, fr⟩ := dnm_facts _ ho2 ho3 hd2 hd3 hs f'
  exact ⟨n', c', s', sp', k', K, Ok, Er, fr⟩

/-- The words `Der::element` leaves when the read succeeds: the content's
address and length, the whole element's address and length, and the tag,
and the reader moved past the element. -/
def DerTlvW (M : Word → BitVec 8) (B : Word) (oc dc : Nat) (rp rl : Word) (t : DerTlv) : Prop :=
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = rp + BitVec.ofNat 32 t.header ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = BitVec.ofNat 32 t.len ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = rp ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 12)) = BitVec.ofNat 32 (t.header + t.len) ∧
  M (B + 0x21A0 + BitVec.ofNat 32 (oc + 16)) = BitVec.ofNat 8 t.tag ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp + BitVec.ofNat 32 (t.header + t.len) ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl - BitVec.ofNat 32 (t.header + t.len)

set_option maxHeartbeats 8000000 in
/-- What `derTlvMem` leaves on the frame. -/
theorem dtm_facts {B : Word} {M : Word → BitVec 8} {oc dc : Nat} {rp rl : Word} (r : Except DerError DerTlv)
    (ho2 : oc + 20 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 20 ≤ dc + 8 ∨ dc + 16 ≤ oc) :
    SvKeepL B M (derTlvMem M (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r)
        [(oc, 17), (dc + 8, 8)] ∧
      (∀ t, r = .ok t → DerTlvW (derTlvMem M (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc)
        rp rl r) B oc dc rp rl t) ∧
      (∀ e, r = .error e → DerErrW (derTlvMem M (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc)
        rp rl r) B oc e) ∧
      (∀ x, SvR B x → derTlvMem M (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r x =
        M x) := by
  have o4 := lit4 (B + 0x21A0) oc (by omega)
  have o8 := lit8 (B + 0x21A0) oc (by omega)
  have o12 := lit12 (B + 0x21A0) oc (by omega)
  have o16 : B + 0x21A0 + BitVec.ofNat 32 oc + 0x10 = B + 0x21A0 + BitVec.ofNat 32 (oc + 16) :=
    frame_lit _ (by simpa using (show oc + 16 < 2 ^ 32 by omega))
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have st : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a + 4 ≤ 0x1690 → e + 1 ≤ 0x1690 → (a + 4 ≤ e ∨ e + 1 ≤ a) →
      memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  have st8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x1690 → e + 1 ≤ 0x1690 → a ≠ e →
      memStore8 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore8_ne (add_ofNat_ne _ (by omega) (by omega) (Ne.symm h))
  have ldst : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a % 4 = 0 → e % 4 = 0 → a + 4 ≤ 0x1690 →
      e + 4 ≤ 0x1690 → memLoad32 (memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v) (B + 0x21A0 + BitVec.ofNat 32 e) =
        if a = e then v else memLoad32 N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 h4 => ld_st_sv h1 h2 (by omega) (by omega)
  have ld8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x1690 → e + 4 ≤ 0x1690 → (a < e ∨ e + 4 ≤ a) →
      memLoad32 (memStore8 N (B + 0x21A0 + BitVec.ofNat 32 a) v) (B + 0x21A0 + BitVec.ofNat 32 e) =
        memLoad32 N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 => memLoad32_store8_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  refine ⟨fun e he hL => ?_, fun t ht => ?_, fun er he => ?_, fun x hx => ?_⟩
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    cases r with
    | error er =>
      simp only [derTlvMem]
      rw [o4, st8 _ (oc + 4) e _ (by omega) he (by omega), st _ oc e _ (by omega) he (by omega)]
    | ok t =>
      simp only [derTlvMem]
      rw [o16, st8 _ (oc + 16) e _ (by omega) he (by omega), o12, st _ (oc + 12) e _ (by omega) he (by omega), o8,
        st _ (oc + 8) e _ (by omega) he (by omega), o4, st _ (oc + 4) e _ (by omega) he (by omega),
        st _ oc e _ (by omega) he (by omega), d12, st _ (dc + 12) e _ (by omega) he (by omega), d8,
        st _ (dc + 8) e _ (by omega) he (by omega)]
  · subst ht
    simp only [DerTlvW, derTlvMem]
    rw [o4, o8, o12, o16, d8, d12, memStore8_same]
    simp (disch := omega) only [ld8, ldst, ite_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp (disch := omega) only [ite_eq_right]) <;> trivial
  · subst he
    simp only [DerErrW, derTlvMem]
    rw [o4, memStore8_same, ld8 _ (oc + 4) oc _ (by omega) (by omega) (by omega), memLoad32_store32_same]
    exact ⟨rfl, rfl⟩
  · have hx' : ∀ c, c + 1 ≤ 0x1690 → Sep (B + 0x21A0 + BitVec.ofNat 32 c) 1 x 1 := fun c hc => svR_hi hx hc
    have s4 : ∀ (N : Word → BitVec 8) (a : Nat) (v : Word), a + 4 ≤ 0x1690 →
        memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v x = N x := fun N a v ha =>
      memStore32_get_sep (svR_hi hx ha)
    cases r with
    | error er =>
      simp only [derTlvMem]
      rw [o4, memStore8_ne (sep1_ne (hx' (oc + 4) (by omega))), s4 _ oc _ (by omega)]
    | ok t =>
      simp only [derTlvMem]
      rw [o16, memStore8_ne (sep1_ne (hx' (oc + 16) (by omega))), o12, s4 _ (oc + 12) _ (by omega), o8,
        s4 _ (oc + 8) _ (by omega), o4, s4 _ (oc + 4) _ (by omega), s4 _ oc _ (by omega), d12,
        s4 _ (dc + 12) _ (by omega), d8, s4 _ (dc + 8) _ (by omega)]

set_option maxHeartbeats 4000000 in
/-- **A call to `Der::element`** with tag `tag`, the result at offset `oc`
of the frame, and the reader at offset `dc`. -/
theorem sv_elemF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc tag : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derElementAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ha2 : reg n a2 = BitVec.ofNat 32 tag) (htag : tag < 256)
    (ho2 : oc + 20 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 20 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ q, tlvClob q = false → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 17), (dc + 8, 8)] ∧
      (∀ t, derElement tag (memBytes M rp rl.toNat) = .ok t → DerTlvW n'.mem B oc dc rp rl t) ∧
      (∀ e, derElement tag (memBytes M rp rl.toNat) = .error e → DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  obtain ⟨n2, c2, pc2, mem2, k2⟩ := derElement_correct n1 (tag := tag) (by decide) (by rw [mem1]; exact C.elem)
    (by rw [mem1]; exact C.tlv) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) htag (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (sv_al F (by omega) ho3) (sv_al F (by omega) hd3)
    (by rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
    (by rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
    (by rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
  rw [mem1, d8, lit12 (B + 0x21A0) dc (by omega), hrp, hrl] at mem2
  obtain ⟨K, Ok, Er, fr⟩ := dtm_facts (rp := rp) (rl := rl) (derElement tag (memBytes M rp rl.toNat)) ho2 ho3 hd2 hd3 hs
  rw [← mem2] at K Ok Er fr
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun q hk hr => by rw [k2 q hk, r1 q hr], K, Ok, Er, fr⟩

end C3.RV32.Sv
