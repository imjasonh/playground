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

end C3.RV32.Sv
