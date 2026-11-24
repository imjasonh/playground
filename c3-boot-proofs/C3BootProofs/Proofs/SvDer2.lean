import C3BootProofs.Proofs.SvDer
import C3BootProofs.Proofs.DerReaders
import C3BootProofs.Proofs.DerPositive

/-!
# `sigstore::verify`: calls to the `Der` readers that return a slice

`Der::bit_string` and `Der::positive_integer` store a slice, or an error,
at the result, and move the reader past the element they read.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- A callee frame `k` bytes below the frame's base. -/
theorem sv_lo (B : Word) (k : Nat) (hk : k ≤ 0x21A0) :
    B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k) = B + BitVec.ofNat 32 (0x21A0 - k) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]; omega

/-- The reader's words after `derAdvance`. -/
def DerAdvW (M : Word → BitVec 8) (B : Word) (dc : Nat) (rp rl : Word) (t : DerTlv) : Prop :=
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp + BitVec.ofNat 32 (t.header + t.len) ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl - BitVec.ofNat 32 (t.header + t.len)

/-- A slice stored at offset `oc`. -/
def SliceW (M : Word → BitVec 8) (B : Word) (oc : Nat) (p l : Word) : Prop :=
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = p ∧ memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = l

set_option maxHeartbeats 8000000 in
/-- What `derSliceMem` after `derAdvance` leaves on the frame, seen outside a
callee frame `kf` bytes below the base. -/
theorem dsm_facts {B : Word} {M M' : Word → BitVec 8} {oc dc kf : Nat} {rp rl : Word}
    (r : Except DerError DerTlv) (s : Except DerError (Word × Word)) (hkf : kf ≤ 0x200) (hkf0 : 0 < kf)
    (ho2 : oc + 8 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hs : oc + 8 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (f : ∀ x, Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf x 1 →
      M' x = derSliceMem (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r) (B + 0x21A0 + BitVec.ofNat 32 oc)
        s x) :
    SvKeepL B M M' [(oc, 8), (dc + 8, 8)] ∧ (∀ t, r = .ok t → DerAdvW M' B dc rp rl t) ∧
      (∀ p l, s = .ok (p, l) → SliceW M' B oc p l) ∧ (∀ e, s = .error e → DerErrW M' B oc e) ∧
      (∀ x, SvR B x → M' x = M x) := by
  have fS : ∀ e, e + 1 ≤ 0x4C0 → Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf (B + 0x21A0 + BitVec.ofNat 32 e) 1 :=
    fun e he => by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  have ld : ∀ e, e + 4 ≤ 0x4C0 → memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) =
      memLoad32 (derSliceMem (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r)
        (B + 0x21A0 + BitVec.ofNat 32 oc) s) (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun e he => memLoad32_congr fun j hj => f _ (by rw [add_ofNat_assoc]; exact fS _ (by omega))
  have o4 := lit4 (B + 0x21A0) oc (by omega)
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have st : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a + 4 ≤ 0x4C0 → e + 1 ≤ 0x4C0 → (a + 4 ≤ e ∨ e + 1 ≤ a) →
      memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  have st8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x4C0 → e + 1 ≤ 0x4C0 → a ≠ e →
      memStore8 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore8_ne (add_ofNat_ne _ (by omega) (by omega) (Ne.symm h))
  have ldst : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a % 4 = 0 → e % 4 = 0 → a + 4 ≤ 0x4C0 →
      e + 4 ≤ 0x4C0 → memLoad32 (memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v) (B + 0x21A0 + BitVec.ofNat 32 e) =
        if a = e then v else memLoad32 N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 h4 => ld_st_sv h1 h2 (by omega) (by omega)
  have ld8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x4C0 → e + 4 ≤ 0x4C0 → (a < e ∨ e + 4 ≤ a) →
      memLoad32 (memStore8 N (B + 0x21A0 + BitVec.ofNat 32 a) v) (B + 0x21A0 + BitVec.ofNat 32 e) =
        memLoad32 N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 => memLoad32_store8_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  have adv : ∀ e, e + 1 ≤ 0x4C0 → (e + 1 ≤ dc + 8 ∨ dc + 16 ≤ e) →
      derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r (B + 0x21A0 + BitVec.ofNat 32 e) =
        M (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h => by
    cases r with
    | error _ => rfl
    | ok t => simp only [derAdvance]; rw [d12, st _ (dc + 12) e _ (by omega) he (by omega), d8,
        st _ (dc + 8) e _ (by omega) he (by omega)]
  have sl : ∀ (N : Word → BitVec 8) e, e + 1 ≤ 0x4C0 → (e + 1 ≤ oc ∨ oc + 8 ≤ e) →
      derSliceMem N (B + 0x21A0 + BitVec.ofNat 32 oc) s (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) := fun N e he h => by
    cases s with
    | error _ => simp only [derSliceMem]; rw [o4, st8 _ (oc + 4) e _ (by omega) he (by omega),
        st _ oc e _ (by omega) he (by omega)]
    | ok pl => obtain ⟨p, l⟩ := pl; simp only [derSliceMem]; rw [o4, st _ (oc + 4) e _ (by omega) he (by omega),
        st _ oc e _ (by omega) he (by omega)]
  refine ⟨fun e he hL => ?_, fun t ht => ?_, fun p l hpl => ?_, fun er he => ?_, fun x hx => ?_⟩
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    rw [f _ (fS e he), sl _ e he (by omega), adv e he (by omega)]
  · subst ht
    have ldA : ∀ e, e + 4 ≤ 0x4C0 → (e + 4 ≤ oc ∨ oc + 8 ≤ e) →
        memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) =
          memLoad32 (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl (.ok t)) (B + 0x21A0 + BitVec.ofNat 32 e) :=
      fun e he h => (ld e he).trans (memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact sl _ _ (by omega) (by omega))
    refine ⟨?_, ?_⟩
    · rw [ldA _ (by omega) (by omega)]
      simp only [derAdvance]; rw [d12, d8, ldst _ _ _ _ (by omega) (by omega) (by omega) (by omega),
        ite_eq_right (by omega), memLoad32_store32_same]
    · rw [ldA _ (by omega) (by omega)]
      simp only [derAdvance]; rw [d12, memLoad32_store32_same]
  · subst hpl
    refine ⟨?_, ?_⟩
    · rw [ld _ (by omega)]; simp only [derSliceMem]
      rw [o4, ldst _ _ _ _ (by omega) (by omega) (by omega) (by omega), ite_eq_right (by omega),
        memLoad32_store32_same]
    · rw [ld _ (by omega)]; simp only [derSliceMem]; rw [o4, memLoad32_store32_same]
  · subst he
    refine ⟨?_, ?_⟩
    · rw [ld _ (by omega)]; simp only [derSliceMem]
      rw [o4, ld8 _ (oc + 4) oc _ (by omega) (by omega) (by omega), memLoad32_store32_same]
    · rw [f _ (fS (oc + 4) (by omega))]; simp only [derSliceMem]; rw [o4, memStore8_same]
  · have hxF : Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf x 1 := by
      have := svR_lo (k := kf) hx (by omega) (by omega)
      rwa [sv_lo B kf (by omega)] at this
    rw [f x hxF]
    have s4 : ∀ (N : Word → BitVec 8) (a : Nat) (v : Word), a + 4 ≤ 0x4C0 →
        memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v x = N x := fun N a v ha =>
      memStore32_get_sep (svR_hi hx ha)
    have a1 : derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r x = M x := by
      cases r with
      | error _ => rfl
      | ok t => simp only [derAdvance]; rw [d12, s4 _ (dc + 12) _ (by omega), d8, s4 _ (dc + 8) _ (by omega)]
    cases s with
    | error _ => simp only [derSliceMem]; rw [o4, memStore8_ne (sep1_ne (svR_hi (l := 1) hx (by omega))),
        s4 _ oc _ (by omega), a1]
    | ok pl => obtain ⟨p, l⟩ := pl; simp only [derSliceMem]; rw [o4, s4 _ (oc + 4) _ (by omega),
        s4 _ oc _ (by omega), a1]

theorem sv_sp30 (B : Word) : B + 0x21A0 + 0xFFFFFFD0 = B + BitVec.ofNat 32 0x2170 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::bit_string`** with the result at offset `oc` and the
reader at offset `dc`. -/
theorem sv_bitsF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derBitStringAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 8 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hs : oc + 8 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 8), (dc + 8, 8)] ∧
      (∀ t, derElement 3 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (∀ p l, derBitsOf (memBytes M rp rl.toNat) rp (derElement 3 (memBytes M rp rl.toNat)) = .ok (p, l) →
        SliceW n'.mem B oc p l) ∧
      (∀ e, derBitsOf (memBytes M rp rl.toNat) rp (derElement 3 (memBytes M rp rl.toNat)) = .error e →
        DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : DerCallEnv M derBitStringCode (BitVec.ofNat 32 derBitStringAddress) 0xFFFFD3A0 (B + 0x21A0)
      (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc) 8 := by
    refine ⟨by decide, by decide, C.derBitString, C.elem, C.tlv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) ho3
    · exact sv_al F (by omega) hd3
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [sv_sp20, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp20, d8, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp20, d8, d12, hrp, hrl]; exact hin.sepLo (by decide)
    · rw [d8, hrp]; exact hin.pos
    · rw [d8, d12, hrp, hrl]; exact hin.fit
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derBitString_correct n1 (by rw [mem1]; exact env)
    (by rw [mem1, d8, d12, hrp, hrl, ← sv_base']; exact (hin.sepLo (by omega)).symm)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp20] at f2
  obtain ⟨K, A, Ok, Er, fr⟩ := dsm_facts (kf := 0x20) _ _ (by decide) (by decide) ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    K, A, Ok, Er, fr⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::positive_integer`** with the result at offset `oc`
and the reader at offset `dc`. -/
theorem sv_posF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derPositiveIntegerAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 8 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hs : oc + 8 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 8), (dc + 8, 8)] ∧
      (∀ t, derElement 2 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (∀ p l, derPosIntOf (memBytes M rp rl.toNat) rp (derElement 2 (memBytes M rp rl.toNat)) = .ok (p, l) →
        SliceW n'.mem B oc p l) ∧
      (∀ e, derPosIntOf (memBytes M rp rl.toNat) rp (derElement 2 (memBytes M rp rl.toNat)) = .error e →
        DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : PIEnv M (BitVec.ofNat 32 derPositiveIntegerAddress) (B + 0x21A0)
      (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc) := by
    refine ⟨by decide, C.derPositiveInteger, C.derInteger, C.elem, C.tlv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) ho3
    · exact sv_al F (by omega) hd3
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [sv_sp30, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp30, d8, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp30, d8, d12, hrp, hrl]; exact hin.sepLo (by decide)
    · rw [d8, d12, hrp, hrl, ← sv_base']; exact (hin.sepLo (by omega)).symm
    · rw [d8, d12, hrp, hrl, ← sv_base']; exact (hin.sepLo (by omega)).symm
    · rw [d8, ← sv_base', ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [d8, hrp]; exact hin.pos
    · rw [d8, d12, hrp, hrl]; exact hin.fit
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derPositiveInteger_correct n1 (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp30] at f2
  obtain ⟨K, A, Ok, Er, fr⟩ := dsm_facts (kf := 0x30) _ _ (by decide) (by decide) ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    K, A, Ok, Er, fr⟩

end C3.RV32.Sv
