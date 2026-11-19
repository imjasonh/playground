import C3BootProofs.Proofs.SvDpv
import C3BootProofs.Proofs.DerScalar32

/-!
# `sigstore::verify`: the timestamp's signature

Wrappers for the calls that read the timestamp's ECDSA P-256 signature.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- What `derAdvance` leaves on the frame, seen outside a callee frame `kf`
bytes below the base and outside `ow` bytes at offset `oc`. -/
theorem dad_facts_out {B : Word} {M M' : Word → BitVec 8} {dc kf oc ow : Nat} {rp rl : Word}
    (r : Except DerError DerTlv) (hkf : kf ≤ 0x200) (hkf0 : 0 < kf) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (ho : oc + ow ≤ 0x1690) (hs : oc + ow ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (f : ∀ x, Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf x 1 → Sep (B + 0x21A0 + BitVec.ofNat 32 oc) ow x 1 →
      M' x = derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r x) :
    SvKeepL B M M' [(oc, ow), (dc + 8, 8)] ∧ (∀ t, r = .ok t → DerAdvW M' B dc rp rl t) ∧
      (∀ x, SvR B x → M' x = M x) := by
  have fS : ∀ e, e + 1 ≤ 0x1690 → Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf (B + 0x21A0 + BitVec.ofNat 32 e) 1 :=
    fun e he => by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  have fO : ∀ e, e + 1 ≤ 0x1690 → (e < oc ∨ oc + ow ≤ e) →
      Sep (B + 0x21A0 + BitVec.ofNat 32 oc) ow (B + 0x21A0 + BitVec.ofNat 32 e) 1 :=
    fun e he h => sepS (B + 0x21A0) (by omega) (by omega) (by omega)
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have st : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a + 4 ≤ 0x1690 → e + 1 ≤ 0x1690 → (a + 4 ≤ e ∨ e + 1 ≤ a) →
      memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  refine ⟨fun e he hL => ?_, fun t ht => ?_, fun x hx => ?_⟩
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only at h1 h2
    rw [f _ (fS e he) (fO e he h1)]
    cases r with
    | error _ => rfl
    | ok t => simp only [derAdvance]; rw [d12, st _ (dc + 12) e _ (by omega) he (by omega), d8,
        st _ (dc + 8) e _ (by omega) he (by omega)]
  · subst ht
    have ld : ∀ e, e + 4 ≤ 0x1690 → (e + 4 ≤ oc ∨ oc + ow ≤ e) → memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) =
        memLoad32 (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl (.ok t)) (B + 0x21A0 + BitVec.ofNat 32 e) :=
      fun e he h => memLoad32_congr fun j hj => f _ (by rw [add_ofNat_assoc]; exact fS _ (by omega))
        (by rw [add_ofNat_assoc]; exact fO _ (by omega) (by omega))
    refine ⟨?_, ?_⟩
    · rw [ld _ (by omega) (by omega)]; simp only [derAdvance]
      rw [d12, d8, ld_st_sv (by omega) (by omega) (by omega) (by omega), ite_eq_right (by omega),
        memLoad32_store32_same]
    · rw [ld _ (by omega) (by omega)]; simp only [derAdvance]; rw [d12, memLoad32_store32_same]
  · have hxF : Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf x 1 := by
      have := svR_lo (k := kf) hx (by omega) hkf0
      rwa [sv_lo B kf (by omega)] at this
    rw [f x hxF (svR_hi hx ho)]
    cases r with
    | error _ => rfl
    | ok t => simp only [derAdvance]; rw [d12, memStore32_get_sep (svR_hi hx (by omega)), d8,
        memStore32_get_sep (svR_hi hx (by omega))]

theorem sv_sp90 (B : Word) : B + 0x21A0 + 0xFFFFFF70 = B + BitVec.ofNat 32 0x2110 := by
  rw [BitVec.add_assoc]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A call to `der::scalar::<32>`** with the 33-byte result at offset `oc`
and the reader at offset `dc`. -/
theorem sv_ds32F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derScalar32Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 33 ≤ 0x1690) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0) (hs : oc + 33 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 33), (dc + 8, 8)] ∧
      (∀ t, derElement 2 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (match derScalarOf 32 (memBytes M rp rl.toNat) rp (derElement 2 (memBytes M rp rl.toNat)) with
        | .ok bs => n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧
            ∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1 + j)) = BitVec.ofNat 8 (bs.getD j 0)
        | .error b => n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 1 ∧
            n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1)) = b) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have eO : B + 0x21A0 + BitVec.ofNat 32 oc = B + BitVec.ofNat 32 (0x21A0 + oc) := (sv_base' B oc).symm
  have eD : B + 0x21A0 + BitVec.ofNat 32 dc + 8 = B + BitVec.ofNat 32 (0x21A0 + (dc + 8)) := by
    rw [d8]; exact (sv_base' B (dc + 8)).symm
  have env : DTEnv M (BitVec.ofNat 32 derScalar32Address) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 oc)
      (B + 0x21A0 + BitVec.ofNat 32 dc) := by
    refine ⟨by decide, C.derScalar32, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact C.derPositiveInteger
    · exact C.derInteger
    · exact C.elem
    · exact C.tlv
    · exact C.zipSkipNext
    · exact C.K.mset
    · exact C.K.stub
    · exact C.K.body
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) hd3
    · rw [sv_at F _ (by omega)]; omega
    iterate 9 (· rw [sv_sp90]; exact F.sepHi (by decide) (by decide) (by decide))
    iterate 2 (· rw [eO]; exact F.sepHi (by omega) (by decide) (by decide))
    · rw [eO, sv_sp90]; exact sepS B (by omega) (by omega) (by omega)
    iterate 8 (· rw [eD]; exact F.sepHi (by omega) (by decide) (by decide))
    · rw [eD, sv_sp90]; exact sepS B (by omega) (by omega) (by omega)
    · rw [d8, d12, hrp, hrl, sv_sp90]; exact hin.sepLo (by decide)
    · rw [d8, d12, hrp, hrl, ← sv_base']; exact (hin.sepLo (by omega)).symm
    · rw [d8, hrp]; exact hin.pos
    · rw [d8, d12, hrp, hrl]; exact hin.fit
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derScalar32_correct n1 (by rw [mem1]; exact env) pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp90] at f2
  generalize hR : derScalarOf 32 (memBytes M rp rl.toNat) rp (derElement 2 (memBytes M rp rl.toNat)) = R at f2 ⊢
  have fG : ∀ x, Sep (B + BitVec.ofNat 32 (0x21A0 - 0x90)) 0x90 x 1 → Sep (B + 0x21A0 + BitVec.ofNat 32 oc) 33 x 1 →
      n2.mem x = derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl (derElement 2 (memBytes M rp rl.toNat)) x := by
    cases R with
    | ok bs => exact fun x hx ho => f2.2.2 x hx ho
    | error b => exact fun x hx ho => f2.2.2 x hx (by
        have := ho.sub (c := 0) (l := 2) (by decide); rwa [add_ofNat_zero] at this)
  obtain ⟨K, A, fr⟩ := dad_facts_out (kf := 0x90) (oc := oc) (ow := 33) _ (by decide) (by decide) hd2 hd3 ho2 hs fG
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], K, A, ?_, fr⟩
  cases R with
  | ok bs =>
    exact ⟨f2.1, fun j hj => by
      rw [show B + 0x21A0 + BitVec.ofNat 32 (oc + 1 + j) = B + 0x21A0 + BitVec.ofNat 32 oc + BitVec.ofNat 32 (1 + j) by
        rw [add_ofNat_assoc, Nat.add_assoc]]
      exact f2.2.1 j hj⟩
  | error b =>
    exact ⟨f2.1, by rw [← add_ofNat_assoc]; exact f2.2.1⟩

end C3.RV32.Sv
