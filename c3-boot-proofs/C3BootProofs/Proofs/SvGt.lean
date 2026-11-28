import C3BootProofs.Proofs.SvTsa

/-!
# `sigstore::verify`: a call to `time::generalized_time`

The TSTInfo's `genTime` goes through `time::generalized_time` directly, with
the result at a frame offset.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

theorem shr_shr (x : Word) (a b : Nat) : x >>> a >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

/-- A positive integer's content bytes, which are never empty. -/
theorem SvIn.posIntIn {B rp rl ip il : Word} {M : Word → BitVec 8} {t : DerTlv} (h : SvIn B rp rl.toNat)
    (ht : derElement 2 (memBytes M rp rl.toNat) = .ok t)
    (hp : derPosIntOf (memBytes M rp rl.toNat) rp (.ok t) = .ok (ip, il)) :
    SvIn B ip il.toNat ∧ 0 < il.toNat := by
  have hb := derElement_bound ht
  rw [memBytes_length] at hb
  have hf := h.fit
  unfold derPosIntOf at hp
  cases hi : derIntOf (memBytes M rp rl.toNat) rp (.ok t) with
  | error e => rw [hi] at hp; cases hp
  | ok pl =>
    rw [hi] at hp
    simp only at hp
    split at hp
    · cases hp
    · cases hp
      simp only [derIntOf] at hi
      split at hi
      · cases hi
      · split at hi
        · cases hi
        · rename_i h0 _
          cases hi
          have hlt : t.len < 2 ^ 32 := by omega
          refine ⟨h.contentW ht, ?_⟩
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact Nat.pos_of_ne_zero h0

set_option maxHeartbeats 8000000 in
/-- **A call to `time::generalized_time`** on the `nl` bytes at `p`, with the
`Result<u64, Error>` at offset `oc`. -/
theorem sv_gtF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p : Word} {oc nl : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 generalizedTimeAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = p)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ho2 : oc + 16 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hin : SvIn B p nl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 16)] ∧
      (∀ t, generalizedTime (memBytes M p nl) = some t → t < 2 ^ 64 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 12)) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
      (generalizedTime (memBytes M p nl) = none → n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1)) = 0x19) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hpl := hin.lo
  obtain ⟨n2, c2, pc2, sp2, k2, Ok, Er, f2⟩ := generalizedTime_correct n1 (n := nl)
    (by rw [mem1]; exact C.generalizedTime) (by rw [mem1]; exact C.dateTime) (by rw [mem1]; exact C.timeDigits2)
    (by rw [mem1]; exact C.timeDigits4) (by rw [mem1]; exact C.allAsciiDigit)
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; omega)
    (by rw [sv_at F _ (by omega)]; omega) (sv_al F (by omega) ho3) (by omega) (by omega) hin.pos
    (by rw [sv_sp60, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [sv_sp60]; exact (hin.sep14.symm.sub (c := 0x1590 + 0x2140) (l := 0x60) (by decide) |> fun h => by
      rw [show B + 0xFFFFEA70 + BitVec.ofNat 32 (0x1590 + 0x2140) = B + BitVec.ofNat 32 0x2140 by
        rw [BitVec.add_assoc]; rfl] at h; exact h.symm))
  rw [mem1, sv_sp60] at f2
  rw [mem1] at Ok Er
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x2140) 0x60 x 1 := fun x hx => by
    have := svR_lo (k := 0x60) hx (by decide) (by decide)
    rwa [sv_lo B 0x60 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    fun e he hL => ?_, fun t ht => ?_, fun ht => ?_, fun x hx => f2 x (hfS x hx) (svR_hi hx ho2)⟩
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  · obtain ⟨h64, b0, w8, w12⟩ := Ok t ht
    refine ⟨h64, b0, ?_, ?_⟩
    · rw [← add_ofNat_assoc]; exact w8
    · rw [← add_ofNat_assoc]; exact w12
  · obtain ⟨b0, b1⟩ := Er ht
    exact ⟨b0, by rw [← lb1 (B + 0x21A0) oc (by omega)]; exact b1⟩

end C3.RV32.Sv
