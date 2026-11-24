import C3BootProofs.Proofs.SvCkpt
import C3BootProofs.Proofs.CheckSigs

/-!
# `sigstore::verify`: the checkpoint's Ed25519 signature

`verify_checkpoint` checks the log's signature over the checkpoint's body
with `ed25519_verify`, on a copy of the signature in `sigstore::verify`'s
frame. `sigMem` is memory as `ed25519_verify` reads it: the bundle and the
image's constants from `M0`, and the 64 signature bytes from the frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The read-only region `ed25519_verify`'s constants live in lies outside
the frame's region. -/
def SvRoSep (B : Word) : Prop := Sep (B + 0xFFFFFE60) 0x39D0 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize)

/-- `M0` with the 64 bytes `L` at `sig`. -/
def sigMem (M0 : Word → BitVec 8) (sig : Word) (L : Bytes) : Word → BitVec 8 :=
  fun x => if (x - sig).toNat < 64 then BitVec.ofNat 8 (L.getD (x - sig).toNat 0) else M0 x

theorem sigMem_out {M0 : Word → BitVec 8} {sig x : Word} {L : Bytes} (h : Sep sig 64 x 1) :
    sigMem M0 sig L x = M0 x := by
  unfold sigMem
  rw [ite_eq_right]
  intro hl
  refine absurd ?_ (h _ hl 0 (by decide))
  rw [ofNat_toNat_self, add_ofNat_zero, BitVec.add_comm, BitVec.sub_add_cancel]

theorem sigMem_in {M0 : Word → BitVec 8} {sig : Word} {L : Bytes} {i : Nat} (hi : i < 64) :
    sigMem M0 sig L (sig + BitVec.ofNat 32 i) = BitVec.ofNat 8 (L.getD i 0) := by
  unfold sigMem
  have e : (sig + BitVec.ofNat 32 i - sig).toNat = i := by
    rw [BitVec.add_comm sig, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  rw [e, ite_eq_left (by omega)]

set_option maxHeartbeats 1000000 in
/-- **A call to `ed25519_verify`** on the key at `pk`, the `len` bytes at
`msg`, and the signature `L` at offset `oc` of the frame. -/
theorem sv_edF {n : Machine} {B : Word} {off : Nat} {imm o pk msg : Word} {oc len : Nat} {L : Bytes}
    {M0 : Word → BitVec 8} (F : Fr B 0x3830) (C : SvCode n.mem) (EE : EvEnv M0) (RS : SvRoSep B)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (fR : ∀ x, SvR B x → n.mem x = M0 x) (s : St n.mem SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = EV) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = pk) (ha1 : reg n a1 = msg) (ha2 : reg n a2 = BitVec.ofNat 32 len)
    (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 oc) (ho : oc + 64 ≤ 0x1690)
    (hsig : ∀ j, j < 64 → n.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + j)) = BitVec.ofNat 8 (L.getD j 0))
    (pk_in : SvIn B pk 32) (msg_in : SvIn B msg len) (hlen : len < 2 ^ 31) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 oc) L) pk (B + 0x21A0 + BitVec.ofNat 32 oc)
        msg len then 1 else 0) ∧
      SvKeepL B n.mem n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have eF : B + 0x21A0 = B + BitVec.ofNat 32 0xB00 + BitVec.ofNat 32 0x16A0 := by
    rw [add_ofNat_assoc]; rfl
  have eG : evG (B + BitVec.ofNat 32 0xB00) = B + BitVec.ofNat 32 0xF0 := by
    show B + BitVec.ofNat 32 0xB00 + 0xFFFFF5F0 = _; rw [BitVec.add_assoc]; rfl
  have hG : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0xF0) 0x20B0 x 1 := fun x hx => by
    have := hx.sub (c := 0x1A0 + 0xF0) (l := 0x20B0) (by decide)
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0xF0) = B + BitVec.ofNat 32 0xF0 by
      rw [BitVec.add_assoc]; rfl] at this
  have hsS : Sep (B + 0x21A0 + BitVec.ofNat 32 oc) 64 (B + BitVec.ofNat 32 0xF0) 0x20B0 := by
    rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  have hro : ∀ i, i < (img% roWindowSize) → SvR B (BitVec.ofNat 32 ((img% roWindowAddress) + i)) := fun i hi => by
    have := RS.symm.sub (c := i) (l := 1) (by omega)
    rw [ofNat_add_ofNat] at this; exact this.symm
  have hroS : Sep (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) (B + BitVec.ofNat 32 0xF0) 0x20B0 := by
    have := RS.symm.subR (c := 0x1A0 + 0xF0) (l := 0x20B0) (by decide)
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0xF0) = B + BitVec.ofNat 32 0xF0 by
      rw [BitVec.add_assoc]; rfl] at this
  -- `n1.mem` agrees with `sigMem` on what `ed25519_verify` reads.
  have aR : ∀ x, SvR B x → Sep (B + 0x21A0 + BitVec.ofNat 32 oc) 64 x 1 →
      n1.mem x = sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 oc) L x := fun x hx hs => by
    rw [mem1, fR x hx, sigMem_out hs]
  have rA : RoAgree n1.mem (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 oc) L) := fun i hi =>
    aR _ (hro i hi) (svR_hi (hro i hi) ho)
  have hE : evSpec n1.mem pk (B + 0x21A0 + BitVec.ofNat 32 oc) msg len =
      evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 oc) L) pk (B + 0x21A0 + BitVec.ofNat 32 oc) msg len :=
    evSpec_congr rA (fun i hi => aR _ (pk_in.r hi) (svR_hi (pk_in.r hi) ho))
      (fun i hi => by rw [mem1, sigMem_in hi, add_ofNat_assoc]; exact hsig i hi)
      (fun i hi => aR _ (msg_in.r hi) (svR_hi (msg_in.r hi) ho))
  have EE1 : EvEnv n1.mem := by
    rw [mem1]
    refine EE.congr (fun x hx => fR x (sep_of_le (by
      have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
      rw [hb]; omega) (by have := x.isLt; omega))) (fun i hi => fR _ (hro i hi))
  have ctx : EvCtx n1.mem (B + BitVec.ofNat 32 0xB00) pk (B + 0x21A0 + BitVec.ofNat 32 oc) msg len := by
    refine ⟨EE1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlen, ?_⟩
    · rw [F.at 0xB00 (by decide)]; omega
    · rw [F.at 0xB00 (by decide)]; omega
    · rw [F.at 0xB00 (by decide)]; omega
    · rw [eG]; exact hroS
    · rw [eG]; exact (pk_in.sepLo (c := 0xF0) (n := 0x20B0) (by decide))
    · rw [eG]; exact hsS
    · rw [eG]; exact (msg_in.sepLo (c := 0xF0) (n := 0x20B0) (by decide))
    · have := pk_in.lo; omega
    · rw [sv_at F _ (by omega)]; omega
    · have := msg_in.lo; omega
    · have := msg_in.lo; omega
    · rw [mem1, s5Hv_ro (fun i hi => (fR _ (hro i hi)))]; exact hiv
  obtain ⟨n2, c2, pc2, sp2, rs2, gp2, tp2, a02, mem2⟩ := ed25519Verify_correct n1 ctx pc1
    (by rw [r1 sp (by decide), rsp, eF]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3])
    (by rw [regs1]; simp +decide only [upd, ↓reduceIte]; exact even_clear _ hev)
  rw [eG] at mem2
  rw [hE] at a02
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2, regs1]; simp +decide only [upd, ↓reduceIte], rfl, fun _ => rfl⟩,
    by rw [sp2, r1 sp (by decide), rsp], fun q hq => ?_, a02,
    fun e he _ => by rw [mem2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)), mem1],
    fun x hx => by rw [mem2 x (hG x hx), mem1]⟩
  have hq' : q = 3 ∨ q = 4 ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨
      q = 25 ∨ q = 26 ∨ q = 27 := by revert hq; revert q; decide
  rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [gp2, r1 _ (by decide)]
  · rw [tp2, r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x68) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x64) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x60) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x5C) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x58) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x54) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x50) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x4C) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x48) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x44) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x40) (by decide), r1 _ (by decide)]
  · rw [rs2 _ (BitVec.ofNat 32 0x3C) (by decide), r1 _ (by decide)]

set_option maxHeartbeats 8000000 in
/-- **A call to `<[u8]>::equal_same_length`** on `nl` bytes at `p` and at `q`. -/
theorem sv_eslF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p q : Word} {nl : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 equalSameLengthAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = p) (ha1 : reg n a1 = q) (ha2 : reg n a2 = BitVec.ofNat 32 nl)
    (hp : SvRo B p nl) (hq : SvRo B q nl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg n r) ∧
      reg n' a0 = (if memBytes M p nl = memBytes M q nl then 1 else 0) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have eM : BitVec.ofNat 32 equalSameLengthAddress + 0xC912 = BitVec.ofNat 32 memcmpAddress := by decide
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := equalSameLength_correct n1 (base := BitVec.ofNat 32 equalSameLengthAddress)
    (by decide) (by rw [mem1]; exact C.equalSameLength) (by rw [mem1, eM]; exact C.memcmp) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by have := hp.fit; omega) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [sp1, hS]; omega)
    (by rw [sp1, sv_sp4]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, sv_sp4, eM]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, sv_sp4]; exact hp.sep F (c := 0x219C) (n := 4) (by decide))
    (by rw [sp1, sv_sp4]; exact hq.sep F (c := 0x219C) (n := 4) (by decide))
  rw [sp1, sv_sp4] at f2
  rw [mem1] at a02
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [k2 sp (by decide) (by decide) (by decide)
    (by decide) (by decide), sp1], fun r hr => ?_, a02, fun e he _ => ?_, fun x hx => ?_⟩
  · have hr' : r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ ra := by revert hr; revert r; decide
    obtain ⟨q10, q11, q12, q13, q14, q1⟩ := hr'
    rw [k2 r q10 q11 q12 q13 q14, r1 r q1]
  · rw [f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)), mem1]
  · rw [f2 x (svR_sp4 hx), mem1]

end C3.RV32.Sv
