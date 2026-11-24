import C3BootProofs.Proofs.SvSha
import C3BootProofs.Proofs.Ed25519VerifyP4b

/-!
# `sigstore::verify`: the hasher `verify_leaf` builds

SHA-384's stream form, the compiled hasher in the frame, and calls of
`sha512FinBlock` and `memset` from `sigstore::verify`'s frame.
-/

namespace C3

open Sha512

/-- FIPS 180-4's SHA-384 digest: SHA-512's computation from SHA-384's initial
hash value over the full blocks, then the padded buffer's one or two blocks,
truncated to 48 bytes. -/
theorem sha384_stream (msg : Bytes) :
    sha384 msg = (((fullBlocks5 msg ++ blocks ((padTail5 msg).length / 128) (padTail5 msg)).foldl compress
      h0384).flatMap wordBytes).take 48 := by
  have hpad : pad msg = msg.take (128 * (msg.length / 128)) ++ padTail5 msg := by
    unfold pad padTail5 tailBytes5 padZeros5
    simp only [← List.append_assoc, List.take_append_drop]
  have hA := take_full5_length msg
  have hT := padTail5_length msg
  have hP : (pad msg).length = 128 * (msg.length / 128 + (padTail5 msg).length / 128) := by
    rw [hpad, List.length_append, hA, hT]; unfold padZeros5; omega
  unfold sha384
  simp only
  rw [blocks5_fuel _ _ _ hP (by omega), hpad, blocks5_append _ _ _ _ hA, ← blocks5_take]
  rfl

end C3

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The 0xD0 bytes at offset `c` of the frame hold the compiled SHA-384
hasher after it has absorbed `msg`: the bytes after `msg`'s full blocks in the
buffer, their count in the buffer's last byte, the hash of the full blocks
from SHA-384's initial value, and the 128-bit count of blocks. -/
structure SvHasher (B : Word) (M : Word → BitVec 8) (c : Nat) (msg : Bytes) : Prop where
  hlen : msg.length < 2 ^ 32
  pos : M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x7F)) = BitVec.ofNat 8 (msg.length % 128)
  buf : memBytes M (B + 0x21A0 + BitVec.ofNat 32 c) (msg.length % 128) = tailBytes5 msg
  hash : (s5Hv M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x80))).toList = (fullBlocks5 msg).foldl Sha512.compress Sha512.h0384
  lo : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (c + 0xC0)) = BitVec.ofNat 32 (msg.length / 128)
  hi : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (c + 0xC4)) = 0
  hi2 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (c + 0xC8)) = 0
  hi3 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (c + 0xCC)) = 0

/-- The hasher's 0xD0 bytes, copied to offset `d`. -/
theorem SvHasher.copy {B : Word} {M M' : Word → BitVec 8} {c d : Nat} {msg : Bytes} (H : SvHasher B M c msg)
    (h : ∀ j, j < 0xD0 → M' (B + 0x21A0 + BitVec.ofNat 32 (d + j)) = M (B + 0x21A0 + BitVec.ofNat 32 (c + j))) :
    SvHasher B M' d msg := by
  have w : ∀ o, o + 4 ≤ 0xD0 → memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 (d + o)) =
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (c + o)) := fun o ho => vk_ld2 fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc, Nat.add_assoc]; exact h _ (by omega)
  have hp : msg.length % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨H.hlen, by rw [h _ (by decide)]; exact H.pos, ?_, ?_, by rw [w _ (by decide)]; exact H.lo,
    by rw [w _ (by decide)]; exact H.hi, by rw [w _ (by decide)]; exact H.hi2, by rw [w _ (by decide)]; exact H.hi3⟩
  · rw [← H.buf]
    unfold memBytes
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [add_ofNat_assoc, add_ofNat_assoc, h _ (by omega)]
  · rw [← H.hash]
    exact congrArg _ (s5Hv_copy fun i hi => by
      rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc, Nat.add_assoc]; exact h _ (by omega))

theorem SvHasher.same {B : Word} {M M' : Word → BitVec 8} {c : Nat} {msg : Bytes} (H : SvHasher B M c msg)
    (h : ∀ j, j < 0xD0 → M' (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = M (B + 0x21A0 + BitVec.ofNat 32 (c + j))) :
    SvHasher B M' c msg := H.copy h

theorem SvKeepL.of {B : Word} {M M' : Word → BitVec 8} {c w : Nat} (K : SvKeep B M M' c w) : SvKeepL B M M' [(c, w)] :=
  fun e he hL => K e he (hL _ (List.mem_singleton_self _))

theorem SvKeepL.same {B : Word} {M M' : Word → BitVec 8} (h : M' = M) : SvKeepL B M M' [] :=
  fun _ _ _ => by rw [h]

/-- Fewer, wider ranges. -/
theorem SvKeepL.wider {B : Word} {M M' : Word → BitVec 8} {L L' : List (Nat × Nat)} (K : SvKeepL B M M' L)
    (h : ∀ p ∈ L, ∃ q ∈ L', q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) : SvKeepL B M M' L' := fun e he hL =>
  K e he fun p hp => by
    obtain ⟨q, hq, h1, h2⟩ := h p hp
    have := hL q hq; omega

/-- SHA-384's initial hash value sits apart from the stack. -/
theorem sv_ivIn {B : Word} (F : Fr B 0x3830) : SvIn B IV5 64 :=
  ⟨by
    have := F.dsep.subR (c := (img% sha384IVAddress - dataWindowAddress)) (l := 78) (by decide)
    rw [show (img% dataWindowAddress : Word) + BitVec.ofNat 32 (img% sha384IVAddress - dataWindowAddress) = IV5 from rfl] at this
    exact this.symm, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- The 64 bytes of SHA-384's initial hash value. -/
theorem iv_hv {M : Word → BitVec 8} {stp : Word}
    (h : ∀ j, j < 64 → M (stp + BitVec.ofNat 32 j) = byteAt sha384IVData j) :
    (s5Hv M stp).toList = Sha512.h0384 := by
  rw [s5Hv_copy (M := fun x => byteAt sha384IVData x.toNat) (b := 0) fun i hi => by
    rw [h i hi]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl]; congr 1; omega]
  decide

/-- The full blocks of `len` bytes at `p`. -/
theorem fullBlocks5_mem (M : Word → BitVec 8) (p : Word) (len : Nat) :
    fullBlocks5 (memBytes M p len) = blockList128 M p (len / 128) := by
  unfold fullBlocks5
  rw [memBytes_length, blocks5_take, memBytes_take' (by omega), S5U.blocks128_memBytes M _ _ _ (Nat.le_refl _)]

/-- The bytes after the full blocks of `len` bytes at `p`. -/
theorem tailBytes5_mem (M : Word → BitVec 8) (p : Word) (len : Nat) :
    tailBytes5 (memBytes M p len) = memBytes M (p + BitVec.ofNat 32 (128 * (len / 128))) (len % 128) := by
  unfold tailBytes5
  rw [memBytes_length]
  rw [show memBytes M p len = memBytes M p (128 * (len / 128) + len % 128) by rw [Nat.div_add_mod],
    memBytes_split, List.drop_left' (memBytes_length _ _ _)]

theorem sv_sp420 (B : Word) : B + 0x21A0 + 0xFFFFFBE0 = B + BitVec.ofNat 32 0x1D80 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 16000000 in
/-- **A call to `sha512FinBlock`** with the state at offset `a` and the block
at offset `b` of the frame. -/
theorem sv_fbF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {a b : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (SC : SvShaCode M) (KS : SvKSep B) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha512FinBlockAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 a)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 b) (ha : a + 64 ≤ 0x1690) (ha4 : a % 4 = 0)
    (hbb : b + 128 ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(a, 64)] ∧
      (s5Hv n'.mem (B + 0x21A0 + BitVec.ofNat 32 a)).toList =
        Sha512.compress (s5Hv M (B + 0x21A0 + BitVec.ofNat 32 a)).toList (memBytes M (B + 0x21A0 + BitVec.ofNat 32 b) 128) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have eA : B + 0x21A0 + BitVec.ofNat 32 a = B + BitVec.ofNat 32 (0x21A0 + a) := (sv_base' B a).symm
  have eB : B + 0x21A0 + BitVec.ofNat 32 b = B + BitVec.ofNat 32 (0x21A0 + b) := (sv_base' B b).symm
  have kS : ∀ (c l : Nat), c + l ≤ 0x3830 → Sep (B + BitVec.ofNat 32 c) l SK5 640 := fun c l hc => by
    have := KS.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + c) = B + BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]; omega] at this
  have env : FB5Env M (B + 0x21A0 + BitVec.ofNat 32 a) (B + 0x21A0 + BitVec.ofNat 32 b) (B + 0x21A0) := by
    refine ⟨SC.fin, SC.cmp, SC.idx, C.K.stub, C.K.body, C.K.mset, SC.k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) ha4
    · rw [sv_at F _ (by omega)]; omega
    · rw [sv_at F _ (by omega)]; omega
    · rw [eA, sv_sp420]; exact sepS B (by omega) (by omega) (by omega)
    · rw [eB, sv_sp420]; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp420]; exact (kS 0x1D80 0x420 (by decide)).symm
    · rw [eA]; exact kS _ _ (by omega)
  obtain ⟨n2, c2, pc2, sp2, k2, hv, f2⟩ := sha512FinBlock_correct n1 (by rw [mem1]; exact env) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
  rw [mem1] at hv f2
  rw [sv_sp420] at f2
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x1D80) 0x420 x 1 := fun x hx => by
    have := svR_lo (k := 0x420) hx (by decide) (by decide)
    rwa [sv_lo B 0x420 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    fun e he hL => ?_, hv, fun x hx => f2 x (hfS x hx) (svR_hi hx ha)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A `memset` of `N` bytes** at offset `c` of the frame. -/
theorem sv_msF {n : Machine} {B : Word} {off : Nat} {imm o v : Word} {c N : Nat}
    (F : Fr B 0x3830) (C : SvCode n.mem) (s : St n.mem SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = MSET) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 c) (ha1 : reg n a1 = v) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      n'.mem = fillBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 c) (v.extractLsb' 0 8) N ∧
      ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg n' r = reg n r := by
  have hFh := F.hi
  exact c_memset s C.self C.K h1 h2 hb hev ha0 ha1 ha2 (by rw [sv_at F _ (by omega)]; omega)
    (by rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))

end C3.RV32.Sv
