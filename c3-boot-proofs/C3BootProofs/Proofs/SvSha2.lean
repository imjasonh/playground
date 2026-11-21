import C3BootProofs.Proofs.SvGt
import C3BootProofs.Proofs.Sha2OneShot
import C3BootProofs.Proofs.Sha2Parts

/-!
# `sigstore::verify`: SHA-256 and digest comparisons

Calls to `c3_crypto::sha::sha256`, `sha256_parts` with two slices, and
`<[u8; 32] as PartialEq>::ne`, from the frame of `sigstore::verify`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

abbrev SK2 : Word := BitVec.ofNat 32 shaKAddress
abbrev IV2 : Word := BitVec.ofNat 32 shaIVAddress

/-- SHA-256's code and constants. -/
structure SvSha2Code (M : Word → BitVec 8) : Prop where
  fn : CodeIn M (BitVec.ofNat 32 sha256FnAddress) sha256FnCode
  parts : CodeIn M (BitVec.ofNat 32 sha256PartsAddress) sha256PartsCode
  upd : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  ublk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  fin : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  z : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  fblk : CodeIn M (BitVec.ofNat 32 shaFinBlockAddress) shaFinBlockCode
  ms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  mcs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cmp : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  idx : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  k : CodeIn M SK2 shaKData
  iv : CodeIn M IV2 shaIVData

/-- SHA-256's round constants lie outside the frame's region. -/
def SvK2Sep (B : Word) : Prop := Sep (B + 0xFFFFFE60) 0x39D0 SK2 256

theorem SvSha2Code.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (KS : SvK2Sep B) (D : SvSha2Code M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvSha2Code M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.fn (by decide) (by decide) hx, codeHi D.parts (by decide) (by decide) hx,
    codeHi D.upd (by decide) (by decide) hx, codeHi D.ublk (by decide) (by decide) hx,
    codeHi D.fin (by decide) (by decide) hx, codeHi D.z (by decide) (by decide) hx,
    codeHi D.fblk (by decide) (by decide) hx, codeHi D.ms (by decide) (by decide) hx,
    codeHi D.mcs (by decide) (by decide) hx, codeHi D.mcb (by decide) (by decide) hx,
    codeHi D.cmp (by decide) (by decide) hx, codeHi D.idx (by decide) (by decide) hx,
    fun i hi' => by
      rw [fR _ (KS.symm.sub (c := i) (l := 1) (by have : shaKData.length = 256 := rfl; omega)).symm]
      exact D.k i hi',
    fun i hi => by
      rw [fR _ (dataR (q := IV2) (ql := shaIVData.length) F (by decide) (by decide) i hi)]; exact D.iv i hi⟩

theorem sv_sp270 (B : Word) : B + 0x21A0 + 0xFFFFFD90 = B + BitVec.ofNat 32 0x1F30 := by
  rw [BitVec.add_assoc]; rfl

theorem SvRo.lo {B q : Word} {ql : Nat} (h : SvRo B q ql) : q.toNat + ql ≤ 0x40000000 := by
  rcases h with h | ⟨_, h2⟩
  · have := h.lo; omega
  · omega

theorem svR_sp270 {B x : Word} (hx : SvR B x) : Sep (B + BitVec.ofNat 32 0x1F30) 0x270 x 1 := by
  have := svR_lo (k := 0x270) hx (by decide) (by decide)
  rwa [sv_lo B 0x270 (by decide)] at this

theorem svR_sp4 {B x : Word} (hx : SvR B x) : Sep (B + BitVec.ofNat 32 0x219C) 4 x 1 := by
  have := svR_lo (k := 4) hx (by decide) (by decide)
  rwa [sv_lo B 4 (by decide)] at this

set_option maxHeartbeats 8000000 in
/-- **A call to `c3_crypto::sha::sha256`** on the `nl` bytes at `p`, with
the digest at offset `oc`. -/
theorem sv_sha256F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p : Word} {oc nl : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (SC : SvSha2Code M) (KS : SvK2Sep B) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha256FnAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = p)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ho2 : oc + 32 ≤ 0x1690) (hin : SvRo B p nl) (hn : nl < 2 ^ 31) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 32)] ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) 32 = sha256 (memBytes M p nl) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hpl := hin.lo
  have env : Sha256Env n1.mem (B + 0x21A0 + BitVec.ofNat 32 oc) p (B + 0x21A0) nl := by
    rw [mem1]
    refine ⟨SC.fn, SC.iv, SC.upd, SC.ublk, SC.fin, SC.z, SC.fblk, SC.ms, SC.mcs, SC.mcb, SC.cmp, SC.idx, SC.k,
      by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega, by omega,
      by rw [sv_at F _ (by omega)]; omega, ?_, ?_, ?_, ?_⟩
    · rw [sv_sp270]; exact (hin.sep F (c := 0x1F30) (n := 0x270) (by decide)).symm
    · rw [sv_sp270, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp270]
      have h := KS.sub (c := 0x1A0 + 0x1F30) (l := 0x270) (by decide)
      rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x1F30) = B + BitVec.ofNat 32 0x1F30 by
        rw [BitVec.add_assoc]; rfl] at h
      exact h.symm
    · rw [sv_sp270]; exact (F.bufData (c := 0x1F30) (n := 0x270) (by decide) (by decide) (by decide)).symm
  obtain ⟨n2, c2, pc2, sp2, k2, dg2, f2⟩ := sha256Fn_correct n1 env pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp]) hn
  rw [mem1, sv_sp270] at f2
  rw [mem1] at dg2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
    fun e he hL => ?_, dg2, fun x hx => f2 x (svR_sp270 hx) (svR_hi hx ho2)⟩
  · have hq' : q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
        q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) ∧
        q ≠ ra := by revert hq; revert q; decide
    obtain ⟨q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, q1⟩ := hq'
    rw [k2 q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r1 q q1]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

theorem dec_toNat {n : Word} (hn : n ≠ 0) : (n + BitVec.ofNat 32 0xFFFFFFFF).toNat = n.toNat - 1 := by
  have h0 : n.toNat ≠ 0 := fun e => hn (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := n.isLt
  omega

/-- A signed-attributes slice without its first byte. -/
theorem sa_drop1 {B p n : Word} (h : SvIn B p n.toNat) (hn : n ≠ 0) :
    SvRo B (p + BitVec.ofNat 32 0x1) (n + BitVec.ofNat 32 0xFFFFFFFF).toNat := by
  rw [dec_toNat hn]
  exact .inl (h.drop (k := 1) (by
    have h0 : n.toNat ≠ 0 := fun e => hn (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    omega))

theorem sa_drop1_lt {B p n : Word} (h : SvIn B p n.toNat) (hn : n ≠ 0) :
    (n + BitVec.ofNat 32 0xFFFFFFFF).toNat < 2 ^ 31 := by
  rw [dec_toNat hn]; have := h.lo; omega

theorem partsBytes_two (M : Word → BitVec 8) (P : Word) :
    partsBytes M P 2 = memBytes M (partPtr M P 0) (partLen M P 0) ++ memBytes M (partPtr M P 1) (partLen M P 1) := by
  simp only [partsBytes, List.nil_append]

set_option maxHeartbeats 8000000 in
/-- **A call to `c3_crypto::sha::sha256_parts`** on two slices whose
descriptors are at offset `pc`, with the digest at offset `oc`. -/
theorem sv_sha256P2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p0 p1 : Word}
    {oc pc l0 l1 : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (SC : SvSha2Code M) (KS : SvK2Sep B) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha256PartsAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 pc) (ha2 : reg n a2 = BitVec.ofNat 32 2)
    (ho2 : oc + 32 ≤ 0x1690) (hp2 : pc + 16 ≤ 0x1690) (hp3 : pc % 4 = 0)
    (hp0 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 pc) = p0)
    (hl0 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 4)) = BitVec.ofNat 32 l0)
    (hp1 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 8)) = p1)
    (hl1 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 12)) = BitVec.ofNat 32 l1)
    (r0 : SvRo B p0 l0) (r1' : SvRo B p1 l1) (hl0' : l0 < 2 ^ 31) (hl1' : l1 < 2 ^ 31) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 32)] ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) 32 = sha256 (memBytes M p0 l0 ++ memBytes M p1 l1) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hq0 := r0.lo
  have hq1 := r1'.lo
  have e0 : partPtr M (B + 0x21A0 + BitVec.ofNat 32 pc) 0 = p0 := by
    unfold partPtr; rw [show 8 * 0 = 0 from rfl, add_ofNat_zero]; exact hp0
  have e1 : partPtr M (B + 0x21A0 + BitVec.ofNat 32 pc) 1 = p1 := by
    unfold partPtr; rw [add_ofNat_assoc, show pc + 8 * 1 = pc + 8 by omega]; exact hp1
  have f0 : partLen M (B + 0x21A0 + BitVec.ofNat 32 pc) 0 = l0 := by
    unfold partLen; rw [add_ofNat_assoc, show pc + (8 * 0 + 4) = pc + 4 by omega, hl0, BitVec.toNat_ofNat]
    omega
  have f1 : partLen M (B + 0x21A0 + BitVec.ofNat 32 pc) 1 = l1 := by
    unfold partLen; rw [add_ofNat_assoc, show pc + (8 * 1 + 4) = pc + 12 by omega, hl1, BitVec.toNat_ofNat]
    omega
  have hpb : partsBytes M (B + 0x21A0 + BitVec.ofNat 32 pc) 2 = memBytes M p0 l0 ++ memBytes M p1 l1 := by
    rw [partsBytes_two, e0, e1, f0, f1]
  have env : PartsEnv n1.mem (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 pc) (B + 0x21A0) 2 := by
    rw [mem1]
    refine ⟨SC.parts, SC.iv, SC.upd, SC.ublk, SC.fin, SC.z, SC.fblk, SC.ms, SC.mcs, SC.mcb, SC.cmp, SC.idx, SC.k,
      by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega,
      by rw [sv_at F _ (by omega)]; omega, sv_al F (by omega) hp3, by rw [sv_at F _ (by omega)]; omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sv_sp270, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [hpb, List.length_append, memBytes_length, memBytes_length]; omega
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [e0, f0, sv_sp270]; exact ⟨hl0', hq0, (r0.sep F (c := 0x1F30) (n := 0x270) (by decide)).symm⟩
      · rw [e1, f1, sv_sp270]; exact ⟨hl1', hq1, (r1'.sep F (c := 0x1F30) (n := 0x270) (by decide)).symm⟩
    · rw [sv_sp270, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp270]
      have h := KS.sub (c := 0x1A0 + 0x1F30) (l := 0x270) (by decide)
      rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x1F30) = B + BitVec.ofNat 32 0x1F30 by
        rw [BitVec.add_assoc]; rfl] at h
      exact h.symm
    · rw [sv_sp270]; exact (F.bufData (c := 0x1F30) (n := 0x270) (by decide) (by decide) (by decide)).symm
  obtain ⟨n2, c2, pc2, sp2, k2, dg2, f2⟩ := sha256Parts_correct n1 env pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
  rw [mem1, sv_sp270] at f2
  rw [mem1, hpb] at dg2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
    fun e he hL => ?_, dg2, fun x hx => f2 x (svR_sp270 hx) (svR_hi hx ho2)⟩
  · have hq' : q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
        q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) ∧
        q ≠ ra := by revert hq; revert q; decide
    obtain ⟨q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, q1⟩ := hq'
    rw [k2 q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r1 q q1]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to `<[u8; 32] as PartialEq>::ne`** on the 32 bytes at offset
`oc` and the 32 bytes at `q`. -/
theorem sv_a32neF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o q : Word} {oc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 arr32NeAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = q)
    (ho2 : oc + 32 ≤ 0x1690) (hq : SvRo B q 32) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg n r) ∧
      reg n' a0 = (if memBytes M (B + 0x21A0 + BitVec.ofNat 32 oc) 32 = memBytes M q 32 then 0 else 1) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have eM : BitVec.ofNat 32 arr32NeAddress + 0xB97A = BitVec.ofNat 32 memcmpAddress := by decide
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := arr32Ne_correct n1 (base := BitVec.ofNat 32 arr32NeAddress) (by decide)
    (by rw [mem1]; exact C.arr32Ne) (by rw [mem1, eM]; exact C.memcmp) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [sp1, hS]; omega)
    (by rw [sp1, sv_sp4]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, sv_sp4, eM]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, sv_sp4, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
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
