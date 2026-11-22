import C3BootProofs.Proofs.SvCs
import C3BootProofs.Proofs.Base64Encode
import C3BootProofs.Proofs.RootFromInclusion
import C3BootProofs.Proofs.Sha2Finish

/-!
# `sigstore::verify`: the log entry

After the checkpoint, `sigstore::verify` checks the entry's index against
the checkpoint's size, rebuilds the entry's leaf hash, and checks the
inclusion proof.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- **The error exit at 0x3122**: the entry's index isn't below the
checkpoint's size, `Err(0x1B)`. -/
theorem sv_fail_3122 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0x3122 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have hz := s.zero
  have sOC := hO.code
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x3128) [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFB01] E.self (by decide)
    ⟨trivial, trivial, trivial⟩
  have a01 : reg n1 a0 = 0x1B01 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, aluEval]
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; rw [updz (by rfl) hq, updz hz hq]
  have M1 : n1.mem = n.mem := u1.mem
  have s1 : St n.mem SV n1 0x3128 (reg n1) := ⟨u1.pc, M1, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := s1.jump E.self sv_at_3128 (off' := 0x2A88) (by decide) (by rw [s1.pc]; decide)
  have s2 : St n.mem SV n2 0x2A88 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have e0 : reg n2 (18 : Fin 32) + 0 = out := by rw [u2.regs, r1 _ (by decide), hout]; exact BitVec.add_zero _
  obtain ⟨n3, d3, u3⟩ := s2.sh E.self sv_at_2a88 (off' := 0x2A8C) (by decide) (by rw [e0]; exact hO.al)
  rw [e0, u2.regs, a01] at u3
  have M3 : n3.mem = memStore8 (memStore8 n.mem out 1) (out + 1) 0x1B := by rw [u3.mem]; rfl
  have C3 : CodeIn n3.mem SV sigstoreVerifyCode := by
    rw [M3]; exact (E.self.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)).store8
      (sOC.sub (c := 1) (l := 1) (by decide))
  have s3 : St n3.mem SV n3 0x2A8C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  obtain ⟨n4, d4, u4⟩ := s3.jump C3 sv_at_2a8c (off' := 0x970) (by decide) (by rw [s3.pc]; decide)
  have s4 : St n3.mem SV n4 0x970 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  refine sv_ret_err (n := n4) (M := n3.mem) F C3 s4
    (t.trans (c1.trans ((Steps.single d2).trans ((Steps.single d3).trans (.single d4)))))
    (by rw [M3]; exact saves_out2 hO V) hret
    (by rw [u4.regs, u3.regs, u2.regs, r1 sp (by decide), rsp]) (by rw [u4.regs, u3.regs, u2.regs, r1 3 (by decide), r3])
    (by rw [u4.regs, u3.regs, u2.regs, r1 4 (by decide), r4]) ?_ ?_
  · rw [M3, memStore8_ne (out_ne1 out), memStore8_same]
  · intro x hx h0 h1; rw [M3, memStore8_ne h1, memStore8_ne h0, fR x hx]

/-- Bytes `sigstore::verify` reads outside the stack: the bundle's, or the
image's read-only constants. -/
def SvRo2 (B q : Word) (ql : Nat) : Prop :=
  SvIn B q ql ∨ (0x3FCC4000 ≤ q.toNat ∧ q.toNat + ql ≤ 0x3FCC5400)

theorem roSep {B b : Word} {len c n : Nat} (RS : SvRoSep B) (h : c + n ≤ 0x3830) (hb : 0x3FCC4000 ≤ b.toNat)
    (hb2 : b.toNat + len ≤ 0x3FCC5400) : Sep (B + BitVec.ofNat 32 c) n b len := by
  have h1 := RS.sub (c := 0x1A0 + c) (l := n) (by omega)
  have h2 := h1.subR (c := b.toNat - 0x3FCC4000) (l := len) (by omega)
  rw [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
    omega] at h2
  rwa [show BitVec.ofNat 32 0x3FCC4000 + BitVec.ofNat 32 (b.toNat - 0x3FCC4000) = b by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := b.isLt; omega] at h2

theorem SvRo2.sepLo {B q : Word} {ql : Nat} (RS : SvRoSep B) (h : SvRo2 B q ql) {c n : Nat} (hc : c + n ≤ 0x3830) :
    Sep q ql (B + BitVec.ofNat 32 c) n := by
  rcases h with h | ⟨h1, h2⟩
  · exact h.sepLo hc
  · exact (roSep RS hc h1 h2).symm

theorem SvRo2.lo {B q : Word} {ql : Nat} (h : SvRo2 B q ql) : q.toNat + ql ≤ 0x40000000 := by
  rcases h with h | ⟨_, h2⟩
  · have := h.lo; omega
  · omega

theorem SvRo2.r {B q : Word} {ql i : Nat} (RS : SvRoSep B) (h : SvRo2 B q ql) (hi : i < ql) :
    SvR B (q + BitVec.ofNat 32 i) := by
  rcases h with h | ⟨h1, h2⟩
  · exact h.r hi
  · have := RS.subR (c := q.toNat - 0x3FCC4000 + i) (l := 1) (by omega)
    rwa [show BitVec.ofNat 32 0x3FCC4000 + BitVec.ofNat 32 (q.toNat - 0x3FCC4000 + i) = q + BitVec.ofNat 32 i by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have := q.isLt; omega] at this

theorem sv_mbRo2 {B q : Word} {ql : Nat} {M M0 : Word → BitVec 8} (RS : SvRoSep B)
    (fR : ∀ x, SvR B x → M x = M0 x) (h : SvRo2 B q ql) : memBytes M q ql = memBytes M0 q ql :=
  memBytes_congr fun _ hi => fR _ (h.r RS hi)

/-- The log-entry code `sigstore::verify` calls, beyond `SvCode`. -/
structure SvRkCode (M : Word → BitVec 8) : Prop where
  fin : CodeIn M (BitVec.ofNat 32 shaFinishAddress) shaFinishCode
  bee : CodeIn M BEE base64EncodeToCode
  bal : CodeIn M BAL b64AlphabetData
  rfi : CodeIn M (BitVec.ofNat 32 rootFromInclusionAddress) rootFromInclusionCode
  node : CodeIn M (BitVec.ofNat 32 merkleNodeHashAddress) merkleNodeHashCode
  pre : CodeIn M (BitVec.ofNat 32 merklePrefixAddress) merklePrefixData

theorem SvRkCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvRkCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvRkCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.fin (by decide) (by decide) hx, codeHi D.bee (by decide) (by decide) hx,
    fun i hi => by rw [fR _ (dataR (q := BAL) (ql := b64AlphabetData.length) F (by decide) (by decide) i hi)]; exact D.bal i hi,
    codeHi D.rfi (by decide) (by decide) hx, codeHi D.node (by decide) (by decide) hx,
    fun i hi => by
      rw [fR _ (dataR (q := BitVec.ofNat 32 merklePrefixAddress) (ql := merklePrefixData.length) F (by decide)
        (by decide) i hi)]; exact D.pre i hi⟩

theorem wordsAt_copy {M M' : Word → BitVec 8} {a b : Word}
    (h : ∀ j, j < 32 → M (a + BitVec.ofNat 32 j) = M' (b + BitVec.ofNat 32 j)) : wordsAt M a 8 = wordsAt M' b 8 := by
  unfold wordsAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have e : ∀ (c : Word) (k : Nat), k < 4 → c + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k = c + BitVec.ofNat 32 (4 * i + k) :=
    fun c k _ => add_ofNat_assoc _ _ _
  unfold memLoad32
  rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, e a 3 (by decide), e a 2 (by decide), e a 1 (by decide),
    e b 3 (by decide), e b 2 (by decide), e b 1 (by decide), h _ (by omega), h _ (by omega), h _ (by omega),
    h _ (by omega)]

/-- A hasher with nothing hashed: a zero position, SHA-256's initial words,
and a zero count. -/
theorem hasher_init {M : Word → BitVec 8} {S : Word} (hpos : M (S + 0x3F) = 0)
    (hiv : wordsAt M (S + 0x40) 8 = Sha256.h0) (hlo : memLoad32 M (S + 0x60) = 0) (hhi : memLoad32 M (S + 0x64) = 0) :
    HasherAt M S [] :=
  { hlen := by decide
    pos := by rw [hpos]; rfl
    buf := by simp [memBytes, tailBytes]
    hash := by rw [hiv]; rfl
    lo := by rw [hlo]; rfl
    hi := hhi }

theorem sv_mcRo2 {B : Word} {m : Machine} {off : Nat} {imm o p : Word} {c N : Nat} (F : Fr B 0x3830)
    (RS : SvRoSep B) (E : SvCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 c)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 N) (hc : c + N ≤ 0x1690) (hin : SvRo2 B p N) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = m.mem (p + BitVec.ofNat 32 j) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hb16 : (B + 0x21A0 + 0xFFFFFFF0).toNat = (B + 0x21A0).toNat - 16 := FS.below 16 (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x21A0 + BitVec.ofNat 32 c) (src := p) (S := B + 0x21A0)
    (N := N) s E.self E.K h1 h2 hb he8 hsp ha0 ha1 ha2
    ⟨E.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega),
      by rw [sv_sp10]; exact hin.sepLo RS (by decide),
      by rw [← sv_base']; exact (hin.sepLo RS (by omega)).symm, fA, fW,
      by rw [FS.at _ (by omega)]; omega, by have := hin.lo; omega⟩
  have lo16 : ∀ x, SvR B x → Sep (B + 0x21A0 + 0xFFFFFFF0) 16 x 1 := fun x hx => svR_lo (k := 16) hx (by decide) (by decide)
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (lo16 x hx), copyBytes_sep (svR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x21A0) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [← add_ofNat_assoc, fr2 _ (by rw [add_ofNat_assoc]; exact FS.lowB hb16 (by decide) (by omega)),
      C3.RV32.Dq.cp_at hj (by omega)]

theorem sv_spX (B : Word) (k : Nat) (hk : k ≤ 0x21A0) :
    B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k) = B + BitVec.ofNat 32 (0x21A0 - k) := sv_lo B k hk

theorem kSep {B : Word} (KS : SvK2Sep B) {c n : Nat} (hc : c + n ≤ 0x3830) : Sep SK2 256 (B + BitVec.ofNat 32 c) n := by
  have h := KS.sub (c := 0x1A0 + c) (l := n) (by omega)
  rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + c) = B + BitVec.ofNat 32 c by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
    omega] at h
  exact h.symm

theorem svR_spX {B x : Word} {k : Nat} (hx : SvR B x) (hk : k ≤ 0x2340) (hk0 : 0 < k) (hk' : k ≤ 0x21A0) :
    Sep (B + BitVec.ofNat 32 (0x21A0 - k)) k x 1 := by
  have := svR_lo (k := k) hx hk hk0
  rwa [sv_lo B k hk'] at this

set_option maxHeartbeats 8000000 in
/-- **A call to `Sha256::update`** on the hasher at offset `hc` with the
`nl` bytes at `D`. -/
theorem sv_updF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o D : Word} {hc nl : Nat}
    {msg : Bytes} (F : Fr B 0x3830) (C : SvCode M) (SC : SvSha2Code M) (KS : SvK2Sep B) (RS : SvRoSep B)
    (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 shaUpdateAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 hc) (ha1 : reg n a1 = D)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (hh : hc + 0x68 ≤ 0x1690) (hh4 : hc % 4 = 0) (hin : SvRo2 B D nl)
    (H : HasherAt M (B + 0x21A0 + BitVec.ofNat 32 hc) msg) (hn : nl < 2 ^ 31) (hlen : msg.length + nl < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(hc, 0x68)] ∧
      HasherAt n'.mem (B + 0x21A0 + BitVec.ofNat 32 hc) (msg ++ memBytes M D nl) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hpl := hin.lo
  have e1 : B + 0x21A0 + 0xFFFFFF00 = B + BitVec.ofNat 32 0x20A0 := sv_spX B 0x100 (by decide)
  have env : UpdEnv n1.mem (B + 0x21A0 + BitVec.ofNat 32 hc) D (B + 0x21A0) nl := by
    rw [mem1]
    refine ⟨SC.upd, SC.ublk, SC.cmp, SC.idx, SC.k, SC.mcs, SC.mcb, sv_al F (by omega) hh4,
      by rw [sv_at F _ (by omega)]; omega, by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega, by omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [← sv_base']; exact hin.sepLo RS (by omega)
    · rw [e1]; exact hin.sepLo RS (by decide)
    · rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [← sv_base']; exact kSep KS (by omega)
    · rw [e1]; exact kSep KS (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, H2, f2⟩ := shaUpdate_correct n1 env pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [mem1]; exact H) hn hlen
  rw [mem1, e1] at f2
  rw [mem1] at H2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
    fun e he hL => ?_, H2, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hh)⟩
  · have hq' : q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
        q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) ∧
        q ≠ ra ∧ q ≠ sp := by revert hq; revert q; decide
    obtain ⟨q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, q1, q2⟩ := hq'
    rw [k2 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2, r1 q q1]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to `base64::encode_to::<Sha256>`** of the `nl` bytes at `D`
into the hasher at offset `hc`. -/
theorem sv_b64eF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o D : Word} {hc nl : Nat}
    {msg : Bytes} (F : Fr B 0x3830) (C : SvCode M) (SC : SvSha2Code M) (RK : SvRkCode M) (KS : SvK2Sep B)
    (RS : SvRoSep B) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BEE)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = D) (ha1 : reg n a1 = BitVec.ofNat 32 nl)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 hc) (hh : hc + 0x68 ≤ 0x1690) (hh4 : hc % 4 = 0)
    (hin : SvRo2 B D nl) (H : HasherAt M (B + 0x21A0 + BitVec.ofNat 32 hc) msg)
    (hlen : msg.length + 4 * (nl / 3) + 4 < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(hc, 0x68)] ∧
      HasherAt n'.mem (B + 0x21A0 + BitVec.ofNat 32 hc) (msg ++ base64Encode (memBytes M D nl)) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hpl := hin.lo
  have e1 : B + 0x21A0 + 0xFFFFFED0 = B + BitVec.ofNat 32 0x2070 := sv_spX B 0x130 (by decide)
  have env : BeeEnv n1.mem (B + 0x21A0 + BitVec.ofNat 32 hc) D (B + 0x21A0) nl := by
    rw [mem1]
    refine ⟨RK.bee, RK.bal, SC.upd, SC.ublk, SC.cmp, SC.idx, SC.k, SC.mcs, SC.mcb, sv_al F (by omega) hh4,
      by rw [sv_at F _ (by omega)]; omega, by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← sv_base']; exact hin.sepLo RS (by omega)
    · rw [e1]; exact hin.sepLo RS (by decide)
    · rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [← sv_base']; exact kSep KS (by omega)
    · rw [e1]; exact kSep KS (by decide)
    · rw [← sv_base']; exact (F.bufData (by omega) (by decide) (by decide)).symm
    · rw [e1]; exact (F.bufData (by decide) (by decide) (by decide)).symm
  obtain ⟨n2, c2, pc2, sp2, k2, H2, f2⟩ := base64EncodeTo_correct n1 env pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [mem1]; exact H) hlen
  rw [mem1, e1] at f2
  rw [mem1] at H2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
    fun e he hL => ?_, H2, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hh)⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to `Sha256::finish`** of the hasher at offset `hc` into the 32
bytes at offset `oc`. -/
theorem sv_finF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {hc oc : Nat}
    {msg : Bytes} (F : Fr B 0x3830) (C : SvCode M) (SC : SvSha2Code M) (RK : SvRkCode M) (KS : SvK2Sep B)
    (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 shaFinishAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 hc) (hh : hc + 0x68 ≤ 0x1690) (ho : oc + 32 ≤ 0x1690)
    (H : HasherAt M (B + 0x21A0 + BitVec.ofNat 32 hc) msg) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 32)] ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) 32 = sha256 msg ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have e1 : B + 0x21A0 + 0xFFFFFE00 = B + BitVec.ofNat 32 0x1FA0 := sv_spX B 0x200 (by decide)
  have env : FinishEnv n1.mem (B + 0x21A0 + BitVec.ofNat 32 hc) (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0) := by
    rw [mem1]
    refine ⟨RK.fin, SC.fin, SC.z, SC.fblk, SC.ms, SC.mcs, SC.mcb, SC.cmp, SC.idx, SC.k,
      by rw [sv_at F _ (by omega)]; omega, by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega,
      by rw [sv_at F _ (by omega)]; omega, ?_, ?_, ?_⟩
    · rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [e1]; exact kSep KS (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, D2, f2⟩ := shaFinish_correct n1 env pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [mem1]; exact H)
  rw [mem1, e1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
    fun e he hL => ?_, D2, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx ho)⟩
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
/-- **A call to `merkle::root_from_inclusion`** with the leaf hash at offset
`lc`, the `np` proof bytes at `Pp`, and the result at offset `oc`. -/
theorem sv_rfiF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o Pp : Word} {oc lc np : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (SC : SvSha2Code M) (RK : SvRkCode M) (KS : SvK2Sep B) (RS : SvRoSep B)
    (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 rootFromInclusionAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha5 : reg n a5 = B + 0x21A0 + BitVec.ofNat 32 lc) (ha6 : reg n a6 = Pp) (ha7 : reg n a7 = BitVec.ofNat 32 np)
    (ho : oc + 33 ≤ 0x1690) (hl : lc + 32 ≤ 0x1690) (hin : SvRo2 B Pp np) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 33)] ∧
      (match rootFromInclusion (pair64 (reg n a1) (reg n a2)) (pair64 (reg n a3) (reg n a4))
          (memBytes M (B + 0x21A0 + BitVec.ofNat 32 lc) 32) (memBytes M Pp np) with
        | some root => n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧
            memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1)) 32 = root
        | none => n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 1 ∧
            n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1)) = 0x1B) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hpl := hin.lo
  have e1 : B + 0x21A0 + 0xFFFFFD10 = B + BitVec.ofNat 32 0x1EB0 := sv_spX B 0x2F0 (by decide)
  have env : RootEnv n1.mem (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 lc) Pp (B + 0x21A0) np := by
    rw [mem1]
    refine ⟨RK.rfi, RK.node, RK.pre, SC.parts, SC.iv, SC.upd, SC.ublk, SC.fin, SC.z, SC.fblk, SC.ms, SC.mcs, SC.mcb,
      SC.cmp, SC.idx, SC.k, by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega,
      by rw [sv_at F _ (by omega)]; omega, by rw [sv_at F _ (by omega)]; omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [e1]; exact hin.sepLo RS (by decide)
    · rw [e1]; exact (F.bufData (by decide) (by decide) (by decide)).symm
    · rw [e1]; exact kSep KS (by decide)
    · rw [e1]; exact (F.bufData (by decide) (by decide) (by decide)).symm
  obtain ⟨n2, c2, pc2, sp2, k2, R2, f2⟩ := rootFromInclusion_correct n1 env pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a5 (by decide), ha5]) (by rw [r1 a6 (by decide), ha6])
    (by rw [r1 a7 (by decide), ha7])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
  rw [mem1, e1] at f2
  rw [mem1, r1 a1 (by decide), r1 a2 (by decide), r1 a3 (by decide), r1 a4 (by decide)] at R2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
    fun e he hL => ?_, ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx ho)⟩
  · have hq' : q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
        q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) ∧
        q ≠ ra := by revert hq; revert q; decide
    obtain ⟨q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, q1⟩ := hq'
    rw [k2 q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r1 q q1]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  · revert R2
    cases rootFromInclusion _ _ _ _ with
    | some root => intro R2; exact ⟨R2.1, by rw [← add_ofNat_assoc]; exact R2.2⟩
    | none => intro R2; exact ⟨R2.1, by rw [← lb1 (B + 0x21A0) oc (by omega)]; exact R2.2⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `<[u8; 32] as PartialEq>::eq`** on the 32 bytes at offsets
`oc` and `oc2`. -/
theorem sv_a32eqF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {oc oc2 : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 arr32EqAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 oc2) (ho : oc + 32 ≤ 0x1690) (ho2 : oc2 + 32 ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg n r) ∧
      reg n' a0 = (if memBytes M (B + 0x21A0 + BitVec.ofNat 32 oc) 32 =
        memBytes M (B + 0x21A0 + BitVec.ofNat 32 oc2) 32 then 1 else 0) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have eM : BitVec.ofNat 32 arr32EqAddress + 0xC0F0 = BitVec.ofNat 32 memcmpAddress := by decide
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := arr32Eq_correct n1 (base := BitVec.ofNat 32 arr32EqAddress) (by decide)
    (by rw [mem1]; exact C.arr32Eq) (by rw [mem1, eM]; exact C.memcmp) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [sp1, hS]; omega)
    (by rw [sp1, sv_sp4]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, sv_sp4, eM]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, sv_sp4, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [sp1, sv_sp4, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
  rw [sp1, sv_sp4] at f2
  rw [mem1] at a02
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [k2 sp (by decide) (by decide) (by decide)
    (by decide) (by decide), sp1], fun r hr => ?_, a02, fun e he _ => ?_, fun x hx => ?_⟩
  · have hr' : r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ ra := by revert hr; revert r; decide
    obtain ⟨q10, q11, q12, q13, q14, q1⟩ := hr'
    rw [k2 r q10 q11 q12 q13 q14, r1 r q1]
  · rw [f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)), mem1]
  · rw [f2 x (svR_sp4 hx), mem1]

theorem b64_len_le : ∀ xs : Bytes, (base64Encode xs).length ≤ 4 * (xs.length / 3) + 4
  | [] => by simp [base64Encode]
  | [_] => by simp [base64Encode]
  | [_, _] => by simp [base64Encode]
  | _ :: _ :: _ :: rest => by
    have := b64_len_le rest
    simp only [base64Encode, List.length_append, List.length_cons, List.length_nil]
    omega

/-- A hasher with nothing hashed at offset 0x420 of the frame: SHA-256's
initial words copied to 0x460, a zero position at 0x45F, and a zero count. -/
theorem hasher_init_f {M M0 : Word → BitVec 8} {B : Word}
    (hpos : M (B + 0x21A0 + BitVec.ofNat 32 0x45F) = (BitVec.ofNat 32 0x0).extractLsb' 0 8)
    (hiv : ∀ j, j < 32 → M (B + 0x21A0 + BitVec.ofNat 32 (0x460 + j)) =
      M0 (BitVec.ofNat 32 0x3FCC42A8 + BitVec.ofNat 32 j))
    (cIV : CodeIn M0 (BitVec.ofNat 32 shaIVAddress) shaIVData)
    (hlo : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 0x480) = BitVec.ofNat 32 0x0)
    (hhi : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 0x484) = BitVec.ofNat 32 0x0) :
    HasherAt M (B + 0x21A0 + BitVec.ofNat 32 0x420) [] := by
  apply hasher_init
  · rw [show (0x3F : Word) = BitVec.ofNat 32 0x3F from rfl, add_ofNat_assoc, hpos]; rfl
  · rw [show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc, ← iv_words cIV]
    apply wordsAt_copy
    intro j hj
    rw [add_ofNat_assoc]; exact hiv j hj
  · rw [show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl, add_ofNat_assoc, hlo]; rfl
  · rw [show (0x64 : Word) = BitVec.ofNat 32 0x64 from rfl, add_ofNat_assoc, hhi]; rfl

/-- The first 32 bytes of `L`, each cut to a byte. -/
def b32 (L : Bytes) : Bytes := (List.range 32).map fun j => (BitVec.ofNat 8 (L.getD j 0)).toNat

/-- 32 bytes of the frame that hold the first 32 bytes of `L`. -/
theorem join32 {M : Word → BitVec 8} {B : Word} {L : Bytes} {c : Nat}
    (h0 : M (B + 0x21A0 + BitVec.ofNat 32 c) = BitVec.ofNat 8 (L.getD 0 0))
    (h1 : ∀ j, j < 31 → M (B + 0x21A0 + BitVec.ofNat 32 (c + 1 + j)) = BitVec.ofNat 8 (L.getD (1 + j) 0)) :
    memBytes M (B + 0x21A0 + BitVec.ofNat 32 c) 32 = b32 L := by
  unfold memBytes b32
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [add_ofNat_assoc]
  rcases j with _ | j
  · rw [Nat.add_zero, h0]
  · have := h1 j (by omega)
    rw [show c + 1 + j = c + (j + 1) by omega, show 1 + j = j + 1 by omega] at this
    rw [this]

end C3.RV32.Sv
