import C3BootProofs.Proofs.ShaFinal

/-!
# SHA-256 of a byte string

The compiled `c3_crypto::sha::sha256` builds a fresh hasher in its frame (an
outlined helper loads the initial hash value's address, and `memcpy` copies
it in), absorbs the input with `update`, moves the hasher with `memcpy`, and
calls `finalize`. `sha256Fn_correct` runs it through those functions'
theorems.
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem os_at_0 : fetchRel sha256FnCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF20, 2) := by decide
theorem os_at_2 : fetchRel sha256FnCode 0x2 = some (.store .sw sp ra 0xDC, 2) := by decide
theorem os_at_4 : fetchRel sha256FnCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xD8, 2) := by decide
theorem os_at_6 : fetchRel sha256FnCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xD4, 2) := by decide
theorem os_at_8 : fetchRel sha256FnCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xD0, 2) := by decide
theorem os_at_a : fetchRel sha256FnCode 0xA = some (.auipc (5 : Fin 32) 0x19000, 4) := by decide
theorem os_at_e : fetchRel sha256FnCode 0xE = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFB10, 4) := by decide
theorem os_at_12 : fetchRel sha256FnCode 0x12 = some (.auipc ra 0x19000, 4) := by decide
theorem os_at_16 : fetchRel sha256FnCode 0x16 = some (.jalr ra ra 0xFFFFFD2E, 4) := by decide
theorem os_at_1a : fetchRel sha256FnCode 0x1A = some (.store .sb sp x0 0x3F, 4) := by decide
theorem os_at_1e : fetchRel sha256FnCode 0x1E = some (.store .sw sp x0 0x60, 2) := by decide
theorem os_at_20 : fetchRel sha256FnCode 0x20 = some (.store .sw sp x0 0x64, 2) := by decide
theorem os_at_22 : fetchRel sha256FnCode 0x22 = some (.alu .add a0 x0 sp, 2) := by decide
theorem os_at_24 : fetchRel sha256FnCode 0x24 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem os_at_26 : fetchRel sha256FnCode 0x26 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem os_at_28 : fetchRel sha256FnCode 0x28 = some (.auipc ra 0x0, 4) := by decide
theorem os_at_2c : fetchRel sha256FnCode 0x2C = some (.jalr ra ra 0xFFFFFEB4, 4) := by decide
theorem os_at_30 : fetchRel sha256FnCode 0x30 = some (.aluImm .add a0 sp 0x68, 2) := by decide
theorem os_at_32 : fetchRel sha256FnCode 0x32 = some (.alu .add a1 x0 sp, 2) := by decide
theorem os_at_34 : fetchRel sha256FnCode 0x34 = some (.aluImm .add a2 x0 0x68, 4) := by decide
theorem os_at_38 : fetchRel sha256FnCode 0x38 = some (.auipc ra 0x19000, 4) := by decide
theorem os_at_3c : fetchRel sha256FnCode 0x3C = some (.jalr ra ra 0xFFFFFD08, 4) := by decide
theorem os_at_40 : fetchRel sha256FnCode 0x40 = some (.aluImm .add a1 sp 0x68, 2) := by decide
theorem os_at_42 : fetchRel sha256FnCode 0x42 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem os_at_44 : fetchRel sha256FnCode 0x44 = some (.auipc ra 0x0, 4) := by decide
theorem os_at_48 : fetchRel sha256FnCode 0x48 = some (.jalr ra ra 0xFFFFFD54, 4) := by decide
theorem os_at_4c : fetchRel sha256FnCode 0x4C = some (.load .lw ra sp 0xDC, 2) := by decide
theorem os_at_4e : fetchRel sha256FnCode 0x4E = some (.load .lw (8 : Fin 32) sp 0xD8, 2) := by decide
theorem os_at_50 : fetchRel sha256FnCode 0x50 = some (.load .lw (9 : Fin 32) sp 0xD4, 2) := by decide
theorem os_at_52 : fetchRel sha256FnCode 0x52 = some (.load .lw (18 : Fin 32) sp 0xD0, 2) := by decide
theorem os_at_54 : fetchRel sha256FnCode 0x54 = some (.aluImm .add sp sp 0xE0, 2) := by decide
theorem os_at_56 : fetchRel sha256FnCode 0x56 = some (.jalr x0 ra 0x0, 2) := by decide
theorem oi_at_0 : fetchRel shaInitCode 0x0 = some (.alu .add (8 : Fin 32) x0 a2, 2) := by decide
theorem oi_at_2 : fetchRel shaInitCode 0x2 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem oi_at_4 : fetchRel shaInitCode 0x4 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem oi_at_6 : fetchRel shaInitCode 0x6 = some (.aluImm .add a0 sp 0x40, 2) := by decide
theorem oi_at_8 : fetchRel shaInitCode 0x8 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem oi_at_c : fetchRel shaInitCode 0xC = some (.aluImm .add a1 a1 0x2A8, 4) := by decide
theorem oi_at_10 : fetchRel shaInitCode 0x10 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem oi_at_14 : fetchRel shaInitCode 0x14 = some (.jalr x0 (5 : Fin 32) 0x0, 2) := by decide

end

theorem memLoad32_copy {M M' : Word → BitVec 8} {b b' : Word}
    (h : ∀ j, j < 4 → M' (b' + BitVec.ofNat 32 j) = M (b + BitVec.ofNat 32 j)) : memLoad32 M' b' = memLoad32 M b := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  rw [h0, show b' + 1 = b' + BitVec.ofNat 32 1 from rfl, h 1 (by decide), show b' + 2 = b' + BitVec.ofNat 32 2 from rfl,
    h 2 (by decide), show b' + 3 = b' + BitVec.ofNat 32 3 from rfl, h 3 (by decide)]
  rfl

theorem wordsAt_copy {M M' : Word → BitVec 8} {b b' : Word} {n : Nat}
    (h : ∀ k, k < 4 * n → M' (b' + BitVec.ofNat 32 k) = M (b + BitVec.ofNat 32 k)) : wordsAt M' b' n = wordsAt M b n := by
  unfold wordsAt
  apply List.map_congr_left; intro i hi
  have hi := List.mem_range.mp hi
  exact memLoad32_copy fun j hj => by rw [add_ofNat_assoc, add_ofNat_assoc]; exact h _ (by omega)

/-- A copy of a hasher's 0x68 bytes holds the same message. -/
theorem HasherAt.copy {M M' : Word → BitVec 8} {S S' : Word} {msg : Bytes} (H : HasherAt M S msg)
    (h : ∀ i, i < 0x68 → M' (S' + BitVec.ofNat 32 i) = M (S + BitVec.ofNat 32 i)) : HasherAt M' S' msg := by
  have ld : ∀ c, c + 4 ≤ 0x68 → memLoad32 M' (S' + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 c) :=
    fun c hc => by
      unfold memLoad32
      rw [show S' + BitVec.ofNat 32 c + 3 = S' + BitVec.ofNat 32 (c + 3) from add_ofNat_assoc _ _ 3,
        show S' + BitVec.ofNat 32 c + 2 = S' + BitVec.ofNat 32 (c + 2) from add_ofNat_assoc _ _ 2,
        show S' + BitVec.ofNat 32 c + 1 = S' + BitVec.ofNat 32 (c + 1) from add_ofNat_assoc _ _ 1,
        show S + BitVec.ofNat 32 c + 3 = S + BitVec.ofNat 32 (c + 3) from add_ofNat_assoc _ _ 3,
        show S + BitVec.ofNat 32 c + 2 = S + BitVec.ofNat 32 (c + 2) from add_ofNat_assoc _ _ 2,
        show S + BitVec.ofNat 32 c + 1 = S + BitVec.ofNat 32 (c + 1) from add_ofNat_assoc _ _ 1,
        h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
  have hp := H.hlen
  have hpos : msg.length % 64 < 64 := Nat.mod_lt _ (by decide)
  exact { hlen := H.hlen
          pos := by rw [show S' + (0x3F : Word) = S' + BitVec.ofNat 32 0x3F from rfl, h _ (by omega)]; exact H.pos
          buf := by
            rw [← H.buf]; unfold memBytes
            apply List.map_congr_left; intro i hi
            have hi := List.mem_range.mp hi
            show (M' (S' + BitVec.ofNat 32 i)).toNat = (M (S + BitVec.ofNat 32 i)).toNat
            rw [h _ (by omega)]
          hash := by
            rw [← H.hash]; unfold wordsAt
            apply List.map_congr_left; intro i hi
            have hi := List.mem_range.mp hi
            show memLoad32 M' (S' + 0x40 + BitVec.ofNat 32 (4 * i)) = memLoad32 M (S + 0x40 + BitVec.ofNat 32 (4 * i))
            rw [show S' + (0x40 : Word) = S' + BitVec.ofNat 32 0x40 from rfl,
              show S + (0x40 : Word) = S + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc, add_ofNat_assoc]
            exact ld _ (by omega)
          lo := by
            rw [show S' + (0x60 : Word) = S' + BitVec.ofNat 32 0x60 from rfl, ld _ (by omega)]; exact H.lo
          hi := by
            rw [show S' + (0x64 : Word) = S' + BitVec.ofNat 32 0x64 from rfl, ld _ (by omega)]; exact H.hi }

set_option maxRecDepth 20000 in
/-- The image's initial hash value, as `memLoad32` reads it, is FIPS 180-4's
`H(0)`. -/
theorem iv_words {M : Word → BitVec 8} (h : CodeIn M (BitVec.ofNat 32 shaIVAddress) shaIVData) :
    wordsAt M (BitVec.ofNat 32 shaIVAddress) 8 = Sha256.h0 := by
  have e : wordsAt M (BitVec.ofNat 32 shaIVAddress) 8 =
      wordsAt (fun a => byteAt shaIVData (a - BitVec.ofNat 32 shaIVAddress).toNat) (BitVec.ofNat 32 shaIVAddress) 8 :=
    wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, h _ (by rw [show shaIVData.length = 32 from rfl]; omega), add_sub_toNat _ (by omega)]
  rw [e]; decide

set_option maxRecDepth 20000 in
/-- A caller's `auipc t0, imm; jalr t0, o(t0)` into the outlined helper that
starts `sha256`: it keeps the arguments in `s0` through `s2` and sets up
`memcpy` of the initial hash value into the frame at `sp + 0x40`. -/
theorem St.callShaInit {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine}
    {off : Nat} {f : Fin 32 → Word} (s : St M base m off f)
    (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc t0 imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr t0 t0 o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 shaInitAddress)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hh : CodeIn M (BitVec.ofNat 32 shaInitAddress) shaInitCode) :
    ∃ m', Steps m m' ∧ St M base m' (off + 8) (reg m') ∧
      reg m' s0 = f a2 ∧ reg m' s1 = f a1 ∧ reg m' s2 = f a0 ∧ reg m' a0 = f sp + 0x40 ∧
      reg m' a1 = BitVec.ofNat 32 shaIVAddress ∧ reg m' a2 = BitVec.ofNat 32 32 ∧
      ∀ r, r ≠ t0 → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = f r := by
  let IB := BitVec.ofNat 32 shaInitAddress
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  have r2 : ∀ r, r ≠ t0 → reg m2 r = f r := fun r h => by
    rw [regs2]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h]
  have t2 : reg m2 t0 = base + BitVec.ofNat 32 (off + 8) := by rw [regs2, hL]; simp +decide [upd]; try rfl
  have hp2 : m2.pc = IB := by
    rw [pc2, show upd f t0 (base + BitVec.ofNat 32 off + imm) t0 = base + BitVec.ofNat 32 off + imm from
      by simp +decide [upd], hb]
    decide
  have u2 : St M IB m2 0 (reg m2) := ⟨by rw [hp2]; simp, mem2, fun _ => rfl⟩
  obtain ⟨m3, e3, u3⟩ := u2.alu hh oi_at_0 (off' := 2) (by decide)
  have K3 := u3.upd_ne u2.zero
  have u3' : St M IB m3 2 (reg m3) := u3.self
  obtain ⟨m4, e4, u4⟩ := u3'.alu hh oi_at_2 (off' := 4) (by decide)
  have K4 := u4.upd_ne u3'.zero
  have u4' : St M IB m4 4 (reg m4) := u4.self
  obtain ⟨m5, e5, u5⟩ := u4'.alu hh oi_at_4 (off' := 6) (by decide)
  have K5 := u5.upd_ne u4'.zero
  have u5' : St M IB m5 6 (reg m5) := u5.self
  obtain ⟨m6, e6, u6⟩ := u5'.aluImm hh oi_at_6 (off' := 8) (by decide)
  have K6 := u6.upd_ne u5'.zero
  have u6' : St M IB m6 8 (reg m6) := u6.self
  obtain ⟨m7, e7, u7⟩ := u6'.lui hh oi_at_8 (off' := 0xC) (by decide)
  have K7 := u7.upd_ne u6'.zero
  have u7' : St M IB m7 0xC (reg m7) := u7.self
  obtain ⟨m8, e8, u8⟩ := u7'.aluImm hh oi_at_c (off' := 0x10) (by decide)
  have K8 := u8.upd_ne u7'.zero
  have u8' : St M IB m8 0x10 (reg m8) := u8.self
  obtain ⟨m9, e9, u9⟩ := u8'.aluImm hh oi_at_10 (off' := 0x14) (by decide)
  have K9 := u9.upd_ne u8'.zero
  have u9' : St M IB m9 0x14 (reg m9) := u9.self
  obtain ⟨m10, e10, pc10, mem10, regs10⟩ := u9'.jalr hh oi_at_14
  have K29 : ∀ r, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m9 r = reg m2 r :=
    fun r q8 q9 q18 q10 q11 q12 => by
      rw [K9 r q12, K8 r q11, K7 r q11, K6 r q10, K5 r q18, K4 r q9, K3 r q8]
  refine ⟨m10, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
    (.single e10))))))))), ⟨?_, mem10, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun r q5 q8 q9 q18 q10 q11 q12 => ?_⟩
  · rw [pc10, K29 t0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t2, add_lit_zero]
    exact even_clear _ hl
  · rw [regs10, K9 s0 (by decide), K8 s0 (by decide), K7 s0 (by decide), K6 s0 (by decide), K5 s0 (by decide),
      K4 s0 (by decide), u3.upd_eq (by decide), u2.zero, r2 a2 (by decide)]
    exact BitVec.zero_add _
  · rw [regs10, K9 s1 (by decide), K8 s1 (by decide), K7 s1 (by decide), K6 s1 (by decide), K5 s1 (by decide),
      u4.upd_eq (by decide), u3'.zero, K3 a1 (by decide), r2 a1 (by decide)]
    exact BitVec.zero_add _
  · rw [regs10, K9 s2 (by decide), K8 s2 (by decide), K7 s2 (by decide), K6 s2 (by decide),
      u5.upd_eq (by decide), u4'.zero, K4 a0 (by decide), K3 a0 (by decide), r2 a0 (by decide)]
    exact BitVec.zero_add _
  · rw [regs10, K9 a0 (by decide), K8 a0 (by decide), K7 a0 (by decide), u6.upd_eq (by decide),
      K5 sp (by decide), K4 sp (by decide), K3 sp (by decide), r2 sp (by decide)]; rfl
  · rw [regs10, K9 a1 (by decide), u8.upd_eq (by decide), u7.upd_eq (by decide)]; rfl
  · rw [regs10, u9.upd_eq (by decide), u8'.zero]; rfl
  · rw [regs10, K29 r q8 q9 q18 q10 q11 q12, r2 r q5]

/-- Where `sha256` runs: its code and its callees', the initial hash value,
the `n` input bytes at `D`, the output at `out`, and 0x270 bytes of stack
below `sp0`, all below 0x40000000; the input, the output, the initial hash
value, and the round constants are each apart from the stack. -/
structure Sha256Env (M : Word → BitVec 8) (out D sp0 : Word) (n : Nat) : Prop where
  cX : CodeIn M (BitVec.ofNat 32 sha256FnAddress) sha256FnCode
  cInit : CodeIn M (BitVec.ofNat 32 shaInitAddress) shaInitCode
  cIV : CodeIn M (BitVec.ofNat 32 shaIVAddress) shaIVData
  cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cUSave : CodeIn M (BitVec.ofNat 32 shaUpdateSaveAddress) shaUpdateSaveCode
  cURest : CodeIn M (BitVec.ofNat 32 shaUpdateRestoreAddress) shaUpdateRestoreCode
  cUBlk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cFSave : CodeIn M (BitVec.ofNat 32 shaFinalizeSaveAddress) shaFinalizeSaveCode
  cFRest : CodeIn M (BitVec.ofNat 32 shaFinalizeRestoreAddress) shaFinalizeRestoreCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cFBlk : CodeIn M (BitVec.ofNat 32 shaFinalizeBlockAddress) shaFinalizeBlockCode
  cBe : CodeIn M (BitVec.ofNat 32 shaStoreBeAddress) shaStoreBeCode
  cMs : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x2B94) shaIndexCode
  c97 : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0xC09C) shaSigma1PartCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hsp : sp0.toNat % 16 = 0
  hspl : 0x270 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hDw : D.toNat + n ≤ 0x40000000
  hOw : out.toNat + 32 ≤ 0x40000000
  sDF : Sep D n (sp0 + 0xFFFFFD90) 0x270
  sOF : Sep out 32 (sp0 + 0xFFFFFD90) 0x270
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFD90) 0x270
  sIF : Sep (BitVec.ofNat 32 shaIVAddress) 32 (sp0 + 0xFFFFFD90) 0x270

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `c3_crypto::sha::sha256`.** Called with the `n` bytes at
`D` and a 32-byte output at `out`, it writes FIPS 180-4's SHA-256 digest of
those bytes to `out`. It returns to `retAddr` with `sp` restored and the
callee-saved registers kept, and changes no memory outside the output and
0x270 bytes of stack below `sp`. `n` is below 2^31, as Rust's slice lengths
are. -/
theorem sha256Fn_correct (m : Machine) {out D sp0 retAddr : Word} {n : Nat}
    (E : Sha256Env m.mem out D sp0 n) (hpc : m.pc = BitVec.ofNat 32 sha256FnAddress)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = D) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hn : n < 2 ^ 31) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
        r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
        r ≠ (31 : Fin 32) → reg m' r = reg m r) ∧
      memBytes m'.mem out 32 = sha256 (memBytes m.mem D n) ∧
      ∀ x, Sep (sp0 + 0xFFFFFD90) 0x270 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  let Q := BitVec.ofNat 32 sha256FnAddress
  let M0 := m.mem
  let R := sp0 + 0xFFFFFD90
  let F := sp0 + 0xFFFFFF20
  have hspw := E.hspw
  have hspl := E.hspl
  have hDw := E.hDw
  have hOw := E.hOw
  have hRn : R.toNat = sp0.toNat - 0x270 := by
    show (sp0 + 0xFFFFFD90).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFD90 : Word).toNat = 2 ^ 32 - 0x270 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x270 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFR : F = R + BitVec.ofNat 32 0x190 := by
    show sp0 + 0xFFFFFF20 = sp0 + 0xFFFFFD90 + BitVec.ofNat 32 0x190; rw [BitVec.add_assoc]; rfl
  have Fc : ∀ c, F + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x190 + c) := fun c => by rw [hFR, add_ofNat_assoc]
  have hFn : F.toNat = sp0.toNat - 0xE0 := by rw [hFR, hRc _ (by omega), hRn]; omega
  have hFc : ∀ c, c ≤ 0xE0 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc => by
    rw [Fc, hRc _ (by omega), hFn, hRn]; omega
  have hFa : F.toNat % 16 = 0 := by rw [hFn]; have := E.hsp; omega
  have hFa4 : F.toNat % 4 = 0 := by omega
  have Rx : ∀ c l, c + l ≤ 0x270 → ∀ x, Sep R 0x270 x 1 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) h
  have Rd : ∀ c l, c + l ≤ 0x270 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk =>
    data_code (by rw [hRc _ (by omega)]; omega) hb hbk
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x270 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  -- The frame and the four saved registers.
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m1, e1, u1⟩ := st0.aluImm E.cX os_at_0 (off' := 2) (by decide)
  have K1 := u1.upd_ne st0.zero
  have u1' : St M0 Q m1 2 (reg m1) := u1.self
  have sp1 : reg m1 sp = F := by rw [u1.upd_eq (by decide), hsp]; rfl
  have slotA : ∀ c, c + 4 ≤ 0xE0 → c % 4 = 0 → (reg m1 sp + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [sp1]; exact aligned_add hFa4 h2
  obtain ⟨m2, e2, u2⟩ := u1'.sw E.cX os_at_2 (off' := 4) (by decide) (slotA 0xDC (by omega) (by omega))
  have cS : ∀ (Ma : Word → BitVec 8) (c : Nat) (v : Word), c + 4 ≤ 0xE0 →
      ∀ (b : Word) (code : List Nat), CodeIn Ma b code → 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn (memStore32 Ma (F + BitVec.ofNat 32 c) v) b code := fun Ma c v h b code hc hb hbl =>
    hc.store32 (by rw [Fc]; exact Rd _ _ (by omega) _ _ hb hbl)
  rw [sp1] at u2
  have cX2 := cS _ 0xDC (reg m1 ra) (by omega) _ _ E.cX (by decide) (by decide)
  obtain ⟨m3, e3, u3⟩ := u2.sw cX2 os_at_4 (off' := 6) (by decide) (by rw [sp1]; exact aligned_add hFa4 (k := 0xD8) (by decide))
  rw [sp1] at u3
  have cX3 := cS _ 0xD8 (reg m1 s0) (by omega) _ _ cX2 (by decide) (by decide)
  obtain ⟨m4, e4, u4⟩ := u3.sw cX3 os_at_6 (off' := 8) (by decide) (by rw [sp1]; exact aligned_add hFa4 (k := 0xD4) (by decide))
  rw [sp1] at u4
  have cX4 := cS _ 0xD4 (reg m1 s1) (by omega) _ _ cX3 (by decide) (by decide)
  obtain ⟨m5, e5, u5⟩ := u4.sw cX4 os_at_8 (off' := 0xA) (by decide) (by rw [sp1]; exact aligned_add hFa4 (k := 0xD0) (by decide))
  rw [sp1] at u5
  let M1 := memStore32 (memStore32 (memStore32 (memStore32 M0 (F + 0xDC) (reg m1 ra)) (F + 0xD8) (reg m1 s0))
    (F + 0xD4) (reg m1 s1)) (F + 0xD0) (reg m1 s2)
  have M1R : ∀ x, Sep R 0x270 x 1 → M1 x = M0 x := fun x hx => by
    show memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _ x = _
    rw [memStore32_get_sep (show Sep (F + 0xD0) 4 x 1 by rw [show F + (0xD0 : Word) = F + BitVec.ofNat 32 0xD0 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0xD4) 4 x 1 by rw [show F + (0xD4 : Word) = F + BitVec.ofNat 32 0xD4 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0xD8) 4 x 1 by rw [show F + (0xD8 : Word) = F + BitVec.ofNat 32 0xD8 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0xDC) 4 x 1 by rw [show F + (0xDC : Word) = F + BitVec.ofNat 32 0xDC from rfl, Fc]; exact Rx _ _ (by omega) x hx)]
  have cM1 := codeX M1 M1R
  have cX5 := cM1 _ _ E.cX (by decide) (by decide)
  obtain ⟨m6, c6, u6, s0_6, s1_6, s2_6, a0_6, a1_6, a2_6, K6⟩ := u5.callShaInit cX5 os_at_a os_at_e (by decide)
    (by decide) (cM1 _ _ E.cInit (by decide) (by decide))
  rw [K1 a2 (by decide), ha2] at s0_6
  rw [K1 a1 (by decide), ha1] at s1_6
  rw [K1 a0 (by decide), ha0] at s2_6
  rw [sp1] at a0_6
  obtain ⟨m7, e7, u7⟩ := u6.auipc cX5 os_at_12 (off' := 0x16) (by decide)
  obtain ⟨m8, e8, pc8, mem8, regs8⟩ := u7.call cX5 os_at_16
  have r8 : ∀ r, r ≠ ra → reg m8 r = reg m6 r := fun r h => by
    rw [regs8]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6.zero.symm
    · simp [upd, h0, h]
  have sp6 : reg m6 sp = F := by
    rw [K6 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1]
  have sp8 : reg m8 sp = F := by rw [r8 sp (by decide), sp6]
  have eF16 : F + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x180 := by rw [hFR, BitVec.add_assoc]; rfl
  have hF16 : (F + 0xFFFFFFF0).toNat = R.toNat + 0x180 := by rw [eF16, hRc _ (by omega)]
  obtain ⟨m9, c9, pc9, sp9, a09, mem9, K9⟩ := memcpy_correct m8 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 0x1A) (F + BitVec.ofNat 32 0x40) (BitVec.ofNat 32 shaIVAddress) 32
    (fun i hi => by show m8.mem _ = _; rw [mem8]; exact cM1 _ _ E.cMS (by decide) (by decide) i hi) (by decide)
    (by rw [pc8, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r8 a0 (by decide), a0_6]; rfl) (by rw [r8 a1 (by decide), a1_6]) (by rw [r8 a2 (by decide), a2_6])
    (by rw [regs8]; simp +decide [upd]; try rfl) (by decide)
    (by
      rw [mem8, sp8]
      exact { code := cM1 _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by rw [hFc _ (by omega)]; omega) (by decide) (by decide)
              hFC := data_code (by rw [hF16, hRn]; omega) (by decide) (by decide)
              hdF := by rw [Fc, eF16]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
              hsF := by rw [eF16]; exact E.sIF.subR (c := 0x180) (l := 16) (by omega)
              hsep := by rw [Fc]; exact (E.sIF.subR (c := 0x190 + 0x40) (l := 32) (by omega)).symm
              hF := by rw [hF16, hRn]; have := E.hsp; omega
              hFw := by rw [hF16, hRn]; omega
              hdw := by rw [hFc _ (by omega)]; omega
              hsw := by decide })
  rw [mem8, sp8, eF16] at mem9
  let MA := m9.mem
  have mA : ∀ x, Sep (R + BitVec.ofNat 32 0x180) 16 x 1 →
      MA x = copyBytes M1 (F + BitVec.ofNat 32 0x40) (BitVec.ofNat 32 shaIVAddress) 32 x := mem9
  have MAR : ∀ x, Sep R 0x270 x 1 → MA x = M0 x := fun x hx => by
    rw [mA x (Rx _ _ (by omega) x hx), copyBytes_sep (by rw [Fc]; exact Rx _ _ (by omega) x hx) (Nat.le_refl 32),
      M1R x hx]
  have cMA := codeX MA MAR
  have cXA := cMA _ _ E.cX (by decide) (by decide)
  have u9 : St MA Q m9 0x1A (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
  have k9 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg m9 r = reg m8 r := K9
  have sp9' : reg m9 sp = F := by rw [sp9, sp8]
  -- A fresh hasher: the initial hash value, an empty buffer, and no blocks.
  obtain ⟨m10, e10, u10⟩ := u9.sb cXA os_at_1a (off' := 0x1E) (by decide)
  rw [sp9', u9.zero] at u10
  have cXA1 := cXA.store8 (a := F + 0x3F) (v := (0 : Word).extractLsb' 0 8)
    (by rw [show F + (0x3F : Word) = F + BitVec.ofNat 32 0x3F from rfl, Fc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide))
  obtain ⟨m11, e11, u11⟩ := u10.sw cXA1 os_at_1e (off' := 0x20) (by decide)
    (by rw [sp9']; exact aligned_add hFa4 (k := 0x60) (by decide))
  rw [sp9', u9.zero] at u11
  have cXA2 := cXA1.store32 (a := F + 0x60) (v := 0)
    (by rw [show F + (0x60 : Word) = F + BitVec.ofNat 32 0x60 from rfl, Fc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide))
  obtain ⟨m12, e12, u12⟩ := u11.sw cXA2 os_at_20 (off' := 0x22) (by decide)
    (by rw [sp9']; exact aligned_add hFa4 (k := 0x64) (by decide))
  rw [sp9', u9.zero] at u12
  let MH := memStore32 (memStore32 (memStore8 MA (F + 0x3F) ((0 : Word).extractLsb' 0 8)) (F + 0x60) 0) (F + 0x64) 0
  have FR : ∀ c, c < 0xE0 → Sep R 0x270 (F + BitVec.ofNat 32 c) 1 → False := fun c hc h => by
    have := h (0x190 + c) (by omega) 0 (by decide); rw [add_ofNat_zero, Fc] at this; exact this rfl
  have MHR : ∀ x, Sep R 0x270 x 1 → MH x = M0 x := fun x hx => by
    show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ x = _
    rw [memStore32_get_sep (show Sep (F + 0x64) 4 x 1 by rw [show F + (0x64 : Word) = F + BitVec.ofNat 32 0x64 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0x60) 4 x 1 by rw [show F + (0x60 : Word) = F + BitVec.ofNat 32 0x60 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore8_ne (show x ≠ F + 0x3F from fun e => by
        rw [e, show F + (0x3F : Word) = F + BitVec.ofNat 32 0x3F from rfl] at hx; exact FR _ (by omega) hx),
      MAR x hx]
  have hF' : ∀ c, c < 0x68 → ∀ d, d < 0x68 → c ≠ d → F + BitVec.ofNat 32 c ≠ F + BitVec.ofNat 32 d :=
    fun c hc d hd h => add_ofNat_ne F (by omega) (by omega) h
  have H0 : HasherAt MH F [] :=
    { hlen := by decide
      pos := by
        show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ _ = _
        rw [memStore32_get_sep (show Sep (F + 0x64) 4 (F + 0x3F) 1 from
            sep_offsets F (c := 0x64) (d := 0x3F) (Or.inr (by omega)) (by omega) (by omega)),
          memStore32_get_sep (show Sep (F + 0x60) 4 (F + 0x3F) 1 from
            sep_offsets F (c := 0x60) (d := 0x3F) (Or.inr (by omega)) (by omega) (by omega)), memStore8_same]
        rfl
      buf := rfl
      hash := by
        show _ = Sha256.h0
        rw [← iv_words (M := M0) E.cIV]
        apply wordsAt_copy; intro k hk
        have hk' : k < 32 := hk
        rw [show F + (0x40 : Word) = F + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc]
        show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ _ = _
        rw [memStore32_get_sep (show Sep (F + 0x64) 4 (F + BitVec.ofNat 32 (0x40 + k)) 1 from
            sep_offsets F (c := 0x64) (d := 0x40 + k) (Or.inr (by omega)) (by omega) (by omega)),
          memStore32_get_sep (show Sep (F + 0x60) 4 (F + BitVec.ofNat 32 (0x40 + k)) 1 from
            sep_offsets F (c := 0x60) (d := 0x40 + k) (Or.inr (by omega)) (by omega) (by omega)),
          memStore8_ne (show F + BitVec.ofNat 32 (0x40 + k) ≠ F + 0x3F from hF' _ (by omega) 0x3F (by omega) (by omega)),
          mA _ (by rw [Fc]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
          ← add_ofNat_assoc, copyBytes_in (by omega) (by omega), M1R _ (E.sIF.sub (c := k) (l := 1) (by omega)).symm]
      lo := by
        show memLoad32 (memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _) _ = _
        rw [memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x60) 4 from
            sep_offsets F (c := 0x64) (d := 0x60) (Or.inr (by omega)) (by omega) (by omega)), memLoad32_store32_same]
        rfl
      hi := by
        show memLoad32 (memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _) _ = _
        rw [memLoad32_store32_same] }
  have cMH := codeX MH MHR
  have cXH := cMH _ _ E.cX (by decide) (by decide)
  have u12' : St MH Q m12 0x22 (reg m12) := u12.self
  have r12 : ∀ r, reg m12 r = reg m9 r := fun r => u12.regs r
  have K69 : ∀ r, r ≠ ra → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg m12 r = reg m6 r := fun r q1 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 => by
    rw [r12, k9 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r8 r q1]
  have s0_12 : reg m12 s0 = BitVec.ofNat 32 n := by
    rw [K69 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_6]
  have s1_12 : reg m12 s1 = D := by
    rw [K69 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_6]
  have s2_12 : reg m12 s2 = out := by
    rw [K69 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_6]
  have sp12 : reg m12 sp = F := by rw [r12, sp9']
  obtain ⟨m13, e13, u13⟩ := u12'.alu cXH os_at_22 (off' := 0x24) (by decide)
  have K13 := u13.upd_ne u12'.zero
  have u13' : St MH Q m13 0x24 (reg m13) := u13.self
  obtain ⟨m14, e14, u14⟩ := u13'.alu cXH os_at_24 (off' := 0x26) (by decide)
  have K14 := u14.upd_ne u13'.zero
  have u14' : St MH Q m14 0x26 (reg m14) := u14.self
  obtain ⟨m15, e15, u15⟩ := u14'.alu cXH os_at_26 (off' := 0x28) (by decide)
  have K15 := u15.upd_ne u14'.zero
  have u15' : St MH Q m15 0x28 (reg m15) := u15.self
  obtain ⟨m16, e16, u16⟩ := u15'.auipc cXH os_at_28 (off' := 0x2C) (by decide)
  obtain ⟨m17, e17, pc17, mem17, regs17⟩ := u16.call cXH os_at_2c
  have r17 : ∀ r, r ≠ ra → reg m17 r = reg m15 r := fun r h => by
    rw [regs17]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u15'.zero.symm
    · simp [upd, h0, h]
  have K1217 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m17 r = reg m12 r := fun r q1 q10 q11 q12 => by
    rw [r17 r q1, K15 r q12, K14 r q11, K13 r q10]
  have eU : F + 0xFFFFFF00 = R + BitVec.ofNat 32 0x90 := by rw [hFR, BitVec.add_assoc]; rfl
  have hUn : (F + 0xFFFFFF00).toNat = R.toNat + 0x90 := by rw [eU, hRc _ (by omega)]
  obtain ⟨m18, c18, pc18, sp18, K18, HU, fr18⟩ := shaUpdate_correct m17 (S := F) (D := D) (sp0 := F) (n := n)
    (msg := []) (retAddr := Q + BitVec.ofNat 32 0x30)
    { cU := by rw [mem17]; exact cMH _ _ E.cU (by decide) (by decide)
      cSave := by rw [mem17]; exact cMH _ _ E.cUSave (by decide) (by decide)
      cRest := by rw [mem17]; exact cMH _ _ E.cURest (by decide) (by decide)
      cBlk := by rw [mem17]; exact cMH _ _ E.cUBlk (by decide) (by decide)
      cC := by rw [mem17]; exact cMH _ _ E.cC (by decide) (by decide)
      cI := by rw [mem17]; exact cMH _ _ E.cI (by decide) (by decide)
      c97 := by rw [mem17]; exact cMH _ _ E.c97 (by decide) (by decide)
      cK := fun i hi => by
        have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
        rw [mem17, MHR _ (E.sKF.sub (c := i) (l := 1) (by omega)).symm]; exact E.cK i hi
      cMS := by rw [mem17]; exact cMH _ _ E.cMS (by decide) (by decide)
      cMB := by rw [mem17]; exact cMH _ _ E.cMB (by decide) (by decide)
      hS := hFa4
      hSw := by omega
      hsp := hFa
      hspl := by omega
      hspw := by omega
      hDw := hDw
      sDS := by rw [hFR]; exact E.sDF.subR (c := 0x190) (l := 0x68) (by omega)
      sDF := by rw [eU]; exact E.sDF.subR (c := 0x90) (l := 0x100) (by omega)
      sSF := by rw [eU, hFR]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
      sKS := by rw [hFR]; exact E.sKF.subR (c := 0x190) (l := 0x68) (by omega)
      sKF := by rw [eU]; exact E.sKF.subR (c := 0x90) (l := 0x100) (by omega) }
    (by rw [pc17, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r17 a0 (by decide), K15 a0 (by decide), K14 a0 (by decide), u13.upd_eq (by decide), u12'.zero, sp12]
        exact BitVec.zero_add _)
    (by rw [r17 a1 (by decide), K15 a1 (by decide), u14.upd_eq (by decide), u13'.zero, K13 s1 (by decide), s1_12]
        exact BitVec.zero_add _)
    (by rw [r17 a2 (by decide), u15.upd_eq (by decide), u14'.zero, K14 s0 (by decide), K13 s0 (by decide), s0_12]
        exact BitVec.zero_add _)
    (by rw [regs17]; simp +decide [upd]; try rfl) (by decide)
    (by rw [K1217 sp (by decide) (by decide) (by decide) (by decide), sp12]) (by rw [mem17]; exact H0) hn
    (by rw [List.length_nil]; omega)
  rw [mem17] at fr18
  let MU := m18.mem
  have fU : ∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → Sep F 0x68 x 1 → MU x = MH x := fr18
  have MUR : ∀ x, Sep R 0x270 x 1 → MU x = M0 x := fun x hx => by
    rw [fU x (by rw [eU]; exact Rx _ _ (by omega) x hx) (by rw [hFR]; exact Rx _ _ (by omega) x hx), MHR x hx]
  have hdat : memBytes MH D n = memBytes M0 D n :=
    memBytes_congr fun i hi => MHR _ (E.sDF.sub (c := i) (l := 1) (by omega)).symm
  rw [List.nil_append, mem17, hdat] at HU
  have cMU := codeX MU MUR
  have cXU := cMU _ _ E.cX (by decide) (by decide)
  have u18 : St MU Q m18 0x30 (reg m18) := ⟨by rw [pc18], rfl, fun _ => rfl⟩
  have k18 : ∀ r, r ≠ ra → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
      r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
      r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → reg m18 r = reg m17 r := K18
  have K1218 : ∀ r, r ≠ ra → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
      r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
      r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → reg m18 r = reg m12 r :=
    fun r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2 => by
      rw [k18 r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2, K1217 r q1 q10 q11 q12]
  have sp18' : reg m18 sp = F := sp18
  -- Move the hasher, as `finalize` takes it by value.
  obtain ⟨m19, e19, u19⟩ := u18.aluImm cXU os_at_30 (off' := 0x32) (by decide)
  have K19 := u19.upd_ne u18.zero
  have u19' : St MU Q m19 0x32 (reg m19) := u19.self
  obtain ⟨m20, e20, u20⟩ := u19'.alu cXU os_at_32 (off' := 0x34) (by decide)
  have K20 := u20.upd_ne u19'.zero
  have u20' : St MU Q m20 0x34 (reg m20) := u20.self
  obtain ⟨m21, e21, u21⟩ := u20'.aluImm cXU os_at_34 (off' := 0x38) (by decide)
  have K21 := u21.upd_ne u20'.zero
  have u21' : St MU Q m21 0x38 (reg m21) := u21.self
  obtain ⟨m22, e22, u22⟩ := u21'.auipc cXU os_at_38 (off' := 0x3C) (by decide)
  obtain ⟨m23, e23, pc23, mem23, regs23⟩ := u22.call cXU os_at_3c
  have r23 : ∀ r, r ≠ ra → reg m23 r = reg m21 r := fun r h => by
    rw [regs23]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u21'.zero.symm
    · simp [upd, h0, h]
  have K1823 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m23 r = reg m18 r := fun r q1 q10 q11 q12 => by
    rw [r23 r q1, K21 r q12, K20 r q11, K19 r q10]
  have sp23 : reg m23 sp = F := by rw [K1823 sp (by decide) (by decide) (by decide) (by decide), sp18']
  obtain ⟨m24, c24, pc24, sp24, a024, mem24, K24⟩ := memcpy_correct m23 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 0x40) (F + BitVec.ofNat 32 0x68) F 0x68
    (fun i hi => by show m23.mem _ = _; rw [mem23]; exact cMU _ _ E.cMS (by decide) (by decide) i hi) (by decide)
    (by rw [pc23, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r23 a0 (by decide), K21 a0 (by decide), K20 a0 (by decide), u19.upd_eq (by decide), sp18']; rfl)
    (by rw [r23 a1 (by decide), K21 a1 (by decide), u20.upd_eq (by decide), u19'.zero, K19 sp (by decide), sp18']
        exact BitVec.zero_add _)
    (by rw [r23 a2 (by decide), u21.upd_eq (by decide), u20'.zero]; rfl)
    (by rw [regs23]; simp +decide [upd]; try rfl) (by decide)
    (by
      rw [mem23, sp23]
      exact { code := cMU _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by rw [hFc _ (by omega)]; omega) (by decide) (by decide)
              hFC := data_code (by rw [hF16, hRn]; omega) (by decide) (by decide)
              hdF := by rw [Fc, eF16]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
              hsF := by rw [eF16, hFR]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
              hsep := by
                have h := sep_offsets F (c := 0x68) (n := 0x68) (d := 0) (k := 0x68) (Or.inr (by omega)) (by omega)
                  (by omega)
                rwa [add_ofNat_zero] at h
              hF := by rw [hF16, hRn]; have := E.hsp; omega
              hFw := by rw [hF16, hRn]; omega
              hdw := by rw [hFc _ (by omega)]; omega
              hsw := by omega })
  rw [mem23, sp23, eF16] at mem24
  let MC := m24.mem
  have mC : ∀ x, Sep (R + BitVec.ofNat 32 0x180) 16 x 1 → MC x = copyBytes MU (F + BitVec.ofNat 32 0x68) F 0x68 x := mem24
  have MCR : ∀ x, Sep R 0x270 x 1 → MC x = M0 x := fun x hx => by
    rw [mC x (Rx _ _ (by omega) x hx), copyBytes_sep (by rw [Fc]; exact Rx _ _ (by omega) x hx) (Nat.le_refl _),
      MUR x hx]
  have HC : HasherAt MC (F + BitVec.ofNat 32 0x68) (memBytes M0 D n) := HU.copy fun i hi => by
    rw [mC (F + BitVec.ofNat 32 0x68 + BitVec.ofNat 32 i) (by
        rw [add_ofNat_assoc, Fc]
        exact sep_offsets R (c := 0x180) (n := 16) (d := 0x190 + (0x68 + i)) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)),
      copyBytes_in hi (by omega)]
  have cMC := codeX MC MCR
  have cXC := cMC _ _ E.cX (by decide) (by decide)
  have u24 : St MC Q m24 0x40 (reg m24) := ⟨by rw [pc24], rfl, fun _ => rfl⟩
  have k24 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg m24 r = reg m23 r := K24
  have sp24' : reg m24 sp = F := by rw [sp24, sp23]
  obtain ⟨m25, e25, u25⟩ := u24.aluImm cXC os_at_40 (off' := 0x42) (by decide)
  have K25 := u25.upd_ne u24.zero
  have u25' : St MC Q m25 0x42 (reg m25) := u25.self
  obtain ⟨m26, e26, u26⟩ := u25'.alu cXC os_at_42 (off' := 0x44) (by decide)
  have K26 := u26.upd_ne u25'.zero
  have u26' : St MC Q m26 0x44 (reg m26) := u26.self
  obtain ⟨m27, e27, u27⟩ := u26'.auipc cXC os_at_44 (off' := 0x48) (by decide)
  obtain ⟨m28, e28, pc28, mem28, regs28⟩ := u27.call cXC os_at_48
  have r28 : ∀ r, r ≠ ra → reg m28 r = reg m26 r := fun r h => by
    rw [regs28]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u26'.zero.symm
    · simp [upd, h0, h]
  have s2_24 : reg m24 s2 = out := by
    rw [k24 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K1823 s2 (by decide) (by decide)
      (by decide) (by decide), K1218 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), s2_12]
  have eR : F + 0xFFFFFE70 = R := by rw [hFR, BitVec.add_assoc]; exact BitVec.add_zero R
  have hS68 : (F + BitVec.ofNat 32 0x68).toNat = F.toNat + 0x68 := hFc _ (by omega)
  obtain ⟨m29, c29, pc29, sp29, K29, out29, fr29⟩ := shaFinalize_correct m28 (S := F + BitVec.ofNat 32 0x68)
    (out := out) (sp0 := F) (retAddr := Q + BitVec.ofNat 32 0x4C) (msg := memBytes M0 D n)
    { cF := by rw [mem28]; exact cMC _ _ E.cF (by decide) (by decide)
      cSave := by rw [mem28]; exact cMC _ _ E.cFSave (by decide) (by decide)
      cRest := by rw [mem28]; exact cMC _ _ E.cFRest (by decide) (by decide)
      cZ := by rw [mem28]; exact cMC _ _ E.cZ (by decide) (by decide)
      cBlk := by rw [mem28]; exact cMC _ _ E.cFBlk (by decide) (by decide)
      cBe := by rw [mem28]; exact cMC _ _ E.cBe (by decide) (by decide)
      cMs := by rw [mem28]; exact cMC _ _ E.cMs (by decide) (by decide)
      cMS := by rw [mem28]; exact cMC _ _ E.cMS (by decide) (by decide)
      cMB := by rw [mem28]; exact cMC _ _ E.cMB (by decide) (by decide)
      cC := by rw [mem28]; exact cMC _ _ E.cC (by decide) (by decide)
      cI := by rw [mem28]; exact cMC _ _ E.cI (by decide) (by decide)
      c97 := by rw [mem28]; exact cMC _ _ E.c97 (by decide) (by decide)
      cK := fun i hi => by
        have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
        rw [mem28, MCR _ (E.sKF.sub (c := i) (l := 1) (by omega)).symm]; exact E.cK i hi
      hS := by rw [hS68]; omega
      hSw := by rw [hS68]; omega
      hsp := hFa
      hspl := by omega
      hspw := by omega
      hOw := hOw
      sSF := by
        rw [eR, Fc]
        have h := sep_offsets R (c := 0x190 + 0x68) (n := 0x68) (d := 0) (k := 0x190) (Or.inr (by omega)) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at h
      sOF := by rw [eR]; have h := E.sOF.subR (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h
      sOS := by rw [Fc]; exact E.sOF.subR (c := 0x190 + 0x68) (l := 0x68) (by omega)
      sKS := by rw [Fc]; exact E.sKF.subR (c := 0x190 + 0x68) (l := 0x68) (by omega)
      sKF := by rw [eR]; have h := E.sKF.subR (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h }
    (by rw [pc28, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r28 a0 (by decide), u26.upd_eq (by decide), u25'.zero, K25 s2 (by decide), s2_24]
        exact BitVec.zero_add _)
    (by rw [r28 a1 (by decide), K26 a1 (by decide), u25.upd_eq (by decide), sp24']; rfl)
    (by rw [regs28]; simp +decide [upd]; try rfl) (by decide)
    (by rw [r28 sp (by decide), K26 sp (by decide), K25 sp (by decide), sp24']) (by rw [mem28]; exact HC)
  rw [eR, mem28] at fr29
  let MF := m29.mem
  have fF : ∀ x, Sep R 0x190 x 1 → Sep (F + BitVec.ofNat 32 0x68) 0x68 x 1 → Sep out 32 x 1 → MF x = MC x := fr29
  -- The saved registers survive in the frame.
  have slotF : ∀ k, 0xD0 ≤ k → k < 0xE0 → MF (F + BitVec.ofNat 32 k) = M1 (F + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have rk : F + BitVec.ofNat 32 k = R + BitVec.ofNat 32 (0x190 + k) := Fc k
    have hR1 : Sep R 0x190 (F + BitVec.ofNat 32 k) 1 := by
      rw [rk]
      have h := sep_offsets R (c := 0) (n := 0x190) (d := 0x190 + k) (k := 1) (Or.inl (by omega)) (by omega)
        (by omega)
      rwa [add_ofNat_zero] at h
    have hS1 : Sep (F + BitVec.ofNat 32 0x68) 0x68 (F + BitVec.ofNat 32 k) 1 :=
      sep_offsets F (c := 0x68) (d := k) (Or.inl (by omega)) (by omega) (by omega)
    have hO1 : Sep out 32 (F + BitVec.ofNat 32 k) 1 := by rw [rk]; exact E.sOF.subR (c := 0x190 + k) (l := 1) (by omega)
    have hF1 : Sep F 0x68 (F + BitVec.ofNat 32 k) 1 := by
      have h := sep_offsets F (c := 0) (n := 0x68) (d := k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at h
    rw [fF _ hR1 hS1 hO1,
      mC _ (by rw [rk]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (sep_offsets F (Or.inl (by omega)) (by omega) (by omega)) (Nat.le_refl _),
      fU _ (by rw [eU, rk]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)) hF1]
    show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ _ = _
    rw [memStore32_get_sep (show Sep (F + 0x64) 4 (F + BitVec.ofNat 32 k) 1 from
        sep_offsets F (c := 0x64) (d := k) (Or.inl (by omega)) (by omega) (by omega)),
      memStore32_get_sep (show Sep (F + 0x60) 4 (F + BitVec.ofNat 32 k) 1 from
        sep_offsets F (c := 0x60) (d := k) (Or.inl (by omega)) (by omega) (by omega)),
      memStore8_ne (show F + BitVec.ofNat 32 k ≠ F + 0x3F from add_ofNat_ne F (c := k) (d := 0x3F) (by omega) (by omega) (by omega)),
      mA _ (by rw [rk]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (sep_offsets F (Or.inl (by omega)) (by omega) (by omega)) (Nat.le_refl _)]
  have ldF : ∀ c, 0xD0 ≤ c → c + 4 ≤ 0xE0 → memLoad32 MF (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact slotF _ (by omega) (by omega)
  have so : ∀ c d, c < 0xE0 → d < 0xE0 → c + 4 ≤ d ∨ d + 4 ≤ c → Sep (F + BitVec.ofNat 32 c) 4 (F + BitVec.ofNat 32 d) 4 :=
    fun c d hc hd h => sep_offsets F h (by omega) (by omega)
  have vRa : memLoad32 M1 (F + 0xDC) = reg m ra := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_sep (show Sep (F + 0xD0) 4 (F + 0xDC) 4 from so 0xD0 0xDC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xDC) 4 from so 0xD4 0xDC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xDC) 4 from so 0xD8 0xDC (by omega) (by omega) (by omega)),
      memLoad32_store32_same, K1 ra (by decide)]
  have vS0 : memLoad32 M1 (F + 0xD8) = reg m s0 := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_sep (show Sep (F + 0xD0) 4 (F + 0xD8) 4 from so 0xD0 0xD8 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xD8) 4 from so 0xD4 0xD8 (by omega) (by omega) (by omega)),
      memLoad32_store32_same, K1 s0 (by decide)]
  have vS1 : memLoad32 M1 (F + 0xD4) = reg m s1 := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_sep (show Sep (F + 0xD0) 4 (F + 0xD4) 4 from so 0xD0 0xD4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same, K1 s1 (by decide)]
  have vS2 : memLoad32 M1 (F + 0xD0) = reg m s2 := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_same, K1 s2 (by decide)]
  sorry

end C3.RV32
