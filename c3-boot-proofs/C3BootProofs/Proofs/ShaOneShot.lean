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

end C3.RV32
