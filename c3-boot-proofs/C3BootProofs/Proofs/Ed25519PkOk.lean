import C3BootProofs.Proofs.EdVerifyingKey
import C3BootProofs.Proofs.IsSmallOrder
import C3BootProofs.Proofs.ByteCompare
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Image.BootloaderData7

/-!
# `c3_crypto::ed25519_public_key_ok`, as compiled

`ed25519_public_key_ok` copies the key, clears its sign bit, and rejects it
unless the copy is below `p` (`less_than_le`) and, when the sign bit is set,
differs from the two encodings with `x = 0`. It then decompresses the key
through the proved `VerifyingKey::from_bytes` and accepts when the point is
not of small order (`is_small_order`).
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem pko_at_0 : fetchRel ed25519PublicKeyOkCode 0x0 = some (.aluImm .add sp sp 0xFFFFFE70, 2) := by decide
theorem pko_at_2 : fetchRel ed25519PublicKeyOkCode 0x2 = some (.aluImm .add a1 sp 0x180, 2) := by decide
theorem pko_at_4 : fetchRel ed25519PublicKeyOkCode 0x4 = some (.store .sw a1 ra 0xC, 4) := by decide
theorem pko_at_8 : fetchRel ed25519PublicKeyOkCode 0x8 = some (.store .sw a1 (8 : Fin 32) 0x8, 2) := by decide
theorem pko_at_a : fetchRel ed25519PublicKeyOkCode 0xA = some (.store .sw a1 (9 : Fin 32) 0x4, 2) := by decide
theorem pko_at_c : fetchRel ed25519PublicKeyOkCode 0xC = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem pko_at_e : fetchRel ed25519PublicKeyOkCode 0xE = some (.alu .add a0 x0 sp, 2) := by decide
theorem pko_at_10 : fetchRel ed25519PublicKeyOkCode 0x10 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem pko_at_14 : fetchRel ed25519PublicKeyOkCode 0x14 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pko_at_16 : fetchRel ed25519PublicKeyOkCode 0x16 = some (.auipc ra 0x12000, 4) := by decide
theorem pko_at_1a : fetchRel ed25519PublicKeyOkCode 0x1A = some (.jalr ra ra 0xFFFFFA18, 4) := by decide
theorem pko_at_1e : fetchRel ed25519PublicKeyOkCode 0x1E = some (.load .lb (9 : Fin 32) sp 0x1F, 4) := by decide
theorem pko_at_22 : fetchRel ed25519PublicKeyOkCode 0x22 = some (.aluImm .and a0 (9 : Fin 32) 0x7F, 4) := by decide
theorem pko_at_26 : fetchRel ed25519PublicKeyOkCode 0x26 = some (.store .sb sp a0 0x1F, 4) := by decide
theorem pko_at_2a : fetchRel ed25519PublicKeyOkCode 0x2A = some (.lui a1 0x3FCC4000, 4) := by decide
theorem pko_at_2e : fetchRel ed25519PublicKeyOkCode 0x2E = some (.aluImm .add a1 a1 0x198, 4) := by decide
theorem pko_at_32 : fetchRel ed25519PublicKeyOkCode 0x32 = some (.alu .add a0 x0 sp, 2) := by decide
theorem pko_at_34 : fetchRel ed25519PublicKeyOkCode 0x34 = some (.auipc ra 0x0, 4) := by decide
theorem pko_at_38 : fetchRel ed25519PublicKeyOkCode 0x38 = some (.jalr ra ra 0xFFFFFFA8, 4) := by decide
theorem pko_at_3c : fetchRel ed25519PublicKeyOkCode 0x3C = some (.branch .beq a0 x0 0x5E, 2) := by decide
theorem pko_at_3e : fetchRel ed25519PublicKeyOkCode 0x3E = some (.branch .blt (9 : Fin 32) x0 0x34, 4) := by decide
theorem pko_at_42 : fetchRel ed25519PublicKeyOkCode 0x42 = some (.alu .add a0 x0 sp, 2) := by decide
theorem pko_at_44 : fetchRel ed25519PublicKeyOkCode 0x44 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pko_at_46 : fetchRel ed25519PublicKeyOkCode 0x46 = some (.auipc ra 0x0, 4) := by decide
theorem pko_at_4a : fetchRel ed25519PublicKeyOkCode 0x4A = some (.jalr ra ra 0x64, 4) := by decide
theorem pko_at_4e : fetchRel ed25519PublicKeyOkCode 0x4E = some (.load .lw a0 sp 0x0, 2) := by decide
theorem pko_at_50 : fetchRel ed25519PublicKeyOkCode 0x50 = some (.branch .bne a0 x0 0x4A, 2) := by decide
theorem pko_at_52 : fetchRel ed25519PublicKeyOkCode 0x52 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem pko_at_54 : fetchRel ed25519PublicKeyOkCode 0x54 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pko_at_56 : fetchRel ed25519PublicKeyOkCode 0x56 = some (.aluImm .add a2 x0 0xC0, 4) := by decide
theorem pko_at_5a : fetchRel ed25519PublicKeyOkCode 0x5A = some (.auipc ra 0x12000, 4) := by decide
theorem pko_at_5e : fetchRel ed25519PublicKeyOkCode 0x5E = some (.jalr ra ra 0xFFFFF9D4, 4) := by decide
theorem pko_at_62 : fetchRel ed25519PublicKeyOkCode 0x62 = some (.aluImm .add a0 sp 0xE4, 2) := by decide
theorem pko_at_64 : fetchRel ed25519PublicKeyOkCode 0x64 = some (.auipc ra 0xE000, 4) := by decide
theorem pko_at_68 : fetchRel ed25519PublicKeyOkCode 0x68 = some (.jalr ra ra 0xFFFFFA7A, 4) := by decide
theorem pko_at_6c : fetchRel ed25519PublicKeyOkCode 0x6C = some (.aluImm .xor a0 a0 0x1, 4) := by decide
theorem pko_at_70 : fetchRel ed25519PublicKeyOkCode 0x70 = some (.jal x0 0x2C, 2) := by decide
theorem pko_at_72 : fetchRel ed25519PublicKeyOkCode 0x72 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem pko_at_76 : fetchRel ed25519PublicKeyOkCode 0x76 = some (.aluImm .add a1 a1 0x158, 4) := by decide
theorem pko_at_7a : fetchRel ed25519PublicKeyOkCode 0x7A = some (.alu .add a0 x0 sp, 2) := by decide
theorem pko_at_7c : fetchRel ed25519PublicKeyOkCode 0x7C = some (.auipc ra 0x0, 4) := by decide
theorem pko_at_80 : fetchRel ed25519PublicKeyOkCode 0x80 = some (.jalr ra ra 0x94, 4) := by decide
theorem pko_at_84 : fetchRel ed25519PublicKeyOkCode 0x84 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem pko_at_86 : fetchRel ed25519PublicKeyOkCode 0x86 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem pko_at_8a : fetchRel ed25519PublicKeyOkCode 0x8A = some (.aluImm .add a1 a1 0x1F8, 4) := by decide
theorem pko_at_8e : fetchRel ed25519PublicKeyOkCode 0x8E = some (.alu .add a0 x0 sp, 2) := by decide
theorem pko_at_90 : fetchRel ed25519PublicKeyOkCode 0x90 = some (.auipc ra 0x0, 4) := by decide
theorem pko_at_94 : fetchRel ed25519PublicKeyOkCode 0x94 = some (.jalr ra ra 0x80, 4) := by decide
theorem pko_at_98 : fetchRel ed25519PublicKeyOkCode 0x98 = some (.branch .beq a0 x0 0xFFFFFFAA, 2) := by decide
theorem pko_at_9a : fetchRel ed25519PublicKeyOkCode 0x9A = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem pko_at_9c : fetchRel ed25519PublicKeyOkCode 0x9C = some (.aluImm .add a1 sp 0x180, 2) := by decide
theorem pko_at_9e : fetchRel ed25519PublicKeyOkCode 0x9E = some (.load .lw ra a1 0xC, 4) := by decide
theorem pko_at_a2 : fetchRel ed25519PublicKeyOkCode 0xA2 = some (.load .lw (8 : Fin 32) a1 0x8, 2) := by decide
theorem pko_at_a4 : fetchRel ed25519PublicKeyOkCode 0xA4 = some (.load .lw (9 : Fin 32) a1 0x4, 2) := by decide
theorem pko_at_a6 : fetchRel ed25519PublicKeyOkCode 0xA6 = some (.aluImm .add sp sp 0x190, 2) := by decide
theorem pko_at_a8 : fetchRel ed25519PublicKeyOkCode 0xA8 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev PKO : Word := BitVec.ofNat 32 ed25519PublicKeyOkAddress

/-- Whether `decompress`'s result is a point not of small order. -/
def pkRes : Option (List Nat × List Nat × List Nat × List Nat) → Bool
  | none => false
  | some (X, Y, Z, _) => !isoSpec X Y Z

/-- The 32 bytes with bit 255 cleared. -/
def clearTop (b : Bytes) : Bytes := b.set 31 (b.getD 31 0 % 128)

/-- `less_than_le` on byte lists: the first `k` bytes, little-endian, of `x`
are below those of `y`. -/
def ltLEb (x y : Bytes) : Nat → Bool
  | 0 => false
  | k + 1 => if x.getD k 0 = y.getD k 0 then ltLEb x y k else decide (x.getD k 0 < y.getD k 0)

/-- `ed25519_public_key_ok` on the key bytes `b`, with `p` and the two
encodings with `x = 0` as the image holds them, and the constants
`decompress` reads. -/
def pkOkSpec (P E1 E2 one d sm : List Nat) (b : Bytes) : Bool :=
  ltLEb (clearTop b) P 32 && !(decide (128 ≤ b.getD 31 0) && (decide (clearTop b = E1) || decide (clearTop b = E2))) &&
    pkRes (decSpec one d sm b)

theorem ltLE_bytes (M : Word → BitVec 8) (a b : Word) {n : Nat} :
    ∀ k, k ≤ n → ltLE M a b k = ltLEb (memBytes M a n) (memBytes M b n) k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [ltLE, ltLEb]
    rw [getD_memBytes M a (by omega), getD_memBytes M b (by omega), ltLE_bytes M a b (n := n) k (by omega)]
    by_cases e : M (a + BitVec.ofNat 32 k) = M (b + BitVec.ofNat 32 k)
    · have e' : byteN M a k = byteN M b k := by unfold byteN; rw [e]
      simp only [e, e', ↓reduceIte]
    · have e' : ¬ byteN M a k = byteN M b k := fun h => e (BitVec.eq_of_toNat_eq h)
      simp only [e, e', ↓reduceIte]

/-- Between calls, `ed25519_public_key_ok`'s state: `sp` at `G + 0x7B0`,
`s0` holding the key's address, the callee-saved registers it doesn't use
as on entry, memory outside the 0x940 bytes of stack at `G` as on entry, and
its three saved registers' slots as after the prologue. -/
structure PkSt (M0 Ms : Word → BitVec 8) (G pk : Word) (r0 : Fin 32 → Word) (M : Word → BitVec 8) (n : Machine)
    (off : Nat) : Prop where
  st : St M PKO n off (reg n)
  hsp : reg n sp = G + BitVec.ofNat 32 0x7B0
  hs0 : reg n (8 : Fin 32) = pk
  keep : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n q = r0 q
  agree : ∀ x, Sep G 0x940 x 1 → M x = M0 x
  slots : ∀ c, 0x934 ≤ c → c < 0x940 → M (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c)

theorem PkSt.jmp {M0 Ms G pk r0 M n off n1 off'} (D : PkSt M0 Ms G pk r0 M n off) (u : St M PKO n1 off' (reg n)) :
    PkSt M0 Ms G pk r0 M n1 off' :=
  ⟨u.self, by rw [u.regs, D.hsp], by rw [u.regs, D.hs0], fun q hq => by rw [u.regs, D.keep q hq], D.agree, D.slots⟩

theorem PkSt.slotW {M0 Ms G pk r0 M n off} (D : PkSt M0 Ms G pk r0 M n off) {c : Nat} (h1 : 0x934 ≤ c)
    (h2 : c + 4 ≤ 0x940) : memLoad32 M (G + BitVec.ofNat 32 c) = memLoad32 Ms (G + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact D.slots _ (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- From offset 0x9C: the epilogue, returning `a0`. -/
theorem pk_tail {M0 Ms G pk r0 M n} (D : PkSt M0 Ms G pk r0 M n 0x9C) (hc : CodeIn M PKO ed25519PublicKeyOkCode)
    (hG : G.toNat % 4 = 0) :
    ∃ m', Steps n m' ∧ m'.pc = memLoad32 Ms (G + BitVec.ofNat 32 0x93C) &&& ~~~1 ∧
      reg m' sp = G + BitVec.ofNat 32 0x940 ∧ reg m' a0 = reg n a0 ∧
      reg m' ra = memLoad32 Ms (G + BitVec.ofNat 32 0x93C) ∧
      reg m' (8 : Fin 32) = memLoad32 Ms (G + BitVec.ofNat 32 0x938) ∧
      reg m' (9 : Fin 32) = memLoad32 Ms (G + BitVec.ofNat 32 0x934) ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = r0 q) ∧ m'.mem = M := by
  have s := D.st
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc pko_at_9c (off' := 0x9E) (by decide)
  have a1v : reg n1 a1 = G + BitVec.ofNat 32 0x930 := by rw [u1.upd_eq (by decide), D.hsp]; exact add_sp G rfl
  have al : ∀ k : Nat, (0x930 + k) % 4 = 0 → (G + BitVec.ofNat 32 0x930 + BitVec.ofNat 32 k).toNat % 4 = 0 :=
    fun k hk => by rw [spk]; exact aligned_add hG hk
  obtain ⟨n2, d2, u2⟩ := u1.self.lw hc pko_at_9e (off' := 0xA2) (by decide) (by rw [a1v]; exact al 0xC rfl)
  obtain ⟨n3, d3, u3⟩ := u2.self.lw hc pko_at_a2 (off' := 0xA4) (by decide)
    (by rw [u2.upd_ne u1.self.zero _ (by decide), a1v]; exact al 8 rfl)
  obtain ⟨n4, d4, u4⟩ := u3.self.lw hc pko_at_a4 (off' := 0xA6) (by decide)
    (by rw [u3.upd_ne u2.self.zero _ (by decide), u2.upd_ne u1.self.zero _ (by decide), a1v]; exact al 4 rfl)
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc pko_at_a6 (off' := 0xA8) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hc pko_at_a8
  have L : ∀ k, memLoad32 M (G + BitVec.ofNat 32 0x930 + BitVec.ofNat 32 k) = memLoad32 M (G + BitVec.ofNat 32 (0x930 + k)) :=
    fun k => by rw [spk]
  have vra : reg n4 ra = memLoad32 Ms (G + BitVec.ofNat 32 0x93C) := by
    rw [u4.upd_ne u3.self.zero _ (by decide), u3.upd_ne u2.self.zero _ (by decide), u2.upd_eq (by decide), a1v]
    exact (L 0xC).trans (D.slotW (by decide) (by decide))
  have vs0 : reg n4 (8 : Fin 32) = memLoad32 Ms (G + BitVec.ofNat 32 0x938) := by
    rw [u4.upd_ne u3.self.zero _ (by decide), u3.upd_eq (by decide), u2.upd_ne u1.self.zero _ (by decide), a1v]
    exact (L 8).trans (D.slotW (by decide) (by decide))
  have vs1 : reg n4 (9 : Fin 32) = memLoad32 Ms (G + BitVec.ofNat 32 0x934) := by
    rw [u4.upd_eq (by decide), u3.upd_ne u2.self.zero _ (by decide), u2.upd_ne u1.self.zero _ (by decide), a1v]
    exact (L 4).trans (D.slotW (by decide) (by decide))
  have r4 : ∀ q, q ≠ a1 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n4 q = reg n q := fun q h1 h2 h3 h4 => by
    rw [u4.upd_ne u3.self.zero q h4, u3.upd_ne u2.self.zero q h3, u2.upd_ne u1.self.zero q h2, u1.upd_ne hz q h1]
  refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ?_, ?_, ?_, ?_, ?_, ?_,
    fun q hq => ?_, by rw [mem6]⟩
  · rw [pc6, u5.upd_ne u4.self.zero _ (by decide), vra, add_lit_zero]
  · rw [regs6, u5.upd_eq (by decide), r4 sp (by decide) (by decide) (by decide) (by decide), D.hsp]; exact add_sp G rfl
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), r4 a0 (by decide) (by decide) (by decide) (by decide)]
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), vra]
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), vs0]
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), vs1]
  · rw [regs6, u5.upd_ne u4.self.zero _ (by revert hq; revert q; decide),
      r4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), D.keep q hq]

set_option maxRecDepth 20000 in
/-- An `ISOEnv` survives any change below the code that keeps `ONE`. -/
theorem ISOEnv.hi {M M' : Word → BitVec 8} (E : ISOEnv M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x)
    (ho : feW M' (BitVec.ofNat 32 edOneAddress) = feW M (BitVec.ofNat 32 edOneAddress)) : ISOEnv M' :=
  ⟨E.cod.hi h (by decide) (by decide), E.mcs.hi h (by decide) (by decide), E.mcb.hi h (by decide) (by decide),
    E.mset.hi h (by decide) (by decide), E.dbl.hi h (by decide) (by decide), E.sq.hi h (by decide) (by decide),
    E.sqi.hi h (by decide) (by decide), E.red.hi h (by decide) (by decide), E.add.hi h (by decide) (by decide),
    E.sub.hi h (by decide) (by decide), E.ap.hi h (by decide) (by decide), E.ax.hi h (by decide) (by decide),
    E.mul.hi h (by decide) (by decide), E.ce.hi h (by decide) (by decide), E.tb.hi h (by decide) (by decide),
    E.cs.hi h (by decide) (by decide), E.cu.hi h (by decide) (by decide), E.bb.hi h (by decide) (by decide),
    ho.trans E.one⟩

/-- The code `ed25519_public_key_ok` runs and its callees', with the field
elements they read. -/
structure PkEnv (M : Word → BitVec 8) : Prop where
  dec : DecEnv M
  iso : ISOEnv M
  vkb : CodeIn M VKB edVerifyingKeyFromBytesCode
  pko : CodeIn M PKO ed25519PublicKeyOkCode
  ltl : CodeIn M (BitVec.ofNat 32 lessThanLeAddress) lessThanLeCode
  aeq : CodeIn M (BitVec.ofNat 32 arr32EqCryptoAddress) arr32EqCryptoCode
  mcmp : CodeIn M (BitVec.ofNat 32 arr32EqCryptoAddress + 0x11896) memcmpCode

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- From offset 0x42: `VerifyingKey::from_bytes`, and for a point,
`is_small_order`, to offset 0x9C with `a0` holding `pkRes`. -/
theorem pk_from {M0 Ms G pk r0 M n} (E : PkEnv M0) (D : PkSt M0 Ms G pk r0 M n 0x42) (hG4 : G.toNat % 4 = 0)
    (hGw : G.toNat + 0x940 ≤ 0x40000000) (hpw : pk.toNat + 32 < 2 ^ 32) (sP : Sep pk 32 G 0x940)
    (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 G 0x940) (sD : Sep (BitVec.ofNat 32 edDAddress) 40 G 0x940)
    (sS : Sep (BitVec.ofNat 32 edSqrtM1Address) 40 G 0x940) :
    ∃ n' M', Steps n n' ∧ PkSt M0 Ms G pk r0 M' n' 0x9C ∧
      reg n' a0 = (if pkRes (decSpec (feW M0 (BitVec.ofNat 32 edOneAddress)) (feW M0 (BitVec.ofNat 32 edDAddress))
        (feW M0 (BitVec.ofNat 32 edSqrtM1Address)) (memBytes M0 pk 32)) then 1 else 0) := by
  have s := D.st
  have hGc : ∀ c, c ≤ 0x940 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x940 → d + k ≤ 0x940 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have inG : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x940 → Sep G 0x940 x 1 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => (hx.symm.subR h).symm
  have hiG : ∀ {c l : Nat} {b : Word} {k : Nat}, c + l ≤ 0x940 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l b k := fun h h1 h2 => sep_of_le (by rw [hGc _ (by omega)]; omega) h2
  have codeG : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep G 0x940 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have sub0 : ∀ {c : Word} {k : Nat}, Sep c k G 0x940 → ∀ l, l ≤ 0x940 → Sep c k G l := fun h l hl => by
    have := h.subR (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this
  have hiM : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => D.agree x (codeG x hx)
  have hc : CodeIn M PKO ed25519PublicKeyOkCode := E.pko.hi hiM (by decide) (by decide)
  have cst : ∀ {c : Word}, Sep c 40 G 0x940 → feW M c = feW M0 c := fun h =>
    feW_frame fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact D.agree _ (h.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have hbp : memBytes M pk 32 = memBytes M0 pk 32 :=
    memBytes_congr fun i hi => D.agree _ (sP.sub (c := i) (l := 1) hi).symm
  obtain ⟨n1, d1, u1⟩ := s.alu hc pko_at_42 (off' := 0x44) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.alu hc pko_at_44 (off' := 0x46) (by decide)
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa (cb := VKB) hc pko_at_46 pko_at_4a (by decide) (by decide)
  have r3 := PEnv.reg1 regs3 u2.self.zero
  have r2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q h0 h1 => by
    rw [u2.upd_ne u1.self.zero q h1, u1.upd_ne s.zero q h0]
  have eG : G + BitVec.ofNat 32 0x7B0 + 0xFFFFF850 = G := by rw [BitVec.add_assoc]; exact BitVec.add_zero G
  obtain ⟨n4, c4, pc4, sp4, k4, vk4, fr4⟩ := edVkFromBytes_correct n3
    (E.dec.hi fun x hx => by rw [mem3]; exact hiM x hx) (E.vkb.hi (fun x hx => by rw [mem3]; exact hiM x hx)
      (by decide) (by decide)) pc3
    (by rw [r3 _ (by decide), u2.upd_ne u1.self.zero _ (by decide), u1.upd_eq (by decide), s.zero, D.hsp]
        exact BitVec.zero_add _)
    (by rw [r3 _ (by decide), u2.upd_eq (by decide), u1.upd_ne s.zero _ (by decide), u1.upd_ne s.zero _ (by decide),
        s.zero, D.hs0]; exact BitVec.zero_add _)
    (by rw [regs3]; simp +decide [upd]) (even_clear _ (even_at PKO (by decide) (0x46 + 8) (by decide)))
    (by rw [r3 _ (by decide), r2 _ (by decide) (by decide), D.hsp]) (aligned_add hG4 (by decide))
    (by rw [hGc _ (by decide)]; omega) (by rw [hGc _ (by decide)]; omega) (aligned_add hG4 (by decide))
    (by rw [hGc _ (by decide)]; omega) hpw
    (by rw [eG]; have := offs (c := 0x7B0) (n := 0xC4) (d := 0) (k := 0x7B0) (Or.inr (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this)
    (by rw [eG]; exact sub0 sP _ (by decide)) (sP.subR (by decide))
    (by rw [eG]; exact sub0 sO _ (by decide)) (by rw [eG]; exact sub0 sD _ (by decide))
    (by rw [eG]; exact sub0 sS _ (by decide))
  rw [mem3, eG] at fr4
  rw [mem3, hbp, cst sO, cst sD, cst sS] at vk4
  have I4 : ∀ x, Sep G 0x940 x 1 → n4.mem x = M0 x := fun x hx => by
    rw [fr4 x (by have := hx.sub (c := 0) (l := 0x7B0) (by decide); rwa [add_ofNat_zero] at this)
      (inG (by decide) hx), D.agree x hx]
  have S4 : ∀ c, 0x934 ≤ c → c < 0x940 → n4.mem (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [fr4 _ (by have := offs (c := 0) (n := 0x7B0) (d := c) (k := 1) (Or.inl (by omega)) (by decide) (by omega)
                  rwa [add_ofNat_zero] at this) (offs (Or.inl (by omega)) (by decide) (by omega)),
      D.slots c h1 h2]
  have hc4 : CodeIn n4.mem PKO ed25519PublicKeyOkCode := E.pko.hi (fun x hx => I4 x (codeG x hx)) (by decide) (by decide)
  have u4 : St n4.mem PKO n4 0x4E (reg n4) := ⟨by rw [pc4], rfl, fun _ => rfl⟩
  have k4' : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [k4 q (by revert hq; revert q; decide), r3 q (by revert hq; revert q; decide),
      r2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have sp4' : reg n4 sp = G + BitVec.ofNat 32 0x7B0 := sp4
  obtain ⟨n5, d5, u5⟩ := u4.lw hc4 pko_at_4e (off' := 0x50) (by decide) (by rw [sp4', add_lit_zero]; exact aligned_add hG4 (by decide))
  have a0_5 : reg n5 a0 = memLoad32 n4.mem (G + BitVec.ofNat 32 0x7B0) := by rw [u5.upd_eq (by decide), sp4', add_lit_zero]
  have r5 : ∀ q, q ≠ a0 → reg n5 q = reg n4 q := fun q h => u5.upd_ne u4.zero q h
  generalize decSpec (feW M0 (BitVec.ofNat 32 edOneAddress)) (feW M0 (BitVec.ofNat 32 edDAddress))
    (feW M0 (BitVec.ofNat 32 edSqrtM1Address)) (memBytes M0 pk 32) = Dv at vk4 ⊢
  cases Dv with
  | none =>
    obtain ⟨n6, d6, u6⟩ := u5.self.taken hc4 0x9A pko_at_50 (by decide)
      (by rw [a0_5, show memLoad32 n4.mem (G + BitVec.ofNat 32 0x7B0) = 1 from vk4, u5.self.zero]; decide)
    obtain ⟨n7, d7, u7⟩ := u6.aluImm hc4 pko_at_9a (off' := 0x9C) (by decide)
    refine ⟨n7, n4.mem, c3.trans (c4.trans (.cons d5 (.cons d6 (.single d7)))) |> fun h => .cons d1 (.cons d2 h),
      ⟨u7.self, ?_, ?_, fun q hq => ?_, I4, S4⟩, ?_⟩
    · rw [u7.upd_ne u6.zero _ (by decide), r5 _ (by decide), sp4']
    · rw [u7.upd_ne u6.zero _ (by decide), r5 _ (by decide), k4' _ (by decide), D.hs0]
    · rw [u7.upd_ne u6.zero _ (by revert hq; revert q; decide), r5 _ (by revert hq; revert q; decide),
        k4' q (by revert hq; revert q; decide), D.keep q hq]
    · rw [u7.upd_eq (by decide), u6.zero]; rfl
  | some P =>
    obtain ⟨X, Y, Z, T⟩ := P
    obtain ⟨tag, -, hX, hY, hZ, -⟩ := vk4
    obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc4 0x52 pko_at_50 (by decide)
      (by rw [a0_5, show memLoad32 n4.mem (G + BitVec.ofNat 32 0x7B0) = 0 from tag, u5.self.zero]; decide)
    obtain ⟨n7, d7, u7⟩ := u6.aluImm hc4 pko_at_52 (off' := 0x54) (by decide)
    obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc4 pko_at_54 (off' := 0x56) (by decide)
    obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hc4 pko_at_56 (off' := 0x5A) (by decide)
    have r9 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n9 q = reg n4 q := fun q h0 h1 h2 => by
      rw [u9.upd_ne u8.self.zero q h2, u8.upd_ne u7.self.zero q h0, u7.upd_ne u6.zero q h1, r5 q h0]
    have sp9 : reg n9 sp = G + BitVec.ofNat 32 0x7B0 := by rw [r9 _ (by decide) (by decide) (by decide), sp4']
    obtain ⟨n10, c10, pc10, mem10, regs10⟩ := u9.self.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc4 pko_at_5a
      pko_at_5e (by decide) (by decide)
    have r10 := PEnv.reg1 regs10 u9.self.zero
    have eFp : G + BitVec.ofNat 32 0x7B0 + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x7A0 := by rw [BitVec.add_assoc]; rfl
    have hst : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = (img% memcpyBodyAddress) := by decide
    obtain ⟨n11, c11, pc11, sp11, _, f11, k11⟩ := memcpy_correct n10 (BitVec.ofNat 32 memcpyStubAddress)
      (PKO + BitVec.ofNat 32 (0x5A + 8)) (G + BitVec.ofNat 32 0x874) (G + BitVec.ofNat 32 0x7B4) 0xC0
      (fun i hi => by rw [mem10]; exact E.iso.mcs.hi (fun x hx => I4 x (codeG x hx)) (by decide) (by decide) i hi)
      (by decide) pc10
      (by rw [r10 _ (by decide), u9.upd_ne u8.self.zero _ (by decide), u8.upd_eq (by decide),
        u7.upd_ne u6.zero _ (by decide), r5 _ (by decide), sp4']; exact add_sp G rfl)
      (by rw [r10 _ (by decide), u9.upd_ne u8.self.zero _ (by decide), u8.upd_ne u7.self.zero _ (by decide),
        u7.upd_eq (by decide), r5 _ (by decide), sp4']; exact add_sp G rfl)
      (by rw [r10 _ (by decide), u9.upd_eq (by decide), u8.self.zero]; rfl)
      (by rw [regs10]; simp +decide [upd]) (even_clear _ (even_at PKO (by decide) (0x5A + 8) (by decide)))
      (by
        rw [mem10, r10 _ (by decide), sp9, eFp]
        exact { code := E.iso.mcb.hi (fun x hx => I4 x (codeG x hx)) (by decide) (by decide)
                hDC := hiG (by decide) (by decide) (by decide)
                hFC := hiG (by decide) (by decide) (by decide)
                hdF := offs (Or.inr (by decide)) (by decide) (by decide)
                hsF := offs (Or.inr (by decide)) (by decide) (by decide)
                hsep := offs (Or.inr (by decide)) (by decide) (by decide)
                hF := aligned_add hG4 (by decide)
                hFw := by rw [hGc _ (by decide)]; omega
                hdw := by rw [hGc _ (by decide)]; omega
                hsw := by rw [hGc _ (by decide)]; omega })
    rw [mem10, r10 _ (by decide), sp9, eFp] at f11
    have I11 : ∀ x, Sep G 0x940 x 1 → n11.mem x = M0 x := fun x hx => by
      rw [f11 x (inG (by decide) hx), copyBytes_sep (inG (by decide) hx) (Nat.le_refl _), I4 x hx]
    have S11 : ∀ c, 0x934 ≤ c → c < 0x940 → n11.mem (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => by
        rw [f11 _ (offs (Or.inl (by omega)) (by decide) (by omega)),
          copyBytes_sep (offs (Or.inl (by omega)) (by decide) (by omega)) (Nat.le_refl _), S4 c h1 h2]
    have W11 : ∀ c, 0x874 ≤ c → c + 40 ≤ 0x934 →
        feW n11.mem (G + BitVec.ofNat 32 c) = feW n4.mem (G + BitVec.ofNat 32 (c - 0xC0)) := fun c h1 h2 =>
      feW_eq2 fun i hi => vk_ld2 fun j hj => by
        have e1 : G + BitVec.ofNat 32 c + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j =
            G + BitVec.ofNat 32 0x874 + BitVec.ofNat 32 (c - 0x874 + 4 * i + j) := by
          simp only [spk]; exact congrArg (fun k => G + BitVec.ofNat 32 k) (by omega)
        have e2 : G + BitVec.ofNat 32 (c - 0xC0) + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j =
            G + BitVec.ofNat 32 0x7B4 + BitVec.ofNat 32 (c - 0x874 + 4 * i + j) := by
          simp only [spk]; exact congrArg (fun k => G + BitVec.ofNat 32 k) (by omega)
        rw [e1, e2, f11 _ (by rw [spk]; exact offs (Or.inl (by omega)) (by decide) (by omega)), cb_in (by omega) (by decide)]
    have hc11 : CodeIn n11.mem PKO ed25519PublicKeyOkCode := E.pko.hi (fun x hx => I11 x (codeG x hx)) (by decide) (by decide)
    have u11 : St n11.mem PKO n11 0x62 (reg n11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
    have k11' : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n11 q = reg n4 q :=
      fun q hq => by
        rw [k11 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide), r10 q (by revert hq; revert q; decide),
          r9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    have sp11' : reg n11 sp = G + BitVec.ofNat 32 0x7B0 := by rw [sp11, r10 _ (by decide), sp9]
    obtain ⟨n12, d12, u12⟩ := u11.aluImm hc11 pko_at_62 (off' := 0x64) (by decide)
    obtain ⟨n13, c13, pc13, mem13, regs13⟩ := u12.self.callRa (cb := ISO) hc11 pko_at_64 pko_at_68 (by decide) (by decide)
    have r13 := PEnv.reg1 regs13 u12.self.zero
    have eI : G + BitVec.ofNat 32 0x7B0 + 0xFFFFFB30 = G + BitVec.ofNat 32 0x2E0 := by rw [BitVec.add_assoc]; rfl
    have one11 : feW n11.mem (BitVec.ofNat 32 edOneAddress) = feW M0 (BitVec.ofNat 32 edOneAddress) :=
      feW_frame fun i hi => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact I11 _ (sO.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    obtain ⟨n14, c14, pc14, sp14, k14, a14, fr14⟩ := isSmallOrder_correct n13
      (E.iso.hi (fun x hx => by rw [mem13]; exact I11 x (codeG x hx)) (by rw [mem13]; exact one11)) pc13
      (by rw [r13 _ (by decide), u12.upd_eq (by decide), sp11']; exact add_sp G rfl)
      (by rw [regs13]; simp +decide [upd]) (even_clear _ (even_at PKO (by decide) (0x64 + 8) (by decide)))
      (by rw [r13 _ (by decide), u12.upd_ne u11.zero _ (by decide), sp11']) (aligned_add hG4 (by decide))
      (by rw [hGc _ (by decide)]; omega) (by rw [hGc _ (by decide)]; omega) (aligned_add hG4 (by decide))
      (by rw [eI]; exact offs (Or.inr (by decide)) (by decide) (by decide))
      (by rw [eI]; exact sO.subR (by decide))
    rw [mem13, eI] at fr14
    rw [mem13] at a14
    have hX' : feW n4.mem (G + BitVec.ofNat 32 0x7D4) = X := by rw [← hX, spk]
    have hY' : feW n4.mem (G + BitVec.ofNat 32 0x7FC) = Y := by rw [← hY, spk]
    have hZ' : feW n4.mem (G + BitVec.ofNat 32 0x824) = Z := by rw [← hZ, spk]
    rw [show G + BitVec.ofNat 32 0x894 + (0x28 : Word) = G + BitVec.ofNat 32 0x8BC from add_ofNat_assoc G 0x894 0x28,
      show G + BitVec.ofNat 32 0x894 + (0x50 : Word) = G + BitVec.ofNat 32 0x8E4 from add_ofNat_assoc G 0x894 0x50,
      W11 _ (by decide) (by decide), W11 _ (by decide) (by decide), W11 _ (by decide) (by decide)] at a14
    rw [show 0x894 - 0xC0 = 0x7D4 from rfl, show 0x8BC - 0xC0 = 0x7FC from rfl, show 0x8E4 - 0xC0 = 0x824 from rfl,
      hX', hY', hZ'] at a14
    have I14 : ∀ x, Sep G 0x940 x 1 → n14.mem x = M0 x := fun x hx => by rw [fr14 x (inG (by decide) hx), I11 x hx]
    have hc14 : CodeIn n14.mem PKO ed25519PublicKeyOkCode := E.pko.hi (fun x hx => I14 x (codeG x hx)) (by decide) (by decide)
    have u14 : St n14.mem PKO n14 0x6C (reg n14) := ⟨by rw [pc14], rfl, fun _ => rfl⟩
    obtain ⟨n15, d15, u15⟩ := u14.aluImm hc14 pko_at_6c (off' := 0x70) (by decide)
    obtain ⟨n16, d16, u16⟩ := u15.self.jump hc14 pko_at_70 (off' := 0x9C) (by decide) (by rw [u15.self.pc]; decide)
    have k14' : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n16 q = reg n q :=
      fun q hq => by
        rw [u16.regs, u15.upd_ne u14.zero q (by revert hq; revert q; decide), k14 q (by revert hq; revert q; decide),
          r13 q (by revert hq; revert q; decide), u12.upd_ne u11.zero q (by revert hq; revert q; decide), k11' q hq,
          k4' q hq]
    refine ⟨n16, n14.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (c10.trans (c11.trans (.cons d12 (c13.trans (c14.trans (.cons d15 (.single d16))))))))))))))),
      ⟨u16.self, ?_, ?_, fun q hq => ?_, I14, fun c h1 h2 => ?_⟩, ?_⟩
    · rw [u16.regs, u15.upd_ne u14.zero _ (by decide), sp14]
    · rw [k14' _ (by decide), D.hs0]
    · rw [k14' q (by revert hq; revert q; decide), D.keep q hq]
    · rw [fr14 _ (offs (Or.inl (by omega)) (by decide) (by omega)), S11 c h1 h2]
    · rw [u16.regs, u15.upd_eq (by decide), a14]
      show aluEval .xor (if isoSpec X Y Z then 1 else 0) 1 = if !isoSpec X Y Z then 1 else 0
      cases isoSpec X Y Z <;> rfl

theorem st8_frame {M : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : Sep a 1 x 1) : memStore8 M a v x = M x := by
  have ne : ¬ x = a := fun e => h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])
  simp only [memStore8, ne, ↓reduceIte]

theorem sb_clear : ∀ x : BitVec 8, (aluEval .and (x.signExtend 32) 0x7F).extractLsb' 0 8 = BitVec.ofNat 8 (x.toNat % 128) := by
  decide

theorem blt_sign : ∀ x : BitVec 8, branchTaken .blt (x.signExtend 32) 0 = decide (128 ≤ x.toNat) := by decide

theorem memBytes_set (M : Word → BitVec 8) (p : Word) (v : BitVec 8) {k n : Nat} (hk : k < n) (hn : n ≤ 2 ^ 32) :
    memBytes (memStore8 M (p + BitVec.ofNat 32 k) v) p n = (memBytes M p n).set k v.toNat := by
  unfold memBytes
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_set, memStore8]
  simp only [List.length_map, List.length_range] at h1
  by_cases e : k = i
  · subst e; simp
  · have : p + BitVec.ofNat 32 i ≠ p + BitVec.ofNat 32 k := fun h => by
      have h' := congrArg (fun w => w - p) h
      simp only [BitVec.add_comm p, BitVec.add_sub_cancel] at h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact e this.symm
    simp [e, this]

set_option maxRecDepth 20000 in
/-- From offset 0x9C: the epilogue, with the slots holding `rM`'s `ra`,
`s0`, and `s1`. -/
theorem pk_fin {M0 Ms G pk r0 M n} {rM : Fin 32 → Word} (E : PkEnv M0) (D : PkSt M0 Ms G pk r0 M n 0x9C)
    (hG4 : G.toNat % 4 = 0) (hGw : G.toNat + 0x940 ≤ 0x40000000)
    (hsl : memLoad32 Ms (G + BitVec.ofNat 32 0x93C) = rM ra ∧ memLoad32 Ms (G + BitVec.ofNat 32 0x938) = rM 8 ∧
      memLoad32 Ms (G + BitVec.ofNat 32 0x934) = rM 9) (hret : rM ra &&& ~~~1 = rM ra) :
    ∃ m', Steps n m' ∧ m'.pc = rM ra ∧ reg m' sp = G + BitVec.ofNat 32 0x940 ∧ reg m' a0 = reg n a0 ∧
      reg m' ra = rM ra ∧ reg m' (8 : Fin 32) = rM 8 ∧ reg m' (9 : Fin 32) = rM 9 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = r0 q) ∧
      ∀ x, Sep G 0x940 x 1 → m'.mem x = M0 x := by
  have hc : CodeIn M PKO ed25519PublicKeyOkCode := E.pko.hi (fun x hx => D.agree x
    (sep_of_le (by omega) (by have := x.isLt; omega))) (by decide) (by decide)
  obtain ⟨m', c', pc', sp', a0', ra', s0', s1', kp', mem'⟩ := pk_tail D hc hG4
  obtain ⟨h1, h2, h3⟩ := hsl
  exact ⟨m', c', by rw [pc', h1, hret], sp', a0', by rw [ra', h1], by rw [s0', h2], by rw [s1', h3], kp',
    fun x hx => by rw [mem', D.agree x hx]⟩

section
variable {P E1 E2 one d sm : List Nat} {b : Bytes}

theorem pkOk_ltF (h : ltLEb (clearTop b) P 32 = false) : pkOkSpec P E1 E2 one d sm b = false := by
  unfold pkOkSpec; rw [h]; rfl

theorem pkOk_sgnF (h1 : ltLEb (clearTop b) P 32 = true) (h2 : decide (128 ≤ b.getD 31 0) = false) :
    pkOkSpec P E1 E2 one d sm b = pkRes (decSpec one d sm b) := by
  unfold pkOkSpec; rw [h1, h2]; simp only [Bool.false_and, Bool.not_false, Bool.true_and]

theorem pkOk_e1 (h1 : ltLEb (clearTop b) P 32 = true) (h2 : decide (128 ≤ b.getD 31 0) = true)
    (h3 : decide (clearTop b = E1) = true) : pkOkSpec P E1 E2 one d sm b = false := by
  unfold pkOkSpec; rw [h1, h2, h3]; rfl

theorem pkOk_e2 (h1 : ltLEb (clearTop b) P 32 = true) (h2 : decide (128 ≤ b.getD 31 0) = true)
    (h3 : decide (clearTop b = E1) = false) (h4 : decide (clearTop b = E2) = true) :
    pkOkSpec P E1 E2 one d sm b = false := by
  unfold pkOkSpec; rw [h1, h2, h3, h4]; rfl

theorem pkOk_e0 (h1 : ltLEb (clearTop b) P 32 = true) (h2 : decide (128 ≤ b.getD 31 0) = true)
    (h3 : decide (clearTop b = E1) = false) (h4 : decide (clearTop b = E2) = false) :
    pkOkSpec P E1 E2 one d sm b = pkRes (decSpec one d sm b) := by
  unfold pkOkSpec; rw [h1, h2, h3, h4]; simp only [Bool.or_self, Bool.and_false, Bool.not_false, Bool.true_and]

end

/-- The registers the prologue saves, at their offsets from `sp + 0x180`. -/
abbrev pkPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0xC), ((8 : Fin 32), BitVec.ofNat 32 8), ((9 : Fin 32), BitVec.ofNat 32 4)]

set_option maxRecDepth 20000 in
theorem pkSave_end : blockEnd ed25519PublicKeyOkCode 0x4 (saveBlockR a1 pkPs) = some 0xC := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **The compiled `c3_crypto::ed25519_public_key_ok`.** For the 32 key
bytes at `pk` it returns `pkOkSpec` of them in `a0`, with `p` and the two
encodings with `x = 0` as the image holds them at `edPrimeAddress`,
`p256OneAddress`, and `edPm1Address`. It returns with `sp` and the callee-saved
registers restored and writes nothing outside the 0x940 bytes of stack
below `sp`. -/
theorem pkOk_correct (m : Machine) {sp0 pk retAddr : Word} (E : PkEnv m.mem) (hpc : m.pc = PKO)
    (ha0 : reg m a0 = pk) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x940 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000) (hpw : pk.toNat + 32 < 2 ^ 32)
    (sP : Sep pk 32 (sp0 + 0xFFFFF6C0) 0x940)
    (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 (sp0 + 0xFFFFF6C0) 0x940)
    (sD : Sep (BitVec.ofNat 32 edDAddress) 40 (sp0 + 0xFFFFF6C0) 0x940)
    (sS : Sep (BitVec.ofNat 32 edSqrtM1Address) 40 (sp0 + 0xFFFFF6C0) 0x940)
    (sPc : Sep (BitVec.ofNat 32 (img% edPrimeAddress)) 32 (sp0 + 0xFFFFF6C0) 0x940)
    (sE1 : Sep (BitVec.ofNat 32 (img% p256OneAddress)) 32 (sp0 + 0xFFFFF6C0) 0x940)
    (sE2 : Sep (BitVec.ofNat 32 (img% edPm1Address)) 32 (sp0 + 0xFFFFF6C0) 0x940) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      reg m' a0 = (if pkOkSpec (memBytes m.mem (BitVec.ofNat 32 (img% edPrimeAddress)) 32)
        (memBytes m.mem (BitVec.ofNat 32 (img% p256OneAddress)) 32) (memBytes m.mem (BitVec.ofNat 32 (img% edPm1Address)) 32)
        (feW m.mem (BitVec.ofNat 32 edOneAddress)) (feW m.mem (BitVec.ofNat 32 edDAddress))
        (feW m.mem (BitVec.ofNat 32 edSqrtM1Address)) (memBytes m.mem pk 32) then 1 else 0) ∧
      ∀ x, Sep (sp0 + 0xFFFFF6C0) 0x940 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFF6C0 = G := ⟨_, rfl⟩
  rw [hG] at sP sO sD sS sPc sE1 sE2 ⊢
  have hGn : G.toNat = sp0.toNat - 0x940 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFF6C0 : Word).toNat = 2 ^ 32 - 0x940 from rfl]; omega
  have hG4 : G.toNat % 4 = 0 := by omega
  have hGw : G.toNat + 0x940 ≤ 0x40000000 := by omega
  have hGc : ∀ c, c ≤ 0x940 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eF : sp0 + 0xFFFFFE70 = G + BitVec.ofNat 32 0x7B0 := by rw [← hG, BitVec.add_assoc]; rfl
  have eS : G + BitVec.ofNat 32 0x940 = sp0 := by rw [← hG, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x940 → d + k ≤ 0x940 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have inG : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x940 → Sep G 0x940 x 1 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => (hx.symm.subR h).symm
  have hiG : ∀ {c l : Nat} {b : Word} {k : Nat}, c + l ≤ 0x940 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l b k := fun h h1 h2 => sep_of_le (by rw [hGc _ (by omega)]; omega) h2
  have codeG : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep G 0x940 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hc := E.pko
  have st0 : St m.mem PKO m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc pko_at_0 (off' := 2) (by decide)
  have sp1 : reg m1 sp = G + BitVec.ofNat 32 0x7B0 := by rw [u1.upd_eq (by decide), hsp]; exact eF
  obtain ⟨m2, d2, u2⟩ := u1.self.aluImm hc pko_at_2 (off' := 4) (by decide)
  have a1_2 : reg m2 a1 = G + BitVec.ofNat 32 0x930 := by rw [u2.upd_eq (by decide), sp1]; exact add_sp G rfl
  have r2 : ∀ q, q ≠ sp → q ≠ a1 → reg m2 q = reg m q := fun q h1 h2 => by
    rw [u2.upd_ne u1.self.zero q h2, u1.upd_ne hz q h1]
  obtain ⟨m3, c3, u3⟩ := St.block (saveBlockR a1 pkPs) u2.self hc pkSave_end (saveBlockR_ok a1 _ pkPs _ fun p hp => by
    rw [a1_2]
    simp only [pkPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact ⟨by rw [add_ofNat_assoc]; exact aligned_add hG4 (by decide),
        by rw [add_ofNat_assoc]; exact hiG (by decide) (by decide) (by decide)⟩)
  rw [saveBlockR_run, a1_2] at u3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (G + BitVec.ofNat 32 0x930) (reg m2) pkPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u3
  dsimp only at u3
  have IMs : ∀ x, Sep G 0x940 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]
    exact saveMem_outside pkPs fun p hp => by
      simp only [pkPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> (rw [add_ofNat_assoc]; exact inG (by decide) hx)
  have slots : memLoad32 Ms (G + BitVec.ofNat 32 0x93C) = reg m ra ∧ memLoad32 Ms (G + BitVec.ofNat 32 0x938) = reg m 8 ∧
      memLoad32 Ms (G + BitVec.ofNat 32 0x934) = reg m 9 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hMs, show G + BitVec.ofNat 32 0x93C = G + BitVec.ofNat 32 0x930 + BitVec.ofNat 32 0xC from (spk G 0x930 0xC).symm,
        saveMem_slot (r := ra) pkPs _ (by decide) (by decide), r2 _ (by decide) (by decide)]
    · rw [← hMs, show G + BitVec.ofNat 32 0x938 = G + BitVec.ofNat 32 0x930 + BitVec.ofNat 32 8 from (spk G 0x930 8).symm,
        saveMem_slot (r := (8 : Fin 32)) pkPs _ (by decide) (by decide), r2 _ (by decide) (by decide)]
    · rw [← hMs, show G + BitVec.ofNat 32 0x934 = G + BitVec.ofNat 32 0x930 + BitVec.ofNat 32 4 from (spk G 0x930 4).symm,
        saveMem_slot (r := (9 : Fin 32)) pkPs _ (by decide) (by decide), r2 _ (by decide) (by decide)]
  have hcS : CodeIn Ms PKO ed25519PublicKeyOkCode := hc.hi (fun x hx => IMs x (codeG x hx)) (by decide) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hcS pko_at_c (off' := 0xE) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.self.alu hcS pko_at_e (off' := 0x10) (by decide)
  obtain ⟨m6, d6, u6⟩ := u5.self.aluImm hcS pko_at_10 (off' := 0x14) (by decide)
  obtain ⟨m7, d7, u7⟩ := u6.self.alu hcS pko_at_14 (off' := 0x16) (by decide)
  have s0_7 : reg m7 (8 : Fin 32) = pk := by
    rw [u7.upd_ne u6.self.zero _ (by decide), u6.upd_ne u5.self.zero _ (by decide), u5.upd_ne u4.self.zero _ (by decide),
      u4.upd_eq (by decide), u2.self.zero, r2 _ (by decide) (by decide), ha0]; exact BitVec.zero_add _
  have r7 : ∀ q, q ≠ (8 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m7 q = reg m2 q := fun q h8 h0 h1 h2 => by
    rw [u7.upd_ne u6.self.zero q h1, u6.upd_ne u5.self.zero q h2, u5.upd_ne u4.self.zero q h0,
      u4.upd_ne u2.self.zero q h8]
  have sp7 : reg m7 sp = G + BitVec.ofNat 32 0x7B0 := by
    rw [r7 _ (by decide) (by decide) (by decide) (by decide), u2.upd_ne u1.self.zero _ (by decide), sp1]
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := u7.self.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hcS pko_at_16
    pko_at_1a (by decide) (by decide)
  have r8 := PEnv.reg1 regs8 u7.self.zero
  have eFp : G + BitVec.ofNat 32 0x7B0 + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x7A0 := by rw [BitVec.add_assoc]; rfl
  have hst : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = (img% memcpyBodyAddress) := by decide
  have hiS : ∀ x : Word, 0x40000000 ≤ x.toNat → Ms x = m.mem x := fun x hx => IMs x (codeG x hx)
  obtain ⟨m9, c9, pc9, sp9, _, f9, k9⟩ := memcpy_correct m8 (BitVec.ofNat 32 memcpyStubAddress)
    (PKO + BitVec.ofNat 32 (0x16 + 8)) (G + BitVec.ofNat 32 0x7B0) pk 32
    (fun i hi => by rw [mem8]; exact E.iso.mcs.hi hiS (by decide) (by decide) i hi) (by decide) pc8
    (by rw [r8 _ (by decide), u7.upd_ne u6.self.zero _ (by decide), u6.upd_ne u5.self.zero _ (by decide),
      u5.upd_eq (by decide), u4.self.zero, u4.upd_ne u2.self.zero _ (by decide), u2.upd_ne u1.self.zero _ (by decide), sp1]
        exact BitVec.zero_add _)
    (by rw [r8 _ (by decide), u7.upd_eq (by decide), u6.self.zero, u6.upd_ne u5.self.zero _ (by decide),
      u5.upd_ne u4.self.zero _ (by decide), u4.upd_eq (by decide), u2.self.zero, r2 _ (by decide) (by decide), ha0]
        show (0 : Word) + (0 + pk) = pk
        exact (BitVec.zero_add _).trans (BitVec.zero_add _))
    (by rw [r8 _ (by decide), u7.upd_ne u6.self.zero _ (by decide), u6.upd_eq (by decide), u5.self.zero]; rfl)
    (by rw [regs8]; simp +decide [upd]) (even_clear _ (even_at PKO (by decide) (0x16 + 8) (by decide)))
    (by
      rw [mem8, r8 _ (by decide), sp7, eFp]
      exact { code := E.iso.mcb.hi hiS (by decide) (by decide)
              hDC := hiG (by decide) (by decide) (by decide)
              hFC := hiG (by decide) (by decide) (by decide)
              hdF := offs (Or.inr (by decide)) (by decide) (by decide)
              hsF := sP.subR (by decide)
              hsep := (sP.subR (c := 0x7B0) (l := 32) (by decide)).symm
              hF := aligned_add hG4 (by decide)
              hFw := by rw [hGc _ (by decide)]; omega
              hdw := by rw [hGc _ (by decide)]; omega
              hsw := hpw })
  rw [mem8, r8 _ (by decide), sp7, eFp] at f9
  have I9 : ∀ x, Sep G 0x940 x 1 → m9.mem x = m.mem x := fun x hx => by
    rw [f9 x (inG (by decide) hx), copyBytes_sep (inG (by decide) hx) (Nat.le_refl _), IMs x hx]
  have cp9 : ∀ i, i < 32 → m9.mem (G + BitVec.ofNat 32 0x7B0 + BitVec.ofNat 32 i) = m.mem (pk + BitVec.ofNat 32 i) :=
    fun i hi => by
      rw [f9 _ (by rw [spk]; exact offs (Or.inl (by omega)) (by decide) (by omega)), cb_in hi (by decide),
        IMs _ (sP.sub (c := i) (l := 1) hi).symm]
  have hc9 : CodeIn m9.mem PKO ed25519PublicKeyOkCode := hc.hi (fun x hx => I9 x (codeG x hx)) (by decide) (by decide)
  have u9 : St m9.mem PKO m9 0x1E (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
  have k9' : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m9 q = reg m7 q :=
    fun q hq => by
      rw [k9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r8 q (by revert hq; revert q; decide)]
  have sp9' : reg m9 sp = G + BitVec.ofNat 32 0x7B0 := by rw [sp9, r8 _ (by decide), sp7]
  obtain ⟨m10, d10, u10⟩ := u9.lb hc9 pko_at_1e (off' := 0x22) (by decide)
  have x31 : m9.mem (reg m9 sp + 0x1F) = m.mem (pk + BitVec.ofNat 32 31) := by
    rw [sp9']; exact cp9 31 (by decide)
  obtain ⟨m11, d11, u11⟩ := u10.self.aluImm hc9 pko_at_22 (off' := 0x26) (by decide)
  obtain ⟨m12, d12, u12⟩ := u11.self.sb hc9 pko_at_26 (off' := 0x2A) (by decide)
  have s1_11 : reg m11 (9 : Fin 32) = (m.mem (pk + BitVec.ofNat 32 31)).signExtend 32 := by
    rw [u11.upd_ne u10.self.zero _ (by decide), u10.upd_eq (by decide), x31]
  have a0_11 : (reg m11 a0).extractLsb' 0 8 = BitVec.ofNat 8 ((m.mem (pk + BitVec.ofNat 32 31)).toNat % 128) := by
    rw [u11.upd_eq (by decide), u10.upd_eq (by decide), x31]; exact sb_clear _
  have sp11 : reg m11 sp = G + BitVec.ofNat 32 0x7B0 := by
    rw [u11.upd_ne u10.self.zero _ (by decide), u10.upd_ne u9.zero _ (by decide), sp9']
  rw [sp11, a0_11] at u12
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore8 m9.mem (G + BitVec.ofNat 32 0x7B0 + 0x1F)
      (BitVec.ofNat 8 ((m.mem (pk + BitVec.ofNat 32 31)).toNat % 128)) = M2 := ⟨_, rfl⟩
  rw [hM2] at u12
  have I2 : ∀ x, Sep G 0x940 x 1 → M2 x = m.mem x := fun x hx => by
    have h := inG (c := 0x7B0 + 0x1F) (l := 1) (by decide) hx
    rw [← spk] at h
    rw [← hM2]; exact (st8_frame h).trans (I9 x hx)
  have S2 : ∀ c, 0x934 ≤ c → c < 0x940 → M2 (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
    have h := offs (c := 0x7B0 + 0x1F) (n := 1) (d := c) (k := 1) (Or.inl (by omega)) (by decide) (by omega)
    rw [← spk] at h
    rw [← hM2]
    refine (st8_frame h).trans ?_
    rw [f9 _ (offs (Or.inl (by omega)) (by decide) (by omega)),
      copyBytes_sep (offs (Or.inl (by omega)) (by decide) (by omega)) (Nat.le_refl _)]
  have yB : memBytes M2 (G + BitVec.ofNat 32 0x7B0) 32 = clearTop (memBytes m.mem pk 32) := by
    rw [← hM2]
    show memBytes (memStore8 m9.mem (G + BitVec.ofNat 32 0x7B0 + BitVec.ofNat 32 31) _) _ 32 = _
    rw [memBytes_set _ _ _ (by decide) (by decide)]
    have e : memBytes m9.mem (G + BitVec.ofNat 32 0x7B0) 32 = memBytes m.mem pk 32 := by
      unfold memBytes; exact List.map_congr_left fun i hi => by rw [cp9 i (List.mem_range.mp hi)]
    rw [e]
    unfold clearTop
    rw [getD_memBytes _ _ (by decide : 31 < 32), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have I2b : ∀ {c : Word}, Sep c 32 G 0x940 → memBytes M2 c 32 = memBytes m.mem c 32 := fun h =>
    memBytes_congr fun i hi => I2 _ (h.sub (c := i) (l := 1) hi).symm
  have hc2 : CodeIn M2 PKO ed25519PublicKeyOkCode := hc.hi (fun x hx => I2 x (codeG x hx)) (by decide) (by decide)
  obtain ⟨m13, d13, u13⟩ := u12.lui hc2 pko_at_2a (off' := 0x2E) (by decide)
  obtain ⟨m14, d14, u14⟩ := u13.self.aluImm hc2 pko_at_2e (off' := 0x32) (by decide)
  obtain ⟨m15, d15, u15⟩ := u14.self.alu hc2 pko_at_32 (off' := 0x34) (by decide)
  have r15 : ∀ q, q ≠ a0 → q ≠ a1 → reg m15 q = reg m11 q := fun q h0 h1 => by
    rw [u15.upd_ne u14.self.zero q h0, u14.upd_ne u13.self.zero q h1, u13.upd_ne u11.self.zero q h1]
  obtain ⟨m16, c16, pc16, mem16, regs16⟩ := u15.self.callRa (cb := BitVec.ofNat 32 lessThanLeAddress) hc2 pko_at_34
    pko_at_38 (by decide) (by decide)
  have r16 := PEnv.reg1 regs16 u15.self.zero
  obtain ⟨m17, c17, pc17, a17, k17, mem17⟩ := lessThanLe_correct m16 (a := G + BitVec.ofNat 32 0x7B0)
    (b := BitVec.ofNat 32 (img% edPrimeAddress))
    (by rw [mem16]; exact E.ltl.hi (fun x hx => I2 x (codeG x hx)) (by decide) (by decide)) pc16
    (by rw [r16 _ (by decide), u15.upd_eq (by decide), u14.self.zero, u14.upd_ne u13.self.zero _ (by decide),
      u13.upd_ne u11.self.zero _ (by decide), sp11]; exact BitVec.zero_add _)
    (by rw [r16 _ (by decide), u15.upd_ne u14.self.zero _ (by decide), u14.upd_eq (by decide), u13.upd_eq (by decide)]; rfl)
    (by rw [regs16]; simp +decide [upd]) (even_clear _ (even_at PKO (by decide) (0x34 + 8) (by decide)))
  rw [mem16, ltLE_bytes (n := 32) _ _ _ 32 (Nat.le_refl _), yB, I2b sPc] at a17
  rw [mem16] at mem17
  have u17 : St M2 PKO m17 0x3C (reg m17) := ⟨by rw [pc17], by rw [mem17], fun _ => rfl⟩
  have k17' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg m17 q = reg m11 q :=
    fun q h0 h1 h2 h3 h4 hr => by rw [k17 q h0 h1 h2 h3 h4, r16 q hr, r15 q h0 h1]
  have r11 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m11 q = reg m q := fun q hq => by
    rw [u11.upd_ne u10.self.zero q (by revert hq; revert q; decide), u10.upd_ne u9.zero q (by revert hq; revert q; decide),
      k9' q (by revert hq; revert q; decide),
      r7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide),
      r2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have D17 : PkSt m.mem Ms G pk (reg m) M2 m17 0x3C :=
    ⟨u17, by rw [k17' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp11],
      by rw [k17' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        u11.upd_ne u10.self.zero _ (by decide), u10.upd_ne u9.zero _ (by decide), k9' _ (by decide), s0_7],
      fun q hq => by
        rw [k17' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r11 q hq],
      I2, S2⟩
  have s1_17 : reg m17 (9 : Fin 32) = (m.mem (pk + BitVec.ofNat 32 31)).signExtend 32 := by
    rw [k17' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_11]
  -- the three ways out
  have endG : ∀ {M : Word → BitVec 8} {n : Machine}, PkSt m.mem Ms G pk (reg m) M n 0x9C →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        reg m' a0 = reg n a0 ∧ ∀ x, Sep G 0x940 x 1 → m'.mem x = m.mem x := fun {M n} D => by
    obtain ⟨m', c', pc', sp', a0', ra', s0', s1', kp', fr'⟩ := pk_fin (rM := reg m) E D hG4 hGw slots (by rw [hra]; exact hret)
    refine ⟨m', c', by rw [pc', hra], by rw [sp', eS], fun q hq => ?_, a0', fr'⟩
    have hq' : q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      revert hq; revert q; decide
    rcases hq' with rfl | rfl | rfl | h
    · exact ra'
    · exact s0'
    · exact s1'
    · exact kp' q h
  have end0 : ∀ {M : Word → BitVec 8} {n : Machine}, PkSt m.mem Ms G pk (reg m) M n 0x9A →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        reg m' a0 = 0 ∧ ∀ x, Sep G 0x940 x 1 → m'.mem x = m.mem x := fun {M n} D => by
    have hcM : CodeIn M PKO ed25519PublicKeyOkCode := hc.hi (fun x hx => D.agree x (codeG x hx)) (by decide) (by decide)
    obtain ⟨n1, e1, v1⟩ := D.st.aluImm hcM pko_at_9a (off' := 0x9C) (by decide)
    have D1 : PkSt m.mem Ms G pk (reg m) M n1 0x9C :=
      ⟨v1.self, by rw [v1.upd_ne D.st.zero _ (by decide), D.hsp], by rw [v1.upd_ne D.st.zero _ (by decide), D.hs0],
        fun q hq => by rw [v1.upd_ne D.st.zero q (by revert hq; revert q; decide), D.keep q hq], D.agree, D.slots⟩
    obtain ⟨m', c', a, b, c, a0', f⟩ := endG D1
    exact ⟨m', .cons e1 c', a, b, c, by rw [a0', v1.upd_eq (by decide), D.st.zero]; rfl, f⟩
  have endF : ∀ {M : Word → BitVec 8} {n : Machine}, PkSt m.mem Ms G pk (reg m) M n 0x42 →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        reg m' a0 = (if pkRes (decSpec (feW m.mem (BitVec.ofNat 32 edOneAddress)) (feW m.mem (BitVec.ofNat 32 edDAddress))
          (feW m.mem (BitVec.ofNat 32 edSqrtM1Address)) (memBytes m.mem pk 32)) then 1 else 0) ∧
        ∀ x, Sep G 0x940 x 1 → m'.mem x = m.mem x := fun {M n} D => by
    obtain ⟨n1, M1, c1, D1, a1⟩ := pk_from E D hG4 hGw hpw sP sO sD sS
    obtain ⟨m', c', a, b, c, a0', f⟩ := endG D1
    exact ⟨m', c1.trans c', a, b, c, by rw [a0', a1], f⟩
  have eA : G + BitVec.ofNat 32 0x7B0 + 0xFFFFFFFC = G + BitVec.ofNat 32 0x7AC := by rw [BitVec.add_assoc]; rfl
  have cB : ∀ {M n off}, PkSt m.mem Ms G pk (reg m) M n off → ∀ {c : Word}, Sep c 32 G 0x940 →
      memBytes M c 32 = memBytes m.mem c 32 := fun {M n off} D {c} h =>
    memBytes_congr fun i hi => D.agree _ (h.sub (c := i) (l := 1) hi).symm
  have hcOf : ∀ {M n off}, PkSt m.mem Ms G pk (reg m) M n off → CodeIn M PKO ed25519PublicKeyOkCode := fun {M n off} D =>
    hc.hi (fun x hx => D.agree x (codeG x hx)) (by decide) (by decide)
  have hy17 : memBytes M2 (G + BitVec.ofNat 32 0x7B0) 32 = clearTop (memBytes m.mem pk 32) := yB
  cases hl : ltLEb (clearTop (memBytes m.mem pk 32)) (memBytes m.mem (BitVec.ofNat 32 (img% edPrimeAddress)) 32) 32 with
  | false =>
    obtain ⟨n1, e1, v1⟩ := D17.st.taken hc2 0x9A pko_at_3c (by decide) (by rw [a17, hl, D17.st.zero]; decide)
    obtain ⟨m', c', a, b, c, a0', f⟩ := end0 (D17.jmp v1)
    refine ⟨m', .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans (c9.trans (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (c16.trans (c17.trans (.cons e1 c'))))))))))))))))), a, b, c, by rw [a0', pkOk_ltF hl]; rfl, f⟩
  | true =>
    obtain ⟨n1, e1, v1⟩ := D17.st.notTaken hc2 0x3E pko_at_3c (by decide) (by rw [a17, hl, D17.st.zero]; decide)
    have D3E := D17.jmp v1
    cases hsg : decide (128 ≤ (m.mem (pk + BitVec.ofNat 32 31)).toNat) with
    | false =>
      obtain ⟨n2, e2, v2⟩ := D3E.st.notTaken hc2 0x42 pko_at_3e (by decide)
        (by rw [v1.regs, s1_17, D3E.st.zero, blt_sign, hsg])
      obtain ⟨m', c', a, b, c, a0', f⟩ := endF (D3E.jmp v2)
      refine ⟨m', .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans (c9.trans (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (c16.trans (c17.trans (.cons e1 (.cons e2 c')))))))))))))))))), a, b, c, ?_, f⟩
      rw [a0', pkOk_sgnF hl (by rw [getD_memBytes _ _ (by decide : 31 < 32)]; exact hsg)]
    | true =>
      obtain ⟨n2, e2, v2⟩ := D3E.st.taken hc2 0x72 pko_at_3e (by decide)
        (by rw [v1.regs, s1_17, D3E.st.zero, blt_sign, hsg])
      have Dx := D3E.jmp v2
      obtain ⟨x_1, x_e1, x_u1⟩ := Dx.st.lui (hcOf Dx) pko_at_72 (off' := 0x76) (by decide)
      obtain ⟨x_2, x_e2, x_u2⟩ := x_u1.self.aluImm (hcOf Dx) pko_at_76 (off' := 0x7A) (by decide)
      obtain ⟨x_3, x_e3, x_u3⟩ := x_u2.self.alu (hcOf Dx) pko_at_7a (off' := 0x7C) (by decide)
      obtain ⟨x_4, x_c4, x_pc4, x_mem4, x_regs4⟩ := x_u3.self.callRa (cb := BitVec.ofNat 32 arr32EqCryptoAddress)
        (hcOf Dx) pko_at_7c pko_at_80 (by decide) (by decide)
      have x_r4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ ra → reg x_4 q = reg n2 q := fun q h0 h1 hr => by
        rw [PEnv.reg1 x_regs4 x_u3.self.zero q hr, x_u3.upd_ne x_u2.self.zero q h0, x_u2.upd_ne x_u1.self.zero q h1,
          x_u1.upd_ne Dx.st.zero q h1]
      have x_sp4 : reg x_4 sp = G + BitVec.ofNat 32 0x7B0 := by
        rw [x_r4 _ (by decide) (by decide) (by decide), Dx.hsp]
      obtain ⟨x_5, x_c5, x_pc5, x_a5, x_k5, x_f5⟩ := arr32EqCrypto_correct x_4 (p := G + BitVec.ofNat 32 0x7B0)
        (q := BitVec.ofNat 32 (img% p256OneAddress)) (by decide)
        (by rw [x_mem4]; exact E.aeq.hi (fun x hx => Dx.agree x (codeG x hx)) (by decide) (by decide))
        (by rw [x_mem4]; exact E.mcmp.hi (fun x hx => Dx.agree x (codeG x hx)) (by decide) (by decide)) x_pc4
        (by rw [PEnv.reg1 x_regs4 x_u3.self.zero _ (by decide), x_u3.upd_eq (by decide), x_u2.self.zero,
          x_u2.upd_ne x_u1.self.zero _ (by decide), x_u1.upd_ne Dx.st.zero _ (by decide), Dx.hsp]
            exact BitVec.zero_add _)
        (by rw [PEnv.reg1 x_regs4 x_u3.self.zero _ (by decide), x_u3.upd_ne x_u2.self.zero _ (by decide),
          x_u2.upd_eq (by decide), x_u1.upd_eq (by decide)]; rfl)
        (by rw [x_regs4]; simp +decide [upd]) (even_clear _ (even_at PKO (by decide) (0x7C + 8) (by decide)))
        (by rw [x_sp4]; exact aligned_add hG4 (by decide))
        (by rw [x_sp4, eA]; exact hiG (by decide) (by decide) (by decide))
        (by rw [x_sp4, eA]; exact hiG (by decide) (by decide) (by decide))
        (by rw [x_sp4, eA]; exact offs (Or.inl (by decide)) (by decide) (by decide))
        (by rw [x_sp4, eA]; exact (sE1.subR (c := 0x7AC) (l := 4) (by decide)).symm)
      rw [x_mem4, hy17, cB Dx sE1] at x_a5
      rw [x_mem4, x_sp4, eA] at x_f5
      have Dx_ : PkSt m.mem Ms G pk (reg m) x_5.mem x_5 0x84 :=
        ⟨⟨by rw [x_pc5], rfl, fun _ => rfl⟩, by rw [x_k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), x_sp4],
          by rw [x_k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), x_r4 _ (by decide) (by decide) (by decide),
            Dx.hs0],
          fun q hq => by
            rw [x_k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
              (by revert hq; revert q; decide) (by revert hq; revert q; decide),
              x_r4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
              Dx.keep q hq],
          fun x hx => by rw [x_f5 x (inG (by decide) hx), Dx.agree x hx],
          fun c h1 h2 => by rw [x_f5 _ (offs (Or.inl (by omega)) (by decide) (by omega)), Dx.slots c h1 h2]⟩
      have hyx_ : memBytes x_5.mem (G + BitVec.ofNat 32 0x7B0) 32 = clearTop (memBytes m.mem pk 32) := by
        rw [← hy17]
        exact memBytes_congr fun i hi => by
          rw [x_f5 _ (by rw [spk]; exact offs (Or.inl (by omega)) (by decide) (by omega))]
      cases he1 : decide (clearTop (memBytes m.mem pk 32) = memBytes m.mem (BitVec.ofNat 32 (img% p256OneAddress)) 32) with
      | true =>
        obtain ⟨n3, e3, v3⟩ := Dx_.st.taken (hcOf Dx_) 0x9A pko_at_84 (by decide) (by rw [x_a5, ite_eq_left_of_eq_true _ _ (eq_true (of_decide_eq_true he1)), Dx_.st.zero]; decide)
        obtain ⟨m', c', a, b, c, a0', f⟩ := end0 (Dx_.jmp v3)
        refine ⟨m', .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans (c9.trans (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (c16.trans (c17.trans (.cons e1 (.cons e2 (.cons x_e1 (.cons x_e2 (.cons x_e3 (x_c4.trans (x_c5.trans (.cons e3 (c'))))))))))))))))))))))))), a, b, c, ?_, f⟩
        rw [a0', pkOk_e1 hl (by rw [getD_memBytes _ _ (by decide : 31 < 32)]; exact hsg) he1]; rfl
      | false =>
        obtain ⟨n3, e3, v3⟩ := Dx_.st.notTaken (hcOf Dx_) 0x86 pko_at_84 (by decide) (by rw [x_a5, ite_eq_right_of_eq_false _ _ (eq_false (of_decide_eq_false he1)), Dx_.st.zero]; decide)
        have Dy := Dx_.jmp v3
        obtain ⟨y_1, y_e1, y_u1⟩ := Dy.st.lui (hcOf Dy) pko_at_86 (off' := 0x8A) (by decide)
        obtain ⟨y_2, y_e2, y_u2⟩ := y_u1.self.aluImm (hcOf Dy) pko_at_8a (off' := 0x8E) (by decide)
        obtain ⟨y_3, y_e3, y_u3⟩ := y_u2.self.alu (hcOf Dy) pko_at_8e (off' := 0x90) (by decide)
        obtain ⟨y_4, y_c4, y_pc4, y_mem4, y_regs4⟩ := y_u3.self.callRa (cb := BitVec.ofNat 32 arr32EqCryptoAddress)
          (hcOf Dy) pko_at_90 pko_at_94 (by decide) (by decide)
        have y_r4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ ra → reg y_4 q = reg n3 q := fun q h0 h1 hr => by
          rw [PEnv.reg1 y_regs4 y_u3.self.zero q hr, y_u3.upd_ne y_u2.self.zero q h0, y_u2.upd_ne y_u1.self.zero q h1,
            y_u1.upd_ne Dy.st.zero q h1]
        have y_sp4 : reg y_4 sp = G + BitVec.ofNat 32 0x7B0 := by
          rw [y_r4 _ (by decide) (by decide) (by decide), Dy.hsp]
        obtain ⟨y_5, y_c5, y_pc5, y_a5, y_k5, y_f5⟩ := arr32EqCrypto_correct y_4 (p := G + BitVec.ofNat 32 0x7B0)
          (q := BitVec.ofNat 32 (img% edPm1Address)) (by decide)
          (by rw [y_mem4]; exact E.aeq.hi (fun x hx => Dy.agree x (codeG x hx)) (by decide) (by decide))
          (by rw [y_mem4]; exact E.mcmp.hi (fun x hx => Dy.agree x (codeG x hx)) (by decide) (by decide)) y_pc4
          (by rw [PEnv.reg1 y_regs4 y_u3.self.zero _ (by decide), y_u3.upd_eq (by decide), y_u2.self.zero,
            y_u2.upd_ne y_u1.self.zero _ (by decide), y_u1.upd_ne Dy.st.zero _ (by decide), Dy.hsp]
              exact BitVec.zero_add _)
          (by rw [PEnv.reg1 y_regs4 y_u3.self.zero _ (by decide), y_u3.upd_ne y_u2.self.zero _ (by decide),
            y_u2.upd_eq (by decide), y_u1.upd_eq (by decide)]; rfl)
          (by rw [y_regs4]; simp +decide [upd]) (even_clear _ (even_at PKO (by decide) (0x90 + 8) (by decide)))
          (by rw [y_sp4]; exact aligned_add hG4 (by decide))
          (by rw [y_sp4, eA]; exact hiG (by decide) (by decide) (by decide))
          (by rw [y_sp4, eA]; exact hiG (by decide) (by decide) (by decide))
          (by rw [y_sp4, eA]; exact offs (Or.inl (by decide)) (by decide) (by decide))
          (by rw [y_sp4, eA]; exact (sE2.subR (c := 0x7AC) (l := 4) (by decide)).symm)
        rw [y_mem4, hyx_, cB Dy sE2] at y_a5
        rw [y_mem4, y_sp4, eA] at y_f5
        have Dy_ : PkSt m.mem Ms G pk (reg m) y_5.mem y_5 0x98 :=
          ⟨⟨by rw [y_pc5], rfl, fun _ => rfl⟩, by rw [y_k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), y_sp4],
            by rw [y_k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), y_r4 _ (by decide) (by decide) (by decide),
              Dy.hs0],
            fun q hq => by
              rw [y_k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
                (by revert hq; revert q; decide) (by revert hq; revert q; decide),
                y_r4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
                Dy.keep q hq],
            fun x hx => by rw [y_f5 x (inG (by decide) hx), Dy.agree x hx],
            fun c h1 h2 => by rw [y_f5 _ (offs (Or.inl (by omega)) (by decide) (by omega)), Dy.slots c h1 h2]⟩
        have hyy_ : memBytes y_5.mem (G + BitVec.ofNat 32 0x7B0) 32 = clearTop (memBytes m.mem pk 32) := by
          rw [← hyx_]
          exact memBytes_congr fun i hi => by
            rw [y_f5 _ (by rw [spk]; exact offs (Or.inl (by omega)) (by decide) (by omega))]
        cases he2 : decide (clearTop (memBytes m.mem pk 32) = memBytes m.mem (BitVec.ofNat 32 (img% edPm1Address)) 32) with
        | true =>
          obtain ⟨n4, e4, v4⟩ := Dy_.st.notTaken (hcOf Dy_) 0x9A pko_at_98 (by decide) (by rw [y_a5, ite_eq_left_of_eq_true _ _ (eq_true (of_decide_eq_true he2)), Dy_.st.zero]; decide)
          obtain ⟨m', c', a, b, c, a0', f⟩ := end0 (Dy_.jmp v4)
          refine ⟨m', .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans (c9.trans (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (c16.trans (c17.trans (.cons e1 (.cons e2 (.cons x_e1 (.cons x_e2 (.cons x_e3 (x_c4.trans (x_c5.trans (.cons e3 (.cons y_e1 (.cons y_e2 (.cons y_e3 (y_c4.trans (y_c5.trans (.cons e4 (c'))))))))))))))))))))))))))))))), a, b, c, ?_, f⟩
          rw [a0', pkOk_e2 hl (by rw [getD_memBytes _ _ (by decide : 31 < 32)]; exact hsg) he1 he2]; rfl
        | false =>
          obtain ⟨n4, e4, v4⟩ := Dy_.st.taken (hcOf Dy_) 0x42 pko_at_98 (by decide) (by rw [y_a5, ite_eq_right_of_eq_false _ _ (eq_false (of_decide_eq_false he2)), Dy_.st.zero]; decide)
          obtain ⟨m', c', a, b, c, a0', f⟩ := endF (Dy_.jmp v4)
          refine ⟨m', .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans (c9.trans (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (c16.trans (c17.trans (.cons e1 (.cons e2 (.cons x_e1 (.cons x_e2 (.cons x_e3 (x_c4.trans (x_c5.trans (.cons e3 (.cons y_e1 (.cons y_e2 (.cons y_e3 (y_c4.trans (y_c5.trans (.cons e4 (c'))))))))))))))))))))))))))))))), a, b, c, ?_, f⟩
          rw [a0', pkOk_e0 hl (by rw [getD_memBytes _ _ (by decide : 31 < 32)]; exact hsg) he1 he2]

end C3.RV32
