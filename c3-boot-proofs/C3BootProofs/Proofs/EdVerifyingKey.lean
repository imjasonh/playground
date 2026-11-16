import C3BootProofs.Proofs.EdDecompress

/-!
# `ed25519_dalek::VerifyingKey::from_bytes`, as compiled

`from_bytes` decompresses the 32 bytes through the proved
`CompressedEdwardsY::decompress`, and on success writes `Ok` (tag 0) with
the bytes and the point's 160 bytes after them: the first four limbs of `X`
through registers and the rest with `memcpy`. On failure it writes tag 1.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem vkb_at_0 : fetchRel edVerifyingKeyFromBytesCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF40, 2) := by decide
theorem vkb_at_2 : fetchRel edVerifyingKeyFromBytesCode 0x2 = some (.store .sw sp ra 0xBC, 2) := by decide
theorem vkb_at_4 : fetchRel edVerifyingKeyFromBytesCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xB8, 2) := by decide
theorem vkb_at_6 : fetchRel edVerifyingKeyFromBytesCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xB4, 2) := by decide
theorem vkb_at_8 : fetchRel edVerifyingKeyFromBytesCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xB0, 2) := by decide
theorem vkb_at_a : fetchRel edVerifyingKeyFromBytesCode 0xA = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem vkb_at_c : fetchRel edVerifyingKeyFromBytesCode 0xC = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem vkb_at_e : fetchRel edVerifyingKeyFromBytesCode 0xE = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem vkb_at_10 : fetchRel edVerifyingKeyFromBytesCode 0x10 = some (.auipc ra 0xB000, 4) := by decide
theorem vkb_at_14 : fetchRel edVerifyingKeyFromBytesCode 0x14 = some (.jalr ra ra 0x2E6, 4) := by decide
theorem vkb_at_18 : fetchRel edVerifyingKeyFromBytesCode 0x18 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem vkb_at_1a : fetchRel edVerifyingKeyFromBytesCode 0x1A = some (.branch .beq a0 x0 0x3C, 2) := by decide
theorem vkb_at_1c : fetchRel edVerifyingKeyFromBytesCode 0x1C = some (.load .lw a0 sp 0x14, 2) := by decide
theorem vkb_at_1e : fetchRel edVerifyingKeyFromBytesCode 0x1E = some (.load .lw a1 sp 0x18, 2) := by decide
theorem vkb_at_20 : fetchRel edVerifyingKeyFromBytesCode 0x20 = some (.load .lw a2 sp 0x1C, 2) := by decide
theorem vkb_at_22 : fetchRel edVerifyingKeyFromBytesCode 0x22 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem vkb_at_24 : fetchRel edVerifyingKeyFromBytesCode 0x24 = some (.store .sw (8 : Fin 32) a0 0x28, 2) := by decide
theorem vkb_at_26 : fetchRel edVerifyingKeyFromBytesCode 0x26 = some (.store .sw (8 : Fin 32) a1 0x2C, 2) := by decide
theorem vkb_at_28 : fetchRel edVerifyingKeyFromBytesCode 0x28 = some (.store .sw (8 : Fin 32) a2 0x30, 2) := by decide
theorem vkb_at_2a : fetchRel edVerifyingKeyFromBytesCode 0x2A = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem vkb_at_2c : fetchRel edVerifyingKeyFromBytesCode 0x2C = some (.aluImm .add a0 (8 : Fin 32) 0x34, 4) := by decide
theorem vkb_at_30 : fetchRel edVerifyingKeyFromBytesCode 0x30 = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem vkb_at_34 : fetchRel edVerifyingKeyFromBytesCode 0x34 = some (.auipc ra 0x10000, 4) := by decide
theorem vkb_at_38 : fetchRel edVerifyingKeyFromBytesCode 0x38 = some (.jalr ra ra 0xFFFFFB40, 4) := by decide
theorem vkb_at_3c : fetchRel edVerifyingKeyFromBytesCode 0x3C = some (.aluImm .add a0 (8 : Fin 32) 0x4, 4) := by decide
theorem vkb_at_40 : fetchRel edVerifyingKeyFromBytesCode 0x40 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem vkb_at_44 : fetchRel edVerifyingKeyFromBytesCode 0x44 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem vkb_at_46 : fetchRel edVerifyingKeyFromBytesCode 0x46 = some (.auipc ra 0x10000, 4) := by decide
theorem vkb_at_4a : fetchRel edVerifyingKeyFromBytesCode 0x4A = some (.jalr ra ra 0xFFFFFB2E, 4) := by decide
theorem vkb_at_4e : fetchRel edVerifyingKeyFromBytesCode 0x4E = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem vkb_at_50 : fetchRel edVerifyingKeyFromBytesCode 0x50 = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0x24, 4) := by decide
theorem vkb_at_54 : fetchRel edVerifyingKeyFromBytesCode 0x54 = some (.jal x0 0x4, 2) := by decide
theorem vkb_at_56 : fetchRel edVerifyingKeyFromBytesCode 0x56 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem vkb_at_58 : fetchRel edVerifyingKeyFromBytesCode 0x58 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem vkb_at_5a : fetchRel edVerifyingKeyFromBytesCode 0x5A = some (.load .lw ra sp 0xBC, 2) := by decide
theorem vkb_at_5c : fetchRel edVerifyingKeyFromBytesCode 0x5C = some (.load .lw (8 : Fin 32) sp 0xB8, 2) := by decide
theorem vkb_at_5e : fetchRel edVerifyingKeyFromBytesCode 0x5E = some (.load .lw (9 : Fin 32) sp 0xB4, 2) := by decide
theorem vkb_at_60 : fetchRel edVerifyingKeyFromBytesCode 0x60 = some (.load .lw (18 : Fin 32) sp 0xB0, 2) := by decide
theorem vkb_at_62 : fetchRel edVerifyingKeyFromBytesCode 0x62 = some (.aluImm .add sp sp 0xC0, 2) := by decide
theorem vkb_at_64 : fetchRel edVerifyingKeyFromBytesCode 0x64 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev VKB : Word := BitVec.ofNat 32 edVerifyingKeyFromBytesAddress

/-- The registers the prologue saves, at their offsets from the new `sp`. -/
abbrev vkbPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0xBC), ((8 : Fin 32), BitVec.ofNat 32 0xB8), ((9 : Fin 32), BitVec.ofNat 32 0xB4),
   ((18 : Fin 32), BitVec.ofNat 32 0xB0)]

set_option maxRecDepth 20000 in
theorem vkbSave_end : blockEnd edVerifyingKeyFromBytesCode 0x2 (saveBlockR sp vkbPs) = some 0xA := by decide

set_option maxRecDepth 20000 in
/-- A `DecEnv` survives any change below the code. -/
theorem DecEnv.hi {M M' : Word → BitVec 8} (E : DecEnv M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    DecEnv M' :=
  ⟨E.cod.hi h (by decide) (by decide), E.l3.hi h (by decide) (by decide), E.l4.hi h (by decide) (by decide),
    E.red.hi h (by decide) (by decide), E.sq.hi h (by decide) (by decide), E.sqi.hi h (by decide) (by decide),
    E.sub.hi h (by decide) (by decide), E.add.hi h (by decide) (by decide), E.mul.hi h (by decide) (by decide),
    E.pw.hi h (by decide) (by decide), E.pk.hi h (by decide) (by decide), E.ce.hi h (by decide) (by decide),
    E.tb.hi h (by decide) (by decide), E.cs.hi h (by decide) (by decide), E.cu.hi h (by decide) (by decide),
    E.bb.hi h (by decide) (by decide), E.neg.hi h (by decide) (by decide), E.fca.hi h (by decide) (by decide),
    E.isn.hi h (by decide) (by decide), E.cn.hi h (by decide) (by decide), E.mcs.hi h (by decide) (by decide),
    E.mcb.hi h (by decide) (by decide)⟩

/-- What `from_bytes` leaves at `out` for the bytes `b` and `decompress`'s
result `o`. -/
def VkOut (M : Word → BitVec 8) (out : Word) (b : Bytes) :
    Option (List Nat × List Nat × List Nat × List Nat) → Prop
  | some (X, Y, Z, T) => memLoad32 M out = 0 ∧ memBytes M (out + BitVec.ofNat 32 4) 32 = b ∧
      feW M (out + BitVec.ofNat 32 0x24) = X ∧ feW M (out + BitVec.ofNat 32 0x4C) = Y ∧
      feW M (out + BitVec.ofNat 32 0x74) = Z ∧ feW M (out + BitVec.ofNat 32 0x9C) = T
  | none => memLoad32 M out = 1

theorem vk_ld2 {M M' : Word → BitVec 8} {b b' : Word}
    (h : ∀ j, j < 4 → M (b + BitVec.ofNat 32 j) = M' (b' + BitVec.ofNat 32 j)) :
    memLoad32 M b = memLoad32 M' b' := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  rw [h0, show b + 1 = b + BitVec.ofNat 32 1 from rfl, h 1 (by decide),
    show b + 2 = b + BitVec.ofNat 32 2 from rfl, h 2 (by decide),
    show b + 3 = b + BitVec.ofNat 32 3 from rfl, h 3 (by decide)]
  rfl

theorem spk (G : Word) (a k : Nat) : G + BitVec.ofNat 32 a + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (a + k) :=
  add_ofNat_assoc ..

set_option maxRecDepth 20000 in
/-- From offset 0x5A: the epilogue reloads `ra` and `s0` to `s2` from the
frame at `F` and returns. -/
theorem vkb_epi {Mx : Word → BitVec 8} {n : Machine} {F : Word} (hc : CodeIn Mx VKB edVerifyingKeyFromBytesCode)
    (s : St Mx VKB n 0x5A (reg n)) (hsp : reg n sp = F) (hF : F.toNat % 4 = 0) :
    ∃ m', Steps n m' ∧ m'.pc = memLoad32 Mx (F + 0xBC) &&& ~~~1 ∧ reg m' sp = F + 0xC0 ∧
      reg m' (8 : Fin 32) = memLoad32 Mx (F + 0xB8) ∧ reg m' (9 : Fin 32) = memLoad32 Mx (F + 0xB4) ∧
      reg m' (18 : Fin 32) = memLoad32 Mx (F + 0xB0) ∧ reg m' ra = memLoad32 Mx (F + 0xBC) ∧
      (∀ q, q ≠ ra → q ≠ sp → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → reg m' q = reg n q) ∧
      m'.mem = Mx := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc vkb_at_5a (off' := 0x5C) (by decide) (by rw [hsp]; exact aligned_add hF (k := 0xBC) (by decide))
  obtain ⟨n2, d2, u2⟩ := u1.self.lw hc vkb_at_5c (off' := 0x5E) (by decide)
    (by rw [u1.upd_ne hz sp (by decide), hsp]; exact aligned_add hF (k := 0xB8) (by decide))
  obtain ⟨n3, d3, u3⟩ := u2.self.lw hc vkb_at_5e (off' := 0x60) (by decide)
    (by rw [u2.upd_ne u1.self.zero sp (by decide), u1.upd_ne hz sp (by decide), hsp]; exact aligned_add hF (k := 0xB4) (by decide))
  obtain ⟨n4, d4, u4⟩ := u3.self.lw hc vkb_at_60 (off' := 0x62) (by decide)
    (by rw [u3.upd_ne u2.self.zero sp (by decide), u2.upd_ne u1.self.zero sp (by decide), u1.upd_ne hz sp (by decide), hsp]
        exact aligned_add hF (k := 0xB0) (by decide))
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc vkb_at_62 (off' := 0x64) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hc vkb_at_64
  have sp4 : reg n4 sp = F := by
    rw [u4.upd_ne u3.self.zero sp (by decide), u3.upd_ne u2.self.zero sp (by decide),
      u2.upd_ne u1.self.zero sp (by decide), u1.upd_ne hz sp (by decide), hsp]
  have r4 : ∀ q, q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → reg n4 q = reg n q :=
    fun q h1 h8 h9 h18 => by
      rw [u4.upd_ne u3.self.zero q h18, u3.upd_ne u2.self.zero q h9, u2.upd_ne u1.self.zero q h8, u1.upd_ne hz q h1]
  have ra4 : reg n4 ra = memLoad32 Mx (F + 0xBC) := by
    rw [u4.upd_ne u3.self.zero _ (by decide), u3.upd_ne u2.self.zero _ (by decide), u2.upd_ne u1.self.zero _ (by decide),
      u1.upd_eq (by decide), hsp]
  have s04 : reg n4 (8 : Fin 32) = memLoad32 Mx (F + 0xB8) := by
    rw [u4.upd_ne u3.self.zero _ (by decide), u3.upd_ne u2.self.zero _ (by decide), u2.upd_eq (by decide),
      u1.upd_ne hz sp (by decide), hsp]
  have s14 : reg n4 (9 : Fin 32) = memLoad32 Mx (F + 0xB4) := by
    rw [u4.upd_ne u3.self.zero _ (by decide), u3.upd_eq (by decide), u2.upd_ne u1.self.zero sp (by decide),
      u1.upd_ne hz sp (by decide), hsp]
  have s24 : reg n4 (18 : Fin 32) = memLoad32 Mx (F + 0xB0) := by
    rw [u4.upd_eq (by decide), u3.upd_ne u2.self.zero sp (by decide), u2.upd_ne u1.self.zero sp (by decide),
      u1.upd_ne hz sp (by decide), hsp]
  refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ?_, ?_, ?_, ?_, ?_, ?_,
    fun q h1 h2 h8 h9 h18 => ?_, by rw [mem6]⟩
  · rw [pc6, u5.upd_ne u4.self.zero _ (by decide), ra4, add_lit_zero]
  · rw [regs6, u5.upd_eq (by decide), sp4]; rfl
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), s04]
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), s14]
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), s24]
  · rw [regs6, u5.upd_ne u4.self.zero _ (by decide), ra4]
  · rw [regs6, u5.upd_ne u4.self.zero _ h2, r4 q h1 h8 h9 h18]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `ed25519_dalek::VerifyingKey::from_bytes`.** For the 32
bytes at `bp` it writes `VkOut` to `out`: `Ok` with the bytes and the point
`decompress` gives, or the error tag when there is none. It returns with
`sp` and the callee-saved registers restored and writes nothing outside
`out`'s 0xC4 bytes and the 0x7B0 bytes of stack below `sp`. -/
theorem edVkFromBytes_correct (m : Machine) {sp0 out bp retAddr : Word} (E : DecEnv m.mem)
    (hc : CodeIn m.mem VKB edVerifyingKeyFromBytesCode) (hpc : m.pc = VKB) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = bp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x7B0 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000) (hout : out.toNat % 4 = 0)
    (hoW : out.toNat + 0xC4 ≤ 0x40000000)
    (hbW : bp.toNat + 32 < 2 ^ 32)
    (sOG : Sep out 0xC4 (sp0 + 0xFFFFF850) 0x7B0) (sBG : Sep bp 32 (sp0 + 0xFFFFF850) 0x7B0) (sBO : Sep bp 32 out 0xC4)
    (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 (sp0 + 0xFFFFF850) 0x7B0)
    (sD : Sep (BitVec.ofNat 32 edDAddress) 40 (sp0 + 0xFFFFF850) 0x7B0)
    (sS : Sep (BitVec.ofNat 32 edSqrtM1Address) 40 (sp0 + 0xFFFFF850) 0x7B0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      VkOut m'.mem out (memBytes m.mem bp 32) (decSpec (feW m.mem (BitVec.ofNat 32 edOneAddress))
        (feW m.mem (BitVec.ofNat 32 edDAddress)) (feW m.mem (BitVec.ofNat 32 edSqrtM1Address)) (memBytes m.mem bp 32)) ∧
      ∀ x, Sep (sp0 + 0xFFFFF850) 0x7B0 x 1 → Sep out 0xC4 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFF850 = G := ⟨_, rfl⟩
  rw [hG] at sOG sBG sO sD sS ⊢
  have hGn : G.toNat = sp0.toNat - 0x7B0 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFF850 : Word).toNat = 2 ^ 32 - 0x7B0 from rfl]; omega
  have hG4 : G.toNat % 4 = 0 := by omega
  have hGc : ∀ c, c ≤ 0x7B0 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eF : sp0 + 0xFFFFFF40 = G + BitVec.ofNat 32 0x6F0 := by rw [← hG, BitVec.add_assoc]; rfl
  have eS : G + BitVec.ofNat 32 0x7B0 = sp0 := by rw [← hG, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x7B0 → d + k ≤ 0x7B0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have inG : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x7B0 → Sep G 0x7B0 x 1 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => (hx.symm.subR h).symm
  have hiG : ∀ {c l : Nat} {b : Word} {k : Nat}, c + l ≤ 0x7B0 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l b k := fun h h1 h2 => sep_of_le (by rw [hGc _ (by omega)]; omega) h2
  have codeG : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep G 0x7B0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have st0 : St m.mem VKB m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc vkb_at_0 (off' := 2) (by decide)
  have sp1 : reg m1 sp = G + BitVec.ofNat 32 0x6F0 := by rw [u1.upd_eq (by decide), hsp]; exact eF
  have r1 : ∀ q, q ≠ sp → reg m1 q = reg m q := fun q h => u1.upd_ne hz q h
  obtain ⟨m3, c3, u3⟩ := St.block (saveBlockR sp vkbPs) u1.self hc vkbSave_end (saveBlockR_ok sp _ vkbPs _ fun p hp => by
    rw [sp1]
    simp only [vkbPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact ⟨by rw [add_ofNat_assoc]; exact aligned_add hG4 (by decide),
        by rw [add_ofNat_assoc]; exact hiG (by decide) (by decide) (by decide)⟩)
  rw [saveBlockR_run, sp1] at u3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (G + BitVec.ofNat 32 0x6F0) (reg m1) vkbPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u3
  dsimp only at u3
  have IMs : ∀ x, Sep G 0x7B0 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]
    exact saveMem_outside vkbPs fun p hp => by
      simp only [vkbPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> (rw [add_ofNat_assoc]; exact inG (by decide) hx)
  have slots : ∀ r o, (r, o) ∈ vkbPs → memLoad32 Ms (G + BitVec.ofNat 32 0x6F0 + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [vkbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot vkbPs _ hm (by
      simp only [vkbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), r1 r hr]
  have hcS : CodeIn Ms VKB edVerifyingKeyFromBytesCode := hc.hi (fun x hx => IMs x (codeG x hx)) (by decide) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hcS vkb_at_a (off' := 0xC) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.self.alu hcS vkb_at_c (off' := 0xE) (by decide)
  obtain ⟨m6, d6, u6⟩ := u5.self.aluImm hcS vkb_at_e (off' := 0x10) (by decide)
  have r6 : ∀ q, q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ a0 → reg m6 q = reg m1 q := fun q h9 h8 h0 => by
    rw [u6.upd_ne u5.self.zero q h0, u5.upd_ne u4.self.zero q h8, u4.upd_ne u1.self.zero q h9]
  have s1_6 : reg m6 (9 : Fin 32) = bp := by
    rw [u6.upd_ne u5.self.zero _ (by decide), u5.upd_ne u4.self.zero _ (by decide), u4.upd_eq (by decide),
      u1.self.zero, r1 a1 (by decide), ha1]; exact BitVec.zero_add _
  have s0_6 : reg m6 (8 : Fin 32) = out := by
    rw [u6.upd_ne u5.self.zero _ (by decide), u5.upd_eq (by decide), u4.self.zero, u4.upd_ne u1.self.zero _ (by decide),
      r1 a0 (by decide), ha0]; exact BitVec.zero_add _
  have sp6 : reg m6 sp = G + BitVec.ofNat 32 0x6F0 := by rw [r6 sp (by decide) (by decide) (by decide), sp1]
  have a0_6 : reg m6 a0 = G + BitVec.ofNat 32 0x6FC := by
    rw [u6.upd_eq (by decide), u5.upd_ne u4.self.zero _ (by decide), u4.upd_ne u1.self.zero _ (by decide), sp1]
    exact add_sp G rfl
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6.self.callRa (cb := DEC) hcS vkb_at_10 vkb_at_14 (by decide) (by decide)
  have r7 := PEnv.reg1 regs7 u6.self.zero
  have eR : G + BitVec.ofNat 32 0x6F0 + 0xFFFFF910 = G := by rw [BitVec.add_assoc]; exact BitVec.add_zero G
  have sub0 : ∀ {c : Word}, Sep c 40 G 0x7B0 → Sep c 40 G 0x6F0 := fun h => by
    have := h.subR (c := 0) (l := 0x6F0) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨m8, c8, pc8, sp8, k8, out8, fr8⟩ := edDecompress_correct m7 (E.hi fun x hx => by rw [mem7]; exact IMs x (codeG x hx))
    pc7 (by rw [r7 a0 (by decide), a0_6]) (by rw [r7 a1 (by decide), r6 a1 (by decide) (by decide) (by decide),
      r1 a1 (by decide), ha1])
    (by rw [regs7]; simp +decide [upd]) (even_clear _ (even_at VKB (by decide) (0x10 + 8) (by decide)))
    (by rw [r7 sp (by decide), sp6]) (aligned_add hG4 (by decide)) (by rw [hGc _ (by decide)]; omega)
    (by rw [hGc _ (by decide)]; omega) (aligned_add hG4 (by decide)) (by rw [hGc _ (by decide)]; omega)
    (by rw [eR]; have := offs (c := 0x6FC) (n := 0xA4) (d := 0) (k := 0x6F0) (Or.inr (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this)
    (by rw [eR]; have := sBG.subR (c := 0) (l := 0x6F0) (by decide); rwa [add_ofNat_zero] at this)
    (by rw [eR]; exact sub0 sO) (by rw [eR]; exact sub0 sD) (by rw [eR]; exact sub0 sS)
  rw [mem7, eR] at fr8
  rw [mem7] at out8
  have cst : ∀ {c : Word}, Sep c 40 G 0x7B0 → feW Ms c = feW m.mem c := fun h =>
    feW_frame fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact IMs _ (h.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have hbp : memBytes Ms bp 32 = memBytes m.mem bp 32 :=
    memBytes_congr fun i hi => IMs _ (sBG.sub (c := i) (l := 1) hi).symm
  rw [cst sO, cst sD, cst sS, hbp] at out8
  have I8 : ∀ x, Sep G 0x7B0 x 1 → m8.mem x = m.mem x := fun x hx => by
    rw [fr8 x (by have := hx.sub (c := 0) (l := 0x6F0) (by decide); rwa [add_ofNat_zero] at this)
      (inG (by decide) hx), IMs x hx]
  have S8 : ∀ c, 0x7A0 ≤ c → c < 0x7B0 → m8.mem (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) := fun c h1 h2 =>
    fr8 _ (by have := offs (c := 0) (n := 0x6F0) (d := c) (k := 1) (Or.inl (by omega)) (by decide) (by omega)
              rwa [add_ofNat_zero] at this) (offs (Or.inl (by omega)) (by decide) (by omega))
  have hc8 : CodeIn m8.mem VKB edVerifyingKeyFromBytesCode := hc.hi (fun x hx => I8 x (codeG x hx)) (by decide) (by decide)
  have u8 : St m8.mem VKB m8 0x18 (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have keep8 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m8 q = reg m7 q := fun q hq =>
    k8 q (by revert hq; revert q; decide)
  have sp8' : reg m8 sp = G + BitVec.ofNat 32 0x6F0 := by rw [sp8]
  obtain ⟨m9, d9, u9⟩ := u8.lw hc8 vkb_at_18 (off' := 0x1A) (by decide) (by rw [sp8']; exact congrArg (fun w : Word => w.toNat % 4) (add_ofNat_assoc G 0x6F0 12) ▸ aligned_add hG4 (k := 0x6FC) (by decide))
  have a0_9 : reg m9 a0 = memLoad32 m8.mem (G + BitVec.ofNat 32 0x6FC) := by
    rw [u9.upd_eq (by decide), sp8']; exact congrArg _ (add_ofNat_assoc G 0x6F0 12)
  have r9 : ∀ q, q ≠ a0 → reg m9 q = reg m8 q := fun q h => u9.upd_ne u8.zero q h
  have slotv : ∀ r o, (r, o) ∈ vkbPs → ∀ Mx : Word → BitVec 8,
      (∀ c, 0x7A0 ≤ c → c < 0x7B0 → Mx (G + BitVec.ofNat 32 c) = m8.mem (G + BitVec.ofNat 32 c)) →
      memLoad32 Mx (G + BitVec.ofNat 32 0x6F0 + o) = reg m r := fun r o hm Mx hMx => by
    rw [← slots r o hm]
    have ho : ∃ c, G + BitVec.ofNat 32 0x6F0 + o = G + BitVec.ofNat 32 c ∧ 0x7A0 ≤ c ∧ c + 4 ≤ 0x7B0 := by
      simp only [vkbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨_, add_ofNat_assoc G 0x6F0 _, by decide, by decide⟩
    obtain ⟨c, hc', h1, h2⟩ := ho
    rw [hc']
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, hMx _ (by omega) (by omega), S8 _ (by omega) (by omega)]
  have hFal : (G + BitVec.ofNat 32 0x6F0).toNat % 4 = 0 := aligned_add hG4 (by decide)
  have eS' : G + BitVec.ofNat 32 0x6F0 + 0xC0 = sp0 := by rw [← eS]; exact add_ofNat_assoc G 0x6F0 0xC0
  have sOut : ∀ c, c + 4 ≤ 0x7B0 → Sep out 4 (G + BitVec.ofNat 32 c) 4 := fun c hc' =>
    sep_pre (sOG.subR (c := c) (l := 4) hc') (by decide)
  have sOC : Sep out 4 VKB edVerifyingKeyFromBytesCode.length := sep_of_le (by
    have : VKB.toNat = edVerifyingKeyFromBytesAddress := by decide
    rw [this]; unfold edVerifyingKeyFromBytesAddress; omega) (by decide)
  have kq : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m9 q = reg m q := fun q hq => by
    rw [r9 q (by revert hq; revert q; decide), keep8 q (by revert hq; revert q; decide),
      r7 q (by revert hq; revert q; decide), r6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have s0_9 : reg m9 (8 : Fin 32) = out := by
    rw [r9 _ (by decide), keep8 _ (by decide), r7 _ (by decide), s0_6]
  have s1_9 : reg m9 (9 : Fin 32) = bp := by
    rw [r9 _ (by decide), keep8 _ (by decide), r7 _ (by decide), s1_6]
  have sp9 : reg m9 sp = G + BitVec.ofNat 32 0x6F0 := by rw [r9 _ (by decide), sp8']
  generalize decSpec (feW m.mem (BitVec.ofNat 32 edOneAddress)) (feW m.mem (BitVec.ofNat 32 edDAddress))
    (feW m.mem (BitVec.ofNat 32 edSqrtM1Address)) (memBytes m.mem bp 32) = Dv at out8 ⊢
  cases Dv with
  | none =>
    obtain ⟨m10, d10, u10⟩ := u9.self.taken hc8 0x56 vkb_at_1a (by decide)
      (by rw [a0_9, show memLoad32 m8.mem (G + BitVec.ofNat 32 0x6FC) = 0 from out8, u9.self.zero]; decide)
    obtain ⟨m11, d11, u11⟩ := u10.aluImm hc8 vkb_at_56 (off' := 0x58) (by decide)
    have s0_11 : reg m11 (8 : Fin 32) = out := by rw [u11.upd_ne u10.zero _ (by decide), s0_9]
    obtain ⟨m12, d12, u12⟩ := u11.self.sw hc8 vkb_at_58 (off' := 0x5A) (by decide)
      (by rw [s0_11, add_lit_zero]; exact hout)
    rw [s0_11, add_lit_zero, u11.upd_eq (by decide), u10.zero] at u12
    have hc12 := hc8.store32 (v := aluEval .add 0 1) sOC
    obtain ⟨m', c', pc', sp', s0', s1', s2', ra', oth', mem'⟩ := vkb_epi hc12 u12.self
      (by rw [u12.regs, u11.upd_ne u10.zero _ (by decide), sp9]) hFal
    have hMx : ∀ c, 0x7A0 ≤ c → c < 0x7B0 → memStore32 m8.mem out (aluEval .add 0 1) (G + BitVec.ofNat 32 c) =
        m8.mem (G + BitVec.ofNat 32 c) := fun c h1 h2 => st32_frame (sep_pre (sOG.subR (c := c) (l := 1) (by omega)) (by decide))
    have vra : memLoad32 (memStore32 m8.mem out (aluEval .add 0 1)) (G + BitVec.ofNat 32 0x6F0 + 0xBC) = reg m ra :=
      slotv ra (BitVec.ofNat 32 0xBC) (by decide) _ hMx
    have vs0 : memLoad32 (memStore32 m8.mem out (aluEval .add 0 1)) (G + BitVec.ofNat 32 0x6F0 + 0xB8) =
        reg m (8 : Fin 32) := slotv _ (BitVec.ofNat 32 0xB8) (by decide) _ hMx
    have vs1 : memLoad32 (memStore32 m8.mem out (aluEval .add 0 1)) (G + BitVec.ofNat 32 0x6F0 + 0xB4) =
        reg m (9 : Fin 32) := slotv _ (BitVec.ofNat 32 0xB4) (by decide) _ hMx
    have vs2 : memLoad32 (memStore32 m8.mem out (aluEval .add 0 1)) (G + BitVec.ofNat 32 0x6F0 + 0xB0) =
        reg m (18 : Fin 32) := slotv _ (BitVec.ofNat 32 0xB0) (by decide) _ hMx
    refine ⟨m', .cons d1 (c3.trans (.cons d4 (.cons d5 (.cons d6 (c7.trans (c8.trans (.cons d9 (.cons d10 (.cons d11 (.cons d12 c')))))))))), ?_, by rw [sp', eS'], fun q hq => ?_, ?_, fun x hx hy => ?_⟩
    · rw [pc', vra, hra, hret]
    · have hq' : q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
          q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
      rcases hq' with rfl | rfl | rfl | rfl | h
      · rw [ra', vra]
      · rw [s0', vs0]
      · rw [s1', vs1]
      · rw [s2', vs2]
      · rw [oth' q (by revert h; revert q; decide) (by revert h; revert q; decide) (by revert h; revert q; decide)
          (by revert h; revert q; decide) (by revert h; revert q; decide), u12.regs,
          u11.upd_ne u10.zero q (by revert h; revert q; decide), kq q h]
    · show memLoad32 m'.mem out = 1
      rw [mem', memLoad32_store32_same]; rfl
    · rw [mem', st32_frame (sep_pre hy (by decide)), I8 x hx]
  | some P =>
    obtain ⟨X, Y, Z, T⟩ := P
    obtain ⟨tag, hX, hY, hZ, hT⟩ := out8
    have hFk : ∀ k : Nat, k % 4 = 0 → (G + BitVec.ofNat 32 0x6F0 + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k hk => by
      rw [spk]; exact aligned_add hG4 (by omega)
    have hOk : ∀ k : Nat, k % 4 = 0 → (out + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k hk => aligned_add hout hk
    have sOCk : ∀ k : Nat, k + 4 ≤ 0xC4 → Sep (out + BitVec.ofNat 32 k) 4 VKB edVerifyingKeyFromBytesCode.length :=
      fun k hk => sep_of_le (by
        have : VKB.toNat = edVerifyingKeyFromBytesAddress := by decide
        rw [this, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold edVerifyingKeyFromBytesAddress; omega) (by decide)
    obtain ⟨m10, d10, u10⟩ := u9.self.notTaken hc8 0x1C vkb_at_1a (by decide)
      (by rw [a0_9, show memLoad32 m8.mem (G + BitVec.ofNat 32 0x6FC) = 1 from tag, u9.self.zero]; decide)
    obtain ⟨m11, d11, u11⟩ := u10.lw hc8 vkb_at_1c (off' := 0x1E) (by decide) (by rw [sp9]; exact hFk 0x14 rfl)
    obtain ⟨m12, d12, u12⟩ := u11.self.lw hc8 vkb_at_1e (off' := 0x20) (by decide)
      (by rw [u11.upd_ne u10.zero _ (by decide), sp9]; exact hFk 0x18 rfl)
    obtain ⟨m13, d13, u13⟩ := u12.self.lw hc8 vkb_at_20 (off' := 0x22) (by decide)
      (by rw [u12.upd_ne u11.self.zero _ (by decide), u11.upd_ne u10.zero _ (by decide), sp9]; exact hFk 0x1C rfl)
    obtain ⟨m14, d14, u14⟩ := u13.self.lw hc8 vkb_at_22 (off' := 0x24) (by decide)
      (by rw [u13.upd_ne u12.self.zero _ (by decide), u12.upd_ne u11.self.zero _ (by decide),
        u11.upd_ne u10.zero _ (by decide), sp9]; exact hFk 0x10 rfl)
    have r14 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (18 : Fin 32) → reg m14 q = reg m9 q := fun q h0 h1 h2 h18 => by
      rw [u14.upd_ne u13.self.zero q h18, u13.upd_ne u12.self.zero q h2, u12.upd_ne u11.self.zero q h1,
        u11.upd_ne u10.zero q h0]
    have L : ∀ k, memLoad32 m8.mem (G + BitVec.ofNat 32 0x6F0 + BitVec.ofNat 32 k) =
        memLoad32 m8.mem (G + BitVec.ofNat 32 (0x6F0 + k)) := fun k => by rw [spk]
    have vA : reg m14 a0 = memLoad32 m8.mem (G + BitVec.ofNat 32 0x704) := by
      rw [u14.upd_ne u13.self.zero _ (by decide), u13.upd_ne u12.self.zero _ (by decide),
        u12.upd_ne u11.self.zero _ (by decide), u11.upd_eq (by decide), sp9]; exact L 0x14
    have vB : reg m14 a1 = memLoad32 m8.mem (G + BitVec.ofNat 32 0x708) := by
      rw [u14.upd_ne u13.self.zero _ (by decide), u13.upd_ne u12.self.zero _ (by decide), u12.upd_eq (by decide),
        u11.upd_ne u10.zero _ (by decide), sp9]; exact L 0x18
    have vC : reg m14 a2 = memLoad32 m8.mem (G + BitVec.ofNat 32 0x70C) := by
      rw [u14.upd_ne u13.self.zero _ (by decide), u13.upd_eq (by decide), u12.upd_ne u11.self.zero _ (by decide),
        u11.upd_ne u10.zero _ (by decide), sp9]; exact L 0x1C
    have vS : reg m14 (18 : Fin 32) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x700) := by
      rw [u14.upd_eq (by decide), u13.upd_ne u12.self.zero _ (by decide), u12.upd_ne u11.self.zero _ (by decide),
        u11.upd_ne u10.zero _ (by decide), sp9]; exact L 0x10
    have s0_14 : reg m14 (8 : Fin 32) = out := by rw [r14 _ (by decide) (by decide) (by decide) (by decide), s0_9]
    obtain ⟨m15, d15, u15⟩ := u14.self.sw hc8 vkb_at_24 (off' := 0x26) (by decide) (by rw [s0_14]; exact hOk 0x28 rfl)
    rw [s0_14, vA] at u15
    have hc15 := hc8.store32 (v := memLoad32 m8.mem (G + BitVec.ofNat 32 0x704)) (sOCk 0x28 (by decide))
    obtain ⟨m16, d16, u16⟩ := u15.sw hc15 vkb_at_26 (off' := 0x28) (by decide) (by rw [s0_14]; exact hOk 0x2C rfl)
    rw [s0_14, vB] at u16
    have hc16 := hc15.store32 (v := memLoad32 m8.mem (G + BitVec.ofNat 32 0x708)) (sOCk 0x2C (by decide))
    obtain ⟨m17, d17, u17⟩ := u16.sw hc16 vkb_at_28 (off' := 0x2A) (by decide) (by rw [s0_14]; exact hOk 0x30 rfl)
    rw [s0_14, vC] at u17
    have hc17 := hc16.store32 (v := memLoad32 m8.mem (G + BitVec.ofNat 32 0x70C)) (sOCk 0x30 (by decide))
    obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 (memStore32 m8.mem (out + 0x28)
        (memLoad32 m8.mem (G + BitVec.ofNat 32 0x704))) (out + 0x2C) (memLoad32 m8.mem (G + BitVec.ofNat 32 0x708)))
        (out + 0x30) (memLoad32 m8.mem (G + BitVec.ofNat 32 0x70C)) = M3 := ⟨_, rfl⟩
    rw [hM3] at u17
    have hc3 : CodeIn M3 VKB edVerifyingKeyFromBytesCode := by rw [← hM3]; exact hc17
    -- `M3` agrees with `m8.mem` off the three words at `out + 0x28`
    have I3 : ∀ x, Sep (out + BitVec.ofNat 32 0x28) 12 x 1 → M3 x = m8.mem x := fun x hx => by
      rw [← hM3, st32_frame (hx.sub (c := 8) (l := 4) (by decide) |> fun h => by rwa [spk] at h),
        st32_frame (hx.sub (c := 4) (l := 4) (by decide) |> fun h => by rwa [spk] at h),
        st32_frame (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]
    have hOn : ∀ c, c ≤ 0xC4 → (out + BitVec.ofNat 32 c).toNat = out.toNat + c := fun c hc' => by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hst : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = 0x403b4856 := by decide
    have eFp : G + BitVec.ofNat 32 0x6F0 + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x6E0 := by rw [BitVec.add_assoc]; rfl
    have hiM3 : ∀ x : Word, 0x40000000 ≤ x.toNat → M3 x = m.mem x := fun x hx => by
      rw [I3 x (sep_of_le (by rw [hOn _ (by decide)]; omega) (by have := x.isLt; omega)), I8 x (codeG x hx)]
    obtain ⟨m18, d18, u18⟩ := u17.aluImm hc3 vkb_at_2a (off' := 0x2C) (by decide)
    obtain ⟨m19, d19, u19⟩ := u18.self.aluImm hc3 vkb_at_2c (off' := 0x30) (by decide)
    obtain ⟨m20, d20, u20⟩ := u19.self.aluImm hc3 vkb_at_30 (off' := 0x34) (by decide)
    have r20 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m20 q = reg m14 q := fun q h0 h1 h2 => by
      rw [u20.upd_ne u19.self.zero q h2, u19.upd_ne u18.self.zero q h0, u18.upd_ne u14.self.zero q h1]
    have sp14 : reg m14 sp = G + BitVec.ofNat 32 0x6F0 := by
      rw [r14 _ (by decide) (by decide) (by decide) (by decide), sp9]
    obtain ⟨m21, c21, pc21, mem21, regs21⟩ := u20.self.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc3 vkb_at_34
      vkb_at_38 (by decide) (by decide)
    have r21 := PEnv.reg1 regs21 u20.self.zero
    have sp21 : reg m21 sp = G + BitVec.ofNat 32 0x6F0 := by
      rw [r21 _ (by decide), r20 _ (by decide) (by decide) (by decide), sp14]
    have sO34 : Sep (out + BitVec.ofNat 32 0x34) 0x90 G 0x7B0 := sOG.sub (by decide)
    obtain ⟨m22, c22, pc22, sp22, _, f22, k22⟩ := memcpy_correct m21 (BitVec.ofNat 32 memcpyStubAddress)
      (VKB + BitVec.ofNat 32 (0x34 + 8)) (out + BitVec.ofNat 32 0x34) (G + BitVec.ofNat 32 0x710) 0x90
      (fun i hi => by rw [mem21]; exact E.mcs.hi hiM3 (by decide) (by decide) i hi) (by decide) pc21
      (by rw [r21 _ (by decide), u20.upd_ne u19.self.zero _ (by decide), u19.upd_eq (by decide),
        u18.upd_ne u14.self.zero _ (by decide), s0_14]; rfl)
      (by rw [r21 _ (by decide), u20.upd_ne u19.self.zero _ (by decide), u19.upd_ne u18.self.zero _ (by decide),
        u18.upd_eq (by decide), sp14]; exact add_sp G rfl)
      (by rw [r21 _ (by decide), u20.upd_eq (by decide), u19.self.zero]; rfl)
      (by rw [regs21]; simp +decide [upd]) (even_clear _ (even_at VKB (by decide) (0x34 + 8) (by decide)))
      (by
        rw [mem21, sp21, eFp]
        exact { code := E.mcb.hi hiM3 (by decide) (by decide)
                hDC := sep_of_le (by rw [hOn _ (by decide), hst]; omega) (by decide)
                hFC := hiG (by decide) (by decide) (by decide)
                hdF := sO34.subR (by decide)
                hsF := offs (Or.inr (by decide)) (by decide) (by decide)
                hsep := sO34.subR (by decide)
                hF := aligned_add hG4 (by decide)
                hFw := by rw [hGc _ (by decide)]; omega
                hdw := by rw [hOn _ (by decide)]; omega
                hsw := by rw [hGc _ (by decide)]; omega })
    rw [mem21, sp21, eFp] at f22
    have hi22 : ∀ x : Word, 0x40000000 ≤ x.toNat → m22.mem x = m.mem x := fun x hx => by
      rw [f22 x (hiG (c := 0x6E0) (l := 16) (k := 1) (by decide) hx (by have := x.isLt; omega)),
        copyBytes_sep (sep_of_le (by rw [hOn _ (by decide)]; omega) (by have := x.isLt; omega)) (Nat.le_refl _),
        hiM3 x hx]
    have hc22 : CodeIn m22.mem VKB edVerifyingKeyFromBytesCode := hc.hi hi22 (by decide) (by decide)
    have u22 : St m22.mem VKB m22 0x3C (reg m22) := ⟨by rw [pc22], rfl, fun _ => rfl⟩
    have k22' : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        reg m22 q = reg m21 q := fun q hq =>
      k22 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    have b22 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        reg m22 q = reg m14 q := fun q hq => by
      rw [k22' q (by revert hq; revert q; decide), r21 q (by revert hq; revert q; decide),
        r20 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    obtain ⟨m23, d23, u23⟩ := u22.aluImm hc22 vkb_at_3c (off' := 0x40) (by decide)
    obtain ⟨m24, d24, u24⟩ := u23.self.aluImm hc22 vkb_at_40 (off' := 0x44) (by decide)
    obtain ⟨m25, d25, u25⟩ := u24.self.alu hc22 vkb_at_44 (off' := 0x46) (by decide)
    have r25 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m25 q = reg m22 q := fun q h0 h1 h2 => by
      rw [u25.upd_ne u24.self.zero q h1, u24.upd_ne u23.self.zero q h2, u23.upd_ne u22.zero q h0]
    obtain ⟨m26, c26, pc26, mem26, regs26⟩ := u25.self.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc22 vkb_at_46
      vkb_at_4a (by decide) (by decide)
    have r26 := PEnv.reg1 regs26 u25.self.zero
    have sp26 : reg m26 sp = G + BitVec.ofNat 32 0x6F0 := by
      rw [r26 _ (by decide), r25 _ (by decide) (by decide) (by decide), sp22, sp21]
    have sO4 : Sep (out + BitVec.ofNat 32 4) 32 G 0x7B0 := sOG.sub (by decide)
    obtain ⟨m27, c27, pc27, sp27, _, f27, k27⟩ := memcpy_correct m26 (BitVec.ofNat 32 memcpyStubAddress)
      (VKB + BitVec.ofNat 32 (0x46 + 8)) (out + BitVec.ofNat 32 4) bp 32
      (fun i hi => by rw [mem26]; exact E.mcs.hi hi22 (by decide) (by decide) i hi) (by decide) pc26
      (by rw [r26 _ (by decide), u25.upd_ne u24.self.zero _ (by decide), u24.upd_ne u23.self.zero _ (by decide),
        u23.upd_eq (by decide), b22 _ (by decide), s0_14]; rfl)
      (by rw [r26 _ (by decide), u25.upd_eq (by decide), u24.self.zero, u24.upd_ne u23.self.zero _ (by decide),
        u23.upd_ne u22.zero _ (by decide), b22 _ (by decide), r14 _ (by decide) (by decide) (by decide) (by decide), s1_9]
          exact BitVec.zero_add _)
      (by rw [r26 _ (by decide), u25.upd_ne u24.self.zero _ (by decide), u24.upd_eq (by decide), u23.self.zero]; rfl)
      (by rw [regs26]; simp +decide [upd]) (even_clear _ (even_at VKB (by decide) (0x46 + 8) (by decide)))
      (by
        rw [mem26, sp26, eFp]
        exact { code := E.mcb.hi hi22 (by decide) (by decide)
                hDC := sep_of_le (by rw [hOn _ (by decide), hst]; omega) (by decide)
                hFC := hiG (by decide) (by decide) (by decide)
                hdF := sO4.subR (by decide)
                hsF := sBG.subR (by decide)
                hsep := sBO.symm.sub (by decide)
                hF := aligned_add hG4 (by decide)
                hFw := by rw [hGc _ (by decide)]; omega
                hdw := by rw [hOn _ (by decide)]; omega
                hsw := hbW })
    rw [mem26, sp26, eFp] at f27
    have hi27 : ∀ x : Word, 0x40000000 ≤ x.toNat → m27.mem x = m.mem x := fun x hx => by
      rw [f27 x (hiG (c := 0x6E0) (l := 16) (k := 1) (by decide) hx (by have := x.isLt; omega)),
        copyBytes_sep (sep_of_le (by rw [hOn _ (by decide)]; omega) (by have := x.isLt; omega)) (Nat.le_refl _),
        hi22 x hx]
    have hc27 : CodeIn m27.mem VKB edVerifyingKeyFromBytesCode := hc.hi hi27 (by decide) (by decide)
    have u27 : St m27.mem VKB m27 0x4E (reg m27) := ⟨by rw [pc27], rfl, fun _ => rfl⟩
    have b27 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        reg m27 q = reg m14 q := fun q hq => by
      rw [k27 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r26 q (by revert hq; revert q; decide),
        r25 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
        b22 q hq]
    have sp27' : reg m27 sp = G + BitVec.ofNat 32 0x6F0 := by rw [sp27, sp26]
    obtain ⟨m28, d28, u28⟩ := u27.aluImm hc27 vkb_at_4e (off' := 0x50) (by decide)
    have s0_28 : reg m28 (8 : Fin 32) = out := by rw [u28.upd_ne u27.zero _ (by decide), b27 _ (by decide), s0_14]
    obtain ⟨m29, d29, u29⟩ := u28.self.sw hc27 vkb_at_50 (off' := 0x54) (by decide) (by rw [s0_28]; exact hOk 0x24 rfl)
    rw [s0_28, u28.upd_ne u27.zero _ (by decide), b27 _ (by decide), vS] at u29
    have hc29 := hc27.store32 (v := memLoad32 m8.mem (G + BitVec.ofNat 32 0x700)) (sOCk 0x24 (by decide))
    obtain ⟨m30, d30, u30⟩ := u29.jump hc29 vkb_at_54 (off' := 0x58) (by decide) (by rw [u29.pc]; decide)
    obtain ⟨m31, d31, u31⟩ := u30.sw hc29 vkb_at_58 (off' := 0x5A) (by decide)
      (by rw [u28.upd_ne u27.zero _ (by decide), b27 _ (by decide), s0_14, add_lit_zero]; exact hout)
    rw [u28.upd_ne u27.zero _ (by decide), b27 _ (by decide), s0_14, add_lit_zero, u28.upd_eq (by decide), u27.zero] at u31
    have hc31 := hc29.store32 (v := aluEval .add 0 0) sOC
    obtain ⟨m', c', pc', sp', s0', s1', s2', ra', oth', mem'⟩ := vkb_epi hc31 u31.self
      (by rw [u31.regs, u28.upd_ne u27.zero _ (by decide), sp27']) hFal
    obtain ⟨Mf, hMf⟩ : ∃ Mf, memStore32 (memStore32 m27.mem (out + BitVec.ofNat 32 0x24) (memLoad32 m8.mem (G + BitVec.ofNat 32 0x700)))
        out (aluEval .add 0 0) = Mf := ⟨_, rfl⟩
    rw [hMf] at mem' pc' ra' s0' s1' s2'
    -- every byte apart from the writes after `decompress` keeps its `m8` value
    have back : ∀ x, Sep (G + BitVec.ofNat 32 0x6E0) 16 x 1 → Sep (out + BitVec.ofNat 32 4) 32 x 1 →
        Sep (out + BitVec.ofNat 32 0x34) 0x90 x 1 → Sep (out + BitVec.ofNat 32 0x28) 12 x 1 → Sep out 4 x 1 →
        Sep (out + BitVec.ofNat 32 0x24) 4 x 1 → Mf x = m8.mem x := fun x h1 h2 h3 h4 h5 h6 => by
      rw [← hMf, st32_frame h5, st32_frame h6, f27 x h1, copyBytes_sep h2 (Nat.le_refl _), f22 x h1,
        copyBytes_sep h3 (Nat.le_refl _), I3 x h4]
    have oo : ∀ {c d k : Nat} {l : Nat}, c + l ≤ d ∨ d + k ≤ c → c + l ≤ 0xC4 → d + k ≤ 0xC4 →
        Sep (out + BitVec.ofNat 32 c) l (out + BitVec.ofNat 32 d) k := fun {c d k l} h h1 h2 =>
      sep_offsets out h (by omega) (by omega)
    have oo0 : ∀ {d k : Nat}, 4 ≤ d → d + k ≤ 0xC4 → Sep out 4 (out + BitVec.ofNat 32 d) k := fun {d k} h1 h2 => by
      have := oo (c := 0) (l := 4) (d := d) (k := k) (Or.inl h1) (by decide) h2; rwa [add_ofNat_zero] at this
    have gO : ∀ {c l d k : Nat}, c + l ≤ 0x7B0 → d + k ≤ 0xC4 → Sep (G + BitVec.ofNat 32 c) l (out + BitVec.ofNat 32 d) k :=
      fun {c l d k} h1 h2 => ((sOG.sub (c := d) (l := k) h2).subR (c := c) (l := l) h1).symm
    have hMx : ∀ c, 0x7A0 ≤ c → c < 0x7B0 → Mf (G + BitVec.ofNat 32 c) = m8.mem (G + BitVec.ofNat 32 c) := fun c h1 h2 =>
      back _ (offs (Or.inl (by omega)) (by decide) (by omega)) (gO (by omega) (by decide)).symm
        (gO (by omega) (by decide)).symm (gO (by omega) (by decide)).symm
        (by have := (gO (c := c) (l := 1) (d := 0) (k := 4) (by omega) (by decide)).symm; rwa [add_ofNat_zero] at this)
        (gO (by omega) (by decide)).symm
    have pt : ∀ c, 0x34 ≤ c → c < 0xC4 → Mf (out + BitVec.ofNat 32 c) = m8.mem (G + BitVec.ofNat 32 (0x6DC + c)) :=
      fun c h1 h2 => by
        rw [← hMf, st32_frame (oo0 (by omega) (by omega)), st32_frame (oo (Or.inl (by omega)) (by decide) (by omega)),
          f27 _ (gO (by decide) (by omega)), copyBytes_sep (oo (Or.inl (by omega)) (by decide) (by omega)) (Nat.le_refl _),
          f22 _ (gO (by decide) (by omega)),
          show out + BitVec.ofNat 32 c = out + BitVec.ofNat 32 0x34 + BitVec.ofNat 32 (c - 0x34) by
            rw [spk]; exact congrArg (fun k => out + BitVec.ofNat 32 k) (by omega),
          cb_in (by omega) (by decide), spk, I3 _ (gO (by omega) (by decide)).symm]
        exact congrArg (fun k => m8.mem (G + BitVec.ofNat 32 k)) (by omega)
    have ptA : ∀ c, 0x28 ≤ c → c < 0x34 → Mf (out + BitVec.ofNat 32 c) = M3 (out + BitVec.ofNat 32 c) := fun c h1 h2 => by
      rw [← hMf, st32_frame (oo0 (by omega) (by omega)), st32_frame (oo (Or.inl (by omega)) (by decide) (by omega)),
        f27 _ (gO (by decide) (by omega)), copyBytes_sep (oo (Or.inl (by omega)) (by decide) (by omega)) (Nat.le_refl _),
        f22 _ (gO (by decide) (by omega)), copyBytes_sep (oo (Or.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _)]
    have ptB : ∀ i, i < 32 → Mf (out + BitVec.ofNat 32 4 + BitVec.ofNat 32 i) = m.mem (bp + BitVec.ofNat 32 i) :=
      fun i hi => by
        rw [← hMf, spk, st32_frame (oo0 (by omega) (by omega)), st32_frame (oo (Or.inr (by omega)) (by decide) (by omega)),
          f27 _ (gO (by decide) (by omega)), ← spk, cb_in hi (by decide),
          f22 _ ((sBG.sub (c := i) (l := 1) hi).subR (c := 0x6E0) (l := 16) (by decide)).symm,
          copyBytes_sep ((sBO.sub (c := i) (l := 1) hi).subR (c := 0x34) (l := 0x90) (by decide)).symm (Nat.le_refl _),
          I3 _ ((sBO.sub (c := i) (l := 1) hi).subR (c := 0x28) (l := 12) (by decide)).symm,
          I8 _ (sBG.sub (c := i) (l := 1) hi).symm]
    have m3a : memLoad32 M3 (out + BitVec.ofNat 32 0x28) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x704) := by
      rw [← hM3]
      exact (memLoad32_store32_sep (oo (c := 0x30) (l := 4) (d := 0x28) (k := 4) (Or.inr (by decide)) (by decide)
        (by decide))).trans ((memLoad32_store32_sep (oo (c := 0x2C) (l := 4) (d := 0x28) (k := 4) (Or.inr (by decide))
        (by decide) (by decide))).trans (memLoad32_store32_same _ _ _))
    have m3b : memLoad32 M3 (out + BitVec.ofNat 32 0x2C) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x708) := by
      rw [← hM3]
      exact (memLoad32_store32_sep (oo (c := 0x30) (l := 4) (d := 0x2C) (k := 4) (Or.inr (by decide)) (by decide)
        (by decide))).trans (memLoad32_store32_same _ _ _)
    have m3c : memLoad32 M3 (out + BitVec.ofNat 32 0x30) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x70C) := by
      rw [← hM3]; exact memLoad32_store32_same _ _ _
    have ldA : ∀ c, 0x28 ≤ c → c + 4 ≤ 0x34 → memLoad32 Mf (out + BitVec.ofNat 32 c) = memLoad32 M3 (out + BitVec.ofNat 32 c) :=
      fun c h1 h2 => vk_ld2 fun j hj => by rw [spk]; exact ptA _ (by omega) (by omega)
    have ldP : ∀ c d, 0x34 ≤ c → c + 4 ≤ 0xC4 → d = 0x6DC + c →
        memLoad32 Mf (out + BitVec.ofNat 32 c) = memLoad32 m8.mem (G + BitVec.ofNat 32 d) :=
      fun c d h1 h2 hd => vk_ld2 fun j hj => by
        rw [spk, spk, pt _ (by omega) (by omega)]; exact congrArg (fun k => m8.mem (G + BitVec.ofNat 32 k)) (by omega)
    have fP : ∀ c d, 0x34 ≤ c → c + 40 ≤ 0xC4 → d = 0x6DC + c →
        feW Mf (out + BitVec.ofNat 32 c) = feW m8.mem (G + BitVec.ofNat 32 d) :=
      fun c d h1 h2 hd => feW_eq2 fun i hi => by rw [spk, spk]; exact ldP _ _ (by omega) (by omega) (by omega)
    have hX' : feW m8.mem (G + BitVec.ofNat 32 0x700) = X := by rw [← hX, spk]
    have hY' : feW m8.mem (G + BitVec.ofNat 32 0x728) = Y := by rw [← hY, spk, spk]
    have hZ' : feW m8.mem (G + BitVec.ofNat 32 0x750) = Z := by rw [← hZ, spk, spk]
    have hT' : feW m8.mem (G + BitVec.ofNat 32 0x778) = T := by rw [← hT, spk, spk]
    have fX : feW Mf (out + BitVec.ofNat 32 0x24) = X := by
      rw [← hX']
      refine feW_eq2 fun i hi => ?_
      rw [spk, spk]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i by omega) with rfl | rfl | rfl | rfl | h4
      · show memLoad32 Mf (out + BitVec.ofNat 32 0x24) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x700)
        rw [← hMf, memLoad32_store32_sep (oo0 (by decide) (by decide))]
        exact memLoad32_store32_same _ _ _
      · show memLoad32 Mf (out + BitVec.ofNat 32 0x28) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x704)
        rw [ldA _ (by decide) (by decide), m3a]
      · show memLoad32 Mf (out + BitVec.ofNat 32 0x2C) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x708)
        rw [ldA _ (by decide) (by decide), m3b]
      · show memLoad32 Mf (out + BitVec.ofNat 32 0x30) = memLoad32 m8.mem (G + BitVec.ofNat 32 0x70C)
        rw [ldA _ (by decide) (by decide), m3c]
      · exact ldP _ _ (by omega) (by omega) (by omega)
    have vra : memLoad32 Mf (G + BitVec.ofNat 32 0x6F0 + 0xBC) = reg m ra := slotv ra (BitVec.ofNat 32 0xBC) (by decide) _ hMx
    have vs0 : memLoad32 Mf (G + BitVec.ofNat 32 0x6F0 + 0xB8) = reg m (8 : Fin 32) :=
      slotv _ (BitVec.ofNat 32 0xB8) (by decide) _ hMx
    have vs1 : memLoad32 Mf (G + BitVec.ofNat 32 0x6F0 + 0xB4) = reg m (9 : Fin 32) :=
      slotv _ (BitVec.ofNat 32 0xB4) (by decide) _ hMx
    have vs2 : memLoad32 Mf (G + BitVec.ofNat 32 0x6F0 + 0xB0) = reg m (18 : Fin 32) :=
      slotv _ (BitVec.ofNat 32 0xB0) (by decide) _ hMx
    refine ⟨m', .cons d1 (c3.trans (.cons d4 (.cons d5 (.cons d6 (c7.trans (c8.trans (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (c21.trans (c22.trans (.cons d23 (.cons d24 (.cons d25 (c26.trans (c27.trans (.cons d28 (.cons d29 (.cons d30 (.cons d31 c'))))))))))))))))))))))))))))), ?_, by rw [sp', eS'], fun q hq => ?_,
      ⟨?_, ?_, by rw [mem']; exact fX, by rw [mem', fP 0x4C 0x728 (by decide) (by decide) rfl, hY'],
        by rw [mem', fP 0x74 0x750 (by decide) (by decide) rfl, hZ'], by rw [mem', fP 0x9C 0x778 (by decide) (by decide) rfl, hT']⟩,
      fun x hx hy => ?_⟩
    · rw [pc', vra, hra, hret]
    · have hq' : q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
          q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
      rcases hq' with rfl | rfl | rfl | rfl | h
      · rw [ra', vra]
      · rw [s0', vs0]
      · rw [s1', vs1]
      · rw [s2', vs2]
      · rw [oth' q (by revert h; revert q; decide) (by revert h; revert q; decide) (by revert h; revert q; decide)
          (by revert h; revert q; decide) (by revert h; revert q; decide), u31.regs,
          u28.upd_ne u27.zero q (by revert h; revert q; decide), b27 q (by revert h; revert q; decide),
          r14 q (by revert h; revert q; decide) (by revert h; revert q; decide) (by revert h; revert q; decide)
            (by revert h; revert q; decide), kq q h]
    · show memLoad32 m'.mem out = 0
      rw [mem', ← hMf, memLoad32_store32_same]; rfl
    · rw [mem']
      unfold memBytes
      exact List.map_congr_left fun i hi => by rw [ptB i (List.mem_range.mp hi)]
    · rw [mem', back x (inG (by decide) hx) (hy.sub (by decide)) (hy.sub (by decide)) (hy.sub (by decide))
        (sep_pre hy (by decide)) (hy.sub (by decide)), I8 x hx]

end C3.RV32
