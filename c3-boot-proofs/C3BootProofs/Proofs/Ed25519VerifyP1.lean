import C3BootProofs.Proofs.Ed25519VerifyWrap
import C3BootProofs.Image.BootloaderData7

/-!
# `ed25519_verify`, offsets 0x40 to 0x7E: the checks before decoding

The function rejects the signature unless `s`, its last 32 bytes, is
below the group order (`less_than_le` against the 32 bytes at
`edOrderAddress`), and `ed25519_public_key_ok` accepts both the key and `R`,
the signature's first 32 bytes.
-/

namespace C3.RV32

open C3.Image

/-- `s` below the group order. -/
def evLt (M : Word → BitVec 8) (sig : Word) : Bool :=
  ltLEb (memBytes M (sig + BitVec.ofNat 32 32) 32) (memBytes M (BitVec.ofNat 32 (img% edOrderAddress)) 32) 32

/-- The checks of offsets 0x40 to 0x7E: `s` below the group order, and the
key and `R` accepted. -/
def evChecks (M : Word → BitVec 8) (pk sig : Word) : Bool :=
  evLt M sig && evPk M (memBytes M pk 32) && evPk M (memBytes M sig 32)

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

theorem EvCtx.sig0 (C : EvCtx M0 F pk sig msg len) : Sep sig 32 (evG F) 0x20B0 := by
  have := C.sSig.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this

theorem EvCtx.sig32 (C : EvCtx M0 F pk sig msg len) : Sep (sig + BitVec.ofNat 32 32) 32 (evG F) 0x20B0 :=
  C.sSig.sub (by decide)

/-- The moves at offsets 0x40 to 0x56. -/
def evB40 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a3, .alu .add (18 : Fin 32) x0 a2, .alu .add (21 : Fin 32) x0 a1,
   .alu .add (9 : Fin 32) x0 a0, .aluImm .add (19 : Fin 32) a3 0x20, .lui a1 0x3FCC4000, .aluImm .add a1 a1 0x178,
   .alu .add a0 x0 (19 : Fin 32)]

theorem evB40_end : blockEnd ed25519VerifyCode 0x40 evB40 = some 0x56 :=
  blockEnd_cons' ev_at_40 rfl (blockEnd_cons' ev_at_42 rfl (blockEnd_cons' ev_at_44 rfl (blockEnd_cons' ev_at_46 rfl
    (blockEnd_cons' ev_at_48 rfl (blockEnd_cons' ev_at_4c rfl (blockEnd_cons' ev_at_50 rfl
      (blockEnd_cons' ev_at_54 rfl rfl)))))))

theorem bEnd1 {code : List Nat} {off off' : Nat} {i : BInstr} {l : Word} (h : fetchRel code off = some (i.toInstr, l))
    (hn : off + l.toNat = off') : blockEnd code off [i] = some off' :=
  blockEnd_cons' h hn rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- At `o0`: `mv a0, r`, a call of `ed25519_public_key_ok` on the 32 bytes
at `p`, and `beqz a0` to the epilogue. -/
theorem ev_pkStep (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} {o0 : Nat}
    (D : EvSt M0 Ms F r0 M n o0) {r : Fin 32} {p imm o bo : Word} (hr : reg n r = p) (hr0 : r ≠ x0)
    (f0 : fetchRel ed25519VerifyCode o0 = some ((BInstr.alu .add a0 x0 r).toInstr, 2))
    (f1 : fetchRel ed25519VerifyCode (o0 + 2) = some (.auipc ra imm, 4))
    (f2 : fetchRel ed25519VerifyCode (o0 + 2 + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 (o0 + 2) + imm + o = PKO) (hoff : (o0 + 2 + 8) % 2 = 0)
    (f3 : fetchRel ed25519VerifyCode (o0 + 2 + 8) = some (.branch .beq a0 x0 bo, 4))
    (hT : BitVec.ofNat 32 (o0 + 2 + 8) + bo = BitVec.ofNat 32 0x100A) {o1 : Nat} (hn : o0 + 2 + 8 + 4 = o1)
    (sP : Sep p 32 (evG F) 0x20B0) (hp : p.toNat + 32 < 2 ^ 32) :
    ∃ n' M', Steps n n' ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (evPk M0 (memBytes M0 p 32) = true → EvSt M0 Ms F r0 M' n' o1) ∧
      (evPk M0 (memBytes M0 p 32) = false → EvSt M0 Ms F r0 M' n' 0x100A ∧ reg n' a0 = 0) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := o0 + 2) [.alu .add a0 x0 r] (bEnd1 f0 rfl) ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r1 : ∀ q : Fin 32, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [hr1]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D.st.zero
  have va0 : reg n1 a0 = p := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D.st.zero, hr]; exact BitVec.zero_add _
  obtain ⟨n2, c2, D2, k2, a02⟩ := D1.pkOk C f1 f2 hb hoff va0 sP hp
  obtain ⟨n3, c3, k3, T3, F3⟩ := D2.br0 C f3 hT hn a02
  refine ⟨n3, n2.mem, c1.trans (c2.trans c3), fun q hq => by
    rw [k3, k2 q hq, r1 q (by revert hq; revert q; decide)], T3, fun h => ⟨F3 h, by rw [k3, a02, h]; rfl⟩⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0x40: the moves and `less_than_le`, to offset 0x62 when
`s` is below the group order and to the epilogue with `a0 = 0` when not. -/
theorem ev_lt (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x40)
    (ha0 : reg n a0 = pk) (ha1 : reg n a1 = msg) (ha2 : reg n a2 = BitVec.ofNat 32 len) (ha3 : reg n a3 = sig) :
    ∃ n', Steps n n' ∧ (evLt M0 sig = false → EvSt M0 Ms F r0 M n' 0x100A ∧ reg n' a0 = 0) ∧
      (evLt M0 sig = true → EvSt M0 Ms F r0 M n' 0x62) ∧ reg n' 8 = sig ∧
        reg n' 18 = BitVec.ofNat 32 len ∧ reg n' 21 = msg ∧ reg n' 9 = pk ∧ reg n' 19 = sig + BitVec.ofNat 32 32 := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C evB40 evB40_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte])
  have v8 : reg n1 8 = sig := by
    rw [hr1]; simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte]; rw [ha3]; exact BitVec.zero_add _
  have v18 : reg n1 18 = BitVec.ofNat 32 len := by
    rw [hr1]; simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte]; rw [ha2]; exact BitVec.zero_add _
  have v21 : reg n1 21 = msg := by
    rw [hr1]; simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte]; rw [ha1]; exact BitVec.zero_add _
  have v9 : reg n1 9 = pk := by
    rw [hr1]; simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte]; rw [ha0]; exact BitVec.zero_add _
  have v19 : reg n1 19 = sig + BitVec.ofNat 32 32 := by
    rw [hr1]; simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte]; rw [ha3]; rfl
  have va0 : reg n1 a0 = sig + BitVec.ofNat 32 32 := by
    rw [hr1]; simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte]; rw [ha3]; exact BitVec.zero_add _
  have va1 : reg n1 a1 = BitVec.ofNat 32 (img% edOrderAddress) := by
    rw [hr1]; simp +decide only [evB40, runBlock, BInstr.run, upd, ↓reduceIte]
  obtain ⟨n2, c2, D2, k2, a02⟩ := D1.ltLe C ev_at_56 ev_at_5a (by decide) (by decide) va0 va1
  rw [D1.bytesOut C.sig32, D1.bytesRo C (by decide) (by decide)] at a02
  change reg n2 a0 = if evLt M0 sig then 1 else 0 at a02
  have q2 : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 21] → reg n2 q = reg n1 q := fun q hq =>
    k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨n3, c3, k3, T3, F3⟩ := D2.br0 C (offT := 0x100A) (off' := 0x62) ev_at_5e (by decide) rfl a02
  refine ⟨n3, c1.trans (c2.trans c3), fun h => ⟨F3 h, by rw [k3, a02, show evLt M0 sig = false from h]; rfl⟩, T3,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [k3, q2 _ (by decide), v8]
  · rw [k3, q2 _ (by decide), v18]
  · rw [k3, q2 _ (by decide), v21]
  · rw [k3, q2 _ (by decide), v9]
  · rw [k3, q2 _ (by decide), v19]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0x40: the three checks, to offset 0x7E when they pass and
to the epilogue with `a0 = 0` when one fails. -/
theorem ev_chk (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x40)
    (ha0 : reg n a0 = pk) (ha1 : reg n a1 = msg) (ha2 : reg n a2 = BitVec.ofNat 32 len) (ha3 : reg n a3 = sig) :
    ∃ n' M', Steps n n' ∧ (evChecks M0 pk sig = false → EvSt M0 Ms F r0 M' n' 0x100A ∧ reg n' a0 = 0) ∧
      (evChecks M0 pk sig = true → EvSt M0 Ms F r0 M' n' 0x7E ∧ reg n' 8 = sig ∧
        reg n' 18 = BitVec.ofNat 32 len ∧ reg n' 21 = msg ∧ reg n' 9 = pk ∧ reg n' 19 = sig + BitVec.ofNat 32 32) := by
  obtain ⟨n1, c1, F1, T1, v8, v18, v21, v9, v19⟩ := ev_lt C D ha0 ha1 ha2 ha3
  have e : evChecks M0 pk sig = (evLt M0 sig && evPk M0 (memBytes M0 pk 32) && evPk M0 (memBytes M0 sig 32)) := rfl
  cases h1 : evLt M0 sig with
  | false =>
    refine ⟨n1, M, c1, fun _ => F1 h1, fun h => ?_⟩
    rw [e, h1] at h; cases h
  | true =>
    obtain ⟨n4, M4, c4, k4, T4, F4⟩ := ev_pkStep C (T1 h1) (r := 9) (p := pk) v9 (by decide)
      ev_at_62 ev_at_64 ev_at_68 (by decide) (by decide) ev_at_6c (by decide) (o1 := 0x70) rfl C.sPk C.hpk
    cases h2 : evPk M0 (memBytes M0 pk 32) with
    | false =>
      refine ⟨n4, M4, c1.trans c4, fun _ => F4 h2, fun h => ?_⟩
      rw [e, h1, h2] at h; cases h
    | true =>
      obtain ⟨n5, M5, c5, k5, T5, F5⟩ := ev_pkStep C (T4 h2) (r := 8) (p := sig) (by rw [k4 8 (by decide), v8])
        (by decide) ev_at_70 ev_at_72 ev_at_76 (by decide) (by decide) ev_at_7a (by decide) (o1 := 0x7E) rfl C.sig0
        (by have := C.hsig; omega)
      have q5 : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 21] → reg n5 q = reg n1 q := fun q hq => by
        rw [k5 q (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide)]
      cases h3 : evPk M0 (memBytes M0 sig 32) with
      | false =>
        refine ⟨n5, M5, c1.trans (c4.trans c5), fun _ => F5 h3, fun h => ?_⟩
        rw [e, h1, h2, h3] at h; cases h
      | true =>
        refine ⟨n5, M5, c1.trans (c4.trans c5), fun h => ?_, fun _ => ⟨T5 h3, ?_, ?_, ?_, ?_, ?_⟩⟩
        · rw [e, h1, h2, h3] at h; cases h
        · rw [q5 _ (by decide), v8]
        · rw [q5 _ (by decide), v18]
        · rw [q5 _ (by decide), v21]
        · rw [q5 _ (by decide), v9]
        · rw [q5 _ (by decide), v19]

end

end C3.RV32
