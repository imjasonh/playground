import C3BootProofs.Proofs.Sha512Update

/-!
# `<sha2::Sha512 as Digest>::update::<&[u8; 32]>`, as compiled

The function sets the length to 32 and tail-calls SHA-512's `update`, which
`sha512Update_correct` proves.
-/

namespace C3.RV32.S5U

open C3.Image C3.RV32

section
set_option maxRecDepth 20000
theorem s5a_at_0 : fetchRel sha512UpdateArr32Code 0x0 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem s5a_at_4 : fetchRel sha512UpdateArr32Code 0x4 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem s5a_at_8 : fetchRel sha512UpdateArr32Code 0x8 = some (.jalr x0 (6 : Fin 32) 0x8, 4) := by decide
end

set_option maxRecDepth 20000 in
/-- **The compiled `Digest::update` of SHA-512 on a 32-byte array.** Called
with the hasher at `S` holding `msg` and the array at `D`, it leaves the
hasher holding `msg` followed by the array's 32 bytes, as
`sha512Update_correct` says for `n = 32`. -/
theorem sha512UpdateArr32_correct (m : Machine) {S D sp0 retAddr : Word} {msg : Bytes}
    (hc : CodeIn m.mem (BitVec.ofNat 32 sha512UpdateArr32Address) sha512UpdateArr32Code)
    (E : UpdEnv m.mem S D sp0 32) (hpc : m.pc = BitVec.ofNat 32 sha512UpdateArr32Address)
    (ha0 : reg m a0 = S) (ha1 : reg m a1 = D) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (H : Hasher5At m.mem S msg) (hlen : msg.length + 32 < 2 ^ 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ ra → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
        r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
        r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → reg m' r = reg m r) ∧
      Hasher5At m'.mem S (msg ++ memBytes m.mem D 32) ∧
      ∀ x, Sep (sp0 + 0xFFFFFC50) 0x3B0 x 1 → Sep S 0xD0 x 1 → m'.mem x = m.mem x := by
  let B := BitVec.ofNat 32 sha512UpdateArr32Address
  have s0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp [B], rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc s5a_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.auipc hc s5a_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.self.jalr hc s5a_at_8
  have pc3' : n3.pc = BitVec.ofNat 32 sha512UpdateAddress := by
    rw [pc3, u2.regs]; simp +decide only [upd, ↓reduceIte]; decide
  have k3 : ∀ q, q ≠ t1 → q ≠ a2 → reg n3 q = reg m q := fun q h6 h2 => by
    rw [regs3, u2.regs, updz u1.self.zero h6, u1.regs, updz hz h2]
  have a2_3 : reg n3 a2 = BitVec.ofNat 32 32 := by
    rw [regs3, u2.regs, upd_ne (by decide) (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [hz]; rfl
  obtain ⟨m', c', pc', sp', K', H', fr'⟩ := sha512Update_correct n3 (by rw [mem3]; exact E) pc3'
    (by rw [k3 a0 (by decide) (by decide), ha0]) (by rw [k3 a1 (by decide) (by decide), ha1]) a2_3
    (by rw [k3 ra (by decide) (by decide), hra]) hret (by rw [k3 sp (by decide) (by decide), hsp])
    (by rw [mem3]; exact H) (by decide) hlen
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 c')), pc', sp',
    fun r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2 => ?_, ?_, fun x hx hy => ?_⟩
  · rw [K' r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2, k3 r q6 q12]
  · rw [mem3] at H'; exact H'
  · rw [fr' x hx hy, mem3]

end C3.RV32.S5U
