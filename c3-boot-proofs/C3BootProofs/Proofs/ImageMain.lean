import C3BootProofs.Proofs.ImageCalls
import C3BootProofs.Proofs.ImageDecode

/-!
# `image::parse`: the frame invariant and the error path

`IInv` is what holds at every point of `image::parse` after its prologue:
memory outside the stack is unchanged, the saved registers' slots hold the
caller's registers, the reader at `G + 0x18` points at the header buffer,
`sp`, `s0`, and `s1` hold the frame, the result address, and the image
length, and every register `image::parse` never writes holds its value from
entry. `IInv.mem` keeps it across any store outside the reader and the slots.
`ip_errTail` finishes every error path from offset 0xBC.
-/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 20000

/-- The registers `image::parse` or its callees write. -/
abbrev ipClob : List (Fin 32) :=
  [a0, a1, a2, a3, a4, a5, a6, a7, t0, t1, ra, sp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]

/-- The registers `image::parse` leaves changed when it returns. -/
abbrev ipTmp : List (Fin 32) := [a0, a1, a2, a3, a4, a5, a6, a7, t0, t1]

structure IInv (R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (Mx : Word → BitVec 8) (g : Fin 32 → Word) : Prop where
  outside : ∀ x, Sep R 0x190 x 1 → Mx x = M0 x
  slots : ∀ p, p ∈ ipSlots → memLoad32 Mx (G + BitVec.ofNat 32 p.2) = f0 p.1
  rdp : memLoad32 Mx (G + 0x18) = ptr
  rdl : memLoad32 Mx (G + 0x18 + 4) = len
  sp : g sp = G
  s0 : g s0 = out
  s1 : g s1 = ilen
  keep : ∀ r, r ∉ ipClob → g r = f0 r
  zero : g 0 = 0

namespace IInv

variable {P R G ptr len out ilen : Word} {M0 Mx My : Word → BitVec 8} {f0 g : Fin 32 → Word}

/-- `IInv` holds after any change outside the reader's pointer and length
and the slots. -/
theorem mem (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    (h : ∀ x, Sep R 0x48 x 1 → Sep (R + BitVec.ofNat 32 0x50) 0x10C x 1 → My x = Mx x) :
    IInv R G ptr len out ilen M0 f0 My g := by
  have fr : ∀ k, k < 0x160 → (k < 0x18 ∨ 0x20 ≤ k) → k < 0x12C ∨ True → True := fun _ _ _ _ => trivial
  have keepF : ∀ k, 0x18 ≤ k → k < 0x20 ∨ 0x12C ≤ k → k < 0x160 →
      My (G + BitVec.ofNat 32 k) = Mx (G + BitVec.ofNat 32 k) := fun k h1 h2 h3 => by
    rw [env.g_ofs]
    apply h
    · exact env.stack_stack 0 0x48 (0x30 + k) 1 (by omega) (by omega) (by omega) |> fun s => by
        rwa [add_ofNat_zero] at s
    · exact env.stack_stack 0x50 0x10C (0x30 + k) 1 (by omega) (by omega) (by omega)
  refine ⟨fun x hx => ?_, fun p hp => ?_, ?_, ?_, inv.sp, inv.s0, inv.s1, inv.keep, inv.zero⟩
  · rw [h x (by have := hx.sub (c := 0) (l := 0x48) (by omega); rwa [add_ofNat_zero] at this)
      (hx.sub (c := 0x50) (l := 0x10C) (by omega)), inv.outside x hx]
  · have hk : 0x12C ≤ p.2 ∧ p.2 + 4 ≤ 0x160 := by
      simp only [ipSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide⟩
    rw [← inv.slots p hp]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact keepF _ (by omega) (Or.inr (by omega)) (by omega)
  · rw [← inv.rdp]; exact memLoad32_congr fun j hj => by
      rw [show G + 0x18 = G + BitVec.ofNat 32 0x18 from rfl, add_ofNat_assoc]
      exact keepF _ (by omega) (Or.inl (by omega)) (by omega)
  · rw [← inv.rdl]; exact memLoad32_congr fun j hj => by
      rw [show G + 0x18 + 4 = G + BitVec.ofNat 32 0x1C by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact keepF _ (by omega) (Or.inl (by omega)) (by omega)

/-- `IInv` holds after a write to a register `image::parse` may clobber,
other than `sp`, `s0`, and `s1`. -/
theorem setReg (inv : IInv R G ptr len out ilen M0 f0 Mx g) {rd : Fin 32} {v : Word}
    (hrd : rd ∈ ipClob) (h1 : rd ≠ RV32.sp) (h2 : rd ≠ RV32.s0) (h3 : rd ≠ RV32.s1) :
    IInv R G ptr len out ilen M0 f0 Mx (C3.RV32.upd g rd v) := by
  have u : ∀ r, r ≠ rd → C3.RV32.upd g rd v r = g r := fun r hr => by
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [C3.RV32.upd, inv.zero]
    · simp [C3.RV32.upd, h0, hr]
  refine ⟨inv.outside, inv.slots, inv.rdp, inv.rdl, by rw [u RV32.sp (Ne.symm h1), inv.sp],
    by rw [u RV32.s0 (Ne.symm h2), inv.s0], by rw [u RV32.s1 (Ne.symm h3), inv.s1], fun r hr => ?_, ?_⟩
  · rw [u r (fun e => hr (e ▸ hrd))]; exact inv.keep r hr
  · simp [C3.RV32.upd]

end IInv

theorem ip_codes {P : Word} {M0 Mf : Word → BitVec 8} (code0 : ICode M0 P)
    (hw : ∀ k, k < ipWindowLen → Mf (ipWindow P + BitVec.ofNat 32 k) = M0 (ipWindow P + BitVec.ofNat 32 k)) :
    CodeIn Mf P imageParseCode ∧ CodeIn Mf (P + 0x16402) imageRestoreCode :=
  ⟨code0.parse.of_ipWindow 0x2AE (ip_wP P) (by decide) hw,
   code0.restore.of_ipWindow 0x166B0 (ip_wq P _ _ (by decide)) (by decide) hw⟩

/-- **`image::parse` returns**: from offset 0xC0, with the code window as at
entry, the slots holding the caller's registers, and every register
`image::parse` never writes as at entry, it returns to the caller with `sp`
restored and every register outside `ipTmp` as at entry. -/
theorem ip_final {P R G ptr len out : Word} (env : IEnv P R G ptr len out) {M0 Mf : Word → BitVec 8}
    {f0 g : Fin 32 → Word} (code0 : ICode M0 P) {n : Machine} (s : St Mf P n 0xC0 g) (hsp : g sp = G)
    (hw : ∀ k, k < ipWindowLen → Mf (ipWindow P + BitVec.ofNat 32 k) = M0 (ipWindow P + BitVec.ofNat 32 k))
    (hsl : ∀ p, p ∈ ipSlots → memLoad32 Mf (G + BitVec.ofNat 32 p.2) = f0 p.1)
    (hk : ∀ r, r ∉ ipClob → g r = f0 r) :
    ∃ n', Steps n n' ∧ n'.pc = f0 ra &&& ~~~1 ∧ n'.mem = Mf ∧ reg n' sp = G + 0x160 ∧
      ∀ r, r ∉ ipTmp → r ≠ sp → reg n' r = f0 r := by
  obtain ⟨cp, cr⟩ := ip_codes code0 hw
  obtain ⟨n', c, pc, mem, spv, sl, other⟩ := image_epilogue s cp cr env.hP hsp env.hG
  refine ⟨n', c, by rw [pc, show G + 0x15C = G + BitVec.ofNat 32 0x15C from rfl,
    hsl (ra, 0x15C) (by decide)], mem, spv, fun r hr hs => ?_⟩
  by_cases hin : ∃ p, p ∈ ipSlots ∧ r = p.1
  · obtain ⟨p, hp, rfl⟩ := hin
    rw [sl p hp, hsl p hp]
  · have hs' : ∀ p, p ∈ ipSlots → r ≠ p.1 := fun p hp e => hin ⟨p, hp, e⟩
    have ha0 : r ≠ a0 := fun e => hr (e ▸ by decide)
    have ht0 : r ≠ t0 := fun e => hr (e ▸ by decide)
    rw [other r ha0 ht0 hs hs']
    have hq : ∀ q, q ∈ ipSlots.map Prod.fst → r ≠ q := fun q hq => by
      simp only [List.mem_map] at hq; obtain ⟨p, hp, rfl⟩ := hq; exact hs' p hp
    apply hk
    simp only [ipClob, ipTmp, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    intro hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals first
      | exact hs h
      | exact hq _ (by decide) h
      | exact hr (by simp [h])

/-- From `n`, `image::parse` returns `Err(e)`: the error byte at `out`, 0xFF at
`out + 0xC`, nothing else outside the stack changed, and the caller's
registers restored. -/
def IErrDone (R G out : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word) (e : BitVec 8)
    (n : Machine) : Prop :=
  ∃ n', Steps n n' ∧ n'.pc = f0 ra &&& ~~~1 ∧ reg n' sp = G + 0x160 ∧
    (∀ r, r ∉ ipTmp → r ≠ sp → reg n' r = f0 r) ∧
    (∀ x, Sep R 0x190 x 1 → Sep out 0x110 x 1 → n'.mem x = M0 x) ∧
    n'.mem out = e ∧ n'.mem (out + 0xC) = 0xFF

section Err

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}

theorem out_ne_frame (env : IEnv P R G ptr len out) {j c : Nat} (hj : j < 0x110) (hc : c < 0x190) :
    out + BitVec.ofNat 32 j ≠ R + BitVec.ofNat 32 c := fun h =>
  env.hOS j hj c hc h

theorem ip_errC0 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {n : Machine} {e : BitVec 8}
    (s : St (memStore8 (memStore8 Mx out e) (out + 0xC) 0xFF) P n 0xC0 g) :
    IErrDone R G out M0 f0 e n := by
  have offO : ∀ x, Sep out 0x110 x 1 → x ≠ out ∧ x ≠ out + 0xC := fun x hx =>
    ⟨fun h => hx 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero, h]),
     fun h => hx 0xC (by omega) 0 (by omega) (by rw [add_ofNat_zero, h]; rfl)⟩
  have Mf_eq : ∀ x, Sep out 0x110 x 1 → memStore8 (memStore8 Mx out e) (out + 0xC) 0xFF x = Mx x :=
    fun x hx => by rw [memStore8_ne (offO x hx).2, memStore8_ne (offO x hx).1]
  have wsep : ∀ k, k < ipWindowLen → Sep out 0x110 (ipWindow P + BitVec.ofNat 32 k) 1 :=
    fun k hk => env.hOW.subR (c := k) (l := 1) (by omega)
  have wR : ∀ k, k < ipWindowLen → Sep R 0x190 (ipWindow P + BitVec.ofNat 32 k) 1 :=
    fun k hk => env.hSW.subR (c := k) (l := 1) (by omega)
  obtain ⟨n', c, pc, mem, spv, regs⟩ := ip_final env code0 s inv.sp
    (fun k hk => by rw [Mf_eq _ (wsep k hk), inv.outside _ (wR k hk)])
    (fun p hp => by
      rw [← inv.slots p hp]
      apply memLoad32_congr; intro j hj
      apply Mf_eq
      have hk : p.2 + 4 ≤ 0x160 := by
        simp only [ipSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [add_ofNat_assoc, env.g_ofs]
      exact (env.hOS.subR (c := 0x30 + (p.2 + j)) (l := 1) (by omega)))
    inv.keep
  refine ⟨n', c, pc, spv, regs, fun x hR hO => ?_, ?_, ?_⟩
  · rw [mem, Mf_eq x hO, inv.outside x hR]
  · have hne : out ≠ out + 0xC := by
      have := add_ofNat_ne out (c := 0) (d := 0xC) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [mem, memStore8_ne hne]
    exact memStore8_same _ _ _
  · rw [mem]; exact memStore8_same _ _ _

theorem IInv.win (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g) :
    ∀ k, k < ipWindowLen → Mx (ipWindow P + BitVec.ofNat 32 k) = M0 (ipWindow P + BitVec.ofNat 32 k) :=
  fun k hk => inv.outside _ (env.hSW.subR (c := k) (l := 1) (by omega))

/-- A byte stored in the result leaves the code window alone. -/
theorem win_out8 (env : IEnv P R G ptr len out) {M : Word → BitVec 8} {j : Nat} (hj : j < 0x110)
    {v : BitVec 8} (h : ∀ k, k < ipWindowLen → M (ipWindow P + BitVec.ofNat 32 k) = M0 (ipWindow P + BitVec.ofNat 32 k)) :
    ∀ k, k < ipWindowLen →
      memStore8 M (out + BitVec.ofNat 32 j) v (ipWindow P + BitVec.ofNat 32 k) = M0 (ipWindow P + BitVec.ofNat 32 k) :=
  fun k hk => by
    rw [memStore8_ne (fun e => env.hOW j hj k hk e.symm), h k hk]

theorem ip_errBC (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {n : Machine} {e : BitVec 8}
    (s : St (memStore8 Mx out e) P n 0xBC g) (ha1 : g a1 = 0xFFFFFFFF) :
    IErrDone R G out M0 f0 e n := by
  have hw := win_out8 env (j := 0) (by omega) (v := e) (inv.win env)
  rw [add_ofNat_zero] at hw
  obtain ⟨n1, d1, u1⟩ := s.sb (ip_codes code0 hw).1 ip_at_bc (off' := 0xC0) (by decide)
  rw [inv.s0, ha1, show (0xFFFFFFFF : Word).extractLsb' 0 8 = 0xFF from rfl] at u1
  obtain ⟨n', c, rest⟩ := ip_errC0 env code0 inv u1
  exact ⟨n', .cons d1 c, rest⟩

theorem ip_errA0 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {n : Machine} {e : BitVec 8}
    (s : St (memStore8 Mx out e) P n 0xA0 g) (ha0 : g a0 = 0xFFFFFFFF) :
    IErrDone R G out M0 f0 e n := by
  have hw := win_out8 env (j := 0) (by omega) (v := e) (inv.win env)
  rw [add_ofNat_zero] at hw
  obtain ⟨n1, d1, u1⟩ := s.sb (ip_codes code0 hw).1 ip_at_a0 (off' := 0xA4) (by decide)
  rw [inv.s0, ha0, show (0xFFFFFFFF : Word).extractLsb' 0 8 = 0xFF from rfl] at u1
  have hw2 := win_out8 env (j := 0xC) (by omega) (v := 0xFF) hw
  obtain ⟨n2, d2, u2⟩ := u1.jump (ip_codes code0 hw2).1 ip_at_a4 (off' := 0xC0) (by decide)
    (by rw [u1.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xC0 (by decide)))
  obtain ⟨n', c, rest⟩ := ip_errC0 env code0 inv u2
  exact ⟨n', .cons d1 (.cons d2 c), rest⟩

theorem minus1 (g : Fin 32 → Word) (hz : g 0 = 0) : aluEval .add (g x0) 0xFFFFFFFF = 0xFFFFFFFF := by
  show g 0 + _ = _; rw [hz]; rfl

/-- Offset 0xB6: the error in the low byte of `a0`. -/
theorem ip_errB6 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {n : Machine} {e : BitVec 8}
    (s : St Mx P n 0xB6 g) (he : (g a0).extractLsb' 0 8 = e) : IErrDone R G out M0 f0 e n := by
  have hc := (ip_codes code0 (inv.win env)).1
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc ip_at_b6 (off' := 0xB8) (by decide)
  rw [minus1 g inv.zero] at u1
  have inv1 := inv.setReg (rd := a1) (v := 0xFFFFFFFF) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sb hc ip_at_b8 (off' := 0xBC) (by decide)
  rw [inv1.s0, add_lit_zero, show upd g a1 0xFFFFFFFF a0 = g a0 by simp +decide [upd], he] at u2
  obtain ⟨n', c, rest⟩ := ip_errBC env code0 inv1 u2 (by simp +decide [upd])
  exact ⟨n', .cons d1 (.cons d2 c), rest⟩

/-- Offset 0x418: the error in the low byte of `a6`. -/
theorem ip_err418 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {n : Machine} {e : BitVec 8}
    (s : St Mx P n 0x418 g) (he : (g a6).extractLsb' 0 8 = e) : IErrDone R G out M0 f0 e n := by
  have hc := (ip_codes code0 (inv.win env)).1
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc ip_at_418 (off' := 0x41A) (by decide)
  rw [minus1 g inv.zero] at u1
  have inv1 := inv.setReg (rd := a1) (v := 0xFFFFFFFF) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sb hc ip_at_41a (off' := 0x41E) (by decide)
  rw [inv1.s0, add_lit_zero, show upd g a1 0xFFFFFFFF (16 : Fin 32) = g a6 by simp +decide [upd], he] at u2
  have hw := win_out8 env (j := 0) (by omega) (v := e) (inv.win env)
  rw [add_ofNat_zero] at hw
  obtain ⟨n3, d3, u3⟩ := u2.jump (ip_codes code0 hw).1 ip_at_41e (off' := 0xBC) (by decide)
    (by rw [u2.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xBC (by decide)))
  obtain ⟨n', c, rest⟩ := ip_errBC env code0 inv1 u3 (by simp +decide [upd])
  exact ⟨n', .cons d1 (.cons d2 (.cons d3 c)), rest⟩

/-- Offset 0x9A: the error in the low byte of `s2`. -/
theorem ip_err9A (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {n : Machine} {e : BitVec 8}
    (s : St Mx P n 0x9A g) (he : (g s2).extractLsb' 0 8 = e) : IErrDone R G out M0 f0 e n := by
  have hc := (ip_codes code0 (inv.win env)).1
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc ip_at_9a (off' := 0x9C) (by decide)
  rw [minus1 g inv.zero] at u1
  have inv1 := inv.setReg (rd := a0) (v := 0xFFFFFFFF) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sb hc ip_at_9c (off' := 0xA0) (by decide)
  rw [inv1.s0, add_lit_zero, show upd g a0 0xFFFFFFFF s2 = g s2 by simp +decide [upd], he] at u2
  obtain ⟨n', c, rest⟩ := ip_errA0 env code0 inv1 u2 (by simp +decide [upd])
  exact ⟨n', .cons d1 (.cons d2 c), rest⟩

/-- Offset 0xF2: the error in the low byte of `s3`. -/
theorem ip_errF2 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {n : Machine} {e : BitVec 8}
    (s : St Mx P n 0xF2 g) (he : (g s3).extractLsb' 0 8 = e) : IErrDone R G out M0 f0 e n := by
  have hc := (ip_codes code0 (inv.win env)).1
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc ip_at_f2 (off' := 0xF4) (by decide)
  rw [minus1 g inv.zero] at u1
  have inv1 := inv.setReg (rd := a0) (v := 0xFFFFFFFF) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sb hc ip_at_f4 (off' := 0xF8) (by decide)
  rw [inv1.s0, add_lit_zero, show upd g a0 0xFFFFFFFF s3 = g s3 by simp +decide [upd], he] at u2
  have hw := win_out8 env (j := 0) (by omega) (v := e) (inv.win env)
  rw [add_ofNat_zero] at hw
  obtain ⟨n3, d3, u3⟩ := u2.jump (ip_codes code0 hw).1 ip_at_f8 (off' := 0xA0) (by decide)
    (by rw [u2.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xA0 (by decide)))
  obtain ⟨n', c, rest⟩ := ip_errA0 env code0 inv1 u3 (by simp +decide [upd])
  exact ⟨n', .cons d1 (.cons d2 (.cons d3 c)), rest⟩

end Err

/-- `andi a1, a0, 0xFF; addi a1, a1, -0xFF; bne a1, x0` in any code: on to
`off + 10` when the low byte of `a0` is 0xFF, to `T` otherwise. -/
theorem check_br {Mx : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine} {off T : Nat}
    {f : Fin 32 → Word} {o : Word} (s : St Mx base m off f) (hc : CodeIn Mx base code)
    (h1 : fetchRel code off = some (.aluImm .and a1 a0 0xFF, 4))
    (h2 : fetchRel code (off + 4) = some (.aluImm .add a1 a1 0xFFFFFF01, 4))
    (h3 : fetchRel code (off + 8) = some (.branch .bne a1 x0 o, 2))
    (ho : BitVec.ofNat 32 (off + 8) + o = BitVec.ofNat 32 T) :
    ∃ m' g, Steps m m' ∧ (∀ r, r ≠ a1 → g r = f r) ∧
      ((f a0 &&& 0xFF = 0xFF ∧ St Mx base m' (off + 10) g) ∨
       (f a0 &&& 0xFF ≠ 0xFF ∧ St Mx base m' T g)) := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.aluImm hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc h2 (off' := off + 8) (ofNat_add_ofNat (off + 4) 4)
  have g2 : ∀ r, r ≠ a1 → upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) r = f r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h]
  have v2 : upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) a1 =
        (f a0 &&& 0xFF) + 0xFFFFFF01 := by simp +decide [upd, aluEval]
  have z2 : upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) x0 = 0 := by simp [upd]
  by_cases h : f a0 &&& 0xFF = 0xFF
  · obtain ⟨m3, e3, t3⟩ := t2.notTaken hc (off + 10) h3 (ofNat_add_ofNat (off + 8) 2)
      (by rw [v2, z2, h]; decide)
    exact ⟨m3, _, .cons e1 (.cons e2 (.single e3)), g2, .inl ⟨h, t3⟩⟩
  · have hne : (f a0 &&& 0xFF) + 0xFFFFFF01 ≠ 0 := fun e => h (by
      have := congrArg (· + 0xFF) e
      simp only [BitVec.add_assoc] at this
      rw [show (0xFFFFFF01 : Word) + 0xFF = 0 from rfl] at this
      exact (BitVec.add_zero _).symm.trans (this.trans (BitVec.zero_add _)))
    obtain ⟨m3, e3, t3⟩ := t2.taken hc T h3 ho (by rw [v2, z2]; exact bne_iff_ne.mpr hne)
    exact ⟨m3, _, .cons e1 (.cons e2 (.single e3)), g2, .inr ⟨h, t3⟩⟩

/-- Memory after a call that only advances the reader's position. -/
def posMem (M : Word → BitVec 8) (self n : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n with
  | none => M
  | some (_, e) => memStore32 M (self + 8) e

theorem magicMem_pos (M : Word → BitVec 8) (self : Word) : magicMem M self = posMem M self 4 := rfl
theorem u16Mem_pos (M : Word → BitVec 8) (self : Word) : u16Mem M self = posMem M self 2 := rfl
theorem reservedMem_pos (M : Word → BitVec 8) (self n : Word) : reservedMem M self n = posMem M self n := rfl

section Rd

variable {P R G ptr len out ilen : Word} {M0 Mx My : Word → BitVec 8} {f0 g : Fin 32 → Word}

/-- The buffer bytes are as at entry. -/
theorem IInv.buf (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g) :
    ∀ i, i < len.toNat → Mx (ptr + BitVec.ofNat 32 i) = M0 (ptr + BitVec.ofNat 32 i) :=
  fun i hi => inv.outside _ (env.hBS.sub (c := i) (l := 1) (by omega)).symm

/-- The bytes a read returns are buffer bytes. -/
theorem buf_bytes (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos n p e : Word} (h : bytesResult ptr len pos n = some (p, e)) :
    ∀ j, j < n.toNat → Mx (p + BitVec.ofNat 32 j) = M0 (p + BitVec.ofNat 32 j) := by
  intro j hj
  rw [bytesResult_eq] at h
  split at h
  · rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have e1 : ptr + pos + BitVec.ofNat 32 j = ptr + BitVec.ofNat 32 (pos.toNat + j) := by
      rw [← add_ofNat_assoc, ofNat_toNat_self]
    rw [e1]; exact inv.buf env _ (by omega)
  · cases h

theorem buf_load (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos n p e : Word} (h : bytesResult ptr len pos n = some (p, e)) (hn : 4 ≤ n.toNat) :
    memLoad32 Mx p = memLoad32 M0 p :=
  memLoad32_congr fun j hj => buf_bytes env inv h j (by omega)

/-- After a call that only advances the position, with its stack inside the
callees' 48 bytes. -/
theorem IInv.adv (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos n : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) {c N : Nat} (hcN : c + N ≤ 0x30)
    (hm : ∀ x, Sep (R + BitVec.ofNat 32 c) N x 1 → My x = posMem Mx (G + 0x18) n x) :
    IInv R G ptr len out ilen M0 f0 My g ∧
      ∀ p e, bytesResult ptr len pos n = some (p, e) → memLoad32 My (G + 0x18 + 8) = e := by
  obtain ⟨-, -, -, -, e50, -, -⟩ := env.r_eqs
  have hpm : ∀ x, posMem Mx (G + 0x18) n x =
      (match bytesResult ptr len pos n with
       | none => Mx | some (_, e) => memStore32 Mx (G + 0x18 + 8) e) x := fun x => by
    unfold posMem; rw [inv.rdp, inv.rdl, hpos]
  have out1 : ∀ x, Sep R 0x48 x 1 → Sep (R + c) N x 1 := fun x h =>
    (h.sub (c := c) (l := N) (by omega))
  have nPos : ∀ x, Sep (R + BitVec.ofNat 32 0x50) 0x10C x 1 → Sep (G + 0x18 + 8) 4 x 1 := fun x h => by
    rw [e50]; exact (h.sub (c := 0) (l := 4) (by omega) |> fun s => by rwa [add_ofNat_zero] at s)
  refine ⟨inv.mem env (fun x h1 h2 => ?_), fun p e he => ?_⟩
  · rw [hm x (out1 x h1), hpm]
    rcases bytesResult ptr len pos n with _ | ⟨q, e'⟩
    · rfl
    · exact memStore32_get_sep (nPos x h2)
  · have hR : Sep (R + BitVec.ofNat 32 c) N (G + 0x18 + 8) 4 := by
      rw [e50]; exact env.stack_stack c N 0x50 4 (by omega) (by omega) (by omega)
    rw [show memLoad32 My (G + 0x18 + 8) = memLoad32 (posMem Mx (G + 0x18) n) (G + 0x18 + 8) from
      memLoad32_congr fun j hj => hm _ (fun i hi k hk q => hR i hi j hj (by
        have : k = 0 := by omega
        subst this; rwa [add_ofNat_zero] at q))]
    unfold posMem; rw [inv.rdp, inv.rdl, hpos, he]
    exact memLoad32_store32_same _ _ _

/-- `Reader::magic`'s result, from the reader's position and the buffer. -/
theorem magicR (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos k : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    magicResult Mx (G + 0x18) k =
      match bytesResult ptr len pos 4 with
      | none => 0
      | some (p, _) => if memLoad32 M0 p == k then 0xFFFFFFFF else 2 := by
  unfold magicResult; rw [inv.rdp, inv.rdl, hpos]
  rcases h : bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rfl
  · dsimp only; rw [buf_load env inv h (by decide)]

/-- `Reader::u8`'s result, from the reader's position and the buffer. -/
theorem u8R (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    u8Result Mx (G + 0x18) =
      match bytesResult ptr len pos 1 with
      | none => (1, 0)
      | some (p, _) => (0, (M0 p).zeroExtend 32) := by
  unfold u8Result; rw [inv.rdp, inv.rdl, hpos]
  rcases h : bytesResult ptr len pos 1 with _ | ⟨p, e⟩
  · rfl
  · dsimp only
    have := buf_bytes env inv h 0 (by decide)
    rw [add_ofNat_zero] at this; rw [this]

theorem buf_b1 (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos p e : Word} (h : bytesResult ptr len pos 2 = some (p, e)) :
    Mx p = M0 p ∧ Mx (p + 1) = M0 (p + 1) := by
  have h0 := buf_bytes env inv h 0 (by decide)
  have h1 := buf_bytes env inv h 1 (by decide)
  rw [add_ofNat_zero] at h0
  exact ⟨h0, h1⟩

/-- `Reader::u16`'s result. -/
theorem u16R (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    u16Result Mx (G + 0x18) =
      match bytesResult ptr len pos 2 with
      | none => 1
      | some (p, _) => (M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16 := by
  unfold u16Result; rw [inv.rdp, inv.rdl, hpos]
  rcases h : bytesResult ptr len pos 2 with _ | ⟨p, e⟩
  · rfl
  · dsimp only; rw [(buf_b1 env inv h).1, (buf_b1 env inv h).2]

/-- `Reader::version_1`'s result. -/
theorem verR (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    version1Result Mx (G + 0x18) =
      match bytesResult ptr len pos 2 with
      | none => 0
      | some (p, _) =>
        if ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16 : Word) >>> 16 == 1
        then 0xFFFFFFFF else 3 := by
  unfold version1Result
  rw [u16R env inv hpos, inv.rdp, inv.rdl, hpos]
  rcases bytesResult ptr len pos 2 with _ | ⟨p, e⟩ <;> rfl

/-- `Reader::reserved(n)`'s result. -/
theorem resR (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos n : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    reservedResult Mx (G + 0x18) n =
      match bytesResult ptr len pos n with
      | none => 0
      | some (p, _) => if allZero M0 p n.toNat then 0xFF else 4 := by
  unfold reservedResult; rw [inv.rdp, inv.rdl, hpos]
  rcases h : bytesResult ptr len pos n with _ | ⟨p, e⟩
  · rfl
  · dsimp only; rw [allZero_congr n.toNat p (buf_bytes env inv h)]

/-- After `Reader::u32` with its result at `G + c`: `IInv`, and the result's
tag, value, and the new position. -/
theorem IInv.u32 (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) {c : Nat} (hc0 : 0x24 ≤ c)
    (hc1 : c + 8 ≤ 0x12C)
    (hm : ∀ x, Sep R 48 x 1 → My x = u32Mem Mx (G + BitVec.ofNat 32 c) (G + 0x18) x) :
    IInv R G ptr len out ilen M0 f0 My g ∧
      match bytesResult ptr len pos 4 with
      | none => My (G + BitVec.ofNat 32 c) = 1 ∧ My (G + BitVec.ofNat 32 c + 1) = 0
      | some (p, e) => My (G + BitVec.ofNat 32 c) = 0 ∧
          memLoad32 My (G + BitVec.ofNat 32 c + 4) = memLoad32 M0 p ∧ memLoad32 My (G + 0x18 + 8) = e := by
  obtain ⟨-, -, -, -, e50, -, -⟩ := env.r_eqs
  have eO : G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x30 + c) := env.g_ofs c
  have hum : ∀ x, u32Mem Mx (G + BitVec.ofNat 32 c) (G + 0x18) x =
      (match bytesResult ptr len pos 4 with
       | none => memStore8 (memStore8 Mx (G + BitVec.ofNat 32 c + 1) 0) (G + BitVec.ofNat 32 c) 1
       | some (p, e) => memStore8 (memStore32 (memStore32 Mx (G + 0x18 + 8) e)
           (G + BitVec.ofNat 32 c + 4) (memLoad32 Mx p)) (G + BitVec.ofNat 32 c) 0) x := fun x => by
    unfold u32Mem; rw [inv.rdp, inv.rdl, hpos]; cases bytesResult ptr len pos 4 <;> rfl
  -- Bytes outside the callee stack: given by the match.
  have frR : ∀ x, Sep R 0x48 x 1 → Sep R 48 x 1 := fun x h => h.sub (c := 0) (l := 48) (by omega)
    |> fun s => by rwa [add_ofNat_zero] at s
  have sO : ∀ x, Sep (R + BitVec.ofNat 32 0x50) 0x10C x 1 → ∀ j, j < 8 →
      x ≠ G + BitVec.ofNat 32 c + BitVec.ofNat 32 j := fun x h j hj e => by
    rw [eO, add_ofNat_assoc] at e
    exact h (0x30 + c + j - 0x50) (by omega) 0 (by omega) (by
      rw [add_ofNat_zero, e, add_ofNat_assoc]; congr 2; omega)
  have sP : ∀ x, Sep (R + BitVec.ofNat 32 0x50) 0x10C x 1 → Sep (G + 0x18 + 8) 4 x 1 := fun x h => by
    rw [e50]; exact (h.sub (c := 0) (l := 4) (by omega) |> fun s => by rwa [add_ofNat_zero] at s)
  have nO : ∀ x, Sep (R + BitVec.ofNat 32 0x50) 0x10C x 1 → ∀ j, j < 8 →
      x ≠ G + BitVec.ofNat 32 (c + j) := fun x h j hj e => sO x h j hj (by rw [add_ofNat_assoc]; exact e)
  have e1 : G + BitVec.ofNat 32 c + 1 = G + BitVec.ofNat 32 (c + 1) := add_ofNat_assoc _ _ _
  have e4 : G + BitVec.ofNat 32 c + 4 = G + BitVec.ofNat 32 (c + 4) := add_ofNat_assoc _ _ _
  have sR48 : ∀ k, 0x18 ≤ k → k < 0x160 → Sep R 48 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [env.g_ofs]
    exact env.stack_stack 0 48 (0x30 + k) 1 (by omega) (by omega) (by omega) |> fun s => by
      rwa [add_ofNat_zero] at s
  refine ⟨inv.mem env (fun x h1 h2 => ?_), ?_⟩
  · rw [hm x (frR x h1), hum]
    rcases bytesResult ptr len pos 4 with _ | ⟨p, e⟩
    · dsimp only
      rw [memStore8_ne (by have := nO x h2 0 (by omega); rwa [Nat.add_zero] at this),
        e1, memStore8_ne (nO x h2 1 (by omega))]
    · dsimp only
      rw [memStore8_ne (by have := nO x h2 0 (by omega); rwa [Nat.add_zero] at this),
        e4, memStore32_get_sep (fun i hi k hk q => nO x h2 (4 + i) (by omega) (by
          have : k = 0 := by omega
          subst this; rw [add_ofNat_zero] at q; rw [← q, add_ofNat_assoc, Nat.add_comm 4 i, Nat.add_assoc]; congr 2; omega)),
        memStore32_get_sep (sP x h2)]
  · rcases hb : bytesResult ptr len pos 4 with _ | ⟨p, e⟩
    · dsimp only
      refine ⟨?_, ?_⟩
      · rw [hm _ (sR48 c (by omega) (by omega)), hum, hb]; exact memStore8_same _ _ _
      · rw [e1, hm _ (sR48 (c + 1) (by omega) (by omega)), hum, hb]; dsimp only
        rw [memStore8_ne (fun q => by
          have := add_ofNat_ne G (c := c) (d := c + 1) (by omega) (by omega) (by omega)
          exact this q.symm), e1, memStore8_same]
    · dsimp only
      have L : ∀ (b : Word), (∀ j, j < 4 → Sep R 48 (b + BitVec.ofNat 32 j) 1) →
          memLoad32 My b = memLoad32 (u32Mem Mx (G + BitVec.ofNat 32 c) (G + 0x18)) b := fun b hb' =>
        memLoad32_congr fun j hj => hm _ (hb' j hj)
      refine ⟨?_, ?_, ?_⟩
      · rw [hm _ (sR48 c (by omega) (by omega)), hum, hb]; exact memStore8_same _ _ _
      · rw [L _ (fun j hj => by rw [e4, add_ofNat_assoc]; exact sR48 _ (by omega) (by omega)), funext hum, hb]
        dsimp only
        rw [e4, memLoad32_store8_sep (sep_offsets G (c := c) (n := 1) (d := c + 4) (k := 4)
          (by omega) (by omega) (by omega) |> fun s => s), memLoad32_store32_same,
          buf_load env inv hb (by decide)]
      · rw [L _ (fun j hj => by
          rw [show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
          exact sR48 _ (by omega) (by omega)), funext hum, hb]
        dsimp only
        rw [memLoad32_store8_sep (show Sep (G + BitVec.ofNat 32 c) 1 (G + 0x18 + 8) 4 by
            rw [show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl]
            exact sep_offsets G (by omega) (by omega) (by omega)),
          memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 c + 4) 4 (G + 0x18 + 8) 4 by
            rw [e4, show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl]
            exact sep_offsets G (by omega) (by omega) (by omega)),
          memLoad32_store32_same]

end Rd

end C3.RV32
