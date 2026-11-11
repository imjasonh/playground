import C3BootProofs.Proofs.Sha256Data
import C3BootProofs.Proofs.Sha256Rounds

/-!
# `sha2::sha256::compress256`, as compiled

`sha256Compress_correct` proves the 11,156-byte compiled compression function
end to end:
- `sha_pro`: prologue (0x00..0x4C) allocates the 0xE0-byte frame, saves `ra`
  and `s0..s11` at `0xAC..0xDF`, loads the 8 working variables from `stp`,
  stores `stp` at `F + 0xC` and `endp = bp + 64 * n` at `F + 0x10`, and sets
  `s3 = 3`, `s4 = F + 0x6C`, `s1 = bp`.
- `sha_load_loop`: inner loop (0x5E..0xA2) calls `shaIndexCode` 16 times and
  assembles the 16 big-endian words of the current 64-byte block into
  `F + 0x6C .. F + 0xAC`.
- `sha_outer_loop`: outer loop (0x4C..0x2B68) iterates over the `n` blocks,
  composing `sha_load_loop` and `sha_rounds` on each block.
- `sha_epi`: epilogue (0x2B68..0x2B86) restores `ra` and `s0..s11`, pops the
  frame, and returns.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 100000

/-- The 13 registers `compress256` saves in its frame `F = sp0 + 0xFFFFFF20`. -/
abbrev shaSaved : List (Fin 32 × Nat) :=
  [(ra, 0xDC), ((8 : Fin 32), 0xD8), ((9 : Fin 32), 0xD4), ((18 : Fin 32), 0xD0),
   ((19 : Fin 32), 0xCC), ((20 : Fin 32), 0xC8), ((21 : Fin 32), 0xC4), ((22 : Fin 32), 0xC0),
   ((23 : Fin 32), 0xBC), ((24 : Fin 32), 0xB8), ((25 : Fin 32), 0xB4), ((26 : Fin 32), 0xB0),
   ((27 : Fin 32), 0xAC)]

section Helpers
variable {M0 : Word → BitVec 8} {P sp0 stp bp : Word} {n : Nat}

theorem SCEnv.hF (env : SCEnv M0 P sp0 stp bp n) : (sp0 + 0xFFFFFF20).toNat % 4 = 0 :=
  aligned_add env.hsp (k := 0xFFFFFF20) (by decide)

theorem SCEnv.headCode (env : SCEnv M0 P sp0 stp bp n) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x) :
    CodeIn M P shaHead := by
  have hc : CodeIn M P sha256CompressCode := fun i hi => by
    rw [fr _ (env.sC.subR (c := i) (l := 1) (by omega)) (env.stC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have hw := CodeIn.window hc (w := shaHead) (s := 0) rfl (by decide)
  rwa [add_ofNat_zero] at hw

theorem SCEnv.tailCode (env : SCEnv M0 P sp0 stp bp n) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x) :
    CodeIn M (P + BitVec.ofNat 32 0x2B64) shaTail := by
  have hc : CodeIn M P sha256CompressCode := fun i hi => by
    rw [fr _ (env.sC.subR (c := i) (l := 1) (by omega)) (env.stC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  exact CodeIn.window hc (w := shaTail) (s := 0x2B64) rfl (by decide)

theorem SCEnv.idxCode (env : SCEnv M0 P sp0 stp bp n) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x) :
    CodeIn M (P + 0x2B94) shaIndexCode := fun i hi => by
  rw [fr _ (env.sI.subR (c := i) (l := 1) (by omega)) (env.stI.subR (c := i) (l := 1) (by omega))]
  exact env.idx i hi

theorem frame_slot_sep {F x : Word} (o : Nat) (ho : o + 4 ≤ 0xE0) (hx : Sep F 0xE0 x 1) :
    Sep (F + BitVec.ofNat 32 o) 4 x 1 :=
  hx.sub (c := o) (l := 4) ho

/-- What holds at offset 0x4C before block `j` (`0 ≤ j ≤ n`):
- `sp = F`, `s1 = bp + 64 * j`, `s3 = 3`, `s4 = F + 0x6C`, `tp` preserved
- `s8, s5, s9, s10, s2, s11, s6, s7` hold `hv`
- when `0 < j`, `wordsAt M stp 8 = hv.toList` (for `j = 0`, `wordsAt M0 stp 8 = hv.toList` and `stp` is untouched)
- `F + 0xC` holds `stp`, `F + 0x10` holds `bp + 64 * n`
- `F + 0xAC .. F + 0xDF` hold the saved registers as in `Ms`
- outside `F..F+0xE0` and `stp..stp+32`, `M` agrees with `M0`. -/
structure ShaLoopInv (M0 Ms : Word → BitVec 8) (P sp0 stp bp : Word) (n j : Nat)
    (hv : Sha256.V8) (tp0 : Word) (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x4C (reg m)
  rsp : reg m sp = sp0 + 0xFFFFFF20
  rs1 : reg m (9 : Fin 32) = bp + BitVec.ofNat 32 (64 * j)
  rs3 : reg m (19 : Fin 32) = 0x3
  rs4 : reg m (20 : Fin 32) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x6C
  rtp : reg m (4 : Fin 32) = tp0
  ra_v : reg m (24 : Fin 32) = hv.a
  rb_v : reg m (21 : Fin 32) = hv.b
  rc_v : reg m (25 : Fin 32) = hv.c
  rd_v : reg m (26 : Fin 32) = hv.d
  re_v : reg m (18 : Fin 32) = hv.e
  rf_v : reg m (27 : Fin 32) = hv.f
  rg_v : reg m (22 : Fin 32) = hv.g
  rh_v : reg m (23 : Fin 32) = hv.h
  hst : wordsAt M stp 8 = hv.toList
  m0c : memLoad32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC) = stp
  m10 : memLoad32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10) = bp + BitVec.ofNat 32 (64 * n)
  sv : ∀ c, 0xAC ≤ c → c < 0xE0 →
    M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) = Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c)
  fr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x

/-- What holds at offset 0x5E inside the 16-word big-endian load loop at word `i` (`0 ≤ i ≤ 16`). -/
structure ShaLoadInv (M0 Ms : Word → BitVec 8) (P sp0 stp bp : Word) (n j i : Nat)
    (hv : Sha256.V8) (tp0 : Word) (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x5E (reg m)
  rsp : reg m sp = sp0 + 0xFFFFFF20
  rs0 : reg m (8 : Fin 32) = BitVec.ofNat 32 (4 * i)
  rs1 : reg m (9 : Fin 32) = bp + BitVec.ofNat 32 (64 * j)
  rs3 : reg m (19 : Fin 32) = 0x3
  rs4 : reg m (20 : Fin 32) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x6C
  rtp : reg m (4 : Fin 32) = tp0
  ra_v : reg m (24 : Fin 32) = hv.a
  rb_v : reg m (21 : Fin 32) = hv.b
  rc_v : reg m (25 : Fin 32) = hv.c
  rd_v : reg m (26 : Fin 32) = hv.d
  re_v : reg m (18 : Fin 32) = hv.e
  rf_v : reg m (27 : Fin 32) = hv.f
  rg_v : reg m (22 : Fin 32) = hv.g
  rh_v : reg m (23 : Fin 32) = hv.h
  hst : wordsAt M stp 8 = hv.toList
  m0c : memLoad32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC) = stp
  m10 : memLoad32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10) = bp + BitVec.ofNat 32 (64 * n)
  m40 : memLoad32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x40) = bp + BitVec.ofNat 32 (64 * (j + 1))
  win : ∀ k, k < i →
    memLoad32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 (0x6C + 4 * k)) =
      (Sha256.schedule (memBytes M0 (bp + BitVec.ofNat 32 (64 * j)) 64))[k]!
  sv : ∀ c, 0xAC ≤ c → c < 0xE0 →
    M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) = Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c)
  fr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x


def hvOf (M : Word → BitVec 8) (stp : Word) : Sha256.V8 :=
  ⟨memLoad32 M (stp + BitVec.ofNat 32 0x0),
   memLoad32 M (stp + BitVec.ofNat 32 0x4),
   memLoad32 M (stp + BitVec.ofNat 32 0x8),
   memLoad32 M (stp + BitVec.ofNat 32 0xC),
   memLoad32 M (stp + BitVec.ofNat 32 0x10),
   memLoad32 M (stp + BitVec.ofNat 32 0x14),
   memLoad32 M (stp + BitVec.ofNat 32 0x18),
   memLoad32 M (stp + BitVec.ofNat 32 0x1C)⟩

theorem wordsAt8_hvOf (M : Word → BitVec 8) (stp : Word) :
    wordsAt M stp 8 = (hvOf M stp).toList := rfl

theorem sll6_add_bp (bp : Word) (n : Nat) (hn : n < 2 ^ 26) :
    ((BitVec.ofNat 32 n <<< 6) + bp) = bp + BitVec.ofNat 32 (64 * n) := by
  rw [BitVec.add_comm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mul_comm n 64]

set_option maxHeartbeats 8000000 in
/-- Prologue of `compress256` (0x00..0x4C). -/
theorem sha_pro (m : Machine) {P sp0 stp bp : Word} {n : Nat}
    (env : SCEnv m.mem P sp0 stp bp n) (hn : n < 2 ^ 26)
    (hpc : m.pc = P) (ha0 : reg m a0 = stp) (ha1 : reg m a1 = bp)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hsp : reg m sp = sp0) :
    ∃ m' Ms, Steps m m' ∧
      ShaLoopInv m.mem Ms P sp0 stp bp n 0 (hvOf m.mem stp) (reg m (4 : Fin 32)) m'.mem m' ∧
      ∀ r c, (r, c) ∈ shaSaved → memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) = reg m r := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hF := env.hF
  have F0 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → m.mem x = m.mem x := fun _ _ => rfl
  have hcOf : ∀ {M' : Word → BitVec 8}, (∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M' x = m.mem x) →
      CodeIn M' P shaHead := fun h => env.headCode fun x hx _ => h x hx
  obtain ⟨n1, d1, u1⟩ := sha_addi_c (off' := 0x2) (c := sp0 + 0xFFFFFF20) s0 (hcOf F0) sh_at_0 rfl hsp rfl
  have sp_1 := reg_step_eq u1 rfl
  obtain ⟨n2, d2, u2⟩ := u1.self.sw (hcOf F0) sh_at_2 (off' := 0x4) (by decide)
    (by rw [sp_1]; exact aligned_add hF (by decide))
  rw [sp_1, (reg_step_ne u1 rfl rfl), show (0xDC : Word) = BitVec.ofNat 32 0xDC from rfl] at u2
  obtain ⟨M2, hM2⟩ : ∃ Mx, memStore32 m.mem (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xDC) (reg m ra) = Mx := ⟨_, rfl⟩
  rw [hM2] at u2
  have F2 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2, memStore32_get_sep (frame_slot_sep 0xDC (by decide) hx), F0 x hx]
  have sp_2 : reg n2 sp = sp0 + 0xFFFFFF20 := reg_step_sw u2 sp_1
  obtain ⟨n3, d3, u3⟩ := u2.self.sw (hcOf F2) sh_at_4 (off' := 0x6) (by decide)
    (by rw [sp_2]; exact aligned_add hF (by decide))
  rw [sp_2, (reg_step_sw u2 (reg_step_ne u1 rfl rfl)), show (0xD8 : Word) = BitVec.ofNat 32 0xD8 from rfl] at u3
  obtain ⟨M3, hM3⟩ : ∃ Mx, memStore32 M2 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD8) (reg m (8 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM3] at u3
  have F3 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (frame_slot_sep 0xD8 (by decide) hx), F2 x hx]
  have sp_3 : reg n3 sp = sp0 + 0xFFFFFF20 := reg_step_sw u3 sp_2
  obtain ⟨n4, d4, u4⟩ := u3.self.sw (hcOf F3) sh_at_6 (off' := 0x8) (by decide)
    (by rw [sp_3]; exact aligned_add hF (by decide))
  rw [sp_3, (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl))), show (0xD4 : Word) = BitVec.ofNat 32 0xD4 from rfl] at u4
  obtain ⟨M4, hM4⟩ : ∃ Mx, memStore32 M3 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD4) (reg m (9 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM4] at u4
  have F4 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, memStore32_get_sep (frame_slot_sep 0xD4 (by decide) hx), F3 x hx]
  have sp_4 : reg n4 sp = sp0 + 0xFFFFFF20 := reg_step_sw u4 sp_3
  obtain ⟨n5, d5, u5⟩ := u4.self.sw (hcOf F4) sh_at_8 (off' := 0xA) (by decide)
    (by rw [sp_4]; exact aligned_add hF (by decide))
  rw [sp_4, (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl)))), show (0xD0 : Word) = BitVec.ofNat 32 0xD0 from rfl] at u5
  obtain ⟨M5, hM5⟩ : ∃ Mx, memStore32 M4 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD0) (reg m (18 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM5] at u5
  have F5 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5, memStore32_get_sep (frame_slot_sep 0xD0 (by decide) hx), F4 x hx]
  have sp_5 : reg n5 sp = sp0 + 0xFFFFFF20 := reg_step_sw u5 sp_4
  obtain ⟨n6, d6, u6⟩ := u5.self.sw (hcOf F5) sh_at_a (off' := 0xC) (by decide)
    (by rw [sp_5]; exact aligned_add hF (by decide))
  rw [sp_5, (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl))))), show (0xCC : Word) = BitVec.ofNat 32 0xCC from rfl] at u6
  obtain ⟨M6, hM6⟩ : ∃ Mx, memStore32 M5 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xCC) (reg m (19 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM6] at u6
  have F6 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M6 x = m.mem x := fun x hx => by
    rw [← hM6, memStore32_get_sep (frame_slot_sep 0xCC (by decide) hx), F5 x hx]
  have sp_6 : reg n6 sp = sp0 + 0xFFFFFF20 := reg_step_sw u6 sp_5
  obtain ⟨n7, d7, u7⟩ := u6.self.sw (hcOf F6) sh_at_c (off' := 0xE) (by decide)
    (by rw [sp_6]; exact aligned_add hF (by decide))
  rw [sp_6, (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl)))))), show (0xC8 : Word) = BitVec.ofNat 32 0xC8 from rfl] at u7
  obtain ⟨M7, hM7⟩ : ∃ Mx, memStore32 M6 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC8) (reg m (20 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM7] at u7
  have F7 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M7 x = m.mem x := fun x hx => by
    rw [← hM7, memStore32_get_sep (frame_slot_sep 0xC8 (by decide) hx), F6 x hx]
  have sp_7 : reg n7 sp = sp0 + 0xFFFFFF20 := reg_step_sw u7 sp_6
  obtain ⟨n8, d8, u8⟩ := u7.self.sw (hcOf F7) sh_at_e (off' := 0x10) (by decide)
    (by rw [sp_7]; exact aligned_add hF (by decide))
  rw [sp_7, (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl))))))), show (0xC4 : Word) = BitVec.ofNat 32 0xC4 from rfl] at u8
  obtain ⟨M8, hM8⟩ : ∃ Mx, memStore32 M7 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC4) (reg m (21 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM8] at u8
  have F8 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8, memStore32_get_sep (frame_slot_sep 0xC4 (by decide) hx), F7 x hx]
  have sp_8 : reg n8 sp = sp0 + 0xFFFFFF20 := reg_step_sw u8 sp_7
  obtain ⟨n9, d9, u9⟩ := u8.self.sw (hcOf F8) sh_at_10 (off' := 0x12) (by decide)
    (by rw [sp_8]; exact aligned_add hF (by decide))
  rw [sp_8, (reg_step_sw u8 (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl)))))))), show (0xC0 : Word) = BitVec.ofNat 32 0xC0 from rfl] at u9
  obtain ⟨M9, hM9⟩ : ∃ Mx, memStore32 M8 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC0) (reg m (22 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM9] at u9
  have F9 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M9 x = m.mem x := fun x hx => by
    rw [← hM9, memStore32_get_sep (frame_slot_sep 0xC0 (by decide) hx), F8 x hx]
  have sp_9 : reg n9 sp = sp0 + 0xFFFFFF20 := reg_step_sw u9 sp_8
  obtain ⟨n10, d10, u10⟩ := u9.self.sw (hcOf F9) sh_at_12 (off' := 0x14) (by decide)
    (by rw [sp_9]; exact aligned_add hF (by decide))
  rw [sp_9, (reg_step_sw u9 (reg_step_sw u8 (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl))))))))), show (0xBC : Word) = BitVec.ofNat 32 0xBC from rfl] at u10
  obtain ⟨M10, hM10⟩ : ∃ Mx, memStore32 M9 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xBC) (reg m (23 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM10] at u10
  have F10 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M10 x = m.mem x := fun x hx => by
    rw [← hM10, memStore32_get_sep (frame_slot_sep 0xBC (by decide) hx), F9 x hx]
  have sp_10 : reg n10 sp = sp0 + 0xFFFFFF20 := reg_step_sw u10 sp_9
  obtain ⟨n11, d11, u11⟩ := u10.self.sw (hcOf F10) sh_at_14 (off' := 0x16) (by decide)
    (by rw [sp_10]; exact aligned_add hF (by decide))
  rw [sp_10, (reg_step_sw u10 (reg_step_sw u9 (reg_step_sw u8 (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl)))))))))), show (0xB8 : Word) = BitVec.ofNat 32 0xB8 from rfl] at u11
  obtain ⟨M11, hM11⟩ : ∃ Mx, memStore32 M10 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB8) (reg m (24 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM11] at u11
  have F11 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M11 x = m.mem x := fun x hx => by
    rw [← hM11, memStore32_get_sep (frame_slot_sep 0xB8 (by decide) hx), F10 x hx]
  have sp_11 : reg n11 sp = sp0 + 0xFFFFFF20 := reg_step_sw u11 sp_10
  obtain ⟨n12, d12, u12⟩ := u11.self.sw (hcOf F11) sh_at_16 (off' := 0x18) (by decide)
    (by rw [sp_11]; exact aligned_add hF (by decide))
  rw [sp_11, (reg_step_sw u11 (reg_step_sw u10 (reg_step_sw u9 (reg_step_sw u8 (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl))))))))))), show (0xB4 : Word) = BitVec.ofNat 32 0xB4 from rfl] at u12
  obtain ⟨M12, hM12⟩ : ∃ Mx, memStore32 M11 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB4) (reg m (25 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM12] at u12
  have F12 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M12 x = m.mem x := fun x hx => by
    rw [← hM12, memStore32_get_sep (frame_slot_sep 0xB4 (by decide) hx), F11 x hx]
  have sp_12 : reg n12 sp = sp0 + 0xFFFFFF20 := reg_step_sw u12 sp_11
  obtain ⟨n13, d13, u13⟩ := u12.self.sw (hcOf F12) sh_at_18 (off' := 0x1A) (by decide)
    (by rw [sp_12]; exact aligned_add hF (by decide))
  rw [sp_12, (reg_step_sw u12 (reg_step_sw u11 (reg_step_sw u10 (reg_step_sw u9 (reg_step_sw u8 (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl)))))))))))), show (0xB0 : Word) = BitVec.ofNat 32 0xB0 from rfl] at u13
  obtain ⟨M13, hM13⟩ : ∃ Mx, memStore32 M12 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB0) (reg m (26 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM13] at u13
  have F13 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M13 x = m.mem x := fun x hx => by
    rw [← hM13, memStore32_get_sep (frame_slot_sep 0xB0 (by decide) hx), F12 x hx]
  have sp_13 : reg n13 sp = sp0 + 0xFFFFFF20 := reg_step_sw u13 sp_12
  obtain ⟨n14, d14, u14⟩ := u13.self.sw (hcOf F13) sh_at_1a (off' := 0x1C) (by decide)
    (by rw [sp_13]; exact aligned_add hF (by decide))
  rw [sp_13, (reg_step_sw u13 (reg_step_sw u12 (reg_step_sw u11 (reg_step_sw u10 (reg_step_sw u9 (reg_step_sw u8 (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5 (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 rfl rfl))))))))))))), show (0xAC : Word) = BitVec.ofNat 32 0xAC from rfl] at u14
  obtain ⟨M14, hM14⟩ : ∃ Mx, memStore32 M13 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xAC) (reg m (27 : Fin 32)) = Mx := ⟨_, rfl⟩
  rw [hM14] at u14
  have F14 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M14 x = m.mem x := fun x hx => by
    rw [← hM14, memStore32_get_sep (frame_slot_sep 0xAC (by decide) hx), F13 x hx]
  have sp_14 : reg n14 sp = sp0 + 0xFFFFFF20 := reg_step_sw u14 sp_13
  have k14 : ∀ q, (q.val == 0 || q.val == 2) = false → reg n14 q = reg m q := fun q hq =>
    reg_step_sw u14 (reg_step_sw u13 (reg_step_sw u12 (reg_step_sw u11 (reg_step_sw u10
      (reg_step_sw u9 (reg_step_sw u8 (reg_step_sw u7 (reg_step_sw u6 (reg_step_sw u5
        (reg_step_sw u4 (reg_step_sw u3 (reg_step_sw u2 (reg_step_ne u1 hq rfl)))))))))))))
  have stp_unch : ∀ {M' : Word → BitVec 8}, (∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M' x = m.mem x) →
      ∀ o, o + 4 ≤ 32 → memLoad32 M' (stp + BitVec.ofNat 32 o) = memLoad32 m.mem (stp + BitVec.ofNat 32 o) :=
    fun h o ho => memLoad32_congr fun j hj => h _ (by
      rw [add_ofNat_assoc]; exact env.stF.symm.subR (c := o + j) (l := 1) (by omega))
  -- 0x1C: mv s1, a1
  obtain ⟨n15, d15, u15⟩ := sha_mv (off' := 0x1E) u14.self (hcOf F14) sh_at_1c rfl ((k14 a1 rfl).trans ha1)
  have a0_15 : reg n15 a0 = stp := reg_step_ne u15 rfl ((k14 a0 rfl).trans ha0)
  -- 0x1E..0x36: 7 loads from stp
  obtain ⟨n16, d16, u16⟩ := u15.self.lw (hcOf F14) sh_at_1e (off' := 0x22) (by decide)
    (by rw [a0_15, show stp + (0x0 : Word) = stp + BitVec.ofNat 32 0x0 from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_15, show stp + (0x0 : Word) = stp + BitVec.ofNat 32 0x0 from rfl, stp_unch F14 0x0 (by decide)] at u16
  have a0_16 : reg n16 a0 = stp := reg_step_ne u16 rfl a0_15
  obtain ⟨n17, d17, u17⟩ := u16.self.lw (hcOf F14) sh_at_22 (off' := 0x26) (by decide)
    (by rw [a0_16, show stp + (0x4 : Word) = stp + BitVec.ofNat 32 0x4 from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_16, show stp + (0x4 : Word) = stp + BitVec.ofNat 32 0x4 from rfl, stp_unch F14 0x4 (by decide)] at u17
  have a0_17 : reg n17 a0 = stp := reg_step_ne u17 rfl a0_16
  obtain ⟨n18, d18, u18⟩ := u17.self.lw (hcOf F14) sh_at_26 (off' := 0x2A) (by decide)
    (by rw [a0_17, show stp + (0x8 : Word) = stp + BitVec.ofNat 32 0x8 from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_17, show stp + (0x8 : Word) = stp + BitVec.ofNat 32 0x8 from rfl, stp_unch F14 0x8 (by decide)] at u18
  have a0_18 : reg n18 a0 = stp := reg_step_ne u18 rfl a0_17
  obtain ⟨n19, d19, u19⟩ := u18.self.lw (hcOf F14) sh_at_2a (off' := 0x2E) (by decide)
    (by rw [a0_18, show stp + (0xC : Word) = stp + BitVec.ofNat 32 0xC from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_18, show stp + (0xC : Word) = stp + BitVec.ofNat 32 0xC from rfl, stp_unch F14 0xC (by decide)] at u19
  have a0_19 : reg n19 a0 = stp := reg_step_ne u19 rfl a0_18
  obtain ⟨n20, d20, u20⟩ := u19.self.lw (hcOf F14) sh_at_2e (off' := 0x32) (by decide)
    (by rw [a0_19, show stp + (0x10 : Word) = stp + BitVec.ofNat 32 0x10 from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_19, show stp + (0x10 : Word) = stp + BitVec.ofNat 32 0x10 from rfl, stp_unch F14 0x10 (by decide)] at u20
  have a0_20 : reg n20 a0 = stp := reg_step_ne u20 rfl a0_19
  obtain ⟨n21, d21, u21⟩ := u20.self.lw (hcOf F14) sh_at_32 (off' := 0x36) (by decide)
    (by rw [a0_20, show stp + (0x14 : Word) = stp + BitVec.ofNat 32 0x14 from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_20, show stp + (0x14 : Word) = stp + BitVec.ofNat 32 0x14 from rfl, stp_unch F14 0x14 (by decide)] at u21
  have a0_21 : reg n21 a0 = stp := reg_step_ne u21 rfl a0_20
  obtain ⟨n22, d22, u22⟩ := u21.self.lw (hcOf F14) sh_at_36 (off' := 0x3A) (by decide)
    (by rw [a0_21, show stp + (0x18 : Word) = stp + BitVec.ofNat 32 0x18 from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_21, show stp + (0x18 : Word) = stp + BitVec.ofNat 32 0x18 from rfl, stp_unch F14 0x18 (by decide)] at u22
  have a0_22 : reg n22 a0 = stp := reg_step_ne u22 rfl a0_21
  have sp_22 : reg n22 sp = sp0 + 0xFFFFFF20 :=
    reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl (reg_step_ne u19 rfl
      (reg_step_ne u18 rfl (reg_step_ne u17 rfl (reg_step_ne u16 rfl (reg_step_ne u15 rfl sp_14)))))))
  -- 0x3A: sw a0, 0xC(sp)
  obtain ⟨n23, d23, u23⟩ := u22.self.sw (hcOf F14) sh_at_3a (off' := 0x3C) (by decide)
    (by rw [sp_22]; exact aligned_add hF (by decide))
  rw [sp_22, a0_22, show (0xC : Word) = BitVec.ofNat 32 0xC from rfl] at u23
  obtain ⟨M23, hM23⟩ : ∃ Mx, memStore32 M14 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC) stp = Mx := ⟨_, rfl⟩
  rw [hM23] at u23
  have F23 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M23 x = m.mem x := fun x hx => by
    rw [← hM23, memStore32_get_sep (frame_slot_sep 0xC (by decide) hx), F14 x hx]
  have a0_23 : reg n23 a0 = stp := reg_step_sw u23 a0_22
  -- 0x3C: lw s7, 0x1C(a0)
  obtain ⟨n24, d24, u24⟩ := u23.self.lw (hcOf F23) sh_at_3c (off' := 0x40) (by decide)
    (by rw [a0_23, show stp + (0x1C : Word) = stp + BitVec.ofNat 32 0x1C from rfl]; exact aligned_add env.hstp (by decide))
  rw [a0_23, show stp + (0x1C : Word) = stp + BitVec.ofNat 32 0x1C from rfl, stp_unch F23 0x1C (by decide)] at u24
  -- 0x40: slli a2, a2, 6
  have a2_24 : reg n24 a2 = BitVec.ofNat 32 n :=
    reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl
      (reg_step_ne u19 rfl (reg_step_ne u18 rfl (reg_step_ne u17 rfl (reg_step_ne u16 rfl
        (reg_step_ne u15 rfl ((k14 a2 rfl).trans ha2))))))))))
  obtain ⟨n25, d25, u25⟩ := sha_sll (off' := 0x42) (k := 6) u24.self (hcOf F23) sh_at_40 rfl rfl a2_24
  have a1_25 : reg n25 a1 = bp :=
    reg_step_ne u25 rfl (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl
      (reg_step_ne u20 rfl (reg_step_ne u19 rfl (reg_step_ne u18 rfl (reg_step_ne u17 rfl
        (reg_step_ne u16 rfl (reg_step_ne u15 rfl ((k14 a1 rfl).trans ha1)))))))))))
  -- 0x42: add a2, a2, a1
  obtain ⟨n26, v26, d26, hn_v26, u26⟩ := sha_add (off' := 0x44) u25.self (hcOf F23) sh_at_42 rfl (reg_step_eq u25 rfl) a1_25
  have ev26 : v26 = bp + BitVec.ofNat 32 (64 * n) := hn_v26.symm.trans (sll6_add_bp bp n hn)
  -- 0x44: sw a2, 0x10(sp)
  have sp_26 : reg n26 sp = sp0 + 0xFFFFFF20 :=
    reg_step_ne u26 rfl (reg_step_ne u25 rfl (reg_step_ne u24 rfl (reg_step_sw u23 sp_22)))
  obtain ⟨n27, d27, u27⟩ := u26.self.sw (hcOf F23) sh_at_44 (off' := 0x46) (by decide)
    (by rw [sp_26]; exact aligned_add hF (by decide))
  rw [sp_26, (reg_step_eq u26 rfl).trans ev26, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl] at u27
  obtain ⟨M27, hM27⟩ : ∃ Mx, memStore32 M23 (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10) (bp + BitVec.ofNat 32 (64 * n)) = Mx := ⟨_, rfl⟩
  rw [hM27] at u27
  have F27 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → M27 x = m.mem x := fun x hx => by
    rw [← hM27, memStore32_get_sep (frame_slot_sep 0x10 (by decide) hx), F23 x hx]
  -- 0x46: li s3, 3; 0x48: addi s4, sp, 0x6C
  obtain ⟨n28, d28, u28⟩ := sha_li (off' := 0x48) u27.self (hcOf F27) sh_at_46 rfl
  have sp_28 : reg n28 sp = sp0 + 0xFFFFFF20 := reg_step_ne u28 rfl (reg_step_sw u27 sp_26)
  obtain ⟨n29, d29, u29⟩ := sha_addi_c (off' := 0x4C) (c := sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x6C)
    u28.self (hcOf F27) sh_at_48 rfl sp_28 rfl
  -- Now switch pc base from shaHead (which is at P, so St M27 P n29 0x4C)
  refine ⟨n29, M14,
    .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
      (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19
        (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28
          (.single d29)))))))))))))))))))))))))))),
    ⟨⟨u29.pc, rfl, fun _ => rfl⟩, reg_step_ne u29 rfl sp_28, ?_, reg_step_ne u29 rfl (reg_step_eq u28 rfl), reg_step_eq u29 rfl, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx _ => by rw [u29.mem]; exact F27 x hx⟩, ?_⟩
  · -- s1 = bp + 0
    rw [Nat.mul_zero, add_ofNat_zero]
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl
        (reg_step_ne u19 rfl (reg_step_ne u18 rfl (reg_step_ne u17 rfl (reg_step_ne u16 rfl
          (reg_step_eq u15 rfl))))))))))))))
  · -- tp
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl
        (reg_step_ne u19 rfl (reg_step_ne u18 rfl (reg_step_ne u17 rfl (reg_step_ne u16 rfl
          (reg_step_ne u15 rfl (k14 (4 : Fin 32) rfl)))))))))))))))
  · -- s8 = hv.a (set at u16)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl
        (reg_step_ne u19 rfl (reg_step_ne u18 rfl (reg_step_ne u17 rfl (reg_step_eq u16 rfl)))))))))))))
  · -- s5 = hv.b (set at u17)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl
        (reg_step_ne u19 rfl (reg_step_ne u18 rfl (reg_step_eq u17 rfl))))))))))))
  · -- s9 = hv.c (set at u18)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl
        (reg_step_ne u19 rfl (reg_step_eq u18 rfl)))))))))))
  · -- s10 = hv.d (set at u19)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_ne u20 rfl
        (reg_step_eq u19 rfl))))))))))
  · -- s2 = hv.e (set at u20)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_ne u21 rfl (reg_step_eq u20 rfl)))))))))
  · -- s11 = hv.f (set at u21)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_ne u22 rfl (reg_step_eq u21 rfl))))))))
  · -- s6 = hv.g (set at u22)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_ne u24 rfl (reg_step_sw u23 (reg_step_eq u22 rfl)))))))
  · -- s7 = hv.h (set at u24)
    exact reg_step_ne u29 rfl (reg_step_ne u28 rfl (reg_step_sw u27 (reg_step_ne u26 rfl (reg_step_ne u25 rfl
      (reg_step_eq u24 rfl)))))
  · -- wordsAt M27 stp 8 = (hvOf m.mem stp).toList
    rw [← wordsAt8_hvOf]
    rw [u29.mem]; unfold wordsAt; exact List.map_congr_left fun i hi => stp_unch F27 (4 * i) (by have := List.mem_range.mp hi; omega)
  · -- m0c
    rw [u29.mem]; exact load_store_ne (c := 0x10) (d := 0xC) hM27 rfl (load_store_eq hM23)
  · -- m10
    rw [u29.mem]; exact load_store_eq hM27
  · -- sv
    intro c h1 h2
    rw [u29.mem, ← hM27, memStore32_get_sep (sep_offsets _ (.inl (by omega)) (by decide) (by omega)),
      ← hM23, memStore32_get_sep (sep_offsets _ (.inl (by omega)) (by decide) (by omega))]
  · -- shaSaved in M14
    intro r c h
    simp only [shaSaved, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [← hM14, ← hM13, ← hM12, ← hM11, ← hM10, ← hM9, ← hM8, ← hM7, ← hM6, ← hM5, ← hM4, ← hM3, ← hM2]
      simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]

set_option maxHeartbeats 4000000 in
/-- Epilogue of `compress256` (0x2B68..0x2B86). -/
theorem sha_epi {M0 Ms M : Word → BitVec 8} {P sp0 stp bp : Word} {n : Nat} {tp0 : Word} {m : Machine}
    (env : SCEnv M0 P sp0 stp bp n)
    (st : St M P m 0x2B68 (reg m)) (rsp : reg m sp = sp0 + 0xFFFFFF20) (rtp : reg m (4 : Fin 32) = tp0)
    (sv : ∀ c, 0xAC ≤ c → c < 0xE0 →
      M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) = Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c))
    (fr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x) :
    ∃ m', Steps m m' ∧ m'.pc = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xDC) &&& ~~~1 ∧
      m'.mem = M ∧ reg m' sp = sp0 ∧ reg m' (4 : Fin 32) = tp0 ∧
      ∀ r c, (r, c) ∈ shaSaved → reg m' r = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) := by
  have cT := env.tailCode fr
  have hF := env.hF
  have s0 : St M (P + BitVec.ofNat 32 0x2B64) m 4 (reg m) := St.rebase (s := 0x2B64) (k := 4) st
  have ld : ∀ c, 0xAC ≤ c → c + 4 ≤ 0xE0 →
      memLoad32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact sv (c + j) (by omega) (by omega)
  obtain ⟨n1, d1, u1⟩ := s0.lw cT st_at_4 (off' := 0x6) (by decide)
    (by rw [rsp, show (sp0 + 0xFFFFFF20 + (0xDC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xDC from rfl]; exact aligned_add hF (by decide))
  rw [rsp, show (sp0 + 0xFFFFFF20 + (0xDC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xDC from rfl, ld 0xDC (by decide) (by decide)] at u1
  have v1 : reg n1 ra = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xDC) := reg_step_eq u1 rfl
  have sp_1 : reg n1 sp = sp0 + 0xFFFFFF20 := reg_step_ne u1 rfl rsp
  obtain ⟨n2, d2, u2⟩ := u1.self.lw cT st_at_6 (off' := 0x8) (by decide)
    (by rw [sp_1, show (sp0 + 0xFFFFFF20 + (0xD8 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD8 from rfl]; exact aligned_add hF (by decide))
  rw [sp_1, show (sp0 + 0xFFFFFF20 + (0xD8 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD8 from rfl, ld 0xD8 (by decide) (by decide)] at u2
  have v2 : reg n2 (8 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD8) := reg_step_eq u2 rfl
  have sp_2 : reg n2 sp = sp0 + 0xFFFFFF20 := reg_step_ne u2 rfl sp_1
  obtain ⟨n3, d3, u3⟩ := u2.self.lw cT st_at_8 (off' := 0xA) (by decide)
    (by rw [sp_2, show (sp0 + 0xFFFFFF20 + (0xD4 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD4 from rfl]; exact aligned_add hF (by decide))
  rw [sp_2, show (sp0 + 0xFFFFFF20 + (0xD4 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD4 from rfl, ld 0xD4 (by decide) (by decide)] at u3
  have v3 : reg n3 (9 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD4) := reg_step_eq u3 rfl
  have sp_3 : reg n3 sp = sp0 + 0xFFFFFF20 := reg_step_ne u3 rfl sp_2
  obtain ⟨n4, d4, u4⟩ := u3.self.lw cT st_at_a (off' := 0xC) (by decide)
    (by rw [sp_3, show (sp0 + 0xFFFFFF20 + (0xD0 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD0 from rfl]; exact aligned_add hF (by decide))
  rw [sp_3, show (sp0 + 0xFFFFFF20 + (0xD0 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD0 from rfl, ld 0xD0 (by decide) (by decide)] at u4
  have v4 : reg n4 (18 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xD0) := reg_step_eq u4 rfl
  have sp_4 : reg n4 sp = sp0 + 0xFFFFFF20 := reg_step_ne u4 rfl sp_3
  obtain ⟨n5, d5, u5⟩ := u4.self.lw cT st_at_c (off' := 0xE) (by decide)
    (by rw [sp_4, show (sp0 + 0xFFFFFF20 + (0xCC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xCC from rfl]; exact aligned_add hF (by decide))
  rw [sp_4, show (sp0 + 0xFFFFFF20 + (0xCC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xCC from rfl, ld 0xCC (by decide) (by decide)] at u5
  have v5 : reg n5 (19 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xCC) := reg_step_eq u5 rfl
  have sp_5 : reg n5 sp = sp0 + 0xFFFFFF20 := reg_step_ne u5 rfl sp_4
  obtain ⟨n6, d6, u6⟩ := u5.self.lw cT st_at_e (off' := 0x10) (by decide)
    (by rw [sp_5, show (sp0 + 0xFFFFFF20 + (0xC8 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC8 from rfl]; exact aligned_add hF (by decide))
  rw [sp_5, show (sp0 + 0xFFFFFF20 + (0xC8 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC8 from rfl, ld 0xC8 (by decide) (by decide)] at u6
  have v6 : reg n6 (20 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC8) := reg_step_eq u6 rfl
  have sp_6 : reg n6 sp = sp0 + 0xFFFFFF20 := reg_step_ne u6 rfl sp_5
  obtain ⟨n7, d7, u7⟩ := u6.self.lw cT st_at_10 (off' := 0x12) (by decide)
    (by rw [sp_6, show (sp0 + 0xFFFFFF20 + (0xC4 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC4 from rfl]; exact aligned_add hF (by decide))
  rw [sp_6, show (sp0 + 0xFFFFFF20 + (0xC4 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC4 from rfl, ld 0xC4 (by decide) (by decide)] at u7
  have v7 : reg n7 (21 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC4) := reg_step_eq u7 rfl
  have sp_7 : reg n7 sp = sp0 + 0xFFFFFF20 := reg_step_ne u7 rfl sp_6
  obtain ⟨n8, d8, u8⟩ := u7.self.lw cT st_at_12 (off' := 0x14) (by decide)
    (by rw [sp_7, show (sp0 + 0xFFFFFF20 + (0xC0 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC0 from rfl]; exact aligned_add hF (by decide))
  rw [sp_7, show (sp0 + 0xFFFFFF20 + (0xC0 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC0 from rfl, ld 0xC0 (by decide) (by decide)] at u8
  have v8 : reg n8 (22 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC0) := reg_step_eq u8 rfl
  have sp_8 : reg n8 sp = sp0 + 0xFFFFFF20 := reg_step_ne u8 rfl sp_7
  obtain ⟨n9, d9, u9⟩ := u8.self.lw cT st_at_14 (off' := 0x16) (by decide)
    (by rw [sp_8, show (sp0 + 0xFFFFFF20 + (0xBC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xBC from rfl]; exact aligned_add hF (by decide))
  rw [sp_8, show (sp0 + 0xFFFFFF20 + (0xBC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xBC from rfl, ld 0xBC (by decide) (by decide)] at u9
  have v9 : reg n9 (23 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xBC) := reg_step_eq u9 rfl
  have sp_9 : reg n9 sp = sp0 + 0xFFFFFF20 := reg_step_ne u9 rfl sp_8
  obtain ⟨n10, d10, u10⟩ := u9.self.lw cT st_at_16 (off' := 0x18) (by decide)
    (by rw [sp_9, show (sp0 + 0xFFFFFF20 + (0xB8 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB8 from rfl]; exact aligned_add hF (by decide))
  rw [sp_9, show (sp0 + 0xFFFFFF20 + (0xB8 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB8 from rfl, ld 0xB8 (by decide) (by decide)] at u10
  have v10 : reg n10 (24 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB8) := reg_step_eq u10 rfl
  have sp_10 : reg n10 sp = sp0 + 0xFFFFFF20 := reg_step_ne u10 rfl sp_9
  obtain ⟨n11, d11, u11⟩ := u10.self.lw cT st_at_18 (off' := 0x1A) (by decide)
    (by rw [sp_10, show (sp0 + 0xFFFFFF20 + (0xB4 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB4 from rfl]; exact aligned_add hF (by decide))
  rw [sp_10, show (sp0 + 0xFFFFFF20 + (0xB4 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB4 from rfl, ld 0xB4 (by decide) (by decide)] at u11
  have v11 : reg n11 (25 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB4) := reg_step_eq u11 rfl
  have sp_11 : reg n11 sp = sp0 + 0xFFFFFF20 := reg_step_ne u11 rfl sp_10
  obtain ⟨n12, d12, u12⟩ := u11.self.lw cT st_at_1a (off' := 0x1C) (by decide)
    (by rw [sp_11, show (sp0 + 0xFFFFFF20 + (0xB0 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB0 from rfl]; exact aligned_add hF (by decide))
  rw [sp_11, show (sp0 + 0xFFFFFF20 + (0xB0 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB0 from rfl, ld 0xB0 (by decide) (by decide)] at u12
  have v12 : reg n12 (26 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xB0) := reg_step_eq u12 rfl
  have sp_12 : reg n12 sp = sp0 + 0xFFFFFF20 := reg_step_ne u12 rfl sp_11
  obtain ⟨n13, d13, u13⟩ := u12.self.lw cT st_at_1c (off' := 0x1E) (by decide)
    (by rw [sp_12, show (sp0 + 0xFFFFFF20 + (0xAC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xAC from rfl]; exact aligned_add hF (by decide))
  rw [sp_12, show (sp0 + 0xFFFFFF20 + (0xAC : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xAC from rfl, ld 0xAC (by decide) (by decide)] at u13
  have v13 : reg n13 (27 : Fin 32) = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xAC) := reg_step_eq u13 rfl
  have sp_13 : reg n13 sp = sp0 + 0xFFFFFF20 := reg_step_ne u13 rfl sp_12
  -- 0x1E: addi sp, sp, 0xE0
  obtain ⟨n14, d14, u14⟩ := sha_addi_c (off' := 0x20) (c := sp0) u13.self cT st_at_1e rfl sp_13
    (by rw [BitVec.add_assoc]; exact BitVec.add_zero _)
  -- 0x20: ret
  obtain ⟨n15, d15, pc15, mem15, regs15⟩ := u14.self.jalr cT st_at_20
  have ra_14 : reg n14 ra = memLoad32 Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xDC) :=
    reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
      (reg_step_ne u9 rfl (reg_step_ne u8 rfl (reg_step_ne u7 rfl (reg_step_ne u6 rfl (reg_step_ne u5 rfl
        (reg_step_ne u4 rfl (reg_step_ne u3 rfl (reg_step_ne u2 rfl v1))))))))))))
  refine ⟨n15, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.single d15)))))))))))))), ?_, mem15, ?_, ?_, ?_⟩
  · rw [pc15, ra_14, add_lit_zero]
  · rw [regs15]; exact reg_step_eq u14 rfl
  · rw [regs15]
    exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
      (reg_step_ne u9 rfl (reg_step_ne u8 rfl (reg_step_ne u7 rfl (reg_step_ne u6 rfl (reg_step_ne u5 rfl
        (reg_step_ne u4 rfl (reg_step_ne u3 rfl (reg_step_ne u2 rfl (reg_step_ne u1 rfl rtp)))))))))))))
  · intro r c h
    rw [regs15]
    simp only [shaSaved, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ra_14
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
        (reg_step_ne u9 rfl (reg_step_ne u8 rfl (reg_step_ne u7 rfl (reg_step_ne u6 rfl (reg_step_ne u5 rfl
          (reg_step_ne u4 rfl (reg_step_ne u3 rfl v2)))))))))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
        (reg_step_ne u9 rfl (reg_step_ne u8 rfl (reg_step_ne u7 rfl (reg_step_ne u6 rfl (reg_step_ne u5 rfl
          (reg_step_ne u4 rfl v3))))))))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
        (reg_step_ne u9 rfl (reg_step_ne u8 rfl (reg_step_ne u7 rfl (reg_step_ne u6 rfl (reg_step_ne u5 rfl v4)))))))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
        (reg_step_ne u9 rfl (reg_step_ne u8 rfl (reg_step_ne u7 rfl (reg_step_ne u6 rfl v5))))))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
        (reg_step_ne u9 rfl (reg_step_ne u8 rfl (reg_step_ne u7 rfl v6)))))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
        (reg_step_ne u9 rfl (reg_step_ne u8 rfl v7))))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
        (reg_step_ne u9 rfl v8)))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl v9))))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl (reg_step_ne u11 rfl v10)))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl (reg_step_ne u12 rfl v11))
    · exact reg_step_ne u14 rfl (reg_step_ne u13 rfl v12)
    · exact reg_step_ne u14 rfl v13


/-! ## Inner 16-word big-endian load loop (0x5E..0xA2) -/


theorem k7_flags : ∀ q : Fin 32, (q.val == 0 || q.val == 1 || q.val == 10 || q.val == 11 || q.val == 12) = false →
    q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧
    (q.val == 0 || q.val == 10) = false ∧ (q.val == 0 || q.val == 11) = false ∧ (q.val == 0 || q.val == 12) = false := by decide

theorem k18_flags : ∀ q : Fin 32,
    (q.val == 0 || q.val == 1 || q.val == 10 || q.val == 11 || q.val == 12 || q.val == 13) = false →
    (q.val == 0 || q.val == 1 || q.val == 10 || q.val == 11 || q.val == 12) = false ∧
    (q.val == 0 || q.val == 10) = false ∧ (q.val == 0 || q.val == 11) = false ∧
    (q.val == 0 || q.val == 12) = false ∧ (q.val == 0 || q.val == 13) = false := by decide

theorem k22_flags : ∀ q : Fin 32,
    (q.val == 0 || q.val == 1 || q.val == 8 || q.val == 10 || q.val == 11 || q.val == 12 || q.val == 13) = false →
    (q.val == 0 || q.val == 1 || q.val == 10 || q.val == 11 || q.val == 12 || q.val == 13) = false ∧
    (q.val == 0 || q.val == 8) = false ∧ (q.val == 0 || q.val == 11) = false := by decide

theorem k5_flags : ∀ q : Fin 32, (q.val == 0 || q.val == 8 || q.val == 10) = false →
    (q.val == 0 || q.val == 8) = false ∧ (q.val == 0 || q.val == 10) = false := by decide

theorem lt16_sub_ne_zero {i : Nat} (hi : i < 16) :
    branchTaken .beq (BitVec.ofNat 32 (4 * i) + 0xFFFFFFC0) 0 = false := by
  unfold branchTaken
  simp only [beq_eq_false_iff_ne]
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have h1 : (0xFFFFFFC0 : Word).toNat = 4294967232 := rfl
  have h2 : (0 : Word).toNat = 0 := rfl
  rw [h1, h2] at this
  omega

theorem eq16_sub_zero : branchTaken .beq (BitVec.ofNat 32 (4 * 16) + 0xFFFFFFC0) 0 = true := by decide

theorem bltu_3_rem {i : Nat} (hi : i < 16) :
    branchTaken .bltu 0x3 (BitVec.ofNat 32 (0x40 - 4 * i)) = true := by
  unfold branchTaken
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  have h3 : (0x3 : Word).toNat = 3 := rfl
  rw [h3, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true (by omega)

set_option maxHeartbeats 8000000 in
/-- One iteration of the big-endian word-loading loop (0x5E..0x5E), advancing `i` to `i + 1`. -/
theorem sha_load_iter {M0 Ms M : Word → BitVec 8} {P sp0 stp bp : Word} {n j i : Nat}
    {hv : Sha256.V8} {tp0 : Word} {m : Machine}
    (env : SCEnv M0 P sp0 stp bp n) (hj : j < n) (hi : i < 16)
    (I : ShaLoadInv M0 Ms P sp0 stp bp n j i hv tp0 M m) :
    ∃ m' M', Steps m m' ∧ ShaLoadInv M0 Ms P sp0 stp bp n j (i + 1) hv tp0 M' m' := by
  have cH := env.headCode I.fr
  have cI := env.idxCode I.fr
  have hF := env.hF
  -- 0x5E: addi a0, s0, -0x40
  obtain ⟨n1, d1, u1⟩ := I.st.aluImm cH sh_at_5e (off' := 0x62) (by decide)
  have a0_1 : reg n1 a0 = BitVec.ofNat 32 (4 * i) + 0xFFFFFFC0 := by
    rw [reg_step_eq u1 rfl, I.rs0]; rfl
  -- 0x62: beqz a0, 0xA2 (not taken since i < 16)
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken cH 0x64 sh_at_62 (by decide)
    (by rw [a0_1, u1.self.zero]; exact lt16_sub_ne_zero hi)
  -- 0x64: li a2, 0x40; 0x68: mv a0, s0; 0x6A: mv a1, s1
  obtain ⟨n3, d3, u3⟩ := sha_li (off' := 0x68) u2.self cH sh_at_64 rfl
  have s0_3 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 (4 * i) :=
    reg_step_ne u3 rfl (reg_step_sw u2 (reg_step_ne u1 rfl I.rs0))
  obtain ⟨n4, d4, u4⟩ := sha_mv (off' := 0x6A) u3.self cH sh_at_68 rfl s0_3
  have s1_4 : reg n4 (9 : Fin 32) = bp + BitVec.ofNat 32 (64 * j) :=
    reg_step_ne u4 rfl (reg_step_ne u3 rfl (reg_step_sw u2 (reg_step_ne u1 rfl I.rs1)))
  obtain ⟨n5, d5, u5⟩ := sha_mv (off' := 0x6C) u4.self cH sh_at_6a rfl s1_4
  -- 0x6C..0x74: call shaIndexCode at P + 0x2B94
  have hbI : P + BitVec.ofNat 32 0x6C + 0x3000 + 0xFFFFFB28 = P + 0x2B94 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨n6, c6, pc6, mem6, regs6⟩ := u5.self.callRa cH sh_at_6c sh_at_70 hbI
    (even_at P env.hP 0x2B94 (by decide))
  have r6 := PEnv.reg1 regs6 u5.self.zero
  obtain ⟨n7, c7, pc7, mem7, r7a0, r7a1, _, r7k⟩ := shaIndex_ok (off := 4 * i)
    (cur := bp + BitVec.ofNat 32 (64 * j)) (retAddr := P + BitVec.ofNat 32 0x74)
    (by rw [mem6]; exact cI) pc6 (by omega)
    (by rw [r6 a0 (by decide)]; exact reg_step_ne u5 rfl (reg_step_eq u4 rfl))
    (by rw [r6 a1 (by decide)]; exact reg_step_eq u5 rfl)
    (by rw [r6 a2 (by decide)]; exact reg_step_ne u5 rfl (reg_step_ne u4 rfl (reg_step_eq u3 rfl)))
    (by rw [regs6]; simp +decide [upd])
    (even_clear _ (even_at P env.hP 0x74 (by decide)))
  have s7 : St M P n7 0x74 (reg n7) := ⟨pc7, mem7.trans mem6, fun _ => rfl⟩
  have k7 : ∀ q, (q.val == 0 || q.val == 1 || q.val == 10 || q.val == 11 || q.val == 12) = false →
      reg n7 q = reg m q := fun q hq => by
    obtain ⟨h10, h11, h12, h1, n10, n11, n12⟩ := k7_flags q hq
    rw [r7k q h10 h11 h12, r6 q h1]
    exact reg_step_ne u5 n11 (reg_step_ne u4 n10 (reg_step_ne u3 n12 (reg_step_sw u2 (reg_step_ne u1 n10 rfl))))
  -- 0x74: bltu s3, a1, 0x7C (taken since 3 < 64 - 4*i)
  obtain ⟨n8, d8, u8⟩ := s7.taken cH 0x7C sh_at_74 (by decide)
    (by rw [k7 (19 : Fin 32) rfl, I.rs3, r7a1]; exact bltu_3_rem hi)
  -- 0x7C..0x8C: four lbu from p = cur + 4*i
  let cur := bp + BitVec.ofNat 32 (64 * j)
  let p := cur + BitVec.ofNat 32 (4 * i)
  have a0_8 : reg n8 a0 = p := (u8.regs a0).trans r7a0
  obtain ⟨n9, d9, u9⟩ := u8.self.lbu cH sh_at_7c (off' := 0x80) (by decide)
  have a0_9 : reg n9 a0 = p := reg_step_ne u9 rfl a0_8
  obtain ⟨n10, d10, u10⟩ := u9.self.lbu cH sh_at_80 (off' := 0x84) (by decide)
  have a0_10 : reg n10 a0 = p := reg_step_ne u10 rfl a0_9
  obtain ⟨n11, d11, u11⟩ := u10.self.lbu cH sh_at_84 (off' := 0x88) (by decide)
  have a0_11 : reg n11 a0 = p := reg_step_ne u11 rfl a0_10
  obtain ⟨n12, d12, u12⟩ := u11.self.lbu cH sh_at_88 (off' := 0x8C) (by decide)
  -- 0x8C..0x98: shifts and ors
  have a1_12 : reg n12 a1 = (M (p + 2)).zeroExtend 32 :=
    reg_step_ne u12 rfl (reg_step_ne u11 rfl (reg_step_ne u10 rfl
      ((reg_step_eq u9 rfl).trans (by rw [a0_8]))))
  have a2_12 : reg n12 a2 = (M (p + 0)).zeroExtend 32 :=
    reg_step_ne u12 rfl (reg_step_ne u11 rfl ((reg_step_eq u10 rfl).trans (by rw [a0_9])))
  have a3_12 : reg n12 a3 = (M (p + 1)).zeroExtend 32 :=
    reg_step_ne u12 rfl ((reg_step_eq u11 rfl).trans (by rw [a0_10]))
  have a0_12 : reg n12 a0 = (M (p + 3)).zeroExtend 32 :=
    (reg_step_eq u12 rfl).trans (by rw [a0_11])
  obtain ⟨n13, d13, u13⟩ := sha_sll (off' := 0x8E) (k := 8) u12.self cH sh_at_8c rfl rfl a1_12
  obtain ⟨n14, d14, u14⟩ := sha_sll (off' := 0x90) (k := 16) u13.self cH sh_at_8e rfl rfl (reg_step_ne u13 rfl a3_12)
  obtain ⟨n15, d15, u15⟩ := sha_sll (off' := 0x92) (k := 24) u14.self cH sh_at_90 rfl rfl
    (reg_step_ne u14 rfl (reg_step_ne u13 rfl a2_12))
  -- 0x92: or a0, a0, a1; 0x94: or a2, a2, a3; 0x96: or a0, a0, a2
  obtain ⟨n16, v16, d16, hn16, u16⟩ := sha_alu (off' := 0x94) u15.self cH sh_at_92 rfl
    (reg_step_ne u15 rfl (reg_step_ne u14 rfl (reg_step_ne u13 rfl a0_12)))
    (reg_step_ne u15 rfl (reg_step_ne u14 rfl (reg_step_eq u13 rfl)))
  obtain ⟨n17, v17, d17, hn17, u17⟩ := sha_alu (off' := 0x96) u16.self cH sh_at_94 rfl
    (reg_step_ne u16 rfl (reg_step_eq u15 rfl))
    (reg_step_ne u16 rfl (reg_step_ne u15 rfl (reg_step_eq u14 rfl)))
  obtain ⟨n18, v18, d18, hn18, u18⟩ := sha_alu (off' := 0x98) u17.self cH sh_at_96 rfl
    (reg_step_ne u17 rfl (reg_step_eq u16 rfl))
    (reg_step_eq u17 rfl)
  -- Prove v18 = (schedule (memBytes M0 cur 64))[i]!
  have bytes_unch : memBytes M cur 64 = memBytes M0 cur 64 :=
    memBytes_congr fun k hk => I.fr _
      (by
        have := env.bF.sub (c := 64 * j + k) (l := 1) (by omega)
        rw [← add_ofNat_assoc] at this; exact this.symm)
      (by
        have := env.bSt.sub (c := 64 * j + k) (l := 1) (by omega)
        rw [← add_ofNat_assoc] at this; exact this.symm)
  have ev18 : v18 = (Sha256.schedule (memBytes M0 cur 64))[i]! := by
    rw [← hn18, ← hn16, ← hn17]
    show (((M (p + 3)).zeroExtend 32 ||| ((M (p + 2)).zeroExtend 32 <<< 8)) |||
      (((M (p + 0)).zeroExtend 32 <<< 24) ||| ((M (p + 1)).zeroExtend 32 <<< 16))) = _
    rw [be32_wordAt M cur hi, bytes_unch]
  -- Propagate non-(a0..a3, ra) registers from n7 to n18
  have k18 : ∀ q, (q.val == 0 || q.val == 1 || q.val == 10 || q.val == 11 || q.val == 12 || q.val == 13) = false →
      reg n18 q = reg m q := fun q hq => by
    obtain ⟨hq7, n10, n11, n12, n13⟩ := k18_flags q hq
    exact reg_step_ne u18 n10 (reg_step_ne u17 n12 (reg_step_ne u16 n10 (reg_step_ne u15 n12
      (reg_step_ne u14 n13 (reg_step_ne u13 n11 (reg_step_ne u12 n10 (reg_step_ne u11 n13
        (reg_step_ne u10 n12 (reg_step_ne u9 n11 (reg_step_sw u8 (k7 q hq7)))))))))))
  -- 0x98: add a1, s4, s0
  obtain ⟨n19, v19, d19, hn19, u19⟩ := sha_add (off' := 0x9C) u18.self cH sh_at_98 rfl
    ((k18 (20 : Fin 32) rfl).trans I.rs4) ((k18 (8 : Fin 32) rfl).trans I.rs0)
  have ev19 : v19 = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 (0x6C + 4 * i) :=
    hn19.symm.trans (add_ofNat_assoc (sp0 + 0xFFFFFF20) 0x6C (4 * i))
  -- 0x9C: sw a0, 0(a1)
  have a1_19 : reg n19 a1 = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 (0x6C + 4 * i) :=
    (reg_step_eq u19 rfl).trans ev19
  have a0_19 : reg n19 a0 = (Sha256.schedule (memBytes M0 cur 64))[i]! :=
    reg_step_ne u19 rfl ((reg_step_eq u18 rfl).trans ev18)
  obtain ⟨n20, d20, u20⟩ := u19.self.sw cH sh_at_9c (off' := 0x9E) (by decide)
    (by rw [a1_19, add_lit_zero]; exact aligned_add hF (by omega))
  rw [a1_19, add_lit_zero, a0_19] at u20
  obtain ⟨M20, hM20⟩ : ∃ Mx, memStore32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 (0x6C + 4 * i))
      (Sha256.schedule (memBytes M0 cur 64))[i]! = Mx := ⟨_, rfl⟩
  rw [hM20] at u20
  have F20 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M20 x = M0 x := fun x hx hst => by
    rw [← hM20, memStore32_get_sep (frame_slot_sep (0x6C + 4 * i) (by omega) hx), I.fr x hx hst]
  -- 0x9E: addi s0, s0, 4
  have s0_20 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 (4 * i) :=
    reg_step_sw u20 (reg_step_ne u19 rfl ((k18 (8 : Fin 32) rfl).trans I.rs0))
  obtain ⟨n21, d21, u21⟩ := sha_addi_c (off' := 0xA0) (c := BitVec.ofNat 32 (4 * (i + 1)))
    u20.self (env.headCode F20) sh_at_9e rfl s0_20
    (by show BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _; rw [ofNat_add_ofNat, show 4 * i + 4 = 4 * (i + 1) by omega])
  -- 0xA0: j 0x5E
  obtain ⟨n22, d22, u22⟩ := u21.self.jump (env.headCode F20) sh_at_a0 (off' := 0x5E) (by decide)
    (by rw [u21.self.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x5E (by decide)))
  have k22 : ∀ q, (q.val == 0 || q.val == 1 || q.val == 8 || q.val == 10 || q.val == 11 || q.val == 12 || q.val == 13) = false →
      reg n22 q = reg m q := fun q hq => by
    obtain ⟨hq18, n8, n11⟩ := k22_flags q hq
    exact (u22.regs q).trans (reg_step_ne u21 n8 (reg_step_sw u20 (reg_step_ne u19 n11 (k18 q hq18))))
  refine ⟨n22, M20,
    .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (c7.trans
      (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15
        (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.single d22))))))))))))))))))))),
    ⟨u22.self, (k22 sp rfl).trans I.rsp, (u22.regs _).trans (reg_step_eq u21 rfl),
      (k22 (9 : Fin 32) rfl).trans I.rs1, (k22 (19 : Fin 32) rfl).trans I.rs3, (k22 (20 : Fin 32) rfl).trans I.rs4,
      (k22 (4 : Fin 32) rfl).trans I.rtp,
      (k22 (24 : Fin 32) rfl).trans I.ra_v, (k22 (21 : Fin 32) rfl).trans I.rb_v,
      (k22 (25 : Fin 32) rfl).trans I.rc_v, (k22 (26 : Fin 32) rfl).trans I.rd_v,
      (k22 (18 : Fin 32) rfl).trans I.re_v, (k22 (27 : Fin 32) rfl).trans I.rf_v,
      (k22 (22 : Fin 32) rfl).trans I.rg_v, (k22 (23 : Fin 32) rfl).trans I.rh_v,
      ?_, ?_, ?_, ?_, ?_, ?_, F20⟩⟩
  · -- hst: wordsAt M20 stp 8 = hv.toList
    rw [← I.hst]
    unfold wordsAt
    refine List.map_congr_left fun k hk => memLoad32_congr fun b hb => ?_
    rw [← hM20]
    refine memStore32_get_sep ?_
    have := (env.stF.sub (c := 4 * k + b) (l := 1) (by have := List.mem_range.mp hk; omega)).subR
      (c := 0x6C + 4 * i) (l := 4) (by omega)
    rw [← add_ofNat_assoc] at this
    exact this.symm
  · -- m0c
    rw [← hM20, memLoad32_store32_sep (sep_offsets _ (.inr (by omega)) (by omega) (by decide))]
    exact I.m0c
  · -- m10
    rw [← hM20, memLoad32_store32_sep (sep_offsets _ (.inr (by omega)) (by omega) (by decide))]
    exact I.m10
  · -- m40
    rw [← hM20, memLoad32_store32_sep (sep_offsets _ (.inr (by omega)) (by omega) (by decide))]
    exact I.m40
  · -- win for k < i + 1
    intro k hk
    by_cases hki : k = i
    · subst hki; exact load_store_eq hM20
    · have hlt : k < i := by
        rcases Nat.lt_or_gt_of_ne (Ne.symm hki) with hgt | hlt
        · exfalso; clear hki; omega
        · exact hlt
      clear hki
      rw [← hM20, memLoad32_store32_sep (sep_offsets _ (.inr (by omega)) (by omega) (by omega))]
      exact I.win k hlt
  · -- sv
    intro c h1 h2
    rw [← hM20, memStore32_get_sep (sep_offsets _ (.inl (by omega)) (by omega) (by omega))]
    exact I.sv c h1 h2

/-- Induction over the remaining `rem` words (`i + rem = 16`) of the inner load loop, ending at 0xA2. -/
theorem sha_load_from {M0 Ms : Word → BitVec 8} {P sp0 stp bp : Word} {n j : Nat}
    {hv : Sha256.V8} {tp0 : Word} (env : SCEnv M0 P sp0 stp bp n) (hj : j < n) :
    ∀ rem i {M : Word → BitVec 8} {m : Machine}, i + rem = 16 →
      ShaLoadInv M0 Ms P sp0 stp bp n j i hv tp0 M m →
      ∃ m' M', Steps m m' ∧ St M' P m' 0xA2 (reg m') ∧
        reg m' sp = sp0 + 0xFFFFFF20 ∧ reg m' (4 : Fin 32) = tp0 ∧
        reg m' (24 : Fin 32) = hv.a ∧ reg m' (21 : Fin 32) = hv.b ∧
        reg m' (25 : Fin 32) = hv.c ∧ reg m' (26 : Fin 32) = hv.d ∧
        reg m' (18 : Fin 32) = hv.e ∧ reg m' (27 : Fin 32) = hv.f ∧
        reg m' (22 : Fin 32) = hv.g ∧ reg m' (23 : Fin 32) = hv.h ∧
        memLoad32 M' (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC) = stp ∧
        memLoad32 M' (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10) = bp + BitVec.ofNat 32 (64 * n) ∧
        memLoad32 M' (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x40) = bp + BitVec.ofNat 32 (64 * (j + 1)) ∧
        (∀ k, k < 16 → memLoad32 M' (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 (0x6C + 4 * k)) =
          (Sha256.schedule (memBytes M0 (bp + BitVec.ofNat 32 (64 * j)) 64))[k]!) ∧
        (∀ c, 0xAC ≤ c → c < 0xE0 →
          M' (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) = Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c)) ∧
        (∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M' x = M0 x)
  | 0, i, M, m, hi, I => by
    have rfl_i : i = 16 := by omega
    subst rfl_i
    have cH := env.headCode I.fr
    obtain ⟨n1, d1, u1⟩ := I.st.aluImm cH sh_at_5e (off' := 0x62) (by decide)
    have a0_1 : reg n1 a0 = BitVec.ofNat 32 (4 * 16) + 0xFFFFFFC0 := by
      rw [reg_step_eq u1 rfl, I.rs0]; rfl
    obtain ⟨n2, d2, u2⟩ := u1.self.taken cH 0xA2 sh_at_62 (by decide)
      (by rw [a0_1, u1.self.zero]; exact eq16_sub_zero)
    have k2 : ∀ q, (q.val == 0 || q.val == 10) = false → reg n2 q = reg m q := fun q hq =>
      (u2.regs q).trans (reg_step_ne u1 hq rfl)
    exact ⟨n2, M, .cons d1 (.single d2), u2.self,
      (k2 sp rfl).trans I.rsp, (k2 (4 : Fin 32) rfl).trans I.rtp,
      (k2 (24 : Fin 32) rfl).trans I.ra_v, (k2 (21 : Fin 32) rfl).trans I.rb_v,
      (k2 (25 : Fin 32) rfl).trans I.rc_v, (k2 (26 : Fin 32) rfl).trans I.rd_v,
      (k2 (18 : Fin 32) rfl).trans I.re_v, (k2 (27 : Fin 32) rfl).trans I.rf_v,
      (k2 (22 : Fin 32) rfl).trans I.rg_v, (k2 (23 : Fin 32) rfl).trans I.rh_v,
      I.m0c, I.m10, I.m40, I.win, I.sv, I.fr⟩
  | rem + 1, i, M, m, hi, I => by
    obtain ⟨m1, M1, c1, I1⟩ := sha_load_iter env hj (by omega) I
    obtain ⟨m2, M2, c2, rest⟩ := sha_load_from env hj rem (i + 1) (by omega) I1
    exact ⟨m2, M2, c1.trans c2, rest⟩


/-! ## Outer block loop (0x4C..0x2B68) and top-level `sha256Compress_correct` -/

def hvAfter (hv : Sha256.V8) (blk : Bytes) : Sha256.V8 :=
  let v := vsW (fun t => (Sha256.schedule blk)[t]!) hv 64
  ⟨hv.a + v.a, hv.b + v.b, hv.c + v.c, hv.d + v.d,
   hv.e + v.e, hv.f + v.f, hv.g + v.g, hv.h + v.h⟩

theorem hvAfter_toList (hv : Sha256.V8) (blk : Bytes) :
    (hvAfter hv blk).toList = Sha256.compress hv.toList blk := by
  rw [Sha256.compress_vs]
  unfold hvAfter
  rw [vsW_def]
  rfl

theorem SCEnv.toShaEnv (env : SCEnv M0 P sp0 stp bp n) {Ml : Word → BitVec 8}
    (fr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → Ml x = M0 x)
    (m0c : memLoad32 Ml (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0xC) = stp) :
    ShaEnv Ml P (sp0 + 0xFFFFFF20) stp := by
  have h14 : ∀ {b : Word} {k : Nat}, Sep (sp0 + 0xFFFFFF20) 0xE0 b k →
      Sep (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x14) 0x58 b k :=
    fun h => h.sub (c := 0x14) (l := 0x58) (by decide)
  refine ⟨?_, ?_, env.hP, env.hF, env.hstp, ?_, m0c,
    h14 env.sC, h14 env.s97, h14 env.sK, env.stC, env.stF.subR (c := 0x14) (l := 0x58) (by decide)⟩
  · intro i hi
    rw [fr _ (env.sC.subR (c := i) (l := 1) (by omega)) (env.stC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  · intro i hi
    rw [fr _ (env.s97.subR (c := i) (l := 1) (by omega)) (env.st97.subR (c := i) (l := 1) (by omega))]
    exact env.o97 i hi
  · intro t ht
    rw [← shaK_words env.kdata t ht]
    exact memLoad32_congr fun j hj => fr _
      (by rw [add_ofNat_assoc]; exact env.sK.subR (c := 4 * t + j) (l := 1) (by omega))
      (by rw [add_ofNat_assoc]; exact env.stK.subR (c := 4 * t + j) (l := 1) (by omega))

theorem bp_ne_end {bp : Word} {j n : Nat} (hj : j < n) (hw : bp.toNat + 64 * n < 2 ^ 32) :
    branchTaken .bne (bp + BitVec.ofNat 32 (64 * j)) (bp + BitVec.ofNat 32 (64 * n)) = true := by
  unfold branchTaken
  simp only [bne_iff_ne]
  exact add_ofNat_ne bp (by omega) (by omega) (by omega)

theorem bp_eq_end (bp : Word) (n : Nat) :
    branchTaken .bne (bp + BitVec.ofNat 32 (64 * n)) (bp + BitVec.ofNat 32 (64 * n)) = false := by
  unfold branchTaken; simp

set_option maxHeartbeats 8000000 in
/-- One full block iteration of `compress256` (0x4C..0x4C), advancing `j` to `j + 1`
and `hv` to `hvAfter hv (memBytes M0 (bp + 64 * j) 64)`. -/
theorem sha_block_iter {M0 Ms M : Word → BitVec 8} {P sp0 stp bp : Word} {n j : Nat}
    {hv : Sha256.V8} {tp0 : Word} {m : Machine}
    (env : SCEnv M0 P sp0 stp bp n) (hj : j < n)
    (I : ShaLoopInv M0 Ms P sp0 stp bp n j hv tp0 M m) :
    ∃ m' M', Steps m m' ∧
      ShaLoopInv M0 Ms P sp0 stp bp n (j + 1)
        (hvAfter hv (memBytes M0 (bp + BitVec.ofNat 32 (64 * j)) 64)) tp0 M' m' := by
  have cH := env.headCode I.fr
  have hF := env.hF
  -- 0x4C: lw a0, 0x10(sp)
  obtain ⟨n1, d1, u1⟩ := I.st.lw cH sh_at_4c (off' := 0x4E) (by decide)
    (by rw [I.rsp, show (sp0 + 0xFFFFFF20 + (0x10 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10 from rfl]; exact aligned_add hF (by decide))
  rw [I.rsp, show (sp0 + 0xFFFFFF20 + (0x10 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10 from rfl, I.m10] at u1
  -- 0x4E: bne s1, a0, 0x56 (taken since j < n)
  obtain ⟨n2, d2, u2⟩ := u1.self.taken cH 0x56 sh_at_4e (by decide)
    (by rw [reg_step_ne u1 rfl I.rs1, reg_step_eq u1 rfl]; exact bp_ne_end hj env.hwbp)
  -- 0x56: li s0, 0
  obtain ⟨n3, d3, u3⟩ := sha_li (off' := 0x58) u2.self cH sh_at_56 rfl
  -- 0x58: addi a0, s1, 0x40
  have s1_3 : reg n3 (9 : Fin 32) = bp + BitVec.ofNat 32 (64 * j) :=
    reg_step_ne u3 rfl (reg_step_sw u2 (reg_step_ne u1 rfl I.rs1))
  obtain ⟨n4, d4, u4⟩ := sha_addi_c (off' := 0x5C) (c := bp + BitVec.ofNat 32 (64 * (j + 1)))
    u3.self cH sh_at_58 rfl s1_3
    (by show bp + BitVec.ofNat 32 (64 * j) + BitVec.ofNat 32 64 = _; rw [add_ofNat_assoc, show 64 * j + 64 = 64 * (j + 1) by omega])
  -- 0x5C: sw a0, 0x40(sp)
  have sp_4 : reg n4 sp = sp0 + 0xFFFFFF20 :=
    reg_step_ne u4 rfl (reg_step_ne u3 rfl (reg_step_sw u2 (reg_step_ne u1 rfl I.rsp)))
  obtain ⟨n5, d5, u5⟩ := u4.self.sw cH sh_at_5c (off' := 0x5E) (by decide)
    (by rw [sp_4]; exact aligned_add hF (by decide))
  rw [sp_4, reg_step_eq u4 rfl, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl] at u5
  obtain ⟨M5, hM5⟩ : ∃ Mx, memStore32 M (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x40)
      (bp + BitVec.ofNat 32 (64 * (j + 1))) = Mx := ⟨_, rfl⟩
  rw [hM5] at u5
  have F5 : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M5 x = M0 x := fun x hx hst => by
    rw [← hM5, memStore32_get_sep (frame_slot_sep 0x40 (by decide) hx), I.fr x hx hst]
  have k5 : ∀ q, (q.val == 0 || q.val == 8 || q.val == 10) = false → reg n5 q = reg m q := fun q hq => by
    obtain ⟨n8, n10⟩ := k5_flags q hq
    exact reg_step_sw u5 (reg_step_ne u4 n10 (reg_step_ne u3 n8 (reg_step_sw u2 (reg_step_ne u1 n10 rfl))))
  -- Build ShaLoadInv at i = 0
  have L0 : ShaLoadInv M0 Ms P sp0 stp bp n j 0 hv tp0 M5 n5 :=
    ⟨u5.self, (k5 sp rfl).trans I.rsp,
      reg_step_sw u5 (reg_step_ne u4 rfl (reg_step_eq u3 rfl)),
      (k5 (9 : Fin 32) rfl).trans I.rs1, (k5 (19 : Fin 32) rfl).trans I.rs3,
      (k5 (20 : Fin 32) rfl).trans I.rs4, (k5 (4 : Fin 32) rfl).trans I.rtp,
      (k5 (24 : Fin 32) rfl).trans I.ra_v, (k5 (21 : Fin 32) rfl).trans I.rb_v,
      (k5 (25 : Fin 32) rfl).trans I.rc_v, (k5 (26 : Fin 32) rfl).trans I.rd_v,
      (k5 (18 : Fin 32) rfl).trans I.re_v, (k5 (27 : Fin 32) rfl).trans I.rf_v,
      (k5 (22 : Fin 32) rfl).trans I.rg_v, (k5 (23 : Fin 32) rfl).trans I.rh_v,
      by
        rw [← I.hst]; unfold wordsAt
        refine List.map_congr_left fun k hk => memLoad32_congr fun b hb => ?_
        rw [← hM5]
        refine memStore32_get_sep ?_
        have := (env.stF.sub (c := 4 * k + b) (l := 1) (by have := List.mem_range.mp hk; omega)).subR
          (c := 0x40) (l := 4) (by decide)
        rw [← add_ofNat_assoc] at this; exact this.symm,
      load_store_ne (c := 0x40) (d := 0xC) hM5 rfl I.m0c,
      load_store_ne (c := 0x40) (d := 0x10) hM5 rfl I.m10,
      load_store_eq hM5,
      fun _ hk => absurd hk (Nat.not_lt_zero _),
      fun c h1 h2 => by
        rw [← hM5, memStore32_get_sep (sep_offsets _ (.inl (by omega)) (by decide) (by omega))]
        exact I.sv c h1 h2,
      F5⟩
  -- Run sha_load_from for 16 words -> reaches 0xA2
  obtain ⟨nl, Ml, cl, sl, l_sp, l_tp, l_a, l_b, l_c, l_d, l_e, l_f, l_g, l_h,
    l_0c, l_10, l_40, l_win, l_sv, l_fr⟩ := sha_load_from env hj 16 0 rfl L0
  -- Run sha_rounds -> reaches 0x2B64
  let blk := memBytes M0 (bp + BitVec.ofNat 32 (64 * j)) 64
  have senv : ShaEnv Ml P (sp0 + 0xFFFFFF20) stp := env.toShaEnv l_fr l_0c
  have hsched : ShaSched (fun t => (Sha256.schedule blk)[t]!) := fun t h1 h2 => Sha256.sched_rec blk h1 h2
  obtain ⟨nr, Mr, cr, sr, fr_r, r_sp, r_tp, r_s1, r_e, r_s3, r_s4, r_b, r_g, r_h, r_a, r_c, r_d, r_f,
    st0, st1, st2, st3, st4, st5, st6, st7⟩ :=
    sha_rounds senv hsched l_win (fun _ _ => rfl) sl l_sp l_tp l_e l_b l_g l_h l_a l_c l_d l_f l_40
  -- Step 0x2B64: j 0x4C (offset 0 of shaTail!)
  have fr_Mr : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → Mr x = M0 x := fun x hx hst =>
    (fr_r x (hx.sub (c := 0x14) (l := 0x58) (by decide)) hst).trans (l_fr x hx hst)
  have sr_tail : St Mr (P + BitVec.ofNat 32 0x2B64) nr 0 (reg nr) := St.rebase0 sr
  obtain ⟨nj, dj, uj⟩ := sr_tail.jump (env.tailCode fr_Mr) st_at_0 (off' := 0xFFFFD4E8) (by decide)
    (by
      rw [sr_tail.pc]
      have eq_pc : P + BitVec.ofNat 32 0x2B64 + BitVec.ofNat 32 0 + 0xFFFFD4E8 = P + BitVec.ofNat 32 0x4C := by
        rw [add_ofNat_zero, BitVec.add_assoc]; rfl
      rw [eq_pc]; exact even_bit0 (even_at P env.hP 0x4C (by decide)))
  have sj : St Mr P nj 0x4C (reg nj) :=
    ⟨by rw [uj.pc, BitVec.add_assoc]; rfl, uj.mem, fun _ => rfl⟩
  have out_R : ∀ o, (0x6C ≤ o ∨ o + 4 ≤ 0x14) → o + 4 ≤ 0xE0 →
      memLoad32 Mr (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 o) = memLoad32 Ml (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 o) :=
    fun o ho ho2 => memLoad32_congr fun b hb => by
      rw [add_ofNat_assoc]
      exact fr_r _
        (sep_offsets _ (by rcases ho with h | h; exact .inl (by omega); exact .inr (by omega)) (by decide) (by omega))
        (by rw [← add_ofNat_assoc]; exact (env.stF.subR (c := o) (l := 4) ho2).subR (c := b) (l := 1) (by omega))
  refine ⟨nj, Mr,
    .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (cl.trans (cr.trans (.single dj))))))),
    ⟨sj, (uj.regs sp).trans r_sp, (uj.regs _).trans r_s1, (uj.regs _).trans r_s3, (uj.regs _).trans r_s4,
      (uj.regs _).trans r_tp,
      (uj.regs _).trans r_a, (uj.regs _).trans r_b, (uj.regs _).trans r_c, (uj.regs _).trans r_d,
      (uj.regs _).trans r_e, (uj.regs _).trans r_f, (uj.regs _).trans r_g, (uj.regs _).trans r_h,
      ?_, (out_R 0xC (.inr (by decide)) (by decide)).trans l_0c,
      (out_R 0x10 (.inr (by decide)) (by decide)).trans l_10, ?_, fr_Mr⟩⟩
  · -- wordsAt Mr stp 8 = (hvAfter hv blk).toList
    rw [wordsAt8_hvOf]; unfold hvOf; rw [st0, st1, st2, st3, st4, st5, st6, st7]; rfl
  · -- sv
    intro c h1 h2
    refine (fr_r _ ?_ ?_).trans (l_sv c h1 h2)
    · exact sep_offsets _ (.inl (by omega)) (by decide) (by omega)
    · exact env.stF.subR (c := c) (l := 1) (by omega)

/-- Induction over the remaining `rem` blocks (`j + rem = n`) of the outer loop, ending at 0x2B68. -/
theorem sha_outer_from {M0 Ms : Word → BitVec 8} {P sp0 stp bp : Word} {n : Nat} {tp0 : Word}
    (env : SCEnv M0 P sp0 stp bp n) :
    ∀ rem j {hv : Sha256.V8} {M : Word → BitVec 8} {m : Machine}, j + rem = n →
      hv.toList = (blockList M0 bp j).foldl Sha256.compress (wordsAt M0 stp 8) →
      ShaLoopInv M0 Ms P sp0 stp bp n j hv tp0 M m →
      ∃ m' M', Steps m m' ∧ St M' P m' 0x2B68 (reg m') ∧
        reg m' sp = sp0 + 0xFFFFFF20 ∧ reg m' (4 : Fin 32) = tp0 ∧
        wordsAt M' stp 8 = (blockList M0 bp n).foldl Sha256.compress (wordsAt M0 stp 8) ∧
        (∀ c, 0xAC ≤ c → c < 0xE0 →
          M' (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c) = Ms (sp0 + 0xFFFFFF20 + BitVec.ofNat 32 c)) ∧
        (∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → M' x = M0 x)
  | 0, j, hv, M, m, hj, hfold, I => by
    have rfl_j : j = n := by omega
    subst rfl_j
    have cH := env.headCode I.fr
    have hF := env.hF
    -- 0x4C: lw a0, 0x10(sp)
    obtain ⟨n1, d1, u1⟩ := I.st.lw cH sh_at_4c (off' := 0x4E) (by decide)
      (by rw [I.rsp, show (sp0 + 0xFFFFFF20 + (0x10 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10 from rfl]; exact aligned_add hF (by decide))
    rw [I.rsp, show (sp0 + 0xFFFFFF20 + (0x10 : Word)) = sp0 + 0xFFFFFF20 + BitVec.ofNat 32 0x10 from rfl, I.m10] at u1
    -- 0x4E: bne s1, a0, 0x56 (not taken since j = n!)
    obtain ⟨n2, d2, u2⟩ := u1.self.notTaken cH 0x52 sh_at_4e (by decide)
      (by rw [reg_step_ne u1 rfl I.rs1, reg_step_eq u1 rfl]; exact bp_eq_end bp j)
    -- 0x52: j 0x2B68
    obtain ⟨n3, d3, u3⟩ := u2.self.jump cH sh_at_52 (off' := 0x2B68) (by decide)
      (by rw [u2.self.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x2B68 (by decide)))
    have k3 : ∀ q, (q.val == 0 || q.val == 10) = false → reg n3 q = reg m q := fun q hq =>
      (u3.regs q).trans (reg_step_sw u2 (reg_step_ne u1 hq rfl))
    exact ⟨n3, M, .cons d1 (.cons d2 (.single d3)), u3.self,
      (k3 sp rfl).trans I.rsp, (k3 (4 : Fin 32) rfl).trans I.rtp,
      I.hst.trans hfold, I.sv, I.fr⟩
  | rem + 1, j, hv, M, m, hj, hfold, I => by
    obtain ⟨m1, M1, c1, I1⟩ := sha_block_iter env (by omega) I
    have hfold1 : (hvAfter hv (memBytes M0 (bp + BitVec.ofNat 32 (64 * j)) 64)).toList =
        (blockList M0 bp (j + 1)).foldl Sha256.compress (wordsAt M0 stp 8) := by
      rw [blockList_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hfold, hvAfter_toList]
    obtain ⟨m2, M2, c2, rest⟩ := sha_outer_from env rem (j + 1) (by omega) hfold1 I1
    exact ⟨m2, M2, c1.trans c2, rest⟩

/-- Every preserved register of `compress256` (`ra`, `sp`, `tp`, `s0..s11`) is classified here. -/
theorem sha_regs_cases : ∀ q : Fin 32,
    q ≠ (3 : Fin 32) → q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) →
    q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ (17 : Fin 32) →
    q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
    q.val = 0 ∨ q = sp ∨ q = (4 : Fin 32) ∨
    q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
    q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨
    q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨ q = (26 : Fin 32) ∨ q = (27 : Fin 32) := by decide

/-- **The compiled `sha2::sha256::compress256`**, called with the 8-word state
at `stp`, `n` 64-byte blocks starting at `bp` (`n < 2^26`, which already
follows from `bp + 64 * n < 2^32`), and `sp = sp0`: it updates the 8 words at
`stp` to `(blockList m.mem bp n).foldl Sha256.compress (wordsAt m.mem stp 8)`
(which equals `(Sha256.blocks n (memBytes m.mem bp (64 * n))).foldl Sha256.compress ...`),
returns to `retAddr` with `sp`, `ra`, `tp`, and `s0` through `s11` restored,
and changes no memory outside the 0xE0 bytes of stack below `sp0` and the 32
bytes at `stp`. -/
theorem sha256Compress_correct (m : Machine) {P sp0 stp bp retAddr : Word} {n : Nat}
    (env : SCEnv m.mem P sp0 stp bp n) (hpc : m.pc = P)
    (ha0 : reg m a0 = stp) (ha1 : reg m a1 = bp) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ (3 : Fin 32) → q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) →
        q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ (17 : Fin 32) →
        q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      wordsAt m'.mem stp 8 = (blockList m.mem bp n).foldl Sha256.compress (wordsAt m.mem stp 8) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → m'.mem x = m.mem x := by
  have hn : n < 2 ^ 26 := by have := env.hwbp; omega
  obtain ⟨m1, Ms, c1, I0, hsl⟩ := sha_pro m env hn hpc ha0 ha1 ha2 hsp
  obtain ⟨m2, M2, c2, st2, sp2, tp2, w2, sv2, fr2⟩ := sha_outer_from env n 0 (Nat.zero_add n)
    (wordsAt8_hvOf m.mem stp).symm I0
  obtain ⟨mf, cf, pcf, memf, spf, tpf, savf⟩ := sha_epi env st2 sp2 tp2 sv2 fr2
  have hm : ∀ r c, (r, c) ∈ shaSaved → reg mf r = reg m r := fun r c h =>
    (savf r c h).trans (hsl r c h)
  refine ⟨mf, c1.trans (c2.trans cf), ?_, spf, ?_, ?_, ?_⟩
  · rw [pcf, hsl ra 0xDC (by simp [shaSaved]), hra, hret]
  · intro q q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31
    rcases sha_regs_cases q q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 with
      h0 | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : q = 0 := Fin.ext h0; subst this; rfl
    · exact spf.trans hsp.symm
    · exact tpf
    · exact hm ra 0xDC (by simp [shaSaved])
    · exact hm (8 : Fin 32) 0xD8 (by simp [shaSaved])
    · exact hm (9 : Fin 32) 0xD4 (by simp [shaSaved])
    · exact hm (18 : Fin 32) 0xD0 (by simp [shaSaved])
    · exact hm (19 : Fin 32) 0xCC (by simp [shaSaved])
    · exact hm (20 : Fin 32) 0xC8 (by simp [shaSaved])
    · exact hm (21 : Fin 32) 0xC4 (by simp [shaSaved])
    · exact hm (22 : Fin 32) 0xC0 (by simp [shaSaved])
    · exact hm (23 : Fin 32) 0xBC (by simp [shaSaved])
    · exact hm (24 : Fin 32) 0xB8 (by simp [shaSaved])
    · exact hm (25 : Fin 32) 0xB4 (by simp [shaSaved])
    · exact hm (26 : Fin 32) 0xB0 (by simp [shaSaved])
    · exact hm (27 : Fin 32) 0xAC (by simp [shaSaved])
  · rw [memf]; exact w2
  · intro x hF hSt; rw [memf]; exact fr2 x hF hSt

end Helpers

end C3.RV32
