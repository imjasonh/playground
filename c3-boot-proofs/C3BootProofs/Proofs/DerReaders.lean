import C3BootProofs.Proofs.DerCall

/-!
# `Der::set`, `Der::octet_string`, `Der::bit_string`, and `Der::integer`

`Der::set` tail-calls `Der::nested` with tag 0x31. The other three call
`Der::element` through the prologue in `DerCall.lean`, then turn its result
into a `Result<&[u8], Error>` at `out`: a pointer and a length, or a zero
pointer and the error's discriminant.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem dset_at_0 : fetchRel derSetCode 0x0 = some (.aluImm .add a2 x0 0x31, 4) := by decide
theorem dset_at_4 : fetchRel derSetCode 0x4 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem dset_at_8 : fetchRel derSetCode 0x8 = some (.jalr x0 (6 : Fin 32) 0xFFFFF93C, 4) := by decide
theorem dos_at_0 : fetchRel derOctetStringCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem dos_at_2 : fetchRel derOctetStringCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem dos_at_4 : fetchRel derOctetStringCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem dos_at_6 : fetchRel derOctetStringCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dos_at_8 : fetchRel derOctetStringCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem dos_at_a : fetchRel derOctetStringCode 0xA = some (.aluImm .add a2 x0 0x4, 2) := by decide
theorem dos_at_c : fetchRel derOctetStringCode 0xC = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dos_at_10 : fetchRel derOctetStringCode 0x10 = some (.jalr ra ra 0x786, 4) := by decide
theorem dos_at_14 : fetchRel derOctetStringCode 0x14 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem dos_at_16 : fetchRel derOctetStringCode 0x16 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem dos_at_18 : fetchRel derOctetStringCode 0x18 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem dos_at_1a : fetchRel derOctetStringCode 0x1A = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem dos_at_1c : fetchRel derOctetStringCode 0x1C = some (.jal x0 0xA, 2) := by decide
theorem dos_at_1e : fetchRel derOctetStringCode 0x1E = some (.load .lbu a1 sp 0x8, 4) := by decide
theorem dos_at_22 : fetchRel derOctetStringCode 0x22 = some (.store .sb (8 : Fin 32) a1 0x4, 4) := by decide
theorem dos_at_26 : fetchRel derOctetStringCode 0x26 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem dos_at_28 : fetchRel derOctetStringCode 0x28 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem dos_at_2a : fetchRel derOctetStringCode 0x2A = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem dos_at_2c : fetchRel derOctetStringCode 0x2C = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem dos_at_2e : fetchRel derOctetStringCode 0x2E = some (.jalr x0 ra 0x0, 2) := by decide
theorem dbs_at_0 : fetchRel derBitStringCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem dbs_at_2 : fetchRel derBitStringCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem dbs_at_4 : fetchRel derBitStringCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem dbs_at_6 : fetchRel derBitStringCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dbs_at_8 : fetchRel derBitStringCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem dbs_at_a : fetchRel derBitStringCode 0xA = some (.aluImm .add a2 x0 0x3, 2) := by decide
theorem dbs_at_c : fetchRel derBitStringCode 0xC = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dbs_at_10 : fetchRel derBitStringCode 0x10 = some (.jalr ra ra 0x1F0, 4) := by decide
theorem dbs_at_14 : fetchRel derBitStringCode 0x14 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem dbs_at_16 : fetchRel derBitStringCode 0x16 = some (.branch .beq a0 x0 0x10, 2) := by decide
theorem dbs_at_18 : fetchRel derBitStringCode 0x18 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem dbs_at_1a : fetchRel derBitStringCode 0x1A = some (.branch .beq a1 x0 0x8, 2) := by decide
theorem dbs_at_1c : fetchRel derBitStringCode 0x1C = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem dbs_at_20 : fetchRel derBitStringCode 0x20 = some (.branch .beq a2 x0 0x1A, 2) := by decide
theorem dbs_at_22 : fetchRel derBitStringCode 0x22 = some (.aluImm .add a0 x0 0x14, 2) := by decide
theorem dbs_at_24 : fetchRel derBitStringCode 0x24 = some (.jal x0 0x6, 2) := by decide
theorem dbs_at_26 : fetchRel derBitStringCode 0x26 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dbs_at_2a : fetchRel derBitStringCode 0x2A = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem dbs_at_2e : fetchRel derBitStringCode 0x2E = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem dbs_at_32 : fetchRel derBitStringCode 0x32 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem dbs_at_34 : fetchRel derBitStringCode 0x34 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem dbs_at_36 : fetchRel derBitStringCode 0x36 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem dbs_at_38 : fetchRel derBitStringCode 0x38 = some (.jalr x0 ra 0x0, 2) := by decide
theorem dbs_at_3a : fetchRel derBitStringCode 0x3A = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem dbs_at_3c : fetchRel derBitStringCode 0x3C = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem dbs_at_3e : fetchRel derBitStringCode 0x3E = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem dbs_at_40 : fetchRel derBitStringCode 0x40 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem dbs_at_42 : fetchRel derBitStringCode 0x42 = some (.jal x0 0xFFFFFFF0, 2) := by decide
end

/-- **The compiled `Der::set`** is `Der::nested` for tag 0x31, which it
tail-calls at `Q + 0xFFFFF940`. -/
theorem derSet_correct (m : Machine) {Q sp0 out d retAddr : Word} (hQ : Q.toNat % 2 = 0)
    (hc : CodeIn m.mem Q derSetCode) (env : NestEnv m.mem (Q + 0xFFFFF940) sp0 out d)
    (hpc : m.pc = Q) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derNestedMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 0x31 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)))
          out (memLoad32 m.mem (d + 8))
          (derElement 0x31 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  have s0 : St m.mem Q m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc dset_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.auipc hc dset_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc dset_at_8
  have k3 : ∀ q, q ≠ a2 → q ≠ t1 → reg n3 q = reg m q := fun q h2 ht => by
    rw [regs3, updz (upd_zero _ _ _) ht, updz hz h2]
  have pcN : n3.pc = Q + 0xFFFFF940 := by
    rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
    rw [show Q + BitVec.ofNat 32 4 + 0x0 + 0xFFFFF93C = Q + 0xFFFFF940 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at Q hQ 0xFFFFF940 (by decide))
  obtain ⟨m4, c4, pc4, sp4, k4, f4⟩ := derNested_correct n3 (tag := 0x31) (by rw [mem3]; exact env) pcN
    (by rw [k3 sp (by decide) (by decide), hsp]) (by rw [k3 a0 (by decide) (by decide), ha0])
    (by rw [k3 a1 (by decide) (by decide), ha1])
    (by rw [regs3, updz (upd_zero _ _ _) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl)
    (by decide) (by rw [k3 ra (by decide) (by decide), hra]) hret
  rw [mem3] at f4
  exact ⟨m4, .cons d1 (.cons d2 (.cons d3 c4)), pc4, sp4, fun q hq => by
    rw [k4 q hq, k3 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))],
    f4⟩

/-- What a reader that returns `Result<&[u8], Error>` stores at `out`: the
slice's pointer and length, or a zero pointer and the error. -/
def derSliceMem (M : Word → BitVec 8) (out : Word) : Except DerError (Word × Word) → Word → BitVec 8
  | .error e => memStore8 (memStore32 M out 0) (out + 4) (derErrByte e)
  | .ok (p, l) => memStore32 (memStore32 M out p) (out + 4) l

/-- `x` is `out` plus a natural offset below `2 ^ 32`. -/
theorem off_of (out x : Word) : out + BitVec.ofNat 32 (x - out).toNat = x := by
  rw [ofNat_toNat_self, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The word at `out` and the one at `out + 4` don't overlap, so their
stores commute. -/
theorem slice_ok_comm (M : Word → BitVec 8) (out p l x : Word) :
    memStore32 (memStore32 M (out + 4) l) out p x = memStore32 (memStore32 M out p) (out + 4) l x := by
  have hx := off_of out x
  have hk := (x - out).isLt
  generalize (x - out).toNat = k at hx hk
  subst hx
  by_cases h : k < 4
  · have s : Sep (out + 4) 4 (out + BitVec.ofNat 32 k) 1 :=
      sep_offsets out (c := 4) (n := 4) (d := k) (k := 1) (.inr (by omega)) (by omega) (by omega)
    rw [memStore32_pt (memStore32_get_sep s), memStore32_get_sep s]
  · have s : Sep out 4 (out + BitVec.ofNat 32 k) 1 := by
      have := sep_offsets out (c := 0) (n := 4) (d := k) (k := 1) (.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep s, memStore32_pt (memStore32_get_sep s)]

/-- The error byte at `out + 4` is outside the word at `out`. -/
theorem slice_err_comm (M : Word → BitVec 8) (out x : Word) (b : BitVec 8) :
    memStore32 (memStore8 M (out + 4) b) out 0 x = memStore8 (memStore32 M out 0) (out + 4) b x := by
  have hx := off_of out x
  have hk := (x - out).isLt
  generalize (x - out).toNat = k at hx hk
  subst hx
  by_cases h : k < 4
  · have s : Sep (out + 4) 1 (out + BitVec.ofNat 32 k) 1 :=
      sep_offsets out (c := 4) (n := 1) (d := k) (k := 1) (.inr (by omega)) (by omega) (by omega)
    have hne : out + BitVec.ofNat 32 k ≠ out + 4 := fun e =>
      s 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
    rw [memStore32_pt (memStore8_ne hne), memStore8_ne hne]
  · have s : Sep out 4 (out + BitVec.ofNat 32 k) 1 := by
      have := sep_offsets out (c := 0) (n := 4) (d := k) (k := 1) (.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep s, memStore8_pt (memStore32_get_sep s)]

/-- An element's contents as a pointer and a length, for unread bytes at `rp`. -/
def derContent (rp : Word) : Except DerError DerTlv → Except DerError (Word × Word)
  | .error e => .error e
  | .ok t => .ok (rp + BitVec.ofNat 32 t.header, BitVec.ofNat 32 t.len)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `Der::octet_string`**: with the reader at `d`, whose
unread bytes start at `rp` and number `rl`, it stores the contents of
`derElement 4` of those bytes at `out`, or its error, and moves the reader
past the element. -/
theorem derOctetString_correct (m : Machine) {P sp0 out d retAddr : Word}
    (env : DerCallEnv m.mem derOctetStringCode P 0xFFFFF792 sp0 out d 8)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derSliceMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 4 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) out
          (derContent (memLoad32 m.mem (d + 8))
            (derElement 4 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) x := by
  obtain ⟨m5, Msv, S5, u5, sp5, s85, k5, frSv, slR, sl8⟩ := derCall_pro m (tag := 4) env dos_at_0
    (by decide) (by decide) dos_at_c dos_at_10 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    hpc hsp ha0 ha1
  have hrp0 := env.hrp; have hrw := env.hrw
  generalize memLoad32 m.mem (d + 8) = rp at u5 hrp0 hrw ⊢
  generalize memLoad32 m.mem (d + 0xC) = rl at u5 hrw ⊢
  generalize hr : derElement 4 (memBytes m.mem rp rl.toNat) = r at u5 ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at u5 sp5 frSv slR sl8 sFC sOF sDF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hc5 : CodeIn (derTlvMem Msv (F + 4) d rp rl r) P derOctetStringCode := fun i hi => by
    rw [derCall_outside r frSv (sFC.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 dos_at_14 (off' := 0x16) (by decide)
    (by rw [sp5]; exact aligned_add hFa (k := 4) (by decide))
  rw [sp5] at u6
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m5 n → St Mx P n 0x28 (reg n) → CodeIn Mx P derOctetStringCode →
      (∀ x, Sep out 8 x 1 → Mx x = derTlvMem Msv (F + 4) d rp rl r x) → reg n sp = F →
      (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro Mx n S s hc hMx rsp kq
    obtain ⟨n', c', pc', mem', sp', ra', s8', k'⟩ := derCall_epi s hc (by decide) dos_at_2c dos_at_2e hFa rsp
      (by rw [derCall_slot r sOF sDF (o := 0x1C) (by decide) hMx, slR, hra]) hret
    refine ⟨n', S5.trans (S.trans c'), pc', mem', by rw [sp', eS],
      derCall_keep hsp k5 (fun q hq h1 h8 hs => by rw [k' q h1 h8 hs, kq q hq]) (by rw [sp', eS])
        (by rw [ra', hra]) (by rw [s8', derCall_slot r sOF sDF (o := 0x18) (by decide) hMx, sl8])⟩
  cases r with
  | error e =>
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4) = 0 := derTlvMem_err0 e
    obtain ⟨n7, d7, u7⟩ := u6.taken hc5 0x1E dos_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.lbu hc5 dos_at_1e (off' := 0x22) (by decide)
    have eb : derTlvMem Msv (F + 4) d rp rl (.error e)
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4)) sp + 8) = derErrByte e := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_err4 e
    rw [eb] at u8
    obtain ⟨n9, d9, u9⟩ := u8.sb hc5 dos_at_22 (off' := 0x26) (by decide)
    simp only [upd_app] at u9; simp +decide only [↓reduceIte] at u9
    rw [s85, tlv_zext] at u9
    have hc9 := CodeIn.store8 (v := derErrByte e) hc5 (env.sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n10, d10, u10⟩ := u9.sw hc9 dos_at_26 (off' := 0x28) (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [s85, add_lit_zero]; exact env.hout)
    simp only [upd_app] at u10; simp +decide only [↓reduceIte] at u10
    rw [s85, add_lit_zero, h0] at u10
    have hc10 := CodeIn.store32 (v := 0) hc9 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.single d10))))) u10.self hc10
      (fun x hx => by
        rw [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
          memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm)])
      (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
      (fun q hq => by
        have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
        have h1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
        rw [u10.regs]; simp only [upd_app]
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp; exact u5.zero.symm
        simp only [hq0, h0, h1, ite_false])
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem', slice_err_comm]; simp only [derSliceMem, derContent]
    exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
  | ok t =>
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4) = rp + BitVec.ofNat 32 t.header :=
      derTlvMem_ok0 t
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have hnz : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_add, ofNat_tn (by omega), Nat.mod_eq_of_lt (by omega)] at this
      change _ = 0 at this; omega
    obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x18 dos_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]
      exact beq_false_of_ne hnz)
    obtain ⟨n8, d8, u8⟩ := u7.lw hc5 dos_at_18 (off' := 0x1A) (by decide)
      (by rw [upd_ne (by decide) (by decide), sp5]; exact aligned_add hFa (k := 8) (by decide))
    have elen : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t))
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4)) sp + 8) =
        BitVec.ofNat 32 t.len := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_ok4 t
    rw [elen, h0] at u8
    obtain ⟨n9, d9, u9⟩ := u8.sw hc5 dos_at_1a (off' := 0x1C) (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [s85]; exact aligned_add env.hout (k := 4) (by decide))
    simp only [upd_app] at u9; simp +decide only [↓reduceIte] at u9
    rw [s85] at u9
    have hc9 := CodeIn.store32 (v := BitVec.ofNat 32 t.len) hc5 (env.sOC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨n10, d10, u10⟩ := u9.jump hc9 dos_at_1c (off' := 0x26) (by decide) (by
      rw [u9.pc, show P + BitVec.ofNat 32 0x1C + 0xA = P + BitVec.ofNat 32 0x26 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x26 (by decide)))
    obtain ⟨n11, d11, u11⟩ := u10.sw hc9 dos_at_26 (off' := 0x28) (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [s85, add_lit_zero]; exact env.hout)
    simp only [upd_app] at u11; simp +decide only [↓reduceIte] at u11
    rw [s85, add_lit_zero] at u11
    have hc11 := CodeIn.store32 (v := rp + BitVec.ofNat 32 t.header) hc9
      (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.single d11))))))
      u11.self hc11
      (fun x hx => by
        rw [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
          memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide))])
      (by rw [u11.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
      (fun q hq => by
        have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
        have h1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
        rw [u11.regs]; simp only [upd_app]
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp; exact u5.zero.symm
        simp only [hq0, h0, h1, ite_false])
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem', slice_ok_comm]; simp only [derSliceMem, derContent]
    exact memStore32_pt (memStore32_pt (derCall_outside _ frSv hx))

/-- `Der::bit_string`'s result for the unread bytes `L` at `rp`: the
contents after their first byte, which counts the unused bits and must be 0. -/
def derBitsOf (L : Bytes) (rp : Word) : Except DerError DerTlv → Except DerError (Word × Word)
  | .error e => .error e
  | .ok t => if t.len ≠ 0 ∧ L.getD t.header 0 = 0 then
      .ok (rp + BitVec.ofNat 32 (t.header + 1), BitVec.ofNat 32 (t.len - 1)) else .error .badDer

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `Der::bit_string`**: with the reader at `d`, whose
unread bytes start at `rp` and number `rl` and don't overlap the reader, it
stores `derBitsOf` of `derElement 3` of those bytes at `out`, and moves the
reader past the element. -/
theorem derBitString_correct (m : Machine) {P sp0 out d retAddr : Word}
    (env : DerCallEnv m.mem derBitStringCode P 0xFFFFF1FC sp0 out d 8)
    (sDR : Sep (d + 8) 8 (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derSliceMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 3 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) out
          (derBitsOf (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
            (memLoad32 m.mem (d + 8))
            (derElement 3 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) x := by
  obtain ⟨m5, Msv, S5, u5, sp5, s85, k5, frSv, slR, sl8⟩ := derCall_pro m (tag := 3) env dbs_at_0
    (by decide) (by decide) dbs_at_c dbs_at_10 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    hpc hsp ha0 ha1
  have hrp0 := env.hrp; have hrw := env.hrw; have sRF := env.sRF
  generalize memLoad32 m.mem (d + 8) = rp at u5 hrp0 hrw sRF sDR ⊢
  generalize memLoad32 m.mem (d + 0xC) = rl at u5 hrw sRF sDR ⊢
  generalize hr : derElement 3 (memBytes m.mem rp rl.toNat) = r at u5 ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at u5 sp5 frSv slR sl8 sFC sOF sDF sRF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hc5 : CodeIn (derTlvMem Msv (F + 4) d rp rl r) P derBitStringCode := fun i hi => by
    rw [derCall_outside r frSv (sFC.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 dbs_at_14 (off' := 0x16) (by decide)
    (by rw [sp5]; exact aligned_add hFa (k := 4) (by decide))
  rw [sp5] at u6
  have hkk : ∀ q : Fin 32, oidKeep q = true → q.val ∉ [10, 11, 12] := by decide
  have kx : ∀ {f : Fin 32 → Word}, (∀ q, q.val ∉ [10, 11, 12] → f q = reg m5 q) →
      ∀ q, oidKeep q = true → f q = reg m5 q := fun hq q hk => hq q (hkk q hk)
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m5 n → St Mx P n 0x32 (reg n) →
      CodeIn Mx P derBitStringCode → (∀ x, Sep out 8 x 1 → Mx x = derTlvMem Msv (F + 4) d rp rl r x) →
      reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro Mx n S s hc hMx rsp kq
    obtain ⟨n', c', pc', mem', sp', ra', s8', k'⟩ := derCall_epi s hc (by decide) dbs_at_36 dbs_at_38 hFa rsp
      (by rw [derCall_slot r sOF sDF (o := 0x1C) (by decide) hMx, slR, hra]) hret
    refine ⟨n', S5.trans (S.trans c'), pc', mem', by rw [sp', eS],
      derCall_keep hsp k5 (fun q hq h1 h8 hs => by rw [k' q h1 h8 hs, kq q hq]) (by rw [sp', eS])
        (by rw [ra', hra]) (by rw [s8', derCall_slot r sOF sDF (o := 0x18) (by decide) hMx, sl8])⟩
  -- the error exit at 0x2A, with the discriminant in `a0`
  have tail : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl r) P n 0x2A (reg n) →
      reg n 8 = out → reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧
        n'.mem = memStore8 (memStore32 (derTlvMem Msv (F + 4) d rp rl r) out 0) (out + 4)
          ((reg n a0).extractLsb' 0 8) ∧ reg n' sp = sp0 ∧ ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro n S s r8 rsp kq
    obtain ⟨n1, d1, u1⟩ := s.sw hc5 dbs_at_2a (off' := 0x2E) (by decide) (by rw [r8, add_lit_zero]; exact env.hout)
    rw [r8, add_lit_zero, s.zero] at u1
    have hc1 := CodeIn.store32 (v := 0) hc5 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 dbs_at_2e (off' := 0x32) (by decide)
    rw [r8] at u2
    have hc2 := CodeIn.store8 (v := (reg n a0).extractLsb' 0 8) hc1 (env.sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.single d2))) u2.self hc2
      (fun x hx => by
        rw [memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
          memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)])
      (by rw [u2.regs]; exact rsp) (fun q hq => by rw [u2.regs]; exact kq q hq)
    exact ⟨n', S', pc', mem', sp', k'⟩
  cases r with
  | error e =>
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4) = 0 := derTlvMem_err0 e
    obtain ⟨n7, d7, u7⟩ := u6.taken hc5 0x26 dbs_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.lbu hc5 dbs_at_26 (off' := 0x2A) (by decide)
    have eb : derTlvMem Msv (F + 4) d rp rl (.error e)
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4)) sp + 8) = derErrByte e := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_err4 e
    rw [eb] at u8
    obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (.cons d6 (.cons d7 (.single d8))) u8.self
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s85)
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
      (fun q hq => by rw [u8.regs]; exact kx (fun q h => by
        simp only [upd_app]
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp; exact u5.zero.symm
        have h0 : q ≠ a0 := fun e => h (by rw [e]; decide)
        simp only [hq0, h0, ite_false]) q hq)
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem', u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [tlv_zext]
    simp only [derSliceMem, derBitsOf]
    exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
  | ok t =>
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4) = rp + BitVec.ofNat 32 t.header :=
      derTlvMem_ok0 t
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hnz : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega
    obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x18 dbs_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]
      exact beq_false_of_ne hnz)
    obtain ⟨n8, d8, u8⟩ := u7.lw hc5 dbs_at_18 (off' := 0x1A) (by decide)
      (by rw [upd_ne (by decide) (by decide), sp5]; exact aligned_add hFa (k := 8) (by decide))
    have elen : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t))
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4)) sp + 8) =
        BitVec.ofNat 32 t.len := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_ok4 t
    rw [elen, h0] at u8
    have r8 : ∀ q, q ≠ a0 → q ≠ a1 → upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1
        (BitVec.ofNat 32 t.len) q = reg m5 q := fun q h0 h1 => by
      rw [upd_ne' h1 (by simp [upd]), upd_ne' h0 u5.zero]
    -- the BadDer exit through 0x22
    have bad : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl (.ok t)) P n 0x22 (reg n) →
        reg n 8 = out → reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
        ∃ n', Steps m n' ∧ n'.pc = retAddr ∧
          n'.mem = memStore8 (memStore32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) out 0) (out + 4) 0x14 ∧
          reg n' sp = sp0 ∧ ∀ q, oidKeep q = true → reg n' q = reg m q := by
      intro n S s r8' rsp kq
      obtain ⟨n1, d1, u1⟩ := s.aluImm hc5 dbs_at_22 (off' := 0x24) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.jump hc5 dbs_at_24 (off' := 0x2A) (by decide) (by
        rw [u1.pc, show P + BitVec.ofNat 32 0x24 + 0x6 = P + BitVec.ofNat 32 0x2A by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x2A (by decide)))
      obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (S.trans (.cons d1 (.single d2))) u2.self
        (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact r8')
        (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact rsp)
        (fun q hq => by
          rw [u2.regs]; rw [upd_ne' (fun e => by subst e; exact absurd hq (by decide)) s.zero]; exact kq q hq)
      refine ⟨n', S', pc', ?_, sp', k'⟩
      rw [mem', u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s.zero]; rfl
    have kq8 : ∀ q, oidKeep q = true → upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1
        (BitVec.ofNat 32 t.len) q = reg m5 q := fun q hq =>
      r8 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
    by_cases hl : t.len = 0
    · obtain ⟨n9, d9, u9⟩ := u8.taken hc5 0x22 dbs_at_1a (by decide) (by
        simp +decide only [upd_app, ↓reduceIte]; rw [hl]; rfl)
      obtain ⟨n', S', pc', mem', sp', k'⟩ := bad (.cons d6 (.cons d7 (.cons d8 (.single d9)))) u9.self
        (by rw [u9.regs, r8 8 (by decide) (by decide), s85]) (by rw [u9.regs, r8 sp (by decide) (by decide), sp5])
        (fun q hq => by rw [u9.regs]; exact kq8 q hq)
      refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
      rw [mem']; simp only [derSliceMem, derBitsOf, hl, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
    have hl1 : 1 ≤ t.len := Nat.one_le_iff_ne_zero.mpr hl
    have hL : t.len < 2 ^ 32 := by have := rl.isLt; omega
    obtain ⟨n9, d9, u9⟩ := u8.notTaken hc5 0x1C dbs_at_1a (by decide) (by
      simp +decide only [upd_app, ↓reduceIte]
      exact beq_false_of_ne fun h => hl (by
        have := congrArg BitVec.toNat h; rwa [ofNat_tn hL] at this))
    obtain ⟨n10, d10, u10⟩ := u9.lbu hc5 dbs_at_1c (off' := 0x20) (by decide)
    have ebyte : derTlvMem Msv (F + 4) d rp rl (.ok t)
        (upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1 (BitVec.ofNat 32 t.len) a0 + 0) =
        m.mem (rp + BitVec.ofNat 32 t.header) := by
      simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero]
      rw [derCall_outside _ frSv (sRF.symm.subR (c := t.header) (l := 1) (by omega)),
        derAdvance_outside _ (sDR.subR (c := t.header) (l := 1) (by omega))]
    rw [ebyte] at u10
    have hgd : (memBytes m.mem rp rl.toNat).getD t.header 0 = (m.mem (rp + BitVec.ofNat 32 t.header)).toNat :=
      memBytes_getD (by omega)
    by_cases hz : (m.mem (rp + BitVec.ofNat 32 t.header)).toNat = 0
    · obtain ⟨n11, d11, u11⟩ := u10.taken hc5 0x3A dbs_at_20 (by decide) (by
        simp +decide only [upd_app, ↓reduceIte]
        show ((m.mem (rp + BitVec.ofNat 32 t.header)).zeroExtend 32 == (0 : Word)) = true
        rw [show m.mem (rp + BitVec.ofNat 32 t.header) = 0 from BitVec.eq_of_toNat_eq hz]; rfl)
      obtain ⟨n12, d12, u12⟩ := u11.aluImm hc5 dbs_at_3a (off' := 0x3C) (by decide)
      obtain ⟨n13, d13, u13⟩ := u12.aluImm hc5 dbs_at_3c (off' := 0x3E) (by decide)
      have v13 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n13 q = reg m5 q := fun q h0 h1 h2 => by
        rw [u13.regs, upd_ne' h0 (by simp [upd]), upd_ne' h1 (by simp [upd]), upd_ne' h2 (by simp [upd]),
          r8 q h0 h1]
      have va0 : reg n13 a0 = rp + BitVec.ofNat 32 (t.header + 1) := by
        rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [ev_add, BitVec.add_assoc, show (1 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
      have va1 : reg n13 a1 = BitVec.ofNat 32 (t.len - 1) := by
        rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, ofNat_tn hL, ofNat_tn (by omega)]
        change (t.len + 4294967295) % 4294967296 = _; omega
      obtain ⟨n14, d14, u14⟩ := u13.self.sw hc5 dbs_at_3e (off' := 0x40) (by decide)
        (by rw [v13 8 (by decide) (by decide) (by decide), s85, add_lit_zero]; exact env.hout)
      rw [v13 8 (by decide) (by decide) (by decide), s85, add_lit_zero, va0] at u14
      have hc14 := CodeIn.store32 (v := rp + BitVec.ofNat 32 (t.header + 1)) hc5
        (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
      obtain ⟨n15, d15, u15⟩ := u14.sw hc14 dbs_at_40 (off' := 0x42) (by decide)
        (by rw [v13 8 (by decide) (by decide) (by decide), s85]; exact aligned_add env.hout (k := 4) (by decide))
      rw [v13 8 (by decide) (by decide) (by decide), s85, va1] at u15
      have hc15 := CodeIn.store32 (v := BitVec.ofNat 32 (t.len - 1)) hc14 (env.sOC.sub (c := 4) (l := 4) (by decide))
      obtain ⟨n16, d16, u16⟩ := u15.jump hc15 dbs_at_42 (off' := 0x32) (by decide) (by
        rw [u15.pc, show P + BitVec.ofNat 32 0x42 + 0xFFFFFFF0 = P + BitVec.ofNat 32 0x32 by
          rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x32 (by decide)))
      obtain ⟨n', S', pc', mem', sp', k'⟩ := fin
        (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14
          (.cons d15 (.single d16)))))))))))
        u16.self hc15
        (fun x hx => by
          rw [memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
            memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)])
        (by rw [u16.regs, v13 sp (by decide) (by decide) (by decide), sp5])
        (fun q hq => by
          rw [u16.regs]
          exact v13 q (fun e => by subst e; exact absurd hq (by decide))
            (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide)))
      refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
      rw [mem']; simp only [derSliceMem, derBitsOf, hgd, hz, ne_eq, hl, not_false_eq_true, and_self, ↓reduceIte]
      exact memStore32_pt (memStore32_pt (derCall_outside _ frSv hx))
    · obtain ⟨n11, d11, u11⟩ := u10.notTaken hc5 0x22 dbs_at_20 (by decide) (by
        simp +decide only [upd_app, ↓reduceIte]
        exact beq_false_of_ne fun h => hz (by
          have := congrArg BitVec.toNat h
          rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.mem (rp + BitVec.ofNat 32 t.header)).isLt; omega)]
            at this))
      have v10 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n11 q = reg m5 q := fun q h0 h1 h2 => by
        rw [u11.regs, upd_ne' h2 (by simp [upd]), r8 q h0 h1]
      obtain ⟨n', S', pc', mem', sp', k'⟩ := bad
        (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.single d11)))))) u11.self
        (by rw [v10 8 (by decide) (by decide) (by decide), s85]) (by rw [v10 sp (by decide) (by decide) (by decide), sp5])
        (fun q hq => v10 q (fun e => by subst e; exact absurd hq (by decide))
          (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide)))
      refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
      rw [mem']; simp only [derSliceMem, derBitsOf, hgd, hz, and_false, ↓reduceIte]
      exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))

end C3.RV32
