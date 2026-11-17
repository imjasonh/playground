import C3BootProofs.Proofs.Ed25519VerifyP5

/-!
# `ed25519_verify`, offsets 0x1356 onward: `Scalar::from_bytes_wide`

The function splits the digest's 16 words at `F + 0x9F0` into two 9-limb
scalars of 29-bit limbs, the low 261 bits at `F + 0x1508` and the rest at
`F + 0x15A8`, and multiplies them by `R` and `R²` in Montgomery form.
-/

namespace C3.RV32

open C3.Image

theorem or_shr_shl (x y : Word) {s k : Nat} (hsk : s + k = 32) : (x >>> s ||| y <<< k) = x >>> s + y <<< k := by
  rw [Sha256.add_disj]
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases h : i < k
  · simp [h]
  · simp [BitVec.getLsbD_of_ge x (s + i) (by omega)]

theorem limbB (x y : Word) {s k : Nat} (hsk : s + k = 32) :
    ((x >>> s ||| y <<< k) &&& BitVec.ofNat 32 0x1FFFFFFF).toNat = (x.toNat / 2 ^ s + y.toNat * 2 ^ k) % 2 ^ 29 := by
  rw [show ((x >>> s ||| y <<< k) &&& BitVec.ofNat 32 0x1FFFFFFF).toNat = (x >>> s ||| y <<< k).toNat % 2 ^ 29 from
    and_mask29 _, or_shr_shl x y hsk, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem limbB' (x y : Word) {s k : Nat} (hsk : s + k = 32) :
    ((y <<< k ||| x >>> s) &&& BitVec.ofNat 32 0x1FFFFFFF).toNat = (x.toNat / 2 ^ s + y.toNat * 2 ^ k) % 2 ^ 29 := by
  rw [BitVec.or_comm]; exact limbB x y hsk

theorem limbA (x : Word) : (x &&& BitVec.ofNat 32 0x1FFFFFFF).toNat = x.toNat % 2 ^ 29 := and_mask29 x

theorem limbC (x : Word) (s : Nat) : ((x >>> s) &&& BitVec.ofNat 32 0x1FFFFFFF).toNat = x.toNat / 2 ^ s % 2 ^ 29 := by
  rw [show ((x >>> s) &&& BitVec.ofNat 32 0x1FFFFFFF).toNat = (x >>> s).toNat % 2 ^ 29 from and_mask29 _, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

/-- A block of register operations and stores into `F + d` to `F + d + k`,
below the slots, that leaves `sp`, `gp`, and `tp` alone. -/
theorem EvSt.blockW (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} {off : Nat}
    (D : EvSt M0 Ms F r0 M n off) (blk : List BInstr) {off' d k : Nat}
    (he : blockEnd ed25519VerifyCode off blk = some off')
    (hok : BlockOk EV ed25519VerifyCode.length blk (M, reg n)) (hd : d + k ≤ 0x166C)
    (hm : ∀ x, Sep (F + BitVec.ofNat 32 d) k x 1 → (runBlock blk (M, reg n)).1 x = M x)
    (hk : ∀ q : Fin 32, q = sp ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) → (runBlock blk (M, reg n)).2 q = reg n q) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 (runBlock blk (M, reg n)).1 n' off' ∧
      ∀ q, reg n' q = (runBlock blk (M, reg n)).2 q := by
  obtain ⟨n', c, u⟩ := St.block blk D.st (D.code C) he hok
  exact ⟨n', c, D.store C (d := d) (k := k) ⟨u.pc, u.mem, fun _ => rfl⟩
    (by rw [u.regs, hk sp (Or.inl rfl), D.hsp]) (by rw [u.regs, hk 3 (Or.inr (Or.inl rfl))])
    (by rw [u.regs, hk 4 (Or.inr (Or.inr rfl))]) hd hm, u.regs⟩

def evFbw1 : List BInstr :=
  ((.aluImm .add a4 (19 : Fin 32) 0x81) :: (.lw a0 a4 0x60) :: (.lw a1 a4 0x64) :: (.lw a2 a4 0x68) :: (.lw a3 a4 0x6C) :: (.alu .and a6 a0 (27 : Fin 32)) :: (.aluImm .srl a0 a0 0x1D) :: (.aluImm .sll a5 a1 0x3) :: (.aluImm .srl a1 a1 0x1A) :: (.aluImm .sll (9 : Fin 32) a2 0x6) :: (.aluImm .srl a2 a2 0x17) :: (.aluImm .sll (8 : Fin 32) a3 0x9) :: (.alu .or a0 a0 a5) :: (.alu .or a1 a1 (9 : Fin 32)) :: (.alu .and (17 : Fin 32) a0 (27 : Fin 32)) :: (.alu .or a2 a2 (8 : Fin 32)) :: (.lw a0 a4 0x70) :: (.alu .and a1 a1 (27 : Fin 32)) :: (.alu .and (5 : Fin 32) a2 (27 : Fin 32)) :: (.aluImm .srl a3 a3 0x14) :: (.lw (9 : Fin 32) a4 0x74) :: (.lw (8 : Fin 32) a4 0x78) :: (.lw a2 a4 0x7C) :: (.aluImm .sll a5 a0 0xC) :: (.sw (23 : Fin 32) a6 0x0) :: (.sw (23 : Fin 32) (17 : Fin 32) 0x4) :: (.alu .add a4 x0 (23 : Fin 32)) :: (.sw a4 a1 0x8) :: (.sw (23 : Fin 32) (5 : Fin 32) 0xC) :: (.alu .or a6 a5 a3) :: (.aluImm .srl a0 a0 0x11) :: (.aluImm .sll a1 (9 : Fin 32) 0xF) :: (.alu .or (17 : Fin 32) a1 a0) :: (.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0xE) :: (.aluImm .sll a1 (8 : Fin 32) 0x12) :: (.lw (7 : Fin 32) (19 : Fin 32) 0x101) :: (.alu .or (5 : Fin 32) a1 (9 : Fin 32)) :: (.aluImm .srl (8 : Fin 32) (8 : Fin 32) 0xB) :: (.aluImm .sll a1 a2 0x15) :: (.aluImm .srl a0 a2 0x8) :: (.lw (9 : Fin 32) (19 : Fin 32) 0x105) :: (.lw a3 (19 : Fin 32) 0x109) :: (.lw (6 : Fin 32) (19 : Fin 32) 0x10D) :: (.aluImm .sll a2 (7 : Fin 32) 0x18) :: (.alu .or a1 a1 (8 : Fin 32)) :: (.alu .or a2 a2 a0) :: (.alu .and a5 a6 (27 : Fin 32)) :: (.alu .and (8 : Fin 32) (17 : Fin 32) (27 : Fin 32)) :: (.alu .and a0 (5 : Fin 32) (27 : Fin 32)) :: (.alu .and a1 a1 (27 : Fin 32)) :: (.alu .and a2 a2 (27 : Fin 32)) :: (.sw a4 a5 0x10) :: (.sw a4 (8 : Fin 32) 0x14) :: (.sw a4 a0 0x18) :: (.sw a4 a1 0x1C) :: (.sw a4 a2 0x20) :: [])

set_option maxRecDepth 20000 in
theorem evFbw1_end : blockEnd ed25519VerifyCode 0x1356 evFbw1 = some 0x1400 :=
  (blockEnd_cons' (off' := 0x135A) ev_at_1356 rfl (blockEnd_cons' (off' := 0x135C) ev_at_135a rfl (blockEnd_cons' (off' := 0x135E) ev_at_135c rfl (blockEnd_cons' (off' := 0x1360) ev_at_135e rfl (blockEnd_cons' (off' := 0x1362) ev_at_1360 rfl (blockEnd_cons' (off' := 0x1366) ev_at_1362 rfl (blockEnd_cons' (off' := 0x1368) ev_at_1366 rfl (blockEnd_cons' (off' := 0x136C) ev_at_1368 rfl (blockEnd_cons' (off' := 0x136E) ev_at_136c rfl (blockEnd_cons' (off' := 0x1372) ev_at_136e rfl (blockEnd_cons' (off' := 0x1374) ev_at_1372 rfl (blockEnd_cons' (off' := 0x1378) ev_at_1374 rfl (blockEnd_cons' (off' := 0x137A) ev_at_1378 rfl (blockEnd_cons' (off' := 0x137C) ev_at_137a rfl (blockEnd_cons' (off' := 0x1380) ev_at_137c rfl (blockEnd_cons' (off' := 0x1382) ev_at_1380 rfl (blockEnd_cons' (off' := 0x1384) ev_at_1382 rfl (blockEnd_cons' (off' := 0x1388) ev_at_1384 rfl (blockEnd_cons' (off' := 0x138C) ev_at_1388 rfl (blockEnd_cons' (off' := 0x138E) ev_at_138c rfl (blockEnd_cons' (off' := 0x1390) ev_at_138e rfl (blockEnd_cons' (off' := 0x1392) ev_at_1390 rfl (blockEnd_cons' (off' := 0x1394) ev_at_1392 rfl (blockEnd_cons' (off' := 0x1398) ev_at_1394 rfl (blockEnd_cons' (off' := 0x139C) ev_at_1398 rfl (blockEnd_cons' (off' := 0x13A0) ev_at_139c rfl (blockEnd_cons' (off' := 0x13A2) ev_at_13a0 rfl (blockEnd_cons' (off' := 0x13A4) ev_at_13a2 rfl (blockEnd_cons' (off' := 0x13A8) ev_at_13a4 rfl (blockEnd_cons' (off' := 0x13AC) ev_at_13a8 rfl (blockEnd_cons' (off' := 0x13AE) ev_at_13ac rfl (blockEnd_cons' (off' := 0x13B2) ev_at_13ae rfl (blockEnd_cons' (off' := 0x13B6) ev_at_13b2 rfl (blockEnd_cons' (off' := 0x13B8) ev_at_13b6 rfl (blockEnd_cons' (off' := 0x13BC) ev_at_13b8 rfl (blockEnd_cons' (off' := 0x13C0) ev_at_13bc rfl (blockEnd_cons' (off' := 0x13C4) ev_at_13c0 rfl (blockEnd_cons' (off' := 0x13C6) ev_at_13c4 rfl (blockEnd_cons' (off' := 0x13CA) ev_at_13c6 rfl (blockEnd_cons' (off' := 0x13CE) ev_at_13ca rfl (blockEnd_cons' (off' := 0x13D2) ev_at_13ce rfl (blockEnd_cons' (off' := 0x13D6) ev_at_13d2 rfl (blockEnd_cons' (off' := 0x13DA) ev_at_13d6 rfl (blockEnd_cons' (off' := 0x13DE) ev_at_13da rfl (blockEnd_cons' (off' := 0x13E0) ev_at_13de rfl (blockEnd_cons' (off' := 0x13E2) ev_at_13e0 rfl (blockEnd_cons' (off' := 0x13E6) ev_at_13e2 rfl (blockEnd_cons' (off' := 0x13EA) ev_at_13e6 rfl (blockEnd_cons' (off' := 0x13EE) ev_at_13ea rfl (blockEnd_cons' (off' := 0x13F2) ev_at_13ee rfl (blockEnd_cons' (off' := 0x13F6) ev_at_13f2 rfl (blockEnd_cons' (off' := 0x13F8) ev_at_13f6 rfl (blockEnd_cons' (off' := 0x13FA) ev_at_13f8 rfl (blockEnd_cons' (off' := 0x13FC) ev_at_13fa rfl (blockEnd_cons' (off' := 0x13FE) ev_at_13fc rfl (blockEnd_cons' (off' := 0x1400) ev_at_13fe rfl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1356: the low scalar's 9 limbs to `F + 0x1508`, with
words 8 to 11 left in `t2`, `s1`, `a3`, and `t1`. -/
theorem ev_fbw1 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1356)
    (h19 : reg n 19 = F + 0x90F) (h23 : reg n 23 = F + BitVec.ofNat 32 0x1508) (h27 : reg n 27 = 0x1FFFFFFF) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1400 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n' q = reg n q) ∧
      ((limbAt M' (F + BitVec.ofNat 32 0x1508) 0 = (memLoad32 M (F + BitVec.ofNat 32 0x9F0)).toNat % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 1 = ((memLoad32 M (F + BitVec.ofNat 32 0x9F0)).toNat / 2 ^ 29 + (memLoad32 M (F + BitVec.ofNat 32 0x9F4)).toNat * 2 ^ 3) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 2 = ((memLoad32 M (F + BitVec.ofNat 32 0x9F4)).toNat / 2 ^ 26 + (memLoad32 M (F + BitVec.ofNat 32 0x9F8)).toNat * 2 ^ 6) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 3 = ((memLoad32 M (F + BitVec.ofNat 32 0x9F8)).toNat / 2 ^ 23 + (memLoad32 M (F + BitVec.ofNat 32 0x9FC)).toNat * 2 ^ 9) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 4 = ((memLoad32 M (F + BitVec.ofNat 32 0x9FC)).toNat / 2 ^ 20 + (memLoad32 M (F + BitVec.ofNat 32 0xA00)).toNat * 2 ^ 12) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 5 = ((memLoad32 M (F + BitVec.ofNat 32 0xA00)).toNat / 2 ^ 17 + (memLoad32 M (F + BitVec.ofNat 32 0xA04)).toNat * 2 ^ 15) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 6 = ((memLoad32 M (F + BitVec.ofNat 32 0xA04)).toNat / 2 ^ 14 + (memLoad32 M (F + BitVec.ofNat 32 0xA08)).toNat * 2 ^ 18) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 7 = ((memLoad32 M (F + BitVec.ofNat 32 0xA08)).toNat / 2 ^ 11 + (memLoad32 M (F + BitVec.ofNat 32 0xA0C)).toNat * 2 ^ 21) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x1508) 8 = ((memLoad32 M (F + BitVec.ofNat 32 0xA0C)).toNat / 2 ^ 8 + (memLoad32 M (F + BitVec.ofNat 32 0xA10)).toNat * 2 ^ 24) % 2 ^ 29)) ∧
      reg n' 7 = memLoad32 M (F + BitVec.ofNat 32 0xA10) ∧ reg n' 9 = memLoad32 M (F + BitVec.ofNat 32 0xA14) ∧
      reg n' 13 = memLoad32 M (F + BitVec.ofNat 32 0xA18) ∧ reg n' 6 = memLoad32 M (F + BitVec.ofNat 32 0xA1C) ∧
      ∀ c, c < 0x16A0 → (c < 0x1508 ∨ 0x152C ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have hal : ∀ c, c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => C.al h
  have hcs : ∀ c, c + 4 ≤ 0x16A0 → Sep (F + BitVec.ofNat 32 c) 4 EV ed25519VerifyCode.length :=
    fun c h => C.codeF h (by decide) (by rw [ev_len]; decide)
  have h19' : reg n 19 = F + BitVec.ofNat 32 0x90F := h19
  have peel : ∀ c v (M' : Word → BitVec 8) d, (c == d) = false → c % 4 = 0 → d % 4 = 0 → c + 4 ≤ 2 ^ 32 →
      d + 4 ≤ 2 ^ 32 → memLoad32 (memStore32 M' (F + BitVec.ofNat 32 c) v) (F + BitVec.ofNat 32 d) =
        memLoad32 M' (F + BitVec.ofNat 32 d) := fun c v M' d h1 h2 h3 h4 h5 => memLoad32_store32_off h1 h2 h3 h4 h5
  have hm : ∀ x, Sep (F + BitVec.ofNat 32 0x1508) 0x24 x 1 → (runBlock evFbw1 (M, reg n)).1 x = M x := fun x hx => by
    have hst : ∀ (c : Nat) (v : Word) (M' : Word → BitVec 8), 0x1508 ≤ c → c + 4 ≤ 0x152C →
        memStore32 M' (F + BitVec.ofNat 32 c) v x = M' x := fun c v M' h1 h2 => st32_frame (by
      have := hx.sub (c := c - 0x1508) (l := 4) (by omega)
      rwa [add_ofNat_assoc, show 0x1508 + (c - 0x1508) = c by omega] at this)
    simp +decide only [evFbw1, runBlock, BInstr.run, upd, ↓reduceIte, h19', h23, aluEval, BitVec.ofNat_eq_ofNat, add_ofNat_assoc, Nat.reduceAdd, BitVec.zero_add, D.st.zero]
    simp (disch := decide) only [hst]
  obtain ⟨n1, c1, D1, hr1⟩ := D.blockW C (d := 0x1508) (k := 0x24) evFbw1 evFbw1_end
    (by simp +decide only [evFbw1, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, true_and, h19', h23, aluEval, BitVec.ofNat_eq_ofNat, add_ofNat_assoc, Nat.reduceAdd, BitVec.zero_add]
        simp (disch := decide) only [hal, hcs, and_self, true_and])
    (by decide) hm
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evFbw1, runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock evFbw1 (M, reg n)).1 = M1 := ⟨_, rfl⟩
  have fr : ∀ c, c < 0x16A0 → (c < 0x1508 ∨ 0x152C ≤ c) → M1 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      rw [← hM1]; refine hm _ (C.offs ?_ (by decide) (by omega))
      rcases hh with hh | hh
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  rw [hM1] at D1
  simp +decide only [evFbw1, runBlock, BInstr.run, upd, ↓reduceIte, h19', h23, h27, aluEval, BitVec.ofNat_eq_ofNat, add_ofNat_assoc, Nat.reduceAdd, BitVec.zero_add, D.st.zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hM1
  have lo : (limbAt M1 (F + BitVec.ofNat 32 0x1508) 0 = (memLoad32 M (F + BitVec.ofNat 32 0x9F0)).toNat % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 1 = ((memLoad32 M (F + BitVec.ofNat 32 0x9F0)).toNat / 2 ^ 29 + (memLoad32 M (F + BitVec.ofNat 32 0x9F4)).toNat * 2 ^ 3) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 2 = ((memLoad32 M (F + BitVec.ofNat 32 0x9F4)).toNat / 2 ^ 26 + (memLoad32 M (F + BitVec.ofNat 32 0x9F8)).toNat * 2 ^ 6) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 3 = ((memLoad32 M (F + BitVec.ofNat 32 0x9F8)).toNat / 2 ^ 23 + (memLoad32 M (F + BitVec.ofNat 32 0x9FC)).toNat * 2 ^ 9) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 4 = ((memLoad32 M (F + BitVec.ofNat 32 0x9FC)).toNat / 2 ^ 20 + (memLoad32 M (F + BitVec.ofNat 32 0xA00)).toNat * 2 ^ 12) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 5 = ((memLoad32 M (F + BitVec.ofNat 32 0xA00)).toNat / 2 ^ 17 + (memLoad32 M (F + BitVec.ofNat 32 0xA04)).toNat * 2 ^ 15) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 6 = ((memLoad32 M (F + BitVec.ofNat 32 0xA04)).toNat / 2 ^ 14 + (memLoad32 M (F + BitVec.ofNat 32 0xA08)).toNat * 2 ^ 18) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 7 = ((memLoad32 M (F + BitVec.ofNat 32 0xA08)).toNat / 2 ^ 11 + (memLoad32 M (F + BitVec.ofNat 32 0xA0C)).toNat * 2 ^ 21) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x1508) 8 = ((memLoad32 M (F + BitVec.ofNat 32 0xA0C)).toNat / 2 ^ 8 + (memLoad32 M (F + BitVec.ofNat 32 0xA10)).toNat * 2 ^ 24) % 2 ^ 29) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [limbAt, add_ofNat_assoc, Nat.reduceMul, Nat.reduceAdd]; rw [← hM1]
     simp (disch := decide) only [↓peel, ↓memLoad32_store32_same]; (first | (simp (disch := decide) only [limbB, limbB']; done) | (simp only [limbC]; done) | (simp only [limbA]; done) | (simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; done)))
  refine ⟨n1, M1, c1, D1, fun q hq h8 h9 => ?_, lo, ?_, ?_, ?_, ?_, fr⟩
  · rw [hr1, evb_reg q D.st.zero (by revert h9; revert h8; revert hq; revert q; decide)]
  all_goals
    rw [hr1]
    simp +decide only [evFbw1, runBlock, BInstr.run, upd, ↓reduceIte, h19', h23, aluEval,
      BitVec.ofNat_eq_ofNat, add_ofNat_assoc, Nat.reduceAdd, BitVec.zero_add, D.st.zero]
    simp (disch := decide) only [peel]

def evFbw2 : List BInstr :=
  ((.aluImm .srl a5 (7 : Fin 32) 0x5) :: (.aluImm .sll a0 (9 : Fin 32) 0x1B) :: (.alu .or a0 a0 a5) :: (.aluImm .srl a1 (9 : Fin 32) 0x2) :: (.alu .and a0 a0 (27 : Fin 32)) :: (.alu .and a1 a1 (27 : Fin 32)) :: (.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x1F) :: (.aluImm .sll a2 a3 0x1) :: (.aluImm .srl a3 a3 0x1C) :: (.aluImm .sll a5 (6 : Fin 32) 0x4) :: (.alu .or a2 a2 (9 : Fin 32)) :: (.alu .or a3 a3 a5) :: (.alu .and a2 a2 (27 : Fin 32)) :: (.alu .and a3 a3 (27 : Fin 32)) :: (.aluImm .add a4 (19 : Fin 32) 0x101) :: (.lw a5 a4 0x10) :: (.lw (9 : Fin 32) a4 0x14) :: (.sw (23 : Fin 32) a0 0xA0) :: (.sw (23 : Fin 32) a1 0xA4) :: (.sw (23 : Fin 32) a2 0xA8) :: (.sw (23 : Fin 32) a3 0xAC) :: (.aluImm .srl a0 (6 : Fin 32) 0x19) :: (.lw a1 a4 0x18) :: (.lw a2 a4 0x1C) :: (.aluImm .sll a3 a5 0x7) :: (.aluImm .srl (8 : Fin 32) a5 0x16) :: (.aluImm .sll a5 (9 : Fin 32) 0xA) :: (.alu .or a0 a0 a3) :: (.alu .or (8 : Fin 32) (8 : Fin 32) a5) :: (.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x13) :: (.aluImm .sll a3 a1 0xD) :: (.aluImm .srl a1 a1 0x10) :: (.aluImm .sll a5 a2 0x10) :: (.alu .or a3 a3 (9 : Fin 32)) :: (.alu .or a1 a1 a5) :: (.alu .and a0 a0 (27 : Fin 32)) :: (.alu .and (8 : Fin 32) (8 : Fin 32) (27 : Fin 32)) :: (.alu .and a3 a3 (27 : Fin 32)) :: (.alu .and a1 a1 (27 : Fin 32)) :: (.aluImm .srl a2 a2 0xD) :: (.aluImm .add a4 (23 : Fin 32) 0x80) :: (.sw a4 a0 0x30) :: (.sw a4 (8 : Fin 32) 0x34) :: (.sw a4 a3 0x38) :: (.sw a4 a1 0x3C) :: (.sw a4 a2 0x40) :: (.lui a2 0x3FCC5000) :: (.aluImm .add a2 a2 0xFFFFF9E4) :: (.aluImm .add a0 sp 0x7F0) :: (.lui a1 0x1000) :: (.aluImm .add a1 a1 0x508) :: (.alu .add a1 a1 sp) :: [])

set_option maxRecDepth 20000 in
theorem evFbw2_end : blockEnd ed25519VerifyCode 0x1400 evFbw2 = some 0x14A2 :=
  (blockEnd_cons' (off' := 0x1404) ev_at_1400 rfl (blockEnd_cons' (off' := 0x1408) ev_at_1404 rfl (blockEnd_cons' (off' := 0x140A) ev_at_1408 rfl (blockEnd_cons' (off' := 0x140E) ev_at_140a rfl (blockEnd_cons' (off' := 0x1412) ev_at_140e rfl (blockEnd_cons' (off' := 0x1416) ev_at_1412 rfl (blockEnd_cons' (off' := 0x1418) ev_at_1416 rfl (blockEnd_cons' (off' := 0x141C) ev_at_1418 rfl (blockEnd_cons' (off' := 0x141E) ev_at_141c rfl (blockEnd_cons' (off' := 0x1422) ev_at_141e rfl (blockEnd_cons' (off' := 0x1424) ev_at_1422 rfl (blockEnd_cons' (off' := 0x1426) ev_at_1424 rfl (blockEnd_cons' (off' := 0x142A) ev_at_1426 rfl (blockEnd_cons' (off' := 0x142E) ev_at_142a rfl (blockEnd_cons' (off' := 0x1432) ev_at_142e rfl (blockEnd_cons' (off' := 0x1434) ev_at_1432 rfl (blockEnd_cons' (off' := 0x1436) ev_at_1434 rfl (blockEnd_cons' (off' := 0x143A) ev_at_1436 rfl (blockEnd_cons' (off' := 0x143E) ev_at_143a rfl (blockEnd_cons' (off' := 0x1442) ev_at_143e rfl (blockEnd_cons' (off' := 0x1446) ev_at_1442 rfl (blockEnd_cons' (off' := 0x144A) ev_at_1446 rfl (blockEnd_cons' (off' := 0x144C) ev_at_144a rfl (blockEnd_cons' (off' := 0x144E) ev_at_144c rfl (blockEnd_cons' (off' := 0x1452) ev_at_144e rfl (blockEnd_cons' (off' := 0x1456) ev_at_1452 rfl (blockEnd_cons' (off' := 0x145A) ev_at_1456 rfl (blockEnd_cons' (off' := 0x145C) ev_at_145a rfl (blockEnd_cons' (off' := 0x145E) ev_at_145c rfl (blockEnd_cons' (off' := 0x1460) ev_at_145e rfl (blockEnd_cons' (off' := 0x1464) ev_at_1460 rfl (blockEnd_cons' (off' := 0x1466) ev_at_1464 rfl (blockEnd_cons' (off' := 0x146A) ev_at_1466 rfl (blockEnd_cons' (off' := 0x146C) ev_at_146a rfl (blockEnd_cons' (off' := 0x146E) ev_at_146c rfl (blockEnd_cons' (off' := 0x1472) ev_at_146e rfl (blockEnd_cons' (off' := 0x1476) ev_at_1472 rfl (blockEnd_cons' (off' := 0x147A) ev_at_1476 rfl (blockEnd_cons' (off' := 0x147E) ev_at_147a rfl (blockEnd_cons' (off' := 0x1480) ev_at_147e rfl (blockEnd_cons' (off' := 0x1484) ev_at_1480 rfl (blockEnd_cons' (off' := 0x1486) ev_at_1484 rfl (blockEnd_cons' (off' := 0x1488) ev_at_1486 rfl (blockEnd_cons' (off' := 0x148A) ev_at_1488 rfl (blockEnd_cons' (off' := 0x148C) ev_at_148a rfl (blockEnd_cons' (off' := 0x148E) ev_at_148c rfl (blockEnd_cons' (off' := 0x1492) ev_at_148e rfl (blockEnd_cons' (off' := 0x1496) ev_at_1492 rfl (blockEnd_cons' (off' := 0x149A) ev_at_1496 rfl (blockEnd_cons' (off' := 0x149C) ev_at_149a rfl (blockEnd_cons' (off' := 0x14A0) ev_at_149c rfl (blockEnd_cons' (off' := 0x14A2) ev_at_14a0 rfl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1400: the high scalar's 9 limbs to `F + 0x15A8`, and the
arguments of `montgomery_mul(F + 0x7F0, F + 0x1508, R)`. -/
theorem ev_fbw2 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1400)
    (h19 : reg n 19 = F + 0x90F) (h23 : reg n 23 = F + BitVec.ofNat 32 0x1508) (h27 : reg n 27 = 0x1FFFFFFF)
    {Mo : Word → BitVec 8} (h7 : reg n 7 = memLoad32 Mo (F + BitVec.ofNat 32 0xA10))
    (h9 : reg n 9 = memLoad32 Mo (F + BitVec.ofNat 32 0xA14)) (h13 : reg n 13 = memLoad32 Mo (F + BitVec.ofNat 32 0xA18))
    (h6 : reg n 6 = memLoad32 Mo (F + BitVec.ofNat 32 0xA1C))
    (hw : ∀ c, 0xA20 ≤ c → c < 0xA30 → M (F + BitVec.ofNat 32 c) = Mo (F + BitVec.ofNat 32 c)) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x14A2 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n' q = reg n q) ∧
      ((limbAt M' (F + BitVec.ofNat 32 0x15A8) 0 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA10)).toNat / 2 ^ 5 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA14)).toNat * 2 ^ 27) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 1 = (memLoad32 Mo (F + BitVec.ofNat 32 0xA14)).toNat / 2 ^ 2 % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 2 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA14)).toNat / 2 ^ 31 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA18)).toNat * 2 ^ 1) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 3 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA18)).toNat / 2 ^ 28 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA1C)).toNat * 2 ^ 4) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 4 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA1C)).toNat / 2 ^ 25 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA20)).toNat * 2 ^ 7) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 5 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA20)).toNat / 2 ^ 22 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA24)).toNat * 2 ^ 10) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 6 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA24)).toNat / 2 ^ 19 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA28)).toNat * 2 ^ 13) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 7 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA28)).toNat / 2 ^ 16 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA2C)).toNat * 2 ^ 16) % 2 ^ 29) ∧
      (limbAt M' (F + BitVec.ofNat 32 0x15A8) 8 = (memLoad32 Mo (F + BitVec.ofNat 32 0xA2C)).toNat / 2 ^ 13)) ∧
      reg n' a0 = F + BitVec.ofNat 32 0x7F0 ∧ reg n' a1 = F + BitVec.ofNat 32 0x1508 ∧
      reg n' a2 = BitVec.ofNat 32 0x3FCC49E4 ∧
      ∀ c, c < 0x16A0 → (c < 0x15A8 ∨ 0x15CC ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have hal : ∀ c, c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => C.al h
  have hcs : ∀ c, c + 4 ≤ 0x16A0 → Sep (F + BitVec.ofNat 32 c) 4 EV ed25519VerifyCode.length :=
    fun c h => C.codeF h (by decide) (by rw [ev_len]; decide)
  have h19' : reg n 19 = F + BitVec.ofNat 32 0x90F := h19
  have peel : ∀ c v (M' : Word → BitVec 8) d, (c == d) = false → c % 4 = 0 → d % 4 = 0 → c + 4 ≤ 2 ^ 32 →
      d + 4 ≤ 2 ^ 32 → memLoad32 (memStore32 M' (F + BitVec.ofNat 32 c) v) (F + BitVec.ofNat 32 d) =
        memLoad32 M' (F + BitVec.ofNat 32 d) := fun c v M' d h1 h2 h3 h4 h5 => memLoad32_store32_off h1 h2 h3 h4 h5
  have hm : ∀ x, Sep (F + BitVec.ofNat 32 0x15A8) 0x24 x 1 → (runBlock evFbw2 (M, reg n)).1 x = M x := fun x hx => by
    have hst : ∀ (c : Nat) (v : Word) (M' : Word → BitVec 8), 0x15A8 ≤ c → c + 4 ≤ 0x15CC →
        memStore32 M' (F + BitVec.ofNat 32 c) v x = M' x := fun c v M' h1 h2 => st32_frame (by
      have := hx.sub (c := c - 0x15A8) (l := 4) (by omega)
      rwa [add_ofNat_assoc, show 0x15A8 + (c - 0x15A8) = c by omega] at this)
    simp +decide only [evFbw2, runBlock, BInstr.run, upd, ↓reduceIte, h19', h23, h7, h9, h13, h6, aluEval, BitVec.ofNat_eq_ofNat, add_ofNat_assoc, Nat.reduceAdd, BitVec.zero_add, D.st.zero]
    simp (disch := decide) only [hst]
  obtain ⟨n1, c1, D1, hr1⟩ := D.blockW C (d := 0x15A8) (k := 0x24) evFbw2 evFbw2_end
    (by simp +decide only [evFbw2, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, true_and, h19', h23, h7, h9, h13, h6, aluEval, BitVec.ofNat_eq_ofNat, add_ofNat_assoc, Nat.reduceAdd, BitVec.zero_add]
        simp (disch := decide) only [hal, hcs, and_self, true_and])
    (by decide) hm
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evFbw2, runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock evFbw2 (M, reg n)).1 = M1 := ⟨_, rfl⟩
  have fr : ∀ c, c < 0x16A0 → (c < 0x15A8 ∨ 0x15CC ≤ c) → M1 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      rw [← hM1]; refine hm _ (C.offs ?_ (by decide) (by omega))
      rcases hh with hh | hh
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  rw [hM1] at D1
  simp +decide only [evFbw2, runBlock, BInstr.run, upd, ↓reduceIte, h19', h23, h27, h7, h9, h13, h6, aluEval, BitVec.ofNat_eq_ofNat, add_ofNat_assoc, Nat.reduceAdd, BitVec.zero_add, D.st.zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hM1
  have hwl : ∀ c, 0xA20 ≤ c → c + 4 ≤ 0xA30 → memLoad32 M (F + BitVec.ofNat 32 c) = memLoad32 Mo (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => vk_ld2 fun j hj => by (try rw [add_ofNat_assoc]); (try rw [add_ofNat_assoc]); exact hw _ (by omega) (by omega)
  have w12 := hwl 0xA20 (by decide) (by decide)
  have w13 := hwl 0xA24 (by decide) (by decide)
  have w14 := hwl 0xA28 (by decide) (by decide)
  have w15 := hwl 0xA2C (by decide) (by decide)
  have hi : (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 0 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA10)).toNat / 2 ^ 5 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA14)).toNat * 2 ^ 27) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 1 = (memLoad32 Mo (F + BitVec.ofNat 32 0xA14)).toNat / 2 ^ 2 % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 2 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA14)).toNat / 2 ^ 31 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA18)).toNat * 2 ^ 1) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 3 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA18)).toNat / 2 ^ 28 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA1C)).toNat * 2 ^ 4) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 4 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA1C)).toNat / 2 ^ 25 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA20)).toNat * 2 ^ 7) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 5 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA20)).toNat / 2 ^ 22 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA24)).toNat * 2 ^ 10) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 6 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA24)).toNat / 2 ^ 19 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA28)).toNat * 2 ^ 13) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 7 = ((memLoad32 Mo (F + BitVec.ofNat 32 0xA28)).toNat / 2 ^ 16 + (memLoad32 Mo (F + BitVec.ofNat 32 0xA2C)).toNat * 2 ^ 16) % 2 ^ 29) ∧
      (limbAt M1 (F + BitVec.ofNat 32 0x15A8) 8 = (memLoad32 Mo (F + BitVec.ofNat 32 0xA2C)).toNat / 2 ^ 13) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [limbAt, add_ofNat_assoc, Nat.reduceMul, Nat.reduceAdd]; rw [← hM1]
     simp (disch := decide) only [↓peel, ↓memLoad32_store32_same]; (try simp only [w12, w13, w14, w15]); (first | (simp (disch := decide) only [limbB, limbB']; done) | (simp only [limbC]; done) | (simp only [limbA]; done) | (simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; done)))
  refine ⟨n1, M1, c1, D1, fun q hq h8 h9 => ?_, hi, ?_, ?_, ?_, fr⟩
  · rw [hr1, evb_reg q D.st.zero (by revert h9; revert h8; revert hq; revert q; decide)]
  · rw [hr1]; simp +decide only [evFbw2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  · rw [hr1]; simp +decide only [evFbw2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]
    exact BitVec.add_comm _ _
  · rw [hr1]; simp +decide only [evFbw2, runBlock, BInstr.run, upd, ↓reduceIte]

end

end C3.RV32

