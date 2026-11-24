import C3BootProofs.Proofs.Ed25519VerifyWrap3
import C3BootProofs.Image.BootloaderData7

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

/-- `Scalar29::add`'s running carry: before limb `i`, the carry is
`s29AddC a b i`, and limb `i` of the sum is `s29AddC a b (i + 1) % 2^29`. -/
def s29AddC (a b : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => s29AddC a b i / 2 ^ 29 + a i + b i

theorem s29AddC_lt {a b : Nat → Nat} (ha : ∀ t, t < 9 → a t < 2 ^ 29) (hb : ∀ t, t < 9 → b t < 2 ^ 29) :
    ∀ i, i ≤ 9 → s29AddC a b i < 2 ^ 31
  | 0, _ => by show 0 < 2 ^ 31; decide
  | i + 1, hi => by
    have := s29AddC_lt ha hb i (by omega)
    have := ha i (by omega); have := hb i (by omega)
    show s29AddC a b i / 2 ^ 29 + a i + b i < 2 ^ 31
    omega

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
      reg n' a2 = BitVec.ofNat 32 (img% edMontRAddress) ∧
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

theorem s29Out_lt (a : Nat → Nat) (j : Nat) : s29Out a j < 2 ^ 32 := by
  unfold s29Out; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

theorem smmIn_congr {M M' : Word → BitVec 8} {p : Word} (h : ∀ i, i < 36 → M' (p + BitVec.ofNat 32 i) = M (p + BitVec.ofNat 32 i)) :
    smmIn M' p = smmIn M p := by
  funext i
  unfold smmIn limbAt
  split
  · rw [vk_ld2 (M := M') (M' := M) (b := p + BitVec.ofNat 32 (4 * i)) (b' := p + BitVec.ofNat 32 (4 * i)) fun j hj => by
      rw [add_ofNat_assoc]; exact h _ (by omega)]
  · rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x14A2: the low scalar times `R` and the high scalar times
`R²`, in Montgomery form, back at `F + 0x1508` and `F + 0x15A8`, and
`F + 0x7F0` cleared. -/
theorem ev_mm (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x14A2)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 0x7F0) (ha1 : reg n a1 = F + BitVec.ofNat 32 0x1508)
    (ha2 : reg n a2 = BitVec.ofNat 32 (img% edMontRAddress)) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1508 ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (∀ j, j < 9 → limbAt M' (F + BitVec.ofNat 32 0x1508) j =
        s29Out (smmRed (smmIn M (F + BitVec.ofNat 32 0x1508)) (smmIn M0 (BitVec.ofNat 32 (img% edMontRAddress)))) j) ∧
      (∀ j, j < 9 → limbAt M' (F + BitVec.ofNat 32 0x15A8) j =
        s29Out (smmRed (smmIn M (F + BitVec.ofNat 32 0x15A8)) (smmIn M0 (BitVec.ofNat 32 (img% edMontRRAddress)))) j) ∧
      (∀ j, j < 36 → M' (F + BitVec.ofNat 32 (0x7F0 + j)) = 0) ∧
      ∀ c, c < 0x16A0 → (c < 0x7F0 ∨ (0x814 ≤ c ∧ c < 0x1508) ∨ (0x152C ≤ c ∧ c < 0x15A8) ∨ 0x15CC ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have ro : ∀ (Mx : Word → BitVec 8) {nx : Machine} {ox : Nat}, EvSt M0 Ms F r0 Mx nx ox → ∀ c, (img% roWindowAddress) ≤ c →
      c + 36 ≤ 0x3FCC5400 → smmIn Mx (BitVec.ofNat 32 c) = smmIn M0 (BitVec.ofNat 32 c) := fun Mx _ _ Dx c h1 h2 =>
    smmIn_congr fun i hi => by
      exact Dx.roM C (a := c) (k := 36) h1 h2 i hi
  obtain ⟨n1, c1, D1, k1, o1, fz1⟩ := D.montMul C (d := 0x7F0) (e := 0x1508) (c := (img% edMontRAddress)) ev_at_14a2 ev_at_14a6
    (by decide) (by decide) ha0 ha1 ha2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [ro M D _ (by decide) (by decide)] at o1
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x14BA)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x508) :: (.alu .add a0 a0 sp) :: (.aluImm .add a1 sp 0x7F0) ::
      (.aluImm .add a2 x0 0x24) :: [])
    (blockEnd_cons' (off' := 0x14AC) ev_at_14aa rfl (blockEnd_cons' (off' := 0x14B0) ev_at_14ac rfl
      (blockEnd_cons' (off' := 0x14B2) ev_at_14b0 rfl (blockEnd_cons' (off' := 0x14B6) ev_at_14b2 rfl
      (blockEnd_cons' (off' := 0x14BA) ev_at_14b6 rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n3, c3, D3, k3, fz3⟩ := D2.memcpy C (d := 0x1508) (s := F + BitVec.ofNat 32 0x7F0) (N := 0x24)
    ev_at_14ba ev_at_14be (by decide) (by decide)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D1.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D1.hsp]; rfl)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n4, c4, D4, hr4⟩ := D3.block C (off' := 0x14D6)
    ((.lui a2 (img% hi20 edMontRRAddress)) :: (.aluImm .add a2 a2 (img% lo12 edMontRRAddress)) :: (.aluImm .add a0 sp 0x7F0) :: (.lui a1 0x1000) ::
      (.aluImm .add a1 a1 0x5A8) :: (.alu .add a1 a1 sp) :: [])
    (blockEnd_cons' (off' := 0x14C6) ev_at_14c2 rfl (blockEnd_cons' (off' := 0x14CA) ev_at_14c6 rfl
      (blockEnd_cons' (off' := 0x14CE) ev_at_14ca rfl (blockEnd_cons' (off' := 0x14D0) ev_at_14ce rfl
      (blockEnd_cons' (off' := 0x14D4) ev_at_14d0 rfl (blockEnd_cons' (off' := 0x14D6) ev_at_14d4 rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n5, c5, D5, k5, o5, fz5⟩ := D4.montMul C (d := 0x7F0) (e := 0x15A8) (c := (img% edMontRRAddress)) ev_at_14d6 ev_at_14da
    (by decide) (by decide)
    (by rw [hr4]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D3.hsp]; rfl)
    (by rw [hr4]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D3.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr4]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [ro n3.mem D3 _ (by decide) (by decide)] at o5
  have hs3 : smmIn n3.mem (F + BitVec.ofNat 32 0x15A8) = smmIn M (F + BitVec.ofNat 32 0x15A8) :=
    smmIn_congr fun i hi => by
      rw [add_ofNat_assoc, cp_out C fz3 (by decide) (by omega) (Or.inr (by omega)), fz1 _ (C.zF (by omega))
        (C.offs (Or.inl (by omega)) (by decide) (by omega))]
  rw [hs3] at o5
  obtain ⟨n6, c6, D6, hr6⟩ := D5.block C (off' := 0x14EE)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x5A8) :: (.alu .add a0 a0 sp) :: (.aluImm .add a1 sp 0x7F0) ::
      (.aluImm .add a2 x0 0x24) :: [])
    (blockEnd_cons' (off' := 0x14E0) ev_at_14de rfl (blockEnd_cons' (off' := 0x14E4) ev_at_14e0 rfl
      (blockEnd_cons' (off' := 0x14E6) ev_at_14e4 rfl (blockEnd_cons' (off' := 0x14EA) ev_at_14e6 rfl
      (blockEnd_cons' (off' := 0x14EE) ev_at_14ea rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n7, c7, D7, k7, fz7⟩ := D6.memcpy C (d := 0x15A8) (s := F + BitVec.ofNat 32 0x7F0) (N := 0x24)
    ev_at_14ee ev_at_14f2 (by decide) (by decide)
    (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D5.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D5.hsp]; rfl)
    (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n8, c8, D8, hr8⟩ := D7.block C (off' := 0x1500)
    ((.aluImm .add a0 sp 0x7F0) :: (.aluImm .add a2 x0 0x24) :: (.aluImm .add a1 x0 0x0) :: [])
    (blockEnd_cons' (off' := 0x14FA) ev_at_14f6 rfl (blockEnd_cons' (off' := 0x14FE) ev_at_14fa rfl
      (blockEnd_cons' (off' := 0x1500) ev_at_14fe rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n9, c9, D9, k9⟩ := D8.memset C (d := 0x7F0) (b := 0) (N := 0x24) ev_at_1500 ev_at_1504 (by decide) (by decide)
    (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D7.hsp]; rfl)
    (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D7.st.zero]); try rfl)
    (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D7.st.zero]); try rfl)
    (by decide)
  have ld : ∀ (b c : Nat) (Mx : Word → BitVec 8), c + 4 ≤ 0x16A0 → (∀ i, i < 4 →
      fillBytes n7.mem (F + BitVec.ofNat 32 0x7F0) ((0 : Word).extractLsb' 0 8) 0x24 (F + BitVec.ofNat 32 (c + i)) =
        Mx (F + BitVec.ofNat 32 (b + i))) →
      memLoad32 (fillBytes n7.mem (F + BitVec.ofNat 32 0x7F0) ((0 : Word).extractLsb' 0 8) 0x24) (F + BitVec.ofNat 32 c) =
        memLoad32 Mx (F + BitVec.ofNat 32 b) := fun b c Mx _ h => vk_ld2 fun i hi => by
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact h i hi
  refine ⟨n9, _, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans c9))))))), D9,
    fun q hq => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun c hc hh => ?_⟩
  · rw [k9 q hq, hr8, evb_reg q D7.st.zero (by revert hq; revert q; decide), k7 q hq, hr6,
      evb_reg q D5.st.zero (by revert hq; revert q; decide), k5 q hq, hr4, evb_reg q D3.st.zero (by revert hq; revert q; decide),
      k3 q hq, hr2, evb_reg q D1.st.zero (by revert hq; revert q; decide), k1 q hq]
  · unfold limbAt
    rw [add_ofNat_assoc, ld (0x7F0 + 4 * j) (0x1508 + 4 * j) n1.mem (by omega) fun i hi => by
        rw [fb_out C (by decide) (by omega) (Or.inr (by omega)), cp_out C fz7 (by decide) (by omega) (Or.inl (by omega)),
          fz5 _ (C.zF (by omega)) (C.offs (Or.inl (by omega)) (by decide) (by omega)),
          show 0x1508 + 4 * j + i = 0x1508 + (4 * j + i) by omega, cp_at C fz3 (by decide) (by omega), add_ofNat_assoc,
          show 0x7F0 + (4 * j + i) = 0x7F0 + 4 * j + i by omega],
      ← add_ofNat_assoc, o1 j hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s29Out_lt _ _)]
  · unfold limbAt
    rw [add_ofNat_assoc, ld (0x7F0 + 4 * j) (0x15A8 + 4 * j) n5.mem (by omega) fun i hi => by
        rw [fb_out C (by decide) (by omega) (Or.inr (by omega)),
          show 0x15A8 + 4 * j + i = 0x15A8 + (4 * j + i) by omega, cp_at C fz7 (by decide) (by omega), add_ofNat_assoc,
          show 0x7F0 + (4 * j + i) = 0x7F0 + 4 * j + i by omega],
      ← add_ofNat_assoc, o5 j hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s29Out_lt _ _)]
  · rw [← add_ofNat_assoc, fb_in hj (by decide)]; rfl
  · have e5 : n5.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
      rcases hh with hh | hh | hh | hh <;>
        rw [fz5 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega)), cp_out C fz3 (by decide) hc (by omega),
          fz1 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
    rcases hh with hh | hh | hh | hh <;>
      rw [fb_out C (by decide) hc (by omega), cp_out C fz7 (by decide) hc (by omega), e5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- One pass of `Scalar29::add`'s loop at offset 0x1512, inlined: limb `i`
of `hi + lo` to `F + 0x7F0 + 4i`. -/
theorem ev_add_body (C : EvCtx M0 F pk sig msg len) {Mb M : Word → BitVec 8} {n : Machine} {i : Nat} (hi9 : i < 9)
    (D : EvSt M0 Ms F r0 M n 0x1512)
    (hA : ∀ t, t < 9 → limbAt Mb (F + BitVec.ofNat 32 0x15A8) t < 2 ^ 29)
    (hB : ∀ t, t < 9 → limbAt Mb (F + BitVec.ofNat 32 0x1508) t < 2 ^ 29)
    (hK : ∀ c, c < 0x16A0 → (c < 0x7F0 ∨ 0x814 ≤ c) → M (F + BitVec.ofNat 32 c) = Mb (F + BitVec.ofNat 32 c))
    (h8 : reg n 8 = BitVec.ofNat 32 i) (h18 : reg n 18 = 9)
    (h20 : reg n 20 = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) i))
    (h27 : reg n 27 = 0x1FFFFFFF) :
    ∃ n', Steps n n' ∧ (i + 1 < 9 → EvSt M0 Ms F r0 (memStore32 M (F + BitVec.ofNat 32 (0x7F0 + 4 * i))
        (BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (i + 1) % 2 ^ 29))) n' 0x1512) ∧
      (i + 1 = 9 → EvSt M0 Ms F r0 (memStore32 M (F + BitVec.ofNat 32 (0x7F0 + 4 * i))
        (BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (i + 1) % 2 ^ 29))) n' 0x1562) ∧
      reg n' 8 = BitVec.ofNat 32 (i + 1) ∧ reg n' 18 = 9 ∧
      reg n' 20 = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (i + 1)) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 19, 20] → reg n' q = reg n q) := by
  have hc0 := s29AddC_lt hA hB i (by omega)
  have hc1 := s29AddC_lt hA hB (i + 1) (by omega)
  have kA := hA i hi9
  have kB := hB i hi9
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1520)
    [.aluImm .add (19 : Fin 32) (8 : Fin 32) 1, .lui a0 0x1000, .aluImm .add a0 a0 0x5A8, .alu .add a0 a0 sp,
      .alu .add a1 x0 (8 : Fin 32)]
    (blockEnd_cons' ev_at_1512 rfl (blockEnd_cons' ev_at_1516 rfl (blockEnd_cons' ev_at_1518 rfl
      (blockEnd_cons' ev_at_151c rfl (blockEnd_cons' ev_at_151e rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, va2, k2⟩ := D1.idx C (p := F + BitVec.ofNat 32 0x15A8) (i := i) ev_at_1520 ev_at_1524 (by decide)
    (by decide) (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]
                    exact BitVec.add_comm _ _)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D.st.zero]); rw [h8]; exact BitVec.zero_add _)
    hi9
  have aA : (F + BitVec.ofNat 32 0x15A8 + BitVec.ofNat 32 (4 * i) + 0).toNat % 4 = 0 := by
    rw [add_lit_zero, add_ofNat_assoc]; exact C.al (by omega)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x1534)
    [.lw (9 : Fin 32) a0 0, .lui a0 0x1000, .aluImm .add a0 a0 0x508, .alu .add a0 a0 sp, .alu .add a1 x0 (8 : Fin 32)]
    (blockEnd_cons' ev_at_1528 rfl (blockEnd_cons' ev_at_152a rfl (blockEnd_cons' ev_at_152c rfl
      (blockEnd_cons' ev_at_1530 rfl (blockEnd_cons' ev_at_1532 rfl rfl)))))
    ⟨by show (reg n2 a0 + 0).toNat % 4 = 0
        rw [va2]; exact aA, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r8 : reg n2 8 = BitVec.ofNat 32 i := by
    rw [k2 8 (by decide) (by decide) (by decide) (by decide), hr1, evb_reg 8 D.st.zero (by decide), h8]
  obtain ⟨n4, c4, D4, va4, k4⟩ := D3.idx C (p := F + BitVec.ofNat 32 0x1508) (i := i) ev_at_1534 ev_at_1538 (by decide)
    (by decide) (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]
                    exact BitVec.add_comm _ _)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D2.st.zero]); rw [r8]; exact BitVec.zero_add _)
    hi9
  have aB : (F + BitVec.ofNat 32 0x1508 + BitVec.ofNat 32 (4 * i) + 0).toNat % 4 = 0 := by
    rw [add_lit_zero, add_ofNat_assoc]; exact C.al (by omega)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x154E)
    [.lw a0 a0 0, .aluImm .srl a1 (20 : Fin 32) 0x1D, .alu .add a1 a1 (9 : Fin 32), .alu .add (20 : Fin 32) a1 a0,
      .aluImm .add a0 sp 0x7F0, .alu .add a1 x0 (8 : Fin 32)]
    (blockEnd_cons' ev_at_153c rfl (blockEnd_cons' ev_at_153e rfl (blockEnd_cons' ev_at_1542 rfl
      (blockEnd_cons' ev_at_1544 rfl (blockEnd_cons' ev_at_1548 rfl (blockEnd_cons' ev_at_154c rfl rfl))))))
    ⟨by show (reg n4 a0 + 0).toNat % 4 = 0
        rw [va4]; exact aB, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k42 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ ra → q ≠ 9 → reg n4 q = reg n2 q := fun q h0 h1 h2 hr h9 => by
    rw [k4 q h0 h1 h2 hr, hr3, evb_reg q D2.st.zero (by revert h9 h1 h0; revert q; decide)]
  have r8' : reg n4 8 = BitVec.ofNat 32 i := by rw [k42 8 (by decide) (by decide) (by decide) (by decide) (by decide), r8]
  have r20 : reg n4 20 = reg n 20 := by
    rw [k42 20 (by decide) (by decide) (by decide) (by decide) (by decide), k2 20 (by decide) (by decide) (by decide)
      (by decide), hr1, evb_reg 20 D.st.zero (by decide)]
  have r9 : reg n4 9 = memLoad32 M (F + BitVec.ofNat 32 0x15A8 + BitVec.ofNat 32 (4 * i)) := by
    rw [k4 9 (by decide) (by decide) (by decide) (by decide), hr3]
    simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [va2, add_lit_zero]
  have lA : (memLoad32 M (F + BitVec.ofNat 32 0x15A8 + BitVec.ofNat 32 (4 * i))).toNat =
      limbAt Mb (F + BitVec.ofNat 32 0x15A8) i := by
    unfold limbAt; congr 1
    exact vk_ld2 fun j hj => by simp only [add_ofNat_assoc]; exact hK _ (by omega) (Or.inr (by omega))
  have lB : (memLoad32 M (F + BitVec.ofNat 32 0x1508 + BitVec.ofNat 32 (4 * i))).toNat =
      limbAt Mb (F + BitVec.ofNat 32 0x1508) i := by
    unfold limbAt; congr 1
    exact vk_ld2 fun j hj => by simp only [add_ofNat_assoc]; exact hK _ (by omega) (Or.inr (by omega))
  have v20 : reg n5 20 = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8))
      (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (i + 1)) := by
    rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [r20, h20, r9, va4, add_lit_zero]
    apply BitVec.eq_of_toNat_eq
    show ((BitVec.ofNat 32 (s29AddC _ _ i) >>> ((0x1D : Word).toNat % 32) +
      memLoad32 M (F + BitVec.ofNat 32 0x15A8 + BitVec.ofNat 32 (4 * i))) +
      memLoad32 M (F + BitVec.ofNat 32 0x1508 + BitVec.ofNat 32 (4 * i))).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, lA, lB, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0x1D : Word).toNat % 32 = 29 from rfl, Nat.shiftRight_eq_div_pow]
    show _ = (s29AddC _ _ i / 2 ^ 29 + _ + _) % 2 ^ 32
    rw [Nat.mod_eq_of_lt (show s29AddC _ _ i < 2 ^ 32 by omega)]
    omega
  have k54 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ 20 → reg n5 q = reg n4 q := fun q h0 h1 h20 => by
    rw [hr5, evb_reg q D4.st.zero (by revert h20 h1 h0; revert q; decide)]
  obtain ⟨n6, c6, D6, va6, k6⟩ := D5.idxm C (p := F + BitVec.ofNat 32 0x7F0) (i := i) ev_at_154e ev_at_1552 (by decide)
    (by decide) (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D4.st.zero]); rw [r8']
        exact BitVec.zero_add _)
    hi9
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x155A) [.alu .and a1 (20 : Fin 32) (27 : Fin 32)] (bEnd1 ev_at_1556 rfl)
    ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k76 : ∀ q : Fin 32, q ≠ a1 → reg n7 q = reg n6 q := fun q h1 => by
    rw [hr7, evb_reg q D6.st.zero (by revert h1; revert q; decide)]
  have k6' : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ ra → q ≠ 20 → q ≠ 9 → reg n6 q = reg n2 q :=
    fun q h0 h1 h2 hr h20 h9 => by rw [k6 q h0 h1 h2 hr, k54 q h0 h1 h20, k42 q h0 h1 h2 hr h9]
  have va1 : reg n7 a1 = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8))
      (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (i + 1) % 2 ^ 29) := by
    rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [k6 20 (by decide) (by decide) (by decide) (by decide), v20, k6' 27 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k2 27 (by decide) (by decide) (by decide) (by decide), hr1,
      evb_reg 27 D.st.zero (by decide), h27]
    apply BitVec.eq_of_toNat_eq
    rw [and_mask29, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show _ < 2 ^ 32 by have := Nat.mod_lt (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8))
        (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (i + 1)) (show 2 ^ 29 > 0 by decide); omega)]
  obtain ⟨n8, d8, D8, k8⟩ := D7.sw C ev_at_155a (off' := 0x155C) rfl (c := 0x7F0 + 4 * i)
    (by rw [k76 a0 (by decide), va6]; exact (add_lit_zero _).trans (add_ofNat_assoc F _ _)) (by omega) (by omega)
  rw [va1] at D8
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x155E) [.alu .add (8 : Fin 32) x0 (19 : Fin 32)] (bEnd1 ev_at_155c rfl)
    ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r19 : reg n9 19 = BitVec.ofNat 32 (i + 1) := by
    rw [hr9, evb_reg 19 D8.st.zero (by decide), k8, k76 19 (by decide),
      k6' 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k2 19 (by decide) (by decide) (by decide) (by decide), hr1]
    simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h8]
    show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1); rw [BitVec.ofNat_add_ofNat]
  have back : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ ra → q ≠ 20 → q ≠ 9 → q ≠ 8 → q ≠ 19 →
      reg n9 q = reg n q := fun q h0 h1 h2 hr h20 h9 h8' h19 => by
    rw [hr9, evb_reg q D8.st.zero (by revert h8'; revert q; decide), k8, k76 q h1, k6' q h0 h1 h2 hr h20 h9,
      k2 q h0 h1 h2 hr, hr1, evb_reg q D.st.zero (by revert h19 h1 h0; revert q; decide)]
  have r18 : reg n9 18 = 9 := by
    rw [back 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h18]
  have r8n : reg n9 8 = BitVec.ofNat 32 (i + 1) := by
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [show reg n8 19 = BitVec.ofNat 32 (i + 1) from by rw [← r19, hr9, evb_reg 19 D8.st.zero (by decide)]]
    exact BitVec.zero_add _
  have r20n : reg n9 20 = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8))
      (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (i + 1)) := by
    rw [hr9, evb_reg 20 D8.st.zero (by decide), k8, k76 20 (by decide), k6 20 (by decide) (by decide) (by decide) (by decide),
      v20]
  have cs : Steps n n9 := c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans
    ((Steps.single d8).trans c9)))))))
  have hne : (BitVec.ofNat 32 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have kq : ∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 19, 20] → reg n9 q = reg n q := fun q hq hn =>
    back q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hn; revert q; decide) (by revert hn; revert q; decide)
      (by revert hn; revert q; decide) (by revert hn; revert q; decide)
  by_cases hl : i + 1 < 9
  · obtain ⟨n10, d10, u10⟩ := D9.st.taken (D9.code C) 0x1512 ev_at_155e rfl (by
      rw [r19, r18]
      show (BitVec.ofNat 32 (i + 1) != 9) = true
      exact bne_iff_ne.mpr fun e => by have := congrArg BitVec.toNat e; rw [hne] at this; exact absurd this (by
        show i + 1 ≠ 9; omega))
    exact ⟨n10, cs.trans (Steps.single d10), fun _ => D9.jmp u10, fun h => absurd h (by omega),
      by rw [u10.regs, r8n], by rw [u10.regs, r18], by rw [u10.regs, r20n], fun q hq hn => by rw [u10.regs, kq q hq hn]⟩
  · obtain ⟨n10, d10, u10⟩ := D9.st.notTaken (D9.code C) 0x1562 ev_at_155e rfl (by
      rw [r19, r18, show i + 1 = 9 by omega]; rfl)
    exact ⟨n10, cs.trans (Steps.single d10), fun h => absurd h hl, fun _ => D9.jmp u10,
      by rw [u10.regs, r8n], by rw [u10.regs, r18], by rw [u10.regs, r20n], fun q hq hn => by rw [u10.regs, kq q hq hn]⟩

/-- `Scalar29::add`'s loop from pass `k`. -/
theorem ev_add_loop (C : EvCtx M0 F pk sig msg len) {Mb : Word → BitVec 8} {R : Fin 32 → Word}
    (hA : ∀ t, t < 9 → limbAt Mb (F + BitVec.ofNat 32 0x15A8) t < 2 ^ 29)
    (hB : ∀ t, t < 9 → limbAt Mb (F + BitVec.ofNat 32 0x1508) t < 2 ^ 29) :
    ∀ d k, k + d = 9 → k < 9 → ∀ (M : Word → BitVec 8) (n : Machine), EvSt M0 Ms F r0 M n 0x1512 →
      (∀ t, t < k → memLoad32 M (F + BitVec.ofNat 32 (0x7F0 + 4 * t)) = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (t + 1) % 2 ^ 29)) →
      (∀ c, c < 0x16A0 → (c < 0x7F0 ∨ 0x814 ≤ c) → M (F + BitVec.ofNat 32 c) = Mb (F + BitVec.ofNat 32 c)) →
      reg n 8 = BitVec.ofNat 32 k → reg n 18 = 9 → reg n 20 = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) k) →
      reg n 27 = 0x1FFFFFFF → (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 19, 20] → reg n q = R q) →
      ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1562 ∧
        (∀ t, t < 9 → memLoad32 M' (F + BitVec.ofNat 32 (0x7F0 + 4 * t)) = BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (t + 1) % 2 ^ 29)) ∧
        (∀ c, c < 0x16A0 → (c < 0x7F0 ∨ 0x814 ≤ c) → M' (F + BitVec.ofNat 32 c) = Mb (F + BitVec.ofNat 32 c)) ∧
        (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 19, 20] → reg n' q = R q) := by
  intro d
  induction d with
  | zero => intro k hk hk9; exact absurd hk (by omega)
  | succ d ih =>
    intro k hk hk9 M n D hS hK h8 h18 h20 h27 hR
    obtain ⟨n1, c1, D1a, D1b, r8, r18, r20, kq⟩ := ev_add_body C hk9 D hA hB hK h8 h18 h20 h27
    have hS1 : ∀ t, t < k + 1 → memLoad32 (memStore32 M (F + BitVec.ofNat 32 (0x7F0 + 4 * k))
        (BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (k + 1) % 2 ^ 29))) (F + BitVec.ofNat 32 (0x7F0 + 4 * t)) =
        BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (t + 1) % 2 ^ 29) := fun t ht => by
      by_cases e : t = k
      · subst e; exact memLoad32_store32_same _ _ _
      · rw [memLoad32_store32_sep (C.offs (by omega) (by omega) (by omega))]; exact hS t (by omega)
    have hK1 : ∀ c, c < 0x16A0 → (c < 0x7F0 ∨ 0x814 ≤ c) → memStore32 M (F + BitVec.ofNat 32 (0x7F0 + 4 * k))
        (BitVec.ofNat 32 (s29AddC (limbAt Mb (F + BitVec.ofNat 32 0x15A8)) (limbAt Mb (F + BitVec.ofNat 32 0x1508)) (k + 1) % 2 ^ 29)) (F + BitVec.ofNat 32 c) = Mb (F + BitVec.ofNat 32 c) :=
      fun c hc hh => by rw [st32_frame (C.offs (by omega) (by omega) (by omega))]; exact hK c hc hh
    have hR1 : ∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 19, 20] → reg n1 q = R q := fun q hq hn => by
      rw [kq q hq hn, hR q hq hn]
    have h271 : reg n1 27 = 0x1FFFFFFF := by rw [kq 27 (by decide) (by decide), h27]
    by_cases hl : k + 1 < 9
    · obtain ⟨n2, M2, c2, rest⟩ := ih (k + 1) (by omega) hl _ n1 (D1a hl) hS1 hK1 r8 r18 r20 h271 hR1
      exact ⟨n2, M2, c1.trans c2, rest⟩
    · have e9 : k + 1 = 9 := by omega
      exact ⟨n1, _, c1, D1b e9, fun t ht => hS1 t (by omega), hK1, hR1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`Scalar29::add(hi, lo)`, inlined**, from offset 0x1508: the sum of the
scalars at `F + 0x15A8` and `F + 0x1508`, limb by limb with carries, to
`F + 0x7F0`. -/
theorem ev_s29add (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1508)
    (h27 : reg n 27 = 0x1FFFFFFF) (hA : ∀ t, t < 9 → limbAt M (F + BitVec.ofNat 32 0x15A8) t < 2 ^ 29)
    (hB : ∀ t, t < 9 → limbAt M (F + BitVec.ofNat 32 0x1508) t < 2 ^ 29) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1562 ∧
      (∀ t, t < 9 → limbAt M' (F + BitVec.ofNat 32 0x7F0) t =
        s29AddC (limbAt M (F + BitVec.ofNat 32 0x15A8)) (limbAt M (F + BitVec.ofNat 32 0x1508)) (t + 1) % 2 ^ 29) ∧
      (∀ c, c < 0x16A0 → (c < 0x7F0 ∨ 0x814 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 18, 19, 20] → reg n' q = reg n q) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x150E)
    [.aluImm .add (8 : Fin 32) x0 0, .aluImm .add (20 : Fin 32) x0 0, .aluImm .add (18 : Fin 32) x0 9]
    (blockEnd_cons' ev_at_1508 rfl (blockEnd_cons' ev_at_150a rfl (blockEnd_cons' ev_at_150c rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v18 : reg n1 18 = 9 := by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D.st.zero]; try rfl
  obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x1512 ev_at_150e rfl (by rw [v18, D1.st.zero]; rfl)
  have D2 := D1.jmp u2
  obtain ⟨n3, M3, c3, D3, hS3, hK3, kq3⟩ := ev_add_loop C (Mb := M) (R := reg n2) hA hB 9 0 rfl (by decide) M n2 D2
    (fun t ht => absurd ht (by omega)) (fun _ _ _ => rfl)
    (by rw [u2.regs, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D.st.zero]; try rfl)
    (by rw [u2.regs, v18])
    (by rw [u2.regs, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D.st.zero]; try rfl)
    (by rw [u2.regs, hr1, evb_reg 27 D.st.zero (by decide), h27]) (fun _ _ _ => rfl)
  refine ⟨n3, M3, c1.trans ((Steps.single d2).trans c3), D3, fun t ht => ?_, hK3, fun q hq hn => ?_⟩
  · show (memLoad32 M3 (F + BitVec.ofNat 32 0x7F0 + BitVec.ofNat 32 (4 * t))).toNat = _
    rw [add_ofNat_assoc, hS3 t ht, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := Nat.mod_lt (s29AddC (limbAt M (F + BitVec.ofNat 32 0x15A8)) (limbAt M (F + BitVec.ofNat 32 0x1508)) (t + 1))
        (show 2 ^ 29 > 0 by decide)
      omega)]
  · rw [kq3 q hq (by revert hn; revert q; decide), u2.regs, hr1, evb_reg q D.st.zero (by revert hn; revert q; decide)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1562: the sum at `F + 0x7F0` reduced by `Scalar29::sub(_, L)`
into `F + 0x1468` and packed into the 32 bytes of `k` at `F + 0x520`. -/
theorem ev_kpack (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1562) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x158E ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 18 → reg n' q = reg n q) ∧ reg n' 18 = F + BitVec.ofNat 32 0x7F0 ∧
      memBytes M' (F + BitVec.ofNat 32 0x520) 32 = evPackS (ssAw M (F + BitVec.ofNat 32 0x7F0)) ∧
      ∀ c, c < 0x16A0 → (c < 0x520 ∨ (0x540 ≤ c ∧ c < 0x1468) ∨ 0x148C ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1572)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x468) :: (.alu .add a0 a0 sp) :: (.aluImm .add a1 sp 0x7F0) ::
      (.aluImm .add (18 : Fin 32) sp 0x7F0) :: [])
    (blockEnd_cons' (off' := 0x1564) ev_at_1562 rfl (blockEnd_cons' (off' := 0x1568) ev_at_1564 rfl
      (blockEnd_cons' (off' := 0x156A) ev_at_1568 rfl (blockEnd_cons' (off' := 0x156E) ev_at_156a rfl
      (blockEnd_cons' (off' := 0x1572) ev_at_156e rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, k2, o2, f2⟩ := D1.s29sub C (d := 0x1468) (e := 0x7F0) ev_at_1572 ev_at_1576 (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x1586)
    ((.aluImm .add a0 sp 0x520) :: (.lui a1 0x1000) :: (.aluImm .add a1 a1 0x468) :: (.alu .add a1 a1 sp) :: [])
    (blockEnd_cons' (off' := 0x157E) ev_at_157a rfl (blockEnd_cons' (off' := 0x1580) ev_at_157e rfl
      (blockEnd_cons' (off' := 0x1584) ev_at_1580 rfl (blockEnd_cons' (off' := 0x1586) ev_at_1584 rfl rfl))))
    ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, o4, f4⟩ := D3.s29pack C (d := 0x520) (e := 0x1468) ev_at_1586 ev_at_158a (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; exact BitVec.add_comm _ _)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨n4, n4.mem, c1.trans (c2.trans (c3.trans c4)), D4, fun q hq h18 => ?_, ?_, ?_, fun c hc hh => ?_⟩
  · rw [k4 q hq, hr3, evb_reg q D2.st.zero (by revert hq; revert q; decide), k2 q hq, hr1,
      evb_reg q D.st.zero (by revert h18; revert hq; revert q; decide)]
  · rw [k4 18 (by decide), hr3, evb_reg 18 D2.st.zero (by decide), k2 18 (by decide), hr1]
    simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  · unfold memBytes evPackS
    refine List.map_congr_left fun j hj => ?_
    rw [o4 j (List.mem_range.mp hj)]
    exact congrArg _ (s29PackByte_congr (fun i hi => o2 i hi) j)
  · rw [f4 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega)),
      f2 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]

end

end C3.RV32


