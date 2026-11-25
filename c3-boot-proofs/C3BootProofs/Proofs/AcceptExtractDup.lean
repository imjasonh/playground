import C3BootProofs.Proofs.AcceptExtractDupK

/-!
# The extract stage's no-duplicates checks

From 0x1434 to 0x1778 the closure checks that no Fulcio subject or key, no
log origin or key, and no TSA signer id or key is listed twice. Each check
sets `s2` and `s4` to the bounds of one of the arrays that the loops before
it filled, starts the enumerator at `sp + 0x244`, and runs one of the two
loop shapes of `AcceptExtractDupN` and `AcceptExtractDupK`. A duplicate
jumps to 0x1774, which leaves through 0x7D6 with code 0xD.

`ace_dup` proves `AceDupStage`: from 0x1434 the closure reaches the exit
at 0x7D6, or 0x1778 with the keys where they were and `AceDistinct`.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

/-! ## The arrays from `AceKeysRead` -/

theorem acedp_slotE (B : Word) (a i : Nat) : acSlot B a + BitVec.ofNat 32 (0x20 * i) = acedpE B a i := by
  unfold acedpE acSlot
  rw [add_ofNat_assoc, Nat.add_assoc 0x3A50]

section
variable {α : Type} {X : AceCtx} {fp : Word} {N : Word → BitVec 8} {a cap : Nat} {l : List α}
  {nm ky : α → Bytes} {n : Nat} {win : α → Window}

theorem acedp_entryAt
    (h : SvArrayAt N (acSlot X.B a) cap l fun e k => AceEntryIn X.Bf fp N e (nm k) (ky k) n (win k))
    {i : Nat} (hi : i < l.length) : AceEntryIn X.Bf fp N (acedpE X.B a i) (nm l[i]) (ky l[i]) n (win l[i]) := by
  have := h.2.1 i hi
  rw [acedp_slotE] at this
  exact this

theorem acedp_getMap (f : α → Bytes) {i : Nat} (hi : i < l.length) : (l.map f)[i]? = some (f l[i]) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hi]
  try rfl

/-- Entry `i`'s name: the slice of its first two words. -/
theorem acedp_name
    (h : SvArrayAt N (acSlot X.B a) cap l fun e k => AceEntryIn X.Bf fp N e (nm k) (ky k) n (win k)) :
    ∀ i, i < l.length → ∃ bs, (l.map nm)[i]? = some bs ∧ AceBytesIn X.Bf fp N (memLoad32 N (acedpE X.B a i))
      (memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 4)).toNat bs :=
  fun i hi => ⟨nm l[i], acedp_getMap nm hi, (acedp_entryAt h hi).name⟩

/-- Entry `i`'s key: the `n` bytes its word at 0x18 points at. -/
theorem acedp_key
    (h : SvArrayAt N (acSlot X.B a) cap l fun e k => AceEntryIn X.Bf fp N e (nm k) (ky k) n (win k)) :
    ∀ i, i < l.length → ∃ bs, (l.map ky)[i]? = some bs ∧
      AceBytesIn X.Bf fp N (memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 0x18)) n bs :=
  fun i hi => ⟨ky l[i], acedp_getMap ky hi, (acedp_entryAt h hi).key⟩

theorem acedp_arr
    (h : SvArrayAt N (acSlot X.B a) cap l fun e k => AceEntryIn X.Bf fp N e (nm k) (ky k) n (win k))
    (hal : a % 4 = 0) (hpos : (0x250 ≤ a ∧ a + 0x20 * cap + 4 ≤ 0x1320) ∨ (0x132C ≤ a ∧ a + 0x20 * cap + 4 ≤ 0x2020))
    (hc : cap ≤ 16) : AcedpArr X N a cap l.length := by
  refine ⟨hal, hpos, hc, h.1, fun i hi e0 => ?_, fun i h1 h2 => ?_⟩
  · have h1 := (acedp_entryAt h hi).name.1
    rw [e0] at h1
    have h0 : (0 : Word).toNat = 0 := rfl
    omega
  · have := h.2.2 i h1 h2
    rwa [acedp_slotE] at this

end

/-! ## The compares -/

theorem acedp_ifEq {xs : List Bytes} {i j : Nat} {bi bj : Bytes} (xi : xs[i]? = some bi) (xj : xs[j]? = some bj) :
    (if bj = bi then (1 : Word) else 0) = if xs[j]? = xs[i]? then 1 else 0 := by
  rw [xj, xi]
  by_cases e : bj = bi
  · rw [if_pos e, if_pos (congrArg some e)]
  · rw [if_neg e, if_neg fun h => e (Option.some.inj h)]

section
variable {X : AceCtx} {N : Word → BitVec 8} {fp : Word} {Q : Post} (S : AcedpS X N fp)
include S

/-- The compare of two names with `sliceEq`. -/
theorem acedp_cmpN {o a len : Nat} {xs : List Bytes} {hi lo : Word}
    (c0 : fetchRel bootMainClosure0Code (o + 0x66) = some (.auipc ra hi, 4))
    (c4 : fetchRel bootMainClosure0Code (o + 0x66 + 4) = some (.jalr ra ra lo, 4))
    (tS : AC + BitVec.ofNat 32 (o + 0x66) + hi + lo = RSE) (hev : (o + 0x66 + 8) % 2 = 0)
    (hn : ∀ i, i < len → ∃ bs, xs[i]? = some bs ∧ AceBytesIn X.Bf fp N (memLoad32 N (acedpE X.B a i))
      (memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 4)).toNat bs) :
    AcedpCmpN X N Q o a len xs := by
  intro M f i j hi hj hM R h0 h1 h2 h3 k
  obtain ⟨bj, xj, Bj⟩ := hn j hj
  obtain ⟨bi, xi, Bi⟩ := hn i hi
  have F := S.ok.lay.fr
  have env := acedp_env S hM
  have hz := R.rz
  refine WP.callSliceEq (p := memLoad32 N (acedpE X.B a j))
    (pl := (memLoad32 N (acedpE X.B a j + BitVec.ofNat 32 4)).toNat) (q := memLoad32 N (acedpE X.B a i))
    (ql := (memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 4)).toNat) c0 c4 tS (by decide) hev env.sliceEq
    (by rw [show RSE + 0xFFFFEBAA = RES by decide]; exact env.equal)
    (by rw [show RSE + 0xBF68 = RMC by decide]; exact env.memcmp)
    h0 (by rw [h1, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h2 (by rw [h3, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (BitVec.isLt _) (BitVec.isLt _)
    (by rw [R.rsp]; exact ace_al4 F (c := 0x3A50) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr4]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr4]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr4]; exact acedp_bSep S Bj (by decide))
    (by rw [R.rsp, acedp_fr4]; exact acedp_bSep S Bi (by decide))
    (by rw [R.rsp, acedp_fr4]; exact ace_cs F (by decide)) fun m2 ha0 hO => ?_
  rw [R.rsp, acedp_fr4] at hO
  refine acedp_wpOff (by omega) (k m2.mem _ (acedp_out4 hO) (acedp_clob hz) ?_)
  rsimp
  rw [ha0, acedp_bytes S hM Bj, acedp_bytes S hM Bi]
  exact acedp_ifEq xi xj

/-- The compare of two 97-byte keys with `eqArr97`. -/
theorem acedp_cmp97 {o a len : Nat} {xs : List Bytes} {hi lo : Word}
    (c0 : fetchRel bootMainClosure0Code (o + 0x60) = some (.auipc ra hi, 4))
    (c4 : fetchRel bootMainClosure0Code (o + 0x60 + 4) = some (.jalr ra ra lo, 4))
    (tS : AC + BitVec.ofNat 32 (o + 0x60) + hi + lo = BitVec.ofNat 32 eqArr97Address)
    (hev : (o + 0x60 + 8) % 2 = 0)
    (hk : ∀ i, i < len → ∃ bs, xs[i]? = some bs ∧
      AceBytesIn X.Bf fp N (memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 0x18)) 0x61 bs) :
    AcedpCmpK X N Q o a len xs := by
  intro M f i j hi hj hM R h0 h1 k
  obtain ⟨bj, xj, Bj⟩ := hk j hj
  obtain ⟨bi, xi, Bi⟩ := hk i hi
  have F := S.ok.lay.fr
  have env := acedp_env S hM
  have hz := R.rz
  refine WP.callEq97 (p := memLoad32 N (acedpE X.B a j + BitVec.ofNat 32 0x18))
    (q := memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 0x18)) c0 c4 tS hev env.eq97
    (by rw [show BitVec.ofNat 32 eqArr97Address + 0xC04C = RMC by decide]; exact env.memcmp)
    h0 h1 (by rw [R.rsp]; exact ace_al4 F (c := 0x3A50) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr16]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr16]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr16]; exact (acedp_bSep S Bj (by decide)).symm)
    (by rw [R.rsp, acedp_fr16]; exact (acedp_bSep S Bi (by decide)).symm)
    (by rw [R.rsp, acedp_fr16]; exact ace_cs F (by decide)) fun m2 ha0 hO => ?_
  rw [R.rsp, acedp_fr16] at hO
  refine acedp_wpOff (by omega) (k m2.mem _ hO (acedp_clob hz) ?_)
  rsimp
  rw [ha0, acedp_bytes S hM Bj, acedp_bytes S hM Bi]
  exact acedp_ifEq xi xj

/-- The compare of two 32-byte keys with `arr32Eq`. -/
theorem acedp_cmp32 {o a len : Nat} {xs : List Bytes} {hi lo : Word}
    (c0 : fetchRel bootMainClosure0Code (o + 0x60) = some (.auipc ra hi, 4))
    (c4 : fetchRel bootMainClosure0Code (o + 0x60 + 4) = some (.jalr ra ra lo, 4))
    (tS : AC + BitVec.ofNat 32 (o + 0x60) + hi + lo = BitVec.ofNat 32 arr32EqAddress)
    (hev : (o + 0x60 + 8) % 2 = 0)
    (hk : ∀ i, i < len → ∃ bs, xs[i]? = some bs ∧
      AceBytesIn X.Bf fp N (memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 0x18)) 32 bs) :
    AcedpCmpK X N Q o a len xs := by
  intro M f i j hi hj hM R h0 h1 k
  obtain ⟨bj, xj, Bj⟩ := hk j hj
  obtain ⟨bi, xi, Bi⟩ := hk i hi
  have F := S.ok.lay.fr
  have env := acedp_env S hM
  have hz := R.rz
  refine WP.callArr32 (p := memLoad32 N (acedpE X.B a j + BitVec.ofNat 32 0x18))
    (q := memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 0x18)) c0 c4 tS hev env.eq32
    (by rw [show BitVec.ofNat 32 arr32EqAddress + 0xC032 = RMC by decide]; exact env.memcmp)
    h0 h1 (by rw [R.rsp]; exact ace_al4 F (c := 0x3A50) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr4]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr4]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rw [R.rsp, acedp_fr4]; exact acedp_bSep S Bj (by decide))
    (by rw [R.rsp, acedp_fr4]; exact acedp_bSep S Bi (by decide))
    (by rw [R.rsp, acedp_fr4]; exact ace_cs F (by decide)) fun m2 ha0 hO => ?_
  rw [R.rsp, acedp_fr4] at hO
  refine acedp_wpOff (by omega) (k m2.mem _ (acedp_out4 hO) (acedp_clob hz) ?_)
  rsimp
  rw [ha0, acedp_bytes S hM Bj, acedp_bytes S hM Bi]
  exact acedp_ifEq xi xj

/-! ## A check from its header's last four instructions -/

/-- `addi a0, sp, 0x200` and the stores of `s2`, `s4`, and 0 to the
enumerator at `sp + 0x244`. -/
theorem acedp_hdr {p a cap : Nat}
    (c0 : fetchRel bootMainClosure0Code p = some (.aluImm .add a0 sp 0x200, 2))
    (c2 : fetchRel bootMainClosure0Code (p + 2) = some (.store .sw a0 (18 : Fin 32) 0x44, 4))
    (c6 : fetchRel bootMainClosure0Code (p + 6) = some (.store .sw a0 (20 : Fin 32) 0x48, 4))
    (cA : fetchRel bootMainClosure0Code (p + 0xA) = some (.store .sw a0 x0 0x4C, 4))
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f)
    (h18 : f 18 = acedpE X.B a 0) (h20 : f 20 = acedpE X.B a cap)
    (k : ∀ (M2 : Word → BitVec 8) (g : Fin 32 → Word), AcedpOut X N M2 g a cap 0 →
      WP bootMainClosure0Code AC Q M2 (p + 0xE) g) :
    WP bootMainClosure0Code AC Q M p f := by
  have F := S.ok.lay.fr
  have hz := R.rz
  refine WP.aluImm c0 ?_; acedp_wo
  refine acedp_sw c2 (a := acSlot X.B 0x244) (w := acedpE X.B a 0)
    (by rsimp; rw [R.rsp]; exact acedp_spE0 X.B) (by rsimp; exact h18)
    (ace_al4 F (c := 0x3C94) (by decide) (by decide)) (ace_cs F (c := 0x3C94) (by decide)) ?_
  acedp_wo
  refine acedp_sw c6 (a := acSlot X.B 0x248) (w := acedpE X.B a cap)
    (by rsimp; rw [R.rsp, acedp_spE4, acedp_E4]) (by rsimp; exact h20)
    (ace_al4 F (c := 0x3C98) (by decide) (by decide)) (ace_cs F (c := 0x3C98) (by decide)) ?_
  acedp_wo
  refine acedp_sw cA (a := acSlot X.B 0x24C) (w := 0)
    (by rsimp; rw [R.rsp, acedp_spE8, acedp_E8]) (by rsimp)
    (ace_al4 F (c := 0x3C9C) (by decide) (by decide)) (ace_cs F (c := 0x3C9C) (by decide)) ?_
  acedp_wo
  obtain ⟨l0, l4, l8, hO⟩ := acedp_st3 (M := M) F (c := 0x244) (c4 := 0x248) (c8 := 0x24C) (by decide) rfl rfl
    (acedpE X.B a 0) (acedpE X.B a cap) 0
  exact k _ _ ⟨fun x hx => (hO x (AcedpW.sE F hx)).trans (hM x hx), by acedp_hr, by rsimp; exact h18,
    by rsimp; exact h20, l0, l4, l8⟩

/-- A check over names, from its header's last four instructions at `p`. -/
theorem acedp_runN {p o a cap len T : Nat} {xs : List Bytes} {hE lE xE hT lT bo : Word}
    (A : AcedpArr X N a cap len) (I : AcedpNI o hE lE xE hT lT bo)
    (c0 : fetchRel bootMainClosure0Code p = some (.aluImm .add a0 sp 0x200, 2))
    (c2 : fetchRel bootMainClosure0Code (p + 2) = some (.store .sw a0 (18 : Fin 32) 0x44, 4))
    (c6 : fetchRel bootMainClosure0Code (p + 6) = some (.store .sw a0 (20 : Fin 32) 0x48, 4))
    (cA : fetchRel bootMainClosure0Code (p + 0xA) = some (.store .sw a0 x0 0x4C, 4)) (hp : p + 0xE = o)
    (ho : o + 0x80 < 2 ^ 32) (hev : o % 2 = 0)
    (tE : AC + BitVec.ofNat 32 (o + 2) + hE + lE = BitVec.ofNat 32 fulcioEnumNextAddress)
    (tT : AC + BitVec.ofNat 32 (o + 0x1E + 0x20) + hT + lT = BitVec.ofNat 32 fulcioIterNthAddress)
    (tX : (o + 0xA + xE.toNat) % 2 ^ 32 = T) (cmp : AcedpCmpN X N Q o a len xs) (hl : xs.length = len)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B a cap → distinct xs = true →
      WP bootMainClosure0Code AC Q M T f)
    (kd : ∀ M f, AcedpM X N M → AcedpR X f → WP bootMainClosure0Code AC Q M (o + 0x72) f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f)
    (h18 : f 18 = acedpE X.B a 0) (h20 : f 20 = acedpE X.B a cap) :
    WP bootMainClosure0Code AC Q M p f :=
  acedp_hdr S c0 c2 c6 cA hM R h18 h20 fun _ _ H =>
    acedp_wpOff hp (acedp_nCheck S A I ho hev tE tT tX cmp hl kx kd H)

/-- A check over keys, from its header's last four instructions at `p`. -/
theorem acedp_runK {p o a cap len T : Nat} {xs : List Bytes} {hE lE xE hT lT bo : Word}
    (A : AcedpArr X N a cap len) (I : AcedpKI o hE lE xE hT lT bo)
    (c0 : fetchRel bootMainClosure0Code p = some (.aluImm .add a0 sp 0x200, 2))
    (c2 : fetchRel bootMainClosure0Code (p + 2) = some (.store .sw a0 (18 : Fin 32) 0x44, 4))
    (c6 : fetchRel bootMainClosure0Code (p + 6) = some (.store .sw a0 (20 : Fin 32) 0x48, 4))
    (cA : fetchRel bootMainClosure0Code (p + 0xA) = some (.store .sw a0 x0 0x4C, 4)) (hp : p + 0xE = o)
    (ho : o + 0x80 < 2 ^ 32) (hev : o % 2 = 0)
    (tE : AC + BitVec.ofNat 32 (o + 2) + hE + lE = BitVec.ofNat 32 fulcioEnumNextAddress)
    (tT : AC + BitVec.ofNat 32 (o + 0x1A + 0x20) + hT + lT = BitVec.ofNat 32 fulcioIterNthAddress)
    (tX : (o + 0xA + xE.toNat) % 2 ^ 32 = T) (cmp : AcedpCmpK X N Q o a len xs) (hl : xs.length = len)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B a cap → distinct xs = true →
      WP bootMainClosure0Code AC Q M T f)
    (kd : ∀ M f, AcedpM X N M → AcedpR X f → WP bootMainClosure0Code AC Q M (o + 0x6C) f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f)
    (h18 : f 18 = acedpE X.B a 0) (h20 : f 20 = acedpE X.B a cap) :
    WP bootMainClosure0Code AC Q M p f :=
  acedp_hdr S c0 c2 c6 cA hM R h18 h20 fun _ _ H =>
    acedp_wpOff hp (acedp_kCheck S A I ho hev tE tT tX cmp hl kx kd H)

end

/-! ## The six checks -/

theorem acedp_i1 : AcedpNI 0x1456 0xB000 0xFFFFF932 0x70 0xB000 0xFFFFF91C 0xFFFFFFBA :=
  ⟨ac_at_1456, ac_at_1458, ac_at_145c, ac_at_1460, ac_at_1462, ac_at_1464, ac_at_1468, ac_at_146c,
    ac_at_1470, ac_at_1472, ac_at_1474, ac_at_1476, ac_at_147a, ac_at_147c, ac_at_1480, ac_at_1484,
    ac_at_1488, ac_at_148c, ac_at_148e, ac_at_1492, ac_at_1494, ac_at_1498, ac_at_149c, ac_at_149e,
    ac_at_14a0, ac_at_14a4, ac_at_14a6, ac_at_14a8, ac_at_14aa, ac_at_14ae, ac_at_14b0, ac_at_14b2,
    ac_at_14b4, ac_at_14b8, ac_at_14ba, ac_at_14c4, ac_at_14c6⟩

theorem acedp_i2 : AcedpKI 0x14E8 0xB000 0xFFFFF8A0 0x64 0xB000 0xFFFFF88E 0xFFFFFFBE :=
  ⟨ac_at_14e8, ac_at_14ea, ac_at_14ee, ac_at_14f2, ac_at_14f4, ac_at_14f6, ac_at_14fa, ac_at_14fe,
    ac_at_1500, ac_at_1502, ac_at_1504, ac_at_1508, ac_at_150a, ac_at_150e, ac_at_1512, ac_at_1516,
    ac_at_151a, ac_at_151c, ac_at_1520, ac_at_1522, ac_at_1526, ac_at_152a, ac_at_152c, ac_at_152e,
    ac_at_1532, ac_at_1534, ac_at_1536, ac_at_1538, ac_at_153c, ac_at_153e, ac_at_1540, ac_at_1542,
    ac_at_1546, ac_at_1550, ac_at_1552⟩

theorem acedp_i3 : AcedpNI 0x156C 0xB000 0xFFFFF81C 0x6A 0xB000 0xFFFFF806 0xFFFFFFBA :=
  ⟨ac_at_156c, ac_at_156e, ac_at_1572, ac_at_1576, ac_at_1578, ac_at_157a, ac_at_157e, ac_at_1582,
    ac_at_1586, ac_at_1588, ac_at_158a, ac_at_158c, ac_at_1590, ac_at_1592, ac_at_1596, ac_at_159a,
    ac_at_159e, ac_at_15a2, ac_at_15a4, ac_at_15a8, ac_at_15aa, ac_at_15ae, ac_at_15b2, ac_at_15b4,
    ac_at_15b6, ac_at_15ba, ac_at_15bc, ac_at_15be, ac_at_15c0, ac_at_15c4, ac_at_15c6, ac_at_15c8,
    ac_at_15ca, ac_at_15ce, ac_at_15d0, ac_at_15da, ac_at_15dc⟩

theorem acedp_i4 : AcedpKI 0x15F2 0xA000 0x796 0x64 0xA000 0x784 0xFFFFFFBE :=
  ⟨ac_at_15f2, ac_at_15f4, ac_at_15f8, ac_at_15fc, ac_at_15fe, ac_at_1600, ac_at_1604, ac_at_1608,
    ac_at_160a, ac_at_160c, ac_at_160e, ac_at_1612, ac_at_1614, ac_at_1618, ac_at_161c, ac_at_1620,
    ac_at_1624, ac_at_1626, ac_at_162a, ac_at_162c, ac_at_1630, ac_at_1634, ac_at_1636, ac_at_1638,
    ac_at_163c, ac_at_163e, ac_at_1640, ac_at_1642, ac_at_1646, ac_at_1648, ac_at_164a, ac_at_164c,
    ac_at_1650, ac_at_165a, ac_at_165c⟩

theorem acedp_i5 : AcedpNI 0x167E 0xA000 0x70A 0x6A 0xA000 0x6F4 0xFFFFFFBA :=
  ⟨ac_at_167e, ac_at_1680, ac_at_1684, ac_at_1688, ac_at_168a, ac_at_168c, ac_at_1690, ac_at_1694,
    ac_at_1698, ac_at_169a, ac_at_169c, ac_at_169e, ac_at_16a2, ac_at_16a4, ac_at_16a8, ac_at_16ac,
    ac_at_16b0, ac_at_16b4, ac_at_16b6, ac_at_16ba, ac_at_16bc, ac_at_16c0, ac_at_16c4, ac_at_16c6,
    ac_at_16c8, ac_at_16cc, ac_at_16ce, ac_at_16d0, ac_at_16d2, ac_at_16d6, ac_at_16d8, ac_at_16da,
    ac_at_16dc, ac_at_16e0, ac_at_16e2, ac_at_16ec, ac_at_16ee⟩

theorem acedp_i6 : AcedpKI 0x1708 0xA000 0x680 0x66 0xA000 0x66E 0xFFFFFFBE :=
  ⟨ac_at_1708, ac_at_170a, ac_at_170e, ac_at_1712, ac_at_1714, ac_at_1716, ac_at_171a, ac_at_171e,
    ac_at_1720, ac_at_1722, ac_at_1724, ac_at_1728, ac_at_172a, ac_at_172e, ac_at_1732, ac_at_1736,
    ac_at_173a, ac_at_173c, ac_at_1740, ac_at_1742, ac_at_1746, ac_at_174a, ac_at_174c, ac_at_174e,
    ac_at_1752, ac_at_1754, ac_at_1756, ac_at_1758, ac_at_175c, ac_at_175e, ac_at_1760, ac_at_1762,
    ac_at_1766, ac_at_1770, ac_at_1772⟩

theorem acedp_v1 (B : Word) : aluEval .add (B + 0x3A50) (aluEval .add 0x2000 0xFFFFFED0) = acedpE B 0x1ED0 0 := by
  unfold acedpE acSlot; rw [ev_add, ev_add, BitVec.add_assoc]; rfl

theorem acedp_v2 (B : Word) : aluEval .add (B + 0x3A50) (aluEval .add 0x2000 0xFFFFFFD0) = acedpE B 0x1ED0 8 := by
  unfold acedpE acSlot; rw [ev_add, ev_add, BitVec.add_assoc]; rfl

theorem acedp_v3 (B : Word) : aluEval .add (B + 0x3A50) 0x350 = acedpE B 0x350 0 := by
  unfold acedpE acSlot; rw [ev_add, BitVec.add_assoc]; rfl

theorem acedp_v4 (B : Word) : aluEval .add (B + 0x3A50) 0x550 = acedpE B 0x350 16 := by
  unfold acedpE acSlot; rw [ev_add, BitVec.add_assoc]; rfl

theorem acedp_v5 (B : Word) : aluEval .add (aluEval .add (B + 0x3A50) 0x7FF) 0x91 = acedpE B 0x890 0 := by
  unfold acedpE acSlot; rw [ev_add, ev_add, BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem acedp_v6 (B : Word) : aluEval .add (aluEval .add (B + 0x3A50) 0x7FF) 0x191 = acedpE B 0x890 8 := by
  unfold acedpE acSlot; rw [ev_add, ev_add, BitVec.add_assoc, BitVec.add_assoc]; rfl

section
variable {X : AceCtx} {N : Word → BitVec 8} {fp : Word} {P : Machine → Prop} (S : AcedpS X N fp)
include S

/-- 0x1434: Fulcio subjects. -/
theorem acedp_c1 {fs : List FulcioKey} (h : SvArrayAt N (acSlot X.B 0x1ED0) 8 fs fun e k => AceEntryIn X.Bf fp N e k.subject k.publicKey 0x61 k.window)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B 0x1ED0 8 →
      distinct (fs.map (·.subject)) = true → WP bootMainClosure0Code AC (acedpQ X P) M 0x14D0 f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x1434 f := by
  have hz := R.rz
  refine WP.lui ac_at_1434 ?_; acedp_wo
  refine WP.aluImm ac_at_1436 ?_; acedp_wo
  refine WP.alu ac_at_143a ?_; acedp_wo
  refine WP.lui ac_at_143e ?_; acedp_wo
  refine WP.aluImm ac_at_1440 ?_; acedp_wo
  refine WP.alu ac_at_1444 ?_; acedp_wo
  refine acedp_runN S (xs := fs.map (·.subject))
    (acedp_arr (a := 0x1ED0) h (by decide) (.inr ⟨by decide, by decide⟩) (by decide)) acedp_i1
    ac_at_1448 ac_at_144a ac_at_144e ac_at_1452 rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (acedp_cmpN S ac_at_14bc ac_at_14c0 (by decide) (by decide) (acedp_name h)) (by simp only [List.length_map])
    kx (fun _ _ hM R => acedp_j1774 S hM R ac_at_14c8 (by decide)) hM (by acedp_hr) ?_ ?_
  · rsimp; rw [R.rsp]; exact acedp_v1 X.B
  · rsimp; rw [R.rsp]; exact acedp_v2 X.B

/-- 0x14D0: Fulcio keys. -/
theorem acedp_c2 {fs : List FulcioKey} (h : SvArrayAt N (acSlot X.B 0x1ED0) 8 fs fun e k => AceEntryIn X.Bf fp N e k.subject k.publicKey 0x61 k.window)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B 0x1ED0 8 →
      distinct (fs.map (·.publicKey)) = true → WP bootMainClosure0Code AC (acedpQ X P) M 0x1556 f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f)
    (h20 : f 20 = acedpE X.B 0x1ED0 8) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x14D0 f := by
  have hz := R.rz
  refine WP.lui ac_at_14d0 ?_; acedp_wo
  refine WP.aluImm ac_at_14d2 ?_; acedp_wo
  refine WP.alu ac_at_14d6 ?_; acedp_wo
  refine acedp_runK S (xs := fs.map (·.publicKey))
    (acedp_arr (a := 0x1ED0) h (by decide) (.inr ⟨by decide, by decide⟩) (by decide)) acedp_i2
    ac_at_14da ac_at_14dc ac_at_14e0 ac_at_14e4 rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (acedp_cmp97 S ac_at_1548 ac_at_154c (by decide) (by decide) (acedp_key h)) (by simp only [List.length_map])
    kx (fun _ _ hM R => acedp_j1774 S hM R ac_at_1554 (by decide)) hM (by acedp_hr) ?_ ?_
  · rsimp; rw [R.rsp]; exact acedp_v1 X.B
  · rsimp; exact h20

/-- 0x1556: log origins. -/
theorem acedp_c3 {ls : List LogKey} (h : SvArrayAt N (acSlot X.B 0x350) 16 ls fun e k => AceEntryIn X.Bf fp N e k.origin k.publicKey 32 k.window)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B 0x350 16 →
      distinct (ls.map (·.origin)) = true → WP bootMainClosure0Code AC (acedpQ X P) M 0x15E0 f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x1556 f := by
  have hz := R.rz
  refine WP.aluImm ac_at_1556 ?_; acedp_wo
  refine WP.aluImm ac_at_155a ?_; acedp_wo
  refine acedp_runN S (xs := ls.map (·.origin))
    (acedp_arr (a := 0x350) h (by decide) (.inl ⟨by decide, by decide⟩) (by decide)) acedp_i3
    ac_at_155e ac_at_1560 ac_at_1564 ac_at_1568 rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (acedp_cmpN S ac_at_15d2 ac_at_15d6 (by decide) (by decide) (acedp_name h)) (by simp only [List.length_map])
    kx (fun _ _ hM R => acedp_j1774 S hM R ac_at_15de (by decide)) hM (by acedp_hr) ?_ ?_
  · rsimp; rw [R.rsp]; exact acedp_v3 X.B
  · rsimp; rw [R.rsp]; exact acedp_v4 X.B

/-- 0x15E0: log keys. -/
theorem acedp_c4 {ls : List LogKey} (h : SvArrayAt N (acSlot X.B 0x350) 16 ls fun e k => AceEntryIn X.Bf fp N e k.origin k.publicKey 32 k.window)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B 0x350 16 →
      distinct (ls.map (·.publicKey)) = true → WP bootMainClosure0Code AC (acedpQ X P) M 0x1660 f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f)
    (h20 : f 20 = acedpE X.B 0x350 16) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x15E0 f := by
  have hz := R.rz
  refine WP.aluImm ac_at_15e0 ?_; acedp_wo
  refine acedp_runK S (xs := ls.map (·.publicKey))
    (acedp_arr (a := 0x350) h (by decide) (.inl ⟨by decide, by decide⟩) (by decide)) acedp_i4
    ac_at_15e4 ac_at_15e6 ac_at_15ea ac_at_15ee rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (acedp_cmp32 S ac_at_1652 ac_at_1656 (by decide) (by decide) (acedp_key h)) (by simp only [List.length_map])
    kx (fun _ _ hM R => acedp_j1774 S hM R ac_at_165e (by decide)) hM (by acedp_hr) ?_ ?_
  · rsimp; rw [R.rsp]; exact acedp_v3 X.B
  · rsimp; exact h20

/-- 0x1660: TSA signer ids. -/
theorem acedp_c5 {ts : List TsaKey} (h : SvArrayAt N (acSlot X.B 0x890) 8 ts fun e k => AceEntryIn X.Bf fp N e k.signerId k.publicKey 0x61 k.window)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B 0x890 8 →
      distinct (ts.map (·.signerId)) = true → WP bootMainClosure0Code AC (acedpQ X P) M 0x16F2 f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x1660 f := by
  have hz := R.rz
  refine WP.aluImm ac_at_1660 ?_; acedp_wo
  refine WP.aluImm ac_at_1664 ?_; acedp_wo
  refine WP.aluImm ac_at_1668 ?_; acedp_wo
  refine WP.aluImm ac_at_166c ?_; acedp_wo
  refine acedp_runN S (xs := ts.map (·.signerId))
    (acedp_arr (a := 0x890) h (by decide) (.inl ⟨by decide, by decide⟩) (by decide)) acedp_i5
    ac_at_1670 ac_at_1672 ac_at_1676 ac_at_167a rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (acedp_cmpN S ac_at_16e4 ac_at_16e8 (by decide) (by decide) (acedp_name h)) (by simp only [List.length_map])
    kx (fun _ _ hM R => acedp_j1774 S hM R ac_at_16f0 (by decide)) hM (by acedp_hr) ?_ ?_
  · rsimp; rw [R.rsp]; exact acedp_v5 X.B
  · rsimp; rw [R.rsp]; exact acedp_v6 X.B

/-- 0x16F2: TSA keys. A duplicate falls through to 0x1774. -/
theorem acedp_c6 {ts : List TsaKey} (h : SvArrayAt N (acSlot X.B 0x890) 8 ts fun e k => AceEntryIn X.Bf fp N e k.signerId k.publicKey 0x61 k.window)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B 0x890 8 →
      distinct (ts.map (·.publicKey)) = true → WP bootMainClosure0Code AC (acedpQ X P) M 0x1778 f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f)
    (h20 : f 20 = acedpE X.B 0x890 8) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x16F2 f := by
  have hz := R.rz
  refine WP.aluImm ac_at_16f2 ?_; acedp_wo
  refine WP.aluImm ac_at_16f6 ?_; acedp_wo
  refine acedp_runK S (xs := ts.map (·.publicKey))
    (acedp_arr (a := 0x890) h (by decide) (.inl ⟨by decide, by decide⟩) (by decide)) acedp_i6
    ac_at_16fa ac_at_16fc ac_at_1700 ac_at_1704 rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (acedp_cmp97 S ac_at_1768 ac_at_176c (by decide) (by decide) (acedp_key h)) (by simp only [List.length_map])
    kx (fun _ _ hM R => acedp_f1774 S hM R) hM (by acedp_hr) ?_ ?_
  · rsimp; rw [R.rsp]; exact acedp_v5 X.B
  · rsimp; exact h20

end

/-! ## The state at 0x1778 -/

theorem acedp_kept {B Bf x : Word} (F : Fr B 0x5A70) (h : AceKept B Bf x) : AcedpW B x := by
  rcases h with ⟨h1, -⟩ | ⟨k, hk, rfl⟩
  · exact acedp_W_sep h1
  · have hk' : k < 0x244 := by rcases hk with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    exact acedp_W_at (by rw [ace_slotN F (by omega)]; omega) (.inl hk')

section
variable {X : AceCtx} {n0 : Machine} {fp : Word} (S : AcedpS X n0.mem fp) {M : Word → BitVec 8}
  (hM : AcedpM X n0.mem M) {n : Machine} (hn : n.mem = M)
include S hM hn

theorem acedp_same {a l : Nat} (hp : (0x250 ≤ a ∧ a + l ≤ 0x1320) ∨ (0x132C ≤ a ∧ a + l ≤ 0x2020)) :
    AceSame n.mem (acSlot X.B a) n0.mem (acSlot X.B a) l := fun c hc => by
  have hk : a + c < 0x244 ∨ (0x250 ≤ a + c ∧ a + c < 0x1320) ∨ 0x132C ≤ a + c := by
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inr (.inl ⟨by omega, by omega⟩)
    · exact .inr (.inr (by omega))
  have hle : 0x3A50 + a + c ≤ 0x5A70 := by rcases hp with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  rw [hn]
  exact hM _ (acedp_W_at (by rw [ace_slot, S.ok.lay.fr.at _ hle]; omega) hk)

theorem acedp_keys {fs : List FulcioKey} {ls : List LogKey} {ts : List TsaKey}
    (KR : AceKeysRead X n0 fp fs ls ts) : AceKeysRead X n fp fs ls ts := by
  have hb : ∀ y, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → n.mem y = n0.mem y := fun y h1 h2 => by
    have := S.fhi
    rw [hn]
    exact hM y (acedp_W_sep (ace_bufOut S.ok.lay (by omega) (by unfold acBufLen; omega)))
  exact ⟨KR.root, ace_array_move KR.fulcio (acedp_same S hM hn (by decide)) hb,
    ace_array_move KR.logs (acedp_same S hM hn (by decide)) hb,
    ace_array_move KR.tsaKeys (acedp_same S hM hn (by decide)) hb⟩

theorem acedp_at {o o' : Nat} (At : AceAt X n0 o fp) {f : Fin 32 → Word} (R : AcedpR X f)
    (hpc : n.pc = AC + BitVec.ofNat 32 o') (hr : ∀ q, reg n q = f q) : AceAt X n o' fp := by
  have F := S.ok.lay.fr
  refine ⟨by rw [hn]; exact acedp_code S hM, ⟨hpc, rfl, fun _ => rfl⟩,
    acedp_inv S hM hn (by rw [hr]; exact R.rsp) (by rw [hr]; exact R.rgp) (by rw [hr]; exact R.rtp),
    ⟨?_, ?_, At.fr.lo, At.fr.hi⟩, ⟨fun x hx => ?_, fun q hq => ?_⟩, ?_⟩
  · rw [hn, acedp_ldS S hM (k := 0x1FDC) (.inr (.inr ⟨by decide, by decide⟩))]; exact At.fr.ptr
  · rw [hn, acedp_ldS S hM (k := 0x1FE0) (.inr (.inr ⟨by decide, by decide⟩))]; exact At.fr.len
  · rw [hn, hM x (acedp_kept F hx)]; exact At.keep.mem x hx
  · rw [hr]
    rcases List.mem_cons.mp hq with e | hq
    · rw [show q = 21 from Fin.ext e]; exact R.r21
    rcases List.mem_cons.mp hq with e | hq
    · rw [show q = 25 from Fin.ext e]; exact R.r25
    rcases List.mem_cons.mp hq with e | hq
    · rw [show q = 27 from Fin.ext e]; exact R.r27
    cases hq
  · have e : acSlot X.B 0x20 + 4 = acSlot X.B 0x24 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
    have h1 := acedp_ldS S hM (k := 0x20) (.inl (by decide))
    have h2 := acedp_ldS S hM (k := 0x24) (.inl (by decide))
    have := At.exp
    unfold AceExpiry aceU64 at this ⊢
    rw [e] at this
    rw [hn, e, h1, h2]
    exact this

end

/-- **The no-duplicates checks**, from 0x1434 to 0x1778. -/
theorem ace_dup : AceDupStage := by
  intro X O n fp fs ls ts At KR
  have hres : memLoad32 n.mem (acSlot X.B 0x40) = X.r := by
    rw [← O.pre.res]
    refine ace_load_eq fun j hj => At.keep.mem _ (.inr ⟨0x40 + j, .inl ⟨by omega, by omega⟩, ?_⟩)
    unfold acSlot; rw [add_ofNat_assoc, Nat.add_assoc]
  have S : AcedpS X n.mem fp := ⟨O, At.code, At.inv.saves, At.inv.out, hres, At.fr.hi⟩
  have R0 : AcedpR X (reg n) := ⟨rfl, At.inv.sp, At.inv.gp, At.inv.tp, At.keep.regs 21 (by decide),
    At.keep.regs 25 (by decide), At.keep.regs 27 (by decide)⟩
  refine acedp_stage At.code At.st ?_
  refine acedp_c1 S KR.fulcio ?_ (fun _ _ => rfl) R0
  intro M1 f1 hM1 R1 e1 d1
  refine acedp_c2 S KR.fulcio ?_ hM1 R1 e1
  intro M2 f2 hM2 R2 _ d2
  refine acedp_c3 S KR.logs ?_ hM2 R2
  intro M3 f3 hM3 R3 e3 d3
  refine acedp_c4 S KR.logs ?_ hM3 R3 e3
  intro M4 f4 hM4 R4 _ d4
  refine acedp_c5 S KR.tsaKeys ?_ hM4 R4
  intro M5 f5 hM5 R5 e5 d5
  refine acedp_c6 S KR.tsaKeys ?_ hM5 R5 e5
  intro M6 f6 hM6 R6 _ d6
  refine acedp_f1778 S hM6 R6 fun n' hpc hn hr =>
    ⟨acedp_at S hM6 hn At R6 hpc hr, acedp_keys S hM6 hn KR, ?_⟩
  unfold AceDistinct
  rw [d1, d2, d3, d4, d5, d6]; rfl

end C3.RV32.Ac
