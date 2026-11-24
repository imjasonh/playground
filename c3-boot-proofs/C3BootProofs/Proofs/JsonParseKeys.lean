import C3BootProofs.Proofs.JsonParseFrame

/-!
# `json::parse`: the key checks of a closed object

When `parse` closes an object, it reopens the object's bytes with `members`
and walks its members with `next_member`. In canonical mode, each key must
sort after the one before it (`keysCanon`). In strict mode, no key may equal
a later one (`keysStrict`), which an inner walk checks with `slice_ne`.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem slt0 (w : Word) : w.slt 0 = decide (2 ^ 31 ≤ w.toNat) := by
  rw [BitVec.slt]
  have h := BitVec.toInt_eq_toNat_cond w
  have h0 : (0 : Word).toInt = 0 := rfl
  rw [h0, h]
  have := w.isLt
  rcases Nat.lt_or_ge (2 * w.toNat) (2 ^ 32) with hc | hc
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

theorem sub_zext_slt (x y : BitVec 8) (hne : x ≠ y) :
    (aluEval .sub (x.zeroExtend 32) (y.zeroExtend 32)).slt 0 = decide (x.toNat < y.toNat) ∧
      aluEval .sub (x.zeroExtend 32) (y.zeroExtend 32) ≠ 0 := by
  have hx := x.isLt
  have hy := y.isLt
  have hn : x.toNat ≠ y.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  have e : (aluEval .sub (x.zeroExtend 32) (y.zeroExtend 32)).toNat = (2 ^ 32 - y.toNat + x.toNat) % 2 ^ 32 := by
    show ((x.zeroExtend 32) - (y.zeroExtend 32)).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 32)]
  refine ⟨?_, fun h => ?_⟩
  · rw [slt0, e]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · have := congrArg BitVec.toNat h
    rw [e] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega

/-- The sign `parse` reads after `memcmp` over the shorter length, and after
the length difference when those bytes are equal, is the key order. -/
theorem cmp_lt {M : Word → BitVec 8} {a b v : Word} {la lb : Nat} (hla : la < 2 ^ 31) (hlb : lb < 2 ^ 31)
    (hc : CmpRes M a b (min la lb) v) :
    (v ≠ 0 → v.slt 0 = bytesLt (memBytes M a la) (memBytes M b lb)) ∧
      (v = 0 → (BitVec.ofNat 32 la - BitVec.ofNat 32 lb).slt 0 = bytesLt (memBytes M a la) (memBytes M b lb)) := by
  rcases hc with ⟨hv, heq⟩ | ⟨i, hi, hpre, hne, hv⟩
  · refine ⟨fun h => absurd hv h, fun _ => ?_⟩
    rw [bytesLt_prefix _ _ fun j hj => ?_, memBytes_length, memBytes_length, slt0]
    · have e : (BitVec.ofNat 32 la - BitVec.ofNat 32 lb).toNat = (2 ^ 32 - lb + la) % 2 ^ 32 := by
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : la < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : lb < 2 ^ 32)]
      rw [e]
      exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · rw [memBytes_length, memBytes_length] at hj
      rw [memBytes_getD (by omega), memBytes_getD (by omega), heq j hj]
  · obtain ⟨h1, h2⟩ := sub_zext_slt _ _ hne
    rw [← hv] at h1 h2
    refine ⟨fun _ => ?_, fun h => absurd h h2⟩
    have hia : i < la := by omega
    have hib : i < lb := by omega
    rw [h1, bytesLt_first _ _ i (by rw [memBytes_length]; exact hia) (by rw [memBytes_length]; exact hib)
      (fun j hj => by rw [memBytes_getD (by omega), memBytes_getD (by omega), hpre j hj])
      (by rw [memBytes_getD hia, memBytes_getD hib]; exact fun h => hne (BitVec.eq_of_toNat_eq h)),
      memBytes_getD hia, memBytes_getD hib]

section
variable {M0 Mp M : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 : Fin 32 → Word}

theorem PaEnv.sepF (E : PaEnv M0 base s p out n g0 Mp F) {a : Word} {l : Nat} (h : Sep s 404 a l) {d w : Nat}
    (hdw : 164 + d + w ≤ 404) : Sep (F + BitVec.ofNat 32 d) w a l := by
  rw [← E.hF, add_ofNat_assoc]; exact h.sub (by omega)

theorem PaEnv.below (E : PaEnv M0 base s p out n g0 Mp F) {d w : Nat} (h : 164 + d + w ≤ 2 ^ 32) :
    Sep (F + BitVec.ofNat 32 d) w s 164 := (gt_below E.hF h).symm

theorem PaEnv.alF (E : PaEnv M0 base s p out n g0 Mp F) {d : Nat} (hd : d % 4 = 0) :
    (F + BitVec.ofNat 32 d).toNat % 4 = 0 := aligned_add E.halF hd

theorem PaEnv.qnz (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (h : st + l ≤ n) :
    (p + BitVec.ofNat 32 st).toNat ≠ 0 ∧ (p + BitVec.ofNat 32 st).toNat + l < 2 ^ 32 := by
  have := E.hpn; have := E.hp0
  rw [toNat_add_lt (by omega)]; exact ⟨by omega, by omega⟩

theorem PaEnv.sepq (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (h : st + l ≤ n) :
    Sep s 404 (p + BitVec.ofNat 32 st) l := E.sP.subR h

/-- The bytes of a slice of the document, read from memory that changed
only on the stack. -/
theorem PaEnv.slice (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (h : st + l ≤ n) (hO : Out M0 M s 404) :
    memBytes M (p + BitVec.ofNat 32 st) l = slice (memBytes M0 p n) st l := by
  rw [← memBytes_slice h, hO.bytes E.sP]

end

theorem MemRes.outF {M1 M2 : Word → BitVec 8} {F : Word} {cc : Nat}
    {r : Option (Option (Word × Nat × Word × Nat × Nat))} (h : MemRes M1 M2 (F + 0xA8) (F + BitVec.ofNat 32 cc) r)
    (hcc : 144 ≤ cc ∧ cc + 12 ≤ 168) : Out M1 M2 (F + BitVec.ofNat 32 144) 44 := fun x hx => by
  refine h.out ?_ ?_
  · have := sep_in hx (d := 24) (l := 20) (by decide)
    rwa [add_ofNat_assoc] at this
  · have := sep_in hx (d := cc - 144 + 8) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 144 + (cc - 144 + 8) = cc + 8 by omega, ← add_ofNat_assoc] at this

section
variable {M0 Mp M : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 f : Fin 32 → Word} {c : Bool}
  {stk : List (Bool × Nat)} {Q : Post}

/-- A call to `next_member` from `parse`, with `out` at `F + 0xA8` and the
cursor at `F + cc` over the `l` bytes of the document at `st`. -/
theorem pa_nm (E : PaEnv M0 base s p out n g0 Mp F) {off cc st l pos : Nat} {hi lo : Word}
    (h1 : fetchRel jsonParseCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel jsonParseCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = base + 0xFFFFF372 + 0xFFFFF438) (hev : (off + 8) % 2 = 0)
    (hcc : cc = 0x90 ∨ cc = 0x9C) (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c)
    (h0 : f a0 = F + 0xA8) (ha1 : f a1 = F + BitVec.ofNat 32 cc)
    (hmp : memLoad32 M (F + BitVec.ofNat 32 cc) = p + BitVec.ofNat 32 st)
    (hmn : memLoad32 M (F + BitVec.ofNat 32 cc + 4) = BitVec.ofNat 32 l)
    (hmq : memLoad32 M (F + BitVec.ofNat 32 cc + 8) = BitVec.ofNat 32 pos) (hsl : st + l ≤ n) (hpos : pos < 2 ^ 32)
    (k : ∀ m2 : Machine, FInv M0 Mp s F n stk m2.mem →
      (∃ M1, Out M M1 s 164 ∧ MemRes M1 m2.mem (F + 0xA8) (F + BitVec.ofNat 32 cc)
        (memRes (p + BitVec.ofNat 32 st) (nextMember (slice (memBytes M0 p n) st l) pos))) →
      (∀ d, d + 4 ≤ 16 ∨ 144 ≤ d ∧ d + 4 ≤ 168 ∧ (d + 4 ≤ cc + 8 ∨ cc + 12 ≤ d) →
        memLoad32 m2.mem (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d)) →
      WP jsonParseCode base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP jsonParseCode base Q M off f := by
  have hcd : 144 ≤ cc ∧ cc + 12 ≤ 168 ∧ cc % 4 = 0 := by rcases hcc with rfl | rfl <;> decide
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  obtain ⟨hq0, hqn⟩ := E.qnz hsl
  refine WP.callNextMember (tb := base + 0xFFFFF372 + 0xFFFFF438) (out := F + 0xA8) (c := F + BitVec.ofNat 32 cc)
    (s := s) (p := p + BitVec.ofNat 32 st) (n := l) (pos := pos) h1 h2 htgt
    (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) hev hc1.get.nm
    (by rw [gt_ad_ri]; exact hc1.get.ri) (by rw [gt_ad_ke]; exact hc1.get.ke) h0 ha1
    (by rw [hR.sp, E.hF]) E.hal (E.alF (d := 0xA8) (by decide)) (E.alF hcd.2.2) hmp hmn hmq (by omega) hpos hq0
    (by omega) ?_ ?_ (sep_low E.sep.get.nm (by decide)) (sep_low (E.sepq hsl) (by decide))
    (E.below (d := 0xA8) (w := 20) (by decide)) (E.below (d := cc) (w := 12) (by omega))
    (sep_offsets F (c := 0xA8) (n := 20) (d := cc) (k := 12) (Or.inr (by omega)) (by decide) (by omega))
    (E.sepF E.sep.get.nm (d := 0xA8) (w := 20) (by decide)) (E.sepF E.sep.get.nm (d := cc) (w := 12) (by omega))
    (sep_low E.sep.parse (by decide)) (E.sepF E.sep.parse (d := 0xA8) (w := 20) (by decide))
    (E.sepF E.sep.parse (d := cc) (w := 12) (by omega)) fun m2 hMR => ?_
  · rw [gt_ad_ri]; have := E.sep.get.ri.sub (c := 0) (l := 164) (by decide); rwa [add_ofNat_zero] at this
  · rw [gt_ad_ke]; exact sep_low E.sep.get.ke (by decide)
  rw [E.slice hsl hFI.1] at hMR
  obtain ⟨M1, hOa, hM⟩ := hMR
  have hOa' : Out M M1 (s + BitVec.ofNat 32 0) 164 := by rw [add_ofNat_zero]; exact hOa
  refine k m2 ((hFI.out E.hF hOa' (Or.inl (by decide))).outF E.hF (hM.outF ⟨hcd.1, hcd.2.1⟩)
    (Or.inr ⟨Nat.le_refl _, by decide⟩)) ⟨M1, hOa, hM⟩ fun d hd => ?_
  have hd168 : d + 4 ≤ 168 := by rcases hd with h | ⟨_, h, _⟩ <;> omega
  refine (memLoad32_congr fun j hj => ?_).trans (hOa.load32 (E.below (d := d) (w := 4) (by omega)).symm)
  rw [add_ofNat_assoc]
  refine hM.out (sep_offsets F (c := d + j) (n := 1) (d := 168) (k := 20) (Or.inl (by omega)) (by omega) (by decide))
    ?_
  show Sep _ 1 (F + BitVec.ofNat 32 cc + BitVec.ofNat 32 8) 4
  rw [add_ofNat_assoc]
  have hs : d + j + 1 ≤ cc + 8 ∨ cc + 8 + 4 ≤ d + j := by
    rcases hd with h | ⟨_, _, h | h⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  exact sep_offsets F hs (by omega) (by omega)

end

theorem gt_ad_nm (b : Word) : b + 0xFFFFF372 + 0xFFFFF438 + 0x1DE = b + 0xFFFFF372 + 0xFFFFF616 := gt_ad_ri _

theorem pa_bne_f {a b : Word} (h : branchTaken .bne a b = false) : a = b := by
  cases hab : (a == b) with
  | true => exact beq_iff_eq.mp hab
  | false => rw [show branchTaken .bne a b = !(a == b) from rfl, hab] at h; cases h

theorem pa_bne_t {a b : Word} (h : branchTaken .bne a b = true) : a ≠ b := fun e => by
  subst e
  rw [show branchTaken .bne a a = !(a == a) from rfl, show (a == a) = true from beq_iff_eq.mpr rfl] at h
  cases h

/-- The registers that the key checks may change. -/
abbrev kE : List (Fin 32) := jClob ++ [ra, 8, 9, 18, 26]

/-- The previous key in the canonical check: `s0` holds its address, or 0
before the first key, and `s2` its length. -/
def PrevW (q pq pl : Word) : Option (Nat × Nat) → Prop
  | none => pq = 0
  | some (a, b) => pq = q + BitVec.ofNat 32 a ∧ pl = BitVec.ofNat 32 b

theorem fr_a0 {h G g0 : Fin 32 → Word} {L : List (Fin 32)} (hh : ∀ x, x ≠ a0 → h x = G x)
    (hG : ∀ x, x ∉ L → G x = g0 x) (ha : a0 ∈ L) : ∀ x, x ∉ L → h x = g0 x := fun x hx => by
  rw [hh x (fun e => hx (by rw [e]; exact ha))]; exact hG x hx

theorem PRegs.a0 {h G g0 : Fin 32 → Word} {F p : Word} {n : Nat} {c : Bool} (hh : ∀ x, x ≠ a0 → h x = G x)
    (hR : PRegs G g0 F p n c) : PRegs h g0 F p n c :=
  ⟨by rw [hh _ (by decide)]; exact hR.sp, by rw [hh _ (by decide)]; exact hR.s3,
    by rw [hh _ (by decide)]; exact hR.s7, by rw [hh _ (by decide)]; exact hR.s8, fr_a0 hh hR.fr (by decide)⟩

theorem upd_ne0 {G : Fin 32 → Word} {r x : Fin 32} {v : Word} (hz : G 0 = 0) (hx : x ≠ r) : upd G r v x = G x := by
  rw [upd_app]
  rcases Nat.decEq x.val 0 with h | h
  · rw [if_neg h, if_neg hx]
  · rw [if_pos h, show x = 0 from Fin.ext h, hz]

section
variable {M : Word → BitVec 8} {base : Word} {Q : Post}

/-- `a2` gets the shorter key length at `0x1E0`. -/
theorem pa_1e0 {G : Fin 32 → Word} {x y : Nat} (hz : G 0 = 0) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (h9 : G 9 = BitVec.ofNat 32 x) (h18 : G 18 = BitVec.ofNat 32 y)
    (k : WP jsonParseCode base Q M 0x1E8 (upd G a2 (BitVec.ofNat 32 (min x y)))) :
    WP jsonParseCode base Q M 0x1E0 G := by
  refine WP.alu pa_at_1e0 ?_; wn
  rw [ev_mv hz, h9]
  refine WP.branch pa_at_1e2 (fun eb => ?_) (fun eb => ?_) <;> wn
  · (try rsimp at eb); rw [h9, h18, br_bltu hx hy] at eb
    rw [Nat.min_eq_left (Nat.le_of_lt (of_decide_eq_true eb))] at k; exact k
  · refine WP.alu pa_at_1e6 ?_; wn
    (try rsimp at eb); rw [h9, h18, br_bltu hx hy] at eb
    rw [Nat.min_eq_right (Nat.le_of_not_lt (of_decide_eq_false eb))] at k
    rw [ev0, h18]; exact k

/-- The order test at `0x1F4`: `memcmp`'s sign, or the length difference's
when the shorter key's bytes match. -/
theorem pa_1f4 {G : Fin 32 → Word} {b : Bool} (hz : G 0 = 0)
    (hb : (G a0 ≠ 0 → (G a0).slt 0 = b) ∧ (G a0 = 0 → (aluEval .sub (G 9) (G 18)).slt 0 = b))
    (kt : b = true → ∀ h : Fin 32 → Word, (∀ x, x ≠ a0 → h x = G x) → WP jsonParseCode base Q M 0x1BC h)
    (kf : b = false → ∀ h : Fin 32 → Word, (∀ x, x ≠ a0 → h x = G x) → WP jsonParseCode base Q M 0x1FE h) :
    WP jsonParseCode base Q M 0x1F4 G := by
  refine WP.branch pa_at_1f4 (fun eb => ?_) (fun eb => ?_) <;> wn
  · rw [hz] at eb
    have hne := pa_bne_t eb
    refine WP.branch pa_at_1fa (fun eb2 => ?_) (fun eb2 => ?_) <;> wn
    · rw [hz] at eb2; exact kt (by rw [← hb.1 hne]; exact eb2) G fun _ _ => rfl
    · rw [hz] at eb2; exact kf (by rw [← hb.1 hne]; exact eb2) G fun _ _ => rfl
  · rw [hz] at eb
    have he := pa_bne_f eb
    refine WP.alu pa_at_1f6 ?_; wn
    refine WP.branch pa_at_1fa (fun eb2 => ?_) (fun eb2 => ?_) <;> wn
    · exact kt (by rw [← hb.2 he]; exact eb2) _ fun x hx => upd_ne0 hz hx
    · exact kf (by rw [← hb.2 he]; exact eb2) _ fun x hx => upd_ne0 hz hx

end

section
variable {M0 Mp : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 : Fin 32 → Word}
  {stk : List (Bool × Nat)}

/-- The canonical key check at `0x1BC`, by fuel. The cursor at `F + 0x90`
walks the object `o`, the `l` bytes at `st`. `hok` continues at `0x252`
once every key sorts after the one before it. -/
theorem pa_canon (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (hsl : st + l ≤ n) {o : Bytes}
    (ho : slice (memBytes M0 p n) st l = o) {R : Except Nat (Nat × Nat)} {w8 : Word} {f0 : Fin 32 → Word}
    (hf0 : f0 0 = 0)
    (hok : ∀ (M' : Word → BitVec 8) (g : Fin 32 → Word), FInv M0 Mp s F n stk M' → memLoad32 M' (F + 8) = w8 →
      memLoad32 M' (F + 0xC) = out → PRegs g g0 F p n true → (∀ x, x ∉ kE → g x = f0 x) →
      WP jsonParseCode base (PPost M0 s p out g0 R) M' 0x252 g) :
    ∀ k prev pos (M : Word → BitVec 8) (f : Fin 32 → Word), l - pos < k → pos < 2 ^ 32 →
      PrevW (p + BitVec.ofNat 32 st) (f 8) (f 18) prev → (∀ a b, prev = some (a, b) → a + b ≤ l) →
      FInv M0 Mp s F n stk M → memLoad32 M (F + 0x90) = p + BitVec.ofNat 32 st →
      memLoad32 M (F + 0x94) = BitVec.ofNat 32 l → memLoad32 M (F + 0x98) = BitVec.ofNat 32 pos →
      memLoad32 M (F + 8) = w8 → memLoad32 M (F + 0xC) = out → PRegs f g0 F p n true →
      (∀ x, x ∉ kE → f x = f0 x) →
      WP jsonParseCode base (PPost M0 s p out g0
        (keysThen (keysCanon o k (prev.map fun x => slice o x.1 x.2) pos) R)) M 0x1BC f := by
  have hlen : o.length = l := by rw [← ho]; unfold slice; rw [memBytes_slice hsl, memBytes_length]
  obtain ⟨hq0, hqn⟩ := E.qnz hsl
  have hn := E.hn
  have kb : ∀ {M : Word → BitVec 8} {a b : Nat}, a + b ≤ l → Out M0 M s 404 →
      memBytes M (p + BitVec.ofNat 32 st + BitVec.ofNat 32 a) b = slice o a b := by
    intro M a b hab hO
    rw [← ho]; unfold slice
    rw [memBytes_slice hsl, memBytes_slice hab, hO.bytes ((E.sepq hsl).subR hab)]
  intro k
  induction k with
  | zero => intro _ _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
  intro prev pos M f hk hpos hpw hpb hFI hm90 hm94 hm98 hm8 hmC hR hkp
  have hfr := hR.fr
  refine WP.zero fun hz => ?_
  refine WP.alu pa_at_1bc ?_; wn
  refine WP.alu pa_at_1be ?_; wn
  refine WP.aluImm pa_at_1c0 ?_; wn
  refine WP.aluImm pa_at_1c2 ?_; wn
  refine pa_nm E (off := 0x1C4) (cc := 0x90) (st := st) (l := l) (pos := pos) (c := true) pa_at_1c4 pa_at_1c8
    (by simp only [BitVec.add_assoc]; rfl) (by decide) (Or.inl rfl) hFI (by pregs hR, E.z0)
    (by (try rsimp); rw [hR.sp, ev_add]) (by (try rsimp); rw [hR.sp, ev_add]; try rfl) hm90
    (by rw [BitVec.add_assoc]; exact hm94) (by rw [BitVec.add_assoc]; exact hm98) hsl hpos
    fun m2 hFI2 hMR hkeep => ?_
  rw [ho] at hMR
  obtain ⟨M1, hOa, hM⟩ := hMR
  generalize m2.mem = M2 at hFI2 hM hkeep
  have hC2 : memLoad32 M2 (F + 0xC) = out := (hkeep 0xC (Or.inl (by decide))).trans hmC
  have h82 : memLoad32 M2 (F + 8) = w8 := (hkeep 8 (Or.inl (by decide))).trans hm8
  have h902 : memLoad32 M2 (F + 0x90) = p + BitVec.ofNat 32 st :=
    (hkeep 0x90 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm90
  have h942 : memLoad32 M2 (F + 0x94) = BitVec.ofNat 32 l :=
    (hkeep 0x94 (Or.inr ⟨by decide, by decide, Or.inl (by decide)⟩)).trans hm94
  have hc2 : ParseCode M2 base := E.code.out hFI2.1 E.sep
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pa_at_1cc ?_; wn
  generalize hnm : nextMember o pos = r at hM
  rcases r with _ | _ | ⟨kp, kl, vp, vl, a⟩
  · obtain ⟨-, t1, t2⟩ := hM
    refine WP.branch pa_at_1d0 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.lbu pa_at_2bc ?_; wn
    have hk' : keysThen (keysCanon o (k + 1) (prev.map fun x => slice o x.1 x.2) pos) R = .error 0x20 := by
      simp only [keysCanon, hnm, keysThen]
    rw [hk']
    exact pa_2c0 E (by (try rsimp); exact hR.sp) hC2
      (by (try rsimp); rw [hR.sp, show F + 0xA9 = F + 0xA8 + 1 by rw [BitVec.add_assoc]; rfl, t2]; rfl)
      hFI2.1 hFI2.2.1 (by keepz E.z0)
  · obtain ⟨-, t1, t2⟩ := hM
    refine WP.branch pa_at_1d0 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw pa_at_1d2 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xAC) (by decide)) ?_; wn
    refine WP.branch pa_at_1d4 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb)
      rw [hR.sp, show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl, t2] at eb
      exact absurd eb (by decide)
    have hk' : keysThen (keysCanon o (k + 1) (prev.map fun x => slice o x.1 x.2) pos) R = R := by
      simp only [keysCanon, hnm, keysThen]
    rw [hk']
    exact hok M2 _ hFI2 h82 hC2 (by pregs hR, E.z0) (by keepz hf0)
  obtain ⟨-, t1, tkq, tkl, -, -, ta⟩ := hM
  obtain ⟨hpl, hpa, hkk, han, -⟩ := nextMember_lt hnm
  rw [hlen] at hpl hkk han
  have tkq' : memLoad32 M2 (F + 0xAC) = p + BitVec.ofNat 32 st + BitVec.ofNat 32 kp := by
    rw [show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl]; exact tkq
  have tkl' : memLoad32 M2 (F + 0xB0) = BitVec.ofNat 32 kl := by
    rw [show F + 0xB0 = F + 0xA8 + 8 by rw [BitVec.add_assoc]; rfl]; exact tkl
  have ta' : memLoad32 M2 (F + 0x98) = BitVec.ofNat 32 a := by
    rw [show F + 0x98 = F + BitVec.ofNat 32 0x90 + 8 by rw [BitVec.add_assoc]; rfl]; exact ta
  refine WP.branch pa_at_1d0 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_1d2 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xAC) (by decide)) ?_; wn
  refine WP.branch pa_at_1d4 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb)
    rw [hR.sp, tkq', nx_q0 hq0 (n := l + 1) (by omega) (by omega)] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_1d6 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xB0) (by decide)) ?_; wn
  refine WP.branch pa_at_1d8 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hR.s3] at eb; exact absurd eb (by decide)
  rcases prev with _ | ⟨pa, pb⟩
  · have h8 : f 8 = 0 := hpw
    refine WP.branch pa_at_1dc (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); (try simp only [ev0] at eb); rw [h8] at eb
      exact absurd eb (by decide)
    have hk' : keysCanon o (k + 1) none pos = keysCanon o k (some (slice o kp kl)) a := by
      simp only [keysCanon, hnm]
    rw [show (none : Option (Nat × Nat)).map (fun x => slice o x.1 x.2) = none from rfl, hk']
    exact ih (some (kp, kl)) a M2 _ (by omega) (by omega)
      ⟨by (try rsimp); rw [hR.sp]; exact tkq', by (try rsimp); rw [hR.sp]; exact tkl'⟩
      (fun a' b' h => by injection h with h; injection h with h1 h2; rw [← h1, ← h2]; exact hkk)
      hFI2 h902 h942 ta' h82 hC2 (by pregs hR, E.z0) (by keepz hf0)
  obtain ⟨h8, h18⟩ := hpw
  have hpab := hpb pa pb rfl
  refine WP.branch pa_at_1dc (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); (try simp only [ev0] at eb)
    rw [h8, nx_q0 hq0 (n := l + 1) (by omega) (by omega)] at eb; exact absurd eb (by decide)
  refine pa_1e0 (x := pb) (y := kl) (by rsimp) (by omega) (by omega)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h18) (by (try rsimp); rw [hR.sp]; exact tkl') ?_
  refine WP.alu pa_at_1e8 ?_; wn
  refine WP.alu pa_at_1ea ?_; wn
  refine WP.callMemcmp (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0xC93C)
    (p := p + BitVec.ofNat 32 st + BitVec.ofNat 32 pa) (q := p + BitVec.ofNat 32 st + BitVec.ofNat 32 kp)
    (l := min pb kl) pa_at_1ec pa_at_1f0 (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
    hc2.get.ri.mc (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h8)
    (by (try rsimp); (try simp only [ev0]); rw [hR.sp]; exact tkq') (by (try rsimp); try rfl) (by omega)
    fun m3 hcmp => ?_
  have hcl := cmp_lt (by omega) (by omega) hcmp
  rw [kb hpab hFI2.1, kb hkk hFI2.1] at hcl
  refine pa_1f4 (b := bytesLt (slice o pa pb) (slice o kp kl)) (by rsimp)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h18, hR.sp, tkl']; exact hcl) (fun hB h hh => ?_)
    (fun hB h hh => ?_)
  · have hk' : keysCanon o (k + 1) (some (slice o pa pb)) pos = keysCanon o k (some (slice o kp kl)) a := by
      simp only [keysCanon, hnm, hB, ↓reduceIte]
    rw [show (some (pa, pb)).map (fun x => slice o x.1 x.2) = some (slice o pa pb) from rfl, hk']
    exact ih (some (kp, kl)) a M2 h (by omega) (by omega)
      ⟨by rw [hh _ (by decide)]; (try rsimp); rw [hR.sp]; exact tkq',
        by rw [hh _ (by decide)]; (try rsimp); rw [hR.sp]; exact tkl'⟩
      (fun a' b' h => by injection h with h; injection h with h1 h2; rw [← h1, ← h2]; exact hkk)
      hFI2 h902 h942 ta' h82 hC2 (PRegs.a0 hh (by pregs hR, E.z0)) (fr_a0 hh (by keepz hf0) (by decide))
  · have hk' : keysCanon o (k + 1) (some (slice o pa pb)) pos = .error 0x20 := by
      simp only [keysCanon, hnm, hB, Bool.false_eq_true, ↓reduceIte]
    rw [show (some (pa, pb)).map (fun x => slice o x.1 x.2) = some (slice o pa pb) from rfl, hk']
    refine WP.jal pa_at_1fe (by decide) ?_; wn
    refine WP.aluImm pa_at_328 ?_; wn
    refine WP.jal pa_at_32c (by decide) ?_; wn
    exact pa_2c0 E (by (try rsimp); rw [hh _ (by decide)]; (try rsimp); exact hR.sp) hC2
      (by (try rsimp); rw [hh 0 (by decide)]; (try rsimp); (try simp only [ev0]); try decide) hFI2.1 hFI2.2.1
      (keepUpd0 E.z0 (by decide) (fr_a0 hh (by keepz E.z0) (by decide)))

end

end C3.RV32
