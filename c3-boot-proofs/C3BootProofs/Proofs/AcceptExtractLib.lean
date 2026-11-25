import C3BootProofs.Proofs.AcceptExtract

/-!
# Tools for the extract stage's sub-stages

`ace_mcpy` runs one call of `memcpy` from the closure into its own frame
and keeps `AcInv`. `AceSame` says that one region of memory equals another,
and `AceKeysIn.move` and its parts carry the key arrays along such a copy.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

local notation "MCS" => (BitVec.ofNat 32 memcpyStubAddress : Word)

/-! ## Frame arithmetic -/

theorem ace_sepB {B : Word} (F : Fr B 0x5A70) {c n k : Nat} (h : c + n ≤ k ∨ k + 1 ≤ c) (hc : c + n ≤ 0x5A70)
    (hk : k < 0x5A70) : Sep (B + BitVec.ofNat 32 c) n (B + BitVec.ofNat 32 k) 1 := by
  have hh := F.hi
  rcases h with h | h
  · exact sep_of_le (by rw [F.at c (by omega), F.at k (by omega)]; omega) (by rw [F.at k (by omega)]; omega)
  · exact (sep_of_le (by rw [F.at c (by omega), F.at k (by omega)]; omega)
      (by rw [F.at c (by omega)]; omega)).symm

theorem ace_sepB' {B : Word} (F : Fr B 0x5A70) {c n k l : Nat} (h : c + n ≤ k ∨ k + l ≤ c) (hc : c + n ≤ 0x5A70)
    (hk : k + l ≤ 0x5A70) : Sep (B + BitVec.ofNat 32 c) n (B + BitVec.ofNat 32 k) l := by
  have hh := F.hi
  rcases h with h | h
  · exact sep_of_le (by rw [F.at c (by omega), F.at k (by omega)]; omega) (by rw [F.at k (by omega)]; omega)
  · exact (sep_of_le (by rw [F.at c (by omega), F.at k (by omega)]; omega)
      (by rw [F.at c (by omega)]; omega)).symm

theorem ace_slotN {B : Word} (F : Fr B 0x5A70) {s : Nat} (h : 0x3A50 + s ≤ 0x5A70) :
    (acSlot B s).toNat = B.toNat + (0x3A50 + s) :=
  F.at _ h

theorem ace_slot (B : Word) (s i : Nat) : acSlot B s + BitVec.ofNat 32 i = B + BitVec.ofNat 32 (0x3A50 + s + i) :=
  add_ofNat_assoc B _ _

/-- The `N` bytes at `a'` in `M'` are the `N` bytes at `a` in `M`. -/
def AceSame (M' : Word → BitVec 8) (a' : Word) (M : Word → BitVec 8) (a : Word) (N : Nat) : Prop :=
  ∀ c, c < N → M' (a' + BitVec.ofNat 32 c) = M (a + BitVec.ofNat 32 c)

theorem ace_memBytes_ext {M M' : Word → BitVec 8} {a b : Word} {n : Nat}
    (h : ∀ i, i < n → M' (a + BitVec.ofNat 32 i) = M (b + BitVec.ofNat 32 i)) : memBytes M' a n = memBytes M b n := by
  unfold memBytes
  exact List.map_congr_left fun i hi => congrArg BitVec.toNat (h i (List.mem_range.mp hi))

/-! ## One call of `memcpy` -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A `memcpy` into the frame**: the `auipc` and `jalr` at `o` call
`memcpy` to copy `N` bytes from `src` to `sp + d`. It returns at `o + 8`
with the copy in memory outside its 16 bytes below `sp`, `AcInv` kept, and
every register it doesn't clobber kept. -/
theorem ace_mcpy {B Bf g t : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n : Machine} {o : Nat}
    {imm off src : Word} {d N : Nat} (F : Fr B 0x5A70) (C : CodeIn n.mem AC bootMainClosure0Code)
    (CS : CodeIn n.mem MCS memcpyStubCode) (CB : CodeIn n.mem (BitVec.ofNat 32 memcpyBodyAddress) memcpyBodyCode)
    (s : St n.mem AC n o (reg n)) (I : AcInv B Bf g t v M0 n) (ho : o % 2 = 0)
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra off, 4))
    (hb : AC + BitVec.ofNat 32 o + imm + off = MCS)
    (ha0 : reg n a0 = acSlot B d) (ha1 : reg n a1 = src) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hd : 0x3A50 + d + N ≤ 0x5A3C) (hsF : Sep src N (B + BitVec.ofNat 32 0x3A40) 16)
    (hds : Sep (acSlot B d) N src N) (hsw : src.toNat + N < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ AcInv B Bf g t v M0 n' ∧
      CodeIn n'.mem AC bootMainClosure0Code ∧
      (∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 → n'.mem x = copyBytes n.mem (acSlot B d) src N x) ∧
      reg n' ra = AC + BitVec.ofNat 32 (o + 8) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have rsp := I.sp
  have hh := F.hi
  obtain ⟨m1, e1, pc1, mem1, regs1⟩ := s.callRa C h1 h2 (cb := MCS) hb (by decide)
  have r1 : ∀ q : Fin 32, q ≠ ra → reg m1 q = reg n q := fun q hq => by
    rw [regs1]; unfold upd
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp only [h0, ↓reduceIte]; exact hz.symm
    · simp only [h0, hq, ↓reduceIte]
  have ra1 : reg m1 ra = AC + BitVec.ofNat 32 (o + 8) := by rw [regs1]; simp +decide only [upd, ↓reduceIte]
  have eF : reg m1 sp + 0xFFFFFFF0 = B + BitVec.ofNat 32 0x3A40 := by
    rw [r1 sp (by decide), rsp, BitVec.add_assoc]; rfl
  have eB : MCS + 8 = BitVec.ofNat 32 memcpyBodyAddress := by decide
  have hdN : (acSlot B d).toNat = B.toNat + (0x3A50 + d) := F.at _ (by omega)
  have hFN : (B + BitVec.ofNat 32 0x3A40).toNat = B.toNat + 0x3A40 := F.at _ (by omega)
  have hevr : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0 := even_at AC (by decide) _ (by omega)
  obtain ⟨m2, e2, pc2, sp2, a02, mem2, k2⟩ := memcpy_correct m1 MCS (AC + BitVec.ofNat 32 (o + 8)) (acSlot B d)
    src N (fun i hi => by show m1.mem _ = _; rw [mem1]; exact CS i hi) (by decide) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]) ra1
    (even_clear _ hevr)
    (by
      rw [eF, eB, mem1]
      exact ⟨CB, F.sepHi (c := 0x3A50 + d) (n := N) (by omega) (by decide) (by decide),
        F.sepHi (c := 0x3A40) (n := 16) (by omega) (by decide) (by decide),
        (sep_of_le (by rw [hFN, hdN]; omega) (by rw [hdN]; omega)).symm, hsF, hds,
        by rw [hFN]; have := F.al; omega, by rw [hFN]; omega, by rw [hdN]; omega, hsw⟩)
  rw [eF, mem1] at mem2
  have W : ∀ y, Sep (B + BitVec.ofNat 32 0x3A40) 16 y 1 → Sep (acSlot B d) N y 1 → m2.mem y = n.mem y :=
    fun y h1 h2 => by rw [mem2 y h1, copyBytes_sep h2 (Nat.le_refl _)]
  have K : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      reg m2 q = reg n q := fun q hq => by
    have hne : ∀ r : Fin 32, r.val ∈ [1, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] → q ≠ r := by
      intro r hr e; rw [e] at hq; simp at hq hr; omega
    by_cases hs : q = sp
    · subst hs; rw [sp2, r1 sp (by decide)]
    · rw [k2 q (hne a1 (by decide)) (hne a2 (by decide)) (hne a3 (by decide)) (hne a4 (by decide))
        (hne a5 (by decide)) (hne a6 (by decide)) (hne a7 (by decide)) (hne t0 (by decide)) (hne t1 (by decide))
        (hne 7 (by decide)) (hne 28 (by decide)) (hne 29 (by decide)) (hne 30 (by decide)) hs,
        r1 q (hne ra (by decide))]
  refine ⟨m2, e1.trans e2, ⟨pc2, rfl, fun _ => rfl⟩, ?_, ?_, mem2, ?_, K⟩
  · refine ⟨by rw [K sp (by decide)]; exact rsp, by rw [K 3 (by decide)]; exact I.gp,
      by rw [K 4 (by decide)]; exact I.tp, fun k hk => ?_, fun x hx hb => ?_⟩
    · rw [memLoad32_congr (M := n.mem) fun j hj => ?_]
      · exact I.saves k hk
      rw [add_ofNat_assoc]
      exact W _ (ace_sepB F (.inl (by omega)) (by omega) (by omega))
        (ace_sepB F (.inl (by omega)) (by omega) (by omega))
    · rw [W x (hx.subR (c := 0x3A40) (l := 16) (by omega)).symm (hx.subR (c := 0x3A50 + d) (l := N) (by omega)).symm]
      exact I.out x hx hb
  · intro i hi
    have hAC : 0x40000000 ≤ AC.toNat := by decide
    have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
    have h2' : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have h := BitVec.toNat_add AC (BitVec.ofNat 32 i)
    rw [h2', Nat.mod_eq_of_lt (by omega)] at h
    rw [W _ (F.hiOut (c := 0x3A40) (n := 16) (by omega) (by rw [h]; omega))
      (F.hiOut (c := 0x3A50 + d) (n := N) (by omega) (by rw [h]; omega))]
    exact C i hi
  · rw [k2 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ra1

/-- `AcInv` survives steps that keep memory and the registers it names. -/
theorem AcInv.same {B Bf g t : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n n' : Machine}
    (I : AcInv B Bf g t v M0 n) (hm : n'.mem = n.mem) (h2 : reg n' (2 : Fin 32) = reg n 2)
    (h3 : reg n' (3 : Fin 32) = reg n 3) (h4 : reg n' (4 : Fin 32) = reg n 4) : AcInv B Bf g t v M0 n' :=
  ⟨h2.trans I.sp, h3.trans I.gp, h4.trans I.tp, by rw [hm]; exact I.saves, by rw [hm]; exact I.out⟩

set_option maxRecDepth 100000 in
/-- **A block that sets `memcpy`'s arguments, then the call.** The block
writes only `a0`, `a1`, and `a2`, and doesn't touch memory. -/
theorem ace_bcpy {B Bf g t : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n : Machine} {o o1 : Nat}
    {is : List BInstr} {imm off src : Word} {d N : Nat} (F : Fr B 0x5A70)
    (C : CodeIn n.mem AC bootMainClosure0Code) (CS : CodeIn n.mem MCS memcpyStubCode)
    (CB : CodeIn n.mem (BitVec.ofNat 32 memcpyBodyAddress) memcpyBodyCode)
    (s : St n.mem AC n o (reg n)) (I : AcInv B Bf g t v M0 n)
    (he : blockEnd bootMainClosure0Code o is = some o1)
    (hok : BlockOk AC bootMainClosure0Code.length is (n.mem, reg n))
    (hm : (runBlock is (n.mem, reg n)).1 = n.mem)
    (hw : ∀ q : Fin 32, q.val ∉ [10, 11, 12] → q ∉ is.filterMap BInstr.dst) (ho : o1 % 2 = 0)
    (h1 : fetchRel bootMainClosure0Code o1 = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o1 + 4) = some (.jalr ra ra off, 4))
    (hb : AC + BitVec.ofNat 32 o1 + imm + off = MCS)
    (ha0 : (runBlock is (n.mem, reg n)).2 a0 = acSlot B d) (ha1 : (runBlock is (n.mem, reg n)).2 a1 = src)
    (ha2 : (runBlock is (n.mem, reg n)).2 a2 = BitVec.ofNat 32 N)
    (hd : 0x3A50 + d + N ≤ 0x5A3C) (hsF : Sep src N (B + BitVec.ofNat 32 0x3A40) 16)
    (hds : Sep (acSlot B d) N src N) (hsw : src.toNat + N < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o1 + 8) (reg n') ∧ AcInv B Bf g t v M0 n' ∧
      CodeIn n'.mem AC bootMainClosure0Code ∧
      (∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 → n'.mem x = copyBytes n.mem (acSlot B d) src N x) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := s.block is C he hok
  have M1 : n1.mem = n.mem := u1.mem.trans hm
  have r1 : ∀ q : Fin 32, q.val ∉ [10, 11, 12] → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q s.zero (hw q hq)]
  have I1 := I.same M1 (r1 sp (by decide)) (r1 3 (by decide)) (r1 4 (by decide))
  obtain ⟨n2, c2, s2, I2, C2, W2, _, K2⟩ := ace_mcpy F (by rw [M1]; exact C) (by rw [M1]; exact CS)
    (by rw [M1]; exact CB) ⟨u1.pc, rfl, fun _ => rfl⟩ I1 ho h1 h2 hb (by rw [u1.regs]; exact ha0)
    (by rw [u1.regs]; exact ha1) (by rw [u1.regs]; exact ha2) hd hsF hds hsw
  rw [M1] at W2
  refine ⟨n2, c1.trans c2, s2, I2, C2, W2, fun q hq => ?_⟩
  rw [K2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

/-- Bytes of `Buffers` lie outside the frame. -/
theorem ace_bufOut {B Bf y : Word} (lay : AceLayout B Bf) (hlo : Bf.toNat ≤ y.toNat)
    (hhi : y.toNat < Bf.toNat + acBufLen) : Sep y 1 B 0x5A70 := by
  have hw := lay.hi
  have e : y = Bf + BitVec.ofNat 32 (y.toNat - Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold acBufLen at hw
    omega
  rw [e]
  exact (lay.sep.subR (c := y.toNat - Bf.toNat) (l := 1) (by omega)).symm

/-! ## After a `memcpy` -/

section Cp

variable {B : Word} {M M' : Word → BitVec 8} {d N : Nat} {src : Word}

/-- Outside the frame, nothing changed. -/
theorem ace_cpO (W : ∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 → M' x = copyBytes M (acSlot B d) src N x)
    (hdN : 0x3A50 + d + N ≤ 0x5A70) {x : Word} (hx : Sep x 1 B 0x5A70) : M' x = M x := by
  rw [W x (hx.subR (c := 0x3A40) (l := 16) (by omega)).symm,
    copyBytes_sep (hx.subR (c := 0x3A50 + d) (l := N) (by omega)).symm (Nat.le_refl _)]

/-- In the frame, above `sp` and away from the copy, nothing changed. -/
theorem ace_cpR (F : Fr B 0x5A70)
    (W : ∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 → M' x = copyBytes M (acSlot B d) src N x)
    (hdN : 0x3A50 + d + N ≤ 0x5A70) {k l : Nat} (h1 : 0x3A50 ≤ k) (h2 : k + l ≤ 0x3A50 + d ∨ 0x3A50 + d + N ≤ k)
    (h3 : k + l ≤ 0x5A70) : AceSame M' (B + BitVec.ofNat 32 k) M (B + BitVec.ofNat 32 k) l := fun c hc => by
  rw [add_ofNat_assoc, W _ (ace_sepB F (.inl (by omega)) (by omega) (by omega)),
    copyBytes_sep (ace_sepB F (by omega) hdN (by omega)) (Nat.le_refl _)]

/-- The copy. -/
theorem ace_cpS (F : Fr B 0x5A70)
    (W : ∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 → M' x = copyBytes M (acSlot B d) src N x)
    (hdN : 0x3A50 + d + N ≤ 0x5A70) : AceSame M' (acSlot B d) M src N := fun c hc => by
  have h := W (acSlot B d + BitVec.ofNat 32 c) (by rw [ace_slot]; exact ace_sepB F (.inl (by omega)) (by omega) (by omega))
  rw [h, copyBytes_at hc (by omega)]

end Cp

/-! ## Copied regions -/

theorem AceSame.sub {M M' : Word → BitVec 8} {a a' : Word} {N k l : Nat} (h : AceSame M' a' M a N)
    (hkl : k + l ≤ N) : AceSame M' (a' + BitVec.ofNat 32 k) M (a + BitVec.ofNat 32 k) l := fun c hc => by
  rw [add_ofNat_assoc, add_ofNat_assoc]; exact h _ (by omega)

theorem AceSame.trans {M M' M'' : Word → BitVec 8} {a a' a'' : Word} {N : Nat} (h1 : AceSame M'' a'' M' a' N)
    (h2 : AceSame M' a' M a N) : AceSame M'' a'' M a N := fun c hc => by rw [h1 c hc, h2 c hc]

theorem AceSame.load {M M' : Word → BitVec 8} {a a' : Word} {N k : Nat} (h : AceSame M' a' M a N)
    (hk : k + 4 ≤ N) : memLoad32 M' (a' + BitVec.ofNat 32 k) = memLoad32 M (a + BitVec.ofNat 32 k) := by
  have h' := h.sub (k := k) (l := 4) hk
  exact memLoad32_congr2 fun j hj => h' j hj

/-- A copy with `memcpy`'s result. -/
theorem ace_same_copy {M M' : Word → BitVec 8} {dst src : Word} {N : Nat} (hN : N < 2 ^ 32)
    (h : ∀ c, c < N → M' (dst + BitVec.ofNat 32 c) = copyBytes M dst src N (dst + BitVec.ofNat 32 c)) :
    AceSame M' dst M src N := fun c hc => by rw [h c hc, copyBytes_at hc hN]

theorem AceEntryIn.move {Bf fp : Word} {M M' : Word → BitVec 8} {e e' : Word} {name key : Bytes} {n : Nat}
    {w : Window} (h : AceEntryIn Bf fp M e name key n w) (hs : AceSame M' e' M e 0x20)
    (hb : ∀ y, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M' y = M y) :
    AceEntryIn Bf fp M' e' name key n w := by
  have l0 : memLoad32 M' e' = memLoad32 M e := by
    have := hs.load (k := 0) (by decide); rwa [add_ofNat_zero, add_ofNat_zero] at this
  have lk : ∀ k, k + 4 ≤ 0x20 → memLoad32 M' (e' + BitVec.ofNat 32 k) = memLoad32 M (e + BitVec.ofNat 32 k) :=
    fun k hk => hs.load hk
  have bytes : ∀ {p : Word} {l : Nat} {bs : Bytes}, AceBytesIn Bf fp M p l bs → AceBytesIn Bf fp M' p l bs :=
    fun {p l bs} ⟨h1, h2, h3⟩ => ⟨h1, h2, by
      rw [← h3]
      refine ace_memBytes_ext fun i hi => hb _ ?_ ?_ <;>
        · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          have := fp.isLt
          rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
          omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [l0, show e' + 4 = e' + BitVec.ofNat 32 4 from rfl, lk 4 (by decide)]; exact bytes h.name
  · obtain ⟨a, b, c⟩ := h.notBefore
    refine ⟨a, ?_, ?_⟩
    · rw [show e' + 8 = e' + BitVec.ofNat 32 8 from rfl, lk 8 (by decide)]; exact b
    · rw [show e' + 8 + 4 = e' + BitVec.ofNat 32 12 by rw [BitVec.add_assoc]; rfl, lk 12 (by decide),
        ← show e + 8 + 4 = e + BitVec.ofNat 32 12 by rw [BitVec.add_assoc]; rfl]; exact c
  · obtain ⟨a, b, c⟩ := h.notAfter
    refine ⟨a, ?_, ?_⟩
    · rw [show e' + 0x10 = e' + BitVec.ofNat 32 0x10 from rfl, lk 0x10 (by decide)]; exact b
    · rw [show e' + 0x10 + 4 = e' + BitVec.ofNat 32 0x14 by rw [BitVec.add_assoc]; rfl, lk 0x14 (by decide),
        ← show e + 0x10 + 4 = e + BitVec.ofNat 32 0x14 by rw [BitVec.add_assoc]; rfl]; exact c
  · rw [show e' + 0x18 = e' + BitVec.ofNat 32 0x18 from rfl, lk 0x18 (by decide)]; exact bytes h.key

theorem ace_array_move {α : Type} {Bf fp : Word} {M M' : Word → BitVec 8} {a a' : Word} {cap : Nat}
    {l : List α} {nm ky : α → Bytes} {n : Nat} {win : α → Window}
    (h : SvArrayAt M a cap l fun e k => AceEntryIn Bf fp M e (nm k) (ky k) n (win k))
    (hs : AceSame M' a' M a (0x20 * cap))
    (hb : ∀ y, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M' y = M y) :
    SvArrayAt M' a' cap l fun e k => AceEntryIn Bf fp M' e (nm k) (ky k) n (win k) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun i hi => (h2 i hi).move (hs.sub (by omega)) hb, fun i hl hc => ?_⟩
  have := hs.load (k := 0x20 * i) (by omega)
  rw [this]; exact h3 i hl hc

/-- **The key arrays, copied.** -/
theorem AceKeysIn.move {Bf fp : Word} {M M' : Word → BitVec 8} {k k' : Word} {fs : List FulcioKey}
    {ls : List LogKey} {ts : List TsaKey} (h : AceKeysIn Bf fp M k fs ls ts) (hs : AceSame M' k' M k 0x400)
    (hb : ∀ y, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M' y = M y) :
    AceKeysIn Bf fp M' k' fs ls ts := by
  obtain ⟨hf, hl, ht⟩ := h
  have e1 : ∀ x : Word, x + 0x100 = x + BitVec.ofNat 32 0x100 := fun _ => rfl
  have e3 : ∀ x : Word, x + 0x300 = x + BitVec.ofNat 32 0x300 := fun _ => rfl
  refine ⟨ace_array_move hf (hs.sub (k := 0) (l := 0x100) (by decide) |> fun h => by
      rwa [add_ofNat_zero, add_ofNat_zero] at h) hb, ?_, ?_⟩
  · unfold AceLogsAt at hl ⊢
    rw [e1] at hl ⊢
    exact ace_array_move hl (hs.sub (k := 0x100) (l := 0x200) (by decide)) hb
  · unfold AceTsasAt at ht ⊢
    rw [e3] at ht ⊢
    exact ace_array_move ht (hs.sub (k := 0x300) (l := 0x100) (by decide)) hb

end C3.RV32.Ac
