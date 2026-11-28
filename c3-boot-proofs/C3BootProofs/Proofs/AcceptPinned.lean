import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.AcceptPinnedErr
import C3BootProofs.Proofs.TufRoleKeysRead
import C3BootProofs.Models.TufLinkKeys

/-!
# `boot_main`'s first closure: the pinned root

From 0x4E4 to 0x584 the closure reads the root that the bootloader pins,
the first root of `verifyTuf`'s chain. It calls `tuf::parse_root` on the
0x1318 bytes at `acpPin`, rejects at 0x7D6 with the error byte when that
fails, and otherwise calls `RoleKeys::read` for the `root` and `targets`
roles of the root's `signed` value and `tuf::expires` on it.

`AcPinnedPost` is where `verifyTuf`'s fold over the slot's roots starts:
the root's version in the frame at `sp + 0x20`, the keys and threshold of
its `root` and `targets` roles at `sp + 0x1320` and `sp + 0xDD0`, and its
expiry at `sp + 0x1310`, each as the spec computes it.
-/

namespace C3.RV32.Ac

open C3.Image C3.Json C3.RV32.P3

/-- The pinned root's address. -/
abbrev acpPin : Word := BitVec.ofNat 32 (img% roWindowAddress + 0x1309)

/-- The address of the role name `targets`. -/
abbrev acpTgt : Word := BitVec.ofNat 32 (img% roWindowAddress + 0x20)

/-- What the stage reads besides the stack: the callees' code and data,
the pinned root, and the role name `targets`. -/
structure AcPinnedEnv (pinned : Bytes) (M : Word → BitVec 8) : Prop where
  pr : PrCode M
  rk : RkCode M
  tex : TexCode M
  pin : memBytes M acpPin 0x1318 = pinned
  tgt : memBytes M acpTgt 7 = ascii!"targets"

/-- At 0x4E4: `s1` is `sp + 0x1310`, and the result pointer is at
`sp + 0x40`. -/
def AcPinnedPre (B r : Word) (n : Machine) : Prop :=
  reg n (9 : Fin 32) = acSlot B 0x1310 ∧ memLoad32 n.mem (acSlot B 0x40) = r

/-- A role's keys as `RoleKeys::read` leaves them at `a`: the threshold
and the keys when the spec's `roleKeys` finds them, and otherwise the tag
0xFE and a `TufError` code. -/
def AcpKeys (M : Word → BitVec 8) (a : Word) : Option (Nat × List (Bytes × Option TufKey)) → Prop
  | some (t, ks) => RkAt M a t (ks.map C3.Json.rkTag)
  | none => M a = 0xFE ∧ (M (a + 1)).toNat < 0x27

/-- An expiry as `tuf::expires` leaves it at `a`: the tag 0 and the time
when the spec's `expires` finds one, and otherwise the tag 1 and a
`TufError` code. -/
def AcpExp (M : Word → BitVec 8) (a : Word) : Option Nat → Prop
  | some t => M a = 0 ∧ memLoad32 M (a + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
      memLoad32 M (a + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)
  | none => M a = 1 ∧ (M (a + 1)).toNat < 0x27

/-- At 0x584, for memory `M` and registers `f` at 0x4E4: no byte changed
outside the callees' stacks below `sp`, the frame words at `sp + 0x1C` to
`sp + 0x2C`, the results at `sp + 0xDD0` to `sp + 0x1860`, and
`parse_root`'s result at `sp + 0x1870`. The registers that later stages
read kept their values. `sp + 0x1C` holds the word from `sp + 0x34C`,
`sp + 0x2C` holds 0, and `sp + 0x28` and `s6` hold the first two bytes of
the `root` keys. The pinned root parses, its version is the 64-bit word
with high half at `sp + 0x20` and low half at `sp + 0x24`, and its `root`
keys, `targets` keys, and expiry are at `sp + 0x1320`, `sp + 0xDD0`, and
`sp + 0x1310`. -/
def AcPinnedPost (pinned : Bytes) (B : Word) (M : Word → BitVec 8) (f : Fin 32 → Word) (n : Machine) : Prop :=
  (∀ x, Sep x 1 B 0x3A50 → Sep x 1 (acSlot B 0x1C) 0x14 → Sep x 1 (acSlot B 0xDD0) 0xA90 →
    Sep x 1 (acSlot B 0x1870) 0x18 → n.mem x = M x) ∧
  (∀ q : Fin 32, q.val ∈ [20, 21, 23, 24, 25, 27] → reg n q = f q) ∧
  memLoad32 n.mem (acSlot B 0x1C) = memLoad32 M (acSlot B 0x34C) ∧
  memLoad32 n.mem (acSlot B 0x2C) = 0 ∧
  memLoad32 n.mem (acSlot B 0x28) = (n.mem (acSlot B 0x1320)).zeroExtend 32 ∧
  reg n (22 : Fin 32) = (n.mem (acSlot B 0x1321)).zeroExtend 32 ∧
  ∃ first, parseTufRoot pinned = some first ∧
    (memLoad32 n.mem (acSlot B 0x20)).toNat * 2 ^ 32 + (memLoad32 n.mem (acSlot B 0x24)).toNat = first.version ∧
    AcpKeys n.mem (acSlot B 0x1320) (roleKeys first.md.signed (ascii!"root")) ∧
    AcpKeys n.mem (acSlot B 0xDD0) (roleKeys first.md.signed (ascii!"targets")) ∧
    AcpExp n.mem (acSlot B 0x1310) (expires first.md)

section
variable {B : Word}

theorem acp_ev (a b : Word) : aluEval .add a b = a + b := rfl

/-- Equal words that are sums of `B` and literals. -/
macro "acp_eq" : tactic => `(tactic| (
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, acp_ev, acSlot, BitVec.reduceToNat]
    omega))

/-- Bounds and alignment of sums of `B` and literals, with the bounds on
`B` in the context. -/
macro "acp_al" : tactic => `(tactic| (
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, acp_ev, acSlot, BitVec.reduceToNat]
    omega))

theorem acp_shr {a b : Word} {n k l : Nat} (h : Sep a n b k) (hl : l ≤ k) : Sep a n b l :=
  fun i hi j hj => h i hi j (by omega)

theorem acp_in {x : Word} {c n c' n' : Nat} (h : Sep x 1 (B + BitVec.ofNat 32 c) n) (h1 : c ≤ c')
    (h2 : c' + n' ≤ c + n) : Sep x 1 (B + BitVec.ofNat 32 c') n' := by
  have := h.subR (c := c' - c) (l := n') (by omega)
  rwa [add_ofNat_assoc, Nat.add_sub_of_le h1] at this

/-- The bytes that only the closure's earlier stages own: below `sp`, the
frame words at `sp + 0x1C`, the results at `sp + 0xDD0`, and `parse_root`'s
result at `sp + 0x1870`. -/
def AcpW (B x : Word) : Prop :=
  Sep x 1 B 0x3A50 ∧ Sep x 1 (B + BitVec.ofNat 32 0x3A6C) 0x14 ∧ Sep x 1 (B + BitVec.ofNat 32 0x4820) 0xA90 ∧
    Sep x 1 (B + BitVec.ofNat 32 0x52C0) 0x18

theorem acp_Wout {x : Word} (hx : Sep x 1 B 0x5A70) : AcpW B x :=
  ⟨acp_shr hx (by decide), hx.subR (by decide), hx.subR (by decide), hx.subR (by decide)⟩

theorem acp_Woff {c : Nat} (h0 : 0x3A50 ≤ c) (h1 : c < 0x3A6C ∨ 0x3A80 ≤ c) (h2 : c < 0x4820 ∨ 0x52B0 ≤ c)
    (h3 : c < 0x52C0 ∨ 0x52D8 ≤ c) (h4 : c < 2 ^ 31) : AcpW B (B + BitVec.ofNat 32 c) := by
  refine ⟨?_, sep_offsets B (by omega) (by omega) (by omega), sep_offsets B (by omega) (by omega) (by omega),
    sep_offsets B (by omega) (by omega) (by omega)⟩
  have := sep_offsets B (c := c) (n := 1) (d := 0) (k := 0x3A50) (Or.inr (by omega)) (by omega) (by decide)
  rwa [add_ofNat_zero] at this

theorem acp_ld {M M' : Word → BitVec 8} {c : Nat}
    (h : ∀ j, j < 4 → M' (B + BitVec.ofNat 32 (c + j)) = M (B + BitVec.ofNat 32 (c + j))) :
    memLoad32 M' (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h j hj

/-- A store to the frame word at `B + d` keeps the byte at `B + c`. -/
theorem acp_stO {M : Word → BitVec 8} {v : Word} {d : Nat} (hd : d + 4 ≤ 2 ^ 31) {c : Nat}
    (h : c + 1 ≤ d ∨ d + 4 ≤ c) (hc : c < 2 ^ 31) :
    memStore32 M (B + BitVec.ofNat 32 d) v (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  memStore32_get_sep (sep_offsets B (Or.symm h) (by omega) (by omega))

/-- A callee with its stack at `B + cs` and its result at `B + co` keeps the
byte at `B + c`. -/
theorem acp_frO {M M' : Word → BitVec 8} {cs K co L : Nat}
    (hfr : ∀ x, Sep x 1 (B + BitVec.ofNat 32 cs) K → Sep x 1 (B + BitVec.ofNat 32 co) L → M' x = M x)
    (h3 : co + L ≤ 2 ^ 31) {c : Nat} (h1 : cs + K ≤ c) (h2 : c + 1 ≤ co ∨ co + L ≤ c) (h4 : c < 2 ^ 31) :
    M' (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  hfr _ (sep_offsets B (Or.inr h1) (by omega) (by omega)) (sep_offsets B h2 (by omega) (by omega))

theorem acp_stW {M Mk : Word → BitVec 8} {v : Word} {c : Nat} (hW : ∀ x, AcpW B x → Mk x = M x)
    (h1 : 0x3A6C ≤ c) (h2 : c + 4 ≤ 0x3A80) : ∀ x, AcpW B x → memStore32 Mk (B + BitVec.ofNat 32 c) v x = M x :=
  fun x hx => (memStore32_get_sep (acp_in hx.2.1 (c' := c) (n' := 4) h1 (by omega)).symm).trans (hW x hx)

theorem acp_frW {M Mk M' : Word → BitVec 8} {cs K co L : Nat}
    (hfr : ∀ x, Sep x 1 (B + BitVec.ofNat 32 cs) K → Sep x 1 (B + BitVec.ofNat 32 co) L → M' x = Mk x)
    (hcs : cs + K ≤ 0x3A50) (hco : 0x4820 ≤ co ∧ co + L ≤ 0x52B0 ∨ 0x52C0 ≤ co ∧ co + L ≤ 0x52D8)
    (hW : ∀ x, AcpW B x → Mk x = M x) : ∀ x, AcpW B x → M' x = M x := fun x hx => by
  refine (hfr x (hx.1.subR (by omega)) ?_).trans (hW x hx)
  rcases hco with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact acp_in hx.2.2.1 h1 (by omega)
  · exact acp_in hx.2.2.2 h1 (by omega)

theorem acp_ro {a : Word} {n : Nat} (h : Sep a n (BitVec.ofNat 32 (img% roWindowAddress)) 0x2625) {c l : Nat}
    (hcl : c + l ≤ 0x2625) : Sep a n (BitVec.ofNat 32 (roWindowAddress + c)) l := by
  have := h.subR hcl
  rwa [BitVec.ofNat_add_ofNat] at this

theorem acp_pinSep {a : Word} {n : Nat} (h : Sep a n (BitVec.ofNat 32 (img% roWindowAddress)) 0x2625) {gp l : Nat}
    (hcl : gp + l ≤ 0x131C) : Sep a n (acpPin + BitVec.ofNat 32 gp) l := by
  rw [show acpPin = BitVec.ofNat 32 (img% roWindowAddress) + BitVec.ofNat 32 0x1309 from by decide, add_ofNat_assoc]
  exact h.subR (by omega)

theorem acp_pinAt {gp : Nat} (h : gp ≤ 0x1318) : (acpPin + BitVec.ofNat 32 gp).toNat = 0x3fcc5309 + gp := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem acp_ne0 {gp : Nat} (h : gp ≤ 0x1318) : branchTaken .beq (acpPin + BitVec.ofNat 32 gp) 0 = false := by
  rw [show acpPin + BitVec.ofNat 32 gp = BitVec.ofNat 32 (0x3fcc5309 + gp) from by
    apply BitVec.eq_of_toNat_eq; rw [acp_pinAt h, BitVec.toNat_ofNat]; omega, br_beq0 (by omega)]
  exact decide_eq_false (by omega)

theorem acp_zext {b : BitVec 8} (h : b.toNat < 0x27) : ((b.zeroExtend 32) &&& 0xFF).toNat < 0x27 := by
  rw [BitVec.toNat_and]
  refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
  rw [BitVec.toNat_setWidth]; omega

theorem acp_prFrame {M M' : Word → BitVec 8} {s out : Word} {r : Except Nat (Word × Nat × Word × Nat × Nat)}
    (h : PrRes M M' s out r) : ∀ x, Sep x 1 s 596 → Sep x 1 out 24 → M' x = M x := by
  rcases r with _ | ⟨_, _, _, _, _⟩
  · exact h.1
  · exact h.1

theorem acp_rkFrame {M M' : Word → BitVec 8} {s out : Word} {r : Except Nat (Nat × List RkEntry)}
    (h : RkRes M M' s out r) : ∀ x, Sep x 1 s 3056 → Sep x 1 out 0x540 → M' x = M x := by
  rcases r with _ | ⟨_, _⟩
  · exact h.1
  · exact h.1

theorem acp_texFrame {M M' : Word → BitVec 8} {s out : Word} {r : Except Nat Nat}
    (h : TexRes M M' s out r) : ∀ x, Sep x 1 s 308 → Sep x 1 out 16 → M' x = M x := by
  rcases r with _ | _
  · exact h.1
  · exact h.1

/-- `RoleKeys::read`'s result on a root's `signed` bytes, carried to later
memory `M''` that keeps its 0x540 bytes, is the spec's `roleKeys`. -/
theorem acp_keys {M M' M'' : Word → BitVec 8} {s a : Word} {d role : Bytes} {dj : Json} (hj : JVal true d dj)
    (h : RkRes M M' s a (rkModel d role)) (hb : ∀ o < 0x540, M'' (a + BitVec.ofNat 32 o) = M' (a + BitVec.ofNat 32 o)) :
    AcpKeys M'' a (roleKeys dj role) := by
  have hs := rkModel_spec (role := role) hj
  have b0 : M'' a = M' a := by simpa only [add_ofNat_zero] using hb 0 (by decide)
  have b1 : M'' (a + 1) = M' (a + 1) := hb 1 (by decide)
  rcases he : rkModel d role with e | ⟨t, es⟩ <;> rw [he] at h hs
  · obtain ⟨-, h1, h2⟩ := h
    have hn : roleKeys dj role = none := by
      cases hr : roleKeys dj role with
      | none => rfl
      | some _ => rw [hr] at hs; cases hs
    rw [hn]
    refine ⟨b0.trans h1, ?_⟩
    rw [b1, h2, BitVec.toNat_ofNat]
    have := acp_rkModel d role e he
    omega
  · obtain ⟨-, h1⟩ := h
    cases hr : roleKeys dj role with
    | none => rw [hr] at hs; cases hs
    | some x =>
      rw [hr] at hs
      obtain ⟨t', ks⟩ := x
      simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact RkB.congr h1 hb

/-- `tuf::expires`'s result on a root's `signed` bytes, carried to later
memory that keeps its 16 bytes, is the spec's `expires`. -/
theorem acp_exp {M M' M'' : Word → BitVec 8} {s a : Word} {d : Bytes} {md : Meta} (hj : JVal true d md.signed)
    (h : TexRes M M' s a (expiresModel d)) (hb : ∀ o < 16, M'' (a + BitVec.ofNat 32 o) = M' (a + BitVec.ofNat 32 o)) :
    AcpExp M'' a (expires md) := by
  have hs := expiresModel_spec hj
  have b0 : M'' a = M' a := by simpa only [add_ofNat_zero] using hb 0 (by decide)
  have b1 : M'' (a + 1) = M' (a + 1) := hb 1 (by decide)
  have w : ∀ k : Nat, k + 4 ≤ 16 → memLoad32 M'' (a + BitVec.ofNat 32 k) = memLoad32 M' (a + BitVec.ofNat 32 k) :=
    fun k hk => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hb _ (by omega)
  rcases he : expiresModel d with e | t <;> rw [he] at h hs
  · obtain ⟨-, h1, h2⟩ := h
    rw [← hs]
    refine ⟨b0.trans h1, ?_⟩
    rw [b1, h2, BitVec.toNat_ofNat]
    have := acp_expiresModel d e he
    omega
  · obtain ⟨-, h1, h2, h3⟩ := h
    rw [← hs]
    exact ⟨b0.trans h1, (w 8 (by decide)).trans h2, (w 0xC (by decide)).trans h3⟩

end

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

theorem acp_lw {rd rs1 : Fin 32} {o l v : Word} (h : fetchRel code off = some (.load .lw rd rs1 o, l))
    (ha : (f rs1 + o).toNat % 4 = 0) (hv : memLoad32 M (f rs1 + o) = v)
    (k : WP code base Q M (off + l.toNat) (upd f rd v)) : WP code base Q M off f :=
  WP.lw h ha (by rw [hv]; exact k)

theorem acp_sw {rs1 rs2 : Fin 32} {o l A V : Word} (h : fetchRel code off = some (.store .sw rs1 rs2 o, l))
    (hA : f rs1 + o = A) (hV : f rs2 = V) (ha : A.toNat % 4 = 0) (hs : Sep A 4 base code.length)
    (k : WP code base Q (memStore32 M A V) (off + l.toNat) f) : WP code base Q M off f :=
  WP.sw h (by rw [hA]; exact ha) (by rw [hA]; exact hs) (by rw [hA, hV]; exact k)

theorem acp_lbu {rd rs1 : Fin 32} {o l A : Word} (h : fetchRel code off = some (.load .lbu rd rs1 o, l))
    (hA : f rs1 + o = A) (k : WP code base Q M (off + l.toNat) (upd f rd ((M A).zeroExtend 32))) :
    WP code base Q M off f :=
  WP.lbu h (by rw [hA]; exact k)

end

section
variable {Q : Post} {M : Word → BitVec 8} {f : Fin 32 → Word} {off : Nat} {hi lo out s p : Word} {n : Nat}

theorem acp_done (h : Q (AC + BitVec.ofNat 32 off) M f) : WP bootMainClosure0Code AC Q M off f :=
  fun _ _ m st => ⟨m, .refl m, by rw [st.pc, st.mem, show reg m = f from funext st.regs]; exact h⟩

/-- A call to `parse_root` from the closure. -/
theorem acp_callPr (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (AC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = TPR)
    (hret : (AC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = AC + BitVec.ofNat 32 (off + 8))
    (hc : PrCode M) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = s + BitVec.ofNat 32 596) (hal : s.toNat % 4 = 0) (hsw : s.toNat + 596 ≤ 0x40000000)
    (hro : Sep s 596 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (halo : out.toNat % 4 = 0)
    (how : out.toNat + 24 ≤ 0x40000000) (hso : Sep out 24 s 596) (hn : n < 2 ^ 31) (hp0 : p.toNat ≠ 0)
    (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep s 596 p n)
    (hcode : ∀ M', PrRes M M' s out (prRes p (prModel (memBytes M p n))) → CodeIn M' AC bootMainClosure0Code)
    (k : ∀ m2 : Machine, PrRes M m2.mem s out (prRes p (prModel (memBytes M p n))) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  refine WP.callGen (tb := TPR) (cl := jClob)
    (P := fun m2 => PrRes M m2.mem s out (prRes p (prModel (memBytes M p n))))
    h1 h2 htgt (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP _ => hcode _ hP) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := tufParseRoot_correct m1 (retAddr := AC + BitVec.ofNat 32 (off + 8))
    (by rw [hmem1]; exact hc) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact hsp) (by rw [hreg1]; rsimp) hret
    hal hsw hro halo how hso hn hp0 hpn hSp
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

/-- A call to `RoleKeys::read` from the closure. -/
theorem acp_callRk {RP : Word} {RN : Nat} (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (AC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = TRK)
    (hret : (AC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = AC + BitVec.ofNat 32 (off + 8))
    (hc : RkCode M) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = RP)
    (ha4 : f a4 = BitVec.ofNat 32 RN)
    (hsp : f sp = s + BitVec.ofNat 32 3056) (hal : s.toNat % 4 = 0) (hsw : s.toNat + 3056 ≤ 0x40000000)
    (hro : Sep s 3056 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (halo : out.toNat % 4 = 0)
    (how : out.toNat + 0x540 ≤ 0x40000000) (hso : Sep out 0x540 s 3056) (hn : n < 2 ^ 31) (hp0 : p.toNat ≠ 0)
    (hpn : p.toNat + n ≤ 0x40000000) (hSp : Sep s 3056 p n) (hRN : RN < 2 ^ 32) (hRS : Sep s 3056 RP RN)
    (hcode : ∀ M', RkRes M M' s out (rkModel (memBytes M p n) (memBytes M RP RN)) → CodeIn M' AC bootMainClosure0Code)
    (k : ∀ m2 : Machine, RkRes M m2.mem s out (rkModel (memBytes M p n) (memBytes M RP RN)) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  refine WP.callGen (tb := TRK) (cl := jClob)
    (P := fun m2 => RkRes M m2.mem s out (rkModel (memBytes M p n) (memBytes M RP RN)))
    h1 h2 htgt (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP _ => hcode _ hP) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := tufRoleKeysRead_correct m1 (retAddr := AC + BitVec.ofNat 32 (off + 8))
    (by rw [hmem1]; exact hc) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact ha3) (by rw [hreg1]; rsimp; exact ha4)
    (by rw [hreg1]; rsimp; exact hsp) (by rw [hreg1]; rsimp) hret
    hal hsw hro halo how hso hn hp0 hpn hSp hRN hRS
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

/-- A call to `tuf::expires` from the closure. -/
theorem acp_callTex (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (AC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = TEX)
    (hret : (AC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = AC + BitVec.ofNat 32 (off + 8))
    (hc : TexCode M) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = s + BitVec.ofNat 32 308) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hsw : s.toNat + 308 ≤ 0x40000000) (hro : Sep s 308 (BitVec.ofNat 32 roWindowAddress) roWindowSize)
    (hp0 : p.toNat ≠ 0) (hpw : p.toNat + n + 4 ≤ 0x40000000) (hSp : Sep s 308 p (n + 4))
    (how : out.toNat + 16 ≤ 0x40000000) (hso : Sep out 16 s 308)
    (hcode : ∀ M', TexRes M M' s out (expiresModel (memBytes M p n)) → CodeIn M' AC bootMainClosure0Code)
    (k : ∀ m2 : Machine, TexRes M m2.mem s out (expiresModel (memBytes M p n)) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  refine WP.callGen (tb := TEX) (cl := jClob)
    (P := fun m2 => TexRes M m2.mem s out (expiresModel (memBytes M p n)))
    h1 h2 htgt (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP _ => hcode _ hP) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := tufExpires_correct m1 (retAddr := AC + BitVec.ofNat 32 (off + 8))
    (by rw [hmem1]; exact hc) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact hsp) (by rw [hreg1]; rsimp) hret
    hal halo hsw hro hp0 hpw hSp how hso
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

end

/-- What the stage leaves at an exit or at 0x584, for every machine in the
final state. -/
abbrev AcpQ (pinned : Bytes) (B Bf g t r : Word) (v : Nat → Word) (M0 M : Word → BitVec 8)
    (f : Fin 32 → Word) : Post :=
  fun pc M' f' => ∀ n' : Machine, n'.pc = pc → n'.mem = M' → (∀ q, reg n' q = f' q) →
    AcInv B Bf g t v M0 n' ∧ (AcFail B r n' ∨ (n'.pc = AC + BitVec.ofNat 32 0x584 ∧ AcPinnedPost pinned B M f n'))

theorem acp_inv {n' : Machine} {B Bf g t : Word} {v : Nat → Word} {M0 M : Word → BitVec 8}
    (hsv : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k)
    (hout : ∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x)
    (hW : ∀ x, AcpW B x → n'.mem x = M x) (hsp : reg n' sp = B + 0x3A50) (h3 : reg n' (3 : Fin 32) = g)
    (h4 : reg n' (4 : Fin 32) = t) : AcInv B Bf g t v M0 n' :=
  ⟨hsp, h3, h4, fun k hk => by
    rw [← hsv k hk]
    exact acp_ld fun j hj => hW _ (acp_Woff (by omega) (by omega) (by omega) (by omega) (by omega)),
   fun x hx hb => (hW x (acp_Wout hx)).trans (hout x hx hb)⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The walk from 0x4E4. -/
theorem acp_wp {pinned : Bytes} {B Bf g t r : Word} {v : Nat → Word} {M0 M : Word → BitVec 8}
    {f : Fin 32 → Word}
    (hE : ∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcPinnedEnv pinned M)
    (C : CodeIn M AC bootMainClosure0Code) (hBa : B.toNat % 16 = 0) (hBh : B.toNat + 0x5A70 ≤ 0x3FCE0000)
    (hro : Sep B 0x5A70 (BitVec.ofNat 32 (img% roWindowAddress)) 0x2625)
    (hsp : f sp = B + 0x3A50) (h3 : f 3 = g) (h4 : f 4 = t)
    (hsv : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k)
    (hout : ∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x)
    (h9 : f 9 = B + BitVec.ofNat 32 0x4D60) (hr : memLoad32 M (B + BitVec.ofNat 32 0x3A90) = r) :
    WP bootMainClosure0Code AC (AcpQ pinned B Bf g t r v M0 M f) M 0x4E4 f := by
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have sAC : Sep B 0x5A70 AC bootMainClosure0Code.length := sep_of_le (by omega) hACl
  have codeOf : ∀ M', (∀ x, AcpW B x → M' x = M x) → CodeIn M' AC bootMainClosure0Code :=
    fun M' hW i hi => by rw [hW _ (acp_Wout (sep_pt sAC hi))]; exact C i hi
  have envOf : ∀ M', (∀ x, AcpW B x → M' x = M x) → AcPinnedEnv pinned M' :=
    fun M' hW => hE M' fun x hx hb => (hW x (acp_Wout hx)).trans (hout x hx hb)
  have hroS : ∀ c K, c + K ≤ 0x5A70 → Sep (B + BitVec.ofNat 32 c) K (BitVec.ofNat 32 roWindowAddress) roWindowSize :=
    fun c K h => acp_shr (hro.sub (c := c) (l := K) h) (by decide)
  refine WP.zero fun hz => ?_
  have a1c : f sp + 0x1C = B + BitVec.ofNat 32 0x3A6C := by rw [hsp]; acp_eq
  have a34c : f sp + 0x34C = B + BitVec.ofNat 32 0x3D9C := by rw [hsp]; acp_eq
  refine WP.lw ac_at_4e4 (by rw [a34c]; acp_al) ?_; wn
  refine WP.sw ac_at_4e8 (by rsimp; rw [a1c]; acp_al) (lowSep (by rsimp; rw [a1c]; acp_al) hAC hACl) ?_
  wn
  rw [a1c, a34c]
  generalize hM1 : memStore32 M (B + BitVec.ofNat 32 0x3A6C) (memLoad32 M (B + BitVec.ofNat 32 0x3D9C)) = M1
  have hW1 : ∀ x, AcpW B x → M1 x = M x := by
    rw [← hM1]; exact acp_stW (fun _ _ => rfl) (by decide) (by decide)
  refine WP.lui ac_at_4ea ?_; wn
  refine WP.aluImm ac_at_4ee ?_; wn
  refine WP.lui ac_at_4f2 ?_; wn
  refine WP.aluImm ac_at_4f4 ?_; wn
  refine WP.lui ac_at_4f8 ?_; wn
  refine WP.aluImm ac_at_4fa ?_; wn
  refine WP.alu ac_at_4fe ?_; wn
  have E1 := envOf _ hW1
  refine acp_callPr (out := B + BitVec.ofNat 32 0x52C0) (s := B + BitVec.ofNat 32 0x37FC) (p := acpPin)
    (n := 0x1318) ac_at_500 ac_at_504 (by decide) (by decide) E1.pr (by rsimp; rw [hsp]; acp_eq)
    (by rsimp) (by rsimp) (by rsimp; rw [hsp]; acp_eq) (by acp_al) (by acp_al)
    (hroS _ _ (by decide)) (by acp_al) (by acp_al) (sep_offsets B (Or.inr (by decide)) (by decide) (by decide))
    (by decide) (by decide) (by decide)
    (by simpa only [add_ofNat_zero] using acp_pinSep (hro.sub (c := 0x37FC) (l := 596) (by decide)) (gp := 0) (l := 0x1318) (by decide))
    (fun M' hP => codeOf M' (acp_frW (acp_prFrame hP) (by decide) (Or.inr ⟨by decide, by decide⟩) hW1)) ?_
  intro m2 hP2
  wn
  rw [E1.pin] at hP2
  have pl : pinned.length = 0x1318 := by rw [← E1.pin, memBytes_length]
  have hsl : ∀ M', (∀ x, AcpW B x → M' x = M x) → ∀ gp gl, gp + gl ≤ 0x1318 →
      memBytes M' (acpPin + BitVec.ofNat 32 gp) gl = slice pinned gp gl := fun M' hW gp gl h => by
    rw [← memBytes_drop_take (n := 0x1318) h, (envOf M' hW).pin]
  have hfrP := acp_prFrame hP2
  have hW2 := acp_frW hfrP (by decide) (Or.inr ⟨by decide, by decide⟩) hW1
  have pP : ∀ c, 0x3A50 ≤ c → (c + 1 ≤ 0x52C0 ∨ 0x52D8 ≤ c) → c < 2 ^ 31 →
      m2.mem (B + BitVec.ofNat 32 c) = M1 (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 h3 => acp_frO hfrP (by decide) (by omega) h2 h3
  have hs := prModel_spec pinned
  rcases hpm : prModel pinned with e | ⟨gp, gl, q2, l2, ver⟩ <;> rw [hpm] at hP2 hs <;>
    simp only [prRes, Except.map] at hP2
  · obtain ⟨-, hl0, he2⟩ := hP2
    refine acp_lw (v := 0) ac_at_508 (by rsimp; rw [h9]; acp_al)
      (by rsimp; exact (congrArg (memLoad32 m2.mem) (by rw [h9]; acp_eq)).trans hl0) ?_; wn
    refine WP.branch ac_at_50c (fun _ => ?_) (fun hb => ?_)
    · wn
      refine acp_lbu (A := B + BitVec.ofNat 32 0x52C0 + 4) ac_at_782 (by rsimp; rw [h9]; acp_eq) ?_; wn
      refine WP.jal ac_at_786 (by decide) ?_; wn
      refine acp_done fun n' hpc hmem hreg => ⟨acp_inv hsv hout (by rw [hmem]; exact hW2)
        (by rw [hreg]; rsimp; exact hsp) (by rw [hreg]; rsimp; exact h3) (by rw [hreg]; rsimp; exact h4),
        Or.inl (Or.inr (Or.inr (Or.inl ⟨hpc, ?_, ?_⟩)))⟩
      · rw [hmem]
        exact (acp_ld fun j hj => hW2 _ (acp_Woff (by omega) (by omega) (by omega) (by omega) (by omega))).trans hr
      · rw [hreg]; rsimp
        rw [he2]
        exact acp_zext (by rw [BitVec.toNat_ofNat]; have := acp_prModel pinned e hpm; omega)
    · rsimp at hb
  · obtain ⟨first, sj, hpr, hver, ⟨hgl, hsg⟩, -, -⟩ := hs
    obtain ⟨-, hq1, hl1, -, -, hv2⟩ := hP2
    have hgl' : gp + gl ≤ 0x1318 := by rw [← pl]; exact hgl
    refine acp_lw (v := acpPin + BitVec.ofNat 32 gp) ac_at_508 (by rsimp; rw [h9]; acp_al)
      (by rsimp; exact (congrArg (memLoad32 m2.mem) (by rw [h9]; acp_eq)).trans hq1) ?_; wn
    refine WP.branch ac_at_50c (fun hb => ?_) (fun _ => ?_)
    · rsimp at hb; rw [acp_ne0 (by omega)] at hb; cases hb
    wn
    refine WP.lui ac_at_510 ?_; wn
    refine WP.aluImm ac_at_512 ?_; wn
    refine WP.alu ac_at_516 ?_; wn
    refine WP.aluImm ac_at_51a ?_; wn
    refine acp_lw (v := BitVec.ofNat 32 gl) ac_at_51e (by rsimp; rw [hsp]; acp_al)
      (by rsimp; exact (congrArg (memLoad32 m2.mem) (by rw [hsp]; acp_eq)).trans hl1) ?_; wn
    refine acp_lw (v := memLoad32 m2.mem (B + BitVec.ofNat 32 0x52D0)) ac_at_520 (by rsimp; rw [hsp]; acp_al)
      (by rsimp; exact congrArg (memLoad32 m2.mem) (by rw [hsp]; acp_eq)) ?_; wn
    refine acp_sw (A := B + BitVec.ofNat 32 0x3A74) (V := memLoad32 m2.mem (B + BitVec.ofNat 32 0x52D0))
      ac_at_522 (by rsimp; rw [hsp]; acp_eq) (by rsimp) (by acp_al) (lowSep (by acp_al) hAC hACl) ?_
    generalize hMa : memStore32 m2.mem (B + BitVec.ofNat 32 0x3A74) (memLoad32 m2.mem (B + BitVec.ofNat 32 0x52D0)) = Ma
    wn
    have hWa : ∀ x, AcpW B x → Ma x = M x := by rw [← hMa]; exact acp_stW hW2 (by decide) (by decide)
    refine acp_lw (v := memLoad32 Ma (B + BitVec.ofNat 32 0x52D4)) ac_at_524 (by rsimp; rw [hsp]; acp_al)
      (by rsimp; exact congrArg (memLoad32 Ma) (by rw [hsp]; acp_eq)) ?_; wn
    refine acp_sw (A := B + BitVec.ofNat 32 0x3A70) (V := memLoad32 Ma (B + BitVec.ofNat 32 0x52D4))
      ac_at_526 (by rsimp; rw [hsp]; acp_eq) (by rsimp) (by acp_al) (lowSep (by acp_al) hAC hACl) ?_
    generalize hMb : memStore32 Ma (B + BitVec.ofNat 32 0x3A70) (memLoad32 Ma (B + BitVec.ofNat 32 0x52D4)) = Mb
    wn
    have hWb : ∀ x, AcpW B x → Mb x = M x := by rw [← hMb]; exact acp_stW hWa (by decide) (by decide)
    refine WP.lui ac_at_528 ?_; wn
    refine WP.aluImm ac_at_52c ?_; wn
    refine WP.lui ac_at_530 ?_; wn
    refine WP.aluImm ac_at_532 ?_; wn
    refine WP.alu ac_at_536 ?_; wn
    refine WP.aluImm ac_at_538 ?_; wn
    refine WP.alu ac_at_53a ?_; wn
    refine WP.alu ac_at_53c ?_; wn
    have Eb := envOf _ hWb
    have hP0 : (acpPin + BitVec.ofNat 32 gp).toNat ≠ 0 := by rw [acp_pinAt (by omega)]; omega
    have hPN : (acpPin + BitVec.ofNat 32 gp).toNat + gl ≤ 0x40000000 := by rw [acp_pinAt (by omega)]; omega
    refine acp_callRk (out := B + BitVec.ofNat 32 0x4D70) (s := B + BitVec.ofNat 32 0x2E60)
      (p := acpPin + BitVec.ofNat 32 gp) (n := gl) (RP := TPR_KR) (RN := 4)
      ac_at_53e ac_at_542 (by decide) (by decide) Eb.rk (by rsimp; rw [hsp]; acp_eq)
      (by rsimp; exact BitVec.zero_add _) (by rsimp; exact BitVec.zero_add _) (by rsimp) (by rsimp)
      (by rsimp; rw [hsp]; acp_eq) (by acp_al) (by acp_al) (hroS _ _ (by decide)) (by acp_al) (by acp_al)
      (sep_offsets B (Or.inr (by decide)) (by decide) (by decide)) (by omega) hP0 hPN
      (acp_pinSep (hro.sub (c := 0x2E60) (l := 3056) (by decide)) (by omega)) (by decide)
      (acp_ro (hro.sub (c := 0x2E60) (l := 3056) (by decide)) (c := 0x76E) (l := 4) (by decide))
      (fun M' hR => codeOf M' (acp_frW (acp_rkFrame hR) (by decide) (Or.inl ⟨by decide, by decide⟩) hWb)) ?_
    intro m3 hR1
    wn
    rw [hsl Mb hWb gp gl hgl', tpr_kr Eb.pr] at hR1
    have hfr3 := acp_rkFrame hR1
    have hW3 := acp_frW hfr3 (by decide) (Or.inl ⟨by decide, by decide⟩) hWb
    have pR1 : ∀ c, 0x3A50 ≤ c → (c + 1 ≤ 0x4D70 ∨ 0x52B0 ≤ c) → c < 2 ^ 31 →
        m3.mem (B + BitVec.ofNat 32 c) = Mb (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 h3 => acp_frO hfr3 (by decide) (by omega) h2 h3
    refine WP.lui ac_at_546 ?_; wn
    refine WP.aluImm ac_at_54a ?_; wn
    refine WP.aluImm ac_at_54e ?_; wn
    refine WP.aluImm ac_at_552 ?_; wn
    refine WP.aluImm ac_at_556 ?_; wn
    refine WP.alu ac_at_558 ?_; wn
    refine WP.alu ac_at_55a ?_; wn
    have E3 := envOf _ hW3
    refine acp_callRk (out := B + BitVec.ofNat 32 0x4820) (s := B + BitVec.ofNat 32 0x2E60)
      (p := acpPin + BitVec.ofNat 32 gp) (n := gl) (RP := acpTgt) (RN := 7)
      ac_at_55c ac_at_560 (by decide) (by decide) E3.rk (by rsimp; rw [hsp]; acp_eq)
      (by rsimp; exact BitVec.zero_add _) (by rsimp; exact BitVec.zero_add _) (by rsimp) (by rsimp)
      (by rsimp; rw [hsp]; acp_eq) (by acp_al) (by acp_al) (hroS _ _ (by decide)) (by acp_al) (by acp_al)
      (sep_offsets B (Or.inr (by decide)) (by decide) (by decide)) (by omega) hP0 hPN
      (acp_pinSep (hro.sub (c := 0x2E60) (l := 3056) (by decide)) (by omega)) (by decide)
      (acp_ro (hro.sub (c := 0x2E60) (l := 3056) (by decide)) (c := 0x20) (l := 7) (by decide))
      (fun M' hR => codeOf M' (acp_frW (acp_rkFrame hR) (by decide) (Or.inl ⟨by decide, by decide⟩) hW3)) ?_
    intro m4 hR2
    wn
    rw [hsl m3.mem hW3 gp gl hgl', E3.tgt] at hR2
    have hfr4 := acp_rkFrame hR2
    have hW4 := acp_frW hfr4 (by decide) (Or.inl ⟨by decide, by decide⟩) hW3
    have pR2 : ∀ c, 0x3A50 ≤ c → (c + 1 ≤ 0x4820 ∨ 0x4D60 ≤ c) → c < 2 ^ 31 →
        m4.mem (B + BitVec.ofNat 32 c) = m3.mem (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 h3 => acp_frO hfr4 (by decide) (by omega) h2 h3
    refine WP.lui ac_at_564 ?_; wn
    refine WP.aluImm ac_at_566 ?_; wn
    refine WP.alu ac_at_56a ?_; wn
    refine WP.alu ac_at_56c ?_; wn
    refine WP.alu ac_at_56e ?_; wn
    have E4 := envOf _ hW4
    refine acp_callTex (out := B + BitVec.ofNat 32 0x4D60) (s := B + BitVec.ofNat 32 0x391C)
      (p := acpPin + BitVec.ofNat 32 gp) (n := gl)
      ac_at_570 ac_at_574 (by decide) (by decide) E4.tex (by rsimp; rw [hsp]; acp_eq)
      (by rsimp; exact BitVec.zero_add _) (by rsimp; exact BitVec.zero_add _)
      (by rsimp; rw [hsp]; acp_eq) (by acp_al) (by acp_al) (by acp_al) (hroS _ _ (by decide)) hP0
      (by rw [acp_pinAt (by omega)]; omega)
      (acp_pinSep (hro.sub (c := 0x391C) (l := 308) (by decide)) (by omega)) (by acp_al)
      (sep_offsets B (Or.inr (by decide)) (by decide) (by decide))
      (fun M' hT => codeOf M' (acp_frW (acp_texFrame hT) (by decide) (Or.inl ⟨by decide, by decide⟩) hW4)) ?_
    intro m5 hT
    wn
    rw [hsl m4.mem hW4 gp gl hgl'] at hT
    have hfr5 := acp_texFrame hT
    have hW5 := acp_frW hfr5 (by decide) (Or.inl ⟨by decide, by decide⟩) hW4
    have pT : ∀ c, 0x3A50 ≤ c → (c + 1 ≤ 0x4D60 ∨ 0x4D70 ≤ c) → c < 2 ^ 31 →
        m5.mem (B + BitVec.ofNat 32 c) = m4.mem (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 h3 => acp_frO hfr5 (by decide) (by omega) h2 h3
    refine acp_sw (A := B + BitVec.ofNat 32 0x3A7C) (V := 0) ac_at_578 (by rsimp; rw [hsp]; acp_eq) (by rsimp)
      (by acp_al) (lowSep (by acp_al) hAC hACl) ?_
    generalize hM6 : memStore32 m5.mem (B + BitVec.ofNat 32 0x3A7C) 0 = M6
    wn
    have hW6 : ∀ x, AcpW B x → M6 x = M x := by rw [← hM6]; exact acp_stW hW5 (by decide) (by decide)
    refine acp_lbu (A := B + BitVec.ofNat 32 0x4D70) ac_at_57a (by rsimp; rw [hsp]; acp_eq) ?_; wn
    refine acp_sw (A := B + BitVec.ofNat 32 0x3A78) (V := (M6 (B + BitVec.ofNat 32 0x4D70)).zeroExtend 32)
      ac_at_57e (by rsimp; rw [hsp]; acp_eq) (by rsimp) (by acp_al) (lowSep (by acp_al) hAC hACl) ?_
    generalize hM7 : memStore32 M6 (B + BitVec.ofNat 32 0x3A78) ((M6 (B + BitVec.ofNat 32 0x4D70)).zeroExtend 32) = M7
    wn
    have hW7 : ∀ x, AcpW B x → M7 x = M x := by rw [← hM7]; exact acp_stW hW6 (by decide) (by decide)
    refine acp_lbu (A := B + BitVec.ofNat 32 0x4D71) ac_at_580 (by rsimp; rw [hsp]; acp_eq) ?_; wn
    have p78 : ∀ c, (c + 1 ≤ 0x3A78 ∨ 0x3A7C ≤ c) → c < 2 ^ 31 →
        M7 (B + BitVec.ofNat 32 c) = M6 (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 => by rw [← hM7]; exact acp_stO (by decide) h1 h2
    have p7C : ∀ c, (c + 1 ≤ 0x3A7C ∨ 0x3A80 ≤ c) → c < 2 ^ 31 →
        M6 (B + BitVec.ofNat 32 c) = m5.mem (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 => by rw [← hM6]; exact acp_stO (by decide) h1 h2
    have p70 : ∀ c, (c + 1 ≤ 0x3A70 ∨ 0x3A74 ≤ c) → c < 2 ^ 31 →
        Mb (B + BitVec.ofNat 32 c) = Ma (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 => by rw [← hMb]; exact acp_stO (by decide) h1 h2
    have p74 : ∀ c, (c + 1 ≤ 0x3A74 ∨ 0x3A78 ≤ c) → c < 2 ^ 31 →
        Ma (B + BitVec.ofNat 32 c) = m2.mem (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 => by rw [← hMa]; exact acp_stO (by decide) h1 h2
    -- From `M7` back to `Mb`, for a byte of the frame words at `sp + 0x1C`.
    have pF : ∀ c, 0x3A6C ≤ c → c < 0x3A78 →
        M7 (B + BitVec.ofNat 32 c) = Mb (B + BitVec.ofNat 32 c) := fun c h1 h2 =>
      (p78 c (by omega) (by omega)).trans ((p7C c (by omega) (by omega)).trans ((pT c (by omega) (by omega)
        (by omega)).trans ((pR2 c (by omega) (by omega) (by omega)).trans (pR1 c (by omega) (by omega) (by omega)))))
    rw [show B + BitVec.ofNat 32 0x52C0 + 0x14 = B + BitVec.ofNat 32 0x52D4 from by acp_eq,
      show B + BitVec.ofNat 32 0x52C0 + 0x10 = B + BitVec.ofNat 32 0x52D0 from by acp_eq] at hv2
    refine acp_done fun n' hpc hmem hreg => ⟨acp_inv hsv hout (by rw [hmem]; exact hW7)
      (by rw [hreg]; rsimp; exact hsp) (by rw [hreg]; rsimp; exact h3) (by rw [hreg]; rsimp; exact h4),
      Or.inr ⟨hpc, fun x h1 h2 h3 h4 => by rw [hmem]; exact hW7 x ⟨h1, h2, h3, h4⟩, ?_, ?_, ?_, ?_, ?_,
        first, hpr, ?_, ?_, ?_, ?_⟩⟩
    · intro q hq
      have e : q = 20 ∨ q = 21 ∨ q = 23 ∨ q = 24 ∨ q = 25 ∨ q = 27 := by revert hq; revert q; decide
      rcases e with rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [hreg]; rsimp)
    · rw [hmem]
      show memLoad32 M7 (B + BitVec.ofNat 32 0x3A6C) = memLoad32 M (B + BitVec.ofNat 32 0x3D9C)
      rw [acp_ld fun j hj => (pF _ (by omega) (by omega)).trans ((p70 _ (by omega) (by omega)).trans
        ((p74 _ (by omega) (by omega)).trans (pP _ (by omega) (by omega) (by omega)))), ← hM1]
      exact memLoad32_store32_same _ _ _
    · rw [hmem]
      show memLoad32 M7 (B + BitVec.ofNat 32 0x3A7C) = 0
      rw [acp_ld fun j hj => p78 _ (by omega) (by omega), ← hM6]
      exact memLoad32_store32_same _ _ _
    · rw [hmem]
      show memLoad32 M7 (B + BitVec.ofNat 32 0x3A78) = (M7 (B + BitVec.ofNat 32 0x4D70)).zeroExtend 32
      rw [p78 _ (by omega) (by omega), ← hM7]
      exact memLoad32_store32_same _ _ _
    · rw [hreg, hmem]; rsimp
    · rw [hmem, hver, ← hv2]
      show (memLoad32 M7 (B + BitVec.ofNat 32 0x3A70)).toNat * 2 ^ 32 +
        (memLoad32 M7 (B + BitVec.ofNat 32 0x3A74)).toNat = _
      rw [acp_ld fun j hj => pF _ (by omega) (by omega),
        acp_ld fun j hj => (pF _ (by omega) (by omega)).trans (p70 _ (by omega) (by omega)), ← hMb,
        memLoad32_store32_same, ← hMa,
        memLoad32_store32_sep (a := B + BitVec.ofNat 32 0x3A74) (b := B + BitVec.ofNat 32 0x52D4)
          (sep_offsets B (by omega) (by omega) (by omega)), memLoad32_store32_same]
    · rw [hmem]
      exact acp_keys hsg hR1 fun o ho => by
        rw [add_ofNat_assoc]
        exact (p78 _ (by omega) (by omega)).trans ((p7C _ (by omega) (by omega)).trans ((pT _ (by omega)
          (by omega) (by omega)).trans (pR2 _ (by omega) (by omega) (by omega))))
    · rw [hmem]
      exact acp_keys hsg hR2 fun o ho => by
        rw [add_ofNat_assoc]
        exact (p78 _ (by omega) (by omega)).trans ((p7C _ (by omega) (by omega)).trans (pT _ (by omega)
          (by omega) (by omega)))
    · rw [hmem]
      exact acp_exp hsg hT fun o ho => by
        rw [add_ofNat_assoc]
        exact (p78 _ (by omega) (by omega)).trans (p7C _ (by omega) (by omega))

/-- From 0x4E4 to 0x584 the closure parses the pinned root and reads its
`root` keys, `targets` keys, and expiry, or rejects with a `TufError` code. -/
def AcPinnedStage : Prop :=
  ∀ (pinned : Bytes) (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcPinnedEnv pinned M) →
    CodeIn n.mem AC bootMainClosure0Code → Fr B 0x5A70 →
    Sep B 0x5A70 (BitVec.ofNat 32 (img% roWindowAddress)) 0x2625 →
    St n.mem AC n 0x4E4 (reg n) → AcInv B Bf g t v M0 n → AcPinnedPre B r n →
    AcStage B Bf g t r v M0 n 0x584 (AcPinnedPost pinned B n.mem (reg n))

/-- **`AcPinnedStage` with its halt refined**: the stage halts only if an
inversion bound fails. -/
def AcPinnedStagePI : Prop :=
  ∀ (pinned : Bytes) (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcPinnedEnv pinned M) →
    CodeIn n.mem AC bootMainClosure0Code → Fr B 0x5A70 →
    Sep B 0x5A70 (BitVec.ofNat 32 (img% roWindowAddress)) 0x2625 →
    St n.mem AC n 0x4E4 (reg n) → AcInv B Bf g t v M0 n → AcPinnedPre B r n →
    AcStagePI B Bf g t r v M0 n 0x584 (AcPinnedPost pinned B n.mem (reg n))

theorem acp_stage_pi : AcPinnedStagePI := by
  intro pinned n B Bf g t r v M0 hE C F hro s I P
  obtain ⟨n', st, hq⟩ := acp_wp (f := reg n) hE C F.al F.hi hro I.sp I.gp I.tp I.saves I.out
    P.1 P.2 (by decide) C n s
  exact ⟨n', st, Or.inr (hq n' rfl rfl fun _ => rfl)⟩

/-- `AcPinnedStage`, from `acp_stage_pi`. -/
theorem acp_stage : AcPinnedStage :=
  fun pinned n B Bf g t r v M0 h1 h2 h3 h4 h5 h6 h7 =>
    (acp_stage_pi pinned n B Bf g t r v M0 h1 h2 h3 h4 h5 h6 h7).acStage

end C3.RV32.Ac
