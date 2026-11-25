import C3BootProofs.Proofs.AcceptExtractHead
import C3BootProofs.Proofs.AcceptExtractSeq
import C3BootProofs.Proofs.AcceptPinnedErr
import C3BootProofs.Proofs.TufRoleKeysMetCalls
import C3BootProofs.Proofs.TufMetaCalls
import C3BootProofs.Proofs.TrustedRootLift
import C3BootProofs.Proofs.Ed25519VerifyWrap
import C3BootProofs.Models.Ed25519Closed

/-!
# The transparency log loop's frame, exits, and calls

From 0xEBA to 0x123A the closure reads one transparency log per pass of a
loop. A pass writes only the ranges of the frame that `acetlW` lists, and
`keys`'s free part once it calls `trusted_root::decode`. `AcetlU` names
the bytes outside those writes, which every pass keeps from the machine at
the start of the pass.

`acetlQ` is the post of a pass: `AcInv`, and the exit at 0x7D6 or the
machine at the next cut. `acetl_f1A6A` is that exit, from the machine at the
start of the pass and the code to log in `s0`.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

/-! ## The frame -/

/-- The ranges, as offsets from the frame's base `B`, that a pass writes:
the callees' stack, `sp + 0x1C`, `sp + 0x28`, `sp + 0x244`, the array at
`sp + 0x890`, `sp + 0x1320`, the cursor's position at `sp + 0x1868`, and the
cursor at `sp + 0x1DC8`. -/
def acetlW : List (Nat × Nat) :=
  [(0x3110, 0x3A50), (0x3A6C, 0x3A70), (0x3A78, 0x3A7C), (0x3C94, 0x3C9C), (0x42E0, 0x43E0), (0x4D70, 0x4D88),
    (0x52B8, 0x52BC), (0x5818, 0x5824)]

theorem acetlW_le : ∀ r ∈ acetlW, r.1 ≤ r.2 ∧ r.2 ≤ 0x5A2C := by decide

/-- `x` lies outside the ranges a pass writes. With `d`, also outside
`keys`'s free part from `fp` and the slice at `sp + 0x1FDC`, which
`decode` writes. -/
def AcetlU (B Bf fp : Word) (d : Bool) (x : Word) : Prop :=
  (∀ r ∈ acetlW, x.toNat < B.toNat + r.1 ∨ B.toNat + r.2 ≤ x.toNat) ∧
    (d = true → (x.toNat < fp.toNat ∨ Bf.toNat + 0xB840 ≤ x.toNat) ∧
      (x.toNat < B.toNat + 0x5A2C ∨ B.toNat + 0x5A34 ≤ x.toNat))

theorem AcetlU.weak {B Bf fp x : Word} {d : Bool} (h : AcetlU B Bf fp true x) : AcetlU B Bf fp d x :=
  ⟨h.1, fun _ => h.2 rfl⟩

section
variable {B Bf fp x : Word} {d : Bool} (F : Fr B 0x5A70)
include F

/-- A range inside one that a pass writes. -/
theorem acetl_sep (h : AcetlU B Bf fp d x) {a b c n : Nat} (hm : (a, b) ∈ acetlW) (h1 : a ≤ c)
    (h2 : c + n ≤ b) : Sep x 1 (B + BitVec.ofNat 32 c) n := by
  have hb := (acetlW_le _ hm).2
  refine ace_sepX F (by simp only at hb; omega) ?_
  rcases h.1 _ hm with h | h
  · exact .inl (by simp only at h; omega)
  · exact .inr (by simp only at h; omega)

theorem acetl_sep' (h : AcetlU B Bf fp d x) {a b c n : Nat} (hm : (a, b) ∈ acetlW) (h1 : a ≤ c)
    (h2 : c + n ≤ b) : Sep (B + BitVec.ofNat 32 c) n x 1 :=
  (acetl_sep F h hm h1 h2).symm

/-- The slice at `sp + 0x1FDC`. -/
theorem acetl_sepFr (h : AcetlU B Bf fp true x) : Sep x 1 (B + BitVec.ofNat 32 0x5A2C) 8 := by
  refine ace_sepX F (by decide) ?_
  rcases (h.2 rfl).2 with h | h
  · exact .inl h
  · exact .inr h

end

/-- `keys`'s free part. -/
theorem acetl_sepBuf {B Bf fp x : Word} (h : AcetlU B Bf fp true x) (hfp : fp.toNat ≤ Bf.toNat + 0xB840)
    (hw : Bf.toNat + 0xB840 ≤ 2 ^ 32) : Sep x 1 fp (Bf.toNat + 0xB840 - fp.toNat) := by
  rcases (h.2 rfl).1 with h | h
  · exact sep_of_le (by omega) (by omega)
  · exact (sep_of_le (by omega) (by have := x.isLt; omega)).symm

/-- Outside the stack and `keys`'s free part, a pass writes nothing. -/
theorem acetl_U_out {B Bf fp x : Word} {d : Bool} (h : x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat)
    (hb : x.toNat < fp.toNat ∨ Bf.toNat + 0xB840 ≤ x.toNat) : AcetlU B Bf fp d x := by
  refine ⟨fun r hr => ?_, fun _ => ⟨hb, ?_⟩⟩
  · have := acetlW_le r hr
    rcases h with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases h with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)

/-- The bytes `n` to `n + l` of the frame, outside the ranges a pass
writes, are in `AcetlU`. -/
theorem acetl_U_at' {X : AceCtx} (O : X.Ok) {fp : Word} {d : Bool} (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat)
    {s l j : Nat} (hs : 0x3A50 + s + l ≤ 0x5A70)
    (hr : ∀ r ∈ acetlW, 0x3A50 + s + l ≤ r.1 ∨ r.2 ≤ 0x3A50 + s)
    (hd : 0x3A50 + s + l ≤ 0x5A2C ∨ 0x5A34 ≤ 0x3A50 + s) (hj : j < l) :
    AcetlU X.B X.Bf fp d (acSlot X.B s + BitVec.ofNat 32 j) := by
  have F := O.lay.fr
  have hx := ace_slotAdd F (k := s) (j := j) (by omega)
  have hbuf : Sep (acSlot X.B s + BitVec.ofNat 32 j) 1 X.Bf acBufLen := by
    rw [ace_slot]; exact O.lay.sep.sub (c := 0x3A50 + s + j) (l := 1) (by omega)
  have hb := ace_ofSep hbuf
  have hbw := O.lay.hi
  unfold acBufLen at hb hbw
  refine ⟨fun r hm => ?_, fun _ => ⟨?_, ?_⟩⟩
  · rcases hr r hm with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases hb with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases hd with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)

theorem acetl_U_at {X : AceCtx} (O : X.Ok) {fp : Word} {d : Bool} (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat)
    {s l j : Nat} (hs : 0x3A50 + s + l ≤ 0x5A70)
    (hr : acetlW.all (fun r => decide (0x3A50 + s + l ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true)
    (hd : (decide (0x3A50 + s + l ≤ 0x5A2C) || decide (0x5A34 ≤ 0x3A50 + s)) = true) (hj : j < l) :
    AcetlU X.B X.Bf fp d (acSlot X.B s + BitVec.ofNat 32 j) := by
  have F := O.lay.fr
  have hx := ace_slotAdd F (k := s) (j := j) (by omega)
  have hbuf : Sep (acSlot X.B s + BitVec.ofNat 32 j) 1 X.Bf acBufLen := by
    rw [ace_slot]; exact O.lay.sep.sub (c := 0x3A50 + s + j) (l := 1) (by omega)
  have hb := ace_ofSep hbuf
  have hbw := O.lay.hi
  unfold acBufLen at hb hbw
  refine ⟨fun r hm => ?_, fun _ => ⟨?_, ?_⟩⟩
  · have := List.all_eq_true.mp hr r hm
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases hb with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at hd
    rcases hd with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)

/-- A word of the frame that a pass keeps. -/
theorem acetl_ld {X : AceCtx} (O : X.Ok) {fp : Word} {d : Bool} {M M' : Word → BitVec 8}
    (hm : ∀ x, AcetlU X.B X.Bf fp d x → M x = M' x) (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat) {s : Nat}
    (hs : 0x3A50 + s + 4 ≤ 0x5A70)
    (hr : acetlW.all (fun r => decide (0x3A50 + s + 4 ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true)
    (hd : (decide (0x3A50 + s + 4 ≤ 0x5A2C) || decide (0x5A34 ≤ 0x3A50 + s)) = true) :
    memLoad32 M (acSlot X.B s) = memLoad32 M' (acSlot X.B s) :=
  ace_load_eq fun j hj => hm _ (acetl_U_at O hfp hs hr hd hj)

/-- Bytes of `Buffers` below `fp` are kept. -/
theorem acetl_U_buf {X : AceCtx} (O : X.Ok) {fp y : Word} {d : Bool} (h1 : X.Bf.toNat ≤ y.toNat)
    (h2 : y.toNat < fp.toNat) (hfp : fp.toNat ≤ X.Bf.toNat + acBufLen) : AcetlU X.B X.Bf fp d y :=
  acetl_U_out (ace_ofSep (ace_bufOut O.lay h1 (by omega))) (.inl h2)

/-- The ranges of `acetlW` that the callees write: their stack and their
results at `sp + 0x244`, `sp + 0x890`, `sp + 0x1320`, and `sp + 0x1DC8`. A
pass's own stores go to the other ranges. -/
def acetlWc : List (Nat × Nat) :=
  [(0x3110, 0x3A50), (0x3C94, 0x3C9C), (0x42E0, 0x43E0), (0x4D70, 0x4D88), (0x5818, 0x5824)]

/-- `x` lies outside the ranges the callees write. -/
def AcetlV (B x : Word) : Prop :=
  ∀ r ∈ acetlWc, x.toNat < B.toNat + r.1 ∨ B.toNat + r.2 ≤ x.toNat

theorem acetl_UV {B Bf fp x : Word} {d : Bool} (h : AcetlU B Bf fp d x) : AcetlV B x := fun r hr =>
  h.1 r ((by decide : ∀ r ∈ acetlWc, r ∈ acetlW) r hr)

theorem acetl_sepV {B x : Word} (F : Fr B 0x5A70) (h : AcetlV B x) {a b c n : Nat} (hm : (a, b) ∈ acetlWc)
    (h1 : a ≤ c) (h2 : c + n ≤ b) : Sep x 1 (B + BitVec.ofNat 32 c) n := by
  have hb := (acetlW_le _ ((by decide : ∀ r ∈ acetlWc, r ∈ acetlW) _ hm)).2
  refine ace_sepX F (by simp only at hb; omega) ?_
  rcases h _ hm with h | h
  · exact .inl (by simp only at h; omega)
  · exact .inr (by simp only at h; omega)

/-- The bytes `j < l` of the slot at `s`, outside the callees' ranges. -/
theorem acetl_V_at {X : AceCtx} (O : X.Ok) {s l j : Nat} (hs : 0x3A50 + s + l ≤ 0x5A70)
    (hr : acetlWc.all (fun r => decide (0x3A50 + s + l ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true) (hj : j < l) :
    AcetlV X.B (acSlot X.B s + BitVec.ofNat 32 j) := by
  have F := O.lay.fr
  have hx := ace_slotAdd F (k := s) (j := j) (by omega)
  intro r hm
  have := List.all_eq_true.mp hr r hm
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

/-- A word of the frame outside the callees' ranges. -/
theorem acetl_ldV {X : AceCtx} (O : X.Ok) {M M' : Word → BitVec 8} (hm : ∀ x, AcetlV X.B x → M x = M' x)
    {s : Nat} (hs : 0x3A50 + s + 4 ≤ 0x5A70)
    (hr : acetlWc.all (fun r => decide (0x3A50 + s + 4 ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true) :
    memLoad32 M (acSlot X.B s) = memLoad32 M' (acSlot X.B s) :=
  ace_load_eq fun j hj => hm _ (acetl_V_at O hs hr hj)

/-- Outside the stack, the callees write nothing. -/
theorem acetl_V_out {B x : Word} (h : x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat) : AcetlV B x := by
  intro r hr
  have := acetlW_le r ((by decide : ∀ r ∈ acetlWc, r ∈ acetlW) _ hr)
  rcases h with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

/-! ## The post and the exits -/

/-- At a pass's exits: `AcInv`, and the exit at 0x7D6 or `P` at `o`. -/
def acetlQ (X : AceCtx) (o : Nat) (P : Machine → Prop) : Post := fun pc M f =>
  ∀ n : Machine, n.pc = pc → n.mem = M → (∀ q, reg n q = f q) →
    AcInv X.B X.Bf X.g X.t X.v X.M0 n ∧ (AcFail X.B X.r n ∨ (n.pc = AC + BitVec.ofNat 32 o ∧ P n))

theorem acetl_stage {X : AceCtx} {n0 : Machine} {o0 o : Nat} {P : Machine → Prop}
    (hc : CodeIn n0.mem AC bootMainClosure0Code) (hs : St n0.mem AC n0 o0 (reg n0))
    (k : WP bootMainClosure0Code AC (acetlQ X o P) n0.mem o0 (reg n0)) : X.stage n0 o P := by
  obtain ⟨m', c, q⟩ := k (by decide) hc n0 hs
  exact ⟨m', c, .inr (q m' rfl rfl fun _ => rfl)⟩

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {o : Nat} {P : Machine → Prop} {M : Word → BitVec 8}
  {f : Fin 32 → Word}

/-- `AcInv` and the result pointer, from the machine at the start of the
pass. -/
theorem acetl_inv (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x)
    {n : Machine} (hn : n.mem = M) (h2 : reg n (2 : Fin 32) = X.B + 0x3A50) (h3 : reg n (3 : Fin 32) = X.g)
    (h4 : reg n (4 : Fin 32) = X.t) :
    AcInv X.B X.Bf X.g X.t X.v X.M0 n ∧ memLoad32 n.mem (acSlot X.B 0x40) = X.r := by
  have F := O.lay.fr
  have hh := F.hi
  have hfp := A.fr.lo
  refine ⟨⟨h2, h3, h4, fun k hk => ?_, fun x h1 h2 => ?_⟩, ?_⟩
  · rw [hn, ← A.inv.saves k hk]
    refine ace_load_eq fun j hj => hm _ ?_
    have e : X.B + BitVec.ofNat 32 (0x5A6C - 4 * k) + BitVec.ofNat 32 j =
        acSlot X.B (0x201C - 4 * k) + BitVec.ofNat 32 j := by
      rw [ace_slot, add_ofNat_assoc]; congr 2; omega
    rw [e]
    refine acetl_U_at' O hfp (l := 4) (by omega) (fun r hr => .inr ?_) (.inr (by omega)) hj
    have := acetlW_le r hr; omega
  · rw [hn, hm x (acetl_U_out (ace_ofSep h1) ?_)]
    · exact A.inv.out x h1 h2
    · have := A.fr.hi; have := ace_ofSep h2; unfold acBufLen at this; omega
  · rw [hn, acetl_ld O hm hfp (s := 0x40) (by decide) (by decide) (by decide), ← O.pre.res]
    exact ace_load_eq fun j hj => A.keep.mem _ (.inr ⟨0x40 + j, .inl ⟨by omega, by omega⟩, by
      rw [ace_slot, Nat.add_assoc]⟩)

/-- From 0x1A6A, with the code to log in `s0`, to the exit at 0x7D6. -/
theorem acetl_f1A6A (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (R : AceHR X f)
    (he : (f 8 &&& 0xFF).toNat < 0x27) : WP bootMainClosure0Code AC (acetlQ X o P) M 0x1A6A f := by
  refine WP.alu ac_at_1a6a ?_
  refine WP.jal ac_at_1a6c (by decide) ?_
  refine WP.here fun n hpc hn hr => ?_
  obtain ⟨hI, hres⟩ := acetl_inv O A hm hn (by rw [hr]; rsimp; exact R.rsp) (by rw [hr]; rsimp; exact R.rgp)
    (by rw [hr]; rsimp; exact R.rtp)
  refine ⟨hI, .inl (.inr (.inr (.inl ⟨by rw [hpc]; rfl, hres, ?_⟩)))⟩
  rw [hr]; rsimp; rw [R.rz, ev_add, show (0 : Word) + f 8 = f 8 from BitVec.zero_add _]; exact he

theorem acetl_f1424 (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (R : AceHR X f) :
    WP bootMainClosure0Code AC (acetlQ X o P) M 0x1424 f := by
  refine WP.aluImm ac_at_1424 ?_; wn
  refine WP.jal ac_at_1426 (by decide) ?_
  refine acetl_f1A6A O A hm (by hr) ?_
  rsimp; rw [R.rz]; decide

/-- From 0x1428, with the code to log at `sp + 0x248`. -/
theorem acetl_f1428 (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (R : AceHR X f)
    (he : (M (acSlot X.B 0x248)).toNat < 0x27) : WP bootMainClosure0Code AC (acetlQ X o P) M 0x1428 f := by
  refine WP.lbu ac_at_1428 ?_; wn
  refine WP.jal ac_at_142c (by decide) ?_
  refine acetl_f1A6A O A hm (by hr) ?_
  rsimp; rw [R.rsp, ace_zeAnd]
  rw [show X.B + 0x3A50 + 0x248 = acSlot X.B 0x248 by simp only [acSlot]; bv_omega]; exact he

/-- From 0x1410, with the code to log at `s3 + 4`. -/
theorem acetl_f1410 (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (R : AceHR X f)
    (he : (M (acSlot X.B 0x890 + 4)).toNat < 0x27) : WP bootMainClosure0Code AC (acetlQ X o P) M 0x1410 f := by
  refine WP.lbu ac_at_1410 ?_; wn
  refine WP.jal ac_at_1414 (by decide) ?_
  refine acetl_f1A6A O A hm (by hr) ?_
  rsimp; rw [R.r19, ace_zeAnd]; exact he

/-- From 0x140A, with `a0` at `sp + 0x1310` and the code to log at
`sp + 0x1324`. -/
theorem acetl_f140A (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (R : AceHR X f) (h10 : f a0 = acSlot X.B 0x1310)
    (he : (M (acSlot X.B 0x1324)).toNat < 0x27) : WP bootMainClosure0Code AC (acetlQ X o P) M 0x140A f := by
  refine WP.lbu ac_at_140a ?_; wn
  refine WP.jal ac_at_140e (by decide) ?_
  refine acetl_f1A6A O A hm (by hr) ?_
  rsimp; rw [h10, ace_zeAnd]
  rw [show acSlot X.B 0x1310 + 0x14 = acSlot X.B 0x1324 by simp only [acSlot]; bv_omega]; exact he

/-- From 0x1402, with the code to log at `sp + 0x1324`. -/
theorem acetl_f1402 (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (R : AceHR X f)
    (he : (M (acSlot X.B 0x1324)).toNat < 0x27) : WP bootMainClosure0Code AC (acetlQ X o P) M 0x1402 f := by
  refine WP.lui ac_at_1402 ?_; wn
  refine WP.aluImm ac_at_1404 ?_; wn
  refine WP.alu ac_at_1408 ?_; wn
  refine acetl_f140A O A hm (by hr) ?_ he
  rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega

/-- From 0x1416, with the code to log at `sp + 0x1321`. -/
theorem acetl_f1416 (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (R : AceHR X f)
    (he : (M (acSlot X.B 0x1321)).toNat < 0x27) : WP bootMainClosure0Code AC (acetlQ X o P) M 0x1416 f := by
  refine WP.lui ac_at_1416 ?_; wn
  refine WP.aluImm ac_at_1418 ?_; wn
  refine WP.alu ac_at_141c ?_; wn
  refine WP.lbu ac_at_141e ?_; wn
  refine WP.jal ac_at_1422 (by decide) ?_
  refine acetl_f1A6A O A hm (by hr) ?_
  rsimp; rw [ace_zeAnd]; simp only [ev_add]
  rw [show (4096 : Word) + 784 + f sp + 0x11 = acSlot X.B 0x1321 by rw [R.rsp]; simp only [acSlot]; bv_omega]
  exact he

end

/-! ## Calls -/

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

theorem acetl_keep {m1 m2 : Machine} {sp0 : Word} (h2 : reg m2 sp = sp0) (h1 : reg m1 sp = sp0)
    (hs : ∀ q : Fin 32, q.val ∈ trSaved → reg m2 q = reg m1 q) : ∀ x, x ∉ jClob → reg m2 x = reg m1 x :=
  tmc_keepVal fun q hq => by
    by_cases e : q = sp
    · rw [e, h2, h1]
    · exact hs q (by revert hq e; revert q; decide)

/-- A call to `trusted_root::decode(out, t, n, fr)`. -/
theorem WP.acetlDecode {hi lo out t fr fp sp0 : Word} {n fl : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = TRDC) (hev : (off + 8) % 2 = 0)
    (hc : TrDecCode M) (h0 : f a0 = out) (ha1 : f a1 = t) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = fr)
    (hsp : f sp = sp0) (hsa : sp0.toNat % 4 = 0)
    (hsl : 0x70 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000) (hoa : out.toNat % 4 = 0)
    (how : out.toNat + 8 ≤ 0x40000000) (hfa : fr.toNat % 4 = 0) (hfw : fr.toNat + 8 ≤ 0x40000000)
    (hfp : memLoad32 M fr = fp) (hfl : memLoad32 M (fr + 4) = BitVec.ofNat 32 fl)
    (hbw : fp.toNat + fl ≤ 0x40000000) (htw : t.toNat + n ≤ 0x40000000)
    (sOG : Sep out 8 (sp0 + 0xFFFFFF90) 0x70) (sFG : Sep fr 8 (sp0 + 0xFFFFFF90) 0x70)
    (sBG : Sep fp fl (sp0 + 0xFFFFFF90) 0x70) (sTG : Sep t n (sp0 + 0xFFFFFF90) 0x70)
    (sTB : Sep t n fp fl) (sOB : Sep out 8 fp fl) (sFB : Sep fr 8 fp fl) (sOF : Sep out 8 fr 8)
    (cG : Sep (sp0 + 0xFFFFFF90) 0x70 base code.length) (cO : Sep out 8 base code.length)
    (cF : Sep fr 8 base code.length) (cB : Sep fp fl base code.length)
    (k : ∀ m2 : Machine,
      trDecMem M (sp0 + 0xFFFFFF90) out fr fp fl (trDecodeRes (base64Decode (memBytes M t n)) fl) m2.mem →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := TRDC) (cl := jClob)
    (P := fun m2 => trDecMem M (sp0 + 0xFFFFFF90) out fr fp fl (trDecodeRes (base64Decode (memBytes M t n)) fl) m2.mem)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by
      rw [hP.2 _ (sep_pt cG hi).symm (sep_pt cO hi).symm (sep_pt cF hi).symm (sep_pt cB hi).symm]; exact hc i hi) k
  have hr := tmc_regs hreg1
  have hra : reg m1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, sp2, sv2, hR⟩ := trustedRootDecode_correct m1 (by rw [hmem1]; exact hc) hpc1
    (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1]) (by rw [hr a2 (by decide), ha2])
    (by rw [hr a3 (by decide), ha3]) hra (even_clear _ (even_at base hb _ hev)) (by rw [hr sp (by decide), hsp])
    hsa hsl hsw hoa how hfa hfw (by rw [hmem1]; exact hfp) (by rw [hmem1]; exact hfl) hbw htw sOG sFG sBG sTG sTB
    sOB sFB sOF
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, acetl_keep sp2 (by rw [hr sp (by decide), hsp]) sv2⟩

/-- A call to `ed25519_public_key_ok(pk)`: `a0` is 1 when `evPk` holds of
the key and 0 otherwise. -/
theorem WP.acetlPkOk {hi lo pk sp0 : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = PKO) (hev : (off + 8) % 2 = 0)
    (E : PkEnv M) (h0 : f a0 = pk) (hsp : f sp = sp0)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x940 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000) (hpw : pk.toNat + 32 < 2 ^ 32)
    (sP : Sep pk 32 (sp0 + 0xFFFFF6C0) 0x940)
    (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 (sp0 + 0xFFFFF6C0) 0x940)
    (sD : Sep (BitVec.ofNat 32 edDAddress) 40 (sp0 + 0xFFFFF6C0) 0x940)
    (sS : Sep (BitVec.ofNat 32 edSqrtM1Address) 40 (sp0 + 0xFFFFF6C0) 0x940)
    (sPc : Sep (BitVec.ofNat 32 (img% edPrimeAddress)) 32 (sp0 + 0xFFFFF6C0) 0x940)
    (sE1 : Sep (BitVec.ofNat 32 (img% p256OneAddress)) 32 (sp0 + 0xFFFFF6C0) 0x940)
    (sE2 : Sep (BitVec.ofNat 32 (img% edPm1Address)) 32 (sp0 + 0xFFFFF6C0) 0x940)
    (cG : Sep (sp0 + 0xFFFFF6C0) 0x940 base code.length)
    (k : ∀ m2 : Machine, reg m2 a0 = (if evPk M (memBytes M pk 32) then 1 else 0) →
      Out M m2.mem (sp0 + 0xFFFFF6C0) 0x940 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := PKO) (cl := jClob)
    (P := fun m2 => reg m2 a0 = (if evPk M (memBytes M pk 32) then 1 else 0) ∧ Out M m2.mem (sp0 + 0xFFFFF6C0) 0x940)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc cG) (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  have hra : reg m1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, sp2, sv2, ha, hO⟩ := pkOk_correct m1 (by rw [hmem1]; exact E) hpc1
    (by rw [hr a0 (by decide), h0]) hra (even_clear _ (even_at base hb _ hev)) (by rw [hr sp (by decide), hsp])
    hsa hsl hsw hpw sP sO sD sS sPc sE1 sE2
  rw [hmem1] at ha hO
  refine ⟨m2, c2, pc2, ⟨ha, fun x hx => hO x hx.symm⟩, acetl_keep sp2 (by rw [hr sp (by decide), hsp]) sv2⟩

theorem acetl_tvfTime (v : Bytes) : ∀ e, tvfTime v = .error e → e < 0x27 := by
  intro e h
  unfold tvfTime at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · cases h

/-- `valid_for`'s error bytes are below 0x27. -/
theorem acetl_vfErr (d : Bytes) : ∀ e, validForPos d = .error e → e < 0x27 := by
  intro e h
  unfold validForPos at h
  split at h
  · next e' he => cases h; exact acp_objField _ _ _ he
  · split at h
    · next e' he => cases h; exact acetl_tvfTime _ _ he
    · unfold tvfRest at h
      split at h
      · next e' he => cases h; exact acp_objGet _ _ _ he
      · cases h
      · split at h
        · next e' he => cases h; exact acetl_tvfTime _ _ he
        · cases h

/-- A call to `trusted_root::valid_for(out, p, n)` on the value `j`. -/
theorem WP.acetlValidFor {hi lo out p sp0 : Word} {n : Nat} {c : Bool} {j : Json}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = TVF) (hev : (off + 8) % 2 = 0)
    (hc : TvfCode M) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (hsp : f sp = sp0)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x144 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (hoa : out.toNat % 4 = 0) (how : out.toNat + 0x18 ≤ 0x40000000) (hpw : p.toNat + n + 4 ≤ 0x40000000)
    (hp0 : p.toNat ≠ 0) (sOG : Sep out 0x18 (sp0 + 0xFFFFFEBC) 0x144) (sPG : Sep p (n + 4) (sp0 + 0xFFFFFEBC) 0x144)
    (sRO : Sep (sp0 + 0xFFFFFEBC) 0x144 TVF_RO 0x1400)
    (hks : memBytes M tvfStartKey 5 = ascii!"start") (hke : memBytes M tvfEndKey 3 = ascii!"end")
    (hj : JVal c (memBytes M p n) j)
    (cG : Sep (sp0 + 0xFFFFFEBC) 0x144 base code.length) (cO : Sep out 0x18 base code.length)
    (k : ∀ m2 : Machine, ∀ r, tvfMem M (sp0 + 0xFFFFFEBC) out r m2.mem →
      r.toOption.map (fun x => (⟨x.1, x.2⟩ : Window)) = validFor j → (∀ e, r = .error e → e < 0x27) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := TVF) (cl := jClob)
    (P := fun m2 => ∃ r, tvfMem M (sp0 + 0xFFFFFEBC) out r m2.mem ∧
      r.toOption.map (fun x => (⟨x.1, x.2⟩ : Window)) = validFor j ∧ ∀ e, r = .error e → e < 0x27)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by
      obtain ⟨r, hR, -, -⟩ := hP
      rw [hR.2 _ (sep_pt cG hi).symm (sep_pt cO hi).symm]; exact hc i hi)
    (fun m2 hP => by obtain ⟨r, hR, hv, he⟩ := hP; exact k m2 r hR hv he)
  have hr := tmc_regs hreg1
  have hra : reg m1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, sp2, sv2, hR⟩ := trustedRootValidFor_correct m1 (by rw [hmem1]; exact hc) hpc1
    (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1]) (by rw [hr a2 (by decide), ha2]) hra
    (even_clear _ (even_at base hb _ hev)) (by rw [hr sp (by decide), hsp]) hsa hsl hsw hoa how hpw hp0 sOG sPG sRO
    (by rw [hmem1]; exact hks) (by rw [hmem1]; exact hke)
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, ⟨_, hR, validForPos_spec hj, acetl_vfErr _⟩,
    acetl_keep sp2 (by rw [hr sp (by decide), hsp]) sv2⟩

end

end C3.RV32.Ac
