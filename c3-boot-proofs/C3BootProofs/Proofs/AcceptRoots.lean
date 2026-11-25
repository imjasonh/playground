import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.TufReadDoc
import C3BootProofs.Proofs.TufParseRoot
import C3BootProofs.Proofs.TufRoleKeysRead
import C3BootProofs.Proofs.TufExpires
import C3BootProofs.Proofs.TufRoleKeysMetSpec
import C3BootProofs.Proofs.TufRoleKeysMetCalls
import C3BootProofs.Proofs.JsonGet
import C3BootProofs.Models.TufLinkMeta
import C3BootProofs.Models.TufLinkKeys
import C3BootProofs.Models.JsonLinkCanon
import C3BootProofs.Models.TufLink

/-!
# `boot_main`'s first closure: the root chain

`AcceptRoots` is the stage from 0x584 to 0x836: the loop of `tuf::verify`
over the roots after the pinned one, and the check of the last root's
expiry after it. It is the fold in `verifyTuf`: each iteration reads the
next root with `tuf::read_doc`, parses it with `tuf::parse_root`, checks
that its version is one more than the trusted root's, and checks its
signatures with `RoleKeys::met` against the trusted root's root role and
then against its own. The last iteration also reads its targets role and
its expiry.

The loop keeps the trusted root's `RoleKeys` in three places: its first
byte in `[sp + 0x28]`, its second in `s6`, and the rest at `sp + 0x1322`.
`acoTB` puts them back together.

`AcRootsGap` lists what the stage assumes about its callees and their
contracts don't say: that the error bytes of `prModel`, `rkModel`, and
`expiresModel` are `TufError` codes, and `AcMetSpec`, `tufRoleKeysMet_spec`
with the two facts about `a0` and `a1` that the loop branches on.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.Json

/-! ## The specification's fold -/

/-- One step of `verifyTuf`'s fold over the roots: the root after `prev`. -/
def acoStep (prev : TufRoot) (doc : Bytes) : Option TufRoot := do
  let next ← parseTufRoot doc
  require (next.version == prev.version + 1)
  require (← thresholdMet next.md prev.md.signed (ascii!"root"))
  require (← thresholdMet next.md next.md.signed (ascii!"root"))
  pure next

theorem aco_verifyTuf (pinned : Bytes) (parts : TufParts) :
    verifyTuf pinned parts = (do
      let first ← parseTufRoot pinned
      let root ← parts.roots.foldlM acoStep first
      let rootExpires ← expires root.md
      let targets ← parseMeta parts.targets (ascii!"targets")
      require (← thresholdMet targets root.md.signed (ascii!"targets"))
      let targetsExpires ← expires targets
      let entry ← targets.signed.field (ascii!"targets") >>= Json.field (ascii!"trusted_root.json")
      let length ← entry.field (ascii!"length") >>= Json.asNum
      let digest ← entry.field (ascii!"hashes") >>= Json.field (ascii!"sha256") >>= Json.asStr
      require (length == parts.trustedRoot.length && digest == hexBytes (sha256 parts.trustedRoot))
      pure (root.version, min rootExpires targetsExpires)) := rfl

/-! ## The callees' gaps -/

/-- `tufRoleKeysMet_spec`, with what the loop reads of the result: `a0`
is zero when its bit 0 is, and when bit 0 is set, the low byte of `a1` is
a `TufError` code. -/
def AcMetSpec : Prop :=
  ∀ (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat}
    {md : Meta} {dj sj : Json} {role : Bytes} {es : List (Bytes × Option TufKey)}
    {M : Word → BitVec 8} {DP : Word} {DL : Nat},
    m.pc = TRM → reg m a0 = R → reg m a1 = A → reg m sp = s + BitVec.ofNat 32 0x3920 →
    reg m ra = retAddr → retAddr &&& ~~~1 = retAddr → s.toNat % 16 = 0 →
    0x3FC80000 ≤ s.toNat → s.toNat + 0x3920 ≤ 0x3FCE0000 →
    Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize) →
    Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) →
    (∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = m.mem x) → RmCode M) →
    R.toNat % 4 = 0 → R.toNat + 0x540 ≤ 0x40000000 → Sep s 0x3920 R 0x540 →
    MP.toNat + ML ≤ 0x40000000 → ML < 2 ^ 31 → Sep s 0x3920 MP ML →
    SP.toNat ≠ 0 → SP.toNat + SL ≤ 0x40000000 → SL < 2 ^ 31 → Sep s 0x3920 SP SL →
    A.toNat % 4 = 0 → Sep s 0x3920 A 16 → memLoad32 m.mem A = MP →
    memLoad32 m.mem (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML →
    memLoad32 m.mem (A + BitVec.ofNat 32 8) = SP →
    memLoad32 m.mem (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL →
    roleKeys dj role = some (t, es) → JVal true (memBytes M DP DL) dj → RkAt m.mem R t (es.map C3.Json.rkTag) →
    RkWf (es.map C3.Json.rkTag) → memBytes m.mem MP ML = encode md.signed →
    JVal true (memBytes m.mem SP SL) sj → (sj.asArr >>= List.mapM sigPair) = some md.sigs →
    ∃ m', Steps m m' ∧
      (rmH m'.pc m'.mem (reg m') ∨
        (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
          (reg m' a0 &&& 1 = 0 → reg m' a0 = 0 ∧ (reg m' a1 ≠ 0 → thresholdMet md dj role = some true)) ∧
          (reg m' a0 &&& 1 ≠ 0 → (reg m' a1 &&& 0xFF).toNat < 0x27)))

/-- What the stage assumes and its callees' contracts don't say. -/
structure AcRootsGap : Prop where
  pr : ∀ d e, prModel d = .error e → e < 0x27
  rk : ∀ d role e, rkModel d role = .error e → e < 0x27
  ex : ∀ d e, expiresModel d = .error e → e < 0x27
  met : AcMetSpec

/-! ## The stage's environment, pre- and postcondition -/

/-- Where `tuf::read_doc` is. -/
abbrev TRD : Word := BitVec.ofNat 32 tufReadDocAddress

/-- Where the role names `root` and `targets` are. -/
abbrev acoRootName : Word := 0x3FCC476E
abbrev acoTargetsName : Word := 0x3FCC4020

/-- The code and data the stage runs and reads, in memory `M`, for the ROM's
stack `R`: the closure, `tuf::read_doc` and its callees, `tuf::parse_root`,
`RoleKeys::met` (and with it `RoleKeys::read`), `tuf::expires`, `memcpy`,
and the two role names. -/
structure AcRootsEnv (R : Nat) (romBase : Word) (romCode : List Nat) (B Bf : Word) (M : Word → BitVec 8) :
    Prop where
  ac : CodeIn M AC bootMainClosure0Code
  rd : CodeIn M TRD tufReadDocCode
  ix : CodeIn M (TRD + 0xB388) tufIndexDocCode
  fp : CodeIn M (TRD + 0x16DA4) flashPartReadCode
  fr : FRdEnv M (TRD + 0x16DA4 + 0xFFFFFEA8) (B + BitVec.ofNat 32 (0x38D0 - R)) (Bf + 0x4000) 0x2800 R
    romBase romCode
  pr : PrCode M
  rm : RmCode M
  tex : TexCode M
  mcs : CodeIn M MCS memcpyStubCode
  mcb : CodeIn M (MCS + 8) memcpyBodyCode
  root : memBytes M acoRootName 4 = ascii!"root"
  tgts : memBytes M acoTargetsName 7 = ascii!"targets"
  ro : Sep B 0x5A70 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize)

/-- A `RoleKeys` result in the bytes `b`: an error (0xFE first, then a
`TufError` code), or the role `role`'s keys in the root `dj`. -/
def AcoRk (b : Nat → BitVec 8) (dj : Json) (role : Bytes) : Prop :=
  (b 0 = 0xFE ∧ (b 1).toNat < 0x27) ∨
    ∃ t es, roleKeys dj role = some (t, es) ∧ RkB b t (es.map C3.Json.rkTag)

/-- The trusted root's `RoleKeys`: the first byte in the word `w`, the
second in `s6`, and the rest at `sp + 0x1322`. -/
def acoTB (B : Word) (M : Word → BitVec 8) (w s6 : Word) : Nat → BitVec 8 := fun o =>
  if o = 0 then w.extractLsb' 0 8 else if o = 1 then s6.extractLsb' 0 8
  else M (acSlot B 0x1320 + BitVec.ofNat 32 o)

/-- `acoTB` with the rest at `sp + k + 2`. -/
def acoTBk (B : Word) (M : Word → BitVec 8) (w s6 : Word) (k : Nat) : Nat → BitVec 8 := fun o =>
  if o = 0 then w.extractLsb' 0 8 else if o = 1 then s6.extractLsb' 0 8
  else M (acSlot B k + BitVec.ofNat 32 o)

/-- `tuf::expires`'s result at `sp + 0x1310`: the expiry of the root `md`,
or a `TufError` code. -/
def AcoExp (B : Word) (M : Word → BitVec 8) (md : Meta) : Prop :=
  (M (acSlot B 0x1310) = 0 → ∃ e, expires md = some e ∧
    memLoad32 M (acSlot B 0x1318) = BitVec.ofNat 32 (e % 2 ^ 32) ∧
    memLoad32 M (acSlot B 0x131C) = BitVec.ofNat 32 (e / 2 ^ 32)) ∧
  (M (acSlot B 0x1310) ≠ 0 → (M (acSlot B 0x1311)).toNat < 0x27)

/-- What the loop keeps of the trusted root `prev`: its version in
`[sp + 0x24]` (low) and `[sp + 0x20]` (high), and its root role's keys.
`prev.md.signed` was parsed from bytes in some memory. -/
structure AcoState (B : Word) (M : Word → BitVec 8) (s6 : Word) (prev : TufRoot) : Prop where
  ver : (memLoad32 M (acSlot B 0x20)).toNat * 2 ^ 32 + (memLoad32 M (acSlot B 0x24)).toNat = prev.version
  w : (memLoad32 M (acSlot B 0x28)).toNat < 256
  b : s6.toNat < 256
  keys : AcoRk (acoTB B M (memLoad32 M (acSlot B 0x28)) s6) prev.md.signed (ascii!"root")
  src : ∃ (M' : Word → BitVec 8) (P : Word) (L : Nat), JVal true (memBytes M' P L) prev.md.signed

/-- The root `prev`'s targets role at `sp + 0xDD0` and its expiry. -/
def AcoTail (B : Word) (M : Word → BitVec 8) (prev : TufRoot) : Prop :=
  AcoRk (fun o => M (acSlot B 0xDD0 + BitVec.ofNat 32 o)) prev.md.signed (ascii!"targets") ∧ AcoExp B M prev.md

/-- The index at `sp + 0x244` places each root `docs[j]` in flash from
`start`. -/
def AcoDocs (flash : Nat → BitVec 8) (M : Word → BitVec 8) (B start : Word) (docs : List Bytes) : Prop :=
  ∀ j, j < docs.length → ∃ o l, tufIndexDocSpec M (acSlot B 0x244) j = .ok (o, l) ∧
    flashBytes flash (start.toNat + o) l = docs.getD j []

/-- The bytes the loop doesn't write: all but the callees' frames below
`sp`, the words from `sp + 0x20` to `sp + 0x30`, the scratch from
`sp + 0x350` to `sp + 0x1EE8`, and `doc`. -/
def AcoFix (B Bf x : Word) : Prop :=
  Sep x 1 B 0x3A50 ∧ Sep x 1 (acSlot B 0x20) 0x10 ∧ Sep x 1 (acSlot B 0x350) 0x1B98 ∧ Sep x 1 (Bf + 0x4000) 0x2800

/-- What the loop doesn't change: each byte that `AcoFix` names. -/
def AcoKeep (B Bf : Word) (M0 M : Word → BitVec 8) : Prop :=
  ∀ x, AcoFix B Bf x → M x = M0 x

/-- The registers the loop doesn't change: `sp`, `gp`, `tp`, `s4`, `s5`,
`s7`, `s8`, `s9`, and `s11`. -/
def acoKept (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 20, 21, 23, 24, 25, 27]

/-- **At 0x584**, the start of the fold: `doc` at `s4`, the roots `docs`
in flash from `s8` (at most `maxRoots`, their count at `sp + 0x1C`), the
fold's index 0 at `sp + 0x2C`, the result pointer `r` at `sp + 0x40`, and
the pinned root `first` as the trusted root, with its targets role and
expiry. -/
def AcRootsPre (flash : Nat → BitVec 8) (B Bf r : Word) (docs : List Bytes) (first : TufRoot) (n : Machine) :
    Prop :=
  reg n (20 : Fin 32) = Bf + 0x4000 ∧ docs.length ≤ maxRoots ∧
  memLoad32 n.mem (acSlot B 0x1C) = BitVec.ofNat 32 docs.length ∧
  memLoad32 n.mem (acSlot B 0x2C) = 0 ∧ memLoad32 n.mem (acSlot B 0x40) = r ∧
  AcoDocs flash n.mem B (reg n (24 : Fin 32)) docs ∧
  AcoState B n.mem (reg n (22 : Fin 32)) first ∧ AcoTail B n.mem first

/-- **At 0x836**, after the fold: the fold from `first` over `docs` ends at
`root`, whose version is in `[sp + 0x24]` and `[sp + 0x20]`, whose root and
targets roles are at `sp + 0x1320` and `sp + 0xDD0`, and whose expiry is at
`sp + 0x1318`; and the registers and memory that `AcoKeep` names are as
they were in `n0`. -/
def AcRootsPost (B Bf : Word) (docs : List Bytes) (first : TufRoot) (n0 n : Machine) : Prop :=
  ∃ root, docs.foldlM acoStep first = some root ∧
    AcoKeep B Bf n0.mem n.mem ∧ (∀ q, acoKept q = true → reg n q = reg n0 q) ∧
    (memLoad32 n.mem (acSlot B 0x20)).toNat * 2 ^ 32 + (memLoad32 n.mem (acSlot B 0x24)).toNat = root.version ∧
    AcoRk (fun o => n.mem (acSlot B 0x1320 + BitVec.ofNat 32 o)) root.md.signed (ascii!"root") ∧
    AcoRk (fun o => n.mem (acSlot B 0xDD0 + BitVec.ofNat 32 o)) root.md.signed (ascii!"targets") ∧
    n.mem (acSlot B 0x1310) = 0 ∧ ∃ e, expires root.md = some e ∧
      memLoad32 n.mem (acSlot B 0x1318) = BitVec.ofNat 32 (e % 2 ^ 32) ∧
      memLoad32 n.mem (acSlot B 0x131C) = BitVec.ofNat 32 (e / 2 ^ 32)

/-- **The loop invariant** at 0x584, after `i` roots: the fold over the
first `i` roots ends at the trusted root `prev`, which the loop keeps as
`AcoState` says; at the start and after the last root, `prev`'s targets
role and expiry are at `sp + 0xDD0` and `sp + 0x1310`; `i` is at
`sp + 0x2C`; and the registers and memory that `AcoKeep` names are as they
were at the start `n0`. -/
structure AcoInv (B Bf : Word) (docs : List Bytes) (first : TufRoot) (n0 n : Machine) (i : Nat) : Prop where
  le : i ≤ docs.length
  keep : AcoKeep B Bf n0.mem n.mem
  regs : ∀ q, acoKept q = true → reg n q = reg n0 q
  cnt : memLoad32 n.mem (acSlot B 0x2C) = BitVec.ofNat 32 i
  fold : ∃ prev, (docs.take i).foldlM acoStep first = some prev ∧ AcoState B n.mem (reg n (22 : Fin 32)) prev ∧
    (i = 0 ∨ i = docs.length → AcoTail B n.mem prev)

/-- **The root-chain stage**, from 0x584 to 0x836, for the callees' code
and data `AcRootsEnv` in memory that agrees with `M0` outside the stack and
`Buffers`. It reaches 0x836 only when the fold over the roots succeeds and
the last root's expiry parses, and then `AcRootsPost` holds. -/
def AcRootsStage : Prop :=
  ∀ (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat), RomRead flash R romBase romCode →
  ∀ (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (docs : List Bytes)
    (first : TufRoot),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcRootsEnv R romBase romCode B Bf M) →
    Fr B 0x5A70 → Sep B 0x5A70 Bf acBufLen → Bf.toNat % 4 = 0 → Bf.toNat + acBufLen ≤ 0x40000000 →
    R ≤ 0x38D0 → St n.mem AC n 0x584 (reg n) → AcInv B Bf g t v M0 n → AcRootsPre flash B Bf r docs first n →
    AcStage B Bf g t r v M0 n 0x836 (AcRootsPost B Bf docs first n)

/-! ## Addresses and separation -/

set_option maxRecDepth 20000

/-- Where the stack and the buffers are, as numbers. -/
structure AcoNum (B Bf : Word) : Prop where
  b0 : 0x3FC801A0 ≤ B.toNat
  b1 : B.toNat + 0x5A70 ≤ 0x3FCE0000
  b2 : B.toNat % 16 = 0
  f0 : Bf.toNat + 0xB954 ≤ 0x40000000
  f1 : Bf.toNat % 4 = 0
  bb : B.toNat + 0x5A70 ≤ Bf.toNat ∨ Bf.toNat + 0xB954 ≤ B.toNat

theorem aco_sepN {a b : Word} {n k : Nat} (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat)
    (ha : a.toNat + n ≤ 2 ^ 32) (hb : b.toNat + k ≤ 2 ^ 32) : Sep a n b k := by
  rcases h with h | h
  · exact sep_of_le h hb
  · exact (sep_of_le h ha).symm

theorem aco_sepD {a b : Word} {n k : Nat} (h : Sep a n b k) (hn : 0 < n) (hk : 0 < k)
    : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_cases h1 : a.toNat + n ≤ b.toNat
  · exact .inl h1
  by_cases h2 : b.toNat + k ≤ a.toNat
  · exact .inr h2
  exfalso
  by_cases hab : a.toNat ≤ b.toNat
  · apply h (b.toNat - a.toNat) (by omega) 0 hk
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  · apply h 0 hn (a.toNat - b.toNat) (by omega)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem aco_num {B Bf : Word} (F : Fr B 0x5A70) (sB : Sep B 0x5A70 Bf acBufLen) (bal : Bf.toNat % 4 = 0)
    (bhi : Bf.toNat + acBufLen ≤ 0x40000000) : AcoNum B Bf :=
  ⟨by have := F.lo; omega, F.hi, by have := F.al; omega, bhi, bal,
    aco_sepD sB (by decide) (by decide)⟩

theorem aco_bv {B x : Word} {k : Nat} (h : x.toNat = (B.toNat + (0x3A50 + k)) % 2 ^ 32) : x = acSlot B k := by
  apply BitVec.eq_of_toNat_eq; rw [h]; simp only [acSlot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem aco_bvB {B x : Word} {c : Nat} (h : x.toNat = (B.toNat + c) % 2 ^ 32) : x = B + BitVec.ofNat 32 c := by
  apply BitVec.eq_of_toNat_eq; rw [h]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

set_option hygiene false in
/-- An address the code computes from `sp` is a frame slot. -/
macro "aco_addr" : tactic => `(tactic| first
  | rfl
  | (apply aco_bv; (try simp only [aluEval, acSlot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]); omega)
  | (apply aco_bvB; (try simp only [aluEval, acSlot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]); omega))

set_option hygiene false in
/-- An alignment or a separation that the numbers decide. -/
macro "aco_num" : tactic => `(tactic| first
  | ((try simp only [aluEval, acSlot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]); omega)
  | (apply lowSep <;> first | decide | ((try simp only [aluEval, acSlot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]); omega))
  | (apply aco_sepN <;> (try simp only [aluEval, acSlot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]) <;> omega))

theorem aco_fixS {B Bf : Word} (N : AcoNum B Bf) {x : Word} (hx1 : B.toNat + 0x3A50 ≤ x.toNat)
    (hx2 : x.toNat < B.toNat + 0x5A70)
    (hx3 : x.toNat < B.toNat + 0x3A70 ∨ (B.toNat + 0x3A80 ≤ x.toNat ∧ x.toNat < B.toNat + 0x3DA0) ∨
      B.toNat + 0x5938 ≤ x.toNat) : AcoFix B Bf x := by
  have := N.b0; have := N.b1; have := N.f0; have := N.bb
  exact ⟨by aco_num, by aco_num, by aco_num, by aco_num⟩

theorem aco_fix_out {B Bf x : Word} (h1 : Sep x 1 B 0x5A70) (h2 : Sep x 1 Bf acBufLen) : AcoFix B Bf x := by
  refine ⟨?_, h1.subR (c := 0x3A70) (l := 0x10) (by decide), h1.subR (c := 0x3DA0) (l := 0x1B98) (by decide),
    h2.subR (c := 0x4000) (l := 0x2800) (by decide)⟩
  have := h1.subR (c := 0) (l := 0x3A50) (by decide); rwa [add_ofNat_zero] at this

/-- A frame slot's bytes that the loop doesn't write. -/
theorem aco_fixK {B Bf : Word} (N : AcoNum B Bf) {k j : Nat} (hj : j < 4)
    (hk : k + 4 ≤ 0x20 ∨ (0x30 ≤ k ∧ k + 4 ≤ 0x350) ∨ (0x1EE8 ≤ k ∧ k + 4 ≤ 0x2020)) :
    AcoFix B Bf (acSlot B k + BitVec.ofNat 32 j) := by
  have := N.b0; have := N.b1
  apply aco_fixS N <;> (try simp only [acSlot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat])
  · omega
  · omega
  · rcases hk with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl (by omega)
    · exact .inr (.inl ⟨by omega, by omega⟩)
    · exact .inr (.inr (by omega))

theorem aco_ldK {B Bf : Word} {M0 M : Word → BitVec 8} (N : AcoNum B Bf) (K : AcoKeep B Bf M0 M) {k : Nat}
    (hk : k + 4 ≤ 0x20 ∨ (0x30 ≤ k ∧ k + 4 ≤ 0x350) ∨ (0x1EE8 ≤ k ∧ k + 4 ≤ 0x2020)) :
    memLoad32 M (acSlot B k) = memLoad32 M0 (acSlot B k) :=
  memLoad32_congr fun j hj => K _ (aco_fixK N hj hk)

theorem AcoKeep.trans {B Bf : Word} {M0 M M' : Word → BitVec 8} (K : AcoKeep B Bf M0 M)
    (h : ∀ x, AcoFix B Bf x → M' x = M x) : AcoKeep B Bf M0 M' := fun x hx => (h x hx).trans (K x hx)

/-- A write below the frame. -/
theorem aco_wLow {B Bf x : Word} (h : AcoFix B Bf x) {c l : Nat} (hc : c + l ≤ 0x3A50) :
    Sep x 1 (B + BitVec.ofNat 32 c) l := h.1.subR hc

/-- A write to the scratch. -/
theorem aco_wScr {B Bf x : Word} (h : AcoFix B Bf x) {k l : Nat} (h1 : 0x350 ≤ k) (h2 : k + l ≤ 0x1EE8) :
    Sep x 1 (acSlot B k) l := by
  have := h.2.2.1.subR (c := k - 0x350) (l := l) (by omega)
  rwa [add_ofNat_assoc, show 0x3A50 + 0x350 + (k - 0x350) = 0x3A50 + k by omega] at this

/-- A write to the loop's words. -/
theorem aco_wW {B Bf x : Word} (h : AcoFix B Bf x) {k l : Nat} (h1 : 0x20 ≤ k) (h2 : k + l ≤ 0x30) :
    Sep x 1 (acSlot B k) l := by
  have := h.2.1.subR (c := k - 0x20) (l := l) (by omega)
  rwa [add_ofNat_assoc, show 0x3A50 + 0x20 + (k - 0x20) = 0x3A50 + k by omega] at this

/-- A write to `doc`. -/
theorem aco_wDoc {B Bf x : Word} (h : AcoFix B Bf x) : Sep x 1 (Bf + 0x4000) 0x2800 := h.2.2.2

theorem aco_st32W {B Bf : Word} {M : Word → BitVec 8} {k : Nat} {v : Word} (h1 : 0x20 ≤ k) (h2 : k + 4 ≤ 0x30) :
    ∀ x, AcoFix B Bf x → memStore32 M (acSlot B k) v x = M x := fun x hx =>
  memStore32_get_sep (aco_wW hx h1 h2).symm

theorem aco_st32S {B Bf : Word} {M : Word → BitVec 8} {k : Nat} {v : Word} (h1 : 0x350 ≤ k) (h2 : k + 4 ≤ 0x1EE8) :
    ∀ x, AcoFix B Bf x → memStore32 M (acSlot B k) v x = M x := fun x hx =>
  memStore32_get_sep (aco_wScr hx h1 h2).symm

theorem aco_st8S {B Bf : Word} {M : Word → BitVec 8} {k : Nat} {v : BitVec 8} (h1 : 0x350 ≤ k) (h2 : k + 1 ≤ 0x1EE8) :
    ∀ x, AcoFix B Bf x → memStore8 M (acSlot B k) v x = M x := fun x hx =>
  memStore8_ne fun e => aco_wScr hx h1 h2 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])

theorem aco_slotAdd (B : Word) (k : Nat) (o : Word) : acSlot B k + o = acSlot B (k + o.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp only [acSlot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem aco_addSlot (B : Word) (k : Nat) (o : Word) : o + acSlot B k = acSlot B (k + o.toNat) := by
  rw [BitVec.add_comm]; exact aco_slotAdd B k o

theorem aco_sp0 (B : Word) : (B + 0x3A50 : Word) = acSlot B 0 := rfl

set_option hygiene false in
/-- Folds the code's `sp`-relative addresses into `acSlot`. -/
macro "aco_simp" : tactic => `(tactic|
  simp only [aluEval, aco_slotAdd, aco_addSlot, BitVec.reduceToNat, Nat.reduceAdd, BitVec.reduceAdd])

theorem aco_ne {x y : Word} (h : x.toNat ≠ y.toNat) : x ≠ y := fun e => h (congrArg _ e)

set_option hygiene false in
/-- Two frame slots differ. -/
macro "aco_neq" : tactic => `(tactic| (apply aco_ne; simp only [acSlot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega))

/-! ## Role keys -/

theorem aco_rkC {b b' : Nat → BitVec 8} {dj : Json} {role : Bytes} (h : ∀ o, o < 0x540 → b' o = b o) :
    AcoRk b dj role → AcoRk b' dj role := by
  rintro (⟨h0, h1⟩ | ⟨t, es, hr, hb⟩)
  · exact .inl ⟨by rw [h 0 (by decide)]; exact h0, by rw [h 1 (by decide)]; exact h1⟩
  · exact .inr ⟨t, es, hr, hb.congr h⟩

/-- A `RoleKeys` the code read has no error tag. -/
theorem aco_rk0 {b : Nat → BitVec 8} {t : Nat} {es : List (Bytes × Option TufKey)}
    (h : RkB b t (es.map C3.Json.rkTag)) : b 0 ≠ 0xFE := by
  have h0 := (h.2.2.2 0 (by decide)).2.2.2
  cases es with
  | nil => simp only [List.map_nil, List.getD_nil] at h0; rw [h0]; decide
  | cons e es =>
    obtain ⟨id, k⟩ := e
    cases k with
    | none => simp only [List.map_cons, List.getD_cons_zero, C3.Json.rkTag, Option.map_none] at h0; rw [h0]; decide
    | some k =>
      cases k <;>
        simp only [List.map_cons, List.getD_cons_zero, C3.Json.rkTag, Option.map_some, keyTag, RkKeyB] at h0 <;>
        rw [h0.1] <;> decide

/-- `AcoRk` with the error tag ruled out. -/
theorem aco_rkOk {b : Nat → BitVec 8} {dj : Json} {role : Bytes} (h : AcoRk b dj role) (h0 : b 0 ≠ 0xFE) :
    ∃ t es, roleKeys dj role = some (t, es) ∧ RkB b t (es.map C3.Json.rkTag) := by
  rcases h with ⟨e, _⟩ | h
  · exact absurd e h0
  · exact h

/-- Each key `decode_key` gives has the tag and length `RoleKeys::met` expects. -/
theorem aco_spki {pfx s p : Bytes} {n : Nat} (h : spkiPoint pfx n s = some p) : p.length = n := by
  unfold spkiPoint at h
  cases h1 : readExpect pfx s with
  | none => simp [h1] at h
  | some q =>
    simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
    by_cases h2 : (q.length == n) = true
    · simp only [require, h2] at h; cases h; exact (beq_iff_eq.mp h2)
    · simp only [require, h2] at h; cases h

theorem aco_dk {j : Json} {k : TufKey} (h : decodeKey j = some k) :
    ((keyTag k).1 = 0 ∧ (keyTag k).2.length = 65) ∨ ((keyTag k).1 = 1 ∧ (keyTag k).2.length = 97) ∨
      ((keyTag k).1 = 2 ∧ (keyTag k).2.length = 32) := by
  unfold decodeKey at h
  simp only [Option.bind_eq_bind] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨kt, -, sc, -, pk, -, h⟩ := h
  split at h
  · simp only [Option.map_eq_map, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨p, ⟨s, -, hp⟩, rfl⟩ := h
    exact .inl ⟨rfl, aco_spki hp⟩
  split at h
  · simp only [Option.map_eq_map, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨p, ⟨s, -, hp⟩, rfl⟩ := h
    exact .inr (.inl ⟨rfl, aco_spki hp⟩)
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨kk, -, h⟩ := h
    by_cases h2 : (kk.length == 32) = true
    · simp [require, h2] at h
      subst h; exact .inr (.inr ⟨rfl, beq_iff_eq.mp h2⟩)
    · simp [require, h2] at h
  · cases h

theorem aco_rkwf {dj : Json} {role : Bytes} {t : Nat} {es : List (Bytes × Option TufKey)}
    (h : roleKeys dj role = some (t, es)) : RkWf (es.map C3.Json.rkTag) := by
  intro e he k hk
  obtain ⟨⟨id, ok⟩, hm, rfl⟩ := List.mem_map.mp he
  simp only [C3.Json.rkTag, Option.map_eq_some_iff] at hk
  obtain ⟨k', hk', rfl⟩ := hk
  subst hk'
  unfold roleKeys at h
  simp only [require, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨r, -, th, -, -, -, keys, -, arr, -, ids, -, -, -, h⟩ := h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨id', -, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, he⟩ := he
  simp only [Option.bind_eq_some_iff] at he
  obtain ⟨j, -, hj⟩ := he
  exact aco_dk hj
/-- The version check: `vh:vl` is one more than `hi:lo`. -/
theorem aco_ver {lo hi vl vh : Word} (h1 : lo &&& hi ≠ 0xFFFFFFFF)
    (h2 : ((lo + 1) ^^^ vl) ||| ((if (lo + 1).ult 1 then (1 : Word) else 0) + hi ^^^ vh) = 0) :
    vh.toNat * 2 ^ 32 + vl.toNat = hi.toNat * 2 ^ 32 + lo.toNat + 1 := by
  change _ = 0#32 at h2
  rw [BitVec.or_eq_zero_iff] at h2
  obtain ⟨e1, e2⟩ := h2
  change _ = 0#32 at e1 e2
  rw [BitVec.xor_eq_zero_iff] at e1 e2
  subst e1; subst e2
  have hl := lo.isLt; have hh := hi.isLt
  have key : lo.toNat = 2 ^ 32 - 1 → hi.toNat ≠ 2 ^ 32 - 1 := fun a b => h1 (by
    rw [show lo = 0xFFFFFFFF from BitVec.eq_of_toNat_eq (by rw [a]; rfl),
      show hi = 0xFFFFFFFF from BitVec.eq_of_toNat_eq (by rw [b]; rfl)]; rfl)
  have t1 : (1 : Word).toNat = 1 := rfl
  have t0 : (0 : Word).toNat = 0 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_add, t1]
  split <;> rename_i hs <;> simp only [BitVec.ult_eq_decide, BitVec.toNat_add, t1, decide_eq_true_eq] at hs
  · rw [t1]; have := key (by omega); omega
  · rw [t0]; omega

/-! ## Calls -/

/-- A call to `memcpy` from the closure, with `sp` at `S`. -/
theorem aco_memcpy {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o dst src S : Word}
    {N : Nat} (s : St Mx AC n off g) (hcd : CodeIn Mx AC bootMainClosure0Code) (hs : CodeIn Mx MCS memcpyStubCode)
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : AC + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (AC + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = dst) (ha1 : g a1 = src) (ha2 : g a2 = BitVec.ofNat 32 N)
    (E : McEnv Mx (MCS + 8) dst src (S + 0xFFFFFFF0) N) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (off + 8) (reg n') ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → n'.mem x = copyBytes Mx dst src N x) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, sp2, a02, mem2, k2⟩ := memcpy_correct n1 MCS (AC + BitVec.ofNat 32 (off + 8)) dst src N
    (fun i hi => by rw [mem1]; exact hs i hi) (by decide) pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [mem1, r1 sp (by decide), hsp]; exact E)
  rw [r1 sp (by decide), hsp, mem1] at mem2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2,
    fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hra => ?_⟩
  by_cases hs : r = sp
  · subst hs; rw [sp2, r1 sp (by decide)]
  · rw [k2 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs, r1 r hra]

/-- The registers `memcpy` may change. -/
def acoMcClob (q : Fin 32) : Bool := q.val ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30]

theorem aco_mcRegs {n' : Machine} {g : Fin 32 → Word}
    (k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → reg n' r = g r) :
    ∀ q, acoMcClob q = false → reg n' q = g q := fun q hq => by
  apply k q <;> (intro e; subst e; revert hq; decide)

/-- Copying `N` bytes from `src` to `dst` in the frame, below 0x1EE8: what
memory holds afterwards. -/
theorem aco_mcMem {M M' : Word → BitVec 8} {B dst src : Word} {N : Nat}
    (hN : N < 2 ^ 32) (h : ∀ x, Sep (B + 0x3A50 + 0xFFFFFFF0) 16 x 1 → M' x = copyBytes M dst src N x) :
    (∀ x, Sep x 1 (B + 0x3A40) 16 → Sep x 1 dst N → M' x = M x) ∧
      ∀ j, j < N → Sep (dst + BitVec.ofNat 32 j) 1 (B + 0x3A40) 16 →
        M' (dst + BitVec.ofNat 32 j) = M (src + BitVec.ofNat 32 j) := by
  have e : (B + 0x3A50 + 0xFFFFFFF0 : Word) = B + 0x3A40 := by rw [BitVec.add_assoc]; rfl
  rw [e] at h
  refine ⟨fun x h1 h2 => ?_, fun j hj h1 => ?_⟩
  · rw [h x h1.symm, copyBytes_sep h2.symm (Nat.le_refl _)]
  · rw [h _ h1.symm, copyBytes_in hj hN]

/-! ## The stage's context -/

/-- What the stage starts from, at `n0`. -/
structure AcoCtx (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat) (B Bf g t r : Word)
    (v : Nat → Word) (M0 : Word → BitVec 8) (docs : List Bytes) (first : TufRoot) (n0 : Machine) : Prop where
  rom : RomRead flash R romBase romCode
  env : ∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcRootsEnv R romBase romCode B Bf M
  F : Fr B 0x5A70
  sB : Sep B 0x5A70 Bf acBufLen
  N : AcoNum B Bf
  hR : R ≤ 0x38D0
  inv : AcInv B Bf g t v M0 n0
  pre : AcRootsPre flash B Bf r docs first n0
  gap : AcRootsGap

section ctx

variable {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat} {B Bf g t r : Word}
  {v : Nat → Word} {M0 : Word → BitVec 8} {docs : List Bytes} {first : TufRoot} {n0 : Machine}

theorem AcoCtx.envK (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {M : Word → BitVec 8}
    (K : AcoKeep B Bf n0.mem M) : AcRootsEnv R romBase romCode B Bf M :=
  C.env M fun x h1 h2 => (K x (aco_fix_out h1 h2)).trans (C.inv.out x h1 h2)

theorem AcoCtx.code (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {M : Word → BitVec 8}
    (K : AcoKeep B Bf n0.mem M) : CodeIn M AC bootMainClosure0Code := (C.envK K).ac

/-- The registers the loop keeps are `n0`'s. -/
abbrev AcoKR (n0 n : Machine) : Prop := ∀ q, acoKept q = true → reg n q = reg n0 q

/-- The registers every exit keeps: `sp`, `gp`, and `tp`. -/
def acoKeptA (q : Fin 32) : Bool := q.val ∈ [2, 3, 4]

abbrev AcoKRA (n0 n : Machine) : Prop := ∀ q, acoKeptA q = true → reg n q = reg n0 q

theorem AcoKR.a {n0 n : Machine} (KR : AcoKR n0 n) : AcoKRA n0 n := fun q hq =>
  KR q (by revert hq; revert q; decide)

theorem AcoCtx.sp (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine}
    (KR : AcoKRA n0 n) : reg n sp = B + 0x3A50 := (KR C3.RV32.sp (by decide)).trans C.inv.sp

theorem AcoCtx.ainv (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine}
    (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKRA n0 n) : AcInv B Bf g t v M0 n := by
  have N := C.N
  have := N.b0; have := N.b1
  refine ⟨C.sp KR, (KR 3 (by decide)).trans C.inv.gp, (KR 4 (by decide)).trans C.inv.tp, fun k hk => ?_,
    fun x h1 h2 => (K x (aco_fix_out h1 h2)).trans (C.inv.out x h1 h2)⟩
  rw [← C.inv.saves k hk]
  exact memLoad32_congr fun j hj => K _ (aco_fixS N (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega))

/-- The stage's goal from `n`. -/
abbrev AcoG (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (docs : List Bytes) (first : TufRoot)
    (n0 n : Machine) : Prop :=
  AcStage B Bf g t r v M0 n 0x836 (AcRootsPost B Bf docs first n0)

theorem aco_pre {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n n1 : Machine} {o : Nat}
    {Q : Machine → Prop} (h : Steps n n1) (e : AcStage B Bf g t r v M0 n1 o Q) : AcStage B Bf g t r v M0 n o Q := by
  obtain ⟨n', s, q⟩ := e
  exact ⟨n', h.trans s, q⟩

/-- `s5 = a0`, at 0x7D4. -/
def acoL1 : List BInstr := [.alu .add (21 : Fin 32) x0 a0]

/-- `a0 = s6; s5 = a0`, at 0x7D2. -/
def acoL2 : List BInstr := [.alu .add a0 x0 (22 : Fin 32), .alu .add (21 : Fin 32) x0 a0]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **A rejection** at 0x7D4, with the code in the low byte of `a0`. -/
theorem aco_leaf (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine}
    (s : St n.mem AC n 0x7D4 (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKRA n0 n)
    (hc : (reg n a0 &&& 0xFF).toNat < 0x27) : AcoG B Bf g t r v M0 docs first n0 n := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x7D6) acoL1 (C.code K) (by decide) ⟨trivial, trivial⟩
  have M1 : n1.mem = n.mem := u1.mem
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [M1]; exact K
  have KR1 : AcoKRA n0 n1 := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acoL1]; revert hq; revert q; decide)]
    exact KR q hq
  refine ⟨n1, c1, .inr ⟨C.ainv K1 KR1, .inl (.inr (.inr (.inl ⟨u1.pc, ?_, ?_⟩)))⟩⟩
  · rw [aco_ldK C.N K1 (by decide)]; exact C.pre.2.2.2.2.1
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoL1, upd, ↓reduceIte, aluEval]
    rw [hz, show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add]; exact hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A rejection** at 0x7D2, with the code in the low byte of `s6`. -/
theorem aco_leaf2 (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine}
    (s : St n.mem AC n 0x7D2 (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKRA n0 n)
    (hc : (reg n (22 : Fin 32) &&& 0xFF).toNat < 0x27) : AcoG B Bf g t r v M0 docs first n0 n := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x7D6) acoL2 (C.code K) (by decide) ⟨trivial, trivial, trivial⟩
  have M1 : n1.mem = n.mem := u1.mem
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [M1]; exact K
  have KR1 : AcoKRA n0 n1 := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acoL2]; revert hq; revert q; decide)]
    exact KR q hq
  refine ⟨n1, c1, .inr ⟨C.ainv K1 KR1, .inl (.inr (.inr (.inl ⟨u1.pc, ?_, ?_⟩)))⟩⟩
  · rw [aco_ldK C.N K1 (by decide)]; exact C.pre.2.2.2.2.1
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoL2, upd, ↓reduceIte, aluEval]
    simp only [hz, show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add]; exact hc

/-- A block, then a jump to a rejection. -/
theorem aco_jmp {n : Machine} {off off' : Nat} {blk : List BInstr} {o len : Word} {tgt : Nat}
    (s : St n.mem AC n off (reg n)) (hc : CodeIn n.mem AC bootMainClosure0Code)
    (he : blockEnd bootMainClosure0Code off blk = some off') (hok : BlockOk AC bootMainClosure0Code.length blk (n.mem, reg n))
    (hm : (runBlock blk (n.mem, reg n)).1 = n.mem)
    (hf : fetchRel bootMainClosure0Code off' = some (.jal 0 o, len))
    (hn : BitVec.ofNat 32 off' + o = BitVec.ofNat 32 tgt) (hev : (AC + BitVec.ofNat 32 off' + o).getLsbD 0 = false) :
    ∃ n', Steps n n' ∧ St n.mem AC n' tgt (reg n') ∧ ∀ q, reg n' q = (runBlock blk (n.mem, reg n)).2 q := by
  obtain ⟨n1, c1, u1⟩ := s.block blk hc he hok
  rw [hm] at u1
  obtain ⟨n2, e2, t2⟩ := u1.jump hc hf hn (by rw [u1.pc]; exact hev)
  exact ⟨n2, c1.trans (.single e2), ⟨t2.pc, t2.mem, fun _ => rfl⟩, t2.regs⟩

theorem aco_ze8 : ∀ b : BitVec 8, ((b.zeroExtend 32) &&& 0xFF).toNat = b.toNat := by decide

theorem aco_zeq : ∀ b : BitVec 8, (b.zeroExtend 32 == 0) = (b == 0) := by decide

theorem aco_ld88 {M : Word → BitVec 8} {a b x : Word} {u w : BitVec 8} (h1 : Sep a 1 x 4) (h2 : Sep b 1 x 4) :
    memLoad32 (memStore8 (memStore8 M a u) b w) x = memLoad32 M x := by
  rw [memLoad32_store8_sep h2, memLoad32_store8_sep h1]

/-- After the loop, at 0x788: record the trusted root's tag byte. -/
def acoE1 : List BInstr := [.lw a0 sp 0x2C, .lw a1 sp 0x1C]

def acoE2 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add a2 sp a0, .lbu a0 a2 0x0,
  .lw a1 sp 0x28, .sb a2 a1 0x10, .lui a1 0x1000, .aluImm .add a1 a1 0x310, .alu .add a1 a1 sp,
  .sb a2 (22 : Fin 32) 0x11]

def acoE3 : List BInstr := [.lbu (21 : Fin 32) a1 0x1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The loop's exit**, at 0x584 with every root read: copy the trusted
root's first two bytes back, then end at 0x836, or reject with the
`expires` error. -/
theorem aco_exit (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine}
    (s : St n.mem AC n 0x584 (reg n)) (I : AcoInv B Bf docs first n0 n docs.length) :
    AcoG B Bf g t r v M0 docs first n0 n := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2
  have hz := s.zero
  have rsp0 : reg n sp = acSlot B 0 := C.sp (AcoKR.a I.regs)
  have CC := C.code I.keep
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x588) acoE1 CC (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoE1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp0]; aco_simp; exact ⟨by aco_num, by aco_num⟩)
  have M1 : n1.mem = n.mem := u1.mem
  have a0v : reg n1 a0 = BitVec.ofNat 32 docs.length := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoE1, upd, ↓reduceIte]; rw [rsp0]; aco_simp; exact I.cnt
  have a1v : reg n1 a1 = BitVec.ofNat 32 docs.length := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoE1, upd, ↓reduceIte]; rw [rsp0]; aco_simp
    rw [aco_ldK N I.keep (by decide)]; exact C.pre.2.2.1
  have r1 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 11 → reg n1 q = reg n q := fun q h0 h1 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acoE1]; revert h0 h1; revert q; decide)]
  have t1 : St n1.mem AC n1 0x588 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have C1 : CodeIn n1.mem AC bootMainClosure0Code := by rw [M1]; exact CC
  obtain ⟨n2, e2, t2⟩ := t1.taken C1 0x788 ac_at_588 (by decide)
    (by rw [a0v, a1v]; simp only [branchTaken, beq_iff_eq])
  have hz2 := t2.zero
  obtain ⟨n3, c3, u3⟩ := t2.block (off' := 0x7A8) acoE2 C1 (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoE2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r1 sp (by decide) (by decide), rsp0]; aco_simp; exact ⟨by aco_num, by aco_num, by aco_num⟩)
  have M3 : n3.mem = memStore8 (memStore8 n.mem (acSlot B 0x1320)
      ((memLoad32 n.mem (acSlot B 0x28)).extractLsb' 0 8)) (acSlot B 0x1321) ((reg n (22 : Fin 32)).extractLsb' 0 8) := by
    rw [u3.mem]; simp only [runBlock, BInstr.run, acoE2]; simp +decide only [upd, ↓reduceIte]
    rw [r1 sp (by decide) (by decide), r1 22 (by decide) (by decide), rsp0, M1]; aco_simp
  have a0v3 : reg n3 a0 = (n.mem (acSlot B 0x1310)).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoE2, upd, ↓reduceIte]
    rw [r1 sp (by decide) (by decide), rsp0, M1]; aco_simp
  have a1v3 : reg n3 a1 = acSlot B 0x1310 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoE2, upd, ↓reduceIte]
    rw [r1 sp (by decide) (by decide), rsp0]; aco_simp
  have KR3 : AcoKR n0 n3 := fun q hq => by
    rw [u3.regs, runBlock_reg _ _ _ q hz2 (by simp only [acoE2]; revert hq; revert q; decide),
      r1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    exact I.regs q hq
  have K3 : AcoKeep B Bf n0.mem n3.mem := I.keep.trans fun x hx => by
    rw [M3, aco_st8S (by decide) (by decide) x hx, aco_st8S (by decide) (by decide) x hx]
  have t3 : St n3.mem AC n3 0x7A8 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have C3 := C.code K3
  obtain ⟨prev, hf, hS, hT⟩ := I.fold
  have hT := hT (.inr rfl)
  rw [List.take_of_length_le (Nat.le_refl _)] at hf
  have n20 : acSlot B 0x1320 ≠ acSlot B 0x1310 := by aco_neq
  have n21 : acSlot B 0x1321 ≠ acSlot B 0x1310 := by aco_neq
  have n2x : acSlot B 0x1320 ≠ acSlot B 0x1311 := by aco_neq
  have n2y : acSlot B 0x1321 ≠ acSlot B 0x1311 := by aco_neq
  have m10 : n3.mem (acSlot B 0x1310) = n.mem (acSlot B 0x1310) := by
    rw [M3, memStore8_ne n21.symm, memStore8_ne n20.symm]
  by_cases h0 : n.mem (acSlot B 0x1310) = 0
  · obtain ⟨n4, e4, t4⟩ := t3.taken C3 0x836 ac_at_7a8 (by decide)
      (by simp only [branchTaken, a0v3, t3.zero, h0]; decide)
    have M4 : n4.mem = n3.mem := t4.mem
    have K4 : AcoKeep B Bf n0.mem n4.mem := by rw [M4]; exact K3
    have KR4 : AcoKR n0 n4 := fun q hq => by rw [t4.regs]; exact KR3 q hq
    refine ⟨n4, c1.trans ((Steps.single e2).trans (c3.trans (.single e4))), .inr ⟨C.ainv K4 KR4.a, .inr ⟨t4.pc, ?_⟩⟩⟩
    obtain ⟨e, he, hlo, hhi⟩ := hT.2.1 h0
    have L : ∀ k, (k + 4 ≤ 0x1320 ∨ 0x1322 ≤ k) → k < 0x2000 →
        memLoad32 n4.mem (acSlot B k) = memLoad32 n.mem (acSlot B k) := fun k h1 h2 => by
      rw [M4, M3]; exact aco_ld88 (by aco_num) (by aco_num)
    refine ⟨prev, hf, K4, KR4, ?_, ?_, ?_, ?_, e, he, ?_, ?_⟩
    · rw [L 0x20 (by decide) (by decide), L 0x24 (by decide) (by decide)]; exact hS.ver
    · refine aco_rkC (fun o ho => ?_) hS.keys
      rw [M4, M3]
      simp only [acoTB]
      by_cases o0 : o = 0
      · subst o0; simp only [↓reduceIte, add_ofNat_zero]
        rw [memStore8_ne (by aco_neq), memStore8_same]
      by_cases o1 : o = 1
      · subst o1; rw [if_neg (show (1 : Nat) ≠ 0 by decide), if_pos rfl]
        rw [aco_slotAdd, show 0x1320 + (BitVec.ofNat 32 1).toNat = 0x1321 from rfl, memStore8_same]
      · simp only [o0, o1, ↓reduceIte]
        rw [memStore8_ne (by aco_neq), memStore8_ne (by aco_neq)]
    · refine aco_rkC (fun o ho => ?_) hT.1
      rw [M4, M3, memStore8_ne (by aco_neq), memStore8_ne (by aco_neq)]
    · rw [M4, m10]; exact h0
    · rw [L 0x1318 (by decide) (by decide)]; exact hlo
    · rw [L 0x131C (by decide) (by decide)]; exact hhi
  · obtain ⟨n4, e4, t4⟩ := t3.notTaken C3 0x7AA ac_at_7a8 (by decide)
      (by simp only [branchTaken, a0v3, t3.zero, aco_zeq]; simp only [beq_eq_false_iff_ne]; exact h0)
    have M4 : n4.mem = n3.mem := t4.mem
    have t4' : St n3.mem AC n4 0x7AA (reg n3) := t4
    obtain ⟨n5, c5, u5⟩ := t4'.block (off' := 0x7AE) acoE3 C3 (by decide) ⟨trivial, trivial⟩
    have M5 : n5.mem = n3.mem := u5.mem
    have s5v : reg n5 (21 : Fin 32) = (n.mem (acSlot B 0x1311)).zeroExtend 32 := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoE3, upd, ↓reduceIte]
      rw [a1v3]; aco_simp; rw [M3, memStore8_ne n2y.symm, memStore8_ne n2x.symm]
    have t5 : St n5.mem AC n5 0x7AE (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have C5 : CodeIn n5.mem AC bootMainClosure0Code := by rw [M5]; exact C3
    obtain ⟨n6, e6, t6⟩ := t5.jump C5 ac_at_7ae (off' := 0x7D6) (by decide)
      (by rw [t5.pc, BitVec.add_assoc]; decide)
    have M6 : n6.mem = n3.mem := t6.mem.trans M5
    have K6 : AcoKeep B Bf n0.mem n6.mem := by rw [M6]; exact K3
    have KR6 : AcoKRA n0 n6 := fun q hq => by
      rw [t6.regs, u5.regs, runBlock_reg _ _ _ q t4'.zero (by simp only [acoE3]; revert hq; revert q; decide)]
      exact KR3.a q hq
    refine ⟨n6, c1.trans ((Steps.single e2).trans (c3.trans ((Steps.single e4).trans
      (c5.trans (.single e6))))), .inr ⟨C.ainv K6 KR6, .inl (.inr (.inr (.inl ⟨t6.pc, ?_, ?_⟩)))⟩⟩
    · rw [aco_ldK N K6 (by decide)]; exact C.pre.2.2.2.2.1
    · rw [t6.regs, s5v, aco_ze8]; exact hT.2.2 h0

theorem aco_so (B : Word) (k o : Nat) (h : o < 2 ^ 32) : acSlot B k + BitVec.ofNat 32 o = acSlot B (k + o) := by
  rw [aco_slotAdd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem aco_expC {B : Word} {M M' : Word → BitVec 8} {md : Meta}
    (h : ∀ j, j < 16 → M' (acSlot B 0x1310 + BitVec.ofNat 32 j) = M (acSlot B 0x1310 + BitVec.ofNat 32 j)) :
    AcoExp B M md → AcoExp B M' md := by
  have h0 : M' (acSlot B 0x1310) = M (acSlot B 0x1310) := by
    simpa only [add_ofNat_zero] using h 0 (by decide)
  have h1 : M' (acSlot B 0x1311) = M (acSlot B 0x1311) := by
    have := h 1 (by decide); rwa [aco_so B _ _ (by decide)] at this
  have hw : ∀ k, k = 0x1318 ∨ k = 0x131C → memLoad32 M' (acSlot B k) = memLoad32 M (acSlot B k) :=
    fun k hk => memLoad32_congr fun j hj => by
      rw [aco_so B k j (by omega), show k + j = 0x1310 + (k - 0x1310 + j) by omega, ← aco_so B _ _ (by omega)]
      exact h _ (by omega)
  rintro ⟨e1, e2⟩
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [h0] at z
    obtain ⟨e, he, l, hh⟩ := e1 z
    exact ⟨e, he, by rw [hw _ (.inl rfl)]; exact l, by rw [hw _ (.inr rfl)]; exact hh⟩
  · rw [h0] at z; rw [h1]; exact e2 z

set_option maxRecDepth 100000 in
/-- **A copy** of `N` bytes from `sp + ks` to `sp + kd`, both in the scratch. -/
theorem aco_mc (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {off : Nat}
    {imm o : Word} {kd ks N : Nat} (s : St n.mem AC n off (reg n)) (K : AcoKeep B Bf n0.mem n.mem)
    (KR : AcoKRA n0 n) (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : AC + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (AC + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = acSlot B kd) (ha1 : reg n a1 = acSlot B ks) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hd : 0x350 ≤ kd) (hdN : kd + N ≤ 0x1EE8) (hs : 0x350 ≤ ks) (hsN : ks + N ≤ 0x1EE8)
    (hsep : kd + N ≤ ks ∨ ks + N ≤ kd) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (off + 8) (reg n') ∧
      (∀ x, Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B kd) N → n'.mem x = n.mem x) ∧
      (∀ j, j < N → n'.mem (acSlot B kd + BitVec.ofNat 32 j) = n.mem (acSlot B ks + BitVec.ofNat 32 j)) ∧
      ∀ q, acoMcClob q = false → reg n' q = reg n q := by
  have N0 := C.N
  have := N0.b0; have := N0.b1; have := N0.b2
  have E := C.envK K
  have hm1 : (MCS + 8 : Word).toNat + memcpyBodyCode.length ≤ 2 ^ 32 := by decide
  have hm2 : 0x40000000 ≤ (MCS + 8 : Word).toNat := by decide
  have e : (B + 0x3A50 + 0xFFFFFFF0 : Word) = B + 0x3A40 := by rw [BitVec.add_assoc]; rfl
  have ME : McEnv n.mem (MCS + 8) (acSlot B kd) (acSlot B ks) (B + 0x3A50 + 0xFFFFFFF0) N := by
    rw [e]
    exact ⟨E.mcb, lowSep (by aco_num) hm2 hm1, lowSep (by aco_num) hm2 hm1, by aco_num, by aco_num, by aco_num,
      by aco_num, by aco_num, by aco_num, by aco_num⟩
  obtain ⟨n', c, s', hm, hr⟩ := aco_memcpy s E.ac E.mcs h1 h2 hb he8 (C.sp KR) ha0 ha1 ha2 ME
  obtain ⟨f1, f2⟩ := aco_mcMem (by omega) hm
  refine ⟨n', c, s', f1, fun j hj => f2 j hj (by aco_num), aco_mcRegs hr⟩

/-- `a1 = sp + 0x890; a2 = 0x53E; a0 = sp + 0x1322`, at 0x75A. -/
def acoF1 : List BInstr := [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x91, .aluImm .add a2 x0 0x53E,
  .lui a0 0x1000, .aluImm .add a0 a0 0x322, .alu .add a0 a0 sp]

/-- `[sp + 0x2C] += 1; [sp + 0x24] = s10; [sp + 0x20] = s3`, at 0x776. -/
def acoF2 : List BInstr := [.lw a0 sp 0x2C, .aluImm .add a0 a0 0x1, .sw sp a0 0x2C, .sw sp (26 : Fin 32) 0x24,
  .sw sp (19 : Fin 32) 0x20]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The end of an iteration**, at 0x75A: the next root's keys at
`sp + 0x890`, its version in `s3:s10`. Move them into place and loop. -/
theorem aco_F (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {i : Nat}
    {next : TufRoot} (s : St n.mem AC n 0x75A (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKR n0 n)
    (hi : i < docs.length) (hc : memLoad32 n.mem (acSlot B 0x2C) = BitVec.ofNat 32 i)
    (hv : (reg n (19 : Fin 32)).toNat * 2 ^ 32 + (reg n (26 : Fin 32)).toNat = next.version)
    (hw : (memLoad32 n.mem (acSlot B 0x28)).toNat < 256) (hb : (reg n (22 : Fin 32)).toNat < 256)
    (hk : AcoRk (acoTBk B n.mem (memLoad32 n.mem (acSlot B 0x28)) (reg n (22 : Fin 32)) 0x88E) next.md.signed
      (ascii!"root")) (hsrc : ∃ (M' : Word → BitVec 8) (P : Word) (L : Nat), JVal true (memBytes M' P L) next.md.signed)
    (hf : (docs.take (i + 1)).foldlM acoStep first = some next)
    (ht : i + 1 = docs.length → AcoTail B n.mem next)
    (IH : ∀ n', St n'.mem AC n' 0x584 (reg n') → AcoInv B Bf docs first n0 n' (i + 1) →
      AcoG B Bf g t r v M0 docs first n0 n') :
    AcoG B Bf g t r v M0 docs first n0 n := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2
  have hz := s.zero
  have rsp0 : reg n sp = acSlot B 0 := C.sp KR.a
  have CC := C.code K
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x76E) acoF1 CC (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoF1]; simp +decide only [upd, ↓reduceIte, true_and, and_true])
  have M1 : n1.mem = n.mem := u1.mem
  have a0v : reg n1 a0 = acSlot B 0x1322 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoF1, upd, ↓reduceIte]; rw [rsp0]; aco_simp
  have a1v : reg n1 a1 = acSlot B 0x890 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoF1, upd, ↓reduceIte]; rw [rsp0]; aco_simp
  have a2v : reg n1 a2 = BitVec.ofNat 32 0x53E := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoF1, upd, ↓reduceIte]
  have r1 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 11 → q.val ≠ 12 → reg n1 q = reg n q := fun q h0 h1 h2 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acoF1]; revert h0 h1 h2; revert q; decide)]
  have t1 : St n1.mem AC n1 0x76E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [M1]; exact K
  have KR1 : AcoKR n0 n1 := fun q hq => by
    rw [r1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    exact KR q hq
  obtain ⟨n2, c2, t2, f2, g2, r2⟩ := aco_mc C t1 K1 KR1.a ac_at_76e ac_at_772 (by decide) (by decide) a0v a1v a2v
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [M1] at f2 g2
  have r21 : ∀ q : Fin 32, acoMcClob q = false → q.val ≠ 10 → q.val ≠ 11 → q.val ≠ 12 → reg n2 q = reg n q :=
    fun q h h0 h1 h2 => (r2 q h).trans (r1 q h0 h1 h2)
  have hz2 := t2.zero
  have rsp2 : reg n2 sp = acSlot B 0 := by rw [r21 sp (by decide) (by decide) (by decide) (by decide), rsp0]
  have C2 : CodeIn n2.mem AC bootMainClosure0Code := C.code (K.trans fun x hx => f2 x (aco_wLow hx (by decide))
    (aco_wScr hx (by decide) (by decide)))
  obtain ⟨n3, c3, u3⟩ := t2.block (off' := 0x780) acoF2 C2 (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoF2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp2]; aco_simp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | aco_num | exact ⟨by aco_num, by aco_num⟩)
  have c2v : memLoad32 n2.mem (acSlot B 0x2C) = BitVec.ofNat 32 i := by
    rw [← hc]; exact memLoad32_congr fun j hj => f2 _ (by aco_num) (by aco_num)
  have M3 : n3.mem = memStore32 (memStore32 (memStore32 n2.mem (acSlot B 0x2C) (BitVec.ofNat 32 i + 1))
      (acSlot B 0x24) (reg n (26 : Fin 32))) (acSlot B 0x20) (reg n (19 : Fin 32)) := by
    rw [u3.mem]; simp only [runBlock, BInstr.run, acoF2]; simp +decide only [upd, ↓reduceIte]
    rw [rsp2, r21 26 (by decide) (by decide) (by decide) (by decide),
      r21 19 (by decide) (by decide) (by decide) (by decide)]; aco_simp; rw [c2v]
  have t3 : St n3.mem AC n3 0x780 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have r3 : ∀ q : Fin 32, q.val ≠ 10 → reg n3 q = reg n2 q := fun q h0 => by
    rw [u3.regs, runBlock_reg _ _ _ q hz2 (by simp only [acoF2]; revert h0; revert q; decide)]
  -- What the iteration's end keeps.
  have W3 : ∀ x, Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B 0x1322) 0x53E → Sep x 1 (acSlot B 0x20) 8 →
      Sep x 1 (acSlot B 0x2C) 4 → n3.mem x = n.mem x := fun x h1 h2 h3 h4 => by
    have s0 : Sep x 1 (acSlot B 0x20) 4 := by
      have := h3.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have s4 : Sep x 1 (acSlot B 0x24) 4 := by
      have := h3.subR (c := 4) (l := 4) (by decide); rwa [aco_slotAdd] at this
    rw [M3, memStore32_get_sep s0.symm, memStore32_get_sep s4.symm, memStore32_get_sep h4.symm, f2 x h1 h2]
  have K3 : AcoKeep B Bf n0.mem n3.mem := K.trans fun x hx =>
    W3 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wW hx (by decide) (by decide))
      (aco_wW hx (by decide) (by decide))
  have KR3 : AcoKR n0 n3 := fun q hq => by
    rw [r3 q (by revert hq; revert q; decide), r21 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    exact KR q hq
  have C3 := C.code K3
  obtain ⟨n4, e4, t4⟩ := t3.jump C3 ac_at_780 (off' := 0x584) (by decide) (by rw [t3.pc, BitVec.add_assoc]; decide)
  have M4 : n4.mem = n3.mem := t4.mem
  have KR4 : AcoKR n0 n4 := fun q hq => by rw [t4.regs]; exact KR3 q hq
  have w28 : memLoad32 n4.mem (acSlot B 0x28) = memLoad32 n.mem (acSlot B 0x28) := by
    rw [M4]; exact memLoad32_congr fun j hj => W3 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
  have s64 : reg n4 (22 : Fin 32) = reg n (22 : Fin 32) := by
    rw [t4.regs, r3 22 (by decide), r21 22 (by decide) (by decide) (by decide) (by decide)]
  refine aco_pre (c1.trans (c2.trans (c3.trans (.single e4)))) (IH n4 ⟨t4.pc, rfl, fun _ => rfl⟩ ⟨by omega,
    by rw [M4]; exact K3, KR4, ?_, next, hf, ⟨?_, ?_, ?_, ?_, hsrc⟩, ?_⟩)
  · rw [M4, M3, memLoad32_store32_sep (by aco_num), memLoad32_store32_sep (by aco_num), memLoad32_store32_same]
    have hL : docs.length ≤ 64 := C.pre.2.1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
  · rw [M4, M3, memLoad32_store32_same, memLoad32_store32_sep (by aco_num), memLoad32_store32_same, ← hv]
  · rw [w28]; exact hw
  · rw [s64]; exact hb
  · rw [w28, s64]
    refine aco_rkC (fun o ho => ?_) hk
    simp only [acoTB, acoTBk]
    split
    · rfl
    split
    · rfl
    rename_i o0 o1
    rw [M4, M3, memStore32_get_sep (by aco_num), memStore32_get_sep (by aco_num), memStore32_get_sep (by aco_num),
      aco_so B _ _ (by omega), show 0x1320 + o = 0x1322 + (o - 2) by omega, ← aco_so B _ _ (by omega),
      g2 (o - 2) (by omega), aco_so B _ _ (by omega), aco_so B _ _ (by omega),
      show 0x890 + (o - 2) = 0x88E + o by omega]
  · intro h
    obtain ⟨T1, T2⟩ := ht (h.resolve_left (by omega))
    refine ⟨aco_rkC (fun o ho => ?_) T1, aco_expC (fun j hj => ?_) T2⟩
    · rw [M4]; exact W3 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
    · rw [M4]; exact W3 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)

/-! ## The callees, from the loop -/

/-- `q` and the `l` bytes after it are in `doc`. -/
def AcoIn (Bf q : Word) (l : Nat) : Prop := Bf.toNat + 0x4000 ≤ q.toNat ∧ q.toNat + l ≤ Bf.toNat + 0x6800

theorem aco_ds (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {c l : Nat}
    (h : c + l ≤ 0x5A70) : Sep (B + BitVec.ofNat 32 c) l (BitVec.ofNat 32 (img% dataWindowAddress))
      (img% dataWindowSize) := by
  have := C.F.dsep.sub (c := 0x1A0 + c) (l := l) (by omega)
  rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c from
    BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (0xFFFFFE60 : Word).toNat = 2 ^ 32 - 0x1A0 from rfl]
      omega)] at this

theorem aco_ro (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {M : Word → BitVec 8}
    (K : AcoKeep B Bf n0.mem M) {c l : Nat} (h : c + l ≤ 0x5A70) :
    Sep (B + BitVec.ofNat 32 c) l (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) :=
  (C.envK K).ro.sub h

theorem aco_inSep {B Bf q : Word} {l : Nat} (N : AcoNum B Bf) (h : AcoIn Bf q l) {c k : Nat} (hc : c + k ≤ 0x5A70) :
    Sep (B + BitVec.ofNat 32 c) k q l := by
  have := N.b0; have := N.b1; have := N.f0; have := N.bb; have := h.1; have := h.2
  aco_num

/-- What `RoleKeys::met` leaves, back in the loop at `off'`. -/
def AcoMetOut (B : Word) (n n' : Machine) (off' : Nat) (md : Meta) (dj : Json) (role : Bytes) : Prop :=
  St n'.mem AC n' off' (reg n') ∧ (∀ x, Sep x 1 (B + 0x130) 0x3920 → n'.mem x = n.mem x) ∧
    (∀ r, r ∉ jClob → r ≠ ra → reg n' r = reg n r) ∧
    (reg n' a0 &&& 1 = 0 → reg n' a0 = 0 ∧ (reg n' a1 ≠ 0 → thresholdMet md dj role = some true)) ∧
    (reg n' a0 &&& 1 ≠ 0 → (reg n' a1 &&& 0xFF).toNat < 0x27)

set_option maxRecDepth 100000 in
/-- **A call to `RoleKeys::met`** from the loop, with the keys at `sp + kR`
and the message and signatures in `doc`, named at `sp + 0x1ED0`. -/
theorem aco_met (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {off : Nat}
    {imm o : Word} {kR : Nat} {q1 q2 : Word} {l1 l2 tt : Nat} {md : Meta} {dj sj : Json} {role : Bytes}
    {es : List (Bytes × Option TufKey)} {M : Word → BitVec 8} {DP : Word} {DL : Nat}
    (s : St n.mem AC n off (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKRA n0 n)
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : AC + BitVec.ofNat 32 off + imm + o = TRM)
    (hret : (AC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = AC + BitVec.ofNat 32 (off + 8))
    (ha0 : reg n a0 = acSlot B kR) (ha1 : reg n a1 = acSlot B 0x1ED0) (hk1 : 0x350 ≤ kR) (hk2 : kR + 0x540 ≤ 0x1ED0)
    (hk3 : kR % 4 = 0) (hq1 : AcoIn Bf q1 l1) (hq2 : AcoIn Bf q2 l2)
    (hA0 : memLoad32 n.mem (acSlot B 0x1ED0) = q1) (hA4 : memLoad32 n.mem (acSlot B 0x1ED4) = BitVec.ofNat 32 l1)
    (hA8 : memLoad32 n.mem (acSlot B 0x1ED8) = q2) (hAC : memLoad32 n.mem (acSlot B 0x1EDC) = BitVec.ofNat 32 l2)
    (hrk : roleKeys dj role = some (tt, es)) (hdj : JVal true (memBytes M DP DL) dj)
    (hR : RkAt n.mem (acSlot B kR) tt (es.map C3.Json.rkTag))
    (hmsg : memBytes n.mem q1 l1 = encode md.signed) (hsj : JVal true (memBytes n.mem q2 l2) sj)
    (hps : (sj.asArr >>= List.mapM sigPair) = some md.sigs) :
    ∃ n', Steps n n' ∧ (Halting n' ∨ AcoMetOut B n n' (off + 8) md dj role) := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2; have := N.f0; have := N.bb
  have := hq1.1; have := hq1.2; have := hq2.1; have := hq2.2
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (C.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [mem1]; exact K
  have sp1 : reg n1 sp = (B + 0x130) + BitVec.ofNat 32 0x3920 := by
    rw [r1 sp (by decide), C.sp KR, BitVec.add_assoc]; rfl
  obtain ⟨n2, c2, q⟩ := C.gap.met n1 (retAddr := AC + BitVec.ofNat 32 (off + 8)) (s := B + 0x130) (MP := q1)
    (R := acSlot B kR) (A := acSlot B 0x1ED0)
    (SP := q2) (ML := l1) (SL := l2) (md := md) (dj := dj) (sj := sj) (role := role) (es := es) (t := tt)
    pc1 (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) sp1
    (by rw [regs1]; simp [upd]) hret (by aco_num) (by aco_num) (by aco_num) (aco_ds C (by decide))
    (aco_ro C K (by decide))
    (fun M hM => (C.envK (fun x hx => (hM x ((hx.1.subR (c := 0x130) (l := 0x3920) (by decide)))).trans
      (by rw [mem1]; exact K x hx))).rm)
    (by aco_num) (by aco_num) (by aco_num) (by omega) (by omega) (aco_inSep N hq1 (by decide)) (by omega)
    (by omega) (by omega) (aco_inSep N hq2 (by decide)) (by aco_num) (by aco_num)
    (by rw [mem1]; exact hA0) (by rw [mem1, aco_so B _ _ (by decide)]; exact hA4)
    (by rw [mem1, aco_so B _ _ (by decide)]; exact hA8) (by rw [mem1, aco_so B _ _ (by decide)]; exact hAC) hrk hdj (by rw [mem1]; exact hR) (aco_rkwf hrk) (by rw [mem1]; exact hmsg)
    (by rw [mem1]; exact hsj) hps
  refine ⟨n2, c1.trans c2, ?_⟩
  rcases q with h | ⟨hp, hM, hr, h0, h1'⟩
  · exact .inl h
  · refine .inr ⟨⟨by rw [hp], rfl, fun _ => rfl⟩, fun x hx => by rw [hM x hx, mem1], fun r hr' hra => ?_, h0, h1'⟩
    rw [hr r hr', r1 r hra]

set_option maxRecDepth 100000 in
/-- **A call to `RoleKeys::read`** from the loop, for the role named by the
`RN` bytes at `RP`, in the root whose `signed` bytes are at `q1`, into
`sp + kO`. -/
theorem aco_rk (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {off : Nat}
    {imm o : Word} {kO : Nat} {q1 RP : Word} {l1 RN : Nat} {role : Bytes} {dj : Json}
    (s : St n.mem AC n off (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKRA n0 n)
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : AC + BitVec.ofNat 32 off + imm + o = TRK)
    (hret : (AC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = AC + BitVec.ofNat 32 (off + 8))
    (ha0 : reg n a0 = acSlot B kO) (ha1 : reg n a1 = q1) (ha2 : reg n a2 = BitVec.ofNat 32 l1) (ha3 : reg n a3 = RP)
    (ha4 : reg n a4 = BitVec.ofNat 32 RN) (hk1 : 0x350 ≤ kO) (hk2 : kO + 0x540 ≤ 0x1EE8) (hk3 : kO % 4 = 0)
    (hq1 : AcoIn Bf q1 l1) (hRP : Sep (B + 0x2E60) 3056 RP RN) (hRN : RN < 2 ^ 32)
    (hrole : memBytes n.mem RP RN = role) (hj : JVal true (memBytes n.mem q1 l1) dj) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (off + 8) (reg n') ∧
      (∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B kO) 0x540 → n'.mem x = n.mem x) ∧
      (∀ r, r ∉ jClob → r ≠ ra → reg n' r = reg n r) ∧ AcoRk (fun o => n'.mem (acSlot B kO + BitVec.ofNat 32 o)) dj role := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2; have := N.f0; have := N.bb
  have := hq1.1; have := hq1.2
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (C.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [mem1]; exact K
  obtain ⟨n2, c2, pc2, res, hr⟩ := tufRoleKeysRead_correct n1 (out := acSlot B kO) (P := q1) (RP := RP) (N := l1)
    (RN := RN) (C.envK K1).rm.a.rk pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [r1 a4 (by decide)]; exact ha4) (s := B + 0x2E60)
    (by rw [r1 sp (by decide), C.sp KR, BitVec.add_assoc]; rfl) (by rw [regs1]; simp [upd]) hret
    (by aco_num) (by aco_num) (aco_ro C K (by decide)) (by aco_num) (by aco_num) (by aco_num) (by omega)
    (by omega) (by omega) (aco_inSep N hq1 (by decide)) hRN hRP
  rw [mem1, hrole] at res
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, ?_, fun r hr' hra => ?_, ?_⟩
  · intro x h1 h2
    cases hm : rkModel (memBytes n.mem q1 l1) role with
    | error e => rw [hm] at res; exact res.1 x h1 h2
    | ok p => obtain ⟨_, _⟩ := p; rw [hm] at res; exact res.1 x h1 h2
  · rw [hr r hr', r1 r hra]
  · cases hm : rkModel (memBytes n.mem q1 l1) role with
    | error e =>
      rw [hm] at res
      have he := C.gap.rk _ _ e hm
      refine .inl ⟨?_, ?_⟩
      · show n2.mem (acSlot B kO + BitVec.ofNat 32 0) = _
        rw [add_ofNat_zero]; exact res.2.1
      · show (n2.mem (acSlot B kO + BitVec.ofNat 32 1)).toNat < _
        rw [show BitVec.ofNat 32 1 = (1 : Word) from rfl, res.2.2, BitVec.toNat_ofNat]; omega
    | ok p =>
      obtain ⟨tt, es'⟩ := p
      rw [hm] at res
      have hs := rkModel_spec (role := role) hj
      rw [hm] at hs
      obtain ⟨⟨t', es⟩, hr2, he⟩ := Option.map_eq_some_iff.mp hs.symm
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .inr ⟨t', es, hr2, res.2⟩

set_option maxRecDepth 100000 in
/-- **A call to `tuf::expires`** from the loop, on the `signed` bytes of
`md` at `q1`, into `sp + 0x1310`. -/
theorem aco_tex (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {off : Nat}
    {imm o : Word} {q1 : Word} {l1 : Nat} {md : Meta}
    (s : St n.mem AC n off (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKRA n0 n)
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : AC + BitVec.ofNat 32 off + imm + o = TEX)
    (hret : (AC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = AC + BitVec.ofNat 32 (off + 8))
    (ha0 : reg n a0 = acSlot B 0x1310) (ha1 : reg n a1 = q1) (ha2 : reg n a2 = BitVec.ofNat 32 l1)
    (hq1 : AcoIn Bf q1 l1) (hj : JVal true (memBytes n.mem q1 l1) md.signed) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (off + 8) (reg n') ∧
      (∀ x, Sep x 1 (B + 0x391C) 308 → Sep x 1 (acSlot B 0x1310) 16 → n'.mem x = n.mem x) ∧
      (∀ r, r ∉ jClob → r ≠ ra → reg n' r = reg n r) ∧ AcoExp B n'.mem md := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2; have := N.f0; have := N.bb
  have := hq1.1; have := hq1.2
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (C.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [mem1]; exact K
  obtain ⟨n2, c2, pc2, res, hr⟩ := tufExpires_correct n1 (out := acSlot B 0x1310) (p := q1) (n := l1)
    (C.envK K1).tex pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (s := B + 0x391C)
    (by rw [r1 sp (by decide), C.sp KR, BitVec.add_assoc]; rfl) (by rw [regs1]; simp [upd]) hret
    (by aco_num) (by aco_num) (by aco_num) (aco_ro C K (by decide)) (by omega) (by omega) (by aco_num)
    (by aco_num) (by aco_num)
  rw [mem1] at res
  have hs := expiresModel_spec hj
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, ?_, fun r hr' hra => ?_, ?_⟩
  · intro x h1 h2
    cases hm : expiresModel (memBytes n.mem q1 l1) with
    | error e => rw [hm] at res; exact res.1 x h1 h2
    | ok e => rw [hm] at res; exact res.1 x h1 h2
  · rw [hr r hr', r1 r hra]
  · cases hm : expiresModel (memBytes n.mem q1 l1) with
    | error e =>
      rw [hm] at res
      have he := C.gap.ex _ e hm
      refine ⟨fun z => absurd (res.2.1.symm.trans z) (by decide), fun _ => ?_⟩
      have e1 : acSlot B 0x1310 + 1 = acSlot B 0x1311 := aco_so B 0x1310 1 (by decide)
      have := res.2.2
      rw [e1] at this
      rw [this, BitVec.toNat_ofNat]; omega
    | ok e =>
      rw [hm] at res hs
      obtain ⟨-, z, l, h⟩ := res
      rw [aco_slotAdd] at l h
      simp only [BitVec.reduceToNat, Nat.reduceAdd] at l h
      exact ⟨fun _ => ⟨e, hs.symm, l, h⟩, fun z' => absurd z z'⟩

set_option maxRecDepth 100000 in
/-- **A call to `tuf::parse_root`** from the loop, on the `l` bytes at
`doc`, into `sp + 0x1870`. -/
theorem aco_pr (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {off : Nat}
    {imm o : Word} {l : Nat}
    (s : St n.mem AC n off (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKRA n0 n)
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : AC + BitVec.ofNat 32 off + imm + o = TPR)
    (hret : (AC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = AC + BitVec.ofNat 32 (off + 8))
    (ha0 : reg n a0 = acSlot B 0x1870) (ha1 : reg n a1 = Bf + 0x4000) (ha2 : reg n a2 = BitVec.ofNat 32 l)
    (hl : l ≤ 0x2800) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (off + 8) (reg n') ∧
      PrRes n.mem n'.mem (B + 0x37FC) (acSlot B 0x1870) (prRes (Bf + 0x4000) (prModel (memBytes n.mem (Bf + 0x4000) l))) ∧
      (∀ r, r ∉ jClob → r ≠ ra → reg n' r = reg n r) := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2; have := N.f0; have := N.f1; have := N.bb
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (C.code K) h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [mem1]; exact K
  obtain ⟨n2, c2, pc2, res, hr⟩ := tufParseRoot_correct n1 (out := acSlot B 0x1870) (p := Bf + 0x4000) (n := l)
    (C.envK K1).pr pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (s := B + 0x37FC)
    (by rw [r1 sp (by decide), C.sp KR, BitVec.add_assoc]; rfl) (by rw [regs1]; simp [upd]) hret
    (by aco_num) (by aco_num) (aco_ro C K (by decide)) (by aco_num) (by aco_num) (by aco_num) (by omega)
    (by aco_num) (by aco_num) (by aco_num)
  rw [mem1] at res
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, res, fun r hr' hra => by
    rw [hr r hr', r1 r hra]⟩

/-- The role names are in `.rodata`, apart from `RoleKeys::read`'s frame. -/
theorem aco_nameSep (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {M : Word → BitVec 8}
    (K : AcoKeep B Bf n0.mem M) {k l : Nat} (hk : k + l ≤ 0x1400) :
    Sep (B + 0x2E60) 3056 (BitVec.ofNat 32 (0x3FCC4000 + k)) l := by
  have := (aco_ro C K (c := 0x2E60) (l := 3056) (by decide)).subR (c := k) (l := l) hk
  rwa [show BitVec.ofNat 32 (img% roWindowAddress) + BitVec.ofNat 32 k = BitVec.ofNat 32 (0x3FCC4000 + k) from
    BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] at this

theorem aco_tbkC {B : Word} {M M' : Word → BitVec 8} {w s6 : Word} {k : Nat} {dj : Json} {role : Bytes}
    (h : ∀ o, 2 ≤ o → o < 0x540 → M' (acSlot B k + BitVec.ofNat 32 o) = M (acSlot B k + BitVec.ofNat 32 o)) :
    AcoRk (acoTBk B M w s6 k) dj role → AcoRk (acoTBk B M' w s6 k) dj role :=
  aco_rkC fun o ho => by
    simp only [acoTBk]
    split
    · rfl
    split
    · rfl
    exact h o (by omega) ho

theorem aco_last {i L : Nat} (hL : L ≤ 64) (hi : i < L)
    (h : BitVec.ofNat 32 L + 0xFFFFFFFF = BitVec.ofNat 32 i) : i + 1 = L := by
  have h' : BitVec.ofNat 32 L + 0xFFFFFFFF + 1 = BitVec.ofNat 32 i + 1 := by rw [h]
  rw [BitVec.add_assoc, show (0xFFFFFFFF : Word) + 1 = 0 from by decide,
    show ∀ x : Word, x + 0 = x from BitVec.add_zero] at h'
  have h'' := congrArg BitVec.toNat h'
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl] at h''
  omega

theorem aco_lastE (i : Nat) : BitVec.ofNat 32 (i + 1) + 0xFFFFFFFF = BitVec.ofNat 32 i := by
  rw [show BitVec.ofNat 32 (i + 1) = BitVec.ofNat 32 i + 1 from BitVec.eq_of_toNat_eq (by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega),
    BitVec.add_assoc, show (1 : Word) + 0xFFFFFFFF = 0 from by decide,
    show ∀ x : Word, x + 0 = x from BitVec.add_zero]

/-- `a0 &= 1`, at 0x716. -/
def acoE4 : List BInstr := [.aluImm .and a0 a0 0x1]

/-- `a1 &= 1`, at 0x71A. -/
def acoE5 : List BInstr := [.aluImm .and a1 a1 0x1]

/-- `a0 = [sp + 0x2C]; a1 = [sp + 0x1C] - 1`, at 0x71E. -/
def acoE6 : List BInstr := [.lw a0 sp 0x2C, .lw a1 sp 0x1C, .aluImm .add a1 a1 0xFFFFFFFF]

/-- The arguments of `RoleKeys::read` for `targets`, at 0x728. -/
def acoE7 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x5D1, .aluImm .add a4 x0 0x7,
  .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (18 : Fin 32), .lui a3 0x3FCC4000, .aluImm .add a3 a3 0x20]

/-- The arguments of `tuf::expires`, at 0x746. -/
def acoE8 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add a0 a0 sp,
  .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (18 : Fin 32)]

/-- `s6 = a1`, at 0x7CA. -/
def acoE9 : List BInstr := [.alu .add (22 : Fin 32) x0 a1]

/-- `s6 = 0x23`, at 0x7CE. -/
def acoE10 : List BInstr := [.aluImm .add (22 : Fin 32) x0 0x23]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **After the second `RoleKeys::met`**, at 0x716: reject on an error or
a failed threshold; otherwise, for the last root, read its targets role
and its expiry, and end the iteration. -/
theorem aco_E (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {i : Nat}
    {next : TufRoot} {q1 : Word} {l1 : Nat}
    (s : St n.mem AC n 0x716 (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKR n0 n)
    (hi : i < docs.length) (hc : memLoad32 n.mem (acSlot B 0x2C) = BitVec.ofNat 32 i)
    (hv : (reg n (19 : Fin 32)).toNat * 2 ^ 32 + (reg n (26 : Fin 32)).toNat = next.version)
    (hw : (memLoad32 n.mem (acSlot B 0x28)).toNat < 256) (hb : (reg n (22 : Fin 32)).toNat < 256)
    (hk : AcoRk (acoTBk B n.mem (memLoad32 n.mem (acSlot B 0x28)) (reg n (22 : Fin 32)) 0x88E) next.md.signed
      (ascii!"root"))
    (hsrc : ∃ (M' : Word → BitVec 8) (P : Word) (L : Nat), JVal true (memBytes M' P L) next.md.signed)
    (hq1 : AcoIn Bf q1 l1) (h8 : reg n (8 : Fin 32) = q1) (h18 : reg n (18 : Fin 32) = BitVec.ofNat 32 l1)
    (hj : JVal true (memBytes n.mem q1 l1) next.md.signed)
    (hf : thresholdMet next.md next.md.signed (ascii!"root") = some true →
      (docs.take (i + 1)).foldlM acoStep first = some next)
    (hm0 : reg n a0 &&& 1 = 0 → reg n a1 ≠ 0 → thresholdMet next.md next.md.signed (ascii!"root") = some true)
    (hm1 : reg n a0 &&& 1 ≠ 0 → (reg n a1 &&& 0xFF).toNat < 0x27)
    (IH : ∀ n', St n'.mem AC n' 0x584 (reg n') → AcoInv B Bf docs first n0 n' (i + 1) →
      AcoG B Bf g t r v M0 docs first n0 n') :
    AcoG B Bf g t r v M0 docs first n0 n := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2
  have hz := s.zero
  have rsp0 : reg n sp = acSlot B 0 := C.sp KR.a
  have CC := C.code K
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x718) acoE4 CC (by decide) ⟨trivial, trivial⟩
  have M1 : n1.mem = n.mem := u1.mem
  have a0v : reg n1 a0 = reg n a0 &&& 1 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoE4, upd, ↓reduceIte, aluEval]
  have r1 : ∀ q : Fin 32, q.val ≠ 10 → reg n1 q = reg n q := fun q h0 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acoE4]; revert h0; revert q; decide)]
  have t1 : St n1.mem AC n1 0x718 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have C1 : CodeIn n1.mem AC bootMainClosure0Code := by rw [M1]; exact CC
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [M1]; exact K
  have KR1 : AcoKR n0 n1 := fun q hq => by rw [r1 q (by revert hq; revert q; decide)]; exact KR q hq
  by_cases e0 : ¬reg n a0 &&& 1 = 0
  · obtain ⟨n2, e2, t2⟩ := t1.taken C1 0x7CA ac_at_718 (by decide)
      (by simp only [branchTaken, a0v, t1.zero, bne_iff_ne, ne_eq]; exact e0)
    have t2' : St n2.mem AC n2 0x7CA (reg n2) := ⟨t2.pc, rfl, fun _ => rfl⟩
    have C2 : CodeIn n2.mem AC bootMainClosure0Code := by rw [t2.mem]; exact C1
    obtain ⟨n3, c3, t3, r3⟩ := aco_jmp (blk := acoE9) (off' := 0x7CC) (tgt := 0x7D2) t2' C2 (by decide)
      ⟨trivial, trivial⟩ rfl ac_at_7cc (by decide) (by decide)
    have M3 : n3.mem = n1.mem := t3.mem.trans t2.mem
    refine aco_pre (c1.trans ((Steps.single e2).trans c3)) (aco_leaf2 C ⟨t3.pc, rfl, fun _ => rfl⟩
      (by rw [M3]; exact K1) (fun q hq => ?_) ?_)
    · rw [r3 q, runBlock_reg _ _ _ q t2'.zero (by simp only [acoE9]; revert hq; revert q; decide), t2.regs]
      exact KR1.a q hq
    · rw [r3]; simp +decide only [runBlock, BInstr.run, acoE9, upd, ↓reduceIte, aluEval]
      rw [t2'.zero, show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, t2.regs, r1 a1 (by decide)]
      exact hm1 e0
  have e0 : reg n a0 &&& 1 = 0 := Decidable.not_not.mp e0
  obtain ⟨n2, e2, t2⟩ := t1.notTaken C1 0x71A ac_at_718 (by decide)
    (by simp only [branchTaken, a0v, t1.zero, e0]; decide)
  have t2' : St n1.mem AC n2 0x71A (reg n1) := t2
  obtain ⟨n3, c3, u3⟩ := t2'.block (off' := 0x71C) acoE5 C1 (by decide) ⟨trivial, trivial⟩
  have M3 : n3.mem = n.mem := u3.mem.trans M1
  have a1v : reg n3 a1 = reg n a1 &&& 1 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoE5, upd, ↓reduceIte, aluEval]
    rw [r1 a1 (by decide)]
  have r3 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 11 → reg n3 q = reg n q := fun q h0 h1 => by
    rw [u3.regs, runBlock_reg _ _ _ q t2'.zero (by simp only [acoE5]; revert h1; revert q; decide), r1 q h0]
  have t3 : St n3.mem AC n3 0x71C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have C3 : CodeIn n3.mem AC bootMainClosure0Code := by rw [M3]; exact CC
  have K3 : AcoKeep B Bf n0.mem n3.mem := by rw [M3]; exact K
  have KR3 : AcoKR n0 n3 := fun q hq => by
    rw [r3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq
  have c13 : Steps n n3 := c1.trans ((Steps.single e2).trans c3)
  by_cases e1 : reg n a1 &&& 1 = 0
  · obtain ⟨n4, e4, t4⟩ := t3.taken C3 0x7CE ac_at_71c (by decide)
      (by simp only [branchTaken, a1v, t3.zero, e1]; decide)
    have t4' : St n3.mem AC n4 0x7CE (reg n3) := t4
    obtain ⟨n5, c5, u5⟩ := t4'.block (off' := 0x7D2) acoE10 C3 (by decide) ⟨trivial, trivial⟩
    have M5 : n5.mem = n3.mem := u5.mem
    refine aco_pre (c13.trans ((Steps.single e4).trans c5)) (aco_leaf2 C ⟨u5.pc, rfl, fun _ => rfl⟩
      (by rw [M5]; exact K3) (fun q hq => ?_) ?_)
    · rw [u5.regs, runBlock_reg _ _ _ q t4'.zero (by simp only [acoE10]; revert hq; revert q; decide)]
      exact KR3.a q hq
    · rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoE10, upd, ↓reduceIte, aluEval]
      rw [t4'.zero]; decide
  have hT : thresholdMet next.md next.md.signed (ascii!"root") = some true :=
    hm0 e0 fun z => e1 (by rw [z]; rfl)
  have hF := hf hT
  obtain ⟨n4, e4, t4⟩ := t3.notTaken C3 0x71E ac_at_71c (by decide)
    (by simp only [branchTaken, a1v, t3.zero, beq_eq_false_iff_ne]; exact e1)
  have t4' : St n3.mem AC n4 0x71E (reg n3) := t4
  obtain ⟨n5, c5, u5⟩ := t4'.block (off' := 0x724) acoE6 C3 (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoE6]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r3 sp (by decide) (by decide), rsp0]; aco_simp; exact ⟨by aco_num, by aco_num⟩)
  have M5 : n5.mem = n.mem := u5.mem.trans M3
  have hL : docs.length ≤ 64 := C.pre.2.1
  have a0v5 : reg n5 a0 = BitVec.ofNat 32 i := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoE6, upd, ↓reduceIte]
    rw [r3 sp (by decide) (by decide), rsp0, M3]; aco_simp; exact hc
  have a1v5 : reg n5 a1 = BitVec.ofNat 32 docs.length + 0xFFFFFFFF := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoE6, upd, ↓reduceIte]
    rw [r3 sp (by decide) (by decide), rsp0, M3]; aco_simp
    rw [aco_ldK N K (by decide), C.pre.2.2.1]
  have r5 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 11 → reg n5 q = reg n q := fun q h0 h1 => by
    rw [u5.regs, runBlock_reg _ _ _ q t4'.zero (by simp only [acoE6]; revert h0 h1; revert q; decide), r3 q h0 h1]
  have t5 : St n5.mem AC n5 0x724 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have C5 : CodeIn n5.mem AC bootMainClosure0Code := by rw [M5]; exact CC
  have c15 : Steps n n5 := c13.trans ((Steps.single e4).trans c5)
  by_cases e2 : ¬i + 1 = docs.length
  · obtain ⟨n6, e6, t6⟩ := t5.taken C5 0x75A ac_at_724 (by decide) (by
      simp only [branchTaken, a0v5, a1v5, bne_iff_ne, ne_eq]
      intro h
      exact e2 (aco_last hL hi h))
    have T6 : St n6.mem AC n6 0x75A (reg n6) := ⟨t6.pc, rfl, fun _ => rfl⟩
    have M6 : n6.mem = n.mem := t6.mem.trans M5
    have r6 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 11 → reg n6 q = reg n q := fun q h0 h1 => by
      rw [t6.regs]; exact r5 q h0 h1
    refine aco_pre (c15.trans (.single e6)) (aco_F C T6 (by rw [M6]; exact K)
      (fun q hq => by rw [r6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq)
      hi (by rw [M6]; exact hc) (by rw [r6 19 (by decide) (by decide), r6 26 (by decide) (by decide)]; exact hv)
      (by rw [M6]; exact hw) (by rw [r6 22 (by decide) (by decide)]; exact hb)
      (by rw [M6, r6 22 (by decide) (by decide)]; exact hk) hsrc hF (fun h => absurd h e2) IH)
  have e2 : i + 1 = docs.length := Decidable.not_not.mp e2
  obtain ⟨n6, e6, t6⟩ := t5.notTaken C5 0x728 ac_at_724 (by decide) (by
    simp only [branchTaken, a0v5, a1v5, ← e2, aco_lastE, bne_self_eq_false])
  have t6' : St n5.mem AC n6 0x728 (reg n5) := t6
  obtain ⟨n7, c7, u7⟩ := t6'.block (off' := 0x73E) acoE7 C5 (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have M7 : n7.mem = n.mem := u7.mem.trans M5
  have z6 := t6'.zero
  have r7 : ∀ q : Fin 32, q ∉ jClob → reg n7 q = reg n q := fun q h => by
    rw [u7.regs, runBlock_reg _ _ _ q z6 (by simp only [acoE7]; revert h; revert q; decide),
      r5 q (by revert h; revert q; decide) (by revert h; revert q; decide)]
  have T7 : St n7.mem AC n7 0x73E (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have K7 : AcoKeep B Bf n0.mem n7.mem := by rw [M7]; exact K
  have KR7 : AcoKR n0 n7 := fun q hq => by rw [r7 q (by revert hq; revert q; decide)]; exact KR q hq
  have b0 : reg n7 a0 = acSlot B 0xDD0 := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, acoE7, upd, ↓reduceIte]
    rw [r5 sp (by decide) (by decide), rsp0]; aco_simp
  have b1 : reg n7 a1 = q1 := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, acoE7, upd, ↓reduceIte, aluEval]
    rw [show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, r5 8 (by decide) (by decide), h8]
  have b2 : reg n7 a2 = BitVec.ofNat 32 l1 := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, acoE7, upd, ↓reduceIte, aluEval]
    rw [show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, r5 18 (by decide) (by decide), h18]
  have b3 : reg n7 a3 = BitVec.ofNat 32 (0x3FCC4000 + 0x20) := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, acoE7, upd, ↓reduceIte, aluEval]
  have b4 : reg n7 a4 = BitVec.ofNat 32 7 := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, acoE7, upd, ↓reduceIte, aluEval]
  have := hq1.1; have := hq1.2; have := N.f0; have := N.bb
  obtain ⟨n8, c8, t8, f8, g8, k8⟩ := aco_rk C T7 K7 KR7.a ac_at_73e ac_at_742 (by decide) (by decide) b0 b1 b2 b3 b4
    (by decide) (by decide) (by decide) hq1 (aco_nameSep C K7 (by decide)) (by decide) (C.envK K7).tgts
    (by rw [M7]; exact hj) (role := ascii!"targets")
  have r8 : ∀ q : Fin 32, q ∉ jClob → q ≠ ra → reg n8 q = reg n q := fun q h h' => by
    rw [g8 q h h', r7 q h]
  have F8 : ∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0xDD0) 0x540 → n8.mem x = n.mem x :=
    fun x h1 h2 => by rw [f8 x h1 h2, M7]
  have K8 : AcoKeep B Bf n0.mem n8.mem := K.trans fun x hx =>
    F8 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide))
  have KR8 : AcoKR n0 n8 := fun q hq => by
    rw [r8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq
  have z8 := t8.zero
  obtain ⟨n9, c9, u9⟩ := t8.block (off' := 0x752) acoE8 (C.code K8) (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have M9 : n9.mem = n8.mem := u9.mem
  have r9 : ∀ q : Fin 32, q ∉ jClob → q ≠ ra → reg n9 q = reg n q := fun q h h' => by
    rw [u9.regs, runBlock_reg _ _ _ q z8 (by simp only [acoE8]; revert h; revert q; decide), r8 q h h']
  have T9 : St n9.mem AC n9 0x752 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have K9 : AcoKeep B Bf n0.mem n9.mem := by rw [M9]; exact K8
  have KR9 : AcoKR n0 n9 := fun q hq => by
    rw [r9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq
  have d0 : reg n9 a0 = acSlot B 0x1310 := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, acoE8, upd, ↓reduceIte]
    rw [r8 sp (by decide) (by decide), rsp0]; aco_simp
  have d1 : reg n9 a1 = q1 := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, acoE8, upd, ↓reduceIte, aluEval]
    rw [show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, r8 8 (by decide) (by decide), h8]
  have d2 : reg n9 a2 = BitVec.ofNat 32 l1 := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, acoE8, upd, ↓reduceIte, aluEval]
    rw [show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, r8 18 (by decide) (by decide), h18]
  have hj9 : JVal true (memBytes n9.mem q1 l1) next.md.signed := by
    rw [M9, memBytes_congr (M := n.mem) fun j hj => F8 _ (by aco_num) (by aco_num)]; exact hj
  obtain ⟨n10, c10, t10, f10, g10, x10⟩ := aco_tex C T9 K9 KR9.a ac_at_752 ac_at_756 (by decide) (by decide)
    d0 d1 d2 hq1 hj9
  have r10 : ∀ q : Fin 32, q ∉ jClob → q ≠ ra → reg n10 q = reg n q := fun q h h' => by
    rw [g10 q h h', r9 q h h']
  have F10 : ∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0xDD0) 0x540 → Sep x 1 (B + 0x391C) 308 →
      Sep x 1 (acSlot B 0x1310) 16 → n10.mem x = n.mem x :=
    fun x h1 h2 h3 h4 => by rw [f10 x h3 h4, M9, F8 x h1 h2]
  have K10 : AcoKeep B Bf n0.mem n10.mem := K.trans fun x hx =>
    F10 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wLow hx (by decide))
      (aco_wScr hx (by decide) (by decide))
  have L10 : ∀ k, (k + 4 ≤ 0xDD0 ∨ 0x1320 ≤ k) → k < 0x2000 →
      memLoad32 n10.mem (acSlot B k) = memLoad32 n.mem (acSlot B k) := fun k h1 h2 =>
    memLoad32_congr fun j hj => F10 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
  have w10 := L10 0x28 (by decide) (by decide)
  have s10 := r10 22 (by decide) (by decide)
  refine aco_pre (c15.trans ((Steps.single e6).trans (c7.trans (c8.trans (c9.trans c10)))))
    (aco_F C ⟨t10.pc, rfl, fun _ => rfl⟩ K10
      (fun q hq => by rw [r10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq)
      hi (by rw [L10 0x2C (by decide) (by decide)]; exact hc)
      (by rw [r10 19 (by decide) (by decide), r10 26 (by decide) (by decide)]; exact hv)
      (by rw [w10]; exact hw) (by rw [s10]; exact hb)
      (by rw [w10, s10]; exact aco_tbkC (fun o _ ho => F10 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)) hk)
      hsrc hF (fun _ => ⟨aco_rkC (fun o ho => ?_) k8, x10⟩) IH)
  rw [f10 _ (by aco_num) (by aco_num), M9]

theorem aco_zfe : ∀ b : BitVec 8, (b.zeroExtend 32 + 0xFFFFFF02 == 0) = (b == 0xFE) := by decide

theorem aco_zx8 : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide

theorem aco_zlt : ∀ b : BitVec 8, (b.zeroExtend 32).toNat < 256 := by decide

/-- The registers `aco_D` keeps: `sp`, `gp`, `tp`, `s0`, `s2`, `s3`, `s4`,
`s5`, `s7`, `s8`, `s9`, `s10`, and `s11`. -/
def acoDK (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 8, 18, 19, 20, 21, 23, 24, 25, 26, 27]

/-- `a0 &= 1; s6 = a1`, at 0x67E. -/
def acoD1 : List BInstr := [.aluImm .and a0 a0 0x1, .alu .add (22 : Fin 32) x0 a1]

/-- `s1 = s6 & 1`, at 0x686. -/
def acoD2 : List BInstr := [.aluImm .and (9 : Fin 32) (22 : Fin 32) 0x1]

/-- `a0 = 0x23`, at 0x7C4. -/
def acoD8 : List BInstr := [.aluImm .add a0 x0 0x23]

/-- The arguments of `RoleKeys::read` for `root`, at 0x68E. -/
def acoD3 : List BInstr := [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF870, .alu .add a0 a0 sp,
  .aluImm .add a4 x0 0x4, .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (18 : Fin 32), .lui a3 0x3FCC4000,
  .aluImm .add a3 a3 0x76E]

/-- Split the next root's `RoleKeys` at 0x6AC: its first byte to
`[sp + 0x28]`, its second to `s6`. -/
def acoD4 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add a0 a0 sp, .lbu a1 a0 0x560,
  .lbu (22 : Fin 32) a0 0x561, .sw sp a1 0x28, .aluImm .add a0 a1 0xFFFFFF02]

/-- The arguments of the copy to `sp + 0x890`, at 0x6C6. -/
def acoD5 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x91, .aluImm .add a2 x0 0x53E,
  .lui a1 0x2000, .aluImm .add a1 a1 0xFFFFF872, .alu .add a1 a1 sp]

/-- The first two bytes to `sp + 0x350`, and the arguments of the copy to
`sp + 0x352`, at 0x6E2. -/
def acoD6 : List BInstr := [.lw a0 sp 0x28, .sb sp a0 0x350, .sb sp (22 : Fin 32) 0x351, .aluImm .add a1 sp 0x7FF,
  .aluImm .add a1 a1 0x91, .aluImm .add a2 x0 0x53E, .aluImm .add a0 sp 0x352]

/-- The arguments of the second `RoleKeys::met`, at 0x704. -/
def acoD7 : List BInstr := [.aluImm .add a0 sp 0x350, .lui a1 0x2000, .aluImm .add a1 a1 0xFFFFFED0,
  .alu .add a1 a1 sp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **After the first `RoleKeys::met`**, at 0x67E: reject on an error or
a failed threshold; otherwise read the next root's root role, keep it as
the trusted root's, and check the next root's signatures against it. -/
theorem aco_D (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {i : Nat}
    {prev next : TufRoot} {q1 q2 : Word} {l1 l2 : Nat} {sj : Json}
    (s : St n.mem AC n 0x67E (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKR n0 n)
    (hi : i < docs.length) (hc : memLoad32 n.mem (acSlot B 0x2C) = BitVec.ofNat 32 i)
    (hv : (reg n (19 : Fin 32)).toNat * 2 ^ 32 + (reg n (26 : Fin 32)).toNat = next.version)
    (hq1 : AcoIn Bf q1 l1) (hq2 : AcoIn Bf q2 l2)
    (h8 : reg n (8 : Fin 32) = q1) (h18 : reg n (18 : Fin 32) = BitVec.ofNat 32 l1)
    (hA0 : memLoad32 n.mem (acSlot B 0x1ED0) = q1) (hA4 : memLoad32 n.mem (acSlot B 0x1ED4) = BitVec.ofNat 32 l1)
    (hA8 : memLoad32 n.mem (acSlot B 0x1ED8) = q2) (hAC : memLoad32 n.mem (acSlot B 0x1EDC) = BitVec.ofNat 32 l2)
    (hj : JVal true (memBytes n.mem q1 l1) next.md.signed)
    (hmsg : memBytes n.mem q1 l1 = encode next.md.signed) (hsj : JVal true (memBytes n.mem q2 l2) sj)
    (hps : (sj.asArr >>= List.mapM sigPair) = some next.md.sigs)
    (hf : thresholdMet next.md prev.md.signed (ascii!"root") = some true →
      thresholdMet next.md next.md.signed (ascii!"root") = some true →
      (docs.take (i + 1)).foldlM acoStep first = some next)
    (hm0 : reg n a0 &&& 1 = 0 → reg n a0 = 0 ∧
      (reg n a1 ≠ 0 → thresholdMet next.md prev.md.signed (ascii!"root") = some true))
    (hm1 : reg n a0 &&& 1 ≠ 0 → (reg n a1 &&& 0xFF).toNat < 0x27)
    (IH : ∀ n', St n'.mem AC n' 0x584 (reg n') → AcoInv B Bf docs first n0 n' (i + 1) →
      AcoG B Bf g t r v M0 docs first n0 n') :
    AcoG B Bf g t r v M0 docs first n0 n := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2; have := N.f0; have := N.bb
  have := hq1.1; have := hq1.2; have := hq2.1; have := hq2.2
  have hz := s.zero
  have rsp0 : reg n sp = acSlot B 0 := C.sp KR.a
  have CC := C.code K
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x682) acoD1 CC (by decide) ⟨trivial, trivial, trivial⟩
  have M1 : n1.mem = n.mem := u1.mem
  have a0v : reg n1 a0 = reg n a0 &&& 1 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoD1, upd, ↓reduceIte, aluEval]
  have s6v : reg n1 (22 : Fin 32) = reg n a1 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoD1, upd, ↓reduceIte, aluEval]
    rw [show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add]
  have r1 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 22 → reg n1 q = reg n q := fun q h0 h1 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acoD1]; revert h0 h1; revert q; decide)]
  have t1 : St n1.mem AC n1 0x682 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have C1 : CodeIn n1.mem AC bootMainClosure0Code := by rw [M1]; exact CC
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [M1]; exact K
  by_cases e0 : ¬reg n a0 &&& 1 = 0
  · obtain ⟨n2, e2, t2⟩ := t1.taken C1 0x7D2 ac_at_682 (by decide)
      (by simp only [branchTaken, a0v, t1.zero, bne_iff_ne, ne_eq]; exact e0)
    refine aco_pre (c1.trans (.single e2)) (aco_leaf2 C ⟨t2.pc, rfl, fun _ => rfl⟩
      (by rw [t2.mem]; exact K1) (fun q hq => ?_) ?_)
    · rw [t2.regs, r1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR.a q hq
    · rw [t2.regs, s6v]; exact hm1 e0
  have e0 : reg n a0 &&& 1 = 0 := Decidable.not_not.mp e0
  obtain ⟨n2, e2, t2⟩ := t1.notTaken C1 0x686 ac_at_682 (by decide)
    (by simp only [branchTaken, a0v, t1.zero, e0]; decide)
  have t2' : St n1.mem AC n2 0x686 (reg n1) := t2
  obtain ⟨n3, c3, u3⟩ := t2'.block (off' := 0x68A) acoD2 C1 (by decide) ⟨trivial, trivial⟩
  have M3 : n3.mem = n.mem := u3.mem.trans M1
  have s1v : reg n3 (9 : Fin 32) = reg n a1 &&& 1 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoD2, upd, ↓reduceIte, aluEval]; rw [s6v]
  have r3 : ∀ q : Fin 32, q.val ≠ 9 → q.val ≠ 10 → q.val ≠ 22 → reg n3 q = reg n q := fun q h0 h1 h2 => by
    rw [u3.regs, runBlock_reg _ _ _ q t2'.zero (by simp only [acoD2]; revert h0; revert q; decide), r1 q h1 h2]
  have t3 : St n3.mem AC n3 0x68A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have CD3 : CodeIn n3.mem AC bootMainClosure0Code := by rw [M3]; exact CC
  have K3 : AcoKeep B Bf n0.mem n3.mem := by rw [M3]; exact K
  have c13 : Steps n n3 := c1.trans ((Steps.single e2).trans c3)
  by_cases e1 : reg n a1 &&& 1 = 0
  · obtain ⟨n4, e4, t4⟩ := t3.taken CD3 0x7C4 ac_at_68a (by decide)
      (by simp only [branchTaken, s1v, t3.zero, e1]; decide)
    have t4' : St n4.mem AC n4 0x7C4 (reg n4) := ⟨t4.pc, rfl, fun _ => rfl⟩
    obtain ⟨n5, c5, t5, r5⟩ := aco_jmp (blk := acoD8) (off' := 0x7C8) (tgt := 0x7D4) t4'
      (by rw [t4.mem]; exact CD3) (by decide) ⟨trivial, trivial⟩ rfl ac_at_7c8 (by decide) (by decide)
    refine aco_pre (c13.trans ((Steps.single e4).trans c5)) (aco_leaf C ⟨t5.pc, rfl, fun _ => rfl⟩
      (by rw [t5.mem, t4.mem]; exact K3) (fun q hq => ?_) ?_)
    · rw [r5 q, runBlock_reg _ _ _ q t4'.zero (by simp only [acoD8]; revert hq; revert q; decide), t4.regs,
        r3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
      exact KR.a q hq
    · rw [r5]; simp +decide only [runBlock, BInstr.run, acoD8, upd, ↓reduceIte, aluEval]
      rw [t4'.zero]; decide
  have hT1 : thresholdMet next.md prev.md.signed (ascii!"root") = some true :=
    (hm0 e0).2 fun z => e1 (by rw [z]; rfl)
  obtain ⟨n4, e4, t4⟩ := t3.notTaken CD3 0x68E ac_at_68a (by decide)
    (by simp only [branchTaken, s1v, t3.zero, beq_eq_false_iff_ne]; exact e1)
  have t4' : St n3.mem AC n4 0x68E (reg n3) := t4
  obtain ⟨n5, c5, u5⟩ := t4'.block (off' := 0x6A4) acoD3 CD3 (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have M5 : n5.mem = n.mem := u5.mem.trans M3
  have z4 := t4'.zero
  have r5 : ∀ q : Fin 32, q ∉ jClob → q.val ≠ 9 → q.val ≠ 22 → reg n5 q = reg n q := fun q h h1 h2 => by
    rw [u5.regs, runBlock_reg _ _ _ q z4 (by simp only [acoD3]; revert h; revert q; decide),
      r3 q h1 (by revert h; revert q; decide) h2]
  have T5 : St n5.mem AC n5 0x6A4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have K5 : AcoKeep B Bf n0.mem n5.mem := by rw [M5]; exact K
  have KR5 : AcoKR n0 n5 := fun q hq => by
    rw [r5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    exact KR q hq
  have b0 : reg n5 a0 = acSlot B 0x1870 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoD3, upd, ↓reduceIte]
    rw [r3 sp (by decide) (by decide) (by decide), rsp0]; aco_simp
  have b1 : reg n5 a1 = q1 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoD3, upd, ↓reduceIte, aluEval]
    rw [show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, r3 8 (by decide) (by decide) (by decide), h8]
  have b2 : reg n5 a2 = BitVec.ofNat 32 l1 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoD3, upd, ↓reduceIte, aluEval]
    rw [show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, r3 18 (by decide) (by decide) (by decide), h18]
  have b3 : reg n5 a3 = BitVec.ofNat 32 (0x3FCC4000 + 0x76E) := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoD3, upd, ↓reduceIte, aluEval]
  have b4 : reg n5 a4 = BitVec.ofNat 32 4 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoD3, upd, ↓reduceIte, aluEval]
  obtain ⟨n6, c6, t6, f6, g6, k6⟩ := aco_rk C T5 K5 KR5.a ac_at_6a4 ac_at_6a8 (by decide) (by decide) b0 b1 b2 b3 b4
    (by decide) (by decide) (by decide) hq1 (aco_nameSep C K5 (by decide)) (by decide) (C.envK K5).root
    (by rw [M5]; exact hj) (role := ascii!"root")
  have r6 : ∀ q : Fin 32, q ∉ jClob → q ≠ ra → q.val ≠ 9 → q.val ≠ 22 → reg n6 q = reg n q :=
    fun q h h' h1 h2 => by rw [g6 q h h', r5 q h h1 h2]
  have F6 : ∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0x1870) 0x540 → n6.mem x = n.mem x :=
    fun x h1 h2 => by rw [f6 x h1 h2, M5]
  have K6 : AcoKeep B Bf n0.mem n6.mem := K.trans fun x hx =>
    F6 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide))
  have z6 := t6.zero
  obtain ⟨n7, c7, u7⟩ := t6.block (off' := 0x6C2) acoD4 (C.code K6) (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoD4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r6 sp (by decide) (by decide) (by decide) (by decide), rsp0]; aco_simp; exact ⟨by aco_num, by aco_num⟩)
  have rsp6 : reg n6 sp = acSlot B 0 := by rw [r6 sp (by decide) (by decide) (by decide) (by decide), rsp0]
  have M7 : n7.mem = memStore32 n6.mem (acSlot B 0x28) ((n6.mem (acSlot B 0x1870)).zeroExtend 32) := by
    rw [u7.mem]; simp only [runBlock, BInstr.run, acoD4]; simp +decide only [upd, ↓reduceIte]
    rw [rsp6]; aco_simp
  have x0 : reg n7 a0 = (n6.mem (acSlot B 0x1870)).zeroExtend 32 + 0xFFFFFF02 := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, acoD4, upd, ↓reduceIte]; rw [rsp6]; aco_simp
  have x22 : reg n7 (22 : Fin 32) = (n6.mem (acSlot B 0x1871)).zeroExtend 32 := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, acoD4, upd, ↓reduceIte]; rw [rsp6]; aco_simp
  have r7 : ∀ q : Fin 32, acoDK q = true → reg n7 q = reg n q := fun q hq => by
    rw [u7.regs, runBlock_reg _ _ _ q z6 (by simp only [acoD4]; revert hq; revert q; decide),
      r6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide)]
  have F7 : ∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0x1870) 0x540 → Sep x 1 (acSlot B 0x28) 4 →
      n7.mem x = n.mem x := fun x h1 h2 h3 => by rw [M7, memStore32_get_sep h3.symm, F6 x h1 h2]
  have K7 : AcoKeep B Bf n0.mem n7.mem := K.trans fun x hx =>
    F7 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wW hx (by decide) (by decide))
  have KR7 : AcoKR n0 n7 := fun q hq => by rw [r7 q (by revert hq; revert q; decide)]; exact KR q hq
  have t7 : St n7.mem AC n7 0x6C2 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have C7 := C.code K7
  have c17 : Steps n n7 := c13.trans ((Steps.single e4).trans (c5.trans (c6.trans c7)))
  have bR0 : n6.mem (acSlot B 0x1870 + BitVec.ofNat 32 0) = n6.mem (acSlot B 0x1870) := by rw [add_ofNat_zero]
  have bR1 : n6.mem (acSlot B 0x1870 + BitVec.ofNat 32 1) = n6.mem (acSlot B 0x1871) := by rw [aco_so B _ _ (by decide)]
  by_cases e2 : n6.mem (acSlot B 0x1870) = 0xFE
  · obtain ⟨n8, e8, t8⟩ := t7.taken C7 0x7D2 ac_at_6c2 (by decide)
      (by simp only [branchTaken, x0, t7.zero, aco_zfe, beq_iff_eq]; exact e2)
    refine aco_pre (c17.trans (.single e8)) (aco_leaf2 C ⟨t8.pc, rfl, fun _ => rfl⟩
      (by rw [t8.mem]; exact K7) (fun q hq => ?_) ?_)
    · rw [t8.regs]; exact KR7.a q hq
    · rw [t8.regs, x22, aco_ze8]
      rcases k6 with ⟨_, h1⟩ | ⟨_, _, _, hb⟩
      · have h1' : (n6.mem (acSlot B 0x1870 + BitVec.ofNat 32 1)).toNat < 0x27 := h1
        rw [bR1] at h1'; exact h1'
      · exact absurd (by rw [bR0]; exact e2) (aco_rk0 hb)
  obtain ⟨n8, e8, t8⟩ := t7.notTaken C7 0x6C6 ac_at_6c2 (by decide)
    (by simp only [branchTaken, x0, t7.zero, aco_zfe, beq_eq_false_iff_ne]; exact e2)
  obtain ⟨tt, es, hrk, hbR⟩ := aco_rkOk k6 (by rw [bR0]; exact e2)
  have t8' : St n7.mem AC n8 0x6C6 (reg n7) := t8
  obtain ⟨n9, c9, u9⟩ := t8'.block (off' := 0x6DA) acoD5 C7 (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have M9 : n9.mem = n7.mem := u9.mem
  have rsp7 : reg n7 sp = acSlot B 0 := by rw [r7 sp (by decide), rsp0]
  have d0 : reg n9 a0 = acSlot B 0x890 := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, acoD5, upd, ↓reduceIte]; rw [rsp7]; aco_simp
  have d1 : reg n9 a1 = acSlot B 0x1872 := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, acoD5, upd, ↓reduceIte]; rw [rsp7]; aco_simp
  have d2 : reg n9 a2 = BitVec.ofNat 32 0x53E := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, acoD5, upd, ↓reduceIte, aluEval]
  have r9 : ∀ q : Fin 32, acoDK q = true → reg n9 q = reg n q := fun q hq => by
    rw [u9.regs, runBlock_reg _ _ _ q t8'.zero (by simp only [acoD5]; revert hq; revert q; decide), r7 q hq]
  have s9 : reg n9 (22 : Fin 32) = reg n7 (22 : Fin 32) := by
    rw [u9.regs, runBlock_reg _ _ _ _ t8'.zero (by simp only [acoD5]; decide)]
  have T9 : St n9.mem AC n9 0x6DA (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have K9 : AcoKeep B Bf n0.mem n9.mem := by rw [M9]; exact K7
  have KR9 : AcoKR n0 n9 := fun q hq => by rw [r9 q (by revert hq; revert q; decide)]; exact KR q hq
  obtain ⟨n10, c10, t10, f10, g10, r10⟩ := aco_mc C T9 K9 KR9.a ac_at_6da ac_at_6de (by decide) (by decide)
    d0 d1 d2 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [M9] at f10 g10
  have F10 : ∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0x1870) 0x540 → Sep x 1 (acSlot B 0x28) 4 →
      Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B 0x890) 0x53E → n10.mem x = n.mem x :=
    fun x h1 h2 h3 h4 h5 => by rw [f10 x h4 h5, F7 x h1 h2 h3]
  have K10 : AcoKeep B Bf n0.mem n10.mem := K.trans fun x hx =>
    F10 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wW hx (by decide) (by decide))
      (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide))
  have r10' : ∀ q : Fin 32, acoDK q = true → reg n10 q = reg n q := fun q hq => by
    rw [r10 q (by revert hq; revert q; decide), r9 q hq]
  have KR10 : AcoKR n0 n10 := fun q hq => by rw [r10' q (by revert hq; revert q; decide)]; exact KR q hq
  have rsp10 : reg n10 sp = acSlot B 0 := by rw [r10' sp (by decide), rsp0]
  have s10 : reg n10 (22 : Fin 32) = (n6.mem (acSlot B 0x1871)).zeroExtend 32 := by
    rw [r10 _ (by decide), s9, x22]
  have w10 : memLoad32 n10.mem (acSlot B 0x28) = (n6.mem (acSlot B 0x1870)).zeroExtend 32 := by
    rw [memLoad32_congr (M := n7.mem) fun j hj => f10 _ (by aco_num) (by aco_num), M7, memLoad32_store32_same]
  have z10 := t10.zero
  obtain ⟨n11, c11, u11⟩ := t10.block (off' := 0x6FC) acoD6 (C.code K10) (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoD6]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp10]; aco_simp; exact ⟨by aco_num, by aco_num, by aco_num⟩)
  have M11 : n11.mem = memStore8 (memStore8 n10.mem (acSlot B 0x350) (n6.mem (acSlot B 0x1870)))
      (acSlot B 0x351) (n6.mem (acSlot B 0x1871)) := by
    rw [u11.mem]; simp only [runBlock, BInstr.run, acoD6]; simp +decide only [upd, ↓reduceIte]
    rw [rsp10]; aco_simp; rw [w10, s10, aco_zx8, aco_zx8]
  have m0 : ∀ x, Sep x 1 (acSlot B 0x350) 2 → n11.mem x = n10.mem x := fun x h => by
    rw [M11, memStore8_ne fun e => h 0 (by decide) 1 (by decide) (by rw [add_ofNat_zero, e, aco_so B _ _ (by decide)]),
      memStore8_ne fun e => h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])]
  have e0 : reg n11 a0 = acSlot B 0x352 := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, acoD6, upd, ↓reduceIte]; rw [rsp10]; aco_simp
  have e1 : reg n11 a1 = acSlot B 0x890 := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, acoD6, upd, ↓reduceIte]; rw [rsp10]; aco_simp
  have e2' : reg n11 a2 = BitVec.ofNat 32 0x53E := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, acoD6, upd, ↓reduceIte, aluEval]
  have r11 : ∀ q : Fin 32, acoDK q = true → reg n11 q = reg n q := fun q hq => by
    rw [u11.regs, runBlock_reg _ _ _ q z10 (by simp only [acoD6]; revert hq; revert q; decide), r10' q hq]
  have s11 : reg n11 (22 : Fin 32) = (n6.mem (acSlot B 0x1871)).zeroExtend 32 := by
    rw [u11.regs, runBlock_reg _ _ _ _ z10 (by simp only [acoD6]; decide), s10]
  have F11 : ∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0x1870) 0x540 → Sep x 1 (acSlot B 0x28) 4 →
      Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B 0x890) 0x53E → Sep x 1 (acSlot B 0x350) 2 →
      n11.mem x = n.mem x := fun x h1 h2 h3 h4 h5 h6 => by rw [m0 x h6, F10 x h1 h2 h3 h4 h5]
  have K11 : AcoKeep B Bf n0.mem n11.mem := K.trans fun x hx =>
    F11 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wW hx (by decide) (by decide))
      (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wScr hx (by decide) (by decide))
  have KR11 : AcoKR n0 n11 := fun q hq => by rw [r11 q (by revert hq; revert q; decide)]; exact KR q hq
  have T11 : St n11.mem AC n11 0x6FC (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  obtain ⟨n12, c12, t12, f12, g12, r12⟩ := aco_mc C T11 K11 KR11.a ac_at_6fc ac_at_700 (by decide) (by decide)
    e0 e1 e2' (by decide) (by decide) (by decide) (by decide) (by decide)
  have F12 : ∀ x, Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0x1870) 0x540 → Sep x 1 (acSlot B 0x28) 4 →
      Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B 0x890) 0x53E → Sep x 1 (acSlot B 0x350) 2 →
      Sep x 1 (acSlot B 0x352) 0x53E → n12.mem x = n.mem x :=
    fun x h1 h2 h3 h4 h5 h6 h7 => by rw [f12 x h4 h7, F11 x h1 h2 h3 h4 h5 h6]
  have K12 : AcoKeep B Bf n0.mem n12.mem := K.trans fun x hx =>
    F12 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wW hx (by decide) (by decide))
      (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wScr hx (by decide) (by decide))
      (aco_wScr hx (by decide) (by decide))
  have r12' : ∀ q : Fin 32, acoDK q = true → reg n12 q = reg n q := fun q hq => by
    rw [r12 q (by revert hq; revert q; decide), r11 q hq]
  have KR12 : AcoKR n0 n12 := fun q hq => by rw [r12' q (by revert hq; revert q; decide)]; exact KR q hq
  have s12 : reg n12 (22 : Fin 32) = (n6.mem (acSlot B 0x1871)).zeroExtend 32 := by
    rw [r12 _ (by decide), s11]
  -- The next root's `RoleKeys`, as read at `sp + 0x1870`, now at `sp + 0x88E + 2` and `sp + 0x350`.
  have P12 : ∀ o, 2 ≤ o → o < 0x540 → n12.mem (acSlot B (0x88E + o)) = n6.mem (acSlot B (0x1870 + o)) :=
    fun o h1 h2 => by
      rw [f12 _ (by aco_num) (by aco_num), m0 _ (by aco_num), show 0x88E + o = 0x890 + (o - 2) by omega,
        ← aco_so B _ _ (by omega), g10 _ (by omega), aco_so B _ _ (by omega), M7, memStore32_get_sep (by aco_num),
        show 0x1872 + (o - 2) = 0x1870 + o by omega]
  have Q12 : ∀ o, o < 0x540 → n12.mem (acSlot B (0x350 + o)) = n6.mem (acSlot B (0x1870 + o)) := fun o ho => by
    rcases o with _ | _ | o
    · rw [f12 _ (by aco_num) (by aco_num), M11, memStore8_ne (by aco_neq), memStore8_same]
    · rw [f12 _ (by aco_num) (by aco_num), M11, memStore8_same]
    · rw [show 0x350 + (o + 2) = 0x352 + o by omega, ← aco_so B _ _ (by omega), g12 _ (by omega),
        aco_so B _ _ (by omega), m0 _ (by aco_num), ← aco_so B _ _ (by omega), g10 _ (by omega),
        aco_so B _ _ (by omega), M7, memStore32_get_sep (by aco_num), show 0x1872 + o = 0x1870 + (o + 2) by omega]
  have hR : RkAt n12.mem (acSlot B 0x350) tt (es.map C3.Json.rkTag) := hbR.congr fun o ho => by
    rw [aco_so B _ _ (by omega), aco_so B _ _ (by omega)]; exact Q12 o ho
  have z12 := t12.zero
  obtain ⟨n13, c13', u13⟩ := t12.block (off' := 0x70E) acoD7 (C.code K12) (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have M13 : n13.mem = n12.mem := u13.mem
  have rsp12 : reg n12 sp = acSlot B 0 := by rw [r12' sp (by decide), rsp0]
  have g0 : reg n13 a0 = acSlot B 0x350 := by
    rw [u13.regs]; simp +decide only [runBlock, BInstr.run, acoD7, upd, ↓reduceIte]; rw [rsp12]; aco_simp
  have g1 : reg n13 a1 = acSlot B 0x1ED0 := by
    rw [u13.regs]; simp +decide only [runBlock, BInstr.run, acoD7, upd, ↓reduceIte]; rw [rsp12]; aco_simp
  have r13 : ∀ q : Fin 32, acoDK q = true → reg n13 q = reg n q := fun q hq => by
    rw [u13.regs, runBlock_reg _ _ _ q z12 (by simp only [acoD7]; revert hq; revert q; decide), r12' q hq]
  have s13 : reg n13 (22 : Fin 32) = (n6.mem (acSlot B 0x1871)).zeroExtend 32 := by
    rw [u13.regs, runBlock_reg _ _ _ _ z12 (by simp only [acoD7]; decide), s12]
  have T13 : St n13.mem AC n13 0x70E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have K13 : AcoKeep B Bf n0.mem n13.mem := by rw [M13]; exact K12
  have KR13 : AcoKR n0 n13 := fun q hq => by rw [r13 q (by revert hq; revert q; decide)]; exact KR q hq
  have L13 : ∀ k, 0x1ED0 ≤ k → k + 4 ≤ 0x1EE8 → memLoad32 n13.mem (acSlot B k) = memLoad32 n.mem (acSlot B k) :=
    fun k h1 h2 => by
      rw [M13]; exact memLoad32_congr fun j hj => F12 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
        (by aco_num) (by aco_num) (by aco_num)
  have D13 : ∀ {q : Word} {l : Nat}, AcoIn Bf q l → memBytes n13.mem q l = memBytes n.mem q l := fun {q l} hq => by
    have := hq.1; have := hq.2
    rw [M13]; exact memBytes_congr fun j hj => F12 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
      (by aco_num) (by aco_num) (by aco_num)
  obtain ⟨n14, c14, h14⟩ := aco_met C T13 K13 KR13.a ac_at_70e ac_at_712 (by decide) (by decide) g0 g1
    (by decide) (by decide) (by decide) hq1 hq2 (by rw [L13 _ (by decide) (by decide)]; exact hA0)
    (by rw [L13 _ (by decide) (by decide)]; exact hA4) (by rw [L13 _ (by decide) (by decide)]; exact hA8)
    (by rw [L13 _ (by decide) (by decide)]; exact hAC) hrk hj (by rw [M13]; exact hR)
    (by rw [D13 hq1]; exact hmsg) (by rw [D13 hq2]; exact hsj) hps
  have c114 : Steps n n14 := c17.trans ((Steps.single e8).trans (c9.trans (c10.trans (c11.trans
    (c12.trans (c13'.trans c14))))))
  rcases h14 with h | ⟨T14, f14, g14, m0', m1'⟩
  · exact ⟨n14, c114, .inl h⟩
  have T14' : St n14.mem AC n14 0x716 (reg n14) := T14
  have K14 : AcoKeep B Bf n0.mem n14.mem := fun x hx => by
    rw [f14 x (aco_wLow hx (by decide)), M13]; exact K12 x hx
  have r14 : ∀ q : Fin 32, acoDK q = true → reg n14 q = reg n q := fun q hq => by
    rw [g14 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r13 q hq]
  have KR14 : AcoKR n0 n14 := fun q hq => by rw [r14 q (by revert hq; revert q; decide)]; exact KR q hq
  have F14 : ∀ x, Sep x 1 (B + 0x130) 0x3920 → Sep x 1 (B + 0x2E60) 3056 → Sep x 1 (acSlot B 0x1870) 0x540 →
      Sep x 1 (acSlot B 0x28) 4 → Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B 0x890) 0x53E →
      Sep x 1 (acSlot B 0x350) 2 → Sep x 1 (acSlot B 0x352) 0x53E → n14.mem x = n.mem x :=
    fun x h0 h1 h2 h3 h4 h5 h6 h7 => by rw [f14 x h0, M13, F12 x h1 h2 h3 h4 h5 h6 h7]
  have s14 : reg n14 (22 : Fin 32) = (n6.mem (acSlot B 0x1871)).zeroExtend 32 := by
    rw [g14 _ (by decide) (by decide), s13]
  have W14 : memLoad32 n14.mem (acSlot B 0x28) = (n6.mem (acSlot B 0x1870)).zeroExtend 32 := by
    rw [← w10]
    exact memLoad32_congr fun j hj => by
      rw [f14 _ (by aco_num), M13, f12 _ (by aco_num) (by aco_num), m0 _ (by aco_num)]
  refine aco_pre c114 (aco_E C T14' K14 KR14 hi ?_ ?_ ?_ ?_ ?_ ⟨n.mem, q1, l1, hj⟩ hq1 ?_ ?_ ?_ (hf hT1)
    (fun h h' => (m0' h).2 h') m1' IH)
  · rw [← hc]; exact memLoad32_congr fun j hj => F14 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
      (by aco_num) (by aco_num) (by aco_num) (by aco_num)
  · rw [r14 19 (by decide), r14 26 (by decide)]; exact hv
  · rw [W14]; exact aco_zlt _
  · rw [s14]; exact aco_zlt _
  · rw [W14, s14]
    refine aco_rkC (fun o ho => ?_) k6
    simp only [acoTBk]
    split
    · rename_i o0; subst o0; rw [aco_zx8, bR0]
    split
    · rename_i o0 o1; subst o1; rw [aco_zx8, bR1]
    rename_i o0 o1
    rw [aco_so B _ _ (by omega), aco_so B _ _ (by omega), f14 _ (by aco_num), M13]
    exact P12 o (by omega) ho
  · rw [r14 8 (by decide)]; exact h8
  · rw [r14 18 (by decide)]; exact h18
  · rw [show memBytes n14.mem q1 l1 = memBytes n13.mem q1 l1 from
      memBytes_congr fun j hj => f14 _ (by have := hq1.1; have := hq1.2; aco_num), D13 hq1]
    exact hj

theorem aco_fe32 {w : Word} (h : w + 0xFFFFFF02 = 0) : w = 0xFE :=
  calc w = w + (0xFFFFFF02 + 0xFE) := by
        rw [show (0xFFFFFF02 + 0xFE : Word) = 0 from by decide, show ∀ x : Word, x + 0 = x from BitVec.add_zero]
    _ = (w + 0xFFFFFF02) + 0xFE := by rw [BitVec.add_assoc]
    _ = 0xFE := by rw [h, show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add]

theorem aco_and8 {s : Word} (h : s.toNat < 256) : (s &&& 0xFF).toNat = (s.extractLsb' 0 8).toNat := by
  have e : s = (s.extractLsb' 0 8).zeroExtend 32 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (by omega)])
  rw [e, aco_ze8, ← e]

theorem aco_w8 {w : Word} (h : w.toNat < 256) (e : w.extractLsb' 0 8 = 0xFE) : w = 0xFE := by
  have := congrArg BitVec.toNat e
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt h] at this
  exact BitVec.eq_of_toNat_eq this

/-- `a0 = [sp + 0x28] - 0xFE`, at 0x62C. -/
def acoC1 : List BInstr := [.lw a0 sp 0x28, .aluImm .add a0 a0 0xFFFFFF02]

/-- `s2 = s1`, and the arguments of the copy of the trusted root's keys to
`sp + 0x1872`, at 0x636. -/
def acoC2 : List BInstr := [.alu .add (18 : Fin 32) x0 (9 : Fin 32), .aluImm .add a2 x0 0x53E, .lui a0 0x2000,
  .aluImm .add a0 a0 0xFFFFF872, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x322, .alu .add a1 a1 sp]

/-- The first two bytes to `sp + 0x1870`, and the arguments of the first
`RoleKeys::met`, at 0x654. -/
def acoC3 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add a0 a0 sp, .lw a1 sp 0x28,
  .sb a0 a1 0x560, .sb a0 (22 : Fin 32) 0x561, .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF870, .alu .add a0 a0 sp,
  .lui a1 0x2000, .aluImm .add a1 a1 0xFFFFFED0, .alu .add a1 a1 sp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The next root's signatures against the trusted root's keys**, at
0x62C: reject when the trusted root's keys are an error; otherwise copy
them to `sp + 0x1870` and call `RoleKeys::met`. -/
theorem aco_C (C : AcoCtx flash R romBase romCode B Bf g t r v M0 docs first n0) {n : Machine} {i : Nat}
    {prev next : TufRoot} {q1 q2 : Word} {l1 l2 : Nat} {sj : Json}
    (s : St n.mem AC n 0x62C (reg n)) (K : AcoKeep B Bf n0.mem n.mem) (KR : AcoKR n0 n)
    (hi : i < docs.length) (hc : memLoad32 n.mem (acSlot B 0x2C) = BitVec.ofNat 32 i)
    (hv : (reg n (19 : Fin 32)).toNat * 2 ^ 32 + (reg n (26 : Fin 32)).toNat = next.version)
    (hS : AcoState B n.mem (reg n (22 : Fin 32)) prev)
    (hq1 : AcoIn Bf q1 l1) (hq2 : AcoIn Bf q2 l2)
    (h8 : reg n (8 : Fin 32) = q1) (h9 : reg n (9 : Fin 32) = BitVec.ofNat 32 l1)
    (hA0 : memLoad32 n.mem (acSlot B 0x1ED0) = q1) (hA4 : memLoad32 n.mem (acSlot B 0x1ED4) = BitVec.ofNat 32 l1)
    (hA8 : memLoad32 n.mem (acSlot B 0x1ED8) = q2) (hAC : memLoad32 n.mem (acSlot B 0x1EDC) = BitVec.ofNat 32 l2)
    (hj : JVal true (memBytes n.mem q1 l1) next.md.signed)
    (hmsg : memBytes n.mem q1 l1 = encode next.md.signed) (hsj : JVal true (memBytes n.mem q2 l2) sj)
    (hps : (sj.asArr >>= List.mapM sigPair) = some next.md.sigs)
    (hf : thresholdMet next.md prev.md.signed (ascii!"root") = some true →
      thresholdMet next.md next.md.signed (ascii!"root") = some true →
      (docs.take (i + 1)).foldlM acoStep first = some next)
    (IH : ∀ n', St n'.mem AC n' 0x584 (reg n') → AcoInv B Bf docs first n0 n' (i + 1) →
      AcoG B Bf g t r v M0 docs first n0 n') :
    AcoG B Bf g t r v M0 docs first n0 n := by
  have N := C.N
  have := N.b0; have := N.b1; have := N.b2; have := N.f0; have := N.bb
  have := hq1.1; have := hq1.2; have := hq2.1; have := hq2.2
  have hz := s.zero
  have rsp0 : reg n sp = acSlot B 0 := C.sp KR.a
  have CC := C.code K
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x632) acoC1 CC (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoC1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp0]; aco_simp; aco_num)
  have M1 : n1.mem = n.mem := u1.mem
  have a0v : reg n1 a0 = memLoad32 n.mem (acSlot B 0x28) + 0xFFFFFF02 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acoC1, upd, ↓reduceIte, aluEval]; rw [rsp0]; aco_simp
  have r1 : ∀ q : Fin 32, q.val ≠ 10 → reg n1 q = reg n q := fun q h0 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acoC1]; revert h0; revert q; decide)]
  have t1 : St n1.mem AC n1 0x632 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have C1 : CodeIn n1.mem AC bootMainClosure0Code := by rw [M1]; exact CC
  have K1 : AcoKeep B Bf n0.mem n1.mem := by rw [M1]; exact K
  have tb0 : acoTB B n.mem (memLoad32 n.mem (acSlot B 0x28)) (reg n (22 : Fin 32)) 0 =
      (memLoad32 n.mem (acSlot B 0x28)).extractLsb' 0 8 := rfl
  have tb1 : acoTB B n.mem (memLoad32 n.mem (acSlot B 0x28)) (reg n (22 : Fin 32)) 1 =
      (reg n (22 : Fin 32)).extractLsb' 0 8 := rfl
  by_cases e0 : memLoad32 n.mem (acSlot B 0x28) = 0xFE
  · obtain ⟨n2, e2, t2⟩ := t1.taken C1 0x7D2 ac_at_632 (by decide)
      (by simp only [branchTaken, a0v, t1.zero, e0, beq_iff_eq]; decide)
    refine aco_pre (c1.trans (.single e2)) (aco_leaf2 C ⟨t2.pc, rfl, fun _ => rfl⟩
      (by rw [t2.mem]; exact K1) (fun q hq => ?_) ?_)
    · rw [t2.regs, r1 q (by revert hq; revert q; decide)]; exact KR.a q hq
    · rw [t2.regs, r1 22 (by decide), aco_and8 hS.b]
      rcases hS.keys with ⟨_, h1⟩ | ⟨_, _, _, hb⟩
      · rw [tb1] at h1; exact h1
      · exact absurd (by rw [tb0, e0]; decide) (aco_rk0 hb)
  obtain ⟨n2, e2, t2⟩ := t1.notTaken C1 0x636 ac_at_632 (by decide)
    (by simp only [branchTaken, a0v, t1.zero, beq_eq_false_iff_ne]; exact fun h => e0 (aco_fe32 h))
  obtain ⟨tt, es, hrk, hbR⟩ := aco_rkOk hS.keys (by rw [tb0]; exact fun h => e0 (aco_w8 hS.w h))
  obtain ⟨Mp, Pp, Lp, hP⟩ := hS.src
  have t2' : St n1.mem AC n2 0x636 (reg n1) := t2
  obtain ⟨n3, c3, u3⟩ := t2'.block (off' := 0x64C) acoC2 C1 (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have M3 : n3.mem = n.mem := u3.mem.trans M1
  have rsp1 : reg n1 sp = acSlot B 0 := by rw [r1 sp (by decide), rsp0]
  have d0 : reg n3 a0 = acSlot B 0x1872 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoC2, upd, ↓reduceIte]; rw [rsp1]; aco_simp
  have d1 : reg n3 a1 = acSlot B 0x1322 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoC2, upd, ↓reduceIte]; rw [rsp1]; aco_simp
  have d2 : reg n3 a2 = BitVec.ofNat 32 0x53E := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoC2, upd, ↓reduceIte, aluEval]
  have d18 : reg n3 (18 : Fin 32) = BitVec.ofNat 32 l1 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acoC2, upd, ↓reduceIte, aluEval]
    rw [t2'.zero, show ∀ x : Word, (0 : Word) + x = x from BitVec.zero_add, r1 9 (by decide), h9]
  have r3 : ∀ q : Fin 32, acoDK q = true → q.val ≠ 18 → reg n3 q = reg n q := fun q hq h18 => by
    rw [u3.regs, runBlock_reg _ _ _ q t2'.zero (by simp only [acoC2]; revert hq h18; revert q; decide),
      r1 q (by revert hq; revert q; decide)]
  have s3 : reg n3 (22 : Fin 32) = reg n (22 : Fin 32) := by
    rw [u3.regs, runBlock_reg _ _ _ _ t2'.zero (by simp only [acoC2]; decide), r1 22 (by decide)]
  have T3 : St n3.mem AC n3 0x64C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have K3 : AcoKeep B Bf n0.mem n3.mem := by rw [M3]; exact K
  have KR3 : AcoKR n0 n3 := fun q hq => by
    rw [r3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq
  obtain ⟨n4, c4, t4, f4, g4, r4⟩ := aco_mc C T3 K3 KR3.a ac_at_64c ac_at_650 (by decide) (by decide)
    d0 d1 d2 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [M3] at f4 g4
  have K4 : AcoKeep B Bf n0.mem n4.mem := K.trans fun x hx =>
    f4 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide))
  have r4' : ∀ q : Fin 32, acoDK q = true → q.val ≠ 18 → reg n4 q = reg n q := fun q hq h18 => by
    rw [r4 q (by revert hq; revert q; decide), r3 q hq h18]
  have KR4 : AcoKR n0 n4 := fun q hq => by
    rw [r4' q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq
  have rsp4 : reg n4 sp = acSlot B 0 := by rw [r4' sp (by decide) (by decide), rsp0]
  have s4 : reg n4 (22 : Fin 32) = reg n (22 : Fin 32) := by rw [r4 _ (by decide), s3]
  have w4 : memLoad32 n4.mem (acSlot B 0x28) = memLoad32 n.mem (acSlot B 0x28) :=
    memLoad32_congr fun j hj => f4 _ (by aco_num) (by aco_num)
  have z4 := t4.zero
  obtain ⟨n5, c5, u5⟩ := t4.block (off' := 0x676) acoC3 (C.code K4) (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acoC3]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp4]; aco_simp; exact ⟨by aco_num, by aco_num, by aco_num⟩)
  have M5 : n5.mem = memStore8 (memStore8 n4.mem (acSlot B 0x1870)
      ((memLoad32 n.mem (acSlot B 0x28)).extractLsb' 0 8)) (acSlot B 0x1871) ((reg n (22 : Fin 32)).extractLsb' 0 8) := by
    rw [u5.mem]; simp only [runBlock, BInstr.run, acoC3]; simp +decide only [upd, ↓reduceIte]
    rw [rsp4]; aco_simp; rw [w4, s4]
  have m0 : ∀ x, Sep x 1 (acSlot B 0x1870) 2 → n5.mem x = n4.mem x := fun x h => by
    rw [M5, memStore8_ne fun e => h 0 (by decide) 1 (by decide) (by rw [add_ofNat_zero, e, aco_so B _ _ (by decide)]),
      memStore8_ne fun e => h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])]
  have g0 : reg n5 a0 = acSlot B 0x1870 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoC3, upd, ↓reduceIte]; rw [rsp4]; aco_simp
  have g1 : reg n5 a1 = acSlot B 0x1ED0 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, acoC3, upd, ↓reduceIte]; rw [rsp4]; aco_simp
  have r5 : ∀ q : Fin 32, acoDK q = true → q.val ≠ 18 → reg n5 q = reg n q := fun q hq h18 => by
    rw [u5.regs, runBlock_reg _ _ _ q z4 (by simp only [acoC3]; revert hq; revert q; decide), r4' q hq h18]
  have e18 : reg n5 (18 : Fin 32) = BitVec.ofNat 32 l1 := by
    rw [u5.regs, runBlock_reg _ _ _ _ z4 (by simp only [acoC3]; decide), r4 _ (by decide), d18]
  have T5 : St n5.mem AC n5 0x676 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have F5 : ∀ x, Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B 0x1872) 0x53E → Sep x 1 (acSlot B 0x1870) 2 →
      n5.mem x = n.mem x := fun x h1 h2 h3 => by rw [m0 x h3, f4 x h1 h2]
  have K5 : AcoKeep B Bf n0.mem n5.mem := K.trans fun x hx =>
    F5 x (aco_wLow hx (by decide)) (aco_wScr hx (by decide) (by decide)) (aco_wScr hx (by decide) (by decide))
  have KR5 : AcoKR n0 n5 := fun q hq => by
    rw [r5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq
  have hR : RkAt n5.mem (acSlot B 0x1870) tt (es.map C3.Json.rkTag) := hbR.congr fun o ho => by
    simp only [acoTB]
    split
    · rename_i o0; subst o0; rw [add_ofNat_zero, M5, memStore8_ne (by aco_neq), memStore8_same]
    split
    · rename_i o0 o1; subst o1; rw [aco_so B _ _ (by decide), M5, memStore8_same]
    rename_i o0 o1
    rw [m0 _ (by rw [aco_so B _ _ (by omega)]; aco_num), show o = 2 + (o - 2) by omega, ← add_ofNat_assoc,
      show acSlot B 0x1870 + BitVec.ofNat 32 2 = acSlot B 0x1872 from aco_so B _ _ (by decide), g4 _ (by omega),
      ← add_ofNat_assoc, show acSlot B 0x1320 + BitVec.ofNat 32 2 = acSlot B 0x1322 from aco_so B _ _ (by decide)]
  have L5 : ∀ k, 0x1ED0 ≤ k → k + 4 ≤ 0x1EE8 → memLoad32 n5.mem (acSlot B k) = memLoad32 n.mem (acSlot B k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => F5 _ (by aco_num) (by aco_num) (by aco_num)
  have D5 : ∀ {q : Word} {l : Nat}, AcoIn Bf q l → memBytes n5.mem q l = memBytes n.mem q l := fun {q l} hq => by
    have := hq.1; have := hq.2
    exact memBytes_congr fun j hj => F5 _ (by aco_num) (by aco_num) (by aco_num)
  obtain ⟨n6, c6, h6⟩ := aco_met C T5 K5 KR5.a ac_at_676 ac_at_67a (by decide) (by decide) g0 g1
    (by decide) (by decide) (by decide) hq1 hq2 (by rw [L5 _ (by decide) (by decide)]; exact hA0)
    (by rw [L5 _ (by decide) (by decide)]; exact hA4) (by rw [L5 _ (by decide) (by decide)]; exact hA8)
    (by rw [L5 _ (by decide) (by decide)]; exact hAC) hrk hP hR
    (by rw [D5 hq1]; exact hmsg) (by rw [D5 hq2]; exact hsj) hps
  have c16 : Steps n n6 := c1.trans ((Steps.single e2).trans (c3.trans (c4.trans (c5.trans c6))))
  rcases h6 with h | ⟨T6, f6, g6, m0', m1'⟩
  · exact ⟨n6, c16, .inl h⟩
  have F6 : ∀ x, Sep x 1 (B + 0x130) 0x3920 → Sep x 1 (B + 0x3A40) 16 → Sep x 1 (acSlot B 0x1872) 0x53E →
      Sep x 1 (acSlot B 0x1870) 2 → n6.mem x = n.mem x := fun x h0 h1 h2 h3 => by rw [f6 x h0, F5 x h1 h2 h3]
  have K6 : AcoKeep B Bf n0.mem n6.mem := fun x hx => by rw [f6 x (aco_wLow hx (by decide))]; exact K5 x hx
  have r6 : ∀ q : Fin 32, acoDK q = true → q.val ≠ 18 → reg n6 q = reg n q := fun q hq h18 => by
    rw [g6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r5 q hq h18]
  have KR6 : AcoKR n0 n6 := fun q hq => by
    rw [r6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]; exact KR q hq
  have L6 : ∀ k, 0x1ED0 ≤ k → k + 4 ≤ 0x1EE8 → memLoad32 n6.mem (acSlot B k) = memLoad32 n.mem (acSlot B k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => F6 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
  have D6 : ∀ {q : Word} {l : Nat}, AcoIn Bf q l → memBytes n6.mem q l = memBytes n.mem q l := fun {q l} hq => by
    have := hq.1; have := hq.2
    exact memBytes_congr fun j hj => F6 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
  refine aco_pre c16 (aco_D C T6 K6 KR6 hi ?_ ?_ hq1 hq2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hps hf m0' m1' IH)
  · rw [← hc]; exact memLoad32_congr fun j hj => F6 _ (by aco_num) (by aco_num) (by aco_num) (by aco_num)
  · rw [r6 19 (by decide) (by decide), r6 26 (by decide) (by decide)]; exact hv
  · rw [r6 8 (by decide) (by decide)]; exact h8
  · rw [g6 18 (by decide) (by decide)]; exact e18
  · rw [L6 _ (by decide) (by decide)]; exact hA0
  · rw [L6 _ (by decide) (by decide)]; exact hA4
  · rw [L6 _ (by decide) (by decide)]; exact hA8
  · rw [L6 _ (by decide) (by decide)]; exact hAC
  · rw [D6 hq1]; exact hj
  · rw [D6 hq1]; exact hmsg
  · rw [D6 hq2]; exact hsj

end ctx

end C3.RV32.Ac
