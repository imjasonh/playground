import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.TufReadDoc
import C3BootProofs.Proofs.TufParseRoot
import C3BootProofs.Proofs.TufRoleKeysMetSpec
import C3BootProofs.Proofs.TufRoleKeysMetCalls
import C3BootProofs.Proofs.TufExpires
import C3BootProofs.Proofs.TufCalls
import C3BootProofs.Proofs.TufPemSpki
import C3BootProofs.Proofs.AcceptTargetsSpec

/-!
# `boot_main`'s first closure: `targets.json`

The stage from 0x836 to 0xC12. With the last root's keys for the `targets`
role at `sp + 0xDD0`, it reads `targets.json` into `doc`, parses it as
metadata, checks the role's threshold of signatures, and reads its expiry.
It then looks up `trusted_root.json`'s length and SHA-256 under
`signed.targets`, reads `trusted_root.json` into `doc`, and compares its
length and the lowercase hex of its SHA-256 with them.

`AcTargetsStage` is the stage's contract. It reaches 0xC12 only when
`verifyTuf` accepts the parts, and then `doc` holds `trusted_root.json`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

/-! ## The stage's interface -/

/-- The code and data that the stage and its callees read: `tuf::read_doc`
and the flash read under it, `parse_metadata`, `RoleKeys::met`, `expires`,
`field`, `get`, `u64`, SHA-256, `memcpy`, `memset`, `memcmp`, the ROM at
`romBase`, the keys that the stage looks up, and the hex digits. -/
structure AcTargetsEnv (romBase : Word) (romCode : List Nat) (M : Word → BitVec 8) : Prop where
  rd : CodeIn M (BitVec.ofNat 32 tufReadDocAddress) tufReadDocCode
  rdI : CodeIn M (BitVec.ofNat 32 tufReadDocAddress + 0xB388) tufIndexDocCode
  rdF : CodeIn M (BitVec.ofNat 32 tufReadDocAddress + 0x16DA4) flashPartReadCode
  fr : CodeIn M (img% flashReadAddress) flashReadCode
  frM : CodeIn M ((img% flashReadAddress) + (img% memsetAddress + 0x100000000 - flashReadAddress)) memsetCode
  frW : CodeIn M ((img% flashReadAddress) + 0xFFFFFFE8) romFlashReadWordsCode
  rom : CodeIn M romBase romCode
  pm : PmCode M
  rm : RmCode M
  tex : TexCode M
  fld : FieldCode M (BitVec.ofNat 32 jsonFieldAddress)
  u64 : CodeIn M TPR_JU jsonU64Code
  aad : CodeIn M AAD allAsciiDigitCode
  sha : Sha256Code M
  mcs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  mset : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  mcmp : CodeIn M (BitVec.ofNat 32 memcmpAddress) memcmpCode
  keys : CodeIn M (BitVec.ofNat 32 acTargetsKeysAddress) acTargetsKeysData
  hex : CodeIn M (BitVec.ofNat 32 acHexDigitsAddress) acHexDigitsData

/-- `Index::doc(i)` for the index at `idx` locates `d` in flash from
`start`. -/
def ActDoc (flash : Nat → BitVec 8) (M : Word → BitVec 8) (idx start : Word) (i : Nat) (d : Bytes) : Prop :=
  ∀ o l, tufIndexDocSpec M idx i = .ok (o, l) → flashBytes flash (start.toNat + o) l = d

/-- At 0x836: the roots led to `root`, whose expiry `re` is at `sp + 0x1318`
and whose keys for `targets` are at `sp + 0xDD0`. The index at `sp + 0x244`
locates `targets.json` and `trusted_root.json` as documents
`sp[0x1C]` and `sp[0x1C] + 1` of the TUF part at `s8`, of `s7` bytes. `s4`
is `doc`, and `sp + 0x40` holds the result pointer `r`. -/
def AcTargetsPre (flash : Nat → BitVec 8) (pinned : Bytes) (parts : TufParts) (root : TufRoot) (re : Nat)
    (B Bf r : Word) (n : Machine) : Prop :=
  actRoot pinned parts = some root ∧ expires root.md = some re ∧
  memLoad32 n.mem (acSlot B 0x1318) = BitVec.ofNat 32 re ∧
  memLoad32 n.mem (acSlot B 0x131C) = BitVec.ofNat 32 (re / 2 ^ 32) ∧
  (∃ t es, roleKeys root.md.signed (ascii!"targets") = some (t, es) ∧
    RkAt n.mem (acSlot B 0xDD0) t (es.map C3.Json.rkTag) ∧ RkWf (es.map C3.Json.rkTag)) ∧
  ActDoc flash n.mem (acSlot B 0x244) (reg n (24 : Fin 32))
    (memLoad32 n.mem (acSlot B 0x1C)).toNat parts.targets ∧
  ActDoc flash n.mem (acSlot B 0x244) (reg n (24 : Fin 32))
    ((memLoad32 n.mem (acSlot B 0x1C)).toNat + 1) parts.trustedRoot ∧
  reg n (20 : Fin 32) = Bf + 0x4000 ∧
  memLoad32 n.mem (acSlot B 0x40) = r

/-- The byte `x` is none that the stage may write: not in the callees'
stacks below `sp`, the frame slots at `sp + 0x14`, `sp + 0x18`, and from
`sp + 0x20` to `sp + 0x30`, the results at `sp + 0x350` and from
`sp + 0x1860`, or `doc`. -/
def ActOut (B Bf x : Word) : Prop :=
  Sep x 1 B 0x3A50 ∧ Sep x 1 (acSlot B 0x14) 8 ∧ Sep x 1 (acSlot B 0x20) 0x10 ∧ Sep x 1 (acSlot B 0x350) 0x41 ∧
    Sep x 1 (acSlot B 0x1860) 0x6B0 ∧ Sep x 1 (Bf + 0x4000) 0x2800

/-- At 0xC12: `verifyTuf` accepts the parts with the expiry `min re te`,
`targets.json`'s expiry `te` is at `sp + 0x20` and the root's at `sp + 0x28`,
`doc` (in `s2`) holds `trusted_root.json` and `s8` its length, `s3` and `s6`
point into the frame, `s5`, `s9`, and `s11` are as they were at 0x836
(`x21`, `x25`, `x27`), and every byte the stage doesn't write is as it was
in `Mi`. -/
def AcTargetsPost (pinned : Bytes) (parts : TufParts) (root : TufRoot) (re : Nat) (B Bf x21 x25 x27 : Word)
    (Mi : Word → BitVec 8) (n : Machine) : Prop :=
  (∃ te, verifyTuf pinned parts = some (root.version, min re te) ∧
    memLoad32 n.mem (acSlot B 0x20) = BitVec.ofNat 32 te ∧
    memLoad32 n.mem (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32)) ∧
  memLoad32 n.mem (acSlot B 0x28) = BitVec.ofNat 32 re ∧
  memLoad32 n.mem (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32) ∧
  reg n (18 : Fin 32) = Bf + 0x4000 ∧
  reg n (24 : Fin 32) = BitVec.ofNat 32 parts.trustedRoot.length ∧
  memBytes n.mem (Bf + 0x4000) parts.trustedRoot.length = parts.trustedRoot ∧
  reg n (19 : Fin 32) = acSlot B 0x890 ∧ reg n (22 : Fin 32) = acSlot B 0x1310 ∧
  reg n (21 : Fin 32) = x21 ∧ reg n (25 : Fin 32) = x25 ∧ reg n (27 : Fin 32) = x27 ∧
  ∀ x, ActOut B Bf x → n.mem x = Mi x

/-- `tufRoleKeysMet_spec`, without `RkBytes`, and with what `RoleKeys::met`
returns in `a0` and `a1`: when bit 0 of `a0` is clear (`Ok`), bit 0 of `a1`
set means `thresholdMet` holds, and when it is set (`Err`), the low byte of
`a1` is an error code below 0x27. The stage assumes this contract. -/
def ActMetSpec : Prop :=
  ∀ (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat}
    {md : Meta} {dj sj : Json} {role : Bytes} {es : List (Bytes × Option TufKey)},
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
    roleKeys dj role = some (t, es) → RkAt m.mem R t (es.map C3.Json.rkTag) →
    RkWf (es.map C3.Json.rkTag) → memBytes m.mem MP ML = encode md.signed →
    JVal true (memBytes m.mem SP SL) sj → (sj.asArr >>= List.mapM sigPair) = some md.sigs →
    ∃ m', Steps m m' ∧
      (rmH m'.pc m'.mem (reg m') ∨
        (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
          (reg m' a0 &&& 1 = 0 → reg m' a1 &&& 1 ≠ 0 → thresholdMet md dj role = some true) ∧
          (reg m' a0 &&& 1 ≠ 0 → (reg m' a1 &&& 0xFF).toNat < 0x27)))

/-- **The `targets.json` stage**, from 0x836 to 0xC12, for the callees' code
and data `AcTargetsEnv` in memory that agrees with `M0` outside the stack
and `Buffers`, and `RoleKeys::met` as `ActMetSpec` describes it. It reaches
0xC12 only when `verifyTuf` accepts the parts, and then `AcTargetsPost`
holds. -/
def AcTargetsStage : Prop :=
  ∀ (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat), RomRead flash R romBase romCode →
  ∀ (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8)
    (pinned : Bytes) (parts : TufParts) (root : TufRoot) (re : Nat),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcTargetsEnv romBase romCode M) →
    CodeIn n.mem AC bootMainClosure0Code → Fr B 0x5A70 → Sep B 0x5A70 Bf acBufLen →
    Sep B 0x5A70 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) →
    Sep B 0x5A70 romBase romCode.length → Sep Bf acBufLen romBase romCode.length →
    Bf.toNat % 4 = 0 → Bf.toNat + acBufLen ≤ 0x40000000 → R % 4 = 0 → R ≤ 0x3A50 - 0x180 →
    St n.mem AC n 0x836 (reg n) → AcInv B Bf g t v M0 n →
    AcTargetsPre flash pinned parts root re B Bf r n →
    AcStage B Bf g t r v M0 n 0xC12
      (AcTargetsPost pinned parts root re B Bf (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32))
        n.mem)

end C3.RV32.Ac
