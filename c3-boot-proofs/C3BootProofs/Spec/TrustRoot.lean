import C3BootProofs.Spec.Level

/-!
# Key-set chains and trust-root blobs

A slot carries a key-set chain from the compiled-in genesis keys and a
trust-root blob signed by the chain's last key set. These definitions follow
`c3_verify::chain`, `c3_verify::keys`, and `c3_verify::trustroot`, with the
signature check taken as a parameter: `verify key message signature`. The
Ed25519 proofs are the plan's cryptography phase. A link's or blob's
`msg` is the message its signatures cover: the domain string, a zero byte,
and the signed body.
-/

namespace C3

/-- One signature: the signing key's index in the signer set, and the
signature. -/
structure SigEntry (Sig : Type) where
  index : Nat
  sig : Sig

/-- One link of a key-set chain. -/
structure Link (Key Msg Sig : Type) where
  level : Nat
  keys : List Key
  msg : Msg
  sigs : List (SigEntry Sig)

/-- A trust-root blob, reduced to what the key-set rules read. -/
structure Blob (Msg Sig : Type) where
  level : Nat
  msg : Msg
  sigs : List (SigEntry Sig)

/-- The signatures every link and blob needs. -/
def threshold : Nat := 2

/-- The most keys a set holds, and the most signatures a list holds. -/
def maxKeys : Nat := 4

variable {Key Msg Sig : Type}

/-- A key set has 1 through 4 keys, all distinct. -/
def validKeySet [DecidableEq Key] (ks : List Key) : Bool :=
  1 ≤ ks.length && ks.length ≤ maxKeys && decide ks.Nodup

/-- Each element is less than the next. -/
def increasing : List Nat → Bool
  | a :: b :: rest => a < b && increasing (b :: rest)
  | _ => true

/-- 2 through 4 signatures, by keys of `signers` with strictly increasing
indexes, each valid over `msg`. Increasing indexes mean no key counts
twice. -/
def thresholdSigned (verify : Key → Msg → Sig → Bool) (signers : List Key) (msg : Msg)
    (sigs : List (SigEntry Sig)) : Bool :=
  threshold ≤ sigs.length && sigs.length ≤ maxKeys && increasing (sigs.map (·.index)) &&
    sigs.all fun e =>
      match signers[e.index]? with
      | some k => verify k msg e.sig
      | none => false

/-- The key set and level at the end of a chain that starts from `keys` at
`level`, if every link is authorized. Levels rise strictly from 1 to at
most 16, so an accepted chain has at most 16 links, which is
`c3_verify::chain::MAX_LINKS`. -/
def chainTip [DecidableEq Key] (verify : Key → Msg → Sig → Bool) :
    List Key → Nat → List (Link Key Msg Sig) → Option (List Key × Nat)
  | keys, lvl, [] => some (keys, lvl)
  | keys, lvl, l :: rest =>
    if lvl < l.level && l.level ≤ maxLevel && validKeySet l.keys &&
        thresholdSigned verify keys l.msg l.sigs then
      chainTip verify l.keys l.level rest
    else none

/-- What a slot holds, reduced to what the trust-root rules read.
`sigstoreOk` is the result of the Sigstore checks against the blob. -/
structure Contents (Key Msg Sig : Type) where
  links : List (Link Key Msg Sig)
  blob : Blob Msg Sig
  securityVersion : Nat
  sigstoreOk : Bool

/-- The slot's level if it passes the key-set, trust-root, level, and
Sigstore checks at eFuse level `efuseLevel`. -/
def acceptContents [DecidableEq Key] (verify : Key → Msg → Sig → Bool) (genesis : List Key)
    (efuseLevel : Nat) (c : Contents Key Msg Sig) : Option Nat :=
  match chainTip verify genesis 0 c.links with
  | some (keys, tipLevel) =>
    if c.blob.level ≤ maxLevel && thresholdSigned verify keys c.blob.msg c.blob.sigs &&
        checkSlot tipLevel c.blob.level c.securityVersion efuseLevel && c.sigstoreOk then
      some c.blob.level
    else none
  | none => none

end C3
