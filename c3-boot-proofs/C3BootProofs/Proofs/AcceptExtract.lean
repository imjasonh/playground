import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.SvRoot
import C3BootProofs.Proofs.TrustedRootLiftChain
import C3BootProofs.Proofs.Ed25519PkOk
import C3BootProofs.Proofs.JsonParse
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Proofs.CtAssign

/-!
# `boot_main`'s first closure: the extract stage

From 0xC12 to 0x1816 the closure runs `trusted_root::extract` inlined on
the trusted root's document: it checks the expiries, parses the document,
checks `mediaType`, reads each certificate authority, transparency log, and
timestamp authority into three arrays on the stack, rejects a repeated name
or key, and copies the arrays behind the policy's last 0x23 bytes at
`sp + 0xDD0`. At 0x1816 it calls `memcpy` to copy those 0x423 bytes into the
`TrustRoot` at `sp + 0x1875`.

`AcExtractStage` states the stage. The sub-stages split it at its loops:

| Sub-stage | From | To |
|-----------|------|----|
| `AceHeadStage` | 0xC12 | 0xD8C, the certificate authority loop |
| `AceCaStage` | 0xD8C | 0xEBA, the transparency log loop |
| `AceTlogStage` | 0xEBA | 0x123A, the timestamp authority loop |
| `AceTsaStage` | 0x123A | 0x1434, the repeat checks |
| `AceDupStage` | 0x1434 | 0x1778, the copies |
| `AceTailStage` | 0x1778 | 0x1816 |

Each loop's sub-stage starts from its invariant after any number of items,
and ends at the next cut with the next loop's invariant before its first
item. `ac_extract` in `AcceptExtractSeq` composes them.

The names and keys the arrays point at lie in `doc` (log origins) and in
`keys` below the free part that the slice at `sp + 0x1FDC` describes.
`AceKeysIn` says so; `AceKeysIn.sv` turns it into `SvRootAt`'s three arrays.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

/-! ## The spec, step by step -/

/-- `mediaType`'s required value. -/
abbrev aceMediaType : Bytes := ascii!"application/vnd.dev.sigstore.trustedroot+json;version=0.1"

/-- A certificate authority's Fulcio key, or `none` inside when its first
certificate has no P-384 key, as `extractTrustedRoot` reads it. -/
def aceCa (ca : Json) : Option (Option FulcioKey) := do
  let (c, w) ← readChain ca
  pure (c.p384Key.map fun k => (⟨c.subject, k, w⟩ : FulcioKey))

/-- A timestamp authority's key, or `none` inside, as `extractTrustedRoot`
reads it. -/
def aceTsa (t : Json) : Option (Option TsaKey) := do
  let (c, w) ← readChain t
  match c.p384Key with
  | none => pure none
  | some k =>
    let body := c.issuer ++ c.serial
    pure (some (⟨[0x30] ++ (← derLen body.length) ++ body, k, w⟩ : TsaKey))

/-- The keys that `f` gives for the items `js`, skipping each `none`. -/
def aceKeys {α : Type} (f : Json → Option (Option α)) (js : List Json) : Option (List α) :=
  (js.mapM f).map (List.filterMap id)

/-- The document parses to the object `jr`, whose `mediaType` is right. -/
def AceRootJ (json : Bytes) (jr : Json) : Prop :=
  parseJson false json = some jr ∧ (jr.field (ascii!"mediaType") >>= Json.asStr) = some aceMediaType

/-- The member `key` of `jr` is an array whose items are `done ++ rest`, and
`ks` are the keys of `done`. -/
def AceProg {α : Type} (jr : Json) (key : Bytes) (f : Json → Option (Option α)) (rest : List Json)
    (ks : List α) : Prop :=
  ∃ done, (jr.field key >>= Json.asArr) = some (done ++ rest) ∧ aceKeys f done = some ks

/-- No subject, origin, `SignerIdentifier`, or key is listed twice. -/
def AceDistinct (fs : List FulcioKey) (ls : List LogKey) (ts : List TsaKey) : Prop :=
  (distinct (fs.map (·.subject)) && distinct (fs.map (·.publicKey)) &&
    distinct (ls.map (·.origin)) && distinct (ls.map (·.publicKey)) &&
    distinct (ts.map (·.signerId)) && distinct (ts.map (·.publicKey))) = true

/-! ## Memory -/

/-- The 64-bit number in the two words at `a`, low word first. -/
def aceU64 (M : Word → BitVec 8) (a : Word) : Nat :=
  (memLoad32 M a).toNat + 2 ^ 32 * (memLoad32 M (a + 4)).toNat

/-- The bytes the stage keeps: those outside the stack and `keys`, and the
frame slots at 0x34 to 0x48 and 0x108 to 0x244 that later stages read. -/
def AceKept (B Bf x : Word) : Prop :=
  (Sep x 1 B 0x5A70 ∧ Sep x 1 (Bf + 0x6800) 0x5040) ∨
    ∃ k, (0x34 ≤ k ∧ k < 0x48 ∨ 0x108 ≤ k ∧ k < 0x244) ∧ x = acSlot B k

/-- `bs`, the `l` bytes at `p`, in `Buffers` from `doc` on and below `fp`. -/
def AceBytesIn (Bf fp : Word) (M : Word → BitVec 8) (p : Word) (l : Nat) (bs : Bytes) : Prop :=
  Bf.toNat + 0x4000 ≤ p.toNat ∧ p.toNat + l ≤ fp.toNat ∧ memBytes M p l = bs

/-- A listed entry at `e`: its name, its window, and its `n`-byte key, in
`Buffers` below `fp`. -/
structure AceEntryIn (Bf fp : Word) (M : Word → BitVec 8) (e : Word) (name key : Bytes) (n : Nat) (w : Window) :
    Prop where
  name : AceBytesIn Bf fp M (memLoad32 M e) (memLoad32 M (e + 4)).toNat name
  notBefore : SvU64At M (e + 8) w.notBefore
  notAfter : SvU64At M (e + 0x10) w.notAfter
  key : AceBytesIn Bf fp M (memLoad32 M (e + 0x18)) n key

/-- The Fulcio keys `fs` in the array of 8 at `a`. -/
def AceFulcioAt (Bf fp : Word) (M : Word → BitVec 8) (a : Word) (fs : List FulcioKey) : Prop :=
  SvArrayAt M a 8 fs fun e k => AceEntryIn Bf fp M e k.subject k.publicKey 0x61 k.window

/-- The log keys `ls` in the array of 16 at `a`. -/
def AceLogsAt (Bf fp : Word) (M : Word → BitVec 8) (a : Word) (ls : List LogKey) : Prop :=
  SvArrayAt M a 16 ls fun e k => AceEntryIn Bf fp M e k.origin k.publicKey 32 k.window

/-- The TSA keys `ts` in the array of 8 at `a`. -/
def AceTsasAt (Bf fp : Word) (M : Word → BitVec 8) (a : Word) (ts : List TsaKey) : Prop :=
  SvArrayAt M a 8 ts fun e k => AceEntryIn Bf fp M e k.signerId k.publicKey 0x61 k.window

/-- The three arrays from `k`, as `TrustRoot` holds them from 0x28. -/
def AceKeysIn (Bf fp : Word) (M : Word → BitVec 8) (k : Word) (fs : List FulcioKey) (ls : List LogKey)
    (ts : List TsaKey) : Prop :=
  AceFulcioAt Bf fp M k fs ∧ AceLogsAt Bf fp M (k + 0x100) ls ∧ AceTsasAt Bf fp M (k + 0x300) ts

/-- The `l` bytes at `p` lie in the document at `D` and are one value that
parses to `j`. -/
def AceVal (D : Word) (json : Bytes) (p : Word) (l : Nat) (j : Json) : Prop :=
  D.toNat ≤ p.toNat ∧ JDen false json (p.toNat - D.toNat) l j

/-- The array cursor at `c`: its words are the array's address `p`, its
length, and a position from which `nextElement` walks the items `rest`. -/
def AceCur (D : Word) (json : Bytes) (M : Word → BitVec 8) (c : Word) (rest : List Json) : Prop :=
  ∃ p l pos, memLoad32 M c = p ∧ memLoad32 M (c + 4) = BitVec.ofNat 32 l ∧
    memLoad32 M (c + 8) = BitVec.ofNat 32 pos ∧ pos < 2 ^ 32 ∧ D.toNat ≤ p.toNat ∧
    p.toNat - D.toNat + l ≤ json.length ∧ ElementsFrom false ((json.drop (p.toNat - D.toNat)).take l) pos rest

/-! ## The callees -/

/-- The extract stage's callees and the constants it reads. -/
structure AcExtractEnv (M : Word → BitVec 8) : Prop where
  parse : ParseCode M (BitVec.ofNat 32 jsonParseAddress)
  field : FieldCode M (BitVec.ofNat 32 jsonFieldAddress)
  str : CodeIn M (BitVec.ofNat 32 jsonStrAddress) jsonStrCode
  elems : CodeIn M RJE jsonElementsCode
  skipWs : CodeIn M RSW jsonSkipWsCode
  next : CodeIn M RJN jsonNextElementCode
  item : RiCode M (RJN + 0xFFFFF7E0)
  sliceNe : CodeIn M RSN sliceNeCode
  sliceEq : CodeIn M RSE sliceEqCode
  equal : CodeIn M RES equalSameLengthCode
  memcmp : CodeIn M RMC memcmpCode
  stub : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  body : CodeIn M (BitVec.ofNat 32 memcpyBodyAddress) memcpyBodyCode
  copy : CodeIn M (BitVec.ofNat 32 copyFromSliceU8Address) copyFromSliceU8Code
  eq97 : CodeIn M (BitVec.ofNat 32 eqArr97Address) eqArr97Code
  eq32 : CodeIn M (BitVec.ofNat 32 arr32EqAddress) arr32EqCode
  enumNext : CodeIn M (BitVec.ofNat 32 fulcioEnumNextAddress) fulcioEnumNextCode
  iterNth : CodeIn M (BitVec.ofNat 32 fulcioIterNthAddress) fulcioIterNthCode
  iterNext : CodeIn M (BitVec.ofNat 32 fulcioIterNextAddress) fulcioIterNextCode
  pk : PkEnv M
  decode : TrDecCode M
  validFor : TvfCode M
  chain : RcCode M
  kMedia : memBytes M 0x3FCC479A 9 = ascii!"mediaType"
  vMedia : memBytes M 0x3FCC47A3 0x39 = aceMediaType
  kCas : memBytes M 0x3FCC47DC 0x16 = ascii!"certificateAuthorities"
  kTlogs : memBytes M 0x3FCC47F2 5 = ascii!"tlogs"
  kTsas : memBytes M 0x3FCC47F7 0x14 = ascii!"timestampAuthorities"
  kKey : memBytes M 0x3FCC480B 9 = ascii!"publicKey"
  kDetails : memBytes M 0x3FCC4814 10 = ascii!"keyDetails"
  vEd25519 : memBytes M 0x3FCC481E 12 = ascii!"PKIX_ED25519"
  kRaw : memBytes M 0x3FCC4730 8 = ascii!"rawBytes"
  vPrefix : memBytes M 0x3FCC4690 12 = ed25519SpkiPrefix
  kUrl : memBytes M 0x3FCC482A 7 = ascii!"baseUrl"
  vHttps : memBytes M 0x3FCC4740 8 = ascii!"https://"
  vSlash : memBytes M 0x3FCC4831 1 = [0x2F]
  kValidFor : memBytes M 0x3FCC4700 8 = ascii!"validFor"
  kStart : memBytes M tvfStartKey 5 = ascii!"start"
  kEnd : memBytes M tvfEndKey 3 = ascii!"end"

/-! ## The stage -/

/-- The stack, `Buffers`, the read-only window, and the policy's last 0x23
bytes, which the stage copies, lie apart. -/
structure AceLayout (B Bf : Word) : Prop where
  fr : Fr B 0x5A70
  sep : Sep B 0x5A70 Bf acBufLen
  al : Bf.toNat % 4 = 0
  hi : Bf.toNat + acBufLen ≤ 0x40000000
  polStack : Sep 0x3FCC4051 0x23 B 0x5A70
  polBuf : Sep 0x3FCC4051 0x23 Bf acBufLen
  ro : Sep B 0x5A70 (BitVec.ofNat 32 roWindowAddress) roWindowSize

/-- At 0xC12: the trusted root's document `json` at `D` in `doc`, its
length in `s8`, `sp + 0x30` holding `keys`'s address, the result pointer
`r` at `sp + 0x40`, and the frame addresses in `s3` and `s6`. -/
structure AcExtractPre (B Bf r D : Word) (json : Bytes) (n : Machine) : Prop where
  docLo : Bf.toNat + 0x4000 ≤ D.toNat
  docHi : D.toNat + json.length ≤ Bf.toNat + 0x6800
  doc : memBytes n.mem D json.length = json
  r18 : reg n (18 : Fin 32) = D
  r19 : reg n (19 : Fin 32) = acSlot B 0x890
  r22 : reg n (22 : Fin 32) = acSlot B 0x1310
  r24 : reg n (24 : Fin 32) = BitVec.ofNat 32 json.length
  keys : memLoad32 n.mem (acSlot B 0x30) = Bf + 0x6800
  res : memLoad32 n.mem (acSlot B 0x40) = r

/-- `keys`'s free part starts at `fp`: the slice at `sp + 0x1FDC` holds it
and runs to the end of `keys`. -/
structure AceFr (B Bf : Word) (n : Machine) (fp : Word) : Prop where
  ptr : memLoad32 n.mem (acSlot B 0x1FDC) = fp
  len : memLoad32 n.mem (acSlot B 0x1FE0) = BitVec.ofNat 32 (Bf.toNat + 0xB840 - fp.toNat)
  lo : Bf.toNat + 0x6800 ≤ fp.toNat
  hi : fp.toNat ≤ Bf.toNat + 0xB840

/-- What the stage keeps of the machine `K` at 0xC12: the bytes `AceKept`
names, and `s5`, `s9`, and `s11`. -/
structure AceKeep (B Bf : Word) (K n : Machine) : Prop where
  mem : ∀ x, AceKept B Bf x → n.mem x = K.mem x
  regs : ∀ q : Fin 32, q.val ∈ [21, 25, 27] → reg n q = reg K q

/-- `sp + 0x20` holds the earlier of the two expiries at `sp + 0x20` and
`sp + 0x28` at 0xC12. -/
def AceExpiry (B : Word) (K n : Machine) : Prop :=
  aceU64 n.mem (acSlot B 0x20) = min (aceU64 K.mem (acSlot B 0x20)) (aceU64 K.mem (acSlot B 0x28))

/-- At 0x1816, the call of `memcpy` that copies the 0x423 bytes at
`sp + 0xDD0` to `sp + 0x1875`: when the document passes, those bytes are
the policy's last 0x23 bytes and the three arrays of the keys that
`extractTrustedRoot` gives, whose names and keys lie below `keys`'s free
part at `fp`. -/
def AcExtractPost (B Bf : Word) (M0 : Word → BitVec 8) (K : Machine) (json : Bytes) (n : Machine) : Prop :=
  ∃ fp fs ls ts,
    (∀ pol, extractTrustedRoot json pol = some ⟨fs, ls, ts, pol⟩) ∧
    AceKeysIn Bf fp n.mem (acSlot B 0xDF3) fs ls ts ∧
    memBytes n.mem (acSlot B 0xDD0) 0x23 = memBytes M0 0x3FCC4051 0x23 ∧
    AceFr B Bf n fp ∧ AceKeep B Bf K n ∧ AceExpiry B K n ∧
    reg n a0 = acSlot B 0x1875 ∧ reg n a1 = acSlot B 0xDD0 ∧ reg n a2 = 0x423 ∧
    reg n ra = AC + BitVec.ofNat 32 (0x1812 + 0x15000)

/-- **The extract stage**, from 0xC12 to 0x1816, for the callees and
constants `AcExtractEnv` in memory that agrees with `M0` outside the stack
and `Buffers`. -/
def AcExtractStage : Prop :=
  ∀ (n : Machine) (B Bf g t r D : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (json : Bytes),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcExtractEnv M) →
    AceLayout B Bf → CodeIn n.mem AC bootMainClosure0Code → St n.mem AC n 0xC12 (reg n) →
    AcInv B Bf g t v M0 n → AcExtractPre B Bf r D json n →
    AcStage B Bf g t r v M0 n 0x1816 (AcExtractPost B Bf M0 n json)

/-! ## The sub-stages -/

/-- What every sub-stage shares: the closure's parameters, the machine `K`
at 0xC12, and the document `json` at `D`. -/
structure AceCtx where
  B : Word
  Bf : Word
  g : Word
  t : Word
  r : Word
  D : Word
  v : Nat → Word
  M0 : Word → BitVec 8
  K : Machine
  json : Bytes

/-- `AcExtractStage`'s hypotheses, of the context `X`. -/
structure AceCtx.Ok (X : AceCtx) : Prop where
  env : ∀ M, (∀ x, Sep x 1 X.B 0x5A70 → Sep x 1 X.Bf acBufLen → M x = X.M0 x) → AcExtractEnv M
  lay : AceLayout X.B X.Bf
  code : CodeIn X.K.mem AC bootMainClosure0Code
  st : St X.K.mem AC X.K 0xC12 (reg X.K)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 X.K
  pre : AcExtractPre X.B X.Bf X.r X.D X.json X.K

/-- `AcStage` in the context `X`. -/
abbrev AceCtx.stage (X : AceCtx) (n : Machine) (o' : Nat) (Q : Machine → Prop) : Prop :=
  AcStage X.B X.Bf X.g X.t X.r X.v X.M0 n o' Q

/-- At every cut after 0xC12: the closure's code and state at `off`, what
the stage keeps, the expiry, and `keys`'s free part at `fp`. -/
structure AceAt (X : AceCtx) (n : Machine) (off : Nat) (fp : Word) : Prop where
  code : CodeIn n.mem AC bootMainClosure0Code
  st : St n.mem AC n off (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  fr : AceFr X.B X.Bf n fp
  keep : AceKeep X.B X.Bf X.K n
  exp : AceExpiry X.B X.K n

/-- `s10` and `sp + 0x30` hold the root object's slice of the document. -/
def AceObj (X : AceCtx) (n : Machine) (jr : Json) : Prop :=
  AceVal X.D X.json (reg n (26 : Fin 32)) (memLoad32 n.mem (acSlot X.B 0x30)).toNat jr

/-- At 0xD8C, before each certificate authority: `rest` are left, `fs` are
the Fulcio keys so far, in the array at `sp + 0x1ED0` and counted in `s6`,
and the cursor is at `sp + 0x1310`. -/
structure AceCaInv (X : AceCtx) (n : Machine) (fp : Word) (jr : Json) (rest : List Json) (fs : List FulcioKey) :
    Prop where
  root : AceRootJ X.json jr
  obj : AceObj X n jr
  cas : AceProg jr (ascii!"certificateAuthorities") aceCa rest fs
  cur : AceCur X.D X.json n.mem (acSlot X.B 0x1310) rest
  fulcio : AceFulcioAt X.Bf fp n.mem (acSlot X.B 0x1ED0) fs
  r9 : reg n (9 : Fin 32) = acSlot X.B 0x1310
  r18 : reg n (18 : Fin 32) = 7
  r19 : reg n (19 : Fin 32) = acSlot X.B 0x890
  r20 : reg n (20 : Fin 32) = acSlot X.B 0x1ED0
  r22 : reg n (22 : Fin 32) = BitVec.ofNat 32 fs.length

/-- At 0xEBA, before each transparency log: `rest` are left, `ls` are the
log keys so far, in the array at `sp + 0x350` and counted at `sp + 0x2C`,
and the cursor is at `sp + 0x1860`. -/
structure AceTlogInv (X : AceCtx) (n : Machine) (fp : Word) (jr : Json) (fs : List FulcioKey)
    (rest : List Json) (ls : List LogKey) : Prop where
  root : AceRootJ X.json jr
  obj : AceObj X n jr
  cas : AceProg jr (ascii!"certificateAuthorities") aceCa [] fs
  tlogs : AceProg jr (ascii!"tlogs") logEntry rest ls
  cur : AceCur X.D X.json n.mem (acSlot X.B 0x1860) rest
  fulcio : AceFulcioAt X.Bf fp n.mem (acSlot X.B 0x1ED0) fs
  logs : AceLogsAt X.Bf fp n.mem (acSlot X.B 0x350) ls
  count : memLoad32 n.mem (acSlot X.B 0x2C) = BitVec.ofNat 32 ls.length
  r19 : reg n (19 : Fin 32) = acSlot X.B 0x890

/-- At 0x123A, before each timestamp authority: `rest` are left, `ts` are
the TSA keys so far, in the array at `sp + 0x890` and counted in `s10`, and
the cursor is at `sp + 0x1DC8`. -/
structure AceTsaInv (X : AceCtx) (n : Machine) (fp : Word) (jr : Json) (fs : List FulcioKey) (ls : List LogKey)
    (rest : List Json) (ts : List TsaKey) : Prop where
  root : AceRootJ X.json jr
  cas : AceProg jr (ascii!"certificateAuthorities") aceCa [] fs
  tlogs : AceProg jr (ascii!"tlogs") logEntry [] ls
  tsas : AceProg jr (ascii!"timestampAuthorities") aceTsa rest ts
  cur : AceCur X.D X.json n.mem (acSlot X.B 0x1DC8) rest
  fulcio : AceFulcioAt X.Bf fp n.mem (acSlot X.B 0x1ED0) fs
  logs : AceLogsAt X.Bf fp n.mem (acSlot X.B 0x350) ls
  tsaKeys : AceTsasAt X.Bf fp n.mem (acSlot X.B 0x890) ts
  r19 : reg n (19 : Fin 32) = acSlot X.B 0x1310
  r26 : reg n (26 : Fin 32) = BitVec.ofNat 32 ts.length

/-- After the loops: every key, in the three arrays. -/
structure AceKeysRead (X : AceCtx) (n : Machine) (fp : Word) (fs : List FulcioKey) (ls : List LogKey)
    (ts : List TsaKey) : Prop where
  root : ∃ jr, AceRootJ X.json jr ∧ AceProg jr (ascii!"certificateAuthorities") aceCa [] fs ∧
    AceProg jr (ascii!"tlogs") logEntry [] ls ∧ AceProg jr (ascii!"timestampAuthorities") aceTsa [] ts
  fulcio : AceFulcioAt X.Bf fp n.mem (acSlot X.B 0x1ED0) fs
  logs : AceLogsAt X.Bf fp n.mem (acSlot X.B 0x350) ls
  tsaKeys : AceTsasAt X.Bf fp n.mem (acSlot X.B 0x890) ts

/-- 0xC12 to 0xD8C: the expiry, `parse`, `mediaType`, and the cursor over
`certificateAuthorities`. -/
def AceHeadStage : Prop :=
  ∀ X : AceCtx, X.Ok →
    X.stage X.K 0xD8C fun n => ∃ fp jr cas, AceAt X n 0xD8C fp ∧ AceCaInv X n fp jr cas []

/-- 0xD8C to 0xEBA: the certificate authorities left, then the cursor over
`tlogs`. -/
def AceCaStage : Prop :=
  ∀ X : AceCtx, X.Ok → ∀ n fp jr rest fs, AceAt X n 0xD8C fp → AceCaInv X n fp jr rest fs →
    X.stage n 0xEBA fun n' => ∃ fp' fs' tlogs, AceAt X n' 0xEBA fp' ∧ AceTlogInv X n' fp' jr fs' tlogs []

/-- 0xEBA to 0x123A: the transparency logs left, then the cursor over
`timestampAuthorities`. -/
def AceTlogStage : Prop :=
  ∀ X : AceCtx, X.Ok → ∀ n fp jr fs rest ls, AceAt X n 0xEBA fp → AceTlogInv X n fp jr fs rest ls →
    X.stage n 0x123A fun n' => ∃ fp' ls' tsas, AceAt X n' 0x123A fp' ∧ AceTsaInv X n' fp' jr fs ls' tsas []

/-- 0x123A to 0x1434: the timestamp authorities left. -/
def AceTsaStage : Prop :=
  ∀ X : AceCtx, X.Ok → ∀ n fp jr fs ls rest ts, AceAt X n 0x123A fp → AceTsaInv X n fp jr fs ls rest ts →
    X.stage n 0x1434 fun n' => ∃ fp' ts', AceAt X n' 0x1434 fp' ∧ AceKeysRead X n' fp' fs ls ts'

/-- 0x1434 to 0x1778: the six checks that no name or key is listed twice. -/
def AceDupStage : Prop :=
  ∀ X : AceCtx, X.Ok → ∀ n fp fs ls ts, AceAt X n 0x1434 fp → AceKeysRead X n fp fs ls ts →
    X.stage n 0x1778 fun n' => AceAt X n' 0x1778 fp ∧ AceKeysRead X n' fp fs ls ts ∧ AceDistinct fs ls ts

/-- 0x1778 to 0x1816: the copies of the arrays and the policy's last 0x23
bytes to `sp + 0xDD0`. -/
def AceTailStage : Prop :=
  ∀ X : AceCtx, X.Ok → ∀ n fp fs ls ts, AceAt X n 0x1778 fp → AceKeysRead X n fp fs ls ts →
    AceDistinct fs ls ts → X.stage n 0x1816 (AcExtractPost X.B X.Bf X.M0 X.K X.json)

end C3.RV32.Ac
