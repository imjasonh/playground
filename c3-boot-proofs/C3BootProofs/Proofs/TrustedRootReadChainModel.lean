import C3BootProofs.Proofs.TrustedRootValidFor
import C3BootProofs.Proofs.JsonMembers
import C3BootProofs.Proofs.JsonNextElement
import C3BootProofs.Proofs.DerAlgorithm
import C3BootProofs.Proofs.DerReaders
import C3BootProofs.Proofs.DerOptional
import C3BootProofs.Proofs.X509ReadTime
import C3BootProofs.Proofs.Fs384Main
import C3BootProofs.Spec.TrustedRoot

/-!
# The position-level model of `trusted_root::read_chain`

`read_chain(entry, free)` reads an entry's `validFor` window and its
`certChain.certificates` array of one to four certificates. It decodes each
certificate's `rawBytes` into the scratch buffer that `free` holds,
parses it with `parse_cert`, which the compiler inlines, and intersects the
window with each certificate's validity. It returns the first certificate
and the window.

`rcParse` is `parse_cert` on a certificate's bytes `L` at `p`: the
pointers and lengths it keeps, and its two times. Readers over `L` are
offsets, so `rcParse` reads only `L`. `rcKey` is `p384_key`: the address
of the 97-byte point of a P-384 key on the curve, or 0 for any other key.
`readChainPos` is `read_chain` on the entry's bytes, with the decoded
certificates at `fp`.

An error's byte is `none` where the callee's theorem leaves it open: the
`Err` of `time::read_time` and of `trusted_root::decode`.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.Dq C3.RV32.P3

/-- A DER reader over a certificate's bytes: the offset of its next unread
byte and the number of unread bytes. -/
abbrev RcRd := Nat × Nat

/-- The unread bytes of the reader `r` over `L`. -/
def rcView (L : Bytes) (r : RcRd) : Bytes := (L.drop r.1).take r.2

/-- A reader over the contents of the element `t` at the front of `r`. -/
def rcIn (r : RcRd) (t : DerTlv) : RcRd := (r.1 + t.header, t.len)

/-- The reader `r` after the element `t` at its front. -/
def rcAdv (r : RcRd) (t : DerTlv) : RcRd := (r.1 + (t.header + t.len), r.2 - (t.header + t.len))

/-- The whole element `t` at the front of `r`, tag and length included. -/
def rcRaw (r : RcRd) (t : DerTlv) : RcRd := (r.1, t.header + t.len)

/-- `Der::element` on the reader `r`, with the error byte the code stores. -/
def rcElem (L : Bytes) (tag : Nat) (r : RcRd) : Except (Option Nat) DerTlv :=
  match derElement tag (rcView L r) with
  | .error e => .error (some (derErrByte e).toNat)
  | .ok t => .ok t

/-- `Der::algorithm` on the reader `r`: the offset and length of the OID's
contents, and the offset and element of the parameters, if any. -/
def rcAlg (L : Bytes) (r : RcRd) : Except Unit ((Nat × Nat) × Option (Nat × DerTlv)) :=
  match derElement 0x30 (rcView L r) with
  | .error _ => .error ()
  | .ok t =>
    match derOid (rcView L (r.1 + t.header, t.len)) with
    | .error _ => .error ()
    | .ok o =>
      if t.len - (o.header + o.len) = 0 then .ok ((r.1 + t.header + o.header, o.len), none)
      else
        match derTlv (rcView L (r.1 + t.header + (o.header + o.len), t.len - (o.header + o.len))) with
        | .error _ => .error ()
        | .ok u =>
          if u.header + u.len = t.len - (o.header + o.len) then
            .ok ((r.1 + t.header + o.header, o.len), some (r.1 + t.header + (o.header + o.len), u))
          else .error ()

/-- `from_sec1_bytes` accepts the 97 bytes `B`: tag 4, then `x` and `y`
below `p` on the curve, as `Fs.FsOk` checks them. -/
def rcFsOk (B : Bytes) : Prop :=
  B.getD 0 0 = 4 ∧ beNat ((B.drop 1).take 48) < p384 ∧ beNat ((B.drop 0x31).take 48) < p384 ∧
    p3fm (beNat ((B.drop 0x31).take 48) * 2 ^ 384 % p384) (beNat ((B.drop 0x31).take 48) * 2 ^ 384 % p384) =
      dqAlpha (beNat ((B.drop 1).take 48) * 2 ^ 384 % p384)

instance (B : Bytes) : Decidable (rcFsOk B) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Whether the parameters of an algorithm are the OID `secp384r1`. -/
def rcCurveOk (L : Bytes) : Option (Nat × DerTlv) → Bool
  | none => false
  | some (q, u) => u.tag == 6 && rcView L (q + u.header, u.len) == oidSecp384r1

/-- `p384_key` on the `SubjectPublicKeyInfo` at `r`, for a certificate
whose bytes `L` are at `p`: the address of its 97-byte point when the key
is a P-384 point on the curve, or 0. -/
def rcKey (L : Bytes) (p : Word) (r : RcRd) : Word :=
  match derElement 0x30 (rcView L r) with
  | .error _ => 0
  | .ok s =>
    if r.2 - (s.header + s.len) ≠ 0 then 0 else
    match derElement 0x30 (rcView L (rcIn r s)) with
    | .error _ => 0
    | .ok a =>
      match rcAlg L (rcIn r s) with
      | .error _ => 0
      | .ok ((oo, ol), par) =>
        if rcCurveOk L par = false then 0
        else if rcView L (oo, ol) ≠ oidEcPublicKey then 0
        else
          let b := rcAdv (rcIn r s) a
          match derElement 3 (rcView L b) with
          | .error _ => 0
          | .ok bt =>
            if ¬(bt.len ≠ 0 ∧ (rcView L b).getD bt.header 0 = 0) then 0
            else if bt.len - 1 ≠ 0x61 then 0
            else if b.2 - (bt.header + bt.len) ≠ 0 then 0
            else if rcFsOk (rcView L (b.1 + bt.header + 1, 0x61)) then p + BitVec.ofNat 32 (b.1 + bt.header + 1)
            else 0

/-- The fields of a certificate that `read_chain` keeps: the addresses and
lengths of its whole serial number, issuer, and subject, its validity,
and the address of its P-384 point, or 0. -/
structure RcCert where
  serial : Word
  serialLen : Nat
  issuer : Word
  issuerLen : Nat
  subject : Word
  subjectLen : Nat
  notBefore : Nat
  notAfter : Nat
  key : Word

/-- From the subject: the subject and the key. -/
def rcSubj (L : Bytes) (p : Word) (sr ir : RcRd) (nb na : Nat) (t : RcRd) : Except (Option Nat) RcCert :=
  match rcElem L 0x30 t with
  | .error e => .error e
  | .ok s =>
    match rcElem L 0x30 (rcAdv t s) with
    | .error e => .error e
    | .ok k =>
      .ok ⟨p + BitVec.ofNat 32 sr.1, sr.2, p + BitVec.ofNat 32 ir.1, ir.2, p + BitVec.ofNat 32 t.1,
        s.header + s.len, nb, na, rcKey L p (rcRaw (rcAdv t s) k)⟩

/-- From the validity's contents `v`: its two times, then the rest of the
`tbsCertificate` at `t`. -/
def rcTimes (L : Bytes) (p : Word) (sr ir v t : RcRd) : Except (Option Nat) RcCert :=
  match readTime (rcView L v) with
  | none => .error none
  | some (nb, r1) =>
    match readTime (rcView L (v.1 + (v.2 - r1.length), r1.length)) with
    | none => .error none
    | some (na, r2) => if r2.length ≠ 0 then .error (some 1) else rcSubj L p sr ir nb na t

/-- From the serial number: the serial number, signature algorithm,
issuer, and validity. -/
def rcSerial (L : Bytes) (p : Word) (t : RcRd) : Except (Option Nat) RcCert :=
  match rcElem L 2 t with
  | .error e => .error e
  | .ok s =>
    match rcElem L 0x30 (rcAdv t s) with
    | .error e => .error e
    | .ok a =>
      match rcElem L 0x30 (rcAdv (rcAdv t s) a) with
      | .error e => .error e
      | .ok i =>
        match rcElem L 0x30 (rcAdv (rcAdv (rcAdv t s) a) i) with
        | .error e => .error e
        | .ok v =>
          rcTimes L p (rcRaw t s) (rcRaw (rcAdv (rcAdv t s) a) i) (rcIn (rcAdv (rcAdv (rcAdv t s) a) i) v)
            (rcAdv (rcAdv (rcAdv (rcAdv t s) a) i) v)

/-- The `tbsCertificate`'s contents `t`: the optional version, then the
rest from the serial number. -/
def rcTbs (L : Bytes) (p : Word) (t : RcRd) : Except (Option Nat) RcCert :=
  match derOptRes 0xA0 (rcView L t) with
  | some (.error e) => .error (some (derErrByte e).toNat)
  | some (.ok u) => rcSerial L p (rcAdv t u)
  | none => rcSerial L p t

/-- The certificate's contents `c`: the `tbsCertificate`, the signature
algorithm, and the signature, and nothing after them. -/
def rcBody (L : Bytes) (p : Word) (c : RcRd) : Except (Option Nat) RcCert :=
  match rcElem L 0x30 c with
  | .error e => .error e
  | .ok tbs =>
    match rcElem L 0x30 (rcAdv c tbs) with
    | .error e => .error e
    | .ok a =>
      match rcElem L 3 (rcAdv (rcAdv c tbs) a) with
      | .error e => .error e
      | .ok b =>
        if ¬(b.len ≠ 0 ∧ (rcView L (rcAdv (rcAdv c tbs) a)).getD b.header 0 = 0) then .error (some 0x14)
        else if (rcAdv (rcAdv (rcAdv c tbs) a) b).2 ≠ 0 then .error (some 1)
        else rcTbs L p (rcIn c tbs)

/-- `parse_cert` on the certificate bytes `L` at `p`. -/
def rcParse (L : Bytes) (p : Word) : Except (Option Nat) RcCert :=
  match rcElem L 0x30 (0, L.length) with
  | .error e => .error e
  | .ok c => if L.length - (c.header + c.len) ≠ 0 then .error (some 1) else rcBody L p (rcIn (0, L.length) c)

/-- `read_chain`'s state between certificates: the array cursor's position,
the bytes decoded so far, the first certificate, and the window. -/
structure RcSt where
  pos : Nat
  dec : Bytes
  first : Option RcCert
  nb : Nat
  na : Nat

/-- One certificate, the element of `l` bytes at `q`, whose array cursor
moves to `after`: its `rawBytes` decoded after `s.dec` in the buffer of
`fl` bytes at `fp`, and parsed. -/
def rcStep (M0 : Word → BitVec 8) (fp : Word) (fl : Nat) (q : Word) (l after : Nat) (s : RcSt) :
    Except (Option Nat) RcSt :=
  match objField (memBytes M0 q l) (ascii!"rawBytes") with
  | .error e => .error (some e)
  | .ok x =>
    match strRes (q + BitVec.ofNat 32 x.1) (memBytes M0 (q + BitVec.ofNat 32 x.1) x.2) with
    | none => .error (some 0x21)
    | some (b, bl) =>
      match trDecodeRes (base64Decode (memBytes M0 b bl)) (fl - s.dec.length) with
      | none => .error none
      | some bs =>
        match rcParse bs (fp + BitVec.ofNat 32 s.dec.length) with
        | .error e => .error e
        | .ok c => .ok ⟨after, s.dec ++ bs, s.first.or (some c), max s.nb c.notBefore, min s.na c.notAfter⟩

/-- The loop over at most `k` more certificates of the array of `an` bytes
at `ap`. -/
def rcLoop (M0 : Word → BitVec 8) (fp : Word) (fl : Nat) (ap : Word) (an : Nat) :
    Nat → RcSt → Except (Option Nat) RcSt
  | 0, s => .ok s
  | k + 1, s =>
    match nextElement (memBytes M0 ap an) s.pos with
    | none => .error (some 0x20)
    | some none => .ok s
    | some (some (st, len, after)) =>
      match rcStep M0 fp fl (ap + BitVec.ofNat 32 st) len after s with
      | .error e => .error e
      | .ok s' => rcLoop M0 fp fl ap an k s'

/-- After the loop: the array must end, and must have had a certificate. -/
def rcFinish (M0 : Word → BitVec 8) (ap : Word) (an : Nat) (s : RcSt) : Except (Option Nat) (RcCert × RcSt) :=
  match nextElement (memBytes M0 ap an) s.pos with
  | none => .error (some 0x20)
  | some (some _) => .error (some 0x21)
  | some none =>
    match s.first with
    | none => .error (some 0x21)
    | some c => .ok (c, s)

/-- From the `certificates` array, whose source is the `an` bytes at `ap`,
with the entry's window `nb`–`na`. -/
def rcChain (M0 : Word → BitVec 8) (fp : Word) (fl : Nat) (ap : Word) (an nb na : Nat) :
    Except (Option Nat) (RcCert × RcSt) :=
  match curOpen 91 ap (memBytes M0 ap an) with
  | none => .error (some 0x21)
  | some (ap', an', pos) =>
    match rcLoop M0 fp fl ap' an' 4 ⟨pos, [], none, nb, na⟩ with
    | .error e => .error e
    | .ok s => rcFinish M0 ap' an' s

/-- `read_chain` on the entry whose source is the `n` bytes at `p`, with
the scratch buffer of `fl` bytes at `fp`: the first certificate and the
final state, whose window is the result's, or the error byte. -/
def readChainPos (M0 : Word → BitVec 8) (p : Word) (n : Nat) (fp : Word) (fl : Nat) :
    Except (Option Nat) (RcCert × RcSt) :=
  match objField (memBytes M0 p n) (ascii!"validFor") with
  | .error e => .error (some e)
  | .ok x =>
    match validForPos (memBytes M0 (p + BitVec.ofNat 32 x.1) x.2) with
    | .error e => .error (some e)
    | .ok (nb, na) =>
      match objField (memBytes M0 p n) (ascii!"certChain") with
      | .error e => .error (some e)
      | .ok y =>
        match objField (memBytes M0 (p + BitVec.ofNat 32 y.1) y.2) (ascii!"certificates") with
        | .error e => .error (some e)
        | .ok z => rcChain M0 fp fl (p + BitVec.ofNat 32 y.1 + BitVec.ofNat 32 z.1) z.2 nb na

/-- `Result<(Cert, Window), TufError>` at `out`, and the scratch slice at
`fr`. An `Err` is a null serial pointer, the niche, and the error byte at
`out + 4` when the model names it. An `Ok` is the `Cert` in the first 0x2C
bytes and the window in the four words from `out + 0x30`; the scratch
slice then starts after the decoded certificates, which the buffer
holds. -/
def RcOut (M : Word → BitVec 8) (out fr fp : Word) (fl : Nat) : Except (Option Nat) (RcCert × RcSt) → Prop
  | .error e => memLoad32 M out = 0 ∧ ∀ b, e = some b → M (out + 4) = BitVec.ofNat 8 b
  | .ok (c, s) =>
    memLoad32 M out = c.serial ∧ memLoad32 M (out + 4) = BitVec.ofNat 32 c.serialLen ∧
    memLoad32 M (out + 8) = c.issuer ∧ memLoad32 M (out + 0xC) = BitVec.ofNat 32 c.issuerLen ∧
    memLoad32 M (out + 0x10) = c.subject ∧ memLoad32 M (out + 0x14) = BitVec.ofNat 32 c.subjectLen ∧
    memLoad32 M (out + 0x18) = BitVec.ofNat 32 (c.notBefore % 2 ^ 32) ∧
    memLoad32 M (out + 0x1C) = BitVec.ofNat 32 (c.notBefore / 2 ^ 32) ∧
    memLoad32 M (out + 0x20) = BitVec.ofNat 32 (c.notAfter % 2 ^ 32) ∧
    memLoad32 M (out + 0x24) = BitVec.ofNat 32 (c.notAfter / 2 ^ 32) ∧
    memLoad32 M (out + 0x28) = c.key ∧
    memLoad32 M (out + 0x30) = BitVec.ofNat 32 (s.nb % 2 ^ 32) ∧
    memLoad32 M (out + 0x34) = BitVec.ofNat 32 (s.nb / 2 ^ 32) ∧
    memLoad32 M (out + 0x38) = BitVec.ofNat 32 (s.na % 2 ^ 32) ∧
    memLoad32 M (out + 0x3C) = BitVec.ofNat 32 (s.na / 2 ^ 32) ∧
    c.notBefore < 2 ^ 64 ∧ c.notAfter < 2 ^ 64 ∧ s.nb < 2 ^ 64 ∧ s.na < 2 ^ 64 ∧
    s.dec.length ≤ fl ∧ memLoad32 M fr = fp + BitVec.ofNat 32 s.dec.length ∧
    memLoad32 M (fr + 4) = BitVec.ofNat 32 (fl - s.dec.length) ∧ memBytes M fp s.dec.length = s.dec

end C3.RV32
