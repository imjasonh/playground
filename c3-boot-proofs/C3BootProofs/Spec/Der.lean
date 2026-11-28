import C3BootProofs.Spec.Formats

/-!
# DER

An executable model of the reader in `c3_verify::der`: one-byte tags,
definite lengths in their shortest form, and at most four length bytes
after the first. Bytes are natural numbers below 256. `usize` is 32 bits,
so a long-form length that passes `2 ^ 32` fails as Rust's `checked_mul`
and `checked_add` do.
-/

namespace C3

/-- The errors the DER reader returns. -/
inductive DerError
  | truncated
  | badDer
  | overflow
  deriving DecidableEq, Repr

/-- One element read from the front of the unread bytes: its tag, the
number of tag and length bytes, and the number of content bytes. -/
structure DerTlv where
  tag : Nat
  header : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- A long-form length from its bytes, most significant first, starting
from `acc`. -/
def derLongLen : Nat → Bytes → Except DerError Nat
  | acc, [] => .ok acc
  | acc, b :: bs => if acc * 256 + b < u32Limit then derLongLen (acc * 256 + b) bs else .error .overflow

/-- `Der::tlv`: the element at the front of `rest`. -/
def derTlv (rest : Bytes) : Except DerError DerTlv :=
  match rest with
  | [] => .error .truncated
  | tag :: afterTag =>
    if tag % 32 = 31 then .error .badDer
    else
      match afterTag with
      | [] => .error .truncated
      | first :: afterLen =>
        if first < 0x80 then
          if afterLen.length < first then .error .truncated else .ok ⟨tag, 2, first⟩
        else
          let count := first % 128
          if count = 0 ∨ 4 < count then .error .badDer
          else if afterLen.length < count then .error .truncated
          else if afterLen.head? = some 0 then .error .badDer
          else
            match derLongLen 0 (afterLen.take count) with
            | .error e => .error e
            | .ok len =>
              if len < 0x80 then .error .badDer
              else if afterLen.length - count < len then .error .truncated
              else .ok ⟨tag, 2 + count, len⟩

/-- `Der::element`: the element at the front of `rest`, which must have tag
`tag`. -/
def derElement (tag : Nat) (rest : Bytes) : Except DerError DerTlv :=
  match rest with
  | [] => .error .truncated
  | t :: _ => if t = tag then derTlv rest else .error .badDer

/-- The content bytes of an element read from the front of `rest`. -/
def DerTlv.content (t : DerTlv) (rest : Bytes) : Bytes := (rest.drop t.header).take t.len

/-- Whether `content` is a valid `OBJECT IDENTIFIER` body: not empty, each
subidentifier in its shortest base-128 form, and the last byte ending one. -/
def derOidOk (content : Bytes) : Bool :=
  let rec go : Bool → Bytes → Bool
    | atStart, [] => atStart
    | atStart, b :: bs => if atStart && b == 0x80 then false else go (b < 0x80) bs
  !content.isEmpty && go true content

/-- `Der::oid`: an `OBJECT IDENTIFIER` element at the front of `rest`. -/
def derOid (rest : Bytes) : Except DerError DerTlv :=
  match derElement 6 rest with
  | .error e => .error e
  | .ok t => if derOidOk (t.content rest) then .ok t else .error .badDer

end C3
