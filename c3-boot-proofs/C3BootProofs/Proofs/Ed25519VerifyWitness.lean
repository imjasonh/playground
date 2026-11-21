import C3BootProofs.Proofs.Ed25519VerifyC
import C3BootProofs.Proofs.RegionMem

/-!
# A machine that meets `ed25519Verify_correct`'s hypotheses

Memory with `ed25519_verify`, every function it calls, the panic code, the
tables of `L` and SHA-512's round constants where the image loads them,
SHA-512's initial hash value at `0x3FCC4AF8`, and zeros elsewhere.
-/

namespace C3.RV32

open C3.Image

/-- SHA-512's initial hash value as `ed25519_verify` reads it: each word
little-endian, low half first. -/
def sha512IvBytes : List Nat :=
  Sha512.h0.flatMap fun w => (List.range 8).map fun i => w.toNat / 256 ^ i % 256

def witnessRegionsEv : List (Nat × List Nat) :=
  panicFns ++
  [(ed25519VerifyAddress, ed25519VerifyCode), (scalar29SubAddress, scalar29SubCode),
    (scalar29IndexAddress, scalar29IndexCode), (scalar29IndexMutAddress, scalar29IndexMutCode),
    (scalarLAddress, scalarLData), (scalar29PackAddress, scalar29PackCode),
    (sha512UpdateAddress, sha512UpdateCode), (sha384UpdateBlocksAddress, sha384UpdateBlocksCode),
    (sha512CompressAddress, sha512CompressCode), (rangeFromIndexAddress, rangeFromIndexCode),
    (sha512KAddress, sha512KData), (sha512FinBlockAddress, sha512FinBlockCode),
    (sha512UpdateArr32Address, sha512UpdateArr32Code), (zeroArray64Address, zeroArray64Code),
    (scalar29MontMulAddress, scalar29MontMulCode), (nonAdjacentFormAddress, nonAdjacentFormCode),
    (lshrdi3Address, lshrdi3Code), (ashldi3Address, ashldi3Code), (nafTableFromAddress, nafTableFromCode),
    (asProjNielsAddress, asProjNielsCode), (edAddNielsAddress, edAddNielsCode),
    (edSubNielsAddress, edSubNielsCode), (nafSelectAddress, nafSelectCode),
    (ed25519PublicKeyOkAddress, ed25519PublicKeyOkCode),
    (edVerifyingKeyFromBytesAddress, edVerifyingKeyFromBytesCode),
    (lessThanLeAddress, lessThanLeCode), (arr32EqCryptoAddress, arr32EqCryptoCode),
    (memcmpAddress, memcmpCode), (memsetAddress, memsetCode),
    (edDoubleAddress, edDoubleCode), (asProjectiveAddress, asProjectiveCode),
    (asExtendedAddress, asExtendedCode), (isSmallOrderAddress, isSmallOrderCode),
    (edDecompressAddress, edDecompressCode), (feLoad3Address, feLoad3Code),
    (feLoad4Address, feLoad4Code), (feReduceAddress, feReduceCode),
    (feSquareAddress, feSquareCode), (feSquareInnerAddress, feSquareInnerCode),
    (feSubAddress, feSubCode), (feAddAddress, feAddCode),
    (feMulAddress, feMulCode), (pow22501Address, pow22501Code),
    (fePow2kAddress, fePow2kCode), (feCtEqAddress, feCtEqCode),
    (feToBytesAddress, feToBytesCode), (ctEqSliceAddress, ctEqSliceCode),
    (ctEqU8Address, ctEqU8Code), (blackBoxU8Address, blackBoxU8Code),
    (feNegAddress, feNegCode), (feCondAssignAddress, feCondAssignCode),
    (feIsNegativeAddress, feIsNegativeCode), (feCondNegAddress, feCondNegCode),
    (memcpyStubAddress, memcpyStubCode), (memcpyBodyAddress, memcpyBodyCode),
    (edOneAddress, edOneData), (edDAddress, edDData), (edSqrtM1Address, edSqrtM1Data),
    (0x3FCC4AF8, sha512IvBytes)]

def witnessMemEv : Word → BitVec 8 := regionMem witnessRegionsEv

set_option maxRecDepth 200000 in
theorem witnessRegionsEv_apart : regionsApart witnessRegionsEv = true := by decide +kernel

/-- Closes `CodeIn witnessMemEv base code` from the region list. -/
local macro "code_ev" : tactic =>
  `(tactic| exact regionMem_codeIn_of_any witnessRegionsEv_apart (by decide +kernel))

/-- The registers on entry: `sp` above the frame at `0x3FCD0000`, the key,
message, length, and signature in `a0` to `a3`, and zeros elsewhere. -/
def witnessRegsEv : Fin 32 → Word := fun r =>
  if r = sp then 0x3FCD16A0 else if r = a0 then 0x3FCC6000 else if r = a1 then 0x3FCC6200
  else if r = a2 then 0 else if r = a3 then 0x3FCC6100 else 0

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- A machine that verifies an empty message against the key at
`0x3FCC6000` and the signature at `0x3FCC6100`, with its frame at
`0x3FCD0000`, meets `ed25519Verify_correct`'s hypotheses. -/
theorem exists_ed25519Verify_machine :
    ∃ (m : Machine) (F pk sig msg : Word) (len : Nat), EvCtx m.mem F pk sig msg len ∧ m.pc = EV ∧
      reg m sp = F + BitVec.ofNat 32 0x16A0 ∧ reg m a0 = pk ∧ reg m a1 = msg ∧ reg m a2 = BitVec.ofNat 32 len ∧
      reg m a3 = sig ∧ reg m ra &&& ~~~1 = reg m ra := by
  refine ⟨⟨witnessRegsEv, EV, witnessMemEv⟩, 0x3FCD0000, 0x3FCC6000, 0x3FCC6100, 0x3FCC6200, 0, ?_, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩
  refine ⟨?_, by decide, by decide, by decide, sep_of_le (by decide) (by decide), sep_of_le (by decide) (by decide),
    sep_of_le (by decide) (by decide), sep_of_le (by decide) (by decide), by decide, by decide, by decide, by decide,
    by decide, by decide +kernel⟩
  exact ⟨⟨⟨by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev,
      by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev,
      by code_ev, by code_ev, by code_ev, by code_ev⟩,
    ⟨by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev,
      by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev,
      by decide +kernel⟩,
    by code_ev, by code_ev, by code_ev, by code_ev, by code_ev⟩,
    by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev,
    by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev, by code_ev,
    by code_ev, by code_ev, by code_ev, by code_ev, by code_ev,
    fun _ hp => regionMem_codeIn witnessRegionsEv_apart (List.mem_append_left _ hp)⟩

end C3.RV32

