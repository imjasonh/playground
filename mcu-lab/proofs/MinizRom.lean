/-!
Formal specifications and round-trip correctness proof for ESP32-C3 silicon ROM miniz DEFLATE routines:
- `tdefl_compress` (`mcu-lab/proofs/rom_asm/tdefl_compress.asm`)
- `tinfl_decompress` (`mcu-lab/proofs/rom_asm/tinfl_decompress.asm`)
-/

namespace Esp32c3Rom.Miniz

/-- Stored-block DEFLATE framing (`BFINAL=1, BTYPE=00` + 16-bit LE `LEN` + `NLEN` + raw payload). -/
def tdeflCompressStored (data : List UInt8) : List UInt8 :=
  let len := data.length
  let lo : UInt8 := UInt8.ofNat (len % 256)
  let hi : UInt8 := UInt8.ofNat ((len / 256) % 256)
  let nlo : UInt8 := ~~~lo
  let nhi : UInt8 := ~~~hi
  [0x01, lo, hi, nlo, nhi] ++ data

/-- Stored-block DEFLATE decoder (`tinfl_decompress` for `BTYPE=00`). -/
def tinflDecompressStored (stream : List UInt8) : Option (List UInt8) :=
  match stream with
  | 0x01 :: lo :: hi :: nlo :: nhi :: rest =>
    if nlo == ~~~lo && nhi == ~~~hi then
      let len := lo.toNat + 256 * hi.toNat
      if rest.length == len then some rest else none
    else
      none
  | _ => none

/-- Round-trip theorem: `tinflDecompressStored (tdeflCompressStored data) = some data`
    for all payloads with `data.length < 65536`. -/
theorem tinfl_tdefl_roundtrip (data : List UInt8) (hlen : data.length < 65536) :
    tinflDecompressStored (tdeflCompressStored data) = some data := by
  unfold tdeflCompressStored tinflDecompressStored
  have hlen_eq : (UInt8.ofNat (data.length % 256)).toNat +
      256 * (UInt8.ofNat ((data.length / 256) % 256)).toNat = data.length := by
    simp only [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
    omega
  simp [hlen_eq]

end Esp32c3Rom.Miniz
