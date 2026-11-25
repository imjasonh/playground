import C3BootProofs.Proofs.AcceptAt
import C3BootProofs.Proofs.Panic
import C3BootProofs.Proofs.JsonFrame
import C3BootProofs.Proofs.TufRoleKeys
import C3BootProofs.Proofs.TufRoleKeysMetSpec
import C3BootProofs.Proofs.SvSpec
import C3BootProofs.Models.JsonLink
import C3BootProofs.Models.TufLinkKeys
import C3BootProofs.Models.TufLinkMeta

/-!
# `boot_main`'s first closure: the plan

`bootMainClosure0` (6,912 bytes at 0x403a00a6) is `|slot| check(slot,
efuse_level, &mut buffers)`. It inlines `check`, `check_slot`,
`tuf_slot::accept_slot`, `tuf::read_index`, `tuf::verify`,
`trusted_root::extract` (with `log_key`, `der_sequence`, `push`,
`has_duplicates`, and `TrustRoot::from_parts`), and `bundle::parse`. The
target is `acceptTufSlot` in `Spec/Accept.lean`.

## Arguments, frame, and exits

* `a0` is the result, an `Option<(Accepted, u32)>`, kept in `s3`. `a1` is
  `efuse_level` (`s10`), `a2` the `Buffers` (`s5`), and `a3` the slot
  (`s0`). The slot's flash base is 0x30000 for slot A and 0x210000 for
  slot B (`s8`).
* `Buffers`: the bundle at +0 (0x4000 bytes), `doc` at +0x4000 (0x2800),
  `keys` at +0x6800 (0x5040), and the header at +0xB840 (0x114).
* The prologue opens 0x100 bytes, saves `ra` and `s0..s11` at
  `sp + 0xFC` down to `sp + 0xCC`, and opens 0x1F20 more: 0x2020 in all.
  `sigstoreVerify` needs 0x3A50 bytes below the frame, the most of any
  callee, so the closure's stack is 0x5A70 bytes.
* Every failure reaches 0x16A, which logs `slot %x not bootable` through
  the ROM's `printf` (0x40000040), writes 0xFF at `result + 0xC` (`None`),
  and leaves through the epilogue at 0x184.
* A rejection reaches 0x7D6 with the error byte in `s5`. A byte below 0x20
  is logged as it is, and a larger one through the jump table at
  `roWindow + 4 * (e - 0x20)` as 0x100 to 0x106. Then 0x812 logs
  `slot rejected %x` and jumps to 0x16A.
* Success writes the result at 0x1A9C to 0x1AFC and jumps to the epilogue.

## Stages

| Offsets | What runs |
|---|---|
| 0x0-0x32 | prologue, slot base |
| 0x38-0x74 | `memset` of the 0x20-byte manifest buffer, `flashRead`, `manifestParse` |
| 0x7E-0xC6 | image address, header `flashRead` of `min(len, 0x114)` bytes |
| 0xC8-0x13C | SHA-256 of the image in 0x2800-byte chunks through `doc` (loop at 0x100) |
| 0x140-0x162 | bundle `flashRead` (at most 0x4000 bytes), TUF address |
| 0x1AA-0x29A | `image::parse`, the security-version check |
| 0x2A6-0x4E0 | `read_index`: `C3TU`, version 2, at most 64 roots, the lengths loop (0x3FE), `tufIndexDoc` |
| 0x504-0x574 | pinned root: `tufParseRoot`, `tufRoleKeysRead` for `root` and `targets`, `tufExpires` |
| 0x584-0x780 | the root loop: `tufReadDoc`, `tufParseRoot`, version + 1, `met` by the trusted and the new keys, the last root's `targets` keys and expiry |
| 0x836-0xC12 | `targets.json`: `tufParseMetadata`, `met`, `tufExpires`, the target's length and SHA-256; `trusted_root.json`: `tufReadDoc`, `sha256Fn`, hex digest, `memcmp` |
| 0xC12-0x1816 | `extract`: `jsonParse`, media type, the CA loop (0xD8C), the tlog loop (0xEBA), the TSA loop (0x123A), six duplicate checks, `from_parts` |
| 0x1816-0x1996 | `bundle::parse`: `readerMagic`, `readerVersion1`, six `bundleField` |
| 0x1A46 | `sigstoreVerify`, then the expiry check at 0x1A80 |

The stage files are `AcceptLib` (frame, prologue, exits, and calls),
`AcceptRead` (to 0x1AA), `AcceptIndex`, `AcceptRoots` (the root loop,
against `verifyTuf`'s `foldlM`), `AcceptTargets`, `AcceptExtract`,
`AcceptBundle`, and `AcceptSpec` (the composition).

## Contracts

Each call has a proved contract in the root: `RoleKeys::met` is
`tufRoleKeysMet_spec`, and `sigstoreVerify` is `sv_verify_spec`.
-/
