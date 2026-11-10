# c3-boot formats

This page defines every byte that the c3-boot bootloader reads from flash.
The Lean specification in `c3-boot-proofs/Spec/` and the `verify` crate
implement these definitions, and each must reject anything this page doesn't
allow. The `verify` crate doesn't implement all of them yet. The
[README](../README.md) lists what is done. The design behind the formats is in
[the verification plan](../../docs/esp32c3-verified-ota-plan.md).

All integers are little-endian unless a row says otherwise. Every reserved
field must be zero, and every parser rejects a nonzero reserved field, so
that a later format version can't be confused with this one.

Constants marked **(hardware)** come from the ESP32-C3 technical reference
manual and ESP-IDF. They need checking on a real board. The plan's
[Work that needs real hardware](../../docs/esp32c3-verified-ota-plan.md#work-that-needs-real-hardware)
section lists how.

## Flash layout

The bootloader uses a fixed layout compiled into it. It doesn't read an
ESP-IDF partition table, so a partition table can't move a slot. The layout
assumes 4 MiB of flash.

| Region | Start | End (exclusive) | Size |
| --- | --- | --- | --- |
| Bootloader image, loaded by the ROM | `0x000000` | `0x020000` | 128 KiB |
| Boot-state record, copy A | `0x020000` | `0x021000` | 4 KiB |
| Boot-state record, copy B | `0x021000` | `0x022000` | 4 KiB |
| Reserved | `0x022000` | `0x030000` | 56 KiB |
| Slot A | `0x030000` | `0x210000` | 1,920 KiB |
| Slot B | `0x210000` | `0x3F0000` | 1,920 KiB |
| Application data | `0x3F0000` | `0x400000` | 64 KiB |

Each boot-state copy fills one 4 KiB erase sector. Each slot starts on a
64 KiB boundary, because the cache maps flash in 64 KiB pages.
**(hardware)**

## Slot

A slot holds a manifest, the signed image, and the material that proves the
image is authentic.

| Slot offset | Contents |
| --- | --- |
| `0x00000` | [Slot manifest](#slot-manifest) |
| Manifest fields | [Signed image](#signed-image), [bundle container](#bundle-container), [key-set chain](#key-set-chain), and [trust-root blob](#trust-root-blob) |

### Slot manifest

The manifest isn't signed. It only says where the other parts are, and every
part it points to is checked on its own, so a forged manifest can only make
the slot fail.

| Offset | Size | Field | Rule |
| --- | --- | --- | --- |
| 0 | 4 | `magic` | ASCII `C3SL` |
| 4 | 2 | `format_version` | 1 |
| 6 | 2 | `reserved` | 0 |
| 8 | 4 | `image_offset` | `0x10000` |
| 12 | 4 | `image_length` | 37 through `0x1D0000` |
| 16 | 4 | `bundle_offset` | See the region rules |
| 20 | 4 | `bundle_length` | 49 through 16,384 |
| 24 | 4 | `chain_offset` | See the region rules |
| 28 | 4 | `chain_length` | 8 through 2,048 |
| 32 | 4 | `blob_offset` | See the region rules |
| 36 | 4 | `blob_length` | 443 through 4,096 |

Region rules:

- Each region's end, computed without overflow, is at most the slot size,
  `0x1E0000`.
- The regions are in the order image, bundle, chain, blob, and each starts
  at or after the end of the one before it.
- The image starts at slot offset `0x10000`, so that its first byte is on a
  64 KiB flash page.

## Signed image

The signed image is the byte string that the release workflow hashes and
signs. It is `image_length` bytes starting at `image_offset`: a header, a
segment table, and segment data. The SHA-256 digest of exactly these bytes is
the digest in the Rekor entry.

### Image header

| Offset | Size | Field | Rule |
| --- | --- | --- | --- |
| 0 | 4 | `magic` | ASCII `C3IM` |
| 4 | 2 | `format_version` | 1 |
| 6 | 2 | `chip_id` | 5, ESP-IDF's ID for the ESP32-C3 |
| 8 | 1 | `security_version` | 0 through 16 |
| 9 | 1 | `segment_count` | 1 through 16 |
| 10 | 2 | `reserved` | 0 |
| 12 | 4 | `entry_point` | Inside an executable segment |
| 16 | 4 | `image_length` | Equal to the manifest's `image_length` |
| 20 | 16 × `segment_count` | Segment table | See the next section |

The header and segment table together are `20 + 16 × segment_count` bytes.

### Segment table entry

| Offset | Size | Field | Rule |
| --- | --- | --- | --- |
| 0 | 1 | `kind` | 1 flash code, 2 flash data, 3 RAM code, or 4 RAM data |
| 1 | 3 | `reserved` | 0 |
| 4 | 4 | `address` | Virtual address of the segment's first byte |
| 8 | 4 | `offset` | Offset of the segment's data from the start of the image |
| 12 | 4 | `length` | Greater than 0 |

Segment rules:

- `offset + length`, computed without overflow, is at most `image_length`.
- The first segment's data starts at or after the end of the segment table.
- Segments are listed in order of `offset`, and each segment's data starts
  at or after the end of the previous segment's data, so no two data ranges
  overlap.
- The last segment's data ends exactly at `image_length`. Bytes between
  segments are padding. They are signed but never loaded or mapped.
- Each address range, `address` through `address + length`, computed without
  overflow, lies inside the region for its kind, from the next table.
- Flash segments (kinds 1 and 2) have `offset` and `address` that are
  multiples of `0x10000`, so the cache maps each 64 KiB image page to one
  64 KiB virtual page.
- No two segments overlap in physical memory. RAM code and RAM data use two
  views of the same SRAM, so the check first converts a RAM code address to
  its data-bus alias by subtracting `0x700000`. Flash code and flash data
  are separate virtual windows, so they can't alias each other or SRAM.
- `entry_point` lies inside a segment of kind 1 or 3, and is a multiple of 2.

| Kind | Address region (exclusive end) | **(hardware)** |
| --- | --- | --- |
| 1, flash code | `0x42000000` through `0x42800000` | Instruction cache window |
| 2, flash data | `0x3C000000` through `0x3C800000` | Data cache window |
| 3, RAM code | `0x40380000` through `0x403A0000` | Instruction bus view of the application RAM region |
| 4, RAM data | `0x3FC80000` through `0x3FCA0000` | Data bus view of the same region |

The application RAM region ends at `0x3FCA0000` on the data bus. The
bootloader's own code, data, and stack occupy `0x3FCA0000` through
`0x3FCDC710`, and the ROM uses the memory above that while it runs. The
bootloader copies RAM segments only into the application RAM region, so no
segment can overwrite the bootloader while it is checking or loading the
image. That is the failure behind CVE-2018-18558.

## Bundle container

CI builds the bundle container from the Sigstore bundle. The container
holds the same signed byte strings, in a fixed order, so the bootloader
doesn't parse JSON. Each field is a 4-byte length followed by that many bytes.

| Order | Field | Length rule | Contents |
| --- | --- | --- | --- |
| Header | `magic` and `format_version` | 6 bytes | ASCII `C3BN`, then version 1 as 2 bytes |
| 1 | `leaf_certificate` | 1 through 4,096 | The Fulcio leaf certificate, DER |
| 2 | `image_signature` | 8 through 72 | The ECDSA P-256 signature over the image digest, DER `ECDSA-Sig-Value`, exactly as logged in Rekor |
| 3 | `log_index` | 8 | The entry's index in the log, as an unsigned 64-bit integer |
| 4 | `inclusion_proof` | Multiple of 32, at most 64 × 32 | The RFC 6962 audit path, ordered from the leaf toward the root |
| 5 | `checkpoint` | 1 through 1,024 | The signed checkpoint note, as text |
| 6 | `timestamp` | 1 through 8,192 | The RFC 3161 `TimeStampToken`, DER |

Every field, including `log_index`, has the 4-byte length prefix, and
`log_index`'s length must be exactly 8. The smallest container is therefore
49 bytes: the 6-byte header, six 4-byte length prefixes, and 1, 8, 8, 0, 1,
and 1 bytes of field data.

The container ends after the last field. Trailing bytes are rejected. The
tree size and root hash come only from the checkpoint, so a container can't
pair a proof with a different tree than the one the log signed.

### Rekor v2 entry

The bootloader rebuilds the Rekor v2 `hashedrekord` entry and checks that
its RFC 6962 leaf hash, `SHA-256(0x00 || entry)`, is the leaf that the
inclusion proof starts from. The entry is the RFC 8785 canonical JSON form of
the protobuf JSON encoding, which is this template with no whitespace:

```json
{"apiVersion":"0.0.2","kind":"hashedrekord","spec":{"hashedRekordV002":{"data":{"algorithm":"SHA2_256","digest":"DIGEST"},"signature":{"content":"SIGNATURE","verifier":{"keyDetails":"PKIX_ECDSA_P256_SHA_256","x509Certificate":{"rawBytes":"CERTIFICATE"}}}}}}
```

Replace the following:

- `DIGEST`: the standard base64 encoding, with padding, of the image's
  SHA-256 digest.
- `SIGNATURE`: the standard base64 encoding, with padding, of
  `image_signature`.
- `CERTIFICATE`: the standard base64 encoding, with padding, of
  `leaf_certificate`.

This matches `ToEntryHash` in `rekor-tiles/pkg/types/hashedrekord`. Phase 1
checks it against real entries from the public log.

### Checkpoint

The checkpoint is a [C2SP signed note](https://c2sp.org/signed-note) whose
text is a [C2SP checkpoint](https://c2sp.org/tlog-checkpoint). The bootloader
accepts this shape only:

1. The origin line, equal to the origin of a log key in the trust-root blob.
2. The tree size, in decimal, with no leading zeros unless the value is 0,
   at most 2^63 − 1.
3. The root hash, standard base64 with padding, decoding to 32 bytes.
4. No extension lines.
5. A blank line.
6. One or more signature lines, each an em dash (U+2014), a space, a key
   name, a space, and standard base64 with padding, followed by a newline.

The bootloader verifies the signature line whose key name equals the origin
and whose decoded value starts with the log key's 4-byte key ID,
`SHA-256(origin || 0x0A || 0x01 || public key)[0..4]`. The rest of that
decoded value must be a 64-byte Ed25519 signature over the note text, which
runs from the first byte through the newline that ends the root hash line.
Exactly one signature line must match. Lines from other keys are ignored.

The bundle's `log_index` must be less than the tree size.

## Key-set chain

The chain is a header followed by zero through 16 links.

| Offset | Size | Field | Rule |
| --- | --- | --- | --- |
| 0 | 4 | `magic` | ASCII `C3KC` |
| 4 | 2 | `format_version` | 1 |
| 6 | 1 | `link_count` | 0 through 16 |
| 7 | 1 | `reserved` | 0 |
| 8 | Varies | Links | `link_count` links, back to back |

The chain ends after the last link. Trailing bytes are rejected.

### Link

| Offset | Size | Field | Rule |
| --- | --- | --- | --- |
| 0 | 1 | `level` | 1 through 16, and greater than the previous link's level |
| 1 | 1 | `key_count` | 1 through 4 |
| 2 | 32 × `key_count` | `keys` | Ed25519 public keys, pairwise distinct, each a canonical encoding of a curve point that doesn't have small order |
| Next | 1 | `signature_count` | 2 through 4 |
| Next | 65 × `signature_count` | `signatures` | Each a 1-byte key index followed by a 64-byte Ed25519 signature |

Each key index refers to the previous key set: the genesis set compiled into
the bootloader for the first link, and the previous link's `keys` otherwise.
The indexes must be strictly increasing, so no key counts twice, and each
must be less than the size of the previous key set. Every listed signature
must verify. At least two must be listed.

Each signature covers the 21-byte ASCII string `c3-boot chain link v1`, a
zero byte, and the link from `level` through the last key.

## Trust-root blob

| Offset | Size | Field | Rule |
| --- | --- | --- | --- |
| 0 | 4 | `magic` | ASCII `C3TR` |
| 4 | 2 | `format_version` | 1 |
| 6 | 4 | `sequence` | Any value. The bootloader ignores it |
| 10 | 1 | `level` | Equal to the image's `security_version`, at least the last link's level, and at least the security level |
| 11 | 1 | `reserved` | 0 |
| 12 | Varies | Fulcio intermediates | `count` (1 byte, 1 through 4), then that many entries |
| Next | Varies | Log keys | `count` (1 byte, 1 through 8), then that many entries |
| Next | Varies | TSA signers | `count` (1 byte, 1 through 4), then that many entries |
| Next | Varies | Identity policy | Five strings, in the order of the identity policy table |
| Next | 1 | `signature_count` | 2 through 4 |
| Next | 65 × `signature_count` | `signatures` | Each a 1-byte key index followed by a 64-byte Ed25519 signature |

The blob ends after the last signature. Trailing bytes are rejected.

The key indexes refer to the last link's `keys`, or to the genesis set if the
chain has no links. They follow the same rules as link signatures. Each
signature covers the 21-byte ASCII string `c3-boot trust root v1`, a zero
byte, and the blob from `magic` through the last policy string.

Within each list, entries are pairwise distinct: no two Fulcio entries share
a subject or a key, no two log entries share an origin or a key, and no two
TSA entries share a signer ID or a key. A checkpoint therefore matches at
most one log entry.

Every P-384 key must be an uncompressed SEC1 point on the curve, other than
the point at infinity. The bootloader rejects a blob with any other value.

A validity window is two unsigned 64-bit integers, `not_before` and
`not_after`, in seconds since the Unix epoch, with `not_before` at most
`not_after`. A time `t` is inside the window if
`not_before <= t <= not_after`.

### Fulcio intermediate entry

| Field | Size | Contents |
| --- | --- | --- |
| `subject_length` | 2 | 1 through 512 |
| `subject` | `subject_length` | The intermediate's subject `Name`, DER. The leaf's issuer must equal it byte for byte |
| `public_key` | 97 | Uncompressed SEC1 P-384 point |
| `window` | 16 | Validity window |

### Log key entry

| Field | Size | Contents |
| --- | --- | --- |
| `origin_length` | 1 | 1 through 128 |
| `origin` | `origin_length` | The log's origin string, printable ASCII |
| `public_key` | 32 | Ed25519 public key: a canonical encoding of a curve point that doesn't have small order |
| `window` | 16 | Validity window |

### TSA signer entry

| Field | Size | Contents |
| --- | --- | --- |
| `signer_id_length` | 2 | 1 through 512 |
| `signer_id` | `signer_id_length` | The DER `SignerIdentifier` that the token's `SignerInfo` must contain, byte for byte |
| `public_key` | 97 | Uncompressed SEC1 P-384 point |
| `window` | 16 | Validity window |

### Identity policy strings

Each string is a 2-byte length (1 through 512) followed by that many bytes
of printable ASCII.

| Order | Fulcio extension that must equal it |
| --- | --- |
| 1 | Issuer (V2), `1.3.6.1.4.1.57264.1.8` |
| 2 | Build Signer URI, `1.3.6.1.4.1.57264.1.9` |
| 3 | Source Repository Identifier, `1.3.6.1.4.1.57264.1.15` |
| 4 | Source Repository Owner Identifier, `1.3.6.1.4.1.57264.1.17` |
| 5 | Build Trigger, `1.3.6.1.4.1.57264.1.20` |

## Boot-state record

Each copy is 32 bytes at the start of its sector. The rest of the sector is
erased (all `0xFF`) and ignored.

| Offset | Size | Field | Rule |
| --- | --- | --- | --- |
| 0 | 4 | `magic` | ASCII `C3BS` |
| 4 | 2 | `format_version` | 1 |
| 6 | 2 | `reserved` | 0 |
| 8 | 4 | `generation` | Any value |
| 12 | 1 | `preferred_slot` | 0 for slot A or 1 for slot B |
| 13 | 1 | `trial_slot` | 0, 1, or `0xFF` for no trial |
| 14 | 1 | `trial_boots_left` | 0 through 3, and 0 when `trial_slot` is `0xFF` |
| 15 | 1 | `confirmed` | Bit 0 for slot A and bit 1 for slot B. Other bits 0 |
| 16 | 12 | `reserved` | 0 |
| 28 | 4 | `crc32` | CRC-32 (IEEE 802.3, the zlib polynomial) of bytes 0 through 27 |

A copy is valid if every rule holds. The bootloader reads both copies:

- If both are valid, it uses the one with the higher `generation`, or copy A
  if they are equal.
- If one is valid, it uses that one.
- If neither is valid, it uses the default state: preferred slot A, no
  trial, nothing confirmed.

To write a new state, it sets `generation` to one more than the copy in use,
or leaves it at `0xFFFFFFFF` if it is already there. It erases the sector of
the other copy and writes the new copy there. The copy in use isn't touched,
so it stays valid if power fails during the write. If neither copy is valid,
it writes copy A with `generation` 1.

### Slot selection

The first slot the bootloader tries is:

1. The trial slot, if `trial_slot` isn't `0xFF` and `trial_boots_left` is
   greater than 0. Before jumping to it, the bootloader writes a new state
   with `trial_boots_left` one lower.
2. Otherwise, the preferred slot. If `trial_slot` isn't `0xFF` and
   `trial_boots_left` is 0, the bootloader first writes a new state with no
   trial, which reverts to the preferred slot.

If the first slot fails any check, the bootloader tries the other slot with
the same checks. If the slot that failed was a trial slot, it first writes a
new state with no trial. If both slots fail, it halts.

The application confirms a slot by writing a state with that slot's bit set
in `confirmed`, `preferred_slot` set to it, and no trial. It starts a trial
by writing a state with `trial_slot` set to the inactive slot,
`trial_boots_left` set to 3, and that slot's `confirmed` bit cleared. The
application can write anything here, so the bootloader treats the record as
a hint. Every slot it boots passes every check.

## Security level

The security level `L` is the number of set bits in the 16-bit
`SECURE_VERSION` eFuse field, block 0, bits 142 through 157. Block 0 has no
Reed-Solomon coding, so the bootloader can set one bit at a time.
**(hardware)**

When the bootloader is about to jump to a slot that the record marks
confirmed, and the slot's level is greater than `L`, it raises `L` to the
slot's level first:

1. Program the lowest clear bit of `SECURE_VERSION`.
2. Read the field back. If the count didn't increase, retry the same bit up
   to two more times, then halt.
3. Repeat until the count equals the slot's level.

It then locks the eFuse controller and jumps.
