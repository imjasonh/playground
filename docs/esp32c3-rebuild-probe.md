# ESP32-C3 bootloader rebuild probe

This page measures how much of the machine-code proof work in
`c3-boot-proofs/` survives a rebuild of the `c3-boot` bootloader. The
trust-anchoring change in `c3-boot/TODO.md` and the production configuration
(`C3_EFUSE_BURN=on` and a real `efuse::lock()`) each produce a new image, and
the proofs are about the bytes of one image. The probe rebuilt the image three
ways, extracted each one, and checked the Lean project against the result. It
changes no proofs or Rust code. It ran against commit `f03a0a14d` of
`cursor/esp32c3-verified-ota-plan-b66c`.

## Results

- A small rebuild changes 55 to 58 of the 264 extracted functions. One or two
  of them change shape. The others differ only in immediates that encode an
  absolute address. The bootloader crate's functions come first in `.text`,
  so the whole library moves when one of them grows, and most of `.rodata`
  moves when a string is added.
- The proofs depend on those immediates. For the variant that adds one log
  line, 98 modules fail on their own, and Lake can't build 621 of the 735
  modules because each one imports a failing module. `SvSpec.lean` and
  `BootSpec.lean` are among the 621.
- Almost all of the breakage is mechanical, but a text rewrite can't finish
  the job. A prototype that rewrites decode lemmas, code chunks, and address
  literals from the new extraction cut the unbuilt modules from 621 to 476.
  With hand edits in 6 more files, 2 modules still fail and 308 stay
  unbuilt. Each remaining failure is an address that the proof text states in
  a form a rewrite can't map back to an object in the image.
- Nothing in CI reports this drift except the pinned image digest. The CI
  generators read the hand-maintained decode files, not the image, so they
  reproduce the committed proofs. The stock extractor stops on two of the
  three variants, because LLVM renumbers nine local symbol names.

## Method

1. Build the image the way CI does: `C3_GENESIS=dev`, `C3_EFUSE_BURN=off`,
   Rust 1.99.1, `cargo build --locked --release`, then
   `c3-ota bootloader-image`. Its SHA-256 matches the one in
   `c3-boot/bootloader/dev-image.sha256`
   (`7b2964d01ca71f7ad3a86037ace21d98d4aed1af6181fabccb3de7e680464fce`).
2. Build three perturbed images. The probe restored every Rust file after each
   build, and commits none of the changes.
3. Extract each image with the code in `scripts/extract-functions.py`, through
   a wrapper that finds a renamed `(.N)` symbol by its rank among symbols with
   the same base name, and compare every function and data item with the base
   extraction.
4. Check every `fetchRel … = some (…)` decode lemma against each variant with
   a Python RV32IMC decoder that agrees with the Lean decoder on the base
   image.
5. Build the base project (`lake build C3BootProofs`, 737 jobs, no errors).
   For the log variant, compile the new `Image` modules. Then compile each
   module that a static scan flagged, plus a random sample of 40 others,
   against the new `Image` modules and the base build of everything else.
   The scan flags a module that has a false decode lemma, a hex literal
   inside a code or data item that moved, or a fact about a data item whose
   bytes changed. Lean doesn't recheck an imported `.olean` file, so a
   failure in this isolation check belongs to the module itself.
6. Run a rebase prototype on the log variant, rerun the 11 CI generators, and
   build the whole tree with Lake.

The burn and prod variants got steps 1 to 4 and the static scan, not the Lean
builds.

## Build variants

| Variant | Change | Image bytes | `.text` bytes | Library shift | `.rodata` shift |
| --- | --- | --- | --- | --- | --- |
| base | Pinned CI build | 89,424 | 84,640 | 0 | 0 |
| burn | `C3_EFUSE_BURN=on` | 89,744 | 84,940 | +300 | +24 |
| log | One more `rom::log` call in `boot_main` | 89,456 | 84,658 | +18 | +16 |
| prod | A random 128-byte genesis file, `C3_EFUSE_BURN=on`, and a `lock()` that writes one register | 89,632 | 84,928 | +288 | -88 |

A non-development genesis file builds with no other change.

## Extraction diff

Each function is in exactly one class. *Address-only* means the same length,
and every differing instruction is part of an `auipc` and `jalr` call pair or
a `lui` and `addi` pair that loads a `.rodata` address.

| Variant | Unchanged | Address-only | Shape changed | Missing |
| --- | --- | --- | --- | --- |
| burn | 207 | 56 | 1 (`bootFn`, 322 to 564 bytes) | 0 |
| log | 209 | 54 | 1 (`bootMain`, 916 to 934 bytes) | 0 |
| prod | 206 | 56 | 2 (`bootFn`, 322 to 570 bytes; `bootMain`, 916 to 898 bytes) | 0 |

Of the address-only functions, 48, 50, and 49 change only data addresses, 4,
2, and 4 change only call targets, and 4, 2, and 3 change both.

- Call targets change only in functions that sit before the library in
  `.text`: `flashRead`, `romFlashReadWords`, `halt`, `beginUnwind`,
  `panicFmt`, `bootMainClosure0`, `bootMainClosure1`, and `bootMain`. A call
  from one library function to another keeps its relative immediate.
- Data addresses change in the library functions that load a `.rodata`
  constant, such as `sha256Compress`, `sha512Compress`, `pointAdd`, the P-384
  field operations, `sigstoreVerify`, `p384VerifyPrehash`, `ed25519Verify`,
  `edDecompress`, and `imageParse`.
- The extractor still finds all 55 data items at their fixed anchor offsets.
  Most move by the `.rodata` shift. Alignment padding moves `bsVersion`,
  `p384CurveA`, and `p384B` by a few bytes more, and `svRekorLeaf`, which
  precedes the padding, doesn't move. Strings, which the extraction doesn't
  name, move by other amounts. In the log variant, the strings after the new
  message move by its 19 bytes, and the strings before it stay put.
- Only `svConst` changes content. Nine of its 32-bit words, at offsets
  `0x80`, `0x88`, `0x90`, `0x98`, `0xD4`, `0xDC`, `0xE4`, `0xEC`, and `0xF4`,
  are pointers into `.rodata`.
- The burn and prod builds renumber nine LLVM local symbols, such as
  `<ctutils::choice::Choice>::select_i64 (.170)`, which becomes `(.172)`. The
  stock extractor looks these up by full name and exits with `no symbol`. The
  log build renames none.
- `bootMain` has no proofs, so its shape change costs nothing. `bootFn` has
  113 decode lemmas in `Boot.lean` and `BootSpec.lean` (1,591 lines), and
  burn and prod change its shape, so those two files need new proofs, not a
  rebase.

The proofs hold 30,629 `fetchRel` decode lemmas in 194 files. The checker
reproduces 26,241 of them on the base image; the rest are about the older V0
image or have a parameter. Of those 26,241:

| Variant | False | No longer decode | Modules with a false lemma |
| --- | --- | --- | --- |
| burn | 239 | 13 | 48 |
| log | 138 | 0 | 48 |
| prod | 254 | 12 | 48 |

`bootFn` accounts for 113 of the burn and prod failures, `sigstoreVerify` for
38 to 45, `p384VerifyPrehash` for 12, and other functions for 1 to 7 each.

## What breaks in Lean

The isolation check on the log variant compiled 241 modules, and 98 failed.
This table counts each failing module once, by the kind of its first error.
Many have errors of more than one kind.

| First error | Modules | Examples |
| --- | --- | --- |
| A `fetchRel` decode lemma is false | 46 | `Sha256LoopDecode`, `PointDecode`, `P384Add` |
| A code address literal is wrong | 20 | `FillLimbs` (`FL.toNat = 0x403ad524`), `EdNafTable` (`memcpyStubAddress + 8`) |
| A data address literal is wrong | 12 | `Pv384C0`, `P2Lib`, `SvLeafH` |
| A `blockEnd` fact is false | 11 | `Pv384A`, `Pv384HS`, `Sha256LoopFrame` |
| An `svConst` pointer word moved | 7 | `SvDp0` to `SvDp5`, `SvX2c` |
| A `List.drop` code chunk no longer matches | 2 | `SvAt`, `EdVerifyDecode` |

A `blockEnd` fact is a second form of decode fact: a straight-line block,
written as a literal list of instructions, checked against the code by
`decide`. The proofs hold 2,411 of them in 325 files.

The static scan flagged 201 modules. 104 of them compile in isolation,
because they hold a stale address in a definition or hypothesis, such as
`abbrev bAddr : Word := 0x3FCC4368` in `PointEnv.lean`, and the check against
the image happens in a module that imports them. One of the 40 unflagged
modules failed: `Sha256LoopFrame` writes an address as a page-aligned high
half plus a low half (`0x3FCC5000 + 0xFFFFFEBC`), which the scan didn't
count.

Lake builds a module only after all of its imports build, so 98 failures leave
621 of the 735 modules unbuilt. A false lemma in `Sha256LoopDecode` alone
blocks 599 modules, `P384Add` blocks 575, `CondNeg12` 536, and `FlashRead`
470. Static prediction for burn and prod gives the same picture as for log:
201 or 202 flagged modules and 622 unbuilt.

The CI generators don't notice a new image. They regenerate 11 proof files
from the decode files, and the decode files don't change when the image
does. After the decode files are updated, four generators stop with
`KeyError: ('imm', 1070351224)`, because each one hardcodes a `.rodata`
address, such as `BADDR = 0x3FCC4368` in `gen-p256-double.py`. In total, 12
generator scripts hold 99 literal `.rodata` addresses.

## Rebase prototype

The prototype is a Python script that carries the proofs to the log variant.
It isn't committed. In order, it does the following:

1. Copies the variant's `Image` files over the committed ones.
2. Rewrites each `fetchRel` lemma whose stated instruction matches the base
   decode and whose decode changed: 138 lemmas.
3. Re-slices the 23 changed code chunks in `SvAt.lean` from the new
   `sigstoreVerifyCode`.
4. Relocates every 8-digit hex literal that falls in the base image's code or
   `.rodata`. A literal inside a known item moves to the same offset in that
   item's new location (5,774); any other `.rodata` literal moves by the
   `.rodata` shift (291). It skips page-aligned values, which are `lui` high
   halves.
5. Relocates split addresses written as `0x3FCCx000 + LO`,
   `aluEval .add HI LO`, or `.lui r HI, .aluImm .add r r LO` (155 pairs).
6. Applies the same literal relocation to `scripts/gen-*.py`, then reruns the
   11 CI generators, which update the low halves in four generated proofs,
   such as `+ 0x368` to `+ 0x378` in `PointAdd.lean`.

It edits 216 files, 13 of them generator scripts. Each Lake build of the
rebased tree stops at a few modules and leaves their importers unbuilt:

| Tree | Failing modules | Unbuilt modules (of 735) |
| --- | --- | --- |
| Log image, no rebase | 98 | 621 |
| Steps 1 to 4, and the `0x3FCCx000 + LO` form of step 5 | 3 | 601 |
| All six steps | 3 | 476 |
| All six steps, and hand edits in 6 files | 2 | 308 |

In the last build, the hand-written proofs in `FeSquare.lean` and
`KcCompress.lean` and the generated `PointAdd.lean` check against the new
image. `SvSpec.lean` and `BootSpec.lean` stay behind the last two failures.

The forms the prototype doesn't handle, and that needed hand edits, are the
following:

- A `blockEnd` instruction list that holds only the low half of an address,
  because the `lui` is in an earlier block. `NonZero384.lean` has
  `.aluImm .add a1 a1 0xFFFFFC2C`.
- A pasted symbolic register state with the high and low halves several terms
  apart. `ImageCheckCur.lean` has `… a3 0x3FCC5000 a3) 0x240)`.
- A call distance across the bootloader crate and library boundary.
  `FlashRead.lean` has `P + 0x1309E`, and `ReadPart.lean` has
  `0x403A1748 + 0x1309E`, which is `memset`'s address written as two
  literals.
- A proof about the current image that reuses a lemma from the proof about
  the V0 image, because the literals happened to match. `ImageCheckCur.lean`
  uses `tbl_al_hi` and `tbl_al_lo` from `ImageCheck.lean`.
- A string address that the prototype moved by the common `.rodata` shift of
  16 bytes. Strings are packed with no alignment, so the strings after the
  inserted log message moved by its length, 19 bytes, and the strings before
  it didn't move. `Panic.lean` and `Boot.lean` needed the values from the new
  image's decode.

Two failures remain:

- `EdVerifyDecode.lean` copies `ed25519VerifyCode` into 516-byte windows
  (`(ed25519VerifyCode.drop K).take 0x204 = evcWn`) and decodes each lemma
  from a window (`FetchWin.lean`). The prototype re-slices only the
  `SvAt.lean` chunk layout.
- `SvCongr.lean` states the bottom of the `.rodata` window once in decimal
  (`1070350848`), and the prototype relocates only hex literals. The window
  start, `0x3FCC4200`, isn't the address of any item, so no rule says how far
  it moves.

## Recommendations

These are ranked by payoff for the work involved.

1. **Generate every image-derived fact, and check it in CI.** The decode
   lemmas, the `blockEnd` instruction lists, and the byte chunks in
   `SvAt.lean` and `EdVerifyDecode.lean` are facts about the image, but
   people maintain them by hand, and CI regenerates nothing from the image.
   `decode-lemmas.py` already writes decode lemmas from `llvm-objdump`
   output, and the chunks are slices of the extraction. Generate all of them
   from the extraction in CI and diff the output, the way CI treats the 11
   generated proofs. Move the lemmas into generated files, or between markers in the files that hold
   them now, and keep their `xx_at_OFF` names so no proof changes. Generate
   each `blockEnd` list the same way, from the function, start offset, and
   length. This removes the 46 decode failures, the 11 `blockEnd` failures,
   and the 2 chunk failures with no proof edits, and it reports drift
   directly instead of through the digest. The work is one generator and a
   move of about 30,000 lemmas and 2,400 lists, mostly mechanical.
2. **Name addresses instead of writing them.** The `Image` files already
   define 264 code and 60 data `fooAddress` names, and proofs use 45 of the
   data names, but `.rodata` addresses still appear as literals 6,271 times
   in 199 proof files, code addresses 108 times in 34 files, and `.rodata`
   addresses 99 times in 12 generator scripts. Add `hi20` and `lo12` helpers
   so a split pair reads `hi20 regionEndsAddress` and `lo12
   regionEndsAddress`, and state call distances as differences of names.
   Name the strings that proofs load, and the `.rodata` window bounds, too.
   The prototype showed that no single shift moves them correctly. Its
   relocation map already finds the item and offset for 5,774 of the
   literals, so most of the rewrite is mechanical. The risk is `decide` and
   `rfl` performance when a name has to unfold, which needs measuring on the
   heaviest modules (`SvZE.lean` has 809 literals). This removes the 32
   literal failures, the generator crashes, the `SvCongr.lean` failure, and
   every hand edit in the prototype section except the V0 lemma reuse.
3. **Make the extractor resolve symbols without LLVM's `(.N)` suffixes.** Find
   a local symbol by its rank among symbols with the same base name, or by the
   call site in a named caller, and check each data anchor by searching for
   the expected bytes. This is a change to one script. Without it, the burn
   and prod images can't be extracted at all.
4. **Place the bootloader crate's code after the library.** The linker script
   already puts `.text_setup` last "so that changing the clock and watchdog
   setup moves no other function." Putting the bootloader crate's own
   functions, and the strings that `rom::log` prints, in sections that come
   after the library's would keep every library function and constant at the
   same address when `boot_main` or `bootFn` changes. The build uses
   `lto = true` and `codegen-units = 1`, so ordering by object file doesn't
   work; `#[link_section]` on the crate's functions and log strings does, the
   way `.text_setup` does now. For a change confined to the bootloader crate,
   this keeps the 50-odd address-only library functions unchanged. It doesn't
   help a change to library code or to a library constant. Do it after the
   first three, because it's a rebuild that needs the same rebase.
5. **Split decode lemmas out of widely imported files.** One false lemma in
   `Sha256LoopDecode.lean` stops 599 modules from building, so each rebase
   iteration shows only the first few errors. Splitting decode lemmas from the
   environment definitions they share a file with lets a failing build report
   every broken module at once. After the first recommendation, this matters
   less.
6. **Parameterize proofs over the data base address.** Proofs already take the
   code base `P` and assume `CodeAt` for the callee code. Taking a data base
   the same way, with `CodeIn M D fooData` as a hypothesis, would make the
   data literals vanish from proofs. It touches every proof that loads a
   constant and every caller that discharges the hypothesis, so it's the
   largest change, and the second recommendation gets most of its benefit.

For the planned trust-anchoring change, the first three recommendations turn
the library's address shifts into a regenerate step, and leave the real proof
work in the functions whose code changes: `bootFn` and whatever new
verification code the change adds.
