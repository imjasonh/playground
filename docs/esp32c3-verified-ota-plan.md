# Plan: verify an ESP32-C3 Sigstore bootloader at the machine-code level

> **Status:** phase 1 is done and phase 2 mostly done in
> [`c3-boot/`](../c3-boot/). The verifier, the bootloader, the release and
> trust-root workflows, and QEMU scenarios with power cuts exist, and a
> production Sigstore bundle signed in GitHub Actions boots in QEMU. Phase 3
> has started in [`c3-boot-proofs/`](../c3-boot-proofs/) with the decision
> logic's, the trust-root rules', and the byte formats' specifications;
> `rollback`, `boots_safe`, `availability`, and `trust_root_monotone` at
> that level; and `mapped_pages_signed` for the image header. Phase 4 has
> an executable RV32IMC model tested in lockstep against QEMU, on random
> sequences and on whole boots of the bootloader image. Phase 5's pilot
> proves the image's compiled `crc32` and the slot-manifest parser on the
> model: `manifestParse_decodes` shows that the compiled `manifest::parse`,
> with the reader functions and `part` under it, returns what the Lean
> decoder `decodeManifest` returns for the 40 bytes its only caller passes.
> `imageParse_decodes` does the same for the image header: the compiled
> `image::parse` returns what `decodeImageHeader` returns, so
> `mapped_pages_signed` holds for its result (`imgW_pages_signed`). Both proofs
> assume a stack and memory layout that the proofs of their callers, not yet
> written, have to establish. The P-256 field multiplication is proved as
> compiled: `fieldMul_correct` shows that `FieldElement::multiply`, through
> `widening_mul_fixed::<8, 8>`, its Montgomery reduction, and `sub_inner`,
> returns the Montgomery product. The point addition is proved as compiled
> too: `pointAdd_correct` shows that `primeorder`'s complete addition, through
> its 46 calls to the field operations and `memcpy`, stores `ptAddSpec` of
> its operands, the Renes, Costello, and Batina formula in the order of the
> Rust source. That this formula is the curve's group law is not yet proved.
> [The throughput report](../c3-boot-proofs/docs/throughput.md) measures 12.5
> proof lines per instruction and projects the whole image at about a tenth
> of the libsignal proof.
> [`c3-boot/README.md`](../c3-boot/README.md) lists what isn't
> done, including the eFuse lock, a release blocker. The facts about
> Sigstore, the ESP32-C3, Sail, and the AlphaProof Code repository were
> checked on 2026-11-10 against the sources listed at the end.

This plan proves security properties of a Rust bootloader for the ESP32-C3,
in Lean, against the RISC-V machine code that ships on the device. It follows
the method that DeepMind used to verify libsignal in "AlphaProof Code:
Verifying Signal's Security at the Machine-Code Level." The bootloader checks
over-the-air (OTA) firmware updates that GitHub Actions signs with Sigstore.
The OTA and signing design is in the appendix. The body of this plan is
about the verification.

## Summary

The proof covers the exact bytes that ROM Secure Boot loads. Neither the
Rust compiler nor Rust's semantics is trusted. The main results are five
theorems:

- **Refinement.** Every run of the bootloader binary, on any flash contents,
  does what a short Lean acceptance function says. No run faults, panics, or
  runs longer than a proved instruction bound.
- **Authenticity.** The bootloader runs an image only if the release
  workflow signed it. This holds even if an attacker steals a signing key
  after its certificate expires. The bound is a sum of signature-forgery and
  hash-collision advantages.
- **Transparency.** The bootloader runs an image only if a checkpoint signed
  by a trusted Rekor log commits to that image's log entry.
- **Trust-root rotation.** The bootloader uses a trust root only if a chain
  of key sets, starting from the four keys compiled into it, authorizes it,
  with two signatures from the previous set at every step, and only if the
  trust root's level is at least the security level in eFuse. Rotating to a
  new key set and raising the level shuts out a stolen key.
- **Rollback and availability.** The security level in eFuse never
  decreases, and the bootloader never runs an image whose security version
  is below it. If the application follows the update protocol, no sequence
  of power losses makes both slots unbootable while one confirmed image
  exists. A malicious application can erase flash, which a USB reflash
  repairs, but it can't burn eFuse, because the bootloader locks the eFuse
  controller before it jumps.

This work differs from the libsignal work in five ways:

- It targets bare-metal RISC-V, not AArch64 Linux user mode. Peripherals,
  eFuse, and NOR flash take the place of system calls.
- Its theorems span many boots with power loss at any instruction, not one
  run of a command-line tool.
- The binary that gets verified is the binary that ships. The
  cryptographic routines stay in the image as real code. The rest of the
  proof treats calls to them through contracts, and phase 7 proves that the
  real code meets those contracts.
- The cryptography is proved, not assumed. libsignal's proof hooked every
  primitive. Here, SHA-2, ECDSA P-256 and P-384 verification, and Ed25519
  verification are proved against Lean specifications at the machine-code
  level. Every digest on the verification path uses software SHA-2, so the
  SHA accelerator isn't trusted. The only hooks left are the ROM's flash
  read, erase, and write functions.
- The security property is short. Most of the specification is parsing:
  X.509, CMS, and Rekor's formats.
- The verified code is much smaller. This plan estimates 5,000 to 20,000
  RV32 instructions for the checks and the hardware code, plus 10,000 to
  40,000 for the cryptography, compared with about 140,000 AArch64
  instructions for libsignal.

The plan is feasible. The largest risks are building the agent setup, which
DeepMind didn't release, and getting the new trusted models of the platform
right. The [feasibility assessment](#feasibility-assessment) covers both.
[Phases and deliverables](#phases-and-deliverables) lists what each phase
produces, starting with the verifier code, and the exit criteria that decide
whether the next phase starts.

## Background on AlphaProof Code

The paper and the
[`google-deepmind/code-verification`](https://github.com/google-deepmind/code-verification)
repository describe the following:

- **Target.** Unmodified libsignal, compiled by stock `rustc` into a static
  AArch64 Linux binary. The theorems are about whole runs of that binary under
  a Lean model of AArch64 and Linux with 467 instructions and 31 system calls.
- **Trust.** The reader trusts the Lean kernel, about 18,000 lines of
  specification, about 8,000 lines of ISA and loader semantics, and 39 hooked
  routines, including every low-level cryptographic primitive. The compiled
  binary had stubs in place of hooked routines.
- **Scale.** About 6.5 million lines of Lean proof, of which 5.3 million are
  about the binary. Five people worked for four weeks. Campaigns ran 40 to 80
  prover agents on one machine for 24 to 72 hours. A clean build took hours
  and 15 to 34 GiB of memory.
- **Checking.** A gatekeeper accepts a proof only if Lean's comparator tool
  shows that it proves exactly a held-out copy of the approved
  specification, using only Lean's standard axioms. `sorry` and
  `native_decide` are rejected.
- **Specification quality.** Agents proved non-vacuity witnesses for every
  hypothesis, and proved that binaries with reintroduced bugs violate the
  theorems.
- **Lesson.** Proofs became cheap. Most of the human effort went into the
  specification.

The repository's trusted AArch64 layer, `arm64-semantics/Arm64/Trusted/`, is
about 16,700 lines. Its untrusted proof library, `ProofLib/`, is about
185,000 lines and is written for 64-bit AArch64 throughout. The repository
doesn't include the agent skills, the orchestrator, or the gatekeeper.

## Theorems

The following Lean is a sketch of the shape of each statement, not final
syntax. `bootImage` is the bootloader image, which the specification pins by
its SHA-256 digest.

### Refinement of one boot

```lean
theorem boot_refines (p : Platform) (hp : p.WellFormed) :
    BootRunsTo bootImage p fun out =>
      out.steps ≤ maxSteps ∧
      match accept p.flash p.efuse p.bootState with
      | .boot slot entry mapping burns =>
          out.result = .jumped slot entry mapping ∧
          out.efuse = p.efuse.burn burns ∧
          out.efuseLocked ∧
          out.bootState = nextBootState p.bootState slot
      | .halt =>
          out.result = .halted ∧ out.efuse = p.efuse
```

`Platform` is the state that the ROM leaves when it starts the bootloader:
flash contents, eFuse values, the boot-state record, and the CPU and
peripheral registers. `accept` is the acceptance function, written in Lean
and trusted. It includes the trust-root checks. For each slot it tries, it
checks the key-set chain and the trust root stored in that slot, checks the
image against them, and checks the security version. It returns the eFuse
bits to burn, which raise the security level only after the application
confirmed the image that justifies it. `BootRunsTo` says that every run
ends in an outcome that satisfies the postcondition and that no run faults. `out.result = .jumped` means the
program counter reached `entry` of `slot` with the flash mapping set to
`mapping` and interrupts disabled. `out.efuseLocked` means the eFuse controller's
registers are locked against writes until the next reset.

### Many boots with power loss

```lean
theorem boots_safe (tr : Trace) (htr : tr.Admissible) :
    ∀ b ∈ tr.boots, ∀ s e m, b.result = .jumped s e m →
      AcceptedSlot (tr.flashAt b) (tr.efuseAt b) s e m ∧
      levelOf (tr.efuseAfter b) ≥ burnTarget (tr.flashAt b) (tr.efuseAt b) s

theorem rollback (tr : Trace) (htr : tr.Admissible) :
    ∀ b₁ b₂ ∈ tr.boots, b₁ ≤ b₂ → ∀ s e m, b₂.result = .jumped s e m →
      slotLevel (tr.flashAt b₂) s ≥ levelOf (tr.efuseAfter b₁)

theorem availability (tr : Trace) (htr : tr.Admissible)
    (hp : tr.AppFollowsProtocol) :
    ∀ b ∈ tr.boots, tr.hasConfirmedAcceptedSlot b →
      b.completes → ∃ s e m, b.result = .jumped s e m
```

A `Trace` interleaves bootloader runs, application writes to flash, and
power losses. A bootloader run can stop at any instruction. A power loss
during a flash erase or write leaves the affected bytes undefined, and a
power loss during an eFuse burn leaves any subset of the requested bits set.

- `AcceptedSlot` is the single definition of every check on a slot, from
  [Image format and boot procedure](#image-format-and-boot-procedure) and the
  appendix sections it links to. `trust_root_monotone` and the security games
  use the same definition.
- `burnTarget` is the slot's level if the boot-state record marks that slot
  confirmed, and the current level otherwise. The second clause of
  `boots_safe` says the bootloader never jumps before the eFuse level reaches
  that target.
- `rollback` says that once a boot ends with the level at some value, no
  later boot runs a slot whose level is below it.
- `availability` restricts the application to the update protocol, because
  an application that erases both slots makes any device unbootable. It says
  that a boot that runs to completion jumps to some slot whenever one
  confirmed, accepted slot exists. The other theorems allow arbitrary
  application writes.

### Trust-root monotonicity

The process that produces new trust roots is in
[Trust-root rotation](#trust-root-rotation).

```lean
theorem trust_root_monotone (tr : Trace) (htr : tr.Admissible) :
    tr.efuseMonotone ∧
    ∀ b ∈ tr.boots, ∀ s e m, b.result = .jumped s e m →
      let (c, r, img) := slotContents (tr.flashAt b) s
      ChainAuthorized genesisKeys c ∧
      ThresholdSigned 2 r c.lastKeySet ∧
      c.lastLevel ≤ r.level ∧
      img.securityVersion = r.level ∧
      r.level ≥ levelOf (tr.efuseAt b)
```

These conjuncts are consequences of `AcceptedSlot`, stated separately so that
a reviewer can read the trust-root rules without reading the whole
acceptance definition.

`efuseMonotone` says that no eFuse bit changes from 1 to 0 on any trace, so
the security level never decreases. `ChainAuthorized genesisKeys c` says
that each link in the key-set chain `c` has a strictly higher level than the
one before it, and carries signatures from at least two distinct keys of the
previous link's key set, where the first link's predecessor is the
compiled-in genesis set. `ThresholdSigned 2 r ks` says that at least two
distinct keys in `ks` signed the trust root `r`. The bootloader verifies
every image with the chain and trust root stored in the same slot, so this
theorem and `boots_safe` together say that every image the device runs
passed checks against an authorized trust root at or above the current
security level.

### Authenticity and transparency

These are computational theorems, stated as games in VCVio. The adversary
can do the following:

- Get Fulcio certificates for any identity except the release workflow.
- Ask the release workflow to sign images of its choice. This is stronger
  than reality, where the workflow signs only honest builds.
- Submit any entry to Rekor, and get a TSA timestamp on any bytes.
- Steal any signing key after its certificate expires.
- Steal at most one key from each key set while that set is current.
  Retired key sets are destroyed when the holders rotate away from them, so
  the adversary can't steal them later.
- Steal any Sigstore key (a Fulcio intermediate, a log key, or a TSA key)
  that appears only in trust roots whose level is below the device's
  security level.
- Ask the trust-root key holders to sign trust roots and chain links. Honest
  holders sign only trust roots that list honest Sigstore keys, and only
  links that name honest key sets.
- Choose all flash contents and every application action between boots.

The adversary wins the authenticity game if a device boots an image that the
release workflow never signed:

```text
Adv_auth(A) ≤ m · Adv_EUF-CMA[Ed25519](trust-root keys)
            + k_F · Adv_EUF-CMA[ECDSA P-384](Fulcio intermediates)
            + q · Adv_EUF-CMA[ECDSA P-256](leaf keys)
            + k_T · Adv_EUF-CMA[ECDSA P-384](TSA keys)
            + Adv_CR[SHA-256] + Adv_CR[SHA-384]
```

In this bound, `m` is the number of trust-root keys across every key set
the holders ever create. The theorem takes `m` as a parameter. At most 17
sets can appear in one chain, but the holders might create sets that never
reach a chain, so the rotation process records every key set created. `q` is the number of releases.
`k_F` and `k_T` are the numbers of Fulcio intermediates and TSA keys listed
in honest trust roots at or above the device's security level. Each factor
comes from a union bound over the keys of one kind, and the security games
in phase 3 derive each one in Lean. The TSA term matters because of key theft after
expiry. Without a trusted signed time inside the certificate's validity
window, a stolen ephemeral key could sign forever.

The adversary wins the transparency game if a device boots an image whose
entry isn't in a log that a trusted checkpoint commits to. That advantage is
at most the trust-root term, plus the Ed25519 forgery advantage against each
log key listed in honest trust roots at or above the device's security
level, plus the SHA-256 collision advantage.

The game makes rotation a theorem. A Sigstore key that the adversary steals
after a device raises its security level past every trust root that lists
the key doesn't appear in the bound. A stolen trust-root key helps only if
the adversary also steals a second key from the same set before the holders
rotate away from it.

Every computational theorem connects to the binary through `boot_refines`.
The games run `accept`, and the refinement theorem says the binary does what
`accept` does.

One assumption sits outside every proof. Fulcio issues a certificate naming
an identity only to a caller that holds a valid OIDC token for that
identity, and GitHub issues that token only to the named workflow.

## Trusted computing base

A reader who wants to believe the theorems must read and accept everything
in this table. Everything else is checked by Lean.

| Component | Estimated size | How it gets validated |
| --- | --- | --- |
| RV32IMC + Zicsr semantics in machine mode | 2,000 to 4,000 lines | Proved equivalent to the Sail-generated Lean model on every instruction the binary uses. Lockstep tests against QEMU and hardware |
| Platform model: memory map, initial state, flash, eFuse, MMU table, watchdog | 1,000 to 3,000 lines | Lockstep tests against Espressif's QEMU fork and hardware |
| Hook contracts: the ROM's flash read, erase, and write functions | 100 to 300 lines | QEMU, then hardware runs |
| Cryptography specifications: SHA-256, SHA-384, and SHA-512 (FIPS 180-4), ECDSA P-256 and P-384 verification (FIPS 186-5), and Ed25519 verification (RFC 8032) | 1,000 to 2,500 lines | Executable Lean definitions run against the Wycheproof and NIST test vectors, and against the Rust code |
| Formats: image header, key-set chain, trust-root blob, device bundle container, boot-state record | 500 to 1,000 lines | Differential tests against the host encoder |
| X.509 and CMS subsets, Rekor v2 entry and checkpoint, RFC 6962 hashing | 2,000 to 5,000 lines | Executable Lean decoders tested against sigstore-go and OpenSSL on a corpus of real bundles |
| Identity policy, acceptance function, boot state machine | 1,000 to 2,000 lines | Human review, non-vacuity proofs, mutation proofs |
| Security games and assumptions | 1,000 to 2,000 lines | Human review against the literature |
| Image extraction tool and build scripts | Tool code | The proof checks extracted bytes against the image digest. Only symbol names are trusted |
| Lean kernel and comparator | Not ours | Standard |

These are estimates. The total is 9,000 to 19,000 lines, compared with about
26,000 trusted lines for libsignal. The contracts that the rest of the proof
uses for the cryptographic routines aren't in this table, because phase 7
proves them.

Lean checks the rest. The Rust compiler and linker, the Rust source, the
separation logic, the weakest-precondition calculus, symbolic execution,
every proof, and every agent are outside the trusted base.

## Machine model

### ISA semantics

Sail has a Lean backend, and `opencompl/sail-riscv-lean` publishes a Lean
model generated from the official Sail RISC-V specification. That model is
large and covers RV64, RV32, and many extensions. Symbolic execution through
generated code is slow, so it isn't a good base for millions of lines of
proof.

The plan uses two models:

1. A compact, hand-written RV32IMC + Zicsr semantics for machine mode. It is
   trusted, and every proof runs against it.
2. A Lean theorem, written by agents and checked by the kernel, that the
   compact semantics agrees with the Sail-generated model on every
   instruction that appears in the bootloader image.

The libsignal work tested its ISA against the Sail and Unicorn oracles. This
plan proves agreement with the Sail-generated model, which leaves only the
Sail model and the generator as trusted. Lockstep testing against QEMU and
hardware remains as a second check.

The CPU state has the 32 general registers, the program counter, and the
machine-mode CSRs that the bootloader reads or writes. Memory is a byte map
with per-region permissions. A fetch from a non-executable region, a write to
the bootloader's own code, and an access outside the memory map are faults.
A proof that a run ends normally rules them out. Interrupts are disabled in
the initial state, and the proof shows that the bootloader never enables
them. The model therefore doesn't need interrupts or traps beyond treating a
trap as a fault.

### Platform model

- **Initial state.** The segments that the ROM loaded into SRAM, the stack
  pointer, the cache and MMU configuration, and the registers that the ROM
  leaves set. The values come from Espressif's ROM documentation and are
  checked by dumping state on hardware with a debug probe.
- **Flash.** A byte array with NOR rules. An erase sets every bit in a sector
  to 1, and a write can only clear bits. A power loss during an erase or a
  write leaves the bytes in the affected range undefined. The adversary
  chooses their values. Flash doesn't change while the bootloader runs,
  which is an explicit assumption. It excludes a physical attacker during
  boot, and any DMA or peripheral write to flash, which the bootloader never
  starts.
- **Flash access.** The bootloader reads flash, and erases and writes the
  boot-state sectors, through ROM functions. Each is a hook. The read
  contract copies bytes from the flash model into a RAM buffer. The erase
  and write contracts change only the named sector and follow the NOR rules,
  including power loss partway through. This keeps the SPI controller and the
  cache out of the model.
- **eFuse.** An array of bits that can only change from 0 to 1. Reads and
  program operations go through the eFuse controller's registers, modeled at
  the register level. Because bits only get set, every counter is unary, and
  its value is the number of set bits. Every eFuse block except block 0 uses
  Reed-Solomon coding and can be programmed only once, so the only counter
  the bootloader can raise one bit at a time is the 16-bit `SECURE_VERSION`
  field in block 0. ESP-IDF reads that field as a count of set bits too. The
  plan calls its value the security level.
- **Register locks.** The memory-protection hardware that the bootloader uses
  to lock the eFuse controller's registers before it jumps. The model says
  that after the lock, a write to those registers has no effect until the
  next reset.
- **MMU table.** The memory-mapped table that maps flash pages to the
  application's virtual addresses. The postcondition of a boot states the
  mapping that the bootloader wrote.
- **Watchdog.** The model counts instructions. `maxSteps` in the refinement
  theorem bounds them. Measured cycles per instruction on hardware turn that
  bound into a time to compare with the watchdog timeout.

### Hooks without stubs

The libsignal binary had stubs in place of its hooked routines, so the
verified binary wasn't the binary that would ship. This plan keeps the real
cryptographic code in the image. The semantics treats a call to a hooked
routine's entry address as a single step that applies the routine's
contract. Each contract has a frame condition. The routine writes only its
output buffers and the stack below the stack pointer, and it restores the
callee-saved registers.

The AlphaProof Code semantics already has `HookOk`, `HookSat`, and
`subroutineHook`, which turn a proof about a subroutine into a proof that the
subroutine meets a hook contract. Phase 7 uses the same mechanism to prove
that the real SHA-2, P-256, P-384, and Ed25519 code meets its contracts.
After that, the only hooks left are the ROM's flash functions. The SHA
accelerator is silicon and can't be verified, so no digest on the
verification path uses it. Every digest that a security decision depends on
comes from the software SHA-2 code that phase 7 proves.

## Getting the binary into Lean

`rust-obj2lean` reads relocatable AArch64 objects and quantifies over every
valid linker placement. The bootloader is a fixed-address image that the ROM
loads, so this plan verifies the final linked image instead:

1. Build the bootloader with a pinned toolchain into an ESP-IDF image.
2. A new tool, `rv32-img2lean`, reads the image, emits each segment's bytes
   and load address as Lean data, and uses the ELF symbol table and DWARF to
   name functions and suggest loop invariants and stack frames. The names and
   hints are untrusted, except that the specification refers to hooked
   routines and entry points by symbol name.
3. A Lean theorem checks that the emitted segments hash to the pinned image
   digest. The image that ROM Secure Boot verifies is therefore the image the
   proofs cover.

Fixed addresses also remove RISC-V linker relaxation from the problem. The
linker can rewrite instruction sequences, but the proof is about the output.

### Proof decomposition

Agents prove a contract for each function at the machine level, then compose
the contracts into the whole-boot theorem. The plan expects these contract
groups:

| Group | What the contracts say |
| --- | --- |
| Byte and buffer helpers | `memcpy`, `memset`, and comparison loops, with exact frame conditions |
| Container and header parsers | Each returns the Lean decoder's value or a rejection, reads only inside its buffer, and terminates |
| DER and X.509 subset | The parser agrees with the Lean decoder for the pinned profile and rejects everything else |
| CMS and RFC 3161 subset | Same, for the timestamp token |
| Rekor v2 | The rebuilt entry equals the canonical JSON that the Lean function produces. Merkle verification equals the Lean definition |
| Policy and acceptance | The composition equals `accept` |
| Boot-state record | Reading picks the valid copy with the higher generation, as [Boot-state record](#boot-state-record) defines. Writing preserves at least one valid copy at every instruction |
| Cryptography | Each routine returns the Lean specification's result. See [Proving the cryptography](#proving-the-cryptography) |
| Trust root | The chain and blob parsers agree with the Lean decoders. Each signature count includes only distinct keys of the right key set. Level comparisons use the eFuse value |
| Message extraction | Each signature check receives exactly the bytes that the [message table](#signed-messages) names, and the hash algorithm the table names |
| eFuse, lock, and MMU | Register writes produce the specified burns, the lock, and the mapping, in that order, before the jump |
| Entry and exit | From reset to the jump, the stack stays in its region and the code is never written |

## Writing the Rust for verification

The proofs are about optimized machine code, so the source must keep that
code regular, and the code must be split so that each part has one kind of
proof.

### Crate split

| Crate | Contents | How it is proved |
| --- | --- | --- |
| `verify` | Every check: container, header, trust root, X.509 subset, CMS subset, Rekor v2, identity policy, and `accept`. Pure functions over byte slices, with no hardware access | Machine-level contracts that equal the Lean specification |
| `crypto` | ECDSA P-256 and P-384 verification, Ed25519 verification, and SHA-2, each behind one function that takes byte slices and returns a result | Machine-level contracts that equal the Lean cryptography specifications, proved in phase 7. Until then, the rest of the proof uses the contracts as hooks |
| `bootloader` | Reset entry, ROM flash access, eFuse reads and burns, the register lock, MMU mapping, the boot-state record, and the jump | Machine-level contracts against the platform model |

The same `verify` source builds for the host and for RV32. The host build is
what CI and the key holders run, so CI and the device run the same checks.

`verify` mirrors the Lean specification. Each Lean definition in the
acceptance path has one Rust function with the same name and the same
argument order, and the specification lists the pairs. This makes the proof
decomposition follow the code, and makes a mismatch between the two easy to
find in review.

### Rules

These are requirements for all three crates, enforced by lints and CI where
a lint exists:

- `verify` has `#![forbid(unsafe_code)]`. Only `bootloader` touches
  registers.
- `#![no_std]`, no heap, no `dyn` traits, no function pointers in the
  verified paths, and no floating point.
- Fixed-size buffers with sizes known at compile time, and loops with
  explicit bounds.
- `panic = "abort"`, with one panic handler that halts. The refinement
  theorem allows a halt, and the agents prove that each panic site that
  remains is unreachable or leads to a specified halt.
- `#[inline(never)]` on every function whose contract the specification
  names, and on every cryptographic routine. CI checks that each of these
  names appears as a symbol in the linked image, so a contract can't silently
  apply to inlined code.
- A pinned `rustc`, a fixed `opt-level`, `codegen-units = 1`, and a
  reproducible build. The build script checks the image digest.

A rebuild changes the binary, and a changed binary needs proof repair. The
libsignal team saw large repairs early on. For a bootloader, that is
acceptable. The verified bootloader is built once, proved, signed with the
Secure Boot key, and rarely changed again. After the code freeze in phase 5,
CI fails any change to the bootloader whose image digest differs from the
digest the specification pins, unless the same change updates the proofs.

## Validating the specification

A proof of the wrong specification is worthless, and the specification is
where most of the effort goes. Every trusted definition gets at least two of
the following checks.

- **Executable reference decoders.** Write every format definition as an
  executable Lean function. Run the compiled Lean decoders against a corpus
  of real Sigstore bundles signed by GitHub Actions, sampled from the public
  Rekor log, and against mutations of those bundles. Compare each verdict
  with sigstore-go and with OpenSSL's X.509 and CMS parsers. Every
  disagreement either fixes the specification or becomes a documented
  profile restriction.
- **Whole-binary lockstep.** Run the bootloader image in the Lean semantics,
  in Espressif's QEMU fork, and on hardware, on the same corpus. Compare the
  final state of every run. The libsignal team did this for 15.6 million
  instructions across 10 runs.
- **End-to-end vectors.** For each bundle in the corpus, record the exact
  bytes and hash algorithm that sigstore-go passes to each signature check,
  and compare them with what the Lean `accept` and the `verify` crate pass.
  Test vectors for the cryptography alone show that the cryptography
  specifications are standard. These show that the parsers feed them the
  right messages.
- **Non-vacuity.** Prove that the hypotheses of each theorem are jointly
  satisfiable and that a real signed release satisfies `accept`.
- **Mutation proofs.** For each bug in the following list, build a mutated
  bootloader and prove that the theorems fail for it:
  - Segments loaded before verification, as in CVE-2018-18558
  - The signature check skipped
  - The image digest computed over fewer bytes than the bootloader maps
  - The identity policy matched by prefix
  - The Build Signer URI read from the wrong extension
  - The signed time not compared with the leaf certificate's validity window
  - The signed time compared with only one of the validity windows that
    [Time checks](#time-checks) requires
  - A trust root accepted with one signature, or with the same key counted
    twice
  - A chain link signed by keys from its own key set instead of the previous
    link's set
  - A chain link whose level isn't higher than the previous link's level
  - The security level read from flash instead of eFuse
  - A trust root or chain from one slot used to verify the image in the
    other slot
  - The security level raised before the application confirmed the image
  - The security level raised above the slot's level
  - A slot accepted whose image security version differs from its blob's
    level
  - A jump after a partial eFuse burn, before the level reaches the target
  - The eFuse controller left unlocked at the jump
  - A counter compared as a binary number instead of a count of set bits
  - The security version not checked
  - The security version checked as greater than the level instead of
    greater than or equal, or with an off-by-one in the other direction
  - The security version not checked on the fallback slot after the first
    slot fails
  - The image signature checked against a SHA-384 digest instead of SHA-256
  - The canonical JSON entry built with its fields in the wrong order
  - An inclusion proof accepted for a tree size other than the checkpoint's
  - An ECDSA check that accepts `r` or `s` equal to zero or at least the
    group order
  - An Ed25519 check that accepts `S` at or above the group order
  - A field reduction that skips its final conditional subtraction
  - A boot-state write that erases both copies before rewriting either
- **Review.** Reviewer agents from a different model family than the
  specification writer check each draft for faithfulness to the RFCs and to
  sigstore-go, and for strength. A human approves the specification before
  proof work starts.

## Security proofs

The computational theorems use VCVio, as the libsignal work did. Reductions
are written in a small costed language, and the proofs bound their cost
explicitly. The reductions here are short. Each one embeds a forgery or a
collision into one place in the game. This plan has no symbolic model,
because a single signed message has no protocol interaction for a Dolev-Yao
analysis to explore.

The games use `accept`, and `boot_refines` transfers their conclusions to
the binary. The proof doesn't need a model of Rust or of the compiler.

Each forgery assumption is about the signature scheme that the Lean
cryptography specification defines. Phase 7 proves that the machine code
computes exactly that specification, and the test vectors check that the
specification is the standard scheme.

## Proving the cryptography

The libsignal proofs assumed every cryptographic primitive. This plan proves
them, because a parser proof means little if the signature check it feeds
can be wrong.

### What gets proved

For each routine, a machine-level contract says that, for every input within
the format's length limits, the routine returns exactly what the Lean
specification returns, writes only its output buffer and the stack below the
stack pointer, restores the callee-saved registers, and finishes within a
proved instruction bound. The routines are:

- SHA-256, SHA-384, and SHA-512, in software
- ECDSA P-256 verification with SHA-256, for image signatures
- ECDSA P-384 verification with SHA-384, for the Fulcio leaf certificate,
  and with SHA-256, for the TSA token
- Ed25519 verification, for chain links, trust-root blobs, and Rekor
  checkpoints

The [message table](#signed-messages) lists the exact bytes each check
covers. The contracts take those bytes as typed arguments, so a proof about
the parser and a proof about the routine meet at one definition.

### Specifications

- **SHA-2.** FIPS 180-4, written over `BitVec 32` and `BitVec 64`.
- **ECDSA.** FIPS 186-5 verification, written step for step as the
  standard gives it, as computations in `ZMod p` and `ZMod n`. It rejects
  `r` or `s` outside `1` through `n - 1`, derives `e` from the leftmost bits
  of the digest, computes `u1 G + u2 Q` with the affine group law, rejects
  the point at infinity, and compares `r` with the x-coordinate reduced
  modulo `n`. Public keys must be uncompressed SEC1 points on the curve.
  Mathlib's Weierstrass-curve results are used only in lemmas, not in the
  trusted definition.
- **Ed25519.** RFC 8032 verification over the twisted Edwards form of
  Curve25519, with the addition law written in affine coordinates and these
  rules fixed now, matching `verify_strict` in `ed25519-dalek`:
  - Reject `S` at or above the group order `L`.
  - Reject a non-canonical encoding of `A` or `R`, meaning a y-coordinate at
    or above `p`, or x equal to 0 with the sign bit set.
  - Reject `A` or `R` of small order.
  - Compute `k` as SHA-512 of `R`, `A`, and the message, reduced modulo
    `L`, and accept only if `[S]B - [k]A` equals `R` as a point, without
    multiplying by the cofactor.

  An honest RFC 8032 signer, including Go's `crypto/ed25519`, which signs
  Rekor checkpoints, always produces signatures that pass these rules.

Validate each specification by running its executable Lean form against the
Wycheproof vectors for ECDSA P-256 and P-384 and for Ed25519, including
every vector that must be rejected, and against the NIST SHA vectors. Run
the same vectors against the Rust code on the host and in the lockstep
harness. Also run the Ed25519 specification on real Rekor v2 checkpoints and
on signed trust-root blobs, so that the strict rules are checked against the
signatures the device actually sees.

### Implementation choices that keep the proofs tractable

Verification uses only public data, so the code doesn't need to run in
constant time. That allows simpler code than signing would. Phase 0 compares
two designs on code size, cycles, and how much generic code compiles in:

- Audited crates: RustCrypto `p256` and `p384`, and `ed25519-dalek` or
  `ed25519-compact`.
- A minimal implementation for this project: field arithmetic generated by
  fiat-crypto for 32-bit targets, complete addition formulas (Renes,
  Costello, and Batina for the Weierstrass curves, and extended coordinates
  for Edwards), and scalar multiplication loops with fixed bounds.

Fiat-crypto's field code is straight-line, with no branches or loops, which
suits symbolic execution. Its Coq correctness proofs are about the source,
so this project doesn't rely on them, but they show the code's structure is
correct. Complete formulas have no special cases, so the point proofs are
algebraic identities in `ZMod p` with no case splits. A new implementation
is acceptable here only because the proof covers it.

### Proof layers

1. **Words.** RV32 has no carry flag, so multi-word additions compile to
   `sltu` sequences, and every 64-bit SHA-512 operation is a pair of 32-bit
   operations. Lemmas show that these sequences compute the wider value.
2. **Field.** Each field operation's machine code computes the right value
   modulo `p`, with the limb bounds that the next operation needs.
3. **Points.** Each point formula equals the specification's group law,
   proved with ring identities in `ZMod p`.
4. **Scalar multiplication.** Loop invariants over the scalar's bits.
5. **Verification.** The routine's result equals the specification's
   verdict.

s2n-bignum (HOL Light proofs of P-256, P-384, and Curve25519 machine code on
x86 and Arm), fiat-crypto, and HACL* show that each layer can be done. None
of them targets RV32 or Lean, so no proofs carry over.

## Running the proof campaigns

### Agent setup

The AlphaProof Code agent setup isn't public, so this project builds its
own with the same roles:

- A specification writer working with a human, and reviewers from a
  different model family.
- An orchestrator that never edits Lean, team leads for large goals, and
  proof workers for single lemmas.
- An architect who designs and revises the proof decomposition, and an
  integrator who merges proofs, removes duplicate lemmas, and is the only
  role that commits.
- A critic that judges proposed specification amendments without seeing the
  proof attempts.
- A gatekeeper that runs comparator against a held-out copy of the
  specification and is the only role that can mark a goal done.

Two rules from the paper carry over unchanged. Every new invariant comes with
a witness that it holds on a reachable state. An amendment that weakens
security is never accepted, and goes to a human as a possible bug.

### Reuse from the AlphaProof Code repository

| Piece | Reuse |
| --- | --- |
| Comparator configuration and scripts | Direct |
| Axiom audit and `sorry` and `native_decide` rejection | Direct |
| Trusted and untrusted layering, enforced like `tcb-map` | Direct, with new paths |
| VCVio game definitions | Direct |
| Separation logic, weakest-precondition calculus, symbolic execution | Port. About 185,000 untrusted lines assume 64-bit AArch64. Agents can port them because they are untrusted and Lean checks the result |
| Hook contracts and `subroutineHook` | Port the definitions into the new trusted layer |
| `rust-obj2lean` | Replace with `rv32-img2lean`. Reuse the DWARF hint code where it applies |
| ISA semantics, ELF process loader, system calls | Not reused |
| DyLean | Not used |

Use the same Lean toolchain as the AlphaProof Code repository,
`leanprover/lean4:v4.34.0`, so that comparator and VCVio work unchanged.

### Compute

A campaign runs dozens of agents and repeated Lean builds on one machine.
Plan for a workstation or cloud machine with at least 64 GiB of memory. The
proof check also needs a CI runner with that much memory. A standard GitHub
runner doesn't have enough, so the proof workflow runs on a larger hosted
runner or a self-hosted one, outside `test.yml`.

## Feasibility assessment

### Size compared with libsignal

| Measure | libsignal | This plan (estimate) |
| --- | --- | --- |
| Verified instructions | About 140,000 AArch64 | 15,000 to 60,000 RV32: 5,000 to 20,000 for the checks and hardware code, and 10,000 to 40,000 for the cryptography |
| Trusted specification and semantics | About 26,000 lines | 9,000 to 19,000 lines |
| Binary proof lines | About 5.3 million | About 0.5 million to 2 million, if lines per instruction are similar |
| Allocator proof | About 70,000 lines | None, because there is no heap |
| Security proof | About 1.2 million lines across two models | Much smaller. One computational model with short reductions |
| New trusted models | AArch64 and Linux process | RV32, bare-metal platform, NOR flash with power loss, eFuse |

The proof-line estimate scales libsignal's ratio of about 38 lines per
instruction. RISC-V instructions are simpler, but RV32 code has more
instructions per operation, so the ratio is a rough guide. Straight-line
field arithmetic is likely cheaper per instruction than parser code, and the
algebra in the point proofs is extra work that the ratio doesn't capture.
Phase 5 measures both.

### What is easier than libsignal

- The verified code is an order of magnitude smaller.
- There is no heap, no file system, no protobuf, and no ratchet state.
- The security argument has one message and short reductions.
- RV32IMC is a small ISA with an official formal model and a Lean
  translation of it.
- The specification can be tested against mature reference implementations.

### What is harder or new

- The platform model has no precedent in the AlphaProof Code repository.
  Each register-level detail that the proof relies on is a trusted
  definition.
- Theorems span many boots and allow a power loss at any instruction.
- Parsers for DER and CMS have a long history of differential bugs, so the
  specification must be exact.
- The proof library must be ported from 64-bit AArch64 to 32-bit RISC-V.
- The cryptography proofs have no counterpart in the libsignal work. They
  need multi-word arithmetic on an ISA with no carry flag, and algebraic
  proofs that the point formulas match the group law.
- The agent setup must be built from scratch.

### Risks

| Risk | Effect | Mitigation | Fallback |
| --- | --- | --- | --- |
| Agent setup underperforms | Slow proof throughput | Pilot in phase 5 before committing to the full scope | Narrow the scope to the parsers and policy at the subroutine level |
| Platform model is unsound | Theorems don't hold on silicon | Lockstep tests on hardware, minimal register coverage, flash reads through a ROM hook | Shrink the model by moving more operations behind ROM hooks |
| X.509 or CMS specification is wrong | A theorem about the wrong parser | Differential testing on real bundles, strict profile | Pin more fields by exact byte match, which shortens the specification |
| CMS is too large to specify well | Delays the CMS contracts in phase 6 | Profile pinned to the Sigstore TSA's exact token shape | Use Rekor v1, whose signed entry timestamp gives signed time without CMS. That changes the threat model, because time then rests on the Rekor key instead of a TSA, and it carries the risk that Rekor v1 is retired. Escalate before switching |
| Cryptography proofs take longer than projected | The release waits on phase 7 | Proof-friendly implementation chosen in phase 0, and a field-multiplication proof in the phase 5 pilot | Escalate before changing scope. The release doesn't ship with cryptography hooks |
| Proof repair after every rebuild | Lost work | Freeze the bootloader early, keep contracts at `#[inline(never)]` boundaries | Accept repair as a campaign cost |
| The C3 can't lock the eFuse controller against code running in machine mode | A malicious application can burn the security level to 16 and permanently block updates | Confirm in phase 0 which protection unit (the permission-control unit or the CPU's PMP) can lock those registers until reset | None. The lock is a release blocker. If it can't be done, escalate, and don't claim the rollback or availability theorems against a malicious application |
| The 16 raises of the security level run out | No more security fixes with rollback protection, and no more key rotations | Raise the level only for security fixes and key rotations, never for routine releases or routine Sigstore changes | A new bootloader over USB |
| Software SHA-256 over a full slot makes boot too slow | Boot time over budget | Measure in phase 0. Hash only the bytes the header declares, not the whole slot | Escalate. The SHA accelerator stays off the verification path |
| Code size exceeds the bootloader region | The design doesn't fit | Measure in phase 0 | Move the partition table, or move signature checks into a second verified stage loaded from flash |

## Phases and deliverables

The project produces two things: Rust code that verifies OTA updates on the
device, and a Lean proof that the compiled code is correct. The work runs on
two tracks that meet at a code freeze:

- **Implementation track** (phases 1 and 2). The verifier, the bootloader,
  the host tools, and the signing and rotation pipelines, written to the
  rules in [Writing the Rust for verification](#writing-the-rust-for-verification)
  from the first commit.
- **Verification track** (phases 3 and 4). The specification, the machine
  model, and the proof tooling.

Phase 0 feeds both tracks, and the tracks run in parallel until phase 5
freezes the code. Phases 6, 7, and 8 prove the frozen code, and phase 9
releases it. Phases 6 and 7 run in parallel.

| Phase | Track | Starts after |
| --- | --- | --- |
| 0. Design and feasibility probes | Both | Approval of this plan |
| 1. Verifier code, host first | Implementation | Phase 0 |
| 2. Bootloader and pipelines | Implementation | Phase 1 |
| 3. Specification | Verification | Phase 0, and the corpus from phase 1 |
| 4. Machine model and proof tooling | Verification | Phase 0 |
| 5. Pilot proofs and code freeze | Both | Phases 2, 3, and 4 |
| 6. Function contracts | Verification | Phase 5 |
| 7. Cryptography proofs | Verification | Phase 5 |
| 8. Headline theorems | Verification | Phases 6 and 7 |
| 9. Mutation proofs and release | Both | Phase 8 |

Each phase ends with exit criteria. A phase that misses them stops the
project or changes its scope before more work goes in.

No ESP32-C3 hardware is available at the start of the project. Deliverables
and exit criteria marked **(hardware)** need a real board. Until one is
available, the work proceeds on the substitute listed in
[Work that needs real hardware](#work-that-needs-real-hardware), assuming the
hardware behaves as Espressif documents it. A phase can finish on the
substitute, but the release in phase 9 can't ship until every hardware item
is validated.

### Phase 0: design and feasibility probes

Deliverables:

- `c3-boot/docs/formats.md`, a byte-exact definition of the image header,
  the device bundle container, the key-set chain, the trust-root blob, the
  boot-state record, and the use of `SECURE_VERSION`.
- A spike bootloader that reads one slot, runs one check of each signature
  scheme with the candidate crypto crates, and jumps. **(hardware)**
- A comparison of the two cryptography designs in
  [Proving the cryptography](#proving-the-cryptography), and a decision.
- The pinned profile of a real Sigstore TSA token: its `SignerInfo` digest
  algorithm and its `messageImprint` algorithm, for the
  [message table](#signed-messages).
- A measurement of software SHA-256 over a full slot. Software SHA-2 is
  required on the verification path, so this measures cost, not whether to
  use it. **(hardware)**
- Measurements from the spike: code size per crate and SRAM use, which the
  linked image gives without hardware, and cycles per signature check and
  total boot time. **(hardware)**
- A test of which protection unit can lock the eFuse controller against
  machine-mode writes until reset. **(hardware)**
- A prototype of `rv32-img2lean` that turns the spike image into Lean data
  and checks the image digest.
- Lint configuration for the rules in
  [Writing the Rust for verification](#writing-the-rust-for-verification).

Exit criteria:

- The bootloader fits the chosen flash and SRAM layout.
- Boot time for two slot checks with 16-link chains, the worst case, is
  within a budget you set in this phase. **(hardware)**
- The eFuse lock works. If it can't, the project stops for a decision.
  **(hardware)**
- The extracted Lean data hashes to the image digest.

### Phase 1: verifier code, host first

Deliverables:

- The `verify` crate with every check, built and tested on the host.
- The `crypto` crate in the design chosen in phase 0, passing the
  Wycheproof and NIST vectors.
- `c3-ota`, a host command-line tool with these subcommands:
  - `pack` builds a signed-image header and segment table.
  - `transcode` turns a Sigstore bundle into the device container.
  - `chain build`, `chain sign`, and `chain verify` handle key-set chain
    links.
  - `blob build`, `blob sign`, and `blob verify` handle trust-root blobs.
  - `verify` runs the host build of `verify` on a slot.
- A corpus in `c3-boot/testdata/`: real bundles signed by GitHub Actions,
  mutated bundles, and each one's expected verdict from sigstore-go. It also
  has slots with an empty chain, a 16-link chain, a blob level that differs
  from the image security version, and a blob below its chain's last link.
- Fuzz targets for every parser, and Kani harnesses that prove the parsers
  can't panic for inputs up to the format's size limits.

Exit criteria:

- `verify` agrees with sigstore-go on the whole corpus, except for
  documented profile restrictions.
- The fuzz targets run for a CPU-hour budget set in phase 0 without a
  finding.
- The Kani harnesses pass.

Fuzzing and Kani are much cheaper than machine-code proofs. They find bugs
in the code before the expensive campaign has to.

### Phase 2: bootloader and pipelines

Deliverables:

- The `bootloader` crate, producing an ESP-IDF image from a reproducible
  build with a pinned digest.
- A minimal untrusted demo application that downloads an update, writes it
  to the inactive slot, and confirms it.
- `c3-release.yml`, which builds, signs in a separate job, transcodes, and
  publishes.
- `c3-trust-root.yml`, the scheduled job that checks Sigstore's trust root
  and opens a pull request with a candidate blob.
- `c3-boot.yml`, which builds every crate, runs host tests and a short fuzz
  run, and checks the reproducible image digest.
- A scenario runner that runs these scenarios end to end, first in
  Espressif's QEMU fork and later on a hardware rig of development boards
  and a relay that cuts power **(hardware)**:
  - A normal update, and updates with a bad signature, the wrong identity, a
    stale timestamp, and a lower security version
  - A rotation to a new Rekor log key, a security-level raise, and a
    trust-root key-set rotation
  - A fallback to the other slot after the first slot fails a check
  - Power cuts at random points during an update write, a boot-state write,
    and an eFuse burn
- A private Sigstore stack (Fulcio, Rekor v2, and a TSA, from
  `sigstore/scaffolding`) for the rotation tests, because the rig must
  rotate keys on demand.

Exit criteria:

- Every scenario passes in QEMU, and later on hardware. **(hardware)**
- A power-cut soak run leaves every board bootable. **(hardware)**
- The image is tagged `v0`, the input to the verification pilot.

### Phase 3: specification

Deliverables:

- The trusted `Spec/` modules in Lean, all executable: formats, the X.509
  and CMS subsets, Rekor v2, the trust root, the identity policy, `accept`,
  the boot state machine, the platform assumptions, the security games, and
  the cryptography specifications.
- A differential harness that runs the compiled Lean decoders on the corpus
  and compares each verdict with `verify` and with sigstore-go.
- Non-vacuity theorems for every hypothesis in the headline theorems.
- A review log from reviewer agents and a human.
- A tagged baseline commit, which the gatekeeper copies into its held-out
  directory.
- Optionally, source-level proofs that `verify` matches the specification,
  using Aeneas, which translates safe Rust into Lean. These find mismatches
  between the code and the specification before the machine-code campaign.

Exit criteria:

- The Lean decoders, `verify`, and sigstore-go agree on the whole corpus.
- The executable cryptography specifications pass every Wycheproof and NIST
  vector.
- A human approves the specification.

### Phase 4: machine model and proof tooling

Deliverables:

- The trusted `Model/` modules: the RV32IMC and Zicsr semantics, the
  platform model, and the hook contracts.
- A kernel-checked proof that the compact semantics agrees with
  `sail-riscv-lean` on every opcode in the `v0` image.
- `rv32-img2lean`, finished, including symbol names and DWARF hints.
- A lockstep harness that runs the whole bootloader on the corpus in the Lean
  semantics, in Espressif's QEMU fork, and on hardware through a debug
  probe, and compares the final states. The hardware leg waits for a board.
  **(hardware)**
- The core of the proof library ported to RV32: weakest-precondition rules
  for each instruction, separation logic, and symbolic execution.
- Gatekeeper scripts: comparator configuration, the axiom audit, and a check
  that trusted files never import untrusted files.
- Agent skills for each role in
  [Running the proof campaigns](#running-the-proof-campaigns), under
  `.cursor/skills/`.

Exit criteria:

- Lockstep runs agree on every corpus input, in QEMU first and on hardware
  later. **(hardware)**
- The equivalence proof covers every opcode in the `v0` image.
- The gatekeeper rejects a planted `sorry` and a planted edit to the
  specification.

### Phase 5: pilot proofs and code freeze

Deliverables:

- Machine-level contract proofs for the image header parser, the Merkle
  inclusion check, one field multiplication, and one point addition in
  `v0`.
- A throughput report covering proof lines per instruction, agent hours per
  function, and Lean build time and memory.
- A list of code changes that make proofs easier, such as splitting large
  functions or replacing a pattern the compiler turns into hard-to-prove
  code. The changes are made, tested on the rig, and rebuilt.
- The frozen image, tagged `v1`, with its digest pinned in the
  specification.

Exit criteria:

- The throughput report projects the full proof at no more than about three
  times the libsignal binary proof. Otherwise, cut scope before phase 6. For
  example, drop CMS by switching to Rekor v1 signed entry timestamps, or stop
  after the parser contracts.
- The cryptography projection from the field multiplication and point
  addition proofs fits the same bound. If it doesn't, escalate. The release
  doesn't ship with cryptography hooks, so cutting scope there is your
  decision.
- The cryptography specifications are frozen, and each hook contract that
  phase 6 uses is defined as the corresponding specification function, so
  phases 6 and 7 prove against the same definitions. A Lean check confirms
  that the definitions are identical.
- `v1` passes every phase 2 scenario in QEMU, and on hardware once a board
  is available. **(hardware)**

### Phase 6: function contracts

Deliverables:

- Gatekept contract proofs for every function reachable from reset in `v1`,
  in the groups from [Proof decomposition](#proof-decomposition). The order
  is byte helpers, container and header, trust root, Rekor v2, X.509 and
  policy, CMS, boot-state record, and eFuse, lock, and MMU.

Exit criteria:

- Every function reachable from reset, other than the cryptographic
  routines, has a contract proof or is one of the ROM flash hooks.

### Phase 7: cryptography proofs

Deliverables:

- Proof libraries for the word, field, and point layers in
  [Proof layers](#proof-layers).
- Machine-level contract proofs for SHA-2, ECDSA P-256 and P-384
  verification, and Ed25519 verification in `v1`.
- Proofs, through `subroutineHook`, that the real routines meet the hook
  contracts that phase 6 used.

Exit criteria:

- Every cryptographic routine in `v1` has a gatekept proof against the Lean
  specification.
- No cryptography hook remains.

### Phase 8: headline theorems

Deliverables:

- `boot_refines`
- `boots_safe`, `trust_root_monotone`, rollback, and availability
- The authenticity and transparency games, connected to `boot_refines`

Exit criteria:

- Comparator confirms every headline theorem against the held-out
  specification.
- The axiom audit is clean.
- The only hooks in the headline theorems are the ROM's flash read, erase,
  and write functions.
- One theorem links each hook contract used in phase 6 to the machine code
  that phase 7 proved.

### Phase 9: mutation proofs and release

Deliverables:

- A mutated image for each bug in
  [Validating the specification](#validating-the-specification), each with
  a proof that the headline theorems fail for it.
- A trusted-base report that lists every trusted file with its line count.
- Bootloader release 1.0: the `v1` image signed with the Secure Boot key,
  the proof artifact, and a CI job that checks the proofs from a clean
  checkout.

Exit criteria:

- Every mutant has a disproof.
- A clean checkout reproduces the image digest and checks every proof.
- The release image boots on the rig and passes every phase 2 scenario.
  **(hardware)**
- Every row in [Work that needs real hardware](#work-that-needs-real-hardware)
  is validated. **(hardware)**

## Work that needs real hardware

Until a board is available, each item uses the substitute in this table. The
substitutes rest on Espressif's documentation (the ESP32-C3 technical
reference manual, ESP-IDF, and the ROM headers) and on Espressif's QEMU fork.
If hardware later disagrees with an assumption, the trusted platform model
changes, and every proof that depends on that part of the model needs
repair.

| Item | Phase | Substitute until hardware | What hardware validates |
| --- | --- | --- | --- |
| Boot time and cycles per signature check | 0 | Instruction counts from QEMU, at an assumed one cycle per instruction at 160 MHz, plus a margin for flash wait states | Measured boot time against the budget |
| Software SHA-256 over a full slot | 0 | Same as boot time | The cost fits the boot-time budget |
| eFuse controller lock against machine-mode writes | 0 | Assume the permission-control unit locks the controller's registers until reset, as the technical reference manual describes | A write after the lock has no effect. This is a release blocker |
| eFuse burn interrupted by power loss | 2 | Assume any subset of the requested bits ends up set | The power-cut soak, with cuts during burns |
| `SECURE_VERSION` is free for the bootloader to use | 0 | Assume ESP-IDF's description: 16 bits in block 0, programmable one bit at a time, with no other user | The bootloader raises it one bit at a time on silicon |
| The state the ROM leaves at bootloader entry | 4 | Values from the technical reference manual and the ROM headers | A debug-probe dump of the registers and memory at entry |
| ROM flash read, erase, and write contracts | 4 | QEMU's flash emulation and the ROM header's documented behavior | The ROM functions on silicon match the contracts |
| eFuse programming, MMU table, and register-lock models | 4 | QEMU and the technical reference manual | Lockstep runs on hardware |
| NOR flash behavior under power loss | 2 | The model in [Platform model](#platform-model), which assumes the worst case: affected bytes take any value | The power-cut soak on the relay rig |
| Watchdog timeout against `maxSteps` | 0 | The ROM's documented watchdog configuration | A boot at `maxSteps` on silicon finishes before the watchdog fires |
| Scenario runs, including Rekor key rotation and key-set rotation | 2 | The QEMU scenario runner | The same scenarios on the rig |
| Release boot | 9 | None | The Secure Boot-signed image boots on a board with Secure Boot enabled |

## Repository layout

`c3-boot/` exists, and `c3-boot-proofs/` holds the first proofs: the
decision logic's specification, the boot-safety theorems over traces with
power loss, and a differential test against `c3-verify`. The rest of this
layout is a proposal:

- `c3-boot/`, a Cargo workspace with the `verify`, `crypto`, `bootloader`,
  and `c3-ota` crates and the demo application. The repository forbids a
  repository-root workspace and imports between top-level apps, so all the
  crates live under one top-level directory. While the workspace holds only
  host-testable crates, `test.yml`'s Rust leg runs its host checks, and
  `c3-boot.yml` adds the RISC-V `no_std` build. When the bootloader crate,
  which builds only for RISC-V, joins the workspace, `c3-boot/` moves out of
  `test.yml` Rust discovery, as `inkbot-esp32/` is, and `c3-boot.yml` takes
  over its host checks too.
- `c3-boot-proofs/`, the Lean project, with these directories:
  - `Spec/` and `Model/`, trusted
  - `Theorems/`, trusted statements of the headline theorems
  - `Equiv/`, `ProofLib/`, and `Proofs/`, untrusted
  - `Extracted/`, generated by `rv32-img2lean` and checked against the
    image digest
  - `Validation/`, with the differential harness, the lockstep harness, and
    the mutant images and their disproofs
  - `tools/`, with `rv32-img2lean` and the gatekeeper scripts

  A `c3-boot-proofs.yml` workflow checks it on a large runner.

The existing `inkbot-esp32/` firmware runs on a classic ESP32 (Xtensa) and
verifies Cosign signatures in the application. This plan doesn't change it.

## Out of scope

- Voltage and electromagnetic fault injection, which researchers have used
  against ESP32 Secure Boot and flash encryption
- Changes to flash by a physical attacker during boot
- Bugs in the ROM or in the silicon
- Custody of the offline keys and the security of the GitHub repository and
  its workflows
- The [rotation process off the device](#rotation-process-off-the-device)
- Destruction of retired trust-root keys. The theorems assume it. If two
  keys of a retired set survive, their holder can build a different chain
  from that point. Each rotation's destruction is a logged step of the key
  ceremony, and a release can't ship until the log for every retired set
  exists
- The application, its network stack, and its OTA download code
- Side channels during boot, which leak nothing secret because verification
  uses only public data

## Appendix: the system under verification

### Hardware constraints

The following ESP32-C3 facts come from ESP-IDF's `soc_caps.h` for the chip:

- The CPU is RV32IMC, supported by the upstream
  `riscv32imc-unknown-none-elf` Rust target.
- The SHA accelerator supports SHA-1, SHA-224, and SHA-256 only.
- There is an RSA accelerator up to 3072 bits, an HMAC peripheral, and a
  digital signature peripheral. There is no elliptic-curve accelerator.
- ROM Secure Boot v2 verifies the bootloader with RSA-3072-PSS only.
- Flash encryption uses XTS-AES-128.

### Chain of trust

1. **ROM.** Verifies the bootloader against an RSA-3072 key whose digest is
   in eFuse.
2. **Bootloader.** The verified code. It has the four genesis trust-root
   public keys compiled in.
3. **Key-set chain.** Stored in each slot. Each link names a new set of up to
   four Ed25519 keys, and two keys of the previous set sign it.
4. **Trust-root blob.** Stored in each slot, and signed by two keys of the
   newest set in the chain.
5. **Sigstore bundle.** Shipped with each image.
6. **Firmware image.** Untrusted until the checks pass.

The RSA-3072 key and the current trust-root key set are long-lived and stay
offline. Routine releases use only the workflow's Sigstore identity.

### Trust-root rotation

The public Rekor v2 instance starts a new log shard with a new key about
every six months, and the Fulcio intermediate certificate expires in October
2031. A trust root compiled into the bootloader would go stale, so it lives
in a signed blob that ships with each image.

#### The security level

The C3 has one eFuse counter that the bootloader can raise one bit at a
time: `SECURE_VERSION`, 16 bits in block 0. Every other eFuse block uses
Reed-Solomon coding and can be programmed only once. The plan therefore uses
one counter, the security level `L`, for everything that needs rollback
protection. It has 16 raises for the life of the device, shared between
image security fixes and trust-root key rotations. Spend them only on
security fixes and key rotations, never on routine releases or routine
Sigstore changes. Running out means a new bootloader over USB.

#### Chain links

Each link has:

- A level, from 1 through 16, strictly higher than the previous link's
  level.
- A key set of one to four Ed25519 public keys.
- Two or more signatures from distinct keys of the previous link's key set,
  each tagged with the key's index in that set. The first link's previous
  set is the genesis set compiled into the bootloader.

A chain has at most 16 links, because levels strictly increase. Each
signature covers the domain-separation string `c3-boot chain link v1`, a zero
byte, and the encoded link without its signatures, so a link signature can't
be reused as a blob signature or the other way around.

#### Blob contents

- A format version, and a sequence number for audit. The bootloader ignores
  the sequence number. Two blobs at the same level are both valid, which is
  safe because the holders raise the level whenever an older blob must stop
  working.
- A level. It must equal the image's security version, be at least the
  level of the chain's last link, and be at least `L`. This number is the
  slot's level.
- The Fulcio intermediates, Rekor v2 log keys with log IDs, and TSA signing
  certificates to accept, each with a validity window. A blob keeps the keys
  of inactive Rekor shards, as Sigstore's `trusted_root.json` file does, so
  that images logged before a shard change still verify.
- The identity policy.
- Two or more signatures from distinct keys of the chain's last key set, or
  of the genesis set if the chain is empty. Each signature covers the string
  `c3-boot trust root v1`, a zero byte, and the encoded blob without its
  signatures.

#### Where chains and blobs live and when they take effect

Each slot holds its image, its bundle, its chain, and its blob, and the
bootloader verifies a slot's image only with that slot's chain and blob. The
application writes all four to the inactive slot, so a new trust root
becomes active in the same step as the image that needs it, and a power loss
during the write leaves the old slot untouched. A bad blob fails only its
own slot, and the bootloader falls back to the other slot.

A routine rotation needs no extra steps on the device. When CI starts
logging to a new Rekor shard, the next release carries a blob at the same
level that lists the new shard's key, signed by the current key set.

#### Raising the level

Because the image's security version equals its blob's level, each slot has
one level. After the application confirms a slot, the next boot that selects
it raises `L` to the slot's level, if that is higher than `L`. From then on,
every slot below the new level fails, including the other slot. A security
fix therefore ships with a higher image security version and a blob
re-signed at that level by the current key set.

The bootloader burns one bit per eFuse program operation, reads the level
back after each one, and doesn't jump until the level reaches the slot's
level. If a bit doesn't read back as set after three attempts, it halts,
because the eFuse hardware has failed. A power loss during a burn leaves the
level between the old and the target value. The record still marks the slot
confirmed, so the next boot that selects the slot finishes the burn before
jumping.

While boards are being tested, nothing should be able to stop a board from
taking updates. A test build doesn't burn eFuses unless it was built with
`C3_EFUSE_BURN=on`, and a test build with the development keys boots the
accepted slot without the raise when a burn fails. Builds with production
keys must burn and halt as described above. The theorems describe that
production configuration.

Rollback protection takes effect when the eFuse level reaches the target,
not when the application confirms. Until then, the older slot still boots if
the confirmed slot fails its checks. `rollback` states the guarantee in
those terms.

#### Rotating trust-root keys

To retire a key set, for example because a key might be stolen, two holders
of the current set sign a new link that names a new set, at a level above
`L`. The next release carries the longer chain, a blob signed by the new set
at that level, and an image with a security version at that level. Once a
device confirms it and raises its level, blobs and images below that level
no longer boot.

Chains don't revoke anything on the device, which keeps no record of key
sets. Any two surviving keys of a retired set can still sign a blob at or
above `L`: the genesis set with an empty chain, or a retired set with a
chain that ends at its own link, followed by a link it signs. So the
retired set's private keys must be destroyed, and that includes the genesis
set after the first rotation. Destroying retired keys closes that path. One
stolen key from the current set can't sign anything on its own.

The genesis keys can't change without a new bootloader, which requires the
RSA-3072 key and a USB write. This plan doesn't include in-field bootloader
updates.

#### Rotation process off the device

1. A scheduled CI job fetches Sigstore's `trusted_root.json` file with a TUF
   client and compares it with the newest blob in the repository.
2. When they differ, the job builds a candidate blob with a deterministic
   encoder and opens a pull request that shows the old and new keys side by
   side.
3. Two key holders review the pull request and sign the candidate offline,
   each on a hardware token, and commit the signatures. Key-set rotations
   and level raises follow the same review.
4. CI checks the signed blob and chain with a host build of the bootloader's
   verifier and with the executable Lean decoder, then merges them.
5. The release workflow attaches the newest signed chain and blob to every
   release.

Today `c3-trust-root.yml` does part of steps 1 and 2. It reads the files at
a commit of `sigstore/root-signing` through the GitHub API, without checking
TUF metadata, and its pull request lists the entries a blob would hold
(`c3-ota describe`) but carries no candidate blob. The offline signing
tooling for step 3 and the Lean decoder for step 4 don't exist yet.

None of these steps runs on the device, so the machine-code proof doesn't
cover them. The proof shows that a device trusts exactly what the key-set
chain authorizes. Whether a signed blob lists the right Sigstore keys
depends on the key holders' review and the CI checks. A blob with a wrong
key makes devices reject new images. It can't make them accept a forged
image unless two holders of the current set signed a blob that lists an
attacker's key.

Sigstore lists a new key in `trusted_root.json` before clients sign with it.
The Rekor v2 key had a validity start of 2025-09-23, while the signing
configuration still listed only Rekor v1. That gap gives the key holders time
to sign a blob before the first release that needs it.

### Release identity policy

The bootloader accepts a Fulcio leaf only if these extensions match exactly:

| Fulcio extension | Required value |
| --- | --- |
| Issuer (V2), `1.3.6.1.4.1.57264.1.8` | `https://token.actions.githubusercontent.com` |
| Build Signer URI, `1.3.6.1.4.1.57264.1.9` | `https://github.com/OWNER/REPO/.github/workflows/c3-release.yml@refs/heads/main` |
| Source Repository Identifier, `1.3.6.1.4.1.57264.1.15` | The repository's numeric ID |
| Source Repository Owner Identifier, `1.3.6.1.4.1.57264.1.17` | The owner's numeric ID |
| Build Trigger, `1.3.6.1.4.1.57264.1.20` | `push` |

Replace the following:

- `OWNER/REPO`: the GitHub repository that publishes firmware.
- `c3-release.yml`: the workflow file that signs releases. If signing moves
  into a reusable workflow, name that file.

### Bundle profile

- `hashedrekord` entries only, with an ECDSA P-256 leaf key over SHA-256.
- The leaf chains to a Fulcio intermediate listed in the blob (ECDSA P-384
  with SHA-384).
- A Rekor v2 inclusion proof and a checkpoint signed with Ed25519 by a log
  key listed in the blob.
- An RFC 3161 token from a TSA listed in the blob, signed with ECDSA P-384.
  Rekor v2 entries have no signed time, so the TSA token is the only signed
  time.
- No check of the leaf's embedded SCT.

Each slot check runs at least six software signature checks. Two Ed25519
checks cover the blob, one Ed25519 check covers the checkpoint, two P-384
checks cover the leaf certificate and the TSA token, and one P-256 check
covers the image signature. Each chain link adds two Ed25519 checks, so a
chain at its 16-link limit adds 32.

CI transcodes the protobuf JSON bundle into a fixed binary container that
holds the same signed byte strings. The bootloader still produces one JSON
document. A Rekor v2 leaf is the RFC 6962 leaf hash of the RFC 8785
canonical JSON form of the `hashedrekord` entry, which the bootloader
rebuilds from bundle fields, as `ToEntryHash` in rekor-tiles does.

### Signed messages

Each signature check covers exactly these bytes. A parser bug that feeds a
check the wrong bytes is as dangerous as a broken signature scheme, so the
specification defines each message once, and the proofs use that
definition.

| Check | Key | Message | Hash |
| --- | --- | --- | --- |
| Chain link | Ed25519, previous key set | `c3-boot chain link v1`, a zero byte, and the link without signatures | SHA-512 inside Ed25519 |
| Trust-root blob | Ed25519, last key set | `c3-boot trust root v1`, a zero byte, and the blob without signatures | SHA-512 inside Ed25519 |
| Image signature | ECDSA P-256, leaf key | The SHA-256 digest of the signed image, which is the header followed by the segments | SHA-256 |
| Leaf certificate | ECDSA P-384, Fulcio intermediate | The leaf's DER `tbsCertificate`, exactly as it appears in the certificate | SHA-384 |
| Checkpoint | Ed25519, Rekor log key | The checkpoint note body, through its final newline | SHA-512 inside Ed25519 |
| Timestamp token | ECDSA P-384, TSA certificate | The DER `signedAttrs` of the token's `SignerInfo`, re-tagged as `SET OF` as RFC 5652 requires | SHA-256, pinned from Sigstore's timestamp authority |
| Timestamp imprint | None | The token's `messageImprint` must equal the hash of the image signature bytes | SHA-256, pinned from Sigstore's timestamp authority |

The Rekor entry's digest must equal the image signature's SHA-256 digest,
and the entry's signature and certificate must equal the bundle's.

#### Time checks

Let `t` be the TSA token's signed time. The bootloader accepts only if all of
the following hold:

- `t` is inside the leaf certificate's validity window.
- `t` is inside the blob's validity window for the Fulcio intermediate that
  signed the leaf.
- `t` is inside the blob's validity window for the TSA certificate that
  signed the token.
- `t` is inside the blob's validity window for the log key that signed the
  checkpoint.

Windows of keys that didn't take part in this check don't matter, so a blob
can keep expired Rekor shard keys without widening what it accepts.

### Image format and boot procedure

The signed image is a header (magic, chip ID, security version, segment
table, entry point) followed by segments. The security version is a number
from 0 through 16. The bootloader rejects a slot whose image security version
is above 16, is below `L`, or differs from its blob's level, on every slot it
tries, including the fallback slot.
It also rejects overlapping segments, segments that overlap its own memory,
segments outside the allowed regions, and length mismatches.

The bootloader reads the boot-state record and chooses a slot. For that slot,
it checks the chain, the blob, and their levels, parses the header, hashes
the image, checks the Rekor entry and checkpoint, checks the certificate and
policy, checks the image signature, checks the timestamp, and checks the
security version. It then raises `L` if a confirmed image calls for it, locks
the eFuse controller, maps the image, and jumps. If a check fails, it tries
the other slot with the same checks. If both fail, it halts.

A trial image boots a fixed number of times. If the application doesn't
confirm it, the bootloader reverts.

### Boot-state record

The record has two copies in two separate flash sectors. Each copy has a
magic number, a format version, a 32-bit generation, the preferred slot, the
trial slot and its remaining trial boots, a confirmed flag for each slot, and
a CRC-32.

- **Reading.** A copy is valid if its magic, format version, and CRC are
  right. The bootloader uses the valid copy with the higher generation, or
  copy A if the generations are equal. If neither copy is valid, it tries
  slot A and then slot B.
- **Writing.** The bootloader erases and rewrites only the sector that
  doesn't hold the copy in use, with the generation one higher. The copy in
  use stays valid until the new one is complete. A generation at its maximum
  value isn't incremented further.

The CRC detects torn writes, not attacks. The application can write
anything to the record, so no security property depends on it. Every slot
the bootloader boots passes every check on that boot. A forged record can
only change which authentic slot boots, or raise `L` early by marking an
authentic image confirmed, which can make the other slot unbootable. A forged
record can also keep selecting an older slot, which postpones the eFuse raise
for a confirmed newer slot for as long as the application keeps doing it.
These are availability effects, and a malicious application can already
erase flash or refuse updates.

### Signing pipeline

1. A build job without `id-token: write` builds the image.
2. A separate signing job, the only one with `id-token: write`, signs the
   image digest with `cosign`, using pinned first-party actions only. Any
   step in that job can mint a token and sign arbitrary bytes.
3. The signing configuration selects Rekor v2 and the Sigstore TSA.
4. The job transcodes the bundle, checks it with a host build of the
   verifier, and publishes the image and container.
5. A Rekor monitor reports any entry for the release identity that doesn't
   match a known release.

Today `c3-release.yml` does steps 1 to 3, checks the bundle in a separate
job that also boots the slot in QEMU, and publishes only workflow
artifacts. The monitor doesn't exist yet. It also signs the demo
application under the release identity on every push to `main`, so every
demo build is a valid image at security version 0. Before production,
releases need their own identity or demo builds need to stop signing.

## Sources

- "AlphaProof Code: Verifying Signal's Security at the Machine-Code Level,"
  Google DeepMind, 2026
- [`google-deepmind/code-verification`](https://github.com/google-deepmind/code-verification)
- [Sail Lean backend](https://github.com/rems-project/sail/tree/sail2/src/sail_lean_backend)
- [`opencompl/sail-riscv-lean`](https://github.com/opencompl/sail-riscv-lean)
- [ESP32-C3 `soc_caps.h`](https://github.com/espressif/esp-idf/blob/master/components/soc/esp32c3/include/soc/soc_caps.h)
- [Rekor v2 README](https://github.com/sigstore/rekor-tiles/blob/main/README.md)
- [rekor-tiles `hashedrekord.go`](https://github.com/sigstore/rekor-tiles/blob/main/pkg/types/hashedrekord/hashedrekord.go)
- [sigstore-go `tlog.go`](https://github.com/sigstore/sigstore-go/blob/main/pkg/verify/tlog.go)
- [Fulcio OID information](https://github.com/sigstore/fulcio/blob/main/docs/oid-info.md)
- [Sigstore `trusted_root.json`](https://github.com/sigstore/root-signing/blob/main/targets/trusted_root.json)
