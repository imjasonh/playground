# Plan: machine-checked Sigstore OTA verification on the ESP32-C3

> **Status:** proposal. Nothing in this plan is implemented. The facts about
> Sigstore and the ESP32-C3 were checked on 2026-11-10 against the sources
> listed at the end.

This plan applies the approach from DeepMind's AlphaProof Code work on
libsignal to over-the-air (OTA) firmware updates on an ESP32-C3. The
bootloader and firmware are Rust. GitHub Actions signs each release with
Sigstore keyless signing. Fulcio issues a short-lived certificate for the
workflow's OIDC identity, and Rekor logs the signature.

## Goal

Prove, with a Lean proof that the Lean kernel checks against the compiled
RISC-V machine code of the bootloader, the following claim:

> On every boot, whatever bytes are in flash, the bootloader either halts
> safely or jumps to an image whose SHA-256 digest a Rekor checkpoint commits
> to, in an entry whose Fulcio certificate names the release workflow on
> `main`. The signing time falls inside that certificate's validity, and the
> image's security version is at least the version burned into eFuse.

The proof also shows that the bootloader never faults, never panics, and
always terminates, on any flash contents.

The firmware application, the network stack, and the OTA download code stay
outside the proof. The adversary controls them.

## Background on AlphaProof Code

The paper "AlphaProof Code: Verifying Signal's Security at the Machine-Code
Level" and the
[`google-deepmind/code-verification`](https://github.com/google-deepmind/code-verification)
repository describe the following:

- **Target.** Unmodified libsignal, compiled by stock `rustc` into a static
  AArch64 Linux binary of about 140,000 instructions. The theorems are about
  whole runs of that binary under a Lean model of AArch64 and Linux. The model
  has 467 instructions and 31 system calls, and it is single-threaded.
- **Trust.** The Rust compiler isn't trusted. The reader trusts the Lean
  kernel, about 18,000 lines of specification, about 8,000 lines of ISA and
  loader semantics, and 39 hooked routines. A hooked routine is replaced by a
  contract instead of verified code. Every low-level cryptographic primitive
  was hooked.
- **Process.** A human and agents write the specification, and reviewer agents
  critique it. Teams of 40 to 80 prover agents then run for 24 to 72 hours per
  campaign. A gatekeeper accepts a proof only if Lean's comparator tool
  confirms that it proves exactly a held-out copy of the specification, using
  only Lean's standard axioms.
- **Lesson.** Proofs became cheap, and most of the human effort went into the
  specification.
- **Released.** The AArch64 semantics, the separation-logic proof library,
  `rust-obj2lean`, the trusted-base checks (`tcb-map`, `axiom-audit`, and
  comparator configurations), and the proofs. The repository doesn't include
  the agent skills, the orchestrator, or the gatekeeper, and it has no RISC-V
  or bare-metal support.

This project reuses the method and the checking discipline. It needs a new
RISC-V machine model, new peripheral models, and its own agent setup.

## Hardware constraints

The following ESP32-C3 facts come from ESP-IDF's `soc_caps.h` for the chip:

- The CPU is RV32IMC, and Rust supports it with the upstream
  `riscv32imc-unknown-none-elf` target. No Espressif compiler fork is needed.
- The SHA accelerator supports SHA-1, SHA-224, and SHA-256. It doesn't
  support SHA-384 or SHA-512.
- The chip has an RSA accelerator up to 3072 bits, an HMAC peripheral, and a
  digital signature peripheral. It has no elliptic-curve accelerator, so
  ECDSA and Ed25519 run in software.
- ROM Secure Boot v2 verifies the second-stage bootloader with RSA-3072-PSS
  only. The eFuse holds up to three key digests, and the chip supports key
  revocation.
- Flash encryption uses XTS-AES-128.

## Chain of trust

1. **ROM.** The mask ROM verifies the bootloader against an RSA-3072 key whose
   digest is in eFuse. The ROM is immutable and trusted.
2. **Bootloader.** The verified Rust bootloader. It is the only code this plan
   proves anything about.
3. **Trust-root blob.** A small file in flash, signed by an offline Ed25519
   trust-root key whose public half is compiled into the bootloader. It lists
   the Sigstore keys and certificates to accept and the identity policy.
4. **Sigstore bundle.** Shipped next to each firmware image. It contains the
   Fulcio leaf certificate, the image signature, the Rekor inclusion proof and
   checkpoint, and a timestamp authority (TSA) token.
5. **Firmware image.** Untrusted code that the bootloader runs only after the
   checks in this plan pass.

This chain has two long-lived keys, and both stay offline:

- The RSA-3072 bootloader key. It can sign a bootloader with any trust root,
  so it is the most powerful key in the system. ROM Secure Boot can't use
  short-lived Fulcio certificates, so this key can't be removed.
- The Ed25519 trust-root key. It signs a new trust-root blob when Sigstore
  rotates keys.

Routine releases use neither key. They use only the workflow's Sigstore
identity.

## Why the trust root lives in flash

The bootloader sits at a fixed flash offset, and replacing it in the field
isn't safe. A trust root compiled into it can't change. Sigstore's keys do
change:

- The public Rekor v2 instance starts a new log shard, with a new key, about
  every six months. Clients learn the new key from the TUF-distributed
  `trusted_root.json` file.
- The Fulcio intermediate certificate and the TSA certificate can also rotate.

If the bootloader had the trust root compiled in, devices would stop
accepting updates at the first rotation. With the trust root in a signed blob,
a rotation is an ordinary OTA update that carries a new blob signed by the
offline trust-root key.

The trust-root blob has a fixed binary layout:

- A format version and a monotonic blob version. The bootloader rejects a
  blob older than the newest one it accepted, and records the version in a
  boot-state record.
- The pinned Fulcio intermediate certificate, in DER, with its validity
  window. Pinning the intermediate instead of the root saves one P-384
  signature check on each boot.
- The Rekor log keys (Ed25519 for Rekor v2), each with its log ID and a
  validity window.
- The TSA certificate chain, with a validity window.
- The identity policy described in the next section.
- An Ed25519 signature over all of the preceding fields.

## Release identity policy

The bootloader accepts a Fulcio leaf certificate only if all of the following
extensions match exactly. Prefix matches aren't allowed.

| Fulcio extension | Required value |
| --- | --- |
| Issuer (V2), `1.3.6.1.4.1.57264.1.8` | `https://token.actions.githubusercontent.com` |
| Build Signer URI, `1.3.6.1.4.1.57264.1.9` | `https://github.com/OWNER/REPO/.github/workflows/release.yml@refs/heads/main` |
| Source Repository Identifier, `1.3.6.1.4.1.57264.1.15` | The repository's numeric ID |
| Source Repository Owner Identifier, `1.3.6.1.4.1.57264.1.17` | The owner's numeric ID |
| Build Trigger, `1.3.6.1.4.1.57264.1.20` | `push` |

Replace the following:

- `OWNER/REPO`: the GitHub repository that publishes firmware.
- `release.yml`: the workflow file that signs releases.

The numeric IDs survive a rename. They also stop an attacker who deletes and
re-registers the repository name. If the signing step moves into a reusable
workflow, the Build Signer URI names the reusable workflow, not the caller,
so the policy must name that file.

## Bundle profile

The bootloader accepts one bundle shape and rejects everything else:

- **Entry type.** `hashedrekord` only, so the leaf key signs the SHA-256
  digest of the image. No DSSE envelopes.
- **Leaf key.** ECDSA P-256 with SHA-256.
- **Certificate chain.** Leaf, then the pinned intermediate. The bootloader
  rejects a leaf with an unknown critical extension.
- **Log.** Rekor v2. The bundle carries an RFC 6962 Merkle inclusion proof
  and a checkpoint that the log key signs with Ed25519.
- **Time.** An RFC 3161 timestamp token from the TSA in the trust root. Rekor
  v2 entries carry no signed integrated time, so the TSA token is the only
  signed time. The signed time must fall inside the leaf certificate's
  validity window, and inside the validity windows of the log key and TSA
  certificate in the trust root.
- **Certificate transparency.** The bootloader doesn't check the Fulcio
  leaf's embedded SCT. Checking it means rebuilding the precertificate's DER,
  and Rekor already provides transparency for the signing event.

The bootloader needs no wall clock. Every time check compares signed times
with signed validity windows.

### Device-side encoding

A Sigstore bundle is protobuf JSON, and its JSON wrapper isn't signed. At
publish time, CI transcodes the bundle into a fixed binary container that
holds the same signed byte strings. Those are the leaf certificate DER, the
image signature, the TSA token DER, the checkpoint text, and the proof
hashes. A
mistake in transcoding can make verification fail, but it can't make a forged
bundle pass, because the bootloader checks every security-relevant byte
cryptographically.

The bootloader still produces one JSON document. A Rekor v2 leaf is the RFC
6962 leaf hash of the RFC 8785 canonical JSON form of the `hashedrekord`
entry (kind, API version `0.0.2`, digest, signature, and verifier
certificate). The bootloader rebuilds that entry from the bundle fields and
hashes it, as `ToEntryHash` in rekor-tiles and `reconstructV2EntryHash` in
sigstore-go do. Serializing a fixed template is much simpler to specify than
parsing arbitrary JSON.

## Firmware image format

The signed image is a header followed by its segments. The SHA-256 digest in
the Rekor entry covers both. The header has:

- A magic number and a format version
- The chip ID, which must equal the ESP32-C3 ID
- A 16-bit security version for anti-rollback, compared with the eFuse
  counter
- The segment table, with a load address and length for each segment
- The entry point

The bootloader rejects an image if any of the following is true:

- A segment overlaps another segment.
- A segment overlaps the bootloader's own code, data, or stack.
- A segment falls outside the RAM regions or the flash mapping that the image
  is allowed to use.
- The segment lengths don't sum to the length that was hashed.

CVE-2018-18558 was an ESP-IDF bootloader that loaded segments before
verifying them, which let a crafted segment overwrite the bootloader and
bypass Secure Boot. That bug is the first mutation test in this plan.

## Boot procedure

The bootloader runs on one core with interrupts disabled and no heap. It
reads a boot-state record from flash, chooses a slot, and checks the slot in
this order:

1. Verify the trust-root blob. Reject it if its version is older than the
   recorded version.
2. Parse the image header and segment table, with the checks from the
   previous section.
3. Hash the header and segments with the SHA accelerator.
4. Rebuild the Rekor entry, compute its leaf hash, verify the inclusion
   proof, and verify the checkpoint signature.
5. Verify the leaf certificate against the pinned intermediate, and check the
   identity policy.
6. Verify the image signature with the leaf key.
7. Verify the TSA token, and check the signed time against every validity
   window.
8. Check the security version against eFuse.
9. Map or copy the image and jump to its entry point.

If any check fails, the bootloader tries the other slot. If both slots fail,
it halts.

### A/B slots and rollback

- The application writes a new image and bundle to the inactive slot, then
  asks for a trial boot by writing the boot-state record.
- The bootloader boots a trial image a fixed number of times. If the
  application doesn't confirm the image within that count, the bootloader
  reverts to the previous slot.
- After the application confirms an image, the bootloader burns the image's
  security version into eFuse on the next boot. eFuse bits can only change
  from 0 to 1, so the version never decreases.
- The boot-state record uses two copies with sequence numbers and checksums,
  so a power loss while writing it leaves one valid copy.

The application can confirm a bad image that is authentic. That is outside
the bootloader's guarantee.

### Execute in place or copy to SRAM

The application runs from flash through the cache (execute in place, or XIP).
A physical attacker can change external flash between the moment the
bootloader verifies an image and the moment the CPU fetches it. This plan
must choose one of the following:

- Assume no physical attacker can change flash during boot. The proof then
  models flash as unchanging while the bootloader runs.
- Copy the image to SRAM, verify the copy, and run from SRAM. This removes
  the gap but limits image size to the available SRAM.

The first option fits the C3's memory. Write the choice into the
specification as an explicit assumption.

## Signing pipeline

1. A build job compiles the firmware and uploads the image as an artifact.
   This job has no `id-token: write` permission.
2. A separate signing job downloads the image, computes its SHA-256 digest,
   and signs it with `cosign`. This job is the only one with
   `id-token: write`. It uses only pinned first-party actions, because any
   step in the job can mint an OIDC token and sign arbitrary bytes.
3. The signing job uses a Sigstore signing configuration that selects Rekor
   v2 and the Sigstore TSA. The default configuration might still select
   Rekor v1.
4. The job transcodes the bundle into the device container, verifies the
   result with a host build of the bootloader's verifier, and publishes the
   image and container.
5. A Rekor monitor watches the log for every entry that matches the release
   identity and reports any entry that doesn't match a known release.
   Without a monitor, transparency protects nothing, because an offline
   device can't detect a log that shows different contents to different
   readers.

## Formal specification

The specification is written in Lean and approved before any proof work
starts. It has the following parts:

- **Formats.** The image header, the trust-root blob, and the device bundle
  container, as byte-level parsers that return either a value or a
  rejection.
- **X.509 subset.** DER encoding rules for exactly the structures in a Fulcio
  leaf and the pinned intermediate, the extensions in the identity policy,
  and the validity window.
- **Rekor v2.** The canonical JSON form of a `hashedrekord` entry, RFC 6962
  leaf and node hashing, inclusion-proof verification, and the checkpoint
  note format.
- **RFC 3161 subset.** The parts of a timestamp token and its CMS
  `SignedData` wrapper that carry the signed time and the message imprint.
- **Acceptance predicate.** A pure function from flash contents and eFuse
  state to the slot and entry point the bootloader must choose, or to a halt.
- **Boot state machine.** Slot selection, trial boots, confirmation,
  rollback, and eFuse burns, under a power loss at any step.
- **Adversary.** Arbitrary initial flash contents in every region that the
  application can write. Arbitrary application behavior between boots,
  including arbitrary writes to the boot-state record. A power loss at any
  instruction.

### Theorems

- **Binary refinement.** For every initial flash and eFuse state, every run
  of the bootloader from reset ends by jumping to the entry point that the
  acceptance predicate chooses, or by halting. No run faults, panics, or
  diverges.
- **Authenticity.** This is a computational theorem in the style of VCVio.
  The probability that the bootloader jumps to an image that no honest
  signing run produced is at most the sum of these terms:
  - The advantage of forging an Ed25519 signature under the trust-root key
    or a Rekor log key
  - The advantage of forging an ECDSA P-384 signature under the Fulcio
    intermediate, or an ECDSA P-256 signature under a leaf key
  - The advantage of forging a TSA signature
  - The advantage of finding a SHA-256 collision
- **Anti-rollback.** The security version of every image the bootloader
  jumps to is at least the eFuse counter, and the counter never decreases.
- **Availability.** If one slot holds a confirmed authentic image, no
  sequence of application writes and power losses leaves both slots
  unbootable.

The authenticity theorem rests on one assumption that no proof can remove:
Fulcio issues a certificate naming an identity only to a caller that holds a
valid OIDC token for that identity, and GitHub issues that token only to the
named workflow.

## Machine model

The released AArch64 semantics models Linux user mode. This project needs a
bare-metal RV32IMC model:

- **ISA.** RV32I, M, C, and the Zicsr instructions that the bootloader uses,
  in machine mode. Derive it from the Sail RISC-V model where possible.
- **Initial state.** The loaded segments, the stack pointer, and the cache
  and MMU configuration that the ROM leaves when it starts the bootloader.
- **Memory map.** SRAM, ROM, the flash mapping, and memory-mapped peripheral
  registers. An access outside the map is a fault.
- **Peripherals.** Models of the SPI flash or cache path, eFuse, RTC memory,
  and the watchdog. Flash follows NOR rules. An erase sets every bit in a
  sector to 1, a write can only clear bits, and a power loss during an erase
  or write leaves the affected bytes undefined.
- **Hooks.** Contracts for ROM functions that the bootloader calls and for
  the SHA accelerator. Every hook is part of the trusted specification.

Validate the trusted model by testing it against the Sail RISC-V model,
Espressif's QEMU fork for the ESP32-C3, and real hardware, running the same
binaries in lockstep. This is the same method the AlphaProof Code team used
with Unicorn, Sail, and qemu.

## Cryptographic primitives

Hook these routines in the first proof campaign, as the libsignal work did:

- ECDSA P-256 verification
- ECDSA P-384 verification, with software SHA-384
- Ed25519 verification, with software SHA-512
- The SHA-256 accelerator

Test the hooks against published test vectors and against the real
implementations on hardware. A later campaign can replace the software hooks
with machine-code proofs of functional correctness against Lean
specifications of FIPS 186-5, RFC 8032, and FIPS 180-4. The SHA accelerator
stays a hook, because silicon can't be verified.

Verification on the device uses only public data, so side-channel leaks
during boot don't expose a secret.

## Proof process

- Reuse comparator, the axiom audit, and the rule that trusted files never
  import untrusted files, from the AlphaProof Code repository.
- Reuse VCVio for the computational theorem.
- Don't use DyLean. A single signed message needs no symbolic protocol model.
- Build an agent setup with the roles from the paper: a specification writer
  with reviewers from a different model family, an orchestrator, proof
  workers, an integrator, and a gatekeeper that only agents outside the proof
  team can run.
- Require every new invariant to come with a witness that it holds on a
  reachable state, so that agents can't make progress with vacuous lemmas.

### Mutation tests

For each of the following bugs, prove that the security theorem is false for
a bootloader binary built with that bug:

- Segments loaded before verification, as in CVE-2018-18558
- The signature check skipped
- The image digest computed over fewer bytes than the bootloader maps
- The identity policy matched by prefix
- The Build Signer URI read from the wrong extension
- The signed time not compared with the leaf certificate's validity window
- A trust-root blob with a lower version accepted
- The eFuse security version not checked

## Repository layout

The repository has no Lean code. These directories are proposals:

- `c3-bootloader/`, the Rust bootloader crate. Like `inkbot-esp32/`, it must
  be excluded from `test.yml` Rust discovery and get a dedicated workflow
  that builds for `riscv32imc-unknown-none-elf`, runs host tests, and checks
  that the binary matches the hash the proofs pin.
- `c3-bootloader-proofs/`, the Lean specification, machine model, and proofs.
  A full build of the libsignal proofs took hours and 15 to 34 GiB of memory,
  so this directory needs its own workflow outside `test.yml`, run on a
  larger runner.

The existing `inkbot-esp32/` firmware runs on a classic ESP32 (Xtensa) and
verifies Cosign signatures in the application. This plan doesn't change it.

## Phases

Each phase depends on the ones before it.

1. **Design.** Fix the image header, the trust-root blob, the device bundle
   container, and the boot-state record. Decide between XIP and SRAM
   execution.
2. **Prototype.** Build the bootloader and the signing pipeline. Measure code
   size and boot time on real hardware.
3. **Specification.** Write the Lean specification and get it approved.
4. **Machine model.** Build the RV32IMC model, the peripheral models, and the
   hooks, and validate them in lockstep.
5. **Source-level pass (optional).** Check the parsers and the state machine
   with Verus, Aeneas, or Kani, to find design bugs before the more expensive
   machine-code campaign.
6. **Machine-code proofs.** Run the agent campaigns and the mutation tests.
7. **Primitive proofs (optional).** Replace the software cryptography hooks
   with proofs.

## Risks and open questions

- **Code size.** By default the C3 bootloader has about 32 KB before the
  partition table at `0x8000`. Software P-256, P-384, Ed25519, SHA-384,
  SHA-512, a DER parser, and a CMS parser probably need far more. The
  partition table can move, but the ROM also limits where it loads the
  bootloader in SRAM. Measure this in the prototype phase.
- **Boot time.** Each boot runs about five software signature checks on a
  160 MHz core. Measure this in the prototype phase. Caching a result with
  the HMAC peripheral and an eFuse key is possible, but it adds a trusted
  path to the specification.
- **Peripheral model soundness.** The flash, cache, and eFuse models are new
  trusted code that the libsignal work had no equivalent of. This is the
  largest specification risk.
- **TSA token profile.** The key type and certificate chain of
  `timestamp.sigstore.dev` determine which signature scheme the bootloader
  needs for step 7. Confirm both before the design phase ends.
- **Sigstore changes.** A change to the Fulcio certificate profile, the Rekor
  v2 entry format, or the TSA token format breaks the strict profile. A new
  trust-root blob can't fix a format change, so a format change needs a new
  bootloader.
- **Agent tooling.** The AlphaProof Code agent setup isn't public. Building
  an equivalent is a project of its own.

## Out of scope

- Voltage and electromagnetic fault injection, which researchers have used
  against ESP32 Secure Boot and flash encryption
- Changes to flash by a physical attacker during boot, unless the design
  copies images to SRAM
- Bugs in the ROM or in the silicon
- Custody of the two offline keys and the security of the GitHub repository
  and its workflows
- The application, its network stack, and its OTA download code

## Sources

- "AlphaProof Code: Verifying Signal's Security at the Machine-Code Level,"
  Google DeepMind, 2026
- [`google-deepmind/code-verification`](https://github.com/google-deepmind/code-verification)
- [ESP32-C3 `soc_caps.h`](https://github.com/espressif/esp-idf/blob/master/components/soc/esp32c3/include/soc/soc_caps.h)
- [Rekor v2 README](https://github.com/sigstore/rekor-tiles/blob/main/README.md)
- [rekor-tiles `hashedrekord.go`](https://github.com/sigstore/rekor-tiles/blob/main/pkg/types/hashedrekord/hashedrekord.go)
- [sigstore-go `tlog.go`](https://github.com/sigstore/sigstore-go/blob/main/pkg/verify/tlog.go)
- [Fulcio OID information](https://github.com/sigstore/fulcio/blob/main/docs/oid-info.md)
- [Sigstore `trusted_root.json`](https://github.com/sigstore/root-signing/blob/main/targets/trusted_root.json)
