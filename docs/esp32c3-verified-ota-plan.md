# Plan: verify an ESP32-C3 Sigstore bootloader at the machine-code level

> **Status:** proposal. Nothing in this plan is implemented. The facts about
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
- **Trust-root rotation and revocation.** The bootloader uses a trust root
  only if two of the four trust-root keys compiled into it signed that trust
  root, not counting keys that eFuse marks revoked, and only if its epoch is
  at least the epoch in eFuse. After a device burns a new epoch, a stolen key
  that only older trust roots list gives an attacker nothing.
- **Rollback and availability.** eFuse counters never decrease. If the
  application follows the update protocol, no sequence of power losses makes
  both slots unbootable while one confirmed image exists. A malicious
  application can erase flash, which a USB reflash repairs, but it can't burn
  eFuse, because the bootloader locks the eFuse controller before it jumps.

This work differs from the libsignal work in five ways:

- It targets bare-metal RISC-V, not AArch64 Linux user mode. Peripherals,
  eFuse, and NOR flash take the place of system calls.
- Its theorems span many boots with power loss at any instruction, not one
  run of a command-line tool.
- The binary that gets verified is the binary that ships. Hooked routines
  stay in the image as real code, and the proof treats calls to them through
  contracts that a later campaign can discharge.
- The security property is short. Most of the specification is parsing:
  X.509, CMS, and Rekor's formats.
- The verified code is much smaller. This plan estimates 5,000 to 20,000
  RV32 instructions outside the hooked cryptography, compared with about
  140,000 AArch64 instructions for libsignal.

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
          out.result = .jumped entry mapping ∧
          out.efuse = p.efuse.burn burns ∧
          out.efuseLocked ∧
          out.bootState = nextBootState p.bootState slot
      | .halt =>
          out.result = .halted ∧ out.efuse = p.efuse
```

`Platform` is the state that the ROM leaves when it starts the bootloader:
flash contents, eFuse values, the boot-state record, and the CPU and
peripheral registers. `accept` is the acceptance function, written in Lean
and trusted. It includes the trust-root checks. It picks the trust root
stored with each slot, checks its signatures and epoch, and returns the
eFuse bits to burn. Those are a higher epoch, revocations, and a higher
security version, each only after the application confirmed the image that
carried it. `BootRunsTo` says that every run ends in an outcome that satisfies the
postcondition and that no run faults. `out.result = .jumped` means the
program counter reached `entry` with the flash mapping set to `mapping` and
interrupts disabled. `out.efuseLocked` means the eFuse controller's
registers are locked against writes until the next reset.

### Many boots with power loss

```lean
theorem boots_safe (tr : Trace) (htr : tr.Admissible) :
    ∀ b ∈ tr.boots, ∀ e m, b.result = .jumped e m →
      AcceptedImage (tr.flashAt b) (tr.efuseAt b) e m
```

A `Trace` interleaves bootloader runs, application writes to flash, and
power losses. A bootloader run can stop at any instruction. A power loss
during a flash erase or write leaves the affected bytes undefined. The
availability and rollback theorems are stated over the same traces. The
availability theorem restricts the application to the update protocol,
because an application that erases both slots makes any device unbootable.
The other theorems allow arbitrary application writes.

### Trust-root monotonicity

The process that produces new trust roots is in
[Trust-root rotation](#trust-root-rotation).

```lean
theorem trust_root_monotone (tr : Trace) (htr : tr.Admissible) :
    tr.efuseMonotone ∧
    ∀ b ∈ tr.boots, ∀ r, b.trustRoot = some r →
      r.epoch ≥ epochOf (tr.efuseAt b) ∧
      ThresholdSigned 2 r (unrevokedKeys (tr.efuseAt b))
```

`efuseMonotone` says that no eFuse bit changes from 1 to 0 on any trace, so
the epoch, the revocation set, and the security version never decrease.
`ThresholdSigned 2 r ks` says that at least two distinct keys in `ks` signed
`r`. The bootloader verifies every image with the trust root stored in the
same slot, so this theorem and `boots_safe` together say that every image
the device runs passed checks against a trust root that two unrevoked keys
signed, at the current epoch or later.

### Authenticity and transparency

These are computational theorems, stated as games in VCVio. The adversary
can do the following:

- Get Fulcio certificates for any identity except the release workflow.
- Ask the release workflow to sign images of its choice. This is stronger
  than reality, where the workflow signs only honest builds.
- Submit any entry to Rekor, and get a TSA timestamp on any bytes.
- Steal any signing key after its certificate expires.
- Steal every trust-root key that eFuse has revoked, and at most one other
  trust-root key.
- Steal any Sigstore key (a Fulcio intermediate, a log key, or a TSA key)
  that appears only in trust roots whose epoch is below the device's eFuse
  epoch.
- Ask the trust-root key holders to sign trust roots. Honest holders sign
  only trust roots that list honest Sigstore keys.
- Choose all flash contents and every application action between boots.

The adversary wins the authenticity game if a device boots an image that the
release workflow never signed:

```text
Adv_auth(A) ≤ 4 · Adv_EUF-CMA[Ed25519](trust-root keys)
            + k_F · Adv_EUF-CMA[ECDSA P-384](Fulcio intermediates)
            + q · Adv_EUF-CMA[ECDSA P-256](leaf keys)
            + k_T · Adv_EUF-CMA[ECDSA P-384](TSA keys)
            + Adv_CR[SHA-256] + Adv_CR[SHA-384]
```

In this bound, `q` is the number of releases. `k_F` and `k_T` are the
numbers of Fulcio intermediates and TSA keys listed in honest trust roots at
or above the device's epoch. The TSA term matters because of key theft after
expiry. Without a trusted signed time inside the certificate's validity
window, a stolen ephemeral key could sign forever.

The adversary wins the transparency game if a device boots an image whose
entry isn't in a log that a trusted checkpoint commits to. That advantage is
at most the trust-root term, plus the Ed25519 forgery advantage against each
log key listed in honest trust roots at or above the device's epoch, plus the
SHA-256 collision advantage.

The game makes revocation a theorem. Keys that the adversary steals after a
device burns a higher epoch don't appear in the bound.

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
| Hook contracts: ROM flash read, SHA accelerator, and the cryptographic routines | 500 to 1,500 lines | Test vectors and hardware runs. Software routines can be discharged by later proofs |
| Formats: image header, trust-root blob, device bundle container | 500 to 1,000 lines | Differential tests against the host encoder |
| X.509 and CMS subsets, Rekor v2 entry and checkpoint, RFC 6962 hashing | 2,000 to 5,000 lines | Executable Lean decoders tested against sigstore-go and OpenSSL on a corpus of real bundles |
| Identity policy, acceptance function, boot state machine | 1,000 to 2,000 lines | Human review, non-vacuity proofs, mutation proofs |
| Security games and assumptions | 1,000 to 2,000 lines | Human review against the literature |
| Image extraction tool and build scripts | Tool code | The proof checks extracted bytes against the image digest. Only symbol names are trusted |
| Lean kernel and comparator | Not ours | Standard |

These are estimates. The total is 8,000 to 18,000 lines, compared with about
26,000 trusted lines for libsignal.

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
  boot.
- **Flash reads.** The bootloader reads flash through a ROM function. That
  function is a hook whose contract copies bytes from the flash model into a
  RAM buffer. This keeps the SPI controller and the cache out of the model.
- **eFuse.** An array of bits that can only change from 0 to 1. Reads and
  program operations go through the eFuse controller's registers, modeled at
  the register level. Because bits only get set, every counter is unary, and
  its value is the number of set bits. That is how ESP-IDF reads the 16-bit
  `SECURE_VERSION` field.
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
subroutine meets a hook contract. A later campaign uses the same mechanism to
prove that the real P-256, P-384, and Ed25519 code meets its contract. After
that, the only hooks left are the ROM functions and the SHA accelerator,
which can't be verified.

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
| Boot-state record | Reading picks the newest valid copy. Writing preserves at least one valid copy at every instruction |
| Trust root | The blob parser agrees with the Lean decoder. The signature count includes only distinct, unrevoked keys. The epoch comparison uses the eFuse value |
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
| `crypto` | P-256, P-384, Ed25519, SHA-384, and SHA-512, each behind one function that takes byte slices and returns a result | Hooks with contracts. A later phase can prove the real code |
| `bootloader` | Reset entry, ROM flash reads, the SHA accelerator driver, eFuse reads and burns, the register lock, MMU mapping, the boot-state record, and the jump | Machine-level contracts against the platform model |

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
  names, and on every hooked routine.
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
  - A trust root accepted with one signature, or with the same key counted
    twice
  - A signature from a revoked trust-root key counted
  - The trust-root epoch read from flash instead of eFuse
  - A trust root from one slot used to verify the image in the other slot
  - An epoch or revocation burned before the application confirmed the image
  - The eFuse controller left unlocked at the jump
  - A counter compared as a binary number instead of a count of set bits
  - The eFuse security version not checked
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
| Verified instructions | About 140,000 AArch64 | 5,000 to 20,000 RV32, excluding hooked cryptography |
| Trusted specification and semantics | About 26,000 lines | 8,000 to 18,000 lines |
| Binary proof lines | About 5.3 million | Several hundred thousand to about one million, if lines per instruction are similar |
| Allocator proof | About 70,000 lines | None, because there is no heap |
| Security proof | About 1.2 million lines across two models | Much smaller. One computational model with short reductions |
| New trusted models | AArch64 and Linux process | RV32, bare-metal platform, NOR flash with power loss, eFuse |

The proof-line estimate scales libsignal's ratio of about 38 lines per
instruction. RISC-V instructions are simpler, but RV32 code has more
instructions per operation, so the ratio is a rough guide. Phase 5
measures it.

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
- The agent setup must be built from scratch.

### Risks

| Risk | Effect | Mitigation | Fallback |
| --- | --- | --- | --- |
| Agent setup underperforms | Slow proof throughput | Pilot in phase 5 before committing to the full scope | Narrow the scope to the parsers and policy at the subroutine level |
| Platform model is unsound | Theorems don't hold on silicon | Lockstep tests on hardware, minimal register coverage, flash reads through a ROM hook | Shrink the model by moving more operations behind ROM hooks |
| X.509 or CMS specification is wrong | A theorem about the wrong parser | Differential testing on real bundles, strict profile | Pin more fields by exact byte match, which shortens the specification |
| CMS is too large to specify well | Delays the CMS contracts in phase 6 | Profile pinned to the Sigstore TSA's exact token shape | Use Rekor v1, whose signed entry timestamp gives signed time without CMS, and accept the risk that Rekor v1 is retired |
| Proof repair after every rebuild | Lost work | Freeze the bootloader early, keep contracts at `#[inline(never)]` boundaries | Accept repair as a campaign cost |
| The C3 can't lock the eFuse controller against code running in machine mode | A malicious application can burn counters or revocations and permanently block updates | Confirm in phase 0 which protection unit (the permission-control unit or the CPU's PMP) can lock those registers until reset | Write-protect the counter fields once, and accept that a malicious application can block updates |
| eFuse bits run out | No more security bumps or revocations | Bump the security version and the epoch only for security fixes and revocations, never for routine releases or routine Sigstore rotations | Reserve more `USER_DATA` bits for the epoch counter |
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
freezes the code. Phases 6 through 8 prove the frozen code.

| Phase | Track | Starts after |
| --- | --- | --- |
| 0. Design and feasibility probes | Both | Approval of this plan |
| 1. Verifier code, host first | Implementation | Phase 0 |
| 2. Bootloader and pipelines on hardware | Implementation | Phase 1 |
| 3. Specification | Verification | Phase 0, and the corpus from phase 1 |
| 4. Machine model and proof tooling | Verification | Phase 0 |
| 5. Pilot proofs and code freeze | Both | Phases 2, 3, and 4 |
| 6. Function contracts | Verification | Phase 5 |
| 7. Headline theorems | Verification | Phase 6 |
| 8. Mutation proofs and release | Both | Phase 7 |
| 9. Cryptography proofs (optional) | Verification | Phase 8 |

Each phase ends with exit criteria. A phase that misses them stops the
project or changes its scope before more work goes in.

### Phase 0: design and feasibility probes

Deliverables:

- `c3-boot/docs/formats.md`, a byte-exact definition of the image header,
  the device bundle container, the trust-root blob, the boot-state record,
  and the eFuse bit layout.
- A spike bootloader on a development board that reads one slot, runs one
  check of each signature scheme with the candidate crypto crates, and
  jumps.
- Measurements from the spike: code size per crate, cycles per signature
  check, total boot time, and SRAM use.
- A hardware test of which protection unit can lock the eFuse controller
  against machine-mode writes until reset.
- A prototype of `rv32-img2lean` that turns the spike image into Lean data
  and checks the image digest.
- Lint configuration for the rules in
  [Writing the Rust for verification](#writing-the-rust-for-verification).

Exit criteria:

- The bootloader fits the chosen flash and SRAM layout.
- Boot time with six signature checks per slot is within a budget you set
  in this phase.
- The eFuse lock works, or the fallback in the risk table is accepted.
- The extracted Lean data hashes to the image digest.

### Phase 1: verifier code, host first

Deliverables:

- The `verify` crate with every check, built and tested on the host.
- The `crypto` crate with the hook interface.
- `c3-ota`, a host command-line tool with these subcommands:
  - `pack` builds a signed-image header and segment table.
  - `transcode` turns a Sigstore bundle into the device container.
  - `blob build`, `blob sign`, and `blob verify` handle trust-root blobs.
  - `verify` runs the host build of `verify` on a slot.
- A corpus in `c3-boot/testdata/`: real bundles signed by GitHub Actions,
  mutated bundles, and each one's expected verdict from sigstore-go.
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

### Phase 2: bootloader and pipelines on hardware

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
- A hardware test rig: development boards, a relay that cuts power, and a
  script that runs these scenarios end to end:
  - A normal update, and updates with a bad signature, the wrong identity, a
    stale timestamp, and a lower security version
  - A rotation to a new Rekor log key, an epoch bump, and a trust-root key
    revocation
  - Power cuts at random points during an update write, a boot-state write,
    and an eFuse burn
- A private Sigstore stack (Fulcio, Rekor v2, and a TSA, from
  `sigstore/scaffolding`) for the rotation tests, because the rig must
  rotate keys on demand.

Exit criteria:

- Every scenario passes on hardware.
- A power-cut soak run leaves every board bootable.
- The image is tagged `v0`, the input to the verification pilot.

### Phase 3: specification

Deliverables:

- The trusted `Spec/` modules in Lean, all executable: formats, the X.509
  and CMS subsets, Rekor v2, the trust root, the identity policy, `accept`,
  the boot state machine, the platform assumptions, and the security games.
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
  probe, and compares the final states.
- The core of the proof library ported to RV32: weakest-precondition rules
  for each instruction, separation logic, and symbolic execution.
- Gatekeeper scripts: comparator configuration, the axiom audit, and a check
  that trusted files never import untrusted files.
- Agent skills for each role in
  [Running the proof campaigns](#running-the-proof-campaigns), under
  `.cursor/skills/`.

Exit criteria:

- Lockstep runs agree on every corpus input.
- The equivalence proof covers every opcode in the `v0` image.
- The gatekeeper rejects a planted `sorry` and a planted edit to the
  specification.

### Phase 5: pilot proofs and code freeze

Deliverables:

- Machine-level contract proofs for the image header parser and the Merkle
  inclusion check in `v0`.
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
- `v1` passes every phase 2 scenario.

### Phase 6: function contracts

Deliverables:

- Gatekept contract proofs for every function reachable from reset in `v1`,
  in the groups from [Proof decomposition](#proof-decomposition), in this
  order: byte helpers, container and header, trust root, Rekor v2, X.509 and
  policy, CMS, boot-state record, and eFuse, lock, and MMU.

Exit criteria:

- Every function reachable from reset has a contract proof or is a hook.

### Phase 7: headline theorems

Deliverables:

- `boot_refines`
- `boots_safe`, `trust_root_monotone`, rollback, and availability
- The authenticity and transparency games, connected to `boot_refines`

Exit criteria:

- Comparator confirms every headline theorem against the held-out
  specification.
- The axiom audit is clean.

### Phase 8: mutation proofs and release

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

### Phase 9: cryptography proofs (optional)

Deliverables:

- Proofs that the real P-256, P-384, and Ed25519 code in `v1` meets its hook
  contracts, against Lean specifications of FIPS 186-5, RFC 8032, and
  FIPS 180-4.

After this phase, the only hooks left are the ROM functions and the SHA
accelerator.

## Repository layout

The repository has no Lean code. These directories are proposals:

- `c3-boot/`, a Cargo workspace with the `verify`, `crypto`, `bootloader`,
  and `c3-ota` crates and the demo application. The repository forbids a
  repository-root workspace and imports between top-level apps, so all the
  crates live under one top-level directory. Like `inkbot-esp32/`, it must
  be excluded from `test.yml` Rust discovery, and `c3-boot.yml` builds and
  tests it instead.
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
2. **Bootloader.** The verified code.
3. **Trust-root blob.** Stored in each slot next to the image, and signed by
   two of four offline Ed25519 trust-root keys whose public halves are
   compiled into the bootloader.
4. **Sigstore bundle.** Shipped with each image.
5. **Firmware image.** Untrusted until the checks pass.

The RSA-3072 key and the four Ed25519 trust-root keys are long-lived and stay
offline. Routine releases use only the workflow's Sigstore identity.

### Trust-root rotation

The public Rekor v2 instance starts a new log shard with a new key about
every six months, and the Fulcio intermediate certificate expires in October
2031. A trust root compiled into the bootloader would go stale, so it lives
in a signed blob that ships with each image.

#### Blob contents

- A format version and a sequence number, for ordering and audit.
- An epoch. The bootloader rejects a blob whose epoch is below the epoch
  counter in eFuse.
- The Fulcio intermediates, Rekor v2 log keys with log IDs, and TSA signing
  certificates to accept, each with a validity window. A blob keeps the keys
  of inactive Rekor shards, as Sigstore's `trusted_root.json` file does, so
  that images logged before a shard change still verify.
- The identity policy.
- The indexes of trust-root keys for the bootloader to mark revoked in
  eFuse.
- Two or more Ed25519 signatures, each tagged with the index of the
  trust-root key that made it.

#### Where blobs live and when they take effect

Each slot holds its image, its bundle, and its blob, and the bootloader
verifies a slot's image only with that slot's blob. The application writes
all three to the inactive slot, so a new trust root becomes active in the
same step as the image that needs it, and a power loss during the write
leaves the old slot untouched. A bad blob fails only its own slot, and the
bootloader falls back to the other slot.

A rotation therefore needs no extra steps on the device. When CI starts
logging to a new Rekor shard, the next release carries a blob that lists the
new shard's key, and the blob's signatures don't depend on Sigstore at all.

#### Epochs and eFuse budget

Most rotations add keys and don't need rollback protection, because an
older blob is still trustworthy. Those rotations keep the same epoch, so the
older slot keeps booting. The key holders raise the epoch only to drop a key
that might be compromised, or to tighten the identity policy. After the
application confirms an image whose blob has a higher epoch or new
revocations, the bootloader burns them on the next boot. From then on, every
blob below the new epoch fails, including the one in the other slot.

The counters are unary, so each one has a fixed budget of bumps:

| Counter | eFuse location | Bumps |
| --- | --- | --- |
| Image security version | `SECURE_VERSION`, 16 bits in block 0 | 16 |
| Trust-root epoch | 64 bits of `USER_DATA` in block 3 | 64 |
| Trust-root key revocations | 4 bits of `USER_DATA` in block 3 | One per key |

`USER_DATA` has 256 bits. ESP-IDF uses bits 200 through 247 for an optional
custom MAC address, so the layout stays clear of them.

#### Revoking and replacing trust-root keys

The two-of-four threshold means one stolen trust-root key can't sign a blob.
It also means a stolen key can't revoke the others, because a revocation
must arrive in a blob that two unrevoked keys signed. The device tolerates up
to two revoked keys and still meets the threshold. Replacing the four
compiled-in keys requires a new bootloader signed with the RSA-3072 key and
written over USB. This plan doesn't include in-field bootloader updates.

#### Rotation process off the device

1. A scheduled CI job fetches Sigstore's `trusted_root.json` file with a TUF
   client and compares it with the newest blob in the repository.
2. When they differ, the job builds a candidate blob with a deterministic
   encoder and opens a pull request that shows the old and new keys side by
   side.
3. Two key holders review the pull request and sign the candidate offline,
   each on a hardware token, and commit the signatures.
4. CI checks the signed blob with a host build of the bootloader's verifier
   and with the executable Lean decoder, then merges it.
5. The release workflow attaches the newest signed blob to every release.

None of these steps runs on the device, so the machine-code proof doesn't
cover them. The proof shows that a device trusts exactly what two unrevoked
trust-root keys signed. Whether a signed blob lists the right Sigstore keys
depends on the key holders' review and the CI checks. A blob with a wrong
key makes devices reject new images. It can't make them accept a forged
image unless two key holders signed a blob that lists an attacker's key.

Sigstore lists a new key in `trusted_root.json` before clients sign with it.
The Rekor v2 key had a validity start of 2025-09-23, while the signing
configuration still listed only Rekor v1. That gap gives the key holders time
to sign a blob before the first release that needs it.

### Release identity policy

The bootloader accepts a Fulcio leaf only if these extensions match exactly:

| Fulcio extension | Required value |
| --- | --- |
| Issuer (V2), `1.3.6.1.4.1.57264.1.8` | `https://token.actions.githubusercontent.com` |
| Build Signer URI, `1.3.6.1.4.1.57264.1.9` | `https://github.com/OWNER/REPO/.github/workflows/release.yml@refs/heads/main` |
| Source Repository Identifier, `1.3.6.1.4.1.57264.1.15` | The repository's numeric ID |
| Source Repository Owner Identifier, `1.3.6.1.4.1.57264.1.17` | The owner's numeric ID |
| Build Trigger, `1.3.6.1.4.1.57264.1.20` | `push` |

Replace the following:

- `OWNER/REPO`: the GitHub repository that publishes firmware.
- `release.yml`: the workflow file that signs releases. If signing moves into
  a reusable workflow, name that file.

### Bundle profile

- `hashedrekord` entries only, with an ECDSA P-256 leaf key over SHA-256.
- The leaf chains to the pinned intermediate (ECDSA P-384 with SHA-384).
- A Rekor v2 inclusion proof and a checkpoint signed with Ed25519.
- An RFC 3161 token from the Sigstore TSA, signed with ECDSA P-384 and
  SHA-384. Rekor v2 entries have no signed time, so the TSA token is the
  only signed time, and it must fall inside every validity window.
- No check of the leaf's embedded SCT.

Each slot check runs six software signature checks. Three are Ed25519
checks, two on the trust-root blob and one on the checkpoint. Two are P-384
checks, on the leaf certificate and the TSA token. One is a P-256 check, on
the image signature.

CI transcodes the protobuf JSON bundle into a fixed binary container that
holds the same signed byte strings. The bootloader still produces one JSON
document. A Rekor v2 leaf is the RFC 6962 leaf hash of the RFC 8785
canonical JSON form of the `hashedrekord` entry, which the bootloader
rebuilds from bundle fields, as `ToEntryHash` in rekor-tiles does.

### Image format and boot procedure

The signed image is a header (magic, chip ID, security version, segment
table, entry point) followed by segments. The security version is compared
with the count of set bits in `SECURE_VERSION`, so a product line gets 16
security bumps in total. The bootloader rejects
overlapping segments, segments that overlap its own memory, segments outside
the allowed regions, and length mismatches.

The bootloader reads a two-copy boot-state record and chooses a slot. It
verifies the slot's trust-root blob, parses the header, hashes the image,
checks the Rekor entry and checkpoint, checks the certificate and policy,
checks the image signature, checks the timestamp, and checks the security
version. It then burns any pending eFuse updates, locks the eFuse
controller, maps the image, and jumps. If a check fails, it tries the other
slot. If both fail, it halts.

A trial image boots a fixed number of times. If the application doesn't
confirm it, the bootloader reverts. After confirmation, the next boot burns
the image's security version and its blob's epoch and revocations.

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
