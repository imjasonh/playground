# verified-fw

A small firmware language and compiler written in Lean 4, with a
machine-checked proof that the bytes it writes for the chip do what the source
program says. The targets are the ESP32-C3 (RISC-V) and QEMU's RISC-V `virt`
board.

The language is meant for LLMs to write programs and proofs in. People review
the specs, which are short. The proofs are long, and the Lean kernel checks
them.

## What is proven

For a program `prog` that passes the decidable `Program.wf` check:

- `decode_encode`: the trusted RISC-V decoder inverts the encoder for every
  instruction the compiler emits.
- `compile_correct`: run on the RISC-V model, the compiled code makes exactly
  the device stores that the source semantics `Program.trace` says, never
  faults, and then stops in a loop that changes nothing. Registers and RAM can
  hold anything at reset.
- `codeAt_image`: the image bytes, loaded at the chip's load address, hold the
  compiled code.
- `qemuVirt_correct` and `esp32c3_correct`: the previous three together, from
  the image file to the device stores.
- `counter_on_qemu`: `Examples/Counter.lean` prints
  `verified-fw: 01*23*45*67*89*` on the UART and stops QEMU.
- `blinky_on_esp32c3`: `Examples/Blinky.lean` disables the watchdogs, sets up
  GPIO8, and toggles the LED 4,294,967,295 times, with no other device stores.

`Checks/Axioms.lean` fails the build if any of these theorems depends on
`sorry` or on an axiom other than `propext`, `Classical.choice`, and
`Quot.sound`. That also rules out `native_decide` and `bv_decide`.

## What you have to trust

A proof is only as good as its statement and its models. These files are the
trusted base, and every change to them needs a person to review it:

| File | What it says |
| --- | --- |
| `VerifiedFw/RiscV/Machine.lean` | How each RV32I instruction changes the machine |
| `VerifiedFw/RiscV/Decode.lean` | How 32-bit words decode to instructions |
| `VerifiedFw/Lang/Syntax.lean`, `Lang/Semantics.lean` | What a program means |
| `VerifiedFw/Targets.lean` | Each chip's device addresses, code address, and RAM address |
| `VerifiedFw/Loader.lean` | How image bytes appear in instruction memory |
| Theorem statements in `EndToEnd.lean` and `Examples/*Spec.lean` | The specs |
| `Checks/Axioms.lean`, `lakefile.toml` | The axiom gate and `warningAsError` |

Outside the repository, you trust the Lean kernel, the hardware and QEMU to
match the RISC-V model, the ESP32-C3 boot ROM, and `esptool`. You also trust
the Lean compiler, because `lake exe emit` runs compiled code to write the
bytes that the proofs describe.

Two checks test the trusted models against independent tools:
`scripts/check-images.sh` decodes the encoder's edge cases with GNU `objdump`
and compares the text, then runs the counter image in QEMU and compares its
UART output with the source semantics.

## The language

Version 0 has 32-bit globals that start at zero, expressions (`+`, `-`, `&`,
`|`, `^`, shifts, unsigned `<`), stores to device registers, `if`, and loops
that run a fixed number of times. Every program terminates, so its meaning is
a total function from the program to the list of device stores it makes.
There are no interrupts yet. See [`docs/roadmap.md`](docs/roadmap.md).

Programs are Lean values, so the proofs and the flashed image come from the
same term:

```lean
def counter : Program where
  globals := 1
  body := seqs [
    print "verified-fw: ",
    .loop 10 (seqs [
      .store uartTx (.bin .add (.var 0) (.const 0x30)),
      .ite (.bin .and (.var 0) (.const 1)) (putc '*') .skip,
      .assign 0 (.bin .add (.var 0) (.const 1))]),
    putc '\n',
    .store finisher (.const finishPass)]
```

## Build and check

Install [elan](https://github.com/leanprover/elan). The `lean-toolchain` file
selects Lean 4.35.0, and the project doesn't use Mathlib. Then run the
following:

```bash
cd verified-fw
lake build                      # check every proof and the axiom gate
lake exe emit out               # write the images to out/
bash scripts/check-images.sh    # needs qemu-system-riscv32 and riscv64-unknown-elf-objdump
```

## Run on an ESP32-C3

The image needs an ESP32-C3. The classic ESP32 that `esp32-ble` and
`inkbot-esp32` use has an Xtensa core and doesn't run it. GPIO8 drives the
LED on "ESP32-C3 SuperMini" boards. Espressif's ESP32-C3-DevKitM-1 has an
addressable RGB LED on GPIO8, which this program can't drive.

The image uses the ROM's direct boot, so it goes at flash offset 0 with no
second-stage bootloader:

```bash
esptool.py --chip esp32c3 write_flash 0x0 out/esp32c3-blinky.bin
```

The blinky image hasn't run on hardware yet. If the board resets every few
seconds, a watchdog is still running, and the register values in
`Examples/Blinky.lean` need checking against the ESP32-C3 Technical Reference
Manual. If nothing happens at all, check direct boot's magic word and load
address in `Targets.lean`.
