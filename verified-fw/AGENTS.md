# Agent guide: verified-fw

A Lean 4 firmware language, compiler, and proofs. Read
[`README.md`](README.md) for what is proven and what is trusted, and
[`docs/roadmap.md`](docs/roadmap.md) for what comes next.

## Contracts

- **Don't weaken a spec to make a proof go through.** The trusted files in the
  README's table and every theorem statement in `EndToEnd.lean` and
  `Examples/*Spec.lean` are the spec. Change them only when the user asks, and
  say so in the PR description. Proofs, the compiler, and `Encode.lean` are
  yours to change.
- **No `sorry`, `native_decide`, `bv_decide`, or new axioms.** `warningAsError`
  turns `sorry` into a build error, and `Checks/Axioms.lean` rejects
  nonstandard axioms. When you add a top-level theorem, add an
  `#assert_standard_axioms` line for it.
- **Keep large loop counts away from the kernel.** A proof that makes the
  kernel reduce `Nat.repeat` on a literal such as `2000000` unfolds it one
  step at a time and times out. Generalize the literal first, or rewrite with
  equation lemmas and lemmas proven for any count. `delay_run` and
  `blinky_trace` in `Examples/BlinkySpec.lean` show both.
- **Hide encoded words from the kernel.** Before you unfold `decode` on an
  encoded instruction, generalize the word to a variable, as
  `decode_encode` does. Otherwise the kernel evaluates `Nat` division on
  symbolic values and times out.
- **`omega` is incomplete for nested `/` and `%`.** For digit extraction,
  use the `digit` lemma in `Encode.lean`, which reduces the goal to linear
  facts.
- **Mark big spec values `noncomputable`.** A closed term such as
  `blinkyEvents` otherwise runs when an executable starts.
- **Keep `scripts/check-images.sh` passing.** It is the only check of the
  trusted decoder and machine model against outside tools.

## Local commands

```bash
cd verified-fw
lake build
lake exe emit out
bash scripts/check-images.sh
```
