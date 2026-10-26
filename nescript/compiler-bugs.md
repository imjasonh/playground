// compiler-bugs.md — a running log of compiler issues surfaced
// while implementing the Pong example (examples/pong.ne et al).
//
// Format, one entry per bug:
//
// ## #N — one-line title
//
// **Status**: OPEN / WORKED-AROUND / FIXED
// **Phase**:   lexer / parser / analyzer / ir / optimizer / codegen / linker / runtime / asset
// **Surfaced in**: examples/pong/<file>.ne (brief context)
//
// ### Reproducer
// ```ne
// ... minimal .ne snippet that triggers the bad behaviour ...
// ```
//
// ### Expected vs actual
// What the user-visible behaviour should be; what the compiler actually does.
//
// ### Workaround (if applied)
// The current shape of the code in examples/pong/ that avoids the bug,
// and exactly what should be reverted once the fix lands. Every workaround
// in examples/pong/ MUST be tagged with `// BUG: compiler-bugs.md #N` so
// grep -r "BUG: compiler-bugs.md" finds every reverible workaround in one pass.
//
// ### Guess at the fix
// Which source file(s) and what kind of change is likely needed. Doesn't
// have to be right — it's a hint for the compiler-bug cleanup milestone.
//
// ---

(no bugs logged — the repo is currently clean)
