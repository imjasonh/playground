# ast — future work

This document tracks planned enhancements to `ast`, drawn from a survey of how
LSP and the structural search-and-rewrite ecosystem (ast-grep, Semgrep, Comby,
GritQL, Coccinelle, OpenRewrite, jscodeshift) express selectors and transforms.

Two ideas from that survey are already implemented and are **not** listed here:

- **Normalized `--kind` selectors** (LSP `SymbolKind`-style cross-language
  vocabulary), backed by curated `tags.scm` / `highlights.scm` queries.
- **Scope-aware `rename`** (LSP-style, position- or name-targeted), backed by
  curated `locals.scm` queries and a scope/definition/reference resolver.

Both currently cover `go`, `python`, `javascript`, `typescript`, `tsx`, and
`rust`. **Extending curated queries to more languages** (drop
`queries/<lang>/{tags,highlights,locals}.scm` into `internal/langs/queries`) is
ongoing, low-risk work: no code changes are needed, only new query files and
tests.

## High-impact, larger effort

### 1. Code-shaped patterns with metavariables (deferred)

Today the selector is a raw tree-sitter query (S-expressions). Tools like
**ast-grep** and **Semgrep** instead let users write patterns that *look like
the target language* with metavariables, which is far more approachable:

```
# instead of:
ast query -q '(call_expression function: (identifier) @fn (#eq? @fn "foo"))'
# users could write:
ast query -p 'foo($$$ARGS)'
```

Design sketch:

- Add a `-p/--pattern` flag (alternative to `-q`). Parse the pattern *as code*
  in the target language, then compile its syntax tree into an equivalent
  tree-sitter query:
  - Concrete nodes become node patterns.
  - `$NAME` (a metavariable) becomes a capture `@NAME` matching any single named
    node; repeated `$NAME` in one pattern adds a `#eq?` constraint so both must
    be textually equal.
  - `$$$NAME` (variadic) matches a (possibly empty) sequence of siblings — this
    needs quantifier support and is the trickiest part.
  - Anonymous/"hole" tokens map to wildcards `(_)`.
- Rewrites (`--replace`, etc.) reuse the same metavariable names in templates,
  so `-p 'foo($X)' --replace-pattern 'bar($X)'` works.

Why deferred: robust pattern→query compilation is a real sub-project (metavar
binding, variadics/quantifiers, operator/precedence handling, partial patterns,
and per-language quirks). It should land behind `-p` without disturbing the
existing raw-query path, and warrants its own package (e.g. `internal/pattern`)
with a large cross-language test matrix. Prior art to study: ast-grep's pattern
compiler, Semgrep's generic/`...` matching, and Comby's balanced-hole matching.

## Medium-impact

### 2. Emit/consume an LSP `WorkspaceEdit`-shaped JSON

Decouple *matching* from *applying*, exactly as LSP does (the server returns a
`WorkspaceEdit`; the client applies it):

- `ast rewrite … --edits-json` (and `ast rename … --edits-json`) prints a
  normalized document: per file, a list of `{range, newText}` edits, using both
  byte offsets and LSP `{line, character}` positions (note the UTF-16 caveat for
  the LSP form).
- `ast apply edits.json` consumes that document and writes the files.

This enables review pipelines, batching, and interop with editors/other tools,
and makes `--patch` one of several serialization formats rather than the only
machine output.

### 3. Relational / compositional constraints

Borrow ast-grep/Semgrep rule composition so selection isn't limited to a single
pattern:

- `--inside KIND` / `--inside 'QUERY'` — only match nodes contained in an
  enclosing match (e.g. calls **inside** a function named `test_*`).
- `--has 'QUERY'`, `--not 'QUERY'`, `--follows` / `--precedes`.
- These map onto tree-sitter's own facilities where possible (anchors,
  quantifiers, `#not-…` predicates) and onto post-filtering otherwise.

### 4. Reusable rule files

Turn ad-hoc invocations into shareable "codemods":

- A YAML/JSON rule format: `{id, language, query|pattern, operations, message,
  severity}`, with `ast run rules.yml <files…>` executing a set.
- Enables sharing and versioning transforms, and a `--json` diagnostics stream.

### 5. CI/lint ergonomics

- Exit non-zero from `query` when matches are found (opt-in, e.g. `--error`), so
  `ast` can act as a structural linter in CI.
- Recursive directory walking with include/exclude globs, `.gitignore`
  awareness, and parallel per-file processing.
- A `--count`/summary-only mode.

### 6. Post-edit validation guard

After a rewrite/rename, re-parse the result and warn (or fail with
`--strict`) if the edit introduced new syntax errors. Cheap, high-value safety
net; echoes LSP's `AnnotatedTextEdit` "needs confirmation" intent.

## Notes on the current design worth preserving

- **Byte-splice rewrites are a feature, not a limitation.** Unlike
  AST-reprint tools (jscodeshift/recast), `ast` never reformats code outside the
  edited spans. Any future AST-level rewrite mode should keep a
  formatting-faithful path.
- **Scope-aware rename is intentionally local.** `locals.scm` models lexical
  scopes within a single file; cross-file/semantic rename (LSP `textDocument/
  rename`) needs project-wide binding resolution and is out of scope for a
  syntactic tool. For package-level or imported symbols, `ast rewrite` with an
  `#eq?` predicate remains the right tool.
