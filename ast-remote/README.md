# ast-remote — AST-compressed git remote helper

**Question:** if we parse source into a tree-sitter AST, store/transmit that
instead of raw text, and rehydrate human-readable source on fetch, do we win
on storage or latency?

**Short answer:** a *full* AST is a clear loss (often 5–20× gzip). A
**leaf-stream** derived from the AST (token texts + trivia gaps, string-table
interned, then gzipped) is much closer, but on normal code still loses to
`gzip(source)`. Encode latency is dominated by parsing. The remote helper
therefore stores `min(leaf-AST+gzip, gzip(raw))` per blob so it never does
worse than plain gzip on size.

This directory is a working experiment: `git-remote-ast` plus `ast-remote bench`.

## Design

```
┌─────────────┐   push (git-remote-ast)   ┌──────────────────────┐
│  local git  │ ───────────────────────► │  ast::/path/store    │
│  (normal    │   source blobs →         │  objects keyed by    │
│   OIDs)     │   tree-sitter leaf       │  original git OID    │
│             │   stream + gzip          │  refs/heads/...      │
│             │ ◄─────────────────────── │                      │
└─────────────┘   fetch: rehydrate       └──────────────────────┘
                  → exact original bytes
                  → same OID via hash-object
```

### Codec (`internal/codec`)

Lossless `AST1` payloads, two modes:

| Mode | What is stored | Typical size vs gzip(raw) |
|------|----------------|---------------------------|
| `leaves` (default) | ordered leaf texts + trivia gaps, interned string table | ~1–3× (sometimes near parity on repetitive code) |
| `full-tree` | every AST node (type/field/children) + gaps | often 5–20× |

Whitespace/comments between tokens are explicit **trivia gaps** so round-trips
are byte-exact (tree-sitter trees omit most whitespace).

`EncodeFile` adaptively stores gzip(raw) when it is smaller than the AST form.

Unsupported extensions, parse errors, and non-blobs always use gzip(raw).

### Remote helper (`git-remote-ast`)

Implements the [git remote helper](https://git-scm.com/docs/gitremote-helpers)
protocol (`capabilities`, `list`, `fetch`, `push`). URL form:

```
ast::/absolute/or/relative/path/to/store
```

Objects stay keyed by the **original git OID**. On fetch the helper decodes to
the original bytes and `git hash-object -w` them, so history is unchanged.

### Why not rewrite OIDs?

Content-addressed AST objects would break every commit hash. Keeping original
OIDs means the remote is a compressed *transport/store*, not a new object model.

## Build

Requires Go 1.22+ and a C compiler (cgo / tree-sitter):

```bash
cd ast-remote
go build -o ast-remote .
go build -o git-remote-ast ./cmd/git-remote-ast
go test ./...
```

Put `git-remote-ast` on your `PATH`.

## Usage

### Encode one file

```bash
./ast-remote encode testdata/corpus/sample.go
./ast-remote encode -no-adaptive -full-tree testdata/corpus/repetitive.go
```

### End-to-end push / fetch

```bash
go build -o "$HOME/bin/git-remote-ast" ./cmd/git-remote-ast

git remote add astremote "ast::/tmp/my-ast-store"
git push astremote main

git clone "ast::/tmp/my-ast-store" recovered
```

### Benchmarks

```bash
./ast-remote bench -out bench-results.json testdata/corpus
./ast-remote bench -repeat 5 -out /tmp/bench.json ../gitdb
```

Per file and in aggregate the report compares:

| Metric | Meaning |
|--------|---------|
| raw | original source size |
| gzip | `gzip(source)` baseline |
| leaf+gzip | default AST-derived leaf stream |
| full+gzip | full flattened tree (experimental) |
| stored | adaptive `min(leaf, gzip)` |
| encode/decode ms | parse+pack vs inflate+rehydrate |

## Benchmark results (this machine)

### Size (`ast-remote bench`)

| Corpus | raw | gzip | leaf+gzip | full+gzip | stored (adaptive) |
|--------|-----|------|-----------|-----------|-------------------|
| `testdata/corpus` | 30.7 KB | 2.9 KB | 5.3 KB (183% of gzip) | 47.7 KB (1654%) | = gzip |
| `gitdb/` (16 Go files) | 83.6 KB | 30.5 KB | 48.7 KB (160% of gzip) | 159 KB (523%) | = gzip |

Mean encode on `gitdb/`: AST **7.2 ms** vs gzip **0.5 ms**. Decode is near parity.

### Push/fetch latency (`ast-remote bench-remote`)

Against a local `file://` bare remote on the same corpus:

| | AST remote | file:// | ratio |
|--|------------|---------|-------|
| push | ~48 ms | ~13 ms | ~3.6× |
| clone/fetch | ~19 ms | ~14 ms | ~1.4× |

Re-run locally — numbers move with corpus and CPU — but the shape is stable:
full trees lose badly, leaf streams still usually lose to gzip, adaptive storage
matches gzip on size, and push pays for parse time.

The JSON `summary.verdict` states the outcome for a given tree.

## Why gzip usually wins

1. A lossless codec must retain every character; the AST cannot discard tokens.
2. Gzip already finds repeated tokens via its sliding window.
3. AST framing adds string-table headers and per-leaf IDs; that overhead only
   pays off when interning beats gzip across a whole file (rare outside
   generated / highly repetitive code).
4. If the goal is *semantic* storage (drop formatting, normalize), sizes drop —
   but that is no longer a transparent git remote (OIDs change).

## Layout

```
ast-remote/
├── main.go                 # ast-remote CLI (encode/decode/bench)
├── cmd/git-remote-ast/     # git remote helper binary
├── internal/
│   ├── codec/              # AST1 encode/decode (leaves + full-tree)
│   ├── langs/              # extension → tree-sitter grammar
│   ├── store/              # filesystem remote object store
│   ├── gitcmd/             # git plumbing wrappers
│   └── helper/             # remote-helper protocol
└── testdata/corpus/        # multi-language fixtures + repetitive.go
```

## Limitations

- Directory remotes only (`ast::/path`); SSH/HTTP would wrap the same store.
- Trees/commits/tags are gzip(raw), not AST-encoded.
- cgo + bundled grammars → large helper binary.
- No format-on-rehydrate / lossy semantic mode (would break OID stability).

## See also

The sibling `ast/` app (structural search/rewrite) shares tree-sitter but is
about editing, not transport. This experiment is specifically about
**storage/transport** of source via ASTs.
