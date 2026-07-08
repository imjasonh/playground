# ast-remote — protocol-compressed git remote helper

**Question:** if we parse source with tree-sitter, store/transmit a compact
protocol form instead of raw text, and rehydrate human-readable source on
fetch, do we win on storage or latency?

**Short answer:** a *full* AST dump is a clear loss (often 5–20× gzip). The
protocol uses in-place atom substitution + raw flate and lands slightly
*under* plain `gzip(source)` (~98% on `testdata/corpus`). A fixed
**per-language zlib dictionary** (no corpus training) does a bit better still
(~96%). The remote helper stores the adaptive min of those candidates so it
never loses to gzip on size. Encode latency is still dominated by parsing.

This directory is a working experiment: `git-remote-ast` plus `ast-remote bench`.

## Design

```
┌─────────────┐   push (git-remote-ast)   ┌──────────────────────┐
│  local git  │ ───────────────────────► │  ast::/path/store    │
│  (normal    │   source blobs →         │  objects keyed by    │
│   OIDs)     │   protocol / lang-dict   │  original git OID    │
│             │ ◄─────────────────────── │  refs/heads/...      │
└─────────────┘   fetch: rehydrate       └──────────────────────┘
                  → exact original bytes
                  → same OID via hash-object
```

### Codec (`internal/codec`)

Lossless payloads. The protocol walks the parse tree's leaves and substitutes
known multi-byte tokens (keywords, operators, common idents) with 2-byte
atoms, preserving layout so deflate still sees source-like structure.

| Encoding | What is stored | Typical size vs gzip(raw) |
|----------|----------------|---------------------------|
| `ast` | protocol payload + raw flate | ~98% |
| `raw-dict` | flate(source, fixed language dictionary) | ~95–97% |
| `ast-dict` | flate(protocol, language dictionary) | ~96–98% |
| `raw` | gzip(source) | 100% (baseline / fallback) |

Whitespace and comments between tokens stay in the substituted byte stream, so
round-trips are byte-exact.

`EncodeFile` adaptively stores `min(protocol+flate, raw-dict, ast-dict, gzip(raw))`.

Unsupported extensions, parse errors, and non-blobs always use gzip(raw).

### How we closed the gap

Packing experiments showed:

1. **String-table interning hurts gzip** — uint32 IDs add entropy gzip cannot
   reuse as well as raw token text.
2. **Interleaved atom streams** (~123%) beat tables but still lose.
3. **In-place substitution** (keep source layout; shrink only long tokens)
   brings the protocol+deflate to ~parity with gzip.
4. **Drop gzip headers** (raw flate) and shrink the frame → ~98%.
5. **Fixed language dictionaries** (keywords + idioms, not corpus-trained)
   beat gzip by ~4% on Go; adaptive storage picks them when smaller.

### Remote helper (`git-remote-ast`)

Implements the [git remote helper](https://git-scm.com/docs/gitremote-helpers)
protocol (`capabilities`, `list`, `fetch`, `push`). URL form:

```
ast::/absolute/or/relative/path/to/store
```

Objects stay keyed by the **original git OID**. On fetch the helper decodes to
the original bytes and `git hash-object -w` them, so history is unchanged.

### Why not rewrite OIDs?

Content-addressed protocol objects would break every commit hash. Keeping
original OIDs means the remote is a compressed *transport/store*, not a new
object model.

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
./ast-remote encode -no-adaptive testdata/corpus/repetitive.go
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
# Per-file size / encode latency vs gzip
./ast-remote bench -out bench-results.json testdata/corpus

# Full git clone wall time: protocol remote vs local git-daemon
./ast-remote bench-remote -out bench-remote.json -repeat 5 -commits 5 testdata/corpus
```

`bench-remote` builds a multi-commit repo from the given tree, publishes once
to both remotes, then times **full `git clone`** end-to-end:

| Side | What runs |
|------|-----------|
| protocol | `git clone ast::/path/store` (helper fetch → rehydrate → `hash-object -w` → checkout) |
| plain | `git clone git://127.0.0.1:<port>/plain.git` served by `git-daemon` from a bare repo |

Both paths include object transfer, local object-store population, reachability
work git does during clone, and worktree checkout. After timing, both clones
are `git fsck --full`'d and their worktrees compared for equality. Setup push
times are reported separately and are not part of the clone ratio.

`file://` clones are intentionally **not** the baseline: same-machine
`file://` can short-circuit via hardlinks/`--local` and skip the network
upload-pack path a real server uses.

Per-file size report columns:

| Metric | Meaning |
|--------|---------|
| raw | original source size |
| gzip | `gzip(source)` baseline (BestCompression) |
| protocol | atom substitution + flate |
| raw+dict | fixed language dictionary + flate |
| stored | adaptive min of candidates |
| encode/decode ms | parse+pack vs inflate+rehydrate |

## Benchmark results (this machine)

### Size (`ast-remote bench`)

| Corpus | raw | gzip | protocol+flate | raw+dict | stored (adaptive) |
|--------|-----|------|----------------|----------|-------------------|
| `testdata/corpus` | 30.7 KB | 2.9 KB | 2.8 KB (**98%** of gzip) | 2.8 KB (**96%**) | **96%** of gzip |

Mean encode on the corpus: protocol is milliseconds-per-file vs sub-millisecond
gzip; decode is near parity.

### Full clone latency (`ast-remote bench-remote`)

Fair comparison on `testdata/corpus` with a 5-commit synthetic history
(30 reachable objects), mean of 5 full clones:

| | protocol `ast::` clone | local `git-daemon` clone | ratio |
|--|------------------------|--------------------------|-------|
| mean wall time | **~49 ms** | **~103 ms** | **0.48×** |

On this small corpus the protocol path is faster: both sides pay for a full
local repo (objects + checkout), and `git-daemon`’s TCP upload-pack overhead
dominates more than protocol rehydrate. Both clones pass `git fsck --full`
and produce identical worktrees. Re-run locally — numbers move with corpus
and CPU; `bench-remote.json` has the latest run.

The JSON `summary.verdict` / `verdict` fields state the outcome for a given run.

## Why gzip is hard to beat (and how we still edged it)

1. A lossless codec must retain every character; the protocol cannot discard tokens.
2. Gzip already finds repeated tokens via its sliding window.
3. Heavy framing (string tables, per-node metadata) adds overhead that only
   pays off on highly repetitive / generated code.
4. **Light** use of the parse tree — tokenizing just enough to substitute known
   multi-byte atoms, then letting deflate cook — preserves gzip-friendly layout
   while shortening the common tokens gzip would otherwise spell out repeatedly.
5. A **shared language prior** (fixed dict) is the remaining win: it is
   knowledge gzip cannot have from a single file alone. That is not “AST
   storage” per se, but it is a fair peer for a language-aware remote that
   already knows the language.

Semantic / format-normalized storage would shrink further — but would change
OIDs and stop being a transparent git remote.

## Layout

```
ast-remote/
├── main.go                 # ast-remote CLI (encode/decode/bench)
├── cmd/git-remote-ast/     # git remote helper binary
├── internal/
│   ├── codec/              # the protocol + dict wrappers
│   ├── langs/              # extension → tree-sitter grammar
│   ├── store/              # filesystem remote object store
│   ├── gitcmd/             # git plumbing wrappers
│   └── helper/             # remote-helper protocol
└── testdata/corpus/        # multi-language fixtures + repetitive.go
```

## Limitations

- Directory remotes only (`ast::/path`); SSH/HTTP would wrap the same store.
- Trees/commits/tags are gzip(raw), not protocol-encoded.
- cgo + bundled grammars → large helper binary.
- Language dictionaries are fixed snapshots; they help most on idiomatic code
  in supported languages (Go dict is the most fleshed out).
- No format-on-rehydrate / lossy semantic mode (would break OID stability).

## See also

The sibling `ast/` app (structural search/rewrite) shares tree-sitter but is
about editing, not transport. This experiment is specifically about
**storage/transport** of source via a parse-derived protocol.
