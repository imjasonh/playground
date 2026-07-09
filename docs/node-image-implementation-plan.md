# Implementation plan: `node-image` v1

Companion to [`node-image-design.md`](./node-image-design.md). This is the
build plan for a working alpha in `node-image/` with thorough CI tests.

## Alpha success bar

One command:

```bash
node-image build ./testdata/ts-app --repo ttl.sh/node-image-demo -t latest
```

- Runs `pnpm install` + `pnpm run build` when `scripts.build` exists
- Hermetically lays out production deps from `pnpm-lock.yaml` (no dep scripts)
- Pushes a **multi-arch** index (`linux/amd64` + `linux/arm64`)
- Second build after a one-line app edit uploads ≪ full deps
- Bumping one dep changes ~one store layer
- `go test ./...` green in CI; layout conformance vs
  `pnpm install --ignore-scripts --prod` on fixtures
- Image path does **not** copy host `node_modules` into layers

## Alpha defaults (locked from design §11)

| Topic | Default |
|-------|---------|
| Lockfile | pnpm-lock **v9 only** |
| Patches / git / exotic resolutions | **Fail if present** |
| Scripts on image deps | **Never**; fail if non-optional dep needs install scripts without prebuilds |
| Layout | Match pnpm virtual store closely enough for oracle tests |
| Config | `"node-image"` key in `package.json` |
| Base | `gcr.io/distroless/nodejs22-debian12` (glibc); allow override; warn on floating tags |
| Entrypoint | `node` + `package.json#main` (overridable) |
| Layer budget | 127 including base; `auto` name-hash buckets when over |
| libc | glibc; loud fail on musl-only needs |

## Milestones

### M0 — Skeleton (this PR start)

- [x] `node-image/` Go module (`github.com/imjasonh/playground/node-image`)
- [x] `README.md`, `.gitignore`, `main.go` CLI stub (`build` subcommand)
- [x] `go build ./...` and `go test ./...` pass
- [x] Discovered automatically by existing `test.yml` via `go.mod`

### M1 — Deterministic layers

- [x] `internal/layer`: normalized tar (epoch mtime, uid/gid 0, sorted entries,
      stable gzip)
- [x] Unit tests: same input → same diffID / compressed digest

### M2 — Lock parse + resolve

- [x] `internal/lock`: parse pnpm-lock.yaml v9
- [x] `internal/resolve`: production closure for an importer path + platform
- [x] Reject unsupported lock versions, patches, git/file exotics
- [x] Fixture locks in `testdata/` (pure JS; TS app)

### M3 — Fetch + layout (Go-native install)

- [x] `internal/fetch`: download by URL, verify SRI, cache
- [x] `internal/layout`: extract + symlinks + bins + scripts policy
- [x] Conformance tests vs `pnpm install --ignore-scripts --prod`

### M4 — Image assemble + push

- [x] `internal/publish`: append layers; `--no-push` digest summary; push helper
- [x] Config from `package.json#node-image` + flags
- [ ] Full OCI layout export; base Node/libc detection polish

### M5 — App compile phase

- [x] `pnpm install` + `pnpm run build` when script present
- [x] Testdata TypeScript app fixture + CI test

### M6 — Multi-arch

- [ ] Per-platform closure sharing pure-JS digests in an OCI index
- [x] Per-platform resolve/layout path exists (push still single-arch with warning)

### M7 — Polish for usable v1

- [ ] Loud errors polish; layer auto-bucketing; README quickstart polish
- [x] CI installs pnpm when testing `node-image`

## Package layout

```
node-image/
├── go.mod
├── go.sum
├── README.md
├── .gitignore
├── main.go                 # cobra/flag CLI → build
├── internal/
│   ├── config/             # package.json + flags
│   ├── lock/
│   ├── resolve/
│   ├── fetch/
│   ├── layout/
│   ├── layer/
│   ├── app/                # compile phase + app layer files
│   ├── base/
│   └── publish/
└── testdata/
    ├── pure-js/            # ms or similar tiny dep
    ├── with-platform-opt/  # optional @esbuild/linux-* style (or stub)
    └── ts-app/             # typescript + build script
```

## Testing strategy

| Layer | What |
|-------|------|
| Unit | lock parse, resolve, tar determinism, SRI verify, bin/symlink writers |
| Conformance | layout vs pnpm oracle on fixtures (requires network + pnpm in CI) |
| Integration | `--no-push` OCI layout; multi-arch index structure; layer digest stability across two runs |
| Manual / e2e (optional in CI) | push to ttl.sh when `NODE_IMAGE_E2E=1` |

CI: existing Go discovery runs `go build ./...` and `go test ./...`. Conformance
tests that need pnpm/network should use build tags or detect tools:

- Default `go test ./...` runs offline unit tests always
- `go test ./... -tags=conformance` (or tests that skip without pnpm) for
  oracle + fetch tests

Prefer **auto-skip with `t.Skip`** when pnpm/network unavailable so local
`go test` stays green, and ensure GitHub Actions has Node/pnpm available when
testing this module (extend `test-go-modules.sh` or add a step that installs
pnpm when `node-image` is in `MODULES`).

## Implementation order (coding)

1. Plan doc + module skeleton + CLI stub + empty tests (**start here**)
2. `internal/layer` determinism
3. `internal/lock` + `resolve` + fixtures
4. `internal/fetch` + `layout` + conformance
5. `internal/publish` + `--no-push`
6. Wire `build` end-to-end on `testdata/pure-js`
7. App compile + `testdata/ts-app`
8. Multi-arch index
9. CI pnpm for conformance; README; design status bump

## Out of scope for this v1 track

- npm/yarn locks
- `--allow-scripts` for image deps
- musl mode
- Go-native app compile (no pnpm for tsc)
- Full monorepo magic beyond “directory with package.json + parent lock”
- SBOM/cosign (nice-to-have if time)
