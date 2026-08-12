# go-builder

A **Go-only** [Cloud Native Buildpacks](https://buildpacks.io) builder that does
what [`ko`](https://ko.build) does: turn a Go module into a tiny, static
container image without a Dockerfile.

```bash
pack build myapp --builder go-builder:local --path ./cmd/myapp
```

## Why this exists

`ko` is the gold standard for shipping Go as containers: `CGO_ENABLED=0`,
`-trimpath`, a minimal static base, binary at `/ko-app`, `kodata/` →
`$KO_DATA_PATH`, and `.ko.yaml` for build knobs. Most CNB builders are
multi-language and land you on a general-purpose stack.

**go-builder** is the opposite: one language, ko-shaped defaults, and a
[Paketo Jammy Static](https://github.com/paketo-buildpacks/jammy-static-stack)
run image (scratch-like: CA certs + tzdata). If it is not a Go module, detection
fails — by design.

## Quick start

### Tests (no Docker)

```bash
cd go-builder
go test ./...
```

### Create the builder (needs `pack` + Docker)

```bash
cd go-builder
./scripts/create-builder.sh          # → go-builder:local
pack build hello-go \
  --builder go-builder:local \
  --path testdata/hello
docker run --rm hello-go
# → hello from go-builder
```

### kodata (same convention as ko)

```bash
pack build kodata-demo \
  --builder go-builder:local \
  --path testdata/with-kodata
docker run --rm kodata-demo
# → kodata-ok
```

## What the buildpack does

| Step | Behavior |
|------|----------|
| **Detect** | Passes only when `go.mod` exists |
| **Toolchain** | Installs Go matching `toolchain` / `go` in `go.mod` into a cached layer |
| **Compile** | `CGO_ENABLED=0 GOOS=linux go build -trimpath -ldflags="-s -w" -o …/ko-app <main>` |
| **kodata** | Copies `<main>/kodata/` into a launch layer; sets `KO_DATA_PATH` |
| **Launch** | Default process `web` → the `ko-app` binary |
| **Run image** | Paketo `run-jammy-static` (tiny / distroless-like) |

### `.ko.yaml` (subset)

```yaml
defaultBaseImage: cgr.dev/chainguard/static   # noted; builder run image wins
defaultLdflags:
  - -X main.version=dev
builds:
  - id: app
    main: ./cmd/app
    flags: [-tags, netgo]
    env: [FOO=bar]
    ldflags: [-s, -w]
```

### Environment overrides

| Variable | Purpose |
|----------|---------|
| `BP_GO_TARGETS` / `KO_MAIN` | Main package (first of a space-separated list) |
| `BP_GO_BUILD_FLAGS` | Extra `go build` flags |
| `BP_GO_LDFLAGS` / `KO_LDFLAGS` | `-ldflags` value |
| `CGO_ENABLED` | Default `0` |
| `BP_GO_TRIMPATH` | Set `false` to keep file paths |
| `BP_GO_DISABLE_OPTIMIZATIONS` | `true` → `-gcflags=all=-N -l` |
| `KO_BUILD_ID` / `BP_KO_BUILD_ID` | Select a `builds[].id` from `.ko.yaml` |

## Layout

```
go-builder/
├── buildpack.toml      # playground/go buildpack identity
├── builder.toml        # Go-only builder → jammy-static stack
├── package.toml        # pack buildpack package targets
├── cmd/detect          # CNB bin/detect
├── cmd/build           # CNB bin/build
├── internal/           # detect, build, config, kodata, toolchain, cnb
├── scripts/
│   ├── package.sh      # compile bin/detect + bin/build
│   └── create-builder.sh
└── testdata/           # hello, with-kodata, with-ko-yaml
```

## ko parity notes

- **Binary path:** CNB launch layers live under `/layers/…/ko-app` (filename
  `ko-app`). Process `command` is that absolute path. Apps should not hardcode
  `/ko-app/...`; use the process argv / `$PATH` like normal.
- **`KO_DATA_PATH`:** Set at launch to the bundled kodata directory (ko uses
  `/var/run/ko`; we nest `var/run/ko` inside the kodata layer so relative paths
  match).
- **Base image:** Chosen by the builder’s run image, not `.ko.yaml`. The YAML
  field is accepted and logged so existing ko configs don’t break detect/build.
- **Multi-arch:** `builder.toml` declares `linux/amd64` and `linux/arm64`; use
  `pack build --target linux/arm64` (or buildx-style targets your pack supports).

## Non-goals

- Other languages (use Paketo/Heroku builders)
- cgo / musl toolchain matrices
- Replacing `ko` for dockerless registry pushes — this is a **buildpacks**
  builder for platforms that already speak CNB (`pack`, kpack, Tekton, …)
