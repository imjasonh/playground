# node-image

Dockerless OCI image builds for Node.js / TypeScript apps — the Node cousin of
[`ko`](https://ko.build) and [`pymage`](https://github.com/imjasonh/pymage).

**Design:** [`docs/node-image-design.md`](../docs/node-image-design.md) ·
**Plan:** [`docs/node-image-implementation-plan.md`](../docs/node-image-implementation-plan.md)

## Quick start

```bash
cd node-image
go build -o node-image .

# Local digest summary (no registry, scratch base — great for CI/smoke)
./node-image build ./testdata/pure-js \
  --no-push --empty-base --skip-build \
  --platform linux/amd64,linux/arm64 \
  --oci-dir /tmp/node-image-out

# TypeScript app: compiles with pnpm, then packages hermetic prod deps
./node-image build ./testdata/ts-app \
  --no-push --empty-base \
  --platform linux/amd64 \
  --oci-dir /tmp/ts-out

# Load into local Docker and run (stdout is only the image ref)
docker run --rm "$(./node-image build ./testdata/pure-js \
  --local --skip-build --platform linux/amd64)"

# Push to a registry (multi-arch index)
./node-image build ./testdata/pure-js \
  --repo registry.example.com/me/myapp -t latest \
  --skip-build
```

`build` prints **exactly one line on stdout**: the fully resolved image ref
(`registry/repo@sha256:…` on push, or `node-image.local/…:tag` with `--local` /
`-L`). Progress goes to stderr, so command substitution works with
`docker run --rm $(node-image build -L …)`.

Layer tar+gzip is **streamed** (re-opened from disk paths) — compressed blobs
are not retained as `[]byte` in memory.

Requirements for a real push: Go 1.23+, network, and registry credentials via
the normal Docker keychain. `--local` needs a running Docker daemon. App
compile needs `pnpm` on `PATH` when `scripts.build` is present (unless
`--skip-build`).

## What it does

1. **Compile (optional):** if `scripts.build` exists, runs `pnpm install` +
   `pnpm run build` on the host.
2. **Hermetic image deps:** parses `pnpm-lock.yaml` (v9), fetches tarballs by
   integrity, extracts a pnpm-compatible virtual store, writes symlinks/bins —
   **never** runs dependency lifecycle scripts.
3. **Layers:** one store layer per package (auto name-hash buckets when over
   the layer budget) + symlink/`node_modules` layer + app layer.
4. **Multi-arch:** builds `linux/amd64` and `linux/arm64` by default and
   publishes an OCI image index.

## Project layout expectations

| Input | Rule |
|-------|------|
| Directory | Contains `package.json` (CLI arg, default `.`) |
| Lockfile | `pnpm-lock.yaml` in that dir or a parent workspace root |
| Config | Optional `"node-image"` key in `package.json` (`repo`, `base`, `platforms`, `buildScript`, `maxLayers`, …) |
| Base | Default `gcr.io/distroless/nodejs22-debian12` (**glibc**). Musl bases (Alpine/Wolfi/Chainguard) fail loudly. Prefer `@sha256:…` pins. |

## Flags

```
node-image build [dir] [flags]

  --repo string        destination repository (required unless --no-push / --local)
  --base string        base image override
  --platform string    linux/amd64,linux/arm64
  -t string            tags (comma-separated)
  --skip-build         skip pnpm compile step
  --no-push            write local digest summary instead of pushing
  --local, -L          load into local Docker daemon
  --oci-dir string     output dir for --no-push
  --empty-base         scratch base (tests / offline)
  --max-layers int     max total layers including base (default 127)
```

`dir` may appear before or after flags.

## Test

```bash
go test ./...
```

Includes lock/resolve/layer units, pnpm layout conformance (skips without
`pnpm`/network), build determinism, TypeScript compile, multi-arch index,
stdout digest-ref contract (push to an in-process registry), and a
`docker run --rm $(node-image build -L …)` e2e that skips without Docker.
CI installs pnpm when this module is selected.

## Non-goals (v1)

- npm/yarn lockfiles, `--allow-scripts` for image deps, musl mode, Electron
