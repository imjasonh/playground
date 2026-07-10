# node-image

Dockerless OCI **packaging** for Node.js apps — the Node cousin of
[`ko`](https://ko.build) and [`pymage`](https://github.com/imjasonh/pymage).

**node-image is complementary to pnpm, not a replacement.** pnpm (or
turbo/esbuild/prisma/etc.) owns install and compile. node-image reads
`pnpm-lock.yaml`, fetches hermetic production deps, lays out a pnpm-compatible
virtual store, and pushes OCI layers — without running dependency lifecycle
scripts.

**Design:** [`docs/node-image-design.md`](../docs/node-image-design.md) ·
**Plan:** [`docs/node-image-implementation-plan.md`](../docs/node-image-implementation-plan.md) ·
**Monorepo roadmap:** [`docs/node-image-monorepo-roadmap.md`](../docs/node-image-monorepo-roadmap.md)

## Quick start

```bash
cd node-image
go build -o node-image .

# Local digest summary (no registry, scratch base — great for CI/smoke)
./node-image build ./testdata/pure-js \
  --no-push --empty-base --skip-build \
  --platform linux/amd64,linux/arm64 \
  --oci-dir /tmp/node-image-out

# Workspace app (materializes workspace:* packages into the image)
./node-image build ./testdata/workspace-app/apps/api \
  --no-push --empty-base --skip-build \
  --platform linux/amd64 \
  --oci-dir /tmp/ws-out

# Monorepo CI shape: compile externally, then pack
./node-image build ./apps/server --skip-build --repo registry.example.com/me/server

# Diagnose lock issues for one importer (all findings at once)
./node-image diagnose ./testdata/patched

# Load into local Docker and run (stdout is only the image ref)
docker run --rm "$(./node-image build ./testdata/pure-js \
  --local --skip-build --platform linux/amd64)"
```

`build` prints **exactly one line on stdout**: the fully resolved image ref
(`registry/repo@sha256:…` on push, or `node-image.local/…:tag` with `--local` /
`-L`). Progress goes to stderr.

## What it does

1. **Optional compile:** if `scripts.build` exists and `--skip-build` is not
   set, runs `pnpm install` + `pnpm run build` on the host. Large monorepos
   should prefer `--skip-build` / `node-image.skipBuild` after turbo/esbuild.
2. **Hermetic image deps:** parses `pnpm-lock.yaml` (v9), fetches tarballs by
   integrity (with npm auth), materializes workspace/link packages, applies
   lock-recorded patches, writes symlinks/bins — **never** runs dependency
   lifecycle scripts (named `allowScripts` only skips the hard-fail).
3. **Layers:** one store layer per package (auto name-hash buckets + optional
   `unbucketed` hot-list when over the layer budget) + symlink layer + app layer.
4. **Multi-arch:** builds `linux/amd64` and `linux/arm64` by default and
   publishes an OCI image index.

## Config (`package.json` → `"node-image"`)

Flags override the package.json block. Point `node-image build` at the package
directory you want to image (that package’s config applies).

| Key | Purpose |
|-----|---------|
| `repo`, `base`, `platforms` | Push destination / base / arches |
| `entrypoint`, `cmd`, `main` | Image Entrypoint / Cmd / JS main |
| `commands` | Named Cmds; select with `--command worker` |
| `include` / `exclude` | App-layer globs (default: `dist/` or `build/` + root) |
| `skipBuild` | Prefer external compile (monorepo CI) |
| `allowScripts` | Named packages allowed to need natives (scripts still not run) |
| `unbucketed` | Package names that always get their own store layer |
| `env`, `workdir`, `user`, `maxLayers` | Runtime / layer budget |

## Flags

```
node-image build [dir] [flags]
node-image diagnose [dir]

  --repo string          destination repository
  --base string          base image override
  --platform string      linux/amd64,linux/arm64
  -t string              tags
  --skip-build           skip pnpm compile; pack existing outputs
  --command string       named Cmd from node-image.commands
  --allow-scripts list   named packages allowed to need natives
  --cache-dir string     portable cache root (packages/spool/layers)
  --entrypoint list      override entrypoint (e.g. node)
  --no-push / --local    digest summary / Docker load
  --empty-base           scratch base (tests)
  --max-layers int       default 127
```

## Test

```bash
go test ./...
```

Includes lock/resolve/layout units, patch/workspace/catalog/override fixtures,
app glob packing, npm auth header injection, multi-command builds, diagnose
importer isolation, and docker/pnpm e2e (auto-skip when tools are missing).

## Non-goals

- Replacing pnpm for install or workspace linking
- npm/yarn/bun lockfiles (pnpm-lock only)
- Running arbitrary dependency install scripts by default
- musl mode (glibc default; loud fail otherwise)
