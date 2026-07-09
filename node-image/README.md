# node-image

Dockerless OCI image builds for Node.js / TypeScript apps, in the spirit of
[`ko`](https://ko.build) and [`pymage`](https://github.com/imjasonh/pymage).

See [`docs/node-image-design.md`](../docs/node-image-design.md) and
[`docs/node-image-implementation-plan.md`](../docs/node-image-implementation-plan.md).

## Status

Alpha in progress. Core pieces landing incrementally with tests.

## Build

Requires Go 1.22+ (`GOTOOLCHAIN=auto` downloads a newer toolchain if needed):

```bash
cd node-image
go build -o node-image .
```

## Usage

```bash
# Build + push (multi-arch when configured)
node-image build ./path/to/app --repo registry.example.com/me/myapp -t latest

# Package to a local OCI layout without pushing
node-image build ./path/to/app --no-push --oci-dir /tmp/out

# Skip host TypeScript/compile step
node-image build ./path/to/app --skip-build --repo …
```

The app directory must contain `package.json`. A `pnpm-lock.yaml` must exist
in that directory or a parent (workspace root).

## Test

```bash
go test ./...
```

Layout conformance tests that compare against `pnpm install --ignore-scripts`
skip automatically when `pnpm` is not on `PATH` or network is unavailable.

## How it works (short)

1. **App compile (optional):** if `scripts.build` exists, run `pnpm install` +
   `pnpm run build` on the host.
2. **Image deps (hermetic):** parse `pnpm-lock.yaml`, fetch tarballs by
   integrity, extract a pnpm-compatible virtual store, write symlinks/bins —
   **never** run dependency lifecycle scripts.
3. **Layers:** one store layer per package + symlink/`node_modules` layer +
   app layer; push via go-containerregistry (multi-arch index).
