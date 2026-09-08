# bun-image

The [deno-image](https://github.com/imjasonh/deno-image) pattern, for Bun.

[`build.sh`](./build.sh) compiles [`example.js`](./example.js) with
[`bun build --compile`](https://bun.sh/docs/bundler/executables), appends that
executable onto a [distroless](https://github.com/GoogleContainerTools/distroless)
base, and sets it as the entrypoint.
[`crane`](https://github.com/google/go-containerregistry/tree/main/cmd/crane)
does the image work. There is no Dockerfile and no `docker build`.

[`run.sh`](./run.sh) calls `build.sh` and then `docker run`. Only that step
needs a container runtime.

`build.sh` and `run.sh` take two optional positional args:
`build.sh [image-to-build] [base-image]`.

## Requirements

- [Bun](https://bun.sh/)
- [crane](https://github.com/google/go-containerregistry/tree/main/cmd/crane)
- Registry credentials, if you push (the default `build.sh` path)

## Usage

```bash
cd bun-image

# Push to a registry. stdout is the digest ref.
./build.sh [image] [base]

# Build, then docker run (needs a registry docker can pull).
./run.sh [image] [base]

# Write a local docker-save tarball instead of pushing.
BUN_IMAGE_OUT=/tmp/bun-image.tar ./build.sh bun-image.local/example
docker load -i /tmp/bun-image.tar
docker run --rm -p 8000:8000 bun-image.local/example
```

Defaults:

- Image: `gcr.io/imjasonh/bun`
- Base: `gcr.io/distroless/cc-debian12`

The example listens on port 8000. `./example --hello` prints `bun-image-ok` and
exits, which `test.sh` uses as a smoke check.

## Why a shell script

Bun can compile a JS file into one Linux executable that already contains the
Bun runtime. That is the same job `deno compile` does. After that,
`crane mutate --append` is enough. A Go CLI does not buy anything at this size.

## Static binaries

I tried `bun build --compile --target=bun-linux-x64-musl` (Bun 1.4.2). The
result is still dynamically linked to musl libc and libstdc++. It does not run
on a glibc host, and it does not run on `gcr.io/distroless/static`. Bun has no
`--static` compile flag.

So this script compiles the glibc target (`bun-linux-x64` or `bun-linux-arm64`,
matching the host) and uses `distroless/cc`, which is the same libc pairing
[deno-image](https://github.com/imjasonh/deno-image) uses.

If you set a `*-musl` `BUN_TARGET` with a `distroless/cc` or `distroless/static`
base, `build.sh` exits. Use an Alpine (or other musl + libstdc++) base if you
want that target.

## Why this is not node-image

[`node-image`](../node-image/) is a Go packager for Node apps that cannot
compile to one binary. It reads `pnpm-lock.yaml`, fetches production tarballs,
lays out a virtual store, and splits layers. That is a different problem.

Stay on the shell script until someone needs to image a Bun app *without*
`bun build --compile`: native addons, files loaded at runtime that the bundler
cannot see, or bun.lock-faithful `node_modules` layers. That would be the
moment to grow a node-image-shaped CLI. Not now.

## Test

```bash
# Needs bun. The image half also needs crane and a pull of the default base.
./test.sh
```

## Environment

| Variable | Purpose |
|----------|---------|
| `BUN_IMAGE_OUT` | Write a docker-save tarball here instead of pushing |
| `BUN_TARGET` | `bun build --compile --target` value. Default is the host's glibc Linux target. |
