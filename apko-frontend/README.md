# apko-frontend

`apko-frontend` is a [BuildKit](https://github.com/moby/buildkit) frontend
that builds an image from an [apko](https://github.com/chainguard-dev/apko)
configuration file. Put a `# syntax=` line at the top of an apko YAML file
and build it with `docker build`:

```yaml
# syntax=localhost:5000/apko-frontend
contents:
  keyring:
    - https://packages.wolfi.dev/os/wolfi-signing.rsa.pub
  repositories:
    - https://packages.wolfi.dev/os
  packages:
    - wolfi-base
entrypoint:
  command: /bin/sh -l
archs:
  - x86_64
  - aarch64
layering:
  strategy: origin
  budget: 10
```

```bash
docker buildx build -f apko.yaml -t example.com/wolfi-base --push .
```

YAML treats the `# syntax=` line as a comment, so the same file still works
with the `apko` CLI.

## Try it

You need Docker with Buildx, and [ko](https://ko.build).

1.  Start a registry that BuildKit can pull the frontend from:

    ```bash
    docker run -d --name registry -p 5000:5000 registry:2
    ```

1.  Build the frontend with ko and push it:

    ```bash
    KO_DOCKER_REPO=localhost:5000/apko-frontend \
      ko build --bare --platform=linux/amd64,linux/arm64 \
      --image-label moby.buildkit.frontend.network.none=true .
    ```

1.  Build and run one of the examples in [`demo/`](demo/):

    ```bash
    docker build -f demo/alpine.apko.yaml -t localhost:5000/demo:alpine demo
    docker run --rm localhost:5000/demo:alpine
    ```

[`demo/run.sh`](demo/run.sh) does these steps and then rebuilds with
`--no-cache` to show that the image digest doesn't change.

The `# syntax=` line names the frontend image. If you push the frontend
somewhere else, change that line, or pass the image with
`--build-arg BUILDKIT_SYNTAX=IMAGE`. With `buildctl`, use the gateway
frontend directly:

```bash
buildctl build --frontend gateway.v0 \
  --opt source=localhost:5000/apko-frontend \
  --opt filename=apko.yaml \
  --local context=. --local dockerfile=. \
  --output type=image,name=example.com/image,push=true
```

## How it works

The frontend runs apko's own Go packages, and BuildKit does every network
fetch and holds every layer.

1.  The frontend parses the YAML with apko's configuration types and rejects
    the fields it doesn't support (see [What doesn't work](#what-doesnt-work)).
1.  It resolves packages for every target architecture at once with apko's
    resolver, the same call that `apko build` and `apko lock` make. apko's
    HTTP requests for keys and `APKINDEX.tar.gz` files go to an
    `http.RoundTripper` that fetches each URL with an `llb.HTTP` source and
    reads the result back through the gateway. The transport records every
    URL apko used.
1.  For each architecture, it writes an apko lock that pins every package,
    in the order `apko build` installs them.
1.  For each architecture, the frontend adds one build step that runs the
    frontend image itself with the `build-layers` argument. BuildKit passes
    a frontend its own image reference, so the frontend pins that image by
    digest and runs it on the build platform. The step has no network. It
    mounts the lock, the keys, and every locked `.apk`, named by a hash of
    their URL, and serves apko's HTTP requests from them. It doesn't mount
    the indexes, because installing from a lock doesn't read them.
1.  In that step, apko installs the locked packages and builds the image
    filesystem as `apko build` does, including accounts, paths, busybox
    links, `/etc/ld.so.cache`, and the apk database, and writes its layers as
    tar files. With `layering`, it plans one layer per origin group plus a
    top layer, exactly as `apko build` does.
1.  The frontend unpacks each tar file into its own scratch state with a
    `Copy` that has `AttemptUnpack` set, and merges the states with
    `llb.Merge`. Each state becomes one layer of the image.
1.  apko's `oci.BuildImageFromLayers` produces the image config (entrypoint,
    command, environment with apko's `PATH` and `SSL_CERT_FILE` defaults,
    user, working directory, volumes, stop signal, labels, and history), and
    its annotations become manifest annotations.

Because the layers come from apko's own code, each layer holds the same
files as `apko build` puts in it: the same paths, modes, owners,
modification times, link targets, and contents. The tar framing and
compression are BuildKit's, so layer digests differ from apko's.

The frontend image needs no network, which the
`moby.buildkit.frontend.network.none` label tells BuildKit.

## What works

| apko field | Notes |
| --- | --- |
| `contents.packages` | Including version constraints such as `curl=8.14.1-r4`. |
| `contents.repositories`, `build_repositories`, `runtime_repositories` | HTTP(S) URLs, or directories in the build context. |
| `contents.keyring` | HTTP(S) URLs, or files in the build context. Chainguard and Alpine key discovery also run, through BuildKit. |
| `contents.runtime_keyring` | |
| `entrypoint.command`, `entrypoint.shell-fragment`, `cmd`, `work-dir`, `stop-signal` | |
| `environment` | apko adds `PATH` and `SSL_CERT_FILE` when you don't set them. |
| `accounts` | Users, groups, and `run-as`. |
| `paths` | Every path type apko supports. |
| `layering` | The `origin` strategy and its budget. |
| `archs` | Each arch becomes a platform. `--platform` overrides the list. Without `--platform`, Buildx warns that the result's platforms don't match the requested one. |
| `annotations`, `vcs-url` | Manifest annotations, and index annotations for a multi-platform build. `vcs-url` must include `@REVISION`. |
| `volumes` | |

Paths in the build context are relative to the root of the context, not to
the YAML file. apko reads them in a fixed directory, `/apko/context`, in both
the frontend and the build step, so `/etc/apko.json` and
`/etc/apk/repositories` record them as written.

These build arguments change the build:

`SOURCE_DATE_EPOCH`
:   The image creation time and the modification time of files apko writes,
    as apko uses it. Without it, the creation time is the newest package build
    time, as with `apko build`.

`APKO_LOCK`
:   The path of an apko lock file in the build context, such as one that
    `apko lock apko.yaml` writes. The build installs the locked packages
    instead of resolving the configuration. Each locked package must still
    appear, with the same version and checksum, in a signed index of the
    configured repositories (see [Signatures](#signatures)).

BuildKit's own options work as usual, for example `--platform`, `--push`,
`--sbom=true` (BuildKit's scanner reads apko's apk database), and
`--provenance`.

## What doesn't work

-   `include`. apko deprecated it. Merge the included file into the
    configuration.
-   `contents.baseimage`, which apko marks experimental.
-   `format: erofs`. BuildKit layers are tar layers.
-   Repositories that need HTTP authentication, such as `apk.cgr.dev`
    with `HTTP_AUTH`. BuildKit's HTTP source can send an `Authorization`
    header from a secret (`llb.AuthHeaderSecret`), but the frontend doesn't
    set it.
-   `vcs-url` detection from a git checkout, which `apko build --vcs` does.
    Set `vcs-url` in the file.
-   apko's command-line flags, such as `--package-append`,
    `--repository-append`, `--keyring-append`, and `--annotations`. Put those
    values in the file.
-   apko's SBOM files. Use BuildKit's `--sbom=true` instead.
-   A lock file whose packages are in a local repository. `apko lock` records
    those packages by absolute path on your machine.
-   Paths outside the build context.

## Signatures

Every package in the image is tied to a signature from the configured
keyring:

-   apko checks the signature of each `APKINDEX.tar.gz` against the keyring,
    for remote and local repositories, while the frontend resolves packages.
    The frontend never turns this off.
-   The signed index lists the SHA-1 checksum of each package's control
    section. The frontend copies those checksums into the lock, and the build
    step checks each downloaded `.apk` against them.
-   The control section records the SHA-256 of the data section, and the
    data section records the SHA-1 of each file. apko checks both while it
    unpacks the package, and fails the build on a mismatch.
-   `apko build --lockfile` trusts the lock's checksums without reading an
    index. With `APKO_LOCK`, the frontend also fetches the indexes, verifies
    their signatures, and fails unless each locked package is listed with the
    same version and checksum. A lock can't add a package that no signed
    index describes.

The keyring is the root of this chain. A keyring URL that starts with
`http://` gets a build warning, because anyone on the network path can
replace the key. As `apko build` does, apko also adds keys that it
discovers: for Alpine repositories, from the release list on
`alpinelinux.org`, and for any HTTP repository, from
`REPOSITORY/apk-configuration`, which only Chainguard repositories serve.

## Caching

The frontend leaves caching to BuildKit and turns off apko's own caches.
apko runs with `WithoutDiskCache`, so it keeps no package, index, or layer
cache. Each build is a fresh process, and nothing outlives it. These are the
BuildKit caches a build uses:

-   **Downloads.** Each index, key, and package is an `llb.HTTP` source.
    BuildKit keeps the file and revalidates it with the server on each build
    by ETag or modification time, without downloading it again when it's
    unchanged. That means one conditional request for each package on each
    build.
-   **The apko step.** Its cache key covers the frontend image, the pinned
    configuration, the lock, the keys, and the packages. A build that
    resolves to the same packages reuses the step, even when an index has
    changed.
-   **Layers.** Each layer is a `Copy` from one of the step's tar files, so
    BuildKit keys it by the tar file's content. When a package changes, the
    apko step runs again, but layers whose content didn't change are cache
    hits, and their blobs, and digests, stay the same.

Because these are ordinary BuildKit cache records, `--cache-to` and
`--cache-from` (registry, local, GitHub Actions, and S3 caches) share them
between machines, and `docker buildx prune` manages them.

There's one trade-off. apko builds the whole filesystem, so the apko step
reruns as a unit and reinstalls every package when any package changes. A
step for each layer would cache better but would duplicate apko's
filesystem logic, which the frontend avoids. For typical images, the step
takes a few seconds.

## Reproducibility

Building the same configuration against the same repository contents
produces the same image digest. The [demo](demo/run.sh) checks this with a
`--no-cache` rebuild. These inputs also change the digest:

-   **Repository contents.** Without a lock, a build resolves against the
    indexes at build time. Use `APKO_LOCK` to pin package versions across
    time.
-   **The frontend version.** The frontend includes its apko version, so pin
    it by digest: `# syntax=example.com/apko-frontend@sha256:...`.
-   **Exporter options and BuildKit's version.** BuildKit compresses the
    layers, so its compression settings (`compression=zstd`,
    `oci-mediatypes`) and its version can change layer digests. The
    uncompressed layer digests (diff IDs) don't change.
-   **Attestations.** Buildx adds a provenance attestation to pushed images
    by default, and the attestation records when the build ran. Compare
    builds made with `--provenance=false`, or compare platform manifests.
-   **Discovered Alpine keys.** apko picks Alpine keys by the current date.
    List the keys in `keyring` to fix them.

The image creation time is the newest package build time, or
`SOURCE_DATE_EPOCH` when you set it, so it doesn't depend on when you build.

Every build shows a step that probes `REPOSITORY/apk-configuration` for each
HTTP repository. This is apko's discovery of Chainguard signing keys.
Repositories other than Chainguard's return 404 there, and BuildKit shows
the 404 as a failed step, but the build continues.

## Develop

```bash
go build ./...
go test -race ./...
```

The tests generate a signed apk repository in memory, resolve a
configuration against it, and run the build step's apko build offline from
the fetched files. They need no network or BuildKit.
