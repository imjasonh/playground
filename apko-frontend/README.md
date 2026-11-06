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
between machines, and `docker buildx prune` manages them. A remote cache
doesn't save the package downloads, though. A builder that has no local
copy of an HTTP source downloads it to compute its cache key, unless the
build pins the file's checksum, and `APKINDEX.tar.gz` lists only each
package's control-section checksum, not a checksum of the whole file. A
fresh builder with `--cache-from` downloads every package, then reuses the
cached apko step and layers.

There's one trade-off. apko builds the whole filesystem, so the apko step
reruns as a unit and reinstalls every package when any package changes.
[Future work](#future-work-a-build-step-for-each-layer) describes a step for
each layer instead.

## Reproducibility

Building the same configuration against the same repository contents
produces the same image digest. The [demo](demo/run.sh) checks this with a
`--no-cache` rebuild.

The digest isn't the one `apko build` produces. Each layer holds the same
files, with the same metadata and contents, but BuildKit writes its own tar
stream (entry order and header encoding) and its own gzip, so the
uncompressed layer digests (diff IDs) differ, and so do the config and
manifest that list them. Matching apko's digests would need BuildKit to use
apko's tar files as layer blobs unchanged, and LLB has no operation that
turns a file into a layer blob.

These inputs also change the digest:

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

## Performance compared with the apko CLI

The frontend isn't faster than `apko build`. It's about as fast when
nothing changed and the image is large, and slower otherwise, by a fixed
overhead of about half a second to a second plus BuildKit's export. Its
benefits are BuildKit's: `docker build`, shared and standard caches,
attestations, and multi-platform output.

These are median times of five builds, each writing an image tarball, from
an nginx mirror on the same machine, so downloads take almost no time:

| Build | Image | `apko build` | Frontend |
| --- | --- | --- | --- |
| Cold, every cache empty | 16 packages | 0.25 s | 1.15 s |
| Cold, every cache empty | 52 packages, 143 MB | 1.41 s | 4.21 s, or 2.9 s with `compression=zstd` |
| Nothing changed | 16 packages | 0.22 s | 0.34 s |
| Nothing changed | 52 packages | 1.07 s | 0.89 s |
| Configuration change | 16 packages | 0.21 s | 0.54 s |
| Configuration change | 52 packages | 1.05 s | 1.99 s |
| Fresh builder, `--cache-from` a registry | 52 packages | 1.37 s, fresh apko cache | 4.2 to 4.5 s |

`apko build` does the same work on every run: it unpacks and verifies each
package, lays out the filesystem, and compresses the layers. BuildKit
skips all of that when nothing changed, which is why the frontend wins on
the large image. For the configuration change on the 52-package image, the
frontend's 1.99 s divides like this:

| Part | Time | Notes |
| --- | --- | --- |
| Start the frontend, resolve packages, and revalidate 55 downloads | 0.43 s | BuildKit sends a conditional request for each index, key, and package on every build, which `apko build` doesn't do. |
| The apko step | 1.08 s | About 0.15 s is starting the container. The rest is the same work as `apko build`, without compression. |
| Read the step's plan and submit the layers | 0.1 s | The frontend learns the number of layers from the step. |
| Export | 0.22 s | BuildKit compresses only the layer that changed. |

On a cold build, BuildKit's default gzip export takes 1.8 s of the 4.2 s.
It compresses each layer on one core, so the 56 MB `nodejs` layer sets the
time, while apko compresses with `pgzip` across cores. The exporter's
options belong to the client, so set them when you build:
`--output type=image,compression=zstd,...` takes the cold build to 2.9 s
and produces smaller layers. zstd layers need containerd 1.5 or later, or
Docker 23 or later, to pull. `compression-level=1` keeps gzip and takes
3.2 s.

A profile of the apko step on the 52-package image showed that about 37% of
its CPU time went to compressing layer tars that BuildKit decompressed again
when it unpacked them. The step writes uncompressed tars instead, which
cut its CPU time by 42%. Its wall time barely moved, because unpacking the
largest package, `nodejs`, on one core sets the critical path, as it does
for `apko build`.

## Future work: a build step for each layer

Today one build step per architecture runs apko's whole build. When any
package changes, that step installs every package again, although BuildKit
still reuses the blobs of layers whose content didn't change.

### What it would take

A build step for each origin group would install only that group's
packages, and a last step would write the top layer. That needs four pieces
of apko's build that apko doesn't export:

1.  **Grouping in the frontend.** apko groups packages by origin, size, and
    `replaces`. `APKINDEX.tar.gz` doesn't carry `replaces`, so the frontend
    would read each package's `.PKGINFO`, for example from a small step that
    writes the control sections as JSON, and port apko's
    `groupByOriginAndSize` (about 120 lines of `layers.go`).
1.  **A step for each group.** Install the group's packages with go-apk's
    exported `APK.InstallPackages` into an empty filesystem, then write the
    layer as apko's `partitionLayers` does: parent directory entries take the
    timestamp of the first file under them, and the layer carries a partial
    installed database with only its packages (about 150 lines).
1.  **Configuration that changes package files.** apko applies `accounts`,
    `paths`, and `certificates` to the whole filesystem, and a file that a
    package owns stays in that package's layer with the change applied. For
    example, `/etc/passwd` with the configured users is in the layer of the
    package that owns `/etc/passwd`. So each group step would apply those
    mutations to the files it owns. That means porting `accounts.go`,
    `paths.go`, and the relevant parts of `certificates.go` (about 840
    lines), and it means a change to those fields reruns every group step.
1.  **A top-layer step.** Mount the merged group layers read-only, and write
    the files no package owns: the full installed database, `world`,
    `repositories`, keys, `scripts.tar`, `triggers`, `/etc/apko.json`,
    busybox links (`busybox.go`, 143 lines), `/etc/ld.so.cache` (apko's
    `ldsocache` package is exported), character devices, the s6 tree, and
    the runtime keyring.

That is roughly 1,000 to 1,500 lines that copy unexported apko code, and it
would drift as apko changes. The file-by-file comparison against
`apko build`, which this frontend passes, would become an end-to-end test
to catch the drift. A smaller alternative is to add two exported functions
to apko upstream, one that builds a group's layer from its packages and one
that builds the top layer from a base filesystem. With those, the frontend
needs about 200 lines, and apko keeps owning its filesystem logic.

### Expected gains

Measured with this frontend on an Alpine image of 52 packages, 143 MB
uncompressed in 11 layers, with `nodejs` (56 MB) and `python3` (25 MB) as the
largest groups:

| Build | Now | With a step for each layer |
| --- | --- | --- |
| No change | 0.89 s, all cached | Same |
| `environment` or `entrypoint` change | 1.99 s, of which the apko step takes 1.08 s | Only the top-layer step runs, because these fields reach only `/etc/apko.json`: about 0.8 s less |
| `accounts`, `paths`, or `certificates` change | 1.99 s | Every group step runs, so about the same |
| One package changes | About 2 s, of which the apko step takes 1.08 s | Only the changed group's step and the top-layer step run: 0.5 to 0.8 s less, depending on the group's size |
| Cold build | 4.21 s | About the same; apko already installs packages in parallel |

The apko step processes about 130 MB/s here, so it grows with image size.
For an image of about 2 GB, such as a CUDA or PyTorch image, the step would
take about 15 s, and a step for each layer would bring a one-package
rebuild down to the time for that package's group plus the top layer, a few
seconds.

A step for each layer doesn't reduce downloads on a builder without a
local cache, such as a CI runner that imports a remote cache with
`--cache-from`. BuildKit downloads every package to compute the cache keys,
as [Caching](#caching) describes. It would save downloads only if
repositories published a checksum of each whole `.apk` that the frontend
could pin.

Most of the remaining time in a rebuild is fixed. It goes to resolving
packages, revalidating each download with the server, and exporting the
image, and a step for each layer doesn't change it.

## Develop

```bash
go build ./...
go test -race ./...
```

The tests generate a signed apk repository in memory, resolve a
configuration against it, and run the build step's apko build offline from
the fetched files. They need no network or BuildKit.
