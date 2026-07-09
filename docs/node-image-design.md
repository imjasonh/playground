# Design: `node-image` — dockerless Node.js / TypeScript image builds

> Status: **Design only** (see §0 for locked decisions).
> Proposes a `ko`/`pymage`-style Go CLI for Node.js (including TypeScript)
> apps. Nothing here is implemented yet.

## 0. Locked decisions

| Topic | Decision |
|-------|----------|
| Name / home | **`node-image`**, as a Go app in **this repo** (`node-image/`) |
| Lockfile | **`pnpm-lock.yaml` required** (pnpm ecosystem lock; see below) |
| pnpm binary | **Not required at build time.** Go reads the lock, fetches tarballs, lays out the store + symlinks (pymage-style). |
| Scripts | **Never run dependency lifecycle scripts.** No `--allow-scripts`. Fail if a required package cannot work without them. |
| Input | A **directory containing `package.json`** (CLI arg, default `.`). Walk up for `pnpm-lock.yaml` if needed. |
| Layering | **Per-package store layers + symlink/`node_modules` layer(s)**; `auto` bucket fallback under a layer budget |
| Multi-arch | **Must for v1** (`linux/amd64` + `linux/arm64` index) |
| libc | **glibc by default**; **loud fail** if the app needs musl-only natives (or base libc mismatches) |
| CLI shape | One easy do-it-all `node-image build [dir]`; optional finer commands later |

Rationale notes:

- **Lockfile ≠ runtime dependency on pnpm.** We consume pnpm's lock format
  because it is content-addressed and graph-complete (`packages` +
  `snapshots` in lockfile v9). Users still *author* deps with pnpm (or
  `pnpm import`); `node-image` itself does not shell out to `pnpm`. Same
  relationship as pymage ↔ `uv.lock`.
- **No scripts is a feature for multi-arch.** Install scripts compile or
  download for the *host* arch; they cannot honestly populate an amd64+arm64
  index from one machine. Prebuilds and platform optional packages only.
- **Directory-scoped builds** match `ko`/`pymage`: point at the app directory
  (the one with `package.json`), default `.`.

## 1. Goal

A single **Go CLI**, `node-image`, that builds and pushes OCI images for
Node.js applications **without a Docker daemon** and **without invoking
pnpm/npm**, in the spirit of [`ko`](https://ko.build),
[`pymage`](https://github.com/imjasonh/pymage),
[`krust`](https://github.com/imjasonh/krust), and
[`jib`](https://github.com/GoogleContainerTools/jib):

- **Dependencies are split into reusable per-package layers** (store contents)
  plus a thin **symlink / `node_modules` layer**.
- **Outside-of-Docker caches are reused** — a local content-addressed tarball
  cache keyed by lock `integrity` (optionally interoperable with a pnpm store
  layout on disk, but not required).
- **Hermetic:** lock + fetched tarballs only; no dependency lifecycle scripts.
- **Configurable base**, defaulting to a slim **glibc** Node image.
- **Multi-arch from day one** via an OCI image index.
- **Unprivileged** registry I/O via
  [`go-containerregistry`](https://github.com/google/go-containerregistry).

### Non-goals (initially)

- A general-purpose Dockerfile / BuildKit interpreter.
- Supporting npm/yarn/bun lockfiles in v1 (pnpm-lock only).
- Requiring or shelling out to the `pnpm` binary.
- Compiling native addons from source (`node-gyp`) during the image build.
- Running dependency `preinstall` / `install` / `postinstall` / `prepare`
  (no escape hatch in v1).
- Electron / browser-extension packaging.
- Building an entire pnpm workspace as one image (point at one package dir).

## 2. Why this is worth doing (and why Node is harder than Go/Python)

### 2.1 The shared insight

`ko`, `jib`, and `pymage` rest on the same OCI facts:

1. Layers are content-addressed (gzip tar digest).
2. Registries support blob existence checks and cross-repo mounts → **zero-byte
   reuse** when a layer digest already exists.
3. A manifest is small JSON. Unchanged deps ⇒ only the app layer + manifest move.

For Node, dependency trees are often hundreds of MB; app code is small. A
dedicated builder can **shard deps**, reuse a **tarball cache**, and push
**only changed layers** — without a Docker daemon.

### 2.2 Why Node is not "pymage with tarballs"

| Concern | Go (`ko`) | Python (`pymage`) | Node (`node-image`) |
|---------|-----------|-------------------|---------------------|
| Artifact | Single static binary | Pre-built wheels | Package tree + optional native bits |
| Install = unzip? | N/A | Mostly yes | **Yes, by design** — extract tarballs + write symlinks/bins |
| Build-time code execution | Compiler only | Avoided (wheels-only) | **Forbidden** for dependencies |
| Multi-arch | Cross-compile | Per-platform wheels | Per-platform optional deps + shared pure-JS layers |
| Resolver / lock | `go.mod` | `uv.lock` | **`pnpm-lock.yaml`** (tool not required) |
| TypeScript | N/A | N/A | App build phase (separate from dep install) |

## 3. Prior art

Nothing currently ships as a maintained, `ko`-like, per-dependency-sharded Node
builder that is hermetic and multi-arch. Closest options:

| Project | Gap |
|---------|-----|
| **[FTL](https://github.com/GoogleCloudPlatform/runtimes-common/tree/master/ftl)** | Abandoned; predates modern pnpm locks |
| **[`pymage`](https://github.com/imjasonh/pymage)** | Closest template (Go unpack + per-artifact layers); Python-only |
| **[`ko`](https://ko.build)** / **[`krust`](https://github.com/imjasonh/krust)** | Single-artifact languages |
| **[containerify](https://github.com/eoftedal/containerify)** | Coarse layering; assumes pre-installed tree |
| **Bazel [`js_image_layer`](https://github.com/aspect-build/rules_js)** | Store + symlink split inspiration; requires Bazel |
| **pnpm itself** | Correct layout oracle — we reimplement a *subset* of install from the lock, not a general package manager |

## 4. Product shape

### 4.1 Do-it-all command

```
node-image build              # dir defaults to .
node-image build ./apps/api   # directory with package.json
node-image build -t v1.2.3
docker run "$(node-image build)"
```

`node-image build [dir]` is the common case: find `package.json` in `dir`,
find `pnpm-lock.yaml` (in `dir` or a parent), fetch → layout → shard → push
multi-arch index. Prints the image reference by digest.

Optional later: `fetch` / `pack` / `push` as split steps. Alpha can ship only
`build`.

### 4.2 Config

In the target directory's `package.json` (key name TBD):

```json
{
  "name": "myapp",
  "main": "dist/index.js",
  "node-image": {
    "repo": "registry.example.com/me/myapp",
    "base": "gcr.io/distroless/nodejs22-debian12@sha256:…",
    "platforms": ["linux/amd64", "linux/arm64"]
  }
}
```

Defaults:

| Knob | Default |
|------|---------|
| Input dir | `.` (must contain `package.json`) |
| Lockfile | `pnpm-lock.yaml` in dir or nearest parent |
| Dep scripts | **never** |
| libc target | **glibc**; fail loudly on musl-only requirements |
| Base | Known-**glibc** slim/distroless Node image |
| Platforms | `linux/amd64,linux/arm64` when the base supports them |
| Workdir | `/app` |
| User | non-root from base (or `65532`) |
| Cmd | `["node", "<main>"]` — never a package manager as PID 1 |
| Production deps only | yes (omit `devDependencies`) |
| Layer strategy | store per-package + symlink layer(s); `auto` buckets over `max-layers` |
| Max layers | ~127 including base |

Auth: standard Docker keychain via ggcr.

## 5. Architecture: Go-native install from `pnpm-lock.yaml`

> **Parse `pnpm-lock.yaml`, download each needed tarball by integrity, extract
> into a pnpm-compatible virtual store, write the symlink/`node_modules` farm
> and bins, emit one OCI layer per store package plus symlink layer(s) plus an
> app layer, append to the base, publish a multi-arch index. Never execute
> package scripts. Never call `pnpm`.**

```
dir/package.json + pnpm-lock.yaml (+ source)
        │
        ▼
1. Load package.json in dir; locate lock (dir or parents)
   Select importer matching this directory (workspace-aware path)
        │
        ▼
2. Resolve production closure for each target platform
     walk snapshots / dependency edges
     filter optional deps by os/cpu/libc=glibc
     pure-JS → platform=any (shared layers)
        │
        ▼
3. For each package: cache lookup by integrity → else HTTPS fetch → verify SRI
        │
        ▼
4. Extract tarball → store path; write symlink farm + .bin
   (no scripts)
        │
        ▼
5. Optional app build phase (§8)
        │
        ▼
6. Pack store layers + symlink layer(s) + app layer
   HEAD/mount/upload; PUT manifests + index
```

### 5.1 Can this be reliable without the pnpm binary?

**Yes for the common case**, with sharp edges called out and failed loudly.

The lockfile (v9) already contains what an installer needs:

| Lock field | Use |
|------------|-----|
| `importers[<path>]` | Which deps belong to this directory / workspace package |
| `packages[<id>].resolution.integrity` (and tarball URL) | Fetch + verify |
| `packages[<id>].os` / `cpu` / `libc` / `engines` | Platform filtering |
| `snapshots[<depPath>].dependencies` / `optionalDependencies` | Exact graph edges (including peer-suffixed paths) |

npm package tarballs are ordinary gzipped tars with a `package/` root — unpack
is straightforward (same class of problem as wheel unzip in pymage).

**What we must implement carefully (reliability checklist):**

1. **Lockfile versions** — support modern `lockfileVersion` 9.x (and 6.x if
   cheap); reject unknown versions with upgrade guidance.
2. **Peer-dependency path suffixes** —
   `foo@1.0.0(react@18.0.0)` keys in `snapshots`; must preserve pnpm's path
   identity so the symlink farm matches Node resolution.
3. **Virtual store layout** — place files under
   `node_modules/.pnpm/<depPath>/node_modules/<name>` and symlink from the
   app's `node_modules` (and nested `.pnpm` links) the way pnpm does.
4. **Bins** — read each package's `package.json` `bin` / `directories.bin`
   and write `.bin` symlinks (no `install` script shims that expect to run).
5. **Optional / platform packages** — skip or include per target arch; never
   run their installers.
6. **Patches** (`pnpm.patchedDependencies`) — apply lock-recorded patches
   during extract, or **fail** if present and unimplemented.
7. **Non-registry deps** — `git:`, `file:`, `link:`, `workspace:` — support
   `workspace:`/`link:` when the target dir is inside a workspace (copy from
   source tree); **fail clearly** on git/http exotic sources until supported.
8. **Bundled dependencies** — unpack as npm would, or fail if we cannot.
9. **Conformance oracle** — CI compares our layout (file digests + symlink
   targets) against `pnpm install --ignore-scripts --prod` on fixtures; pnpm
   is a **test dependency**, not a runtime dependency.

**When we refuse (loud errors, not silent breakage):**

- Package has install scripts *and* no usable prebuild / is not pure JS /
  not a skipped optional — actually: we never run scripts, so we only fail if
  **runtime would be broken**. Heuristic for alpha: fail if the package's
  `package.json` lists `install`/`postinstall`/`preinstall` **and** it has
  no `prebuilds/` / `node-gyp-build`-style layout we can detect **and** it is
  not an optional dependency we can omit. Tune with fixtures.
- musl-only native artifacts under glibc default.
- Unsupported lock version or exotic resolution type.

This is the same honesty bargain as pymage's wheels-only rule: **narrower
compatibility, stronger hermeticity and multi-arch.**

### 5.2 Local cache (outside-of-Docker reuse)

- Content-addressed dir, e.g. `~/.cache/node-image/packages/sha512-…`.
- Optionally read from an existing pnpm store if the same integrity is already
  present (best-effort speedup) — still no need to *run* pnpm.
- Layer blob cache: `integrity → {compressed digest, diffID, size}` so rebuilds
  skip recompression and registry uploads via HEAD/mount.

### 5.3 Determinism

- Fixed `mtime` / uid / gid / modes; sorted tar entries; deterministic gzip
  **or** cache compressed blobs by content.
- Stable `/app` prefix.
- Store package → layer by `(name, version, integrity)` (and depPath when peer
  suffixes matter for *symlink* layers, not store bytes).
- Symlinks preserved as symlinks.
- Exclude junk: `**/.cache`, VCS dirs, optional `**/*.map`.

## 6. Alternatives (rejected / later)

| Approach | Status |
|----------|--------|
| Shell out to `pnpm install --ignore-scripts` | **Rejected for v1** — keep as conformance oracle in tests only |
| `--allow-scripts` | **Rejected** — fights multi-arch; no escape hatch in v1 |
| Bundle-first (`esbuild` → one file) | Later optional mode |
| Single monolith `node_modules` layer | Escape hatch only |
| npm/yarn lock backends | Later |

## 7. Layering strategy (v1): store + symlink

| Layer kind | Contents | Changes when… |
|------------|----------|---------------|
| **Store (per package)** | Extracted package files under `.pnpm/…` | That package integrity changes |
| **Symlink / `node_modules`** | Symlink farm, `.bin`, graph edges | Dependency graph / peer resolution changes |
| **App** (last) | Build output + root `package.json` | App source / build output changes |

`auto`: per-package while under `max-layers`; else name-hash buckets for store
layers. App layer never re-embeds deps.

## 8. TypeScript, app builds, and directories

### 8.1 Input model (locked)

- CLI takes a **directory** (default `.`).
- That directory must contain **`package.json`** — that package is what gets
  imaged.
- **`pnpm-lock.yaml`** may live in that directory or a parent (workspace root).
  The importer path in the lock is derived from the relative path between lock
  root and the package dir.
- No separate `--filter` flag required for the common case: **the directory
  is the filter.**

### 8.2 App build phase

Hermetic **dependency** layout vs apps that need `tsc` / bundlers:

1. Prod dep layers: always from lock + tarball extract (no scripts).
2. Inside do-it-all `build`, if a build script is configured: run it on the
   host with whatever toolchain the user already has (may use a pre-existing
   local `node_modules` for compile only — or we materialize a dev closure
   the same hermetic way). **Build outputs** are copied into the app layer;
   compile-time `node_modules` is not what we ship unless it is the prod
   closure.
3. Fail closed on `*.ts` entrypoints without a build unless opted into a
   TS-runner base.

Exact "how does `tsc` get its deps if we never run pnpm" is an open
implementation detail (§11): either expect the user to have built already
(`--build=false` default for pure packaging), or hermetically materialize
devDeps too for the build phase only.

Framework-specific graphs (Next standalone, etc.) are out of scope for alpha —
configure the output path.

## 9. Multi-arch, libc, and scripts

### 9.1 Multi-arch flow

For each target `linux/<arch>`:

1. Resolve closure with os=linux, cpu=arch, libc=glibc.
2. Fetch missing tarballs (optional platform packages for that arch).
3. Build arch-specific image (shared pure-JS store layers by digest).
4. Publish an **OCI image index**.

### 9.2 Native addons

| Package kind | Behavior |
|--------------|----------|
| Pure JS | Shared store layer |
| Optional platform package | Per-arch store layer |
| In-tarball `prebuilds/` / `node-gyp-build` | Shared layer; runtime picks `.node` |
| Needs compile via install script | **Hard fail** |

### 9.3 libc (locked)

- Default target: **glibc**.
- Default base: a **glibc** Node image (verify before shipping; do not assume
  Chainguard/Wolfi).
- musl-only requirements or musl base mismatch → **loud fail** with guidance.
- Later: explicit `--libc musl` mode with the same fail-loud rules.

### 9.4 Why there is no `--allow-scripts`

Dependency lifecycle scripts often compile or download for **the host they
run on**. One scripted install cannot correctly fill `linux/amd64` and
`linux/arm64` from a single machine without per-arch build environments —
which reintroduces containerized builds. Hermetic fetch of per-arch optional
packages / prebuilds is the multi-arch path. **Scripts stay unsupported.**

## 10. Implementation sketch (this repo)

```
node-image/
├── go.mod
├── go.sum
├── README.md
├── .gitignore
├── main.go
├── internal/
│   ├── lock/        # pnpm-lock.yaml v9 (+ v6 if needed)
│   ├── resolve/     # importer → per-platform closure
│   ├── fetch/       # integrity-addressed tarball cache
│   ├── layout/      # extract + virtual store + symlinks + bins
│   ├── layer/       # store per-package tar + symlink layer + buckets
│   ├── app/         # dist/source layer + ignores
│   ├── base/        # Node version + libc detect
│   └── publish/     # ggcr assemble, mount/push, index
└── testdata/        # fixtures; CI compares to pnpm --ignore-scripts oracle
```

Phased delivery:

1. Module skeleton + deterministic tar + push app-on-base.
2. Lock parse + fetch-by-integrity + extract one package → layer.
3. Full prod closure layout (store + symlinks + bins) + conformance tests
   vs `pnpm install --ignore-scripts --prod`.
4. Per-package store layers + symlink layer + registry reuse demo.
5. Multi-arch index + glibc checks + shared pure-JS blobs.
6. Directory/importer selection (`.` and nested package dirs).
7. App build phase policy; loud diagnostics for scripts/libc/ABI.
8. SBOM from integrities; optional cosign.
9. (Later) patches, more exotic resolutions, musl mode, npm lock backend.

## 11. Remaining open questions

### 11.1 Reliability / layout

1. Virtual store: match pnpm's on-disk layout **bug-for-bug**, or a simplified
   layout that Node still resolves (higher risk)? Recommendation: match pnpm
   closely enough that the conformance oracle passes on fixtures.
2. Which lockfile versions exactly for alpha (9 only vs 6+9)?
3. Patches: implement in alpha or fail-if-present?
4. Heuristic for "this package needs scripts to function" — how aggressive?

### 11.2 App build vs hermetic deps

5. Default: package whatever is already built (`dist/`), and require users to
   compile first? Or have `build` hermetically materialize devDeps and run
   `scripts.build`?
6. Config key name: `"node-image"` vs `nodeImage` vs separate YAML.

### 11.3 Base / runtime polish

7. Exact default glibc base image ref after libc/Node metadata check.
8. Base digest required vs tags with warning.
9. Entrypoint resolution: `package.json#main` vs `node-image.entrypoint` vs `bin`.

### 11.4 Success bar for alpha

10. Demo: directory with `package.json` + pnpm lock, multi-arch push, code-only
    rebuild uploads ≪ deps; one dep bump uploads ~one store layer; CI layout
    oracle green — **and no `pnpm` binary on the build PATH**.

## 12. Risks

- **Reimplementing install wrong** — mitigated by conformance tests against
  pnpm as oracle; start with a small fixture corpus and grow.
- **Peer-suffixed dep paths** — subtle; must be in early fixtures.
- **`--ignore-scripts`-incompatible packages** — fail loud; document
  known-good patterns (pure JS, platform optional deps, prebuildify).
- **Wrong default base libc** — verify; fail loud.
- **Layer explosion** — `auto` bucketing.
- **Adoption: pnpm lock required** — document `pnpm import`; no pnpm at
  *image build* time still helps CI images stay tiny.

## 13. Decision summary

| Decision | Default |
|----------|---------|
| Name / location | `node-image/` in this repo |
| Input | directory with `package.json` (default `.`) |
| Lockfile | `pnpm-lock.yaml` (dir or parent) |
| pnpm binary | **not used** at build time |
| Dep scripts | **never** (no `--allow-scripts`) |
| Layering | store per-package + symlink layer(s) |
| Multi-arch | yes |
| libc | glibc default; loud fail otherwise |
| CLI | `node-image build [dir]` do-it-all |
| Cmd | `["node", "<main>"]` |

## 14. References

- [pymage README / DESIGN](https://github.com/imjasonh/pymage)
- [pnpm lockfile v9 spec](https://github.com/pnpm/spec/blob/master/lockfile/9.0.md)
- [ko](https://ko.build)
- [Jib](https://github.com/GoogleContainerTools/jib)
- [FTL](https://github.com/GoogleCloudPlatform/runtimes-common/tree/master/ftl)
- [containerify](https://github.com/eoftedal/containerify)
- [aspect `js_image_layer`](https://github.com/aspect-build/rules_js)
- [pnpm `supportedArchitectures`](https://pnpm.io/settings#supportedarchitectures)
- Stack Overflow: [Equivalent of Google's Jib for Node.JS?](https://stackoverflow.com/questions/61598311/equivalent-of-googles-jib-for-node-js)
