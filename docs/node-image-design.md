# Design: `node-image` — dockerless Node.js / TypeScript image builds

> Status: **Design only** (see §0 for locked decisions).
> Proposes a `ko`/`pymage`-style Go CLI for Node.js (including TypeScript)
> apps. Nothing here is implemented yet.

## 0. Locked decisions

| Topic | Decision |
|-------|----------|
| Name / home | **`node-image`**, as a Go app in **this repo** (`node-image/`) |
| Lockfile | **`pnpm-lock.yaml` required** (pnpm ecosystem lock; see below) |
| pnpm binary | **Not used for image dependency layout.** Go reads the lock, fetches tarballs, lays out the store + symlinks (pymage-style). **May invoke `pnpm` for the app compile phase only** (TypeScript / `scripts.build`). |
| Dep scripts | **Never run dependency lifecycle scripts** when materializing image layers. No `--allow-scripts`. Fail if a required package cannot work without them. |
| App build | **Do-it-all `build` compiles the app** when a build script is present — typically by invoking `pnpm run build` (or configured script) on the host after a normal pnpm install for compile. |
| Input | A **directory containing `package.json`** (CLI arg, default `.`). Walk up for `pnpm-lock.yaml` if needed. |
| Layering | **Per-package store layers + symlink/`node_modules` layer(s)**; `auto` bucket fallback under a layer budget |
| Multi-arch | **Must for v1** (`linux/amd64` + `linux/arm64` index) |
| libc | **glibc by default**; **loud fail** if the app needs musl-only natives (or base libc mismatches) |
| CLI shape | One easy do-it-all `node-image build [dir]`; optional finer commands later |

Rationale notes:

- **Two different jobs.** (1) *Image dependency layers* must be hermetic and
  multi-arch → Go-native extract from the lock, no dep scripts, no `pnpm`
  required for that path. (2) *App compile* (tsc, bundlers) is a host-side
  build → invoking `pnpm install` + `pnpm run build` is fine and keeps
  do-it-all UX. Compile artifacts go in the app layer; the production
  `node_modules` in the image still comes from the hermetic path.
- **Lockfile ≠ requiring pnpm for packaging.** Users author deps with pnpm.
  Image layout does not shell out to pnpm. App build may. Same spirit as
  pymage ↔ `uv.lock`, plus an explicit compile step ko does not need.
- **No dependency install scripts** remains hard — that is what protects
  multi-arch. Root/app `scripts.build` is different: it runs on the host to
  produce JS output, not to fill per-arch native deps in the image.
- **Directory-scoped builds** match `ko`/`pymage`: point at the app directory
  (the one with `package.json`), default `.`.

## 1. Goal

A single **Go CLI**, `node-image`, that builds and pushes OCI images for
Node.js applications **without a Docker daemon**, in the spirit of
[`ko`](https://ko.build), [`pymage`](https://github.com/imjasonh/pymage),
[`krust`](https://github.com/imjasonh/krust), and
[`jib`](https://github.com/GoogleContainerTools/jib):

- **Dependencies are split into reusable per-package layers** (store contents)
  plus a thin **symlink / `node_modules` layer**, laid out in Go from the lock
  (no Docker; no `pnpm` for that step).
- **Do-it-all `build` also compiles the app** (e.g. TypeScript) when needed,
  by invoking pnpm on the host for the compile phase only.
- **Outside-of-Docker caches are reused** — integrity-addressed tarball cache
  for image deps; pnpm's own store/cache for the compile install.
- **Hermetic image deps:** lock + fetched tarballs only; no dependency
  lifecycle scripts in the image layout path.
- **Configurable base**, defaulting to a slim **glibc** Node image.
- **Multi-arch from day one** via an OCI image index.
- **Unprivileged** registry I/O via
  [`go-containerregistry`](https://github.com/google/go-containerregistry).

### Non-goals (initially)

- A general-purpose Dockerfile / BuildKit interpreter.
- Supporting npm/yarn/bun lockfiles in v1 (pnpm-lock only).
- Using `pnpm` to populate the **image's** production `node_modules` layers.
- Compiling native addons from source (`node-gyp`) for image dependency layers.
- Running dependency `preinstall` / `install` / `postinstall` / `prepare`
  when materializing image layers (no escape hatch in v1).
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
> dependency lifecycle scripts for image layers. Call `pnpm` only for the host
> app-compile phase when needed.**

```
dir/package.json + pnpm-lock.yaml (+ source)
        │
        ▼
1. Load package.json in dir; locate lock (dir or parents)
   Select importer matching this directory (workspace-aware path)
        │
        ▼
2. App compile phase (when build script configured / detected)  ← may use pnpm
     pnpm install (host, for compile toolchain)
     pnpm run build   (or node-image.buildScript)
     collect outputs (dist/, …)
        │
        ▼
3. Resolve production closure for each target platform          ← Go only
     walk snapshots / dependency edges
     filter optional deps by os/cpu/libc=glibc
     pure-JS → platform=any (shared layers)
        │
        ▼
4. For each package: cache lookup by integrity → else HTTPS fetch → verify SRI
        │
        ▼
5. Extract tarball → store path; write symlink farm + .bin
   (no dependency scripts)
        │
        ▼
6. Pack store layers + symlink layer(s) + app layer (compile outputs)
   HEAD/mount/upload; PUT manifests + index
```

### 5.1 Can image layout be reliable without calling pnpm?

**Yes for the common case**, with sharp edges called out and failed loudly.
(App compile is a separate phase that *may* call pnpm — §8.2.)

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
   is a **test dependency** for layout, and a **runtime dependency only for
   the optional app-compile phase**.

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
| Shell out to `pnpm` for **image** prod `node_modules` | **Rejected for v1** — Go-native layout; pnpm remains layout oracle in tests |
| Shell out to `pnpm` for **app compile** | **Accepted** — do-it-all TypeScript / `scripts.build` |
| `--allow-scripts` on image dep install | **Rejected** — fights multi-arch; no escape hatch in v1 |
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

### 8.2 App build phase (locked: do-it-all may invoke pnpm)

Hermetic **image dependency** layout vs host **app compile** are separate:

1. **Compile (host, may use pnpm):** If the package has a build script
   (`scripts.build` by default, or `node-image.buildScript`), `node-image
   build` runs roughly:
   - `pnpm install` at the lock root / package dir (so `tsc` and friends
     exist — this install may run scripts; it is *not* what gets layered
     into the image),
   - `pnpm run <buildScript>` in the package directory,
   - collect configured outputs (default: `dist/` if present, else
     configurable).
   Requires `pnpm` on `PATH` (or corepack) **when a build script runs**.
   Pure-JS apps with no build script need no pnpm binary.
2. **Image prod deps (Go, no pnpm, no dep scripts):** Always from lock +
   tarball extract for each target platform. This is what becomes store +
   symlink layers — not the host `node_modules` from step 1.
3. **App layer:** compile outputs + root `package.json` (not host
   `node_modules`).
4. Fail closed on `*.ts` entrypoints if build did not produce a runnable JS
   entry, unless opted into a TS-runner base.

`--build=false` / `--skip-build` can skip compile for "I already built"
workflows; default is to build when a script is present.

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
7. App compile phase: invoke `pnpm install` + `pnpm run build`; wire outputs
   into app layer; `--skip-build` escape.
8. Loud diagnostics for dep-scripts/libc/ABI.
9. SBOM from integrities; optional cosign.
10. (Later) patches, more exotic resolutions, musl mode, npm lock backend.

## 11. Remaining open questions (alpha defaults proposed)

These are small enough to lock as defaults in the implementation plan unless
someone objects:

| # | Topic | Proposed alpha default |
|---|-------|------------------------|
| 1 | Virtual store fidelity | Match pnpm closely; CI oracle vs `pnpm install --ignore-scripts --prod` |
| 2 | Lockfile versions | **v9 only**; reject others with guidance |
| 3 | Patches / git / exotic | **Fail if present** |
| 4 | "Needs scripts" heuristic | Fail if non-optional dep has install/postinstall/preinstall and no detectable prebuilds |
| 5 | App build script | Run `scripts.build` when present via `pnpm run build`; configurable; `--skip-build` to opt out |
| 6 | Config key | `"node-image"` in `package.json` |
| 7 | Default base | Distroless Node on Debian (glibc); confirm digest in impl spike |
| 8 | Base pin | Allow tags with warning; docs prefer digest |
| 9 | Entrypoint | `package.json#main`, overridable in config |
| 10 | Success bar | TS app: one command builds+pushes multi-arch; code-only rebuild ≪ deps; dep bump ~one store layer; layout oracle green; image path works without using host `node_modules` |

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
| pnpm binary | not used for **image** dep layout; **used for app compile** when `scripts.build` runs |
| Dep scripts (image layers) | **never** (no `--allow-scripts`) |
| App compile | `pnpm install` + `pnpm run build` inside do-it-all when script present |
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
