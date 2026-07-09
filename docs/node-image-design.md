# Design: `node-image` — dockerless Node.js / TypeScript image builds

> Status: **Design only** (see §0 for locked decisions).
> Proposes a `ko`/`pymage`-style Go CLI for Node.js (including TypeScript)
> apps. Nothing here is implemented yet.

## 0. Locked decisions

| Topic | Decision |
|-------|----------|
| Name / home | **`node-image`**, as a Go app in **this repo** (`node-image/`) |
| Package manager | **pnpm only** for v1 (require `pnpm-lock.yaml`) |
| Scripts | Default **`--ignore-scripts`**; aim for hermeticity |
| Layering | **Per-package store layers + symlink/`node_modules` layer(s)** in v1; `auto` bucket fallback under a layer budget |
| Multi-arch | **Must for v1** (at least `linux/amd64` + `linux/arm64` index) |
| libc | Target **glibc by default**; **loud fail** if the app/lock needs musl-only native artifacts (or if the chosen base is not glibc) |
| Install driver | Shell out to pnpm for v1; Go-native extract is a later optimization (explained in §5.1) |
| CLI shape | One easy do-it-all command for the common case; optional finer commands underneath |
| `--allow-scripts` | Omit from alpha unless needed; it fights multi-arch (explained in §9.4) |

Rationale notes:

- **pnpm-only** is the same tradeoff as `pymage` requiring `uv`: content-addressable
  store ≈ per-package layers, lock integrities, `--ignore-scripts`, and
  [`supportedArchitectures`](https://pnpm.io/settings#supportedarchitectures)
  for multi-arch fetches from one host. Docs: bring a pnpm lock (or `pnpm import`).
- **Hermetic + ignore-scripts + multi-arch reinforce each other.** Install
  scripts that compile native code on the host cannot produce correct
  linux/amd64 *and* linux/arm64 artifacts from one machine.
- **glibc default:** most published native optional packages (`@esbuild/*`,
  `@swc/*`, etc.) center on glibc. Prefer a glibc Node base by default
  (Chainguard/Wolfi may be wrong here — pick a known-glibc default, allow
  override). If the lock or base implies musl and we cannot satisfy it,
  fail with an actionable error rather than shipping a broken image.

## 1. Goal

A single **Go CLI**, `node-image`, that builds and pushes OCI images for
Node.js applications **without a Docker daemon**, in the spirit of
[`ko`](https://ko.build), [`pymage`](https://github.com/imjasonh/pymage),
[`krust`](https://github.com/imjasonh/krust), and
[`jib`](https://github.com/GoogleContainerTools/jib):

- **Dependencies are split into reusable per-package layers** (store contents)
  plus a thin **symlink / `node_modules` layer**. Changing app code updates
  only the app layer; bumping one dependency updates that package's layer
  (or its bucket under the layer budget).
- **Outside-of-Docker caches are reused** — especially the **pnpm store**.
- **Hermetic by default:** no dependency lifecycle scripts.
- **Configurable base**, defaulting to a slim **glibc** Node image.
- **Multi-arch from day one** via an OCI image index.
- **Unprivileged** registry I/O via
  [`go-containerregistry`](https://github.com/google/go-containerregistry).

### Non-goals (initially)

- A general-purpose Dockerfile / BuildKit interpreter.
- Supporting npm/yarn/bun lockfiles in v1 (pnpm only).
- Compiling native addons from source (`node-gyp`) during the image build.
- Electron / browser-extension packaging.
- Inventing a sandbox for arbitrary `postinstall` scripts.

## 2. Why this is worth doing (and why Node is harder than Go/Python)

### 2.1 The shared insight

`ko`, `jib`, and `pymage` rest on the same OCI facts:

1. Layers are content-addressed (gzip tar digest).
2. Registries support blob existence checks and cross-repo mounts → **zero-byte
   reuse** when a layer digest already exists.
3. A manifest is small JSON. Unchanged deps ⇒ only the app layer + manifest move.

For Node, `node_modules` is often hundreds of MB; app code is small. A dedicated
builder can **shard deps**, reuse the **pnpm store**, and push **only changed
layers** — without a Docker daemon.

### 2.2 Why Node is not "pymage with tarballs"

| Concern | Go (`ko`) | Python (`pymage`) | Node (`node-image`) |
|---------|-----------|-------------------|---------------------|
| Artifact | Single static binary | Pre-built wheels | Package tree + optional native bits |
| Install = unzip? | N/A | Mostly yes | Layout + symlinks (pnpm virtual store) |
| Build-time code execution | Compiler only | Avoided (wheels-only) | **Default off** (`--ignore-scripts`); fail if compile required |
| Multi-arch | Cross-compile | Per-platform wheels | Per-platform optional deps + shared pure-JS layers |
| Package managers | One (`go`) | `uv` preferred | **pnpm only (v1)** |
| TypeScript | N/A | N/A | Explicit compile step (app build, not dep scripts) |

## 3. Prior art

Nothing currently ships as a maintained, `ko`-like, per-dependency-sharded Node
builder. Closest options:

### 3.1 Direct ancestors / siblings

| Project | What it does | Gap vs this goal |
|---------|--------------|------------------|
| **[FTL](https://github.com/GoogleCloudPlatform/runtimes-common/tree/master/ftl)** (Google, ~2018) | Dockerless Node/Python/PHP builders; registry-as-cache | Abandoned; predates modern pnpm |
| **[`pymage`](https://github.com/imjasonh/pymage)** | Per-wheel layers, `uv.lock`, Go + ggcr | Python-only; closest design template |
| **[`ko`](https://ko.build)** / **[`krust`](https://github.com/imjasonh/krust)** | Compile → one layer on base | Single-artifact languages |
| **[Jib](https://github.com/GoogleContainerTools/jib)** | Java deps layered separately from classes | Classpath ≠ `node_modules` |

### 3.2 Node-specific dockerless tools

| Project | What it does | Gap |
|---------|--------------|-----|
| **[containerify](https://github.com/eoftedal/containerify)** | Base + one deps layer + app layer; no daemon | Coarse layering; assumes pre-installed tree |
| **[nodejs-container-image-builder](https://github.com/google/nodejs-container-image-builder)** | Node library to append files and push | Library; no sharding |
| **[tko](https://github.com/dskiff/tko)** | `(base) + (artifacts) → push` | Language-agnostic |

### 3.3 Related but different

| Project | Relevance |
|---------|-----------|
| **Bazel [`js_image_layer`](https://github.com/aspect-build/rules_js)** + `rules_oci` | Splits Node toolchain / 3p store / 1p store / symlinks / app — **layout inspiration for store + link farm layers** |
| **Paketo / CNB Node buildpacks** | Lockfile-keyed `node_modules` cache; build-container model |
| **Kaniko / Buildah / BuildKit** | General Dockerfile builders |
| **pnpm `deploy` / Docker docs** | Portable prod trees for workspaces (see §8.2) |

**Conclusion:** niche is real. A modern pnpm-native CLI with per-package layers
+ multi-arch does not appear to exist.

## 4. Product shape

### 4.1 The easy path (do-it-all)

```
node-image build [dir]           # build + push; prints image ref by digest
node-image build -t v1.2.3
docker run "$(node-image build)"
```

`node-image build` is the common case: resolve lock → fetch → (optional app
compile) → shard layers → push multi-arch index. One command, like `ko build`
/ `pymage build`.

### 4.2 Optional finer commands

Multiple commands are fine underneath for power users / CI caching, e.g.:

| Command (illustrative) | Role |
|------------------------|------|
| `node-image build` | **Do-it-all** (default UX) |
| `node-image fetch` | Populate store / local tarball cache from lock |
| `node-image pack` | Build OCI layout / tarball without push |
| `node-image push` | Push an already-packed image |

Alpha can ship only `build` if the others are not needed yet.

### 4.3 Config

In `package.json` (key name TBD — `node-image` or `nodeImage`):

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
| Package manager | pnpm (`pnpm-lock.yaml` required) |
| Scripts | `--ignore-scripts` for dependencies |
| libc target | **glibc**; fail loudly on musl-only requirements |
| Base | Known-**glibc** slim/distroless Node image (not assumed Chainguard/Wolfi); overrideable |
| Platforms | `linux/amd64,linux/arm64` when the base supports them |
| Workdir | `/app` |
| User | non-root from base (or `65532`) |
| Cmd | `["node", "<main>"]` — never `npm`/`pnpm` as PID 1 |
| Production deps only | yes (`--prod`) |
| Layer strategy | store per-package + symlink layer(s); `auto` buckets when over `max-layers` |
| Max layers | ~127 including base |

Auth: standard Docker keychain via ggcr.

## 5. Architecture: hermetic pnpm fetch + store/symlink layers

> **From `pnpm-lock.yaml`, fetch package tarballs (reusing the pnpm store),
> materialize a deterministic layout without lifecycle scripts, emit one OCI
> layer per store package plus symlink/`node_modules` layer(s) plus an app
> layer, append to the base, and publish a multi-arch index.**

```
pnpm-lock.yaml + package.json + source
        │
        ▼
1. Require pnpm; parse lock (importers, packages, snapshots, integrities)
        │
        ▼
2. Resolve per-target-platform closure (os/cpu/libc=glibc)
     pure-JS packages shared across arches
     platform optional deps per arch
     fail if musl-only native artifacts are required
        │
        ▼
3. Fetch tarballs into pnpm store / content-addressed cache (by integrity)
   Never run dependency lifecycle scripts
        │
        ▼
4. Optional app build phase (§8) — separate from prod dep layers
        │
        ▼
5. For each platform:
     materialize layout under /app
     store layers (one per package) + symlink/node_modules layer(s) + app layer
        │
        ▼
6. HEAD/mount/upload blobs; PUT per-arch manifests; PUT image index
```

### 5.1 What "Go-native extract" means (vs shelling out to pnpm)

Two ways to turn lock → files on disk:

**A. Shell out to pnpm (v1 choice)**  
Run `pnpm install --prod --frozen-lockfile --ignore-scripts` with
`supportedArchitectures` set for the target platform, pointed at an isolated
store/modules dir. pnpm downloads tarballs, unpacks them into its virtual
store, and writes the symlink farm. `node-image` then **reads that tree** and
packs layers.

- Pros: pnpm owns layout correctness (peers, bins, nesting).
- Cons: hard dependency on a pnpm binary/version; layout stability tied to
  pnpm releases.

**B. Go-native extract (later optimization — "pymage-strict")**  
`node-image` itself (in Go) parses the lock, downloads each tarball by
`integrity` URL, unpacks the npm package tarball into the correct store path,
and writes the symlinks/bins **without calling pnpm**. Same end state, but
the builder owns every byte (like pymage unpacking wheels in Go instead of
calling `uv pip install`).

- Pros: no pnpm binary at build time; tighter bit-stability; easier to reason
  about cache keys.
- Cons: reimplementing pnpm's layout rules is real work.

**v1:** A. Keep B as a future swap-in behind the same layer cache keys
`(name, version, integrity, layout-version, platform-or-any)`.

### 5.2 Hermeticity

| Allowed | Not allowed (default) |
|---------|------------------------|
| Read lock + package metadata | Dependency `preinstall` / `install` / `postinstall` |
| Fetch tarballs by integrity | `node-gyp rebuild` / compile native code |
| Extract / link into image layout | Network calls from package scripts |
| Run **app** build under a separate policy (§8) | Silent fallback to scripted installs |

If a required package cannot work without scripts (no in-tarball prebuilds,
not a pure optional platform package), **fail fast** with a clear error.

### 5.3 Determinism

- Fixed `mtime` / uid / gid / modes; sorted tar entries; deterministic gzip
  **or** cache compressed blobs by content.
- Stable `/app` prefix.
- Store package → layer by `(name, version, integrity)`; over budget → bucket
  by `hash(name)`.
- Symlinks preserved as symlinks with stable targets (store + link split).
- Exclude junk: `**/.cache`, VCS dirs, optional `**/*.map`.

Pure-JS packages use `platform=any` and are **shared** across the multi-arch
index (same blob digest in each arch manifest).

## 6. Alternatives (secondary)

### 6.A Host install with scripts (rejected as default)

Fights hermeticity and multi-arch. Not in alpha.

### 6.B Bundle-first (esbuild → one file)

Different product. Optional later (`--bundle`), not default.

### 6.C Coarse two-layer (containerify)

`--layer-strategy=single-deps-layer` escape hatch only.

## 7. Layering strategy (v1): store + symlink

Inspired by Bazel `js_image_layer`:

| Layer kind | Contents | Changes when… |
|------------|----------|---------------|
| **Store (per package)** | Files for one package under the virtual store path | That package version/integrity changes |
| **Symlink / `node_modules`** | Symlink farm, `.bin`, graph edges into the store | Dependency *graph* changes (even if package bytes do not) |
| **App** (last) | Build output (`dist/`, …) + root `package.json` | App source / build output changes |

Knobs:

| Strategy | Behavior |
|----------|----------|
| `per-package` + symlink (default path) | Headline v1 |
| `auto` | Per-package while under `max-layers`; else name-hash buckets for store layers |
| `single-deps-layer` | Escape hatch |

App layer never re-embeds deps.

## 8. TypeScript, app builds, and workspaces

### 8.1 App build phase

Hermetic **dependency** installs vs apps that need `tsc` / bundlers:

1. **Production dep layers** always from `--ignore-scripts --prod`.
2. **App compile** is a separate phase inside the do-it-all `build` when a
   build script is configured:
   - Dev install as needed → run build → take outputs (`dist/`, etc.).
   - Prod dep layers still script-free.
3. Fail closed on `*.ts` entrypoints without a build unless the user opts into
   a TS-runner base.

Framework-specific graphs (Next standalone, etc.) are out of scope for alpha —
configure the output path.

### 8.2 What "workspaces / `pnpm deploy`" means

A **pnpm workspace** is a monorepo: one root `pnpm-workspace.yaml`, many
packages (`apps/api`, `packages/ui`, …), one lockfile. Dependencies can be
workspace-local (`"foo": "workspace:*"`).

For containers you usually want **one image per app package**, not one image
of the whole monorepo. pnpm's
[`pnpm deploy --filter=<pkg> --prod <dir>`](https://pnpm.io/cli/deploy)
copies that package plus its dependency closure into a **portable directory**
(localized store + `node_modules`), which is what people put in Docker images.

For `node-image`, the question is how alpha handles monorepos:

| Option | Meaning |
|--------|---------|
| **Single-package only** | Project root is the app; no workspace support yet |
| **`--filter=<pkg>`** | Build image for one workspace package (like `pnpm --filter`) |
| **Use `pnpm deploy` as input** | Shell out to `deploy`, then shard the deployed tree |

**Recommendation for alpha:** support a repo root that is a single package;
add `--filter` (and/or deploy) as soon as the single-package path works.
Document the monorepo path explicitly so we do not pretend `node-image build`
at a workspace root "does the right thing" for all packages.

## 9. Multi-arch, libc, and why scripts fight multi-arch

### 9.1 Multi-arch flow

For each target `linux/<arch>`:

1. Resolve closure with `supportedArchitectures` → linux + cpu + **libc=glibc**.
2. Fetch missing tarballs (optional platform packages for that arch).
3. Build arch-specific image (shared pure-JS store layers by digest; unique
   layers for platform packages; arch-specific symlink layer if needed).
4. Publish an **OCI image index**.

### 9.2 Native addons policy

| Package kind | Multi-arch behavior |
|--------------|---------------------|
| Pure JS | One shared store layer |
| Optional platform package (`@esbuild/linux-x64`, …) | Per-arch store layer |
| `prebuildify` / in-tarball `prebuilds/` | Shared layer; runtime picks `.node` |
| Needs `node-gyp` at install time | **Build fails** with a clear error |

Detect base image Node major (env / metadata) and **hard-error** on mismatch
when native prebuilds are in play.

### 9.3 libc policy (locked)

- Default target: **glibc**.
- Default base: a **glibc** Node image (distroless Debian Node or similar).
  Do **not** silently default to a musl/Wolfi base without verifying.
- If the lock requires musl-only native artifacts (or the user selects a musl
  base while the closure is glibc-oriented): **fail loudly** with guidance
  (change base, change deps, or wait for an explicit musl mode later).
- Override path later: `--libc musl` + matching base, same fail-loud rules in
  reverse.

### 9.4 Why `--allow-scripts` fights multi-arch

Dependency lifecycle scripts often **compile or download for the host they
run on**:

- `node-gyp rebuild` produces a `.node` binary for **this machine's**
  OS/CPU/libc — not for every platform in the image index.
- Some install scripts download a single prebuild based on `process.arch`
  at install time.
- Running scripts once on an arm64 Mac cannot honestly populate
  `linux/amd64` and `linux/arm64` images with correct native bits.

So if scripts are allowed:

- multi-arch either becomes **same-arch only**, or
- you need a **per-arch build environment** (VMs/qemu) — i.e. you have
  reinvented "build inside containers," which this tool is trying to avoid.

Hermetic + ignore-scripts keeps multi-arch as "fetch the right optional
packages / prebuilds for each arch from the registry," which *does* work from
one host — the pymage/wheels model.

## 10. Implementation sketch (this repo)

Per playground Go-app conventions (`go.mod` at module root, no repo-root
Go module):

```
node-image/
├── go.mod
├── go.sum
├── README.md
├── .gitignore
├── main.go                 # or cmd/node-image/
├── internal/
│   ├── lock/               # pnpm-lock.yaml parser
│   ├── fetch/              # integrity-addressed cache; pnpm store interop
│   ├── install/            # pnpm --ignore-scripts + supportedArchitectures
│   ├── layer/              # store per-package tar + symlink layer + buckets
│   ├── app/                # dist/source layer + ignores
│   ├── base/               # manifest/config, Node version + libc detect
│   └── publish/            # ggcr assemble, mount/push, image index
└── testdata/               # pure JS, optional platform dep, TS build
```

Phased delivery:

1. Module skeleton + deterministic tar + push app-on-base (single-arch smoke).
2. pnpm lock parse + fetch/store + **ignore-scripts** prod install.
3. **Store per-package layers + symlink layer** + registry HEAD/mount reuse.
4. **Multi-arch index** + glibc checks + shared pure-JS blobs.
5. App build phase folded into do-it-all `build`.
6. Loud diagnostics: scripts required, libc mismatch, Node ABI mismatch.
7. SBOM from lock integrities; optional cosign.
8. (Later) Go-native extract; npm backend; musl mode; workspace `--filter`.

## 11. Remaining open questions

### 11.1 Defaults to pick with a spike (not product forks)

1. Exact **default glibc base image** ref (distroless Node? node:*-slim?
   Chainguard glibc variant if one exists) — choose after checking libc + Node
   version metadata signals.
2. Pin pnpm via **corepack** / `packageManager` field — hard requirement?
3. Default `max-layers` 127 — confirm against a realistically wide pnpm tree.

### 11.2 Product polish

4. Auto-run `scripts.build` when present vs require explicit
   `node-image.buildScript` / flag? (Do-it-all `build` should still feel
   magical for the common TS case.)
5. Config key: `"node-image"` in `package.json` vs `node-image.yaml`?
6. Hard-require base digest vs allow tags with a warning?
7. How `main` / entrypoint is resolved (`package.json#main` vs config vs `bin`).

### 11.3 Workspaces timing

8. Alpha = single-package only, with `--filter` / `pnpm deploy` in the next
   milestone? (Recommended yes.)

### 11.4 Success bar for alpha

9. Demo: TS API on pnpm, multi-arch push, second build after one-line edit
   uploads ≪ full deps; bump one dep uploads ~one store layer.

## 12. Risks

- **pnpm-only adoption ceiling** — accept for v1; document `pnpm import`.
- **`--ignore-scripts` breaks popular packages** — actionable errors; track
  known-good patterns (prebuildify, pure JS, platform optional deps).
- **Wrong default base libc** — verify before shipping; fail loud on mismatch.
- **pnpm layout non-determinism** across versions — pin pnpm; golden tests.
- **Symlink farms** packed wrong — integration tests that run
  `node -e "require('…')"` per arch in a container.
- **Layer explosion** — `auto` bucketing when over budget.
- **App build vs hermetic deps** — keep phases separated inside do-it-all.

## 13. Decision summary

| Decision | Default |
|----------|---------|
| Name / location | `node-image/` in this repo |
| Lockfile | `pnpm-lock.yaml` required |
| Dep scripts | ignored |
| Layering | store per-package + symlink layer(s) (+ auto buckets) |
| Multi-arch | yes — image index, shared pure-JS layers |
| libc | glibc default; loud fail on musl-only needs |
| Install driver | shell out to pnpm (Go-native extract later) |
| CLI | `node-image build` do-it-all; optional subcommands later |
| TS | build phase inside do-it-all; prod layers stay script-free |
| Workspaces | single-package alpha; `--filter` next |
| Cmd | `["node", "<main>"]` |
| `--allow-scripts` | not in alpha |

## 14. References

- [pymage README / DESIGN](https://github.com/imjasonh/pymage)
- [ko](https://ko.build)
- [Jib](https://github.com/GoogleContainerTools/jib)
- [FTL (Google runtimes-common)](https://github.com/GoogleCloudPlatform/runtimes-common/tree/master/ftl)
- [containerify](https://github.com/eoftedal/containerify)
- [tko](https://github.com/dskiff/tko)
- [google/nodejs-container-image-builder](https://github.com/google/nodejs-container-image-builder)
- [aspect `js_image_layer`](https://github.com/aspect-build/rules_js) / [rules_oci JS docs](https://github.com/bazel-contrib/rules_oci/blob/main/docs/javascript.md)
- [pnpm `supportedArchitectures`](https://pnpm.io/settings#supportedarchitectures)
- [pnpm `deploy`](https://pnpm.io/cli/deploy) / [pnpm + Docker](https://pnpm.io/docker)
- [Paketo Node.js reference](https://paketo.io/docs/reference/nodejs-reference/)
- Stack Overflow: [Equivalent of Google's Jib for Node.JS?](https://stackoverflow.com/questions/61598311/equivalent-of-googles-jib-for-node-js)
