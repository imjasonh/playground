# Design: dockerless Node.js / TypeScript image builds

> Status: **Design only** (decisions partially locked — see §0).
> Proposes a `ko`/`pymage`-style Go CLI for Node.js (including TypeScript)
> apps. Nothing here is implemented yet.

## 0. Locked decisions (2026-07-09)

| Topic | Decision |
|-------|----------|
| Package manager | **pnpm only** for v1 (require `pnpm-lock.yaml`) |
| Scripts | Default **`--ignore-scripts`**; aim for hermeticity |
| Layering | **Per-package sharding is v1** (with `auto` bucket fallback under a layer budget) |
| Multi-arch | **Must for v1** (at least `linux/amd64` + `linux/arm64` index) |

Rationale notes:

- **pnpm-only does limit adoption** vs npm-default shops, but it is the right
  constraint for this product: content-addressable store ≈ per-package layers,
  lockfile integrities, first-class `--ignore-scripts`, and
  [`supportedArchitectures`](https://pnpm.io/settings#supportedarchitectures)
  so one host can fetch linux/amd64 *and* linux/arm64 optional deps. Same
  tradeoff as `pymage` requiring `uv`. npm/yarn can be a later backend; v1
  docs should say "bring a pnpm lock" (or `pnpm import`).
- **Hermetic + ignore-scripts + multi-arch reinforce each other.** You cannot
  honestly multi-arch if install scripts compile native code on the host.
  Prebuilds / platform optional packages only.

## 1. Goal

A single **Go CLI** (same family as [`ko`](https://ko.build),
[`pymage`](https://github.com/imjasonh/pymage), [`krust`](https://github.com/imjasonh/krust),
[`jib`](https://github.com/GoogleContainerTools/jib)) that builds and pushes OCI
images for Node.js applications **without a Docker daemon**, and that is fast
because it exploits content-addressed layering:

- **Dependencies are split into reusable per-package layers.** Changing app
  code without changing deps updates only the app layer. Bumping one dependency
  updates only that package's layer (or its bucket under the layer budget).
- **Outside-of-Docker caches are reused** — especially the **pnpm store** and
  locally cached package tarballs — so rebuilds are not cold network fetches.
- **Hermetic by default:** no dependency lifecycle scripts; install layout
  derived from the lock + fetched tarballs.
- **Base image is configurable**, defaulting to a slim distroless/Chainguard
  Node image (e.g. `cgr.dev/chainguard/node`).
- **Multi-arch from day one** via an OCI image index.
- Builds are **unprivileged** and talk to registries via
  [`go-containerregistry`](https://github.com/google/go-containerregistry).

Working name for this doc: **`nok`** ("Node ko"). Naming still open (§11.1).

### Non-goals (initially)

- A general-purpose Dockerfile / BuildKit interpreter.
- Supporting npm/yarn/bun lockfiles in v1 (pnpm only).
- Compiling native addons from source (`node-gyp`) during the image build.
- Electron / browser-extension packaging.
- Inventing a sandbox to safely run arbitrary `postinstall` scripts.

## 2. Why this is worth doing (and why Node is harder than Go/Python)

### 2.1 The shared insight

`ko`, `jib`, and `pymage` all rest on the same OCI facts:

1. Layers are content-addressed (gzip tar digest).
2. Registries support blob existence checks and cross-repo mounts → **zero-byte
   reuse** when a layer digest already exists.
3. A manifest is small JSON. Unchanged deps ⇒ only the app layer + manifest move.

For Node, `node_modules` is often hundreds of MB; app code is small. A dedicated
builder can **shard deps**, reuse the **pnpm store**, and push **only changed
layers** — without a Docker daemon.

### 2.2 Why Node is not "pymage with tarballs"

| Concern | Go (`ko`) | Python (`pymage`) | Node (this proposal) |
|---------|-----------|-------------------|----------------------|
| Artifact | Single static binary | Pre-built wheels | Tree of packages + optional native bits |
| Install = unzip? | N/A | Mostly yes | Layout + symlinks (pnpm virtual store) |
| Build-time code execution | Compiler only | Avoided (wheels-only) | **Default off** (`--ignore-scripts`); fail if compile required |
| Multi-arch | Cross-compile | Per-platform wheels | Per-platform optional deps + shared pure-JS layers |
| Package managers | One (`go`) | `uv` preferred | **pnpm only (v1)** |
| TypeScript | N/A | N/A | Explicit compile step (app scripts, not dep scripts) |

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
| **Bazel [`js_image_layer`](https://github.com/aspect-build/rules_js)** + `rules_oci` | Splits Node toolchain / 3p store / 1p store / symlinks / app — closest sharding story; requires Bazel. **Layout inspiration for pnpm store + link farm.** |
| **Paketo / CNB Node buildpacks** | Lockfile-keyed `node_modules` cache; still a build-container model |
| **Kaniko / Buildah / BuildKit** | General Dockerfile builders |
| **pnpm `deploy` / Docker docs** | Portable prod trees for workspaces; useful for monorepo packaging, not registry-as-cache sharding |

**Conclusion:** niche is real. FTL proved Node dockerless builds; Bazel proved
fine-grained JS layers; pymage is the template. A modern pnpm-native CLI with
per-package layers + multi-arch does not appear to exist.

## 4. Product shape

```
nok build [dir]          # default: .
nok build -t v1.2.3
docker run "$(nok build)"   # index digest; runtime picks platform
```

Config in `package.json` (or `pnpm-workspace.yaml` / dedicated file — TBD):

```json
{
  "name": "myapp",
  "main": "dist/index.js",
  "nok": {
    "repo": "registry.example.com/me/myapp",
    "base": "cgr.dev/chainguard/node@sha256:…",
    "platforms": ["linux/amd64", "linux/arm64"]
  }
}
```

Defaults:

| Knob | Default |
|------|---------|
| Package manager | pnpm (`pnpm-lock.yaml` required) |
| Scripts | `--ignore-scripts` (deps); opt-in `--allow-scripts` escape hatch |
| Base | `cgr.dev/chainguard/node` (docs push digest pins) |
| Platforms | intersection of base image platforms and config; default aim `linux/amd64,linux/arm64` |
| Workdir | `/app` |
| User | non-root from base (or `65532`) |
| Cmd | `["node", "<main>"]` — never `npm`/`pnpm` as PID 1 |
| Production deps only | yes (`--prod`) |
| Layer strategy | `per-package`, with `auto` bucketing when over `max-layers` |
| Max layers | ~127 including base (pymage-aligned; revisit for huge trees) |

Auth: standard Docker keychain via ggcr.

## 5. Recommended architecture: hermetic pnpm fetch + per-package layers

v1 default is **not** "run a normal host install with scripts." It is:

> **From `pnpm-lock.yaml`, fetch package tarballs (reusing the pnpm store),
> materialize a deterministic per-package filesystem layout without lifecycle
> scripts, shard one OCI layer per package, append to the base, and publish a
> multi-arch index.**

```
pnpm-lock.yaml + package.json + source
        │
        ▼
1. Require pnpm; parse lock (importers, packages, snapshots, integrities)
        │
        ▼
2. Resolve per-target-platform closure
     supportedArchitectures / lock os+cpu+libc fields
     pure-JS packages shared across arches
     platform optional deps (e.g. @esbuild/linux-arm64) per arch
        │
        ▼
3. Fetch tarballs into pnpm store (or Go content-addressed cache keyed by
   integrity). Never run dependency lifecycle scripts.
        │
        ▼
4. Optional app build (see §8) — may use a separate full install with
   devDeps; must not poison the production layer set
        │
        ▼
5. For each platform:
     materialize install layout under /app
     one deterministic layer per package (+ link/symlink layer if needed)
     + app layer last
        │
        ▼
6. HEAD/mount/upload blobs; PUT per-arch manifests; PUT image index
```

### 5.1 Two viable materialization strategies

**A. Shell out to pnpm (preferred if "hermeticity is easy")**

Per target platform, in an isolated directory:

```bash
pnpm fetch --prod   # or install with store-dir, frozen lockfile
pnpm install --prod --frozen-lockfile --ignore-scripts \
  --config.supportedArchitectures.os[]=linux \
  --config.supportedArchitectures.cpu[]=x64 \  # or arm64
  --config.supportedArchitectures.libc[]=glibc \
  --modules-dir … --store-dir …
```

Then walk the resulting virtual store + `node_modules` link farm and shard.

- **Pros:** pnpm owns layout correctness; we reuse store cache; less Go code.
- **Cons:** pnpm becomes a hard runtime dependency; must pin/detect pnpm
  version (corepack); determinism depends on pnpm's on-disk layout stability
  across versions; need careful isolation so two platform installs do not
  clobber each other.

**B. Go-native tarball extract (pymage-strict)**

Parse lock → download by integrity → extract each tarball into
`/app/node_modules/.pnpm/<name>@<ver>/node_modules/<name>` (or a simplified
hoisted tree) → synthesize bins/symlinks ourselves.

- **Pros:** strongest hermeticity and bit-stability; multi-arch without
  caring about host arch; no pnpm binary required at build time (only lock).
- **Cons:** reimplementing pnpm layout is non-trivial (peers, bins, nested
  deps, `node_modules/.bin`).

**Recommendation:** start with **A** for layout fidelity, but treat the
**layer input as content-addressed by lock integrity** so we can swap in **B**
later. If pnpm layout proves non-deterministic across minor versions, invest
in B sooner.

### 5.2 What "hermetic" means here

| Allowed | Not allowed (default) |
|---------|------------------------|
| Read lock + package metadata | Run dependency `preinstall` / `install` / `postinstall` |
| Fetch tarballs by integrity into store | `node-gyp rebuild` / compile native code |
| Extract / link files into image layout | Network calls from package scripts |
| Run **app** build script with an explicit, separate policy (§8) | Silent fallback to "just install with scripts" |

If a required package cannot work without scripts (no `prebuildify` /
`node-gyp-build` prebuilds in the tarball, not a pure optional platform
package), **fail fast** with a clear error and document `--allow-scripts` as
an explicit, non-default escape hatch (and note that `--allow-scripts` may
break multi-arch).

### 5.3 Determinism requirements

Layer tarballs must be byte-stable:

- Fixed `mtime` / uid / gid / modes; sorted tar entries; deterministic gzip
  **or** cache compressed blobs by content.
- Stable path prefix under `/app`.
- Package → layer assignment: one layer per package identity
  `(name, version, integrity)`; when over budget, bucket by `hash(name)`.
- Symlinks preserved as symlinks with stable targets (do not follow into
  duplicate file copies unless using a dedicated "store layer + link layer"
  split like Bazel).
- Exclude junk: `**/.cache`, VCS dirs, optional `**/*.map`.

Cache key:

```
(package-name, version, integrity, layout-version, platform-or-any)
```

Pure-JS packages use `platform=any` and are **shared** across the multi-arch
index (same blob digest referenced from each arch manifest).

## 6. Alternatives (secondary)

### 6.A Host install with scripts (rejected as default)

Fastest path to "apps just work," but fights hermeticity and multi-arch.
Kept only as `--allow-scripts` escape hatch.

### 6.B Bundle-first (esbuild → one file)

Different product. Optional later (`--bundle`), not default.

### 6.C Coarse two-layer (containerify)

`--layer-strategy=single-deps-layer` fallback only.

## 7. Layering strategy (v1)

| Strategy | Behavior |
|----------|----------|
| `per-package` | Headline path: one layer per package |
| `auto` (default knobs) | `per-package` while under `max-layers`; else name-hash buckets (pymage-style) so one dep bump touches one bucket |
| `single-deps-layer` | Escape hatch |

**Suggested physical split** (inspired by Bazel `js_image_layer`):

1. **Store layers** — one per package contents under the virtual store path
   (content-addressed; maximum reuse).
2. **Link / `node_modules` layer(s)** — symlink farm + `.bin` (changes when
   the dependency *graph* changes even if package bytes do not).
3. **App layer** — last: `dist/` / configured output + root `package.json`.

If implementing the full store/link split is too much for alpha, v1 can ship
**one layer per package including its link edges** at the cost of slightly
worse reuse when only the graph changes — but still far better than a monolith
`node_modules` layer.

**App layer last**, never re-embedding deps.

## 8. TypeScript and app builds

Tension: hermetic **dependency** installs vs apps that need `tsc` / bundlers
(**devDependencies** + running the app's own scripts).

Proposed model:

1. **Production image closure** is always built with `--ignore-scripts --prod`.
2. **App compile** is a separate phase:
   - If `nok.buildScript` / `--build` / `scripts.build` is enabled, run a
     **dev install** (may allow scripts only for the root package, still
     prefer `--ignore-scripts` for deps) → run build → take outputs
     (`dist/`, etc.).
   - Then materialize the **production** dep layers from the lock (no
     devDeps) + app output layer.
3. Fail closed on `*.ts` entrypoints without a build unless the user opts into
   a TS-runner base.

Framework-specific graphs (Next standalone, etc.) are **out of scope for
alpha** — "bring your build output path" via config.

## 9. Multi-arch (v1 requirement)

### 9.1 How it works with pnpm

For each target platform `linux/<arch>`:

1. Set `supportedArchitectures` to that os/cpu/libc (and/or rely on lock
   platform fields).
2. Compute the package closure; fetch any missing tarballs (optional deps for
   that arch).
3. Build arch-specific image (shared pure-JS layers by digest; unique layers
   for platform packages).
4. Publish an **OCI image index** listing both manifests.

This matches pymage's "pure wheels shared, platform wheels per arch" model.

### 9.2 Native addons policy under multi-arch

| Package kind | Multi-arch behavior |
|--------------|---------------------|
| Pure JS | One shared layer |
| Optional platform package (`@esbuild/linux-x64`, …) | Per-arch layer; fetched via `supportedArchitectures` |
| `prebuildify` / in-tarball `prebuilds/` | Shared layer; runtime picks `.node` |
| Needs `node-gyp` at install time | **Build fails** unless `--allow-scripts` (and then multi-arch is best-effort / same-arch only) |

Detect base image Node major (env / apko metadata) and **hard-error** on
mismatch with the lock's expected engine when native prebuilds are present.

### 9.3 libc

Chainguard/Wolfi bases are musl-ish/apk; many native optional packages publish
`glibc` vs `musl` variants. **Must validate** `supportedArchitectures.libc`
against the base (or document "glibc Node base only" / "Chainguard Node is X").
This is an easy footgun — treat as a first-class check, not an afterthought.

## 10. Implementation sketch (Go)

```
nok/
├── go.mod
├── README.md
├── DESIGN.md
├── internal/
│   ├── lock/       # pnpm-lock.yaml parser (v6/v9 as needed)
│   ├── fetch/      # integrity-addressed tarball cache; optional pnpm store interop
│   ├── install/    # invoke pnpm ignore-scripts + supportedArchitectures, or Go layout
│   ├── layer/      # per-package deterministic tar + auto buckets
│   ├── app/        # dist/source layer + ignores
│   ├── base/       # manifest/config, Node version + libc detect
│   └── publish/    # ggcr assemble, mount/push, image index
└── testdata/       # small pnpm apps: pure JS, optional platform dep, TS build
```

Phased delivery (aligned to locked decisions):

1. Deterministic tar helpers + push single-arch app-on-base (smoke).
2. pnpm lock parse + fetch/store reuse + **ignore-scripts** prod install.
3. **Per-package layers** + registry HEAD/mount reuse demo.
4. **Multi-arch index** with `supportedArchitectures` + shared pure-JS blobs.
5. App build phase for TypeScript.
6. Fail-fast diagnostics for script-requiring / ABI / libc mismatches.
7. SBOM from lock integrities; optional cosign.
8. (Later) Go-native layout; npm backend; `--allow-scripts` hardening.

## 11. Remaining open questions

### 11.1 Naming & home

1. Name: `nok`? `pnpmage`? something else?
2. Standalone repo (like pymage) vs incubate in this playground?

### 11.2 Hermetic mechanics

3. Materialization **A (shell out to pnpm)** vs **B (Go extract)** for alpha?
4. Is `--allow-scripts` in v1 at all, or omit until someone screams?
5. Pin pnpm via **corepack** / `packageManager` field — hard requirement?

### 11.3 Layout

6. Full **store layers + symlink layer** (Bazel-like) in v1, or simpler
   per-package tars of the visible tree?
7. Default `max-layers` 127 — OK for Node's wide trees, or start lower/higher?
8. Hoist (`node-linker=hoisted`) for simpler images, or embrace default
   isolated linker?

### 11.4 TypeScript / workspaces

9. Auto-run `scripts.build` when present, or require explicit opt-in?
10. Monorepos: require `pnpm deploy --filter=…`, a `--filter` flag, or
    single-package repos only for alpha?

### 11.5 Base / runtime

11. Hard-require base digest, or allow tags with a loud warning?
12. libc policy for default Chainguard Node — confirm musl/glibc story and
    which optional native packages we claim to support.
13. Default entry: always `node <main>`, with `main` resolved how
    (`package.json#main` vs `nok.entrypoint` vs `bin`)?

### 11.6 Success bar for alpha

14. Demo: TS API on pnpm, multi-arch push to ttl.sh/ghcr, second build after
    one-line edit uploads ≪ full deps; bump one dep uploads ~one layer.

## 12. Risks

- **pnpm-only adoption ceiling** — mitigated by `pnpm import` docs; accept for v1.
- **`--ignore-scripts` breaks popular packages** — fail with actionable errors;
  track a compatibility allowlist of known-good patterns (prebuildify, pure JS,
  platform optional deps).
- **libc / Node ABI skew** vs Chainguard base — detect and fail.
- **pnpm layout non-determinism** across pnpm versions — pin pnpm; cache by
  integrity; golden tests.
- **Symlink farms** copied wrong → broken images — integration tests that
  actually `node -e "require('…')"` in a container per arch.
- **Layer explosion** — `auto` bucketing must be default-on when over budget.
- **App build vs hermetic deps** — keep phases strictly separated.

## 13. Decision summary (coding defaults)

| Decision | Default |
|----------|---------|
| Name | `nok` (placeholder) |
| Lockfile | `pnpm-lock.yaml` required |
| Dep scripts | ignored (`--ignore-scripts`) |
| Layering | per-package (+ auto bucket under max-layers) |
| Multi-arch | yes — image index, shared pure-JS layers |
| Install driver | shell out to pnpm first; Go-native layout later if needed |
| TS | explicit build phase; prod layers stay script-free |
| Base | `cgr.dev/chainguard/node` (prefer digest) |
| Cmd | `["node", "<main>"]` |
| Escape hatch | `--allow-scripts` (optional in alpha; disables multi-arch guarantees) |
| Repo home | TBD (lean standalone, like pymage) |

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
