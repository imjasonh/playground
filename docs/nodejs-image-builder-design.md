# Design: dockerless Node.js / TypeScript image builds

> Status: **Design only.** This document proposes a `ko`/`pymage`-style CLI for
> Node.js (including TypeScript) apps. Nothing here is implemented yet. Open
> questions in §11 are meant to steer the first cut.

## 1. Goal

A single **Go CLI** (same family as [`ko`](https://ko.build),
[`pymage`](https://github.com/imjasonh/pymage), [`krust`](https://github.com/imjasonh/krust),
[`jib`](https://github.com/GoogleContainerTools/jib)) that builds and pushes OCI
images for Node.js applications **without a Docker daemon**, and that is fast
because it exploits content-addressed layering:

- **Dependencies are split into reusable layers.** Changing app code without
  changing deps updates only the app layer. Bumping one dependency updates only
  that dependency's layer (or its bucket).
- **Host / package-manager caches are reused.** The tool should not force a
  cold `npm install` inside a container when the developer or CI runner already
  has a warm cache.
- **Base image is configurable**, defaulting to a slim distroless/Chainguard
  Node image (e.g. `cgr.dev/chainguard/node`).
- Builds are **unprivileged** and talk to registries via
  [`go-containerregistry`](https://github.com/google/go-containerregistry)
  (HEAD / mount / upload), like `ko` and `pymage`.

Working name for this doc: **`nok`** ("Node ko"). Naming is an open question
(§11.1).

### Non-goals (initially)

- A general-purpose Dockerfile / BuildKit interpreter.
- Replacing npm/yarn/pnpm/bun as the dependency *resolver* — we consume lockfiles
  (and optionally shell out to the package manager for install).
- Guaranteeing every package with a native `node-gyp` build works hermetically
  on day one (see §6).
- Electron / browser-extension packaging.
- Running the app's `postinstall` / `prepare` scripts inside an untrusted sandbox
  we invent.

## 2. Why this is worth doing (and why Node is harder than Go/Python)

### 2.1 The shared insight

`ko`, `jib`, and `pymage` all rest on the same OCI facts:

1. Layers are content-addressed (gzip tar digest).
2. Registries support blob existence checks and cross-repo mounts → **zero-byte
   reuse** when a layer digest already exists.
3. A manifest is small JSON. Unchanged deps ⇒ only the app layer + manifest move.

For Node, the payoff is the same as for Python: `node_modules` is often hundreds
of MB; app code is small. Today most Node Dockerfiles either:

- invalidate `npm ci` on every source change (slow), or
- carefully order `COPY package*.json` → `npm ci` → `COPY .` (better, but still
  one giant deps layer, and still requires a Docker daemon / BuildKit).

A dedicated builder can do better: **shard deps**, reuse the **host install
cache**, and push **only changed layers**.

### 2.2 Why Node is not "pymage with tarballs"

| Concern | Go (`ko`) | Python (`pymage`) | Node (this proposal) |
|---------|-----------|-------------------|----------------------|
| Artifact | Single static binary | Pre-built wheels | Tree of packages + optional compile |
| Install = unzip? | N/A | Mostly yes | **No** — layout, hoisting, symlinks, bins |
| Build-time code execution | Compiler only | Avoided (wheels-only) | **Common** (`postinstall`, `node-gyp`) |
| Multi-arch | Cross-compile | Per-platform wheels | Per-platform optional deps + native addons |
| Package managers | One (`go`) | Several, `uv` preferred | **npm / yarn / pnpm / bun**, incompatible layouts |
| TypeScript | N/A | N/A | Needs an explicit compile step |

The design must pick a stance on **who runs install** and **what happens to
lifecycle scripts / native addons**. That choice dominates everything else.

## 3. Prior art

Nothing currently ships as a maintained, `ko`-like, per-dependency-sharded Node
builder. Closest options:

### 3.1 Direct ancestors / siblings

| Project | What it does | Gap vs this goal |
|---------|--------------|------------------|
| **[FTL](https://github.com/GoogleCloudPlatform/runtimes-common/tree/master/ftl)** (Google, ~2018) | Dockerless Node/Python/PHP builders; registry-as-cache; language-aware layers | Effectively abandoned; Node FTL predates lockfile-first npm, pnpm, workspaces |
| **[`pymage`](https://github.com/imjasonh/pymage)** | Per-wheel layers, `uv.lock`, Go + ggcr | Python-only; wheels-only model does not map cleanly to npm |
| **[`ko`](https://ko.build)** / **[`krust`](https://github.com/imjasonh/krust)** | Compile → one layer on base | Single-artifact languages; no dep sharding needed |
| **[Jib](https://github.com/GoogleContainerTools/jib)** | Java deps layered separately from classes | Maven/Gradle classpath model ≠ `node_modules` |

### 3.2 Node-specific dockerless tools

| Project | What it does | Gap |
|---------|--------------|-----|
| **[containerify](https://github.com/eoftedal/containerify)** | Pull base, add `package.json`+lock+`node_modules` as **one** layer, app as another; push; no Docker daemon | Coarse layering (any dep change rebuilds whole deps layer); assumes you already ran install; JS implementation |
| **[nodejs-container-image-builder](https://github.com/google/nodejs-container-image-builder)** | Node library to append files to a base and push | Library, not a CLI; no dep sharding / lock awareness |
| **[tko](https://github.com/dskiff/tko)** | `(base) + (artifacts) → push` | Language-agnostic; you bring a finished tree; no Node layering |

### 3.3 Related but different

| Project | Relevance |
|---------|-----------|
| **Bazel [`js_image_layer`](https://github.com/aspect-build/rules_js)** + `rules_oci` | Splits into ~5 layers (Node toolchain, 3p store, 1p store, `node_modules` symlinks, app). Closest *sharding* story in production — but requires Bazel. |
| **Paketo / CNB Node buildpacks** | Cache `node_modules` keyed on lockfile; still run install in a build container; not a local unprivileged CLI. |
| **Kaniko / Buildah / BuildKit** | General Dockerfile builders; daemonless-ish, but not Node-specialized and still "run Dockerfile steps". |
| **apko + melange** | Declarative apk → OCI; Node apps would need packaging as apk first. |
| **Optimized Dockerfiles** | Multi-stage + `COPY package*.json` + BuildKit cache mounts — good practice, still Docker-centric, one deps layer. |

**Conclusion:** the niche is real. FTL proved the idea for Node years ago;
`containerify` covers the coarse dockerless case; Bazel covers fine layering
inside a heavy toolchain. A modern `pymage`-shaped CLI for everyday npm/pnpm
apps does not appear to exist.

## 4. Proposed product shape

```
nok build [dir]          # default: .
nok build -t v1.2.3
docker run "$(nok build)"
```

Config in `package.json` (idiomatic for Node tooling), e.g.:

```json
{
  "name": "myapp",
  "main": "dist/index.js",
  "nok": {
    "repo": "registry.example.com/me/myapp",
    "base": "cgr.dev/chainguard/node:latest",
    "platforms": ["linux/amd64", "linux/arm64"]
  }
}
```

(Exact key name — `nok` vs `ko`-style `.ko.yaml` vs `package.json#nok` — TBD.)

Defaults (proposed):

| Knob | Default |
|------|---------|
| Base | `cgr.dev/chainguard/node` (pin by digest in docs) |
| Workdir | `/app` |
| User | non-root from base (or `65532`) |
| Entrypoint / Cmd | `node` + resolved main / `package.json#main` / configured entry |
| Production deps only | yes (`omit=dev`) |
| Layer strategy | `auto` (per-package until layer budget, then name-hash buckets) — same idea as pymage |
| Max layers | ~127 including base |

Auth: standard Docker keychain via ggcr (same as `ko`/`pymage`).

## 5. Recommended architecture: hybrid "host install + deterministic shard"

After comparing pure-hermetic vs host-install approaches (§6), the recommended
**v1** is:

> **Let the package manager produce `node_modules` on the host (reusing its
> cache), then have `nok` deterministically shard that tree into OCI layers and
> push.**

```
package.json + lockfile + source
        │
        ▼
1. Detect package manager (lockfile / packageManager field)
        │
        ▼
2. Ensure production install on host
     npm ci --omit=dev   |  pnpm install --prod  |  yarn workspaces focus …
     (skip if node_modules already matches lock — optional verify)
        │
        ▼
3. Optional app build
     npm run build   (or configured script: tsc / esbuild / next build …)
        │
        ▼
4. Inventory installable units
     each top-level package in node_modules (and nested where not hoisted),
     or each pnpm store package + link graph
        │
        ▼
5. Shard into deterministic layers (per-package or hashed buckets)
   + app/source layer (dist/ + package.json, excluding node_modules)
        │
        ▼
6. Append to base (by digest), rewrite config, HEAD/mount/upload, PUT manifest
```

### Why this hybrid for v1

- **Reuses outside-of-Docker build cache** — the user's explicit goal. `npm`/`pnpm`
  local stores stay warm; CI cache dirs (`~/.npm`, pnpm store) keep working.
- **Lifecycle scripts and native addons mostly "just work"** on the host the
  same way they do for local `npm ci`, without reimplementing npm in Go.
- **Layer sharding still delivers registry-side reuse** — the part Docker
  Dockerfiles cannot do well (per-dep layers + blob mounts).
- **TypeScript fits naturally**: run the project's build script on the host,
  package `dist/` (or configured output) as the app layer.

### What we still make deterministic

Even when install runs on the host, **layer tarballs must be byte-stable**:

- Fixed `mtime` / uid / gid / modes; sorted tar entries; deterministic gzip
  (or cache compressed blobs by content).
- Stable path prefix (`/app/node_modules/...`).
- Stable assignment of packages → layer buckets (hash of package name, like
  pymage).
- Ignore junk: `**/.cache`, `**/*.map` (configurable), VCS dirs, nested
  `.git`.

Cache key for a dep layer roughly:

```
(package-name, version, resolved-integrity-from-lock, layout-version, platform)
```

If integrity matches and the layer blob exists in the registry → mount, no upload.

## 6. Alternative approaches (and why they're secondary)

### 6.A Hermetic tarball install in Go (pymage-strict)

Download each package tarball from the lock (`resolved` + `integrity`), extract
into a layout we control, **never run lifecycle scripts**.

- **Pros:** hermetic, multi-arch friendly, no host Node required for deps,
  closest to pymage.
- **Cons:** reinventing install layout (especially pnpm); native addons that
  need `node-gyp` fail; packages that *require* `postinstall` break; large
  engineering surface.
- **Fit:** strong **v2 / strict mode** for pure-JS apps and for CI that wants
  "no scripts". Fail fast when a package needs compile and no prebuild is in
  the tarball.

### 6.B Bundle-first (esbuild/rollup → one JS file)

Compile the app (+ deps) into a single artifact, then `ko`-style one layer.

- **Pros:** tiny images, trivial layering, multi-arch if pure JS.
- **Cons:** different product (bundler semantics, dynamic `require`, native
  addons); not "ship node_modules".
- **Fit:** optional mode later (`--bundle`), not the default.

### 6.C Coarse two-layer (containerify)

`node_modules` one layer + app one layer.

- **Pros:** small implementation; already exists (containerify).
- **Cons:** misses the "small dependency change → small layer change" goal.
- **Fit:** `--layer-strategy=single-deps-layer` fallback, not the headline.

## 7. Layering strategy (detail)

Mirror pymage's knobs:

| Strategy | Behavior |
|----------|----------|
| `auto` (default) | One layer per package while under `max-layers`; else bin-pack by hash(name) → K buckets |
| `per-package` | One layer per package, no cap |
| `single-deps-layer` | All deps in one layer |

**App layer last**, containing:

- Built output (`dist/`, `.next/standalone`, etc. — configurable)
- Root `package.json` (and lockfile if useful for diagnostics)
- Non-`node_modules` runtime files the app needs
- Explicitly **not** re-including deps

**pnpm note:** pnpm's content-addressable store + symlink farm is awkward for
naive per-directory tarring (symlinks must resolve inside the image). Options:

1. Prefer `node-linker=hoisted` / `shamefully-hoist` for images (simpler tree).
2. Or emit layers as (store packages) + (symlink/`node_modules` structure)
   similar to Bazel's `js_image_layer` split — more correct, more work.

**npm/yarn hoisting:** nested duplicates of the same version should map to the
**same** layer digest when integrity matches (content-addressed), even if
linked from multiple paths — either via hardlink-aware tar or by putting the
package once and relying on Node's resolution (harder). v1 can tar the real
tree as-is (simpler, some duplication) and optimize later.

## 8. TypeScript and "build" integration

Node apps are often not runnable as raw `src/`. Proposed model:

1. Config key `build` / `package.json#scripts.build` — if present, `nok` runs it
   (or a configured script name) **before** packaging, on the host, with the
   already-installed (possibly full, including devDeps) tree.
2. Practical flow for TS:
   - install **all** deps (including dev) → `npm run build` → prune / reinstall
     production-only → shard production `node_modules` + `dist/`.
   - Or: two-phase like multi-stage Dockerfiles, but both phases on the host.
3. Entrypoint defaults to `node dist/index.js` or `package.json#main` after
   build.

Open question: should `nok` refuse to package `*.ts` entrypoints without a
build, or allow `tsx`/ts-node bases? Recommendation: **fail closed** unless
base clearly includes a TS runner and user opts in.

## 9. Base image, Node ABI, and native addons

- Default base: **Chainguard Node** (or distroless node). Document digest
  pinning.
- Detect Node major/minor from the base (image env / apko metadata / `node -p`
  if we ever exec — prefer metadata) and **warn/fail** if host install used a
  different major (native `.node` binaries are ABI-sensitive).
- Native addons:
  - **Best case:** `prebuildify` / bundled `prebuilds/` → works with
    `--ignore-scripts` and hermetic mode.
  - **Common case:** `postinstall` downloads or builds → needs host install
    mode and matching libc/arch (building linux/arm64 deps on macOS amd64 is
    a problem).
- Multi-arch: for v1, either
  - require building on each arch (or in qemu/CI matrix), or
  - support hermetic mode only for pure-JS closures on multi-arch.

This is the largest practical footgun vs pymage (which can fetch
`manylinux` wheels from any host).

## 10. Implementation sketch (Go)

New top-level module (name TBD), mirroring `pymage` / playground Go apps:

```
nok/                     # or whatever name
├── go.mod
├── README.md
├── DESIGN.md            # this doc, or link to docs/
├── cmd/nok/             # or main at root like pymage
├── internal/
│   ├── lock/            # parse package-lock v2/v3, pnpm-lock, yarn
│   ├── install/         # shell out to npm/pnpm/yarn; verify
│   ├── layout/          # walk node_modules → package units
│   ├── layer/           # deterministic tar + bucket strategy
│   ├── app/             # source/dist layer + ignore rules
│   ├── base/            # pull manifest/config, Node version detect
│   └── publish/         # ggcr assemble, HEAD/mount/push, index
└── testdata/
```

Phased delivery:

1. Deterministic tar + push app files onto configurable base (tko-like MVP).
2. Single deps layer from existing `node_modules` (containerify parity).
3. Per-package / auto bucket sharding + local layer cache.
4. Lock-aware install orchestration (`npm ci` / pnpm) + production omit.
5. Build-script hook for TypeScript.
6. Multi-arch index (pure-JS / hermetic path first).
7. Optional hermetic `--ignore-scripts` tarball mode.
8. SBOM from lockfile integrities; optional cosign.

## 11. Open questions (please steer)

### 11.1 Naming & home

1. Name: `nok`? `npmage`? `nodeko`? something else?
2. Live as its own GitHub repo (like `pymage`/`krust`) or as a playground Go
   app under this monorepo first?

### 11.2 Install model (load-bearing)

3. Confirm **host install + shard** as v1 default? Or prefer **hermetic
   tarball / no scripts** from day one (narrower app compatibility, stronger
   reproducibility story)?
4. Should `nok` invoke the package manager itself, or require the user to
   present a finished `node_modules` (containerify-style) and only package?
5. Which package managers are in-scope for v1: **npm only**, npm+pnpm, or all
   of npm/yarn/pnpm/bun?

### 11.3 TypeScript / build

6. Always run `scripts.build` when present, or require explicit
   `nok.buildScript` / `--build`?
7. After build, how aggressive should pruning be (`npm prune --omit=dev` vs
   reinstall prod-only vs leave it to the user)?
8. First-class support for frameworks with non-obvious output graphs
   (Next.js standalone, Nest, Remix)? Or "bring your `dist/`" only?

### 11.4 Layering & layout

9. Is per-package layering the headline feature, or is "deps layer + app
   layer" enough for v1 with sharding as v2?
10. For pnpm: require hoisted linker for images, or invest in store+symlink
    layers up front?
11. Layer budget default: pymage's 127, or something smaller for Node
    (registry/runtime pain with thousands of micro-packages)?

### 11.5 Native addons & multi-arch

12. Accept that **multi-arch v1 = CI matrix / same-arch only** when native
    addons are present?
13. Fail the build if any dependency has an `install`/`postinstall` script
    unless `--allow-scripts` (secure default) — or allow scripts by default
    because otherwise too many apps break?
14. Should matching host Node major to base Node major be a hard error?

### 11.6 Runtime contract

15. Default base image tag vs digest policy (float `latest` with warning, or
    require digest)?
16. Default command: `node <main>` vs `npm start` (signal handling argues
    against npm as PID 1)?
17. Monorepos / workspaces: build one workspace package at a time
    (`--filter`), or whole repo?

### 11.7 Success metrics

18. What makes this "done" for an alpha: containerify feature parity, or
    pymage-style per-dep reuse demo on a real app (e.g. Express + a few
    native-free deps)?
19. Target demo story: `nok build && docker run …` on a TypeScript API, with
    a second build after a one-line code change uploading ≪ full
    `node_modules`?

## 12. Risks

- **Reimplementing or trusting install incorrectly** → subtle runtime
  differences vs local `node_modules`.
- **Non-determinism** in tar/gzip silently killing layer reuse.
- **Script / RCE surface** if hermetic mode later shells out carelessly.
- **ABI skew** between build host and base image Node.
- **pnpm symlink semantics** producing broken images if followed or not
  followed wrongly.
- **Layer explosion** on apps with 1k+ transitive packages → need `auto`
  bucketing defaults that are good out of the box.
- **Competing with "just use a good Dockerfile + BuildKit cache"** — the
  differentiator must be clear: **no daemon + per-dep registry reuse + host
  cache**.

## 13. Suggested decision defaults (if we want to start coding)

Until the questions above are answered, proposed defaults for an alpha:

| Decision | Default |
|----------|---------|
| Name | `nok` (placeholder) |
| Install | Host `npm ci --omit=dev` when `package-lock.json` present; else fail with guidance |
| Package managers v1 | npm only (lockfile v2/v3) |
| Layering | `auto` buckets, deps + app |
| Scripts | Allow install scripts on host; document risk |
| TS | Run `build` script if defined; package `dist/` if it exists else `.` |
| Base | `cgr.dev/chainguard/node` (document digest pin) |
| Cmd | `["node", "<main>"]` — never `npm start` as PID 1 |
| Multi-arch | Single platform = host arch, unless pure lock + hermetic mode |
| Repo home | Standalone repo (like pymage), design doc can live here until then |

## 14. References

- [pymage README / DESIGN](https://github.com/imjasonh/pymage)
- [ko](https://ko.build)
- [Jib](https://github.com/GoogleContainerTools/jib)
- [FTL (Google runtimes-common)](https://github.com/GoogleCloudPlatform/runtimes-common/tree/master/ftl)
- [containerify](https://github.com/eoftedal/containerify)
- [tko](https://github.com/dskiff/tko)
- [google/nodejs-container-image-builder](https://github.com/google/nodejs-container-image-builder)
- [aspect `js_image_layer`](https://github.com/aspect-build/rules_js) / [rules_oci JS docs](https://github.com/bazel-contrib/rules_oci/blob/main/docs/javascript.md)
- [Paketo Node.js reference](https://paketo.io/docs/reference/nodejs-reference/)
- Stack Overflow: [Equivalent of Google's Jib for Node.JS?](https://stackoverflow.com/questions/61598311/equivalent-of-googles-jib-for-node-js)
