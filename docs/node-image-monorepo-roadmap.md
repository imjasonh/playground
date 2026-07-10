# Roadmap: `node-image` for real-world pnpm monorepos

> Status: **planning only** — no implementation in this doc.
> Companion to [`node-image-design.md`](./node-image-design.md) and
> [`node-image-implementation-plan.md`](./node-image-implementation-plan.md).
>
> Alpha (M0–M7) shipped a hermetic, multi-arch builder for **simple** pnpm v9
> apps. A gap analysis against a large production monorepo (hundreds of
> importers, thousands of packages, private registries, workspace packages,
> patches, overrides, catalogs, git deps, fat custom bases) showed that alpha
> is not yet sufficient for that class of app. This document is the plan to
> close those gaps.

## 0. Framing

### What alpha already gets right

Keep these as invariants unless a phase explicitly revisits them:

- **Go-native image dep layout** from the lock (no `pnpm` for image
  `node_modules`).
- **Never run arbitrary dependency lifecycle scripts** as the default path
  (multi-arch safety).
- **Store + symlink + app** layering with content-addressed caches.
- **Directory = importer filter** (point at the package to image).
- **Production-only closure** (no `devDependencies` in the image).
- **Stdout = one image ref**; progress on stderr (ko-style).

### What the gap analysis changes

Several alpha “fail if present” / “out of scope” choices become **required
features** for monorepo adoption. A few locked decisions need a **narrow
revisit** (scripts escape hatch, custom bases that are not distroless Node,
app output globs, CI cache portability). The rest are extensions of the
existing pipeline.

### Success bar (end state)

Point `node-image build` at a workspace package in a large monorepo and get a
runnable multi-arch image that:

1. Resolves **only that importer’s prod closure** from a 300+ importer lock.
2. Materializes **workspace / link / directory** packages into the virtual
   store (deploy-like), without publishing internals.
3. Honors **catalogs**, **overrides**, and **patchedDependencies** as recorded
   in the lock.
4. Fetches **private-registry** and **git** tarballs with auth + integrity.
5. Packages **pre-built app outputs** (`--skip-build` as the primary CI path)
   including non-`dist/` trees and non-JS assets.
6. Appends Node layers onto an **arbitrary fat glibc base** with configurable
   `PATH` / `ENTRYPOINT` / `CMD` / `WORKDIR`.
7. Fits under the **~127 layer** budget with stable, change-local buckets and
   **zero-byte** reuse of unchanged store layers on push.
8. Fails with a **single report** of all unsupported features, not the first
   one only.

---

## 1. Gap inventory → workstreams

Map every identified gap to a workstream. Priority within a stream follows
dependency order, not the original “worst to best” list alone — some “worse”
items unblock others.

| # | Gap | Workstream | Phase |
|---|-----|------------|-------|
| G1 | `pnpm.patchedDependencies` | Lock fidelity | P1 |
| G2 | `workspace:` / `link:` / `directory` deps | Deploy-like closure | P1 |
| G3 | `catalog:` + lockfile catalogs | Lock fidelity | P1 |
| G4 | `pnpm.overrides` | Lock fidelity | P1 |
| G5 | Git / non-registry resolutions | Fetch & auth | P2 |
| G6 | Private registry auth (npm `_authToken`) | Fetch & auth | P2 |
| G7 | Prebuild-aware natives (`prebuilds/`, `node-gyp-build`) | Natives policy | P2 |
| G8 | Escape hatch for compile-from-source packages | Natives policy | P2 |
| G9 | Optional platform filtering parity with pnpm | Resolve & platforms | P1 |
| G10 | Configurable app output dirs / globs | App packaging | P1 |
| G11 | Non-JS runtime assets in app layer | App packaging | P1 |
| G12 | `--skip-build` as primary external-compile contract | App packaging | P1 |
| G13 | Workspace-aware deploy-like closure + `.bin` | Deploy-like closure | P1 |
| G14 | Smarter bucketing under ~127 layers | Layer economics | P3 |
| G15 | Stable symlink / `node_modules` layer splitting | Layer economics | P3 |
| G16 | Cross-repo mount / existence checks on push | Layer economics | P3 |
| G17 | Content-addressed caches that survive CI | CI & cache | P3 |
| G18 | Custom base without distroless Node assumptions | Runtime config | P2 |
| G19 | Config for `CMD` / multi-entrypoint | Runtime config | P1 |
| G20 | Multi-arch × native optional deps (lock-scale) | Resolve & platforms | P2 |
| G21 | Importer selection in huge lockfiles | Lock fidelity | P1 |
| G22 | pnpm 9/10 lock quirks (peers, extensions, URLs) | Lock fidelity | P1 |
| G23 | Deterministic, reproducible digests | Hardening | P3 |
| G24 | Better failure UX (enumerate all unsupported) | Hardening | P0 |
| G25 | npm auth for fetch + push (Buildkite/ECR, ko-like) | Fetch & auth | P2 |

---

## 2. Decision revisits (before coding)

Alpha locked a few choices that block monorepo adoption. Resolve these in
design before implementation:

### D1 — Patches: apply, don’t only reject

**Alpha:** fail if `patchedDependencies` present.  
**Monorepo need:** apply lock-recorded patches at extract (or accept
pre-patched tarballs whose integrity matches the lock).  
**Decision:** **Apply patches during spool extract.** Prefer the lock’s patch
file + hash; verify post-patch content against lock integrity when the lock
records a patched integrity. Document that patch application is hermetic
(no network, no scripts) — only file transforms from the recorded patch.

### D2 — Workspace / link / directory: materialize, don’t reject

**Alpha:** reject `workspace:` / `link:` / `file:` on resolve.  
**Design §5.1 already foreshadowed** copy-from-source for workspace/link.  
**Decision:** **Materialize workspace packages into the virtual store** as
content-addressed “local packages” (files from the workspace tree, or a
pack-equivalent subset), with store paths and symlink edges matching pnpm’s
deploy layout. This is the Go equivalent of `pnpm --filter <pkg> --prod
deploy`. Do **not** shell out to `pnpm deploy` for the image path (keeps
hermeticity); use pnpm deploy only as a **conformance oracle** in tests.

### D3 — Catalogs & overrides: resolve from the lock, don’t re-resolve

**Alpha:** reject catalogs/overrides at parse.  
**Decision:** Treat the lock as source of truth. Catalogs are already
**expanded into concrete versions** on importer edges / package keys in a
properly written lock — parse and walk those. Overrides similarly appear as
the resolved graph in `packages` / `snapshots`. Implementation work is:

1. Stop rejecting the lock sections.
2. Ensure resolve walks the **already-overridden** snapshot graph.
3. Add fixtures where catalog/override presence would previously hard-fail
   even when the closure is ordinary registry tarballs.
4. Only fail if a catalog specifier remains **unexpanded** on an edge we must
   follow (malformed / unsupported lock shape).

### D4 — Scripts policy: keep default “never”; add a narrow allowlist

**Alpha:** no `--allow-scripts` (design §9.4).  
**Monorepo need:** packages like `sqlite3` that need `binding.gyp` with no
usable prebuild.  
**Decision (revisited):**

| Path | Policy |
|------|--------|
| Default | Still **never** run dep scripts |
| Preferred fixes | Vendored prebuilt tarball; replace package; platform optionalDeps; patch to ship prebuilds |
| Escape hatch | **`--allow-scripts <name[@range],…>`** (and/or `node-image.allowScripts`) — **named allowlist only**, never `--allow-scripts=true` for the whole tree |
| Multi-arch | Allowlisted scripts run **per target platform** in an isolated host/CI environment that matches that platform (document: cross-arch scripted installs require a matching builder or pre-vendored artifacts). If the builder cannot produce the other arch, fail that arch rather than silently shipping a host-arch binary |

This is a deliberate exception to alpha §9.4, scoped so the default path stays
hermetic.

### D5 — Custom bases: append app+deps; don’t assume `/nodejs/bin/node`

**Alpha:** default entrypoint `/nodejs/bin/node` (distroless layout).  
**Monorepo need:** fat glibc bases (Node/Nsolid + Chrome, system libs, etc.).  
**Decision:**

- `node-image.base` may be **any** OCI image (glibc still required unless
  musl mode exists later).
- Config must set `entrypoint`, `cmd`, `env.PATH`, `workdir`, `user`
  explicitly when the base is non-distroless.
- Optional: detect Node on `PATH` in the base and default entrypoint to
  `["node"]` when `/nodejs/bin/node` is absent.
- Still validate libc / `engines.node` when detectable; skip Node-path
  assumptions when overridden.

### D6 — App packaging: globs + skip-build first

**Alpha:** collect `dist/` or root `index.js`; compile via pnpm by default.  
**Monorepo need:** `build/` (and arbitrary trees), lua/templates/proto assets,
CI that already ran turbo/esbuild/prisma/NAPI.  
**Decision:**

- `node-image.include` / `exclude` globs (default keep today’s `dist/` +
  root fallbacks for back-compat).
- `--skip-build` (and config `skipBuild: true`) is a **first-class primary
  path**, not an escape hatch — document the “external compile contract”:
  host/CI produces outputs; `node-image` only packs + hermetic deps.
- Do-it-all compile remains for small apps; large monorepos should skip it.

### D7 — Failure UX: diagnose-all before fail

**Decision:** On lock/resolve validation, **collect** all unsupported or
blocking features (patches-not-applied-yet during rollout, workspace edges,
git deps, scripted natives, missing auth) into one stderr report, then exit
non-zero. Never fail only on the first finding when more exist.

---

## 3. Phased delivery

Phases are sequenced so each leaves the tool more useful on real monorepos
without requiring the entire roadmap. Within a phase, ship behind clear
errors until the feature is complete (no silent half-support).

```
P0  Diagnostics & parse hardening
P1  Monorepo lock + deploy-like layout + app packaging
P2  Auth, git, natives escape, custom runtime
P3  Layer economics, CI cache, reproducibility polish
```

---

### Phase 0 — Diagnostics & parse hardening

**Goal:** Make large locks inspectable and failures actionable before adding
features. Unblocks every later phase.

#### Work

1. **Unsupported-feature report (G24)**  
   Replace fail-fast `checkUnsupported` with a collector:
   - patches, overrides, catalogs, git, directory/link, workspace edges,
     missing integrity, scripted natives (when detectable at plan time).
   - Print a structured summary (counts + examples + hints).
   - Exit code non-zero if any **blocking** item remains; allow
     `--explain-lock` (or `node-image diagnose`) that always exits 0 after
     printing the report for CI triage.

2. **Importer-scoped validation (G21)**  
   Today, exotic packages **anywhere** in the lock can fail the parse even
   if unused by the selected importer. Change to:
   - Parse the full lock leniently (record exotic metadata).
   - **Hard-fail only on packages reachable from the selected importer’s
     prod closure** (or on lock-global settings that affect that closure,
     e.g. patches that apply to a reachable package).
   - Unused git/directory packages elsewhere must not block the build.

3. **pnpm 9/10 quirk inventory (G22)**  
   Document and fixture:
   - Peer-suffixed snapshot keys (already partly handled).
   - `packageExtensions` (ignore if already baked into lock graph; fail if
     we would need to re-apply).
   - Patched resolution hashes / integrity fields.
   - Tarball URL hosts that differ from `registry.npmjs.org` (Cloudsmith /
     org caches) — prefer lock `resolution.tarball` over derived URLs.

4. **Lock size / performance baseline**  
   Add a synthetic or anonymized large-lock fixture (or generate in test)
   and benchmark parse + resolve. Target: closure resolve for one importer
   must not be accidentally O(all packages × all importers) in the hot path.

#### Exit criteria

- `node-image diagnose <dir>` (or build with report mode) lists every blocker
  for a monorepo package in one shot.
- Pointing at an importer whose closure is “simple” succeeds even if the
  sibling importers use git/patches.
- Parse+resolve of a 6k-package lock completes in acceptable CI time (set a
  concrete budget once benchmarked; track regressions in tests).

---

### Phase 1 — Monorepo lock fidelity, deploy-like closure, app packaging

**Goal:** The common monorepo path works: workspace packages + catalogs +
overrides + patches + configurable outputs + skip-build + multi-CMD config.
This is the largest product jump.

#### 1.A Lock fidelity (G1, G3, G4, G21, G22)

| Feature | Approach |
|---------|----------|
| **Catalogs** | Stop rejecting. Walk expanded versions from importer/snapshot edges. Fail only on unresolved `catalog:` literals in the selected closure. |
| **Overrides** | Stop rejecting. Trust snapshot graph; add tests that override changes the closed package id/integrity. |
| **Patches** | Load `patchedDependencies` + patch files from the workspace. After spool extract (or on a copy), apply patch; verify integrity when the lock provides a post-patch hash. Cache spool key = `integrity` (patched). |
| **Importer selection** | Keep directory→importer key; add explicit optional `--importer` only if path mapping is ambiguous. Ensure 300+ importer locks don’t load unused importer graphs into the closure walk. |

**Fixtures:** catalog-only app; override pins a transitive dep; patched
`ms`-style (flip `testdata/patched` from reject to apply); large-lock
importer isolation.

#### 1.B Deploy-like workspace closure (G2, G13)

This is the core monorepo feature.

**Model (pnpm deploy equivalent, Go-native):**

1. Resolve prod closure for the target importer (incl. optional, platform-
   filtered).
2. For each `workspace:` / `link:` / `directory` edge:
   - Locate the package directory in the workspace.
   - Determine files to include (respect package `files` if present;
     otherwise a conservative pack-like set: package contents minus
     `node_modules`, VCS, tests — exact rules TBD against pnpm pack/deploy
     oracle).
   - Assign a stable virtual-store identity (name + version from that
     package’s `package.json`, plus content hash for layer addressability).
3. Inject those packages into the store layer set like registry packages.
4. Wire snapshot-equivalent symlink edges and `.bin` links so Node
   resolution matches a `pnpm deploy --prod` tree.
5. Do **not** require publishing workspace packages to a registry.

**Conformance:** For fixtures, compare against
`pnpm --filter <pkg> deploy --prod <outdir>` (or `pnpm deploy`) on file
digests + symlink targets for the store subset that node-image emits.

**Non-goals in P1:** copying the entire workspace source into the image;
devDependency workspace links; building workspace packages’ TypeScript as
part of dep materialization (that remains the external compile / skip-build
contract — workspace packages should already be built, or be pure JS, or be
bundled into the app outputs).

#### 1.C Platform optional filtering parity (G9)

Audit `resolve` against pnpm’s `os` / `cpu` / `libc` / `supportedArchitectures`
behavior:

- Skip darwin/win32 optionals on `linux/amd64` and `linux/arm64`.
- Optional→required upgrade: keep fail-loud when the required package is
  platform-incompatible (already started).
- Ensure skipped optionals don’t appear in store layers or symlink farms.
- Fixture: lock with darwin-only optional; linux build must not fetch it and
  must not fail.

#### 1.D App packaging (G10, G11, G12, G19)

Config additions under `"node-image"`:

```json
{
  "node-image": {
    "skipBuild": true,
    "include": ["build/**", "package.json"],
    "exclude": ["**/*.map", "**/*.ts"],
    "main": "build/index.js",
    "cmd": ["build/index.js"],
    "commands": {
      "api": ["build/index.js"],
      "worker": ["build/workerTemporal.js"]
    }
  }
}
```

| Knob | Behavior |
|------|----------|
| `include` / `exclude` | Glob sets for the app layer; default remains `dist/**` + root fallbacks |
| `skipBuild` | Config equivalent of `--skip-build`; preferred in monorepo CI |
| `cmd` / `main` | Already exist — document multi-entrypoint via separate images or tags |
| `commands` (optional) | Named entrypoints: `node-image build --command worker` selects `commands.worker` as Cmd (same layers, different config). Alternative: document “build twice with different `-t` and `cmd`” if named commands are deferred |

**External compile contract (document in README):**

1. CI runs turbo/esbuild/prisma/NAPI/etc.
2. Outputs land in configured `include` paths.
3. `node-image build --skip-build` packs those files + hermetic prod deps.
4. node-image does **not** re-run generators inside the image.

#### 1.E Phase 1 exit criteria

- Workspace app with ~N internal packages images without `pnpm deploy`.
- Catalog + override + patch fixtures green.
- App layer can ship `build/` + lua/templates/proto-like assets via globs.
- `--skip-build` documented as the monorepo-default path.
- Diagnose report is empty (or warnings-only) for the representative
  monorepo’s **supported** subset once P1 features land.

---

### Phase 2 — Fetch/auth, git deps, natives, custom runtime

**Goal:** Reach private registries and awkward natives; run on fat bases.

#### 2.A Private registry auth (G6, G25)

- Read npm-style auth the way users already configure CI:
  - project/user `.npmrc` (`//host/:_authToken`, `registry=`, scoped
    `@scope:registry=`)
  - env `NPM_TOKEN` / `NODE_AUTH_TOKEN` conventions where unambiguous
- Use that auth **only for package tarball HTTPS fetches** (not for OCI
  push — OCI keeps Docker/ggcr keychain).
- Never log tokens; never write tokens into image layers.
- Document Buildkite/ECR setup: npm creds for fetch, Docker/ECR creds for
  push (same split ko uses for GOPROXY vs registry).

#### 2.B Git / GitHub archive deps (G5)

- Support `resolution.type: git` (and GitHub codeload / archive URLs) when
  the lock provides integrity (or a reproducible resolved commit +
  integrity).
- Fetch → verify → spool like registry tarballs.
- Auth: HTTPS with token from `.npmrc` / `GIT_CONFIG` / `GITHUB_TOKEN` as
  documented; prefer lock-provided tarball URLs over live `git clone` when
  available.
- Still fail on floating refs without integrity.

#### 2.C Natives policy (G7, G8, G20)

1. **Strengthen prebuild detection:** `prebuilds/`, `node-gyp-build`,
   known patterns that work at runtime without scripts (bcrypt/sharp-class).
2. **Allowlist escape hatch (D4):** `--allow-scripts` named packages; per-arch
   execution rules; clear errors when allowlisted package lacks a binary for
   the target arch.
3. **Document replace/patch path** for packages that will never be
   allowlist-friendly in multi-arch CI.
4. **Multi-arch × optionals:** integration test on a lock that pulls
   `@img/sharp-linux-x64` / `arm64` (or similar) and asserts per-arch store
   layer membership.

#### 2.D Custom base & runtime config (G18, G19)

- Relax assumptions that the base contains `/nodejs/bin/node`.
- Config-driven `entrypoint`, `cmd`, `env`, `workdir`, `user`, and optional
  `pathPrefix` / `env.PATH`.
- Validate: glibc still required; warn if base has no detectable Node when
  entrypoint is defaulted.
- Multi-entrypoint: finish `commands` map or equivalent flags from P1.

#### 2.E Phase 2 exit criteria

- Fetch succeeds against an authenticated private registry fixture (httptest
  mock with Bearer).
- At least one git-resolution fixture builds.
- Fat-base smoke: append layers onto a non-distroless Node image; container
  runs with configured Cmd.
- Allowlisted scripted package either builds per-arch or fails with an
  explicit arch message — never ships the wrong arch binary silently.

---

### Phase 3 — Layer economics, CI cache, reproducibility

**Goal:** Make ~1.5k-package closures fast to rebuild and cheap to push; make
caches CI-portable; harden determinism.

#### 3.A Bucketing under the layer cap (G14)

Today: FNV-32a(`package.Name`) `% slots` when over budget. Fine for demos;
painful at 1.5k packages (coarse invalidation).

**Plan:**

1. Keep per-package layers while `storePackages ≤ slots`.
2. When over budget, use a **tunable fan-out** strategy:
   - Default: hash(`name`) into `N` buckets (N = store slots).
   - Config: `node-image.layerBuckets` / `--layer-buckets` to set N explicitly
     within budget.
   - **Hot list:** `node-image.unbucketed: ["react", "lodash", …]` — named
     packages always get their own layer (consume slots first); remainder
     fill hash buckets. Lets teams pin high-churn deps.
3. Stability rule: bucket assignment depends only on package **name** (and
   hot-list config), not integrity — so a version bump changes one bucket’s
   bytes without reshuffling membership.
4. Benchmark: measure “one dep bump → how many store layers change” on a
   synthetic 1.5k graph; set a regression threshold.

#### 3.B Symlink layer splitting (G15)

A single giant symlink/`node_modules` layer rewrites on any graph edge
change. Mitigations (pick after spike):

- **A.** Split symlink layer into a few stable shards (e.g. by first letter /
  hash of top-level link name) — small constant number of layers from the
  reserved budget.
- **B.** Keep one symlink layer but ensure it stays small (symlinks only;
  no file bodies) so rewrite cost is dominated by manifest, not upload size.
- **C.** Hybrid: root `.bin` + direct deps in one thin layer; store-internal
  links stay inside store layers (already partly true).

Prefer **B + C** first (simpler); add **A** only if measured push cost
demands it.

#### 3.C Registry mount / existence checks (G16)

Core ko/pymage value: unchanged layers → **zero-byte** uploads via cross-repo
mount / blob HEAD.

- Audit `publish` for explicit existence check + mount before PUT.
- Integration test against a registry that supports mounts; assert second
  push of unchanged store layers uploads ~0 bytes of blob body.
- Document registries that lack mount support (fallback: still skip PUT if
  HEAD shows digest exists in the **same** repo).

#### 3.D CI-surviving content-addressed caches (G17)

Today: `~/.cache/node-image/{packages,spool,layers}` on one machine.

**Plan:**

- Keep local layout; add optional **cache mirror** directory or tarball
  import/export:
  - `NODE_IMAGE_CACHE` / `--cache-dir`
  - `node-image cache export|import` **or** document “cache dir is the unit
    of Buildkite/S3 restore” (prefer dir-based; fewer custom formats).
- Keys remain integrity / DiffID — restore is just files in the right paths.
- Document Buildkite `cache` paths and S3 sync examples.
- Do not require a network cache protocol in-process for v1 of this phase.

#### 3.E Determinism & hardening (G23)

- Digest-pinned bases in docs and examples; warn on floating tags (exists).
- Stable tar metadata audit (mtime/uid/gid/order/gzip) — extend tests.
- No host leakage: strip user names, local paths, mtimes from layer
  contents; refuse absolute symlinks (exists); scrub build metadata.
- Reproducible digest test: two builds on clean caches → identical index
  digest for fixed inputs.

#### 3.F Phase 3 exit criteria

- Synthetic 1.5k-package closure fits in budget; single dep bump changes
  ≤ small N store layers (threshold TBD from spike).
- Second push of unchanged image is near-zero blob upload (mount/HEAD).
- CI restore of `--cache-dir` skips re-fetch/recompress for warm integrities.
- Reproducible digest test green.

---

## 4. Cross-cutting concerns

### 4.1 Testing strategy upgrades

| Kind | Purpose |
|------|---------|
| Unit | Patch apply, catalog/override parse, glob include/exclude, bucket hot-list, auth header injection |
| Conformance | Layout vs `pnpm install --ignore-scripts --prod` **and** vs `pnpm deploy --prod` for workspace fixtures |
| Integration | Private registry mock; git tarball mock; fat-base run; multi-arch sharp-like optionals; layer mount byte counts |
| Scale | Generated large lock (importers × packages) for resolve perf + bucketing |
| Diagnose | Snapshot stderr reports for multi-blocker locks |

Grow `testdata/` with positive-path fixtures (not only rejects):
`patched-apply/`, `workspace-deploy/`, `catalog-app/`, `override-app/`,
`git-dep/`, `build-globs/`, `custom-base/` (where feasible offline).

### 4.2 Documentation updates (when implementing)

- Revise design §0 / §6 / §9.4 for D1–D7 decision revisits.
- README: monorepo quickstart (`--skip-build`, include globs, workspace,
  auth, custom base).
- New doc section: **External compile contract** and **Deploy-like layout**.
- Keep alpha implementation plan as historical; this roadmap is the v2
  track.

### 4.3 What stays explicitly out of scope (for now)

- npm / yarn / bun lock backends
- Full musl mode (unless a later phase needs it)
- Shelling out to `pnpm` to populate **image** `node_modules`
- Electron / browser-extension packaging
- SBOM / cosign (nice-to-have; can follow P3)
- Interpreting Dockerfiles / BuildKit
- Building **all** workspace packages’ TS as part of dep materialization
  (CI must build those, or bundle them into app outputs)

### 4.4 Risk register

| Risk | Mitigation |
|------|------------|
| Workspace pack file-set ≠ pnpm deploy | Oracle tests; start with `files`-field packages and pure-JS workspace libs |
| Patch application differs from pnpm | Use same patch library semantics; integrity check post-apply |
| Allowlisted scripts break multi-arch | Per-arch runs; refuse cross-arch contamination |
| Private auth footguns | Keychain/.npmrc only; never bake tokens into layers; redact logs |
| Bucket reshuffles invalidate caches | Name-stable assignment + hot-list; version bumps don’t change membership |
| Huge locks OOM / slow parse | Importer-scoped closure; streaming YAML if needed; benchmarks in CI |
| Custom bases missing Node | Require explicit entrypoint; detect or fail loud |

---

## 5. Suggested implementation order (engineering sequence)

Within phases, implement in this order to keep each PR reviewable and
testable:

**P0**

1. Diagnose/report collector + importer-scoped validation  
2. Prefer lock tarball URLs; peer/extension quirk fixtures  
3. Large-lock parse/resolve benchmark harness  

**P1**

4. Catalogs + overrides (stop rejecting; fixtures)  
5. App include/exclude globs + skip-build-as-primary docs/config  
6. CMD / named commands  
7. Patches apply-on-extract  
8. Workspace/link/directory materialization + deploy oracle  
9. Platform optional filtering audit  

**P2**

10. `.npmrc` / token auth for tarball fetch  
11. Git resolution fetch  
12. Prebuild heuristics + allowlist scripts  
13. Custom base entrypoint/PATH behavior  
14. Multi-arch native optional integration tests  

**P3**

15. Hot-list + tunable bucketing  
16. Symlink layer strategy spike → implement winner  
17. Mount/HEAD push audit + test  
18. `--cache-dir` / CI cache docs  
19. Reproducible digest hardening  

Each item should land as its own PR (or small PR stack off `main`, never
stacked on unmerged feature branches per repo policy), with fixtures and
README/design updates in the same change.

---

## 6. Mapping back to the original gap list

Worst → best from the analysis, with the phase that addresses it:

| Original gap | Phase |
|--------------|-------|
| `pnpm.patchedDependencies` | P1 |
| workspace / link / directory deps | P1 |
| catalog: + lockfile catalogs | P1 |
| `pnpm.overrides` | P1 |
| Git / non-registry resolutions | P2 |
| Private registry auth | P2 |
| Prebuild-aware natives | P2 |
| Escape hatch for compile-from-source | P2 |
| Optional platform filtering | P1 |
| Configurable app output dirs | P1 |
| Non-JS runtime assets | P1 |
| `--skip-build` + external compile | P1 |
| Workspace-aware deploy-like closure | P1 |
| Smarter bucketing (~127 cap) | P3 |
| Stable symlink layer splitting | P3 |
| Cross-repo mount / existence checks | P3 |
| CI-surviving content-addressed caches | P3 |
| Custom base (non-distroless) | P2 |
| CMD / multi-entrypoint config | P1 |
| Multi-arch × native optionals | P2 |
| Importer selection in huge locks | P0–P1 |
| pnpm 9/10 lock quirks | P0–P1 |
| Deterministic digests | P3 |
| Better failure UX (enumerate all) | P0 |
| npm auth for fetch + push (CI) | P2 |

---

## 7. Immediate next step

After this plan is accepted:

1. Update `node-image-design.md` §0 / §6 / §9.4 / §11 to record decisions
   D1–D7 (still no feature code).
2. Open P0 implementation (`diagnose` + importer-scoped validation) as the
   first code PR — it makes every subsequent monorepo experiment debuggable.
