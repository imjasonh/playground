# node-image pnpm fixtures

These fixtures exercise pnpm lockfile and install shapes used by node-image
stress and end-to-end tests. Each fixture keeps only source files, package
manifests, and generated `pnpm-lock.yaml` files; installed `node_modules`
directories are intentionally omitted.

## Core

- `hello-e2e/` - Docker-socket smoke (`node-image-e2e-ok` on stdout).
- `pure-js/` - depends on `ms@2.1.3`.
- `nested-deps/` - depends on `debug@4.3.4`, which pulls nested `ms` (runtime symlink farm).
- `scoped-dep/` - depends on `@sindresorhus/is@4.6.0` (scoped store path).
- `with-bin/` - depends on `rimraf@5.0.5`; asserts `.bin/rimraf` realpath into `.pnpm`.
- `optional-platform/` - `esbuild@0.21.5` + platform optionals; runtime `transformSync` loads the native binary.
- `lifecycle-scripts/` - depends on `es5-ext@0.10.64` (noop postinstall allowed; scripts never run).
- `ts-app/` - TypeScript app with `scripts.build` (compile path); Docker e2e packs committed `dist/`.

## Monorepo / lock fidelity

- `patched/` - `ms@2.1.3` with `patchedDependencies` + `patches/ms.patch`; runtime asserts patch marker in `require.resolve('ms')`.
- `workspace-app/` - pnpm workspace; `apps/api` depends on `@fixture/lib` via `workspace:*` / `link:` (materialized into the store).
- `catalog-app/` - `catalog:` specifier expanded to a concrete version in the lock.
- `override-app/` - lock with `overrides` (graph already resolved).

## App packaging

- `build-globs/` - packs `build/**` including a `.lua` asset; excludes `*.map`; runtime reads the lua file.
- `multi-cmd/` - `node-image.commands` for `api` vs `worker` entrypoints.

Docker-socket runtime coverage lives in
`internal/buildcmd/docker_run_test.go` (`TestE2EDockerSocketRuntimeCases`).
