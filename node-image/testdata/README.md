# node-image pnpm fixtures

These fixtures exercise pnpm lockfile and install shapes used by node-image
stress and end-to-end tests. Each fixture keeps only source files, package
manifests, and generated `pnpm-lock.yaml` files; installed `node_modules`
directories are intentionally omitted.

## Core

- `pure-js/` - depends on `ms@2.1.3`.
- `nested-deps/` - depends on `debug@4.3.4`, which pulls nested `ms`.
- `scoped-dep/` - depends on `@sindresorhus/is@4.6.0`.
- `with-bin/` - depends on `rimraf@5.0.5` (bins).
- `optional-platform/` - depends on `esbuild@0.21.5` (optional platform pkgs).
- `lifecycle-scripts/` - depends on `es5-ext@0.10.64` (noop postinstall allowed).
- `ts-app/` - TypeScript app with `scripts.build` (compile path).

## Monorepo / lock fidelity

- `patched/` - `ms@2.1.3` with `patchedDependencies` + `patches/ms.patch` (applied on extract).
- `workspace-app/` - pnpm workspace; `apps/api` depends on `@fixture/lib` via `workspace:*` / `link:` (materialized into the store).
- `catalog-app/` - `catalog:` specifier expanded to a concrete version in the lock.
- `override-app/` - lock with `overrides` (graph already resolved).

## App packaging

- `build-globs/` - packs `build/**` including a `.lua` asset; excludes `*.map`.
- `multi-cmd/` - `node-image.commands` for `api` vs `worker` entrypoints.
