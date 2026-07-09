# node-image pnpm fixtures

These fixtures exercise pnpm lockfile and install shapes used by node-image
stress and end-to-end tests. Each fixture keeps only source files, package
manifests, and generated `pnpm-lock.yaml` files; installed `node_modules`
directories are intentionally omitted.

- `nested-deps/` - depends on `debug@4.3.4`, which pulls the nested `ms` dependency.
- `scoped-dep/` - depends on the scoped package `@sindresorhus/is@4.6.0`.
- `with-bin/` - depends on `rimraf@5.0.5`, exercising packages that expose bins.
- `optional-platform/` - depends on `esbuild@0.21.5`, exercising optional platform packages.
- `lifecycle-scripts/` - depends on `es5-ext@0.10.64`; lockfile generated with `pnpm install --ignore-scripts` for a package with lifecycle/build metadata.
- `patched/` - depends on `ms@2.1.3` with a pnpm `patchedDependencies` entry and `patches/ms.patch`.
- `workspace-app/` - a pnpm workspace with `packages/lib` and `apps/api`, where the API app depends on the library via `workspace:*`.
