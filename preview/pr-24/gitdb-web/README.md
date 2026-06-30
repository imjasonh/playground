# gitdb-web

A browser compatibility spike for [`gitdb`](../gitdb/) and
[`go-sqlite-fdw`](https://github.com/values-conflict/go-sqlite-fdw).

The page runs a Go WebAssembly worker containing:

- a deterministic in-memory repository built with `go-git`
- the existing `gitdb` `fdw.Source` and `fdw.Cursor` implementations
- the `go-sqlite-fdw/ncruces` adapter
- SQLite via `github.com/ncruces/go-sqlite3`

The native `gitdb` CLI continues to use the modernc adapter. Both runtimes query
the same virtual-table implementations.

## Run locally

Go 1.25+ and Node.js are required.

```bash
cd gitdb-web
npm install
npm start
```

Open <http://localhost:3000>. The build writes `gitdb.wasm` and the matching Go
runtime into the ignored `generated/` directory.

## Test

```bash
npm test
npm run test:e2e
```

The end-to-end test builds the worker and executes SQL against the virtual
tables in Chromium.

## Deliberate limits

This spike is offline and read-only. It proves the SQLite/FDW compatibility
layer, worker bridge, planner callbacks, and Pages deployment path. It does not
yet provide remote cloning, a browser-backed Git object cache, authentication,
or CORS proxying.
