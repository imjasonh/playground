# gitdb-web

A browser compatibility spike for [`gitdb`](../gitdb/) and
[`go-sqlite-fdw`](https://github.com/values-conflict/go-sqlite-fdw).

The page runs a Go WebAssembly worker containing:

- a deterministic in-memory repository built with `go-git`
- the existing `gitdb` `fdw.Source` and `fdw.Cursor` implementations
- the `go-sqlite-fdw/ncruces` adapter
- SQLite via `github.com/ncruces/go-sqlite3`
- a same-origin HTTP-backed table that verifies browser Fetch can complete
  while an FDW `Filter` callback is suspended

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

## Current footprint

With Go 1.25, the stripped worker is approximately 31 MiB before HTTP
compression and 7.6 MiB with gzip. It initializes and runs the fixture queries
off the main thread, but bundle size is an explicit tradeoff of maximizing Go
code reuse in this approach.

## Deliberate limits

The Git fixture is offline and read-only. The HTTP probe fetches only a bundled
same-origin file. The spike proves the SQLite/FDW compatibility layer, worker
bridge, planner callbacks, browser Fetch scheduling, and Pages deployment path.
It does not yet provide remote cloning, a browser-backed Git object cache,
authentication, or CORS proxying.
