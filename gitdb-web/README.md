# gitdb-web

A browser application for [`gitdb`](../gitdb/) and
[`go-sqlite-fdw`](https://github.com/values-conflict/go-sqlite-fdw).

The page runs a Go WebAssembly worker containing:

- a live smart-HTTP clone of the selected public repository using `go-git`
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

Open <http://localhost:3000>. The build writes `gitdb.wasm.gz` and the matching
Go runtime into the ignored `generated/` directory. The Worker uses the browser
`DecompressionStream` API before instantiating the module.

## Test

```bash
npm test
npm run test:e2e
```

The end-to-end test builds the worker and executes SQL against the virtual
tables in Chromium.

## Current footprint

With Go 1.25, the stripped worker is approximately 31 MiB raw and 7.6 MiB with
gzip. Only the compressed artifact is loaded by the browser, both to reduce
transfer size and to stay below the per-file limit of the legacy Pages
publisher. It initializes and runs repository queries off the main thread, but
bundle size is an explicit tradeoff of maximizing Go code reuse in this
approach.

## Browser cloning

Most Git hosts do not permit browser smart-HTTP requests directly. The UI
defaults to `https://cors.isomorphic-git.org`, matching the existing browser Git
app. The proxy can observe repository URLs and all public data it relays; clear
the field for a CORS-enabled host or provide a proxy you control.

Clone depth and default-branch controls bound memory use. A depth of zero
requests full history.

## Current limits

- Repository objects are held in memory and disappear when the Worker closes.
- Only public HTTP(S) repositories are supported; browser authentication is not
  implemented yet.
- Very large histories, full-tree content searches, and blame can consume
  substantial browser memory and CPU.
- SQL virtual tables are intentionally non-mutating: querying never pushes
  changes back to the remote.
