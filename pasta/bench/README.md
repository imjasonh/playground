# pasta benchmarks

`results/monorepo-wasm.json` records before/after numbers for the
WASM tree-sitter backend on this playground monorepo with the
enrolled `.pasta/` rule set.

Reproduce (requires a `.pasta/` rules directory at the repo root):

```bash
CGO_ENABLED=0 go build -o /tmp/pasta ./pasta/cmd/pasta
PASTA_BIN=/tmp/pasta ./pasta/scripts/bench-monorepo.sh after
```
