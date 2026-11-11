# OVERRIDE

Three-suit cycle card game with a mercenary suit and Home Advantage. Rules are in [`rules.md`](rules.md).

## Simulation harness

The Go module implements the locked v2 rules and runs Monte Carlo checks in tests:

```bash
cd override
go test ./...
```

| Test | Purpose |
| --- | --- |
| `TestResolvability` | Full games in 1p/2p/3p modes terminate; card conservation holds |
| `TestResolutionCases` | Hand-built Clashes, including Direct Counter rank ties into War |
| `TestBalance` | Symmetric random play: win rates and Ingenuity steals stay within bounds |

Use `-short` for a smaller sample (CI-friendly):

```bash
go test -short ./...
```

Longer runs (local balance tuning):

```bash
go test -count=1 -timeout 5m ./...
```
