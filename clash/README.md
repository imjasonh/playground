# Clash

A simultaneous-bidding card game for two to four players, played with a standard
deck minus its four Aces. Each round a pot of cards gathers on the table and
everyone bids for it in secret, all at once, from a hand that never refills. The
rules are in [`rules.md`](rules.md).

## Simulation harness

The Go module implements the rules and runs Monte Carlo checks in tests:

```bash
cd clash
go test ./...
```

| Test | Purpose |
| --- | --- |
| `TestNewDeck` | The deck is 48 cards, Aces removed, 12 per suit |
| `TestBidAndResolve` | Bids, the Home bonus, tie carries, and winners resolve correctly |
| `TestResolvability` | Games in 2p/3p/4p end with every card and every pip accounted for |
| `TestSeatBalance` | Identical strategies win about equally from every seat |
| `TestBotBeatable` | The printed solo bot gives a real game, not a walkover; "always lowest" is trivial |
| `TestNoDominantStrategy` | No strategy beats the whole field, so there is no single correct line |

Use `-short` for a smaller, CI-friendly sample:

```bash
go test -short ./...
```

Longer runs (local balance tuning):

```bash
go test -count=1 -timeout 5m ./...
```
