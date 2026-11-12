# Clash

A simultaneous-bidding card game for two to four players, played with a standard
deck minus its four Aces. Each round a pot of cards gathers on the table and
everyone plays for it in secret, all at once: one card from a small hand of four
that refills from a face-down draw pile, spent whether it wins or loses. The
highest bid takes the pot, and the most pips at the end wins. The rules are in
[`rules.md`](rules.md), with a one-page summary in
[`quick-reference.md`](quick-reference.md).

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
| `TestResolvability` | Games in 2p/3p/4p over one to three decks end with every card and every pip accounted for |
| `TestDealPlan` | The even split gives a four-card hand, equal draw and ante piles, and the expected clash count from one to four decks |
| `TestHandRefill` | The hand tops back up from the draw pile, so it is full of four cards every clash |
| `TestSeatBalance` | Identical strategies win about equally from every seat |
| `TestBotBeatable` | The printed solo bot gives a real game, not a walkover; "always lowest" is trivial |
| `TestNoDominantStrategy` | No strategy beats the whole field heads-up, so there is no single correct line |
| `TestNoDominantStrategyMultiplayer` | No strategy takes much over a fair share at three- and four-handed tables |

`PlayGame` runs the standard one-deck game; `PlayGameDecks` shuffles several
48-card decks together for a longer one (the ante pile, and so the clash count,
grows with the deal). See the clash-count table in
[`quick-reference.md`](quick-reference.md#longer-games).

Use `-short` for a smaller, CI-friendly sample:

```bash
go test -short ./...
```

Longer runs (local balance tuning):

```bash
go test -count=1 -timeout 5m ./...
```
