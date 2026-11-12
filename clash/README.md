# Clash

A simultaneous-bidding card game for two to four players, played with a standard
deck minus its four Aces. Each clash a pot of cards gathers on the table and
everyone plays for it in secret, all at once: one card from a small hand of four
that refills from a face-down pile. The card you play is spent whether it wins or
loses, but the pot you win slides back under your pile to come round again. The
game ends the moment a player runs out of cards, and whoever holds the most
wins. The rules are in [`rules.md`](rules.md), with a one-page summary in
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
| `TestResolvability` | Games in 2p/3p/4p end with every card accounted for in one place |
| `TestDeal` | The 48-card deck splits into equal stacks, leaving a 20/12/8-card pile after the hand |
| `TestGameTerminates` | Every game ends on its own within DeckSize/players clashes, never near the safety cap |
| `TestHandDepletes` | The hand starts full and stays full while the pile lasts, then shrinks as it runs out |
| `TestSeatBalance` | Identical strategies win about equally from every seat |
| `TestBotBeatable` | The printed solo bot gives a real game, not a walkover; "always lowest" is clearly beatable |
| `TestNoDominantStrategy` | No strategy beats the whole field heads-up, so there is no single correct line |
| `TestNoDominantStrategyMultiplayer` | No strategy takes much over a fair share at three- and four-handed tables |

`PlayGame` runs one game: each seat plays from a face-down pile that feeds the
pot and refills a four-card hand, the pot a winner takes goes back under their
pile, and the game ends by attrition when a seat runs out of cards. The winner
is whoever holds the most cards.

Use `-short` for a smaller, CI-friendly sample:

```bash
go test -short ./...
```

Longer runs (local balance tuning):

```bash
go test -count=1 -timeout 5m ./...
```
