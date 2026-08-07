# It's Not Jaws — harness design

Two Cursor agents play **It's Not Jaws**, a movie shared-fact guessing game.
Canonical rules live in [GAME.md](./GAME.md). This document covers the harness
architecture around those rules.

## Goals

1. **Iterate the harness** — fair channels, leak detection, protocol robustness.
2. **Benchmark models** — knower skill (hide + slowly reveal via shared facts)
   vs guesser skill (use facts + published traces) across model pairs.

## Architecture

```
                 ┌──────────────────────────────────────┐
                 │               Harness                 │
                 │  turn loop · judge · metrics · I/O    │
                 │  (does NOT pick the movie)            │
                 └────────────────┬─────────────────────┘
                                  │
         setup commit (private)   │   full gameplay traces
              ┌───────────────────┼───────────────────┐
              ▼                   │                   ▼
     ┌─────────────────┐          │          ┌─────────────────┐
     │ Knower (Agent A)│ ─────────┘          │Guesser (Agent B)│
     │  tools: []      │  shared facts ───►  │  tools: []      │
     └─────────────────┘                     └─────────────────┘
```

| Backend | Purpose |
|---------|---------|
| `mock`  | Deterministic scripts for unit tests / dry runs (no API spend) |
| `cursor`| Real local Cursor SDK agents (`@cursor/sdk`) |

## Who picks the movie?

The **knower** picks a real, fairly well-known movie. The harness does not
sample from a title list.

Ground truth is established in a **private setup turn**:

```json
{"type":"commit","secret":"Movie Title"}
```

Setup is audited in the game record but **never forwarded** to the guesser.

## Gameplay loop

1. Guesser makes the **first guess** (cold open — no free clue).
2. On a wrong guess, knower replies with one **shared fact** true of both films:
   ```json
   {"type":"shared_fact","text":"set during WW2"}
   ```
3. Guesser uses accumulated facts + the knower's full published trace to guess again.

## Information channels

| Phase | Trace kinds | Shown to opponent? |
|-------|-------------|--------------------|
| `setup` (knower only) | thinking, text, tools | **No** — harness-private commit |
| `play` | thinking, text, tool calls (name/args/result) | **Yes** — full trace |

## Outcomes

| Kind | Meaning |
|------|---------|
| `guesser_correct` | B named A's movie |
| `knower_wins` | B gave up / stalled; movie looks fair & well-known enough |
| `unguessable` | B gave up / stalled; movie looks nonexistent / obscure / private |
| `secret_leaked` | Title appears in A's **play** thinking, text, or tool trace |
| `max_turns` | Reserved / folded into knower_wins vs unguessable via fairness |
| `protocol_error` | A never committed during setup |
| `aborted` | Residual / unclassified |

Priority: protocol → **leak** → correct guess → give-up fairness split.
Naming the title during private setup is expected and not a leak.

## Metrics

- `outcome`, `secret`, `secretCommitted`, `gameLength` (guesser turns)
- Full `turns[]` including setup (`phase`) and play traces
- Token totals; optional billed `rawCostCents` via `Agent.getUsage()`

## Near-term iteration

- [ ] Richer well-known / exists judge (third agent or catalog) for `unguessable`
- [ ] Judge whether shared facts are actually true of both films
- [ ] Stronger title leak detectors (aliases, year disambiguation, word boundaries)
- [ ] Suite runner: N games × model matrix → summary table
- [ ] Cloud runtime path for parallel tournaments
- [ ] CI discovery for this Node CLI (today: `cd its-not-jaws && npm test`)
