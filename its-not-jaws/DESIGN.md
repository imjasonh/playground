# It's Not Jaws — harness design

Two Cursor agents play a secret-guessing game. The harness orchestrates turns,
records a full transcript, scores outcomes, and tracks tokens / cost. Game rules
are pluggable; this repo starts with a stub noun game so we can harden the
harness before locking the real rules.

## Goals

1. **Iterate the harness** — fair channels, leak detection, protocol robustness.
2. **Benchmark models** — knower skill (hide + slowly reveal) vs guesser skill
   (use clues + published traces) across model pairs.

## Architecture

```
                 ┌──────────────────────────────────────┐
                 │               Harness                 │
                 │  turn loop · judge · metrics · I/O    │
                 │  (does NOT pick the secret)           │
                 └────────────────┬─────────────────────┘
                                  │
         setup commit (private)   │   full gameplay traces
              ┌───────────────────┼───────────────────┐
              ▼                   │                   ▼
     ┌─────────────────┐          │          ┌─────────────────┐
     │  Knower agent   │ ─────────┘          │  Guesser agent  │
     │  tools: []      │   play traces ───►  │  tools: []      │
     └─────────────────┘                     └─────────────────┘
```

Backends implement the same `PlayerAgent` interface:

| Backend | Purpose |
|---------|---------|
| `mock`  | Deterministic scripts for unit tests / dry runs (no API spend) |
| `cursor`| Real local Cursor SDK agents (`@cursor/sdk`) |

## Who picks the secret?

The **knower** picks the secret. The harness is not smart and does not sample
from a word list (that would collapse the game to “pick a random index”).

Ground truth is established in a **private setup turn**:

1. Harness asks the knower to choose a secret.
2. Knower replies with a structured commit:
   ```json
   {"type":"commit","secret":"..."}
   ```
3. Harness parses that move and stores `secret`.
4. The setup turn is kept in the game record for audit, but is **never
   forwarded** to the guesser.

After setup, gameplay begins. The guesser sees every message the knower emits
on play turns.

## Information channels

| Phase | Trace kinds | Shown to opponent? |
|-------|-------------|--------------------|
| `setup` (knower only) | thinking, text, tools | **No** — harness-private commit |
| `play` | thinking, text, tool calls (name/args/result) | **Yes** — full trace |

Both players run with `tools: []` and empty `settingSources` in isolated
workspaces. If tools are re-enabled later, play-phase tool traces remain public
and are scanned for leaks.

## Turn protocol

```json
{"type":"commit","secret":"..."}   // setup only
{"type":"clue","text":"..."}
{"type":"guess","value":"..."}
{"type":"give_up","reason":"..."}
```

### Loop

1. **Setup (private):** knower commits a secret.
2. Knower first public clue.
3. Repeat until terminal:
   - Guesser receives the knower's latest **play** trace, emits a guess (or give up).
   - If incorrect and turns remain, knower receives the guesser's full trace and
     emits the next clue.
4. Judge assigns a single outcome; write `results/<id>.json`.

## Outcomes

| Kind | Meaning |
|------|---------|
| `guesser_correct` | Guess matches knower's secret (normalized) |
| `guesser_gave_up` | Guesser emitted `give_up` |
| `secret_leaked` | Secret appears in knower **play** thinking, text, or tool trace |
| `unguessable` | Secret fails `game.isGuessable` (heuristic — not an allowlist sample) |
| `max_turns` | Hit configured turn limit |
| `protocol_error` | e.g. knower never committed during setup |
| `aborted` | Residual / unclassified |

Priority: protocol / unguessable / **leak** before correct guess. A guesser who
wins only because the knower spilled the secret during play still counts as
`secret_leaked`. Naming the secret during private setup is expected and not a leak.

## Metrics (per game record)

- `outcome`, `secret`, `secretCommitted`, `gameLength` (guesser turns)
- Full `turns[]` including setup (with `phase`) and play traces
- Aggregated token totals; optional billed `rawCostCents` via `Agent.getUsage()`

## Fairness notes (v1)

- Fixed model ids for reproducible pairs (avoid Router/`auto-smart` for benches).
- Same role prompts across models under test; knower chooses the secret.
- Mock backend for tests; Cursor backend for live experiments (`CURSOR_API_KEY`).

## Near-term iteration checklist

- [ ] Real game rules + richer `isGuessable` / domain constraints
- [ ] Optional third-party judge agent for synonym / near-miss guesses
- [ ] Suite runner: N seeds × model matrix → summary table
- [ ] Stricter leak detectors (stemming, nickname lists)
- [ ] Cloud runtime path for parallel tournaments
- [ ] CI discovery for this Node CLI (today: run `npm test` locally)
