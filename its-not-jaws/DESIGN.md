# It's Not Jaws — harness design

Two Cursor agents play a secret-guessing game. The harness orchestrates turns,
records a full transcript, scores outcomes, and tracks tokens / cost. Game rules
are pluggable; this repo starts with a stub noun game so we can harden the
harness before locking the real rules.

## Goals

1. **Iterate the harness** — fair channels, leak detection, protocol robustness.
2. **Benchmark models** — keeper skill (hide + slowly reveal) vs guesser skill
   (use clues + published traces) across model pairs.

## Architecture

```
                 ┌─────────────────────────────────────┐
                 │              Harness                 │
                 │  turn loop · judge · metrics · I/O   │
                 │  assigns SECRET → keeper setup only  │
                 └───────────────┬─────────────────────┘
                                 │
              ┌──────────────────┼──────────────────┐
              ▼                                     ▼
     ┌─────────────────┐                   ┌─────────────────┐
     │  Keeper agent   │  full trace ───►  │  Guesser agent  │
     │  tools: []      │                   │  tools: []      │
     └─────────────────┘                   └─────────────────┘
```

Backends implement the same `PlayerAgent` interface:

| Backend | Purpose |
|---------|---------|
| `mock`  | Deterministic scripts for unit tests / dry runs (no API spend) |
| `cursor`| Real local Cursor SDK agents (`@cursor/sdk`) |

## Information channels

The opponent sees **every message the agent emits**:

| Trace kind | Forwarded? | Notes |
|------------|------------|-------|
| Thinking / reasoning | Yes | Core thesis: hide secrets from published thinking |
| Assistant text | Yes | Clues / guesses |
| Tool calls (name, args, result) | Yes | No private tool side-channel |

Harness → keeper setup (system prompt containing `SECRET: …`) is **not** a
message from the keeper, so the guesser does not see it. That is how ground
truth is established without a moot `commit_secret` tool.

Both players run with `tools: []` and empty `settingSources` in isolated
workspaces. If a future experiment re-enables tools, their traces are still
published and scanned for leaks.

## Turn protocol

Agents end each visible reply with a fenced JSON move:

```json
{"type":"clue","text":"..."}
{"type":"guess","value":"..."}
{"type":"give_up","reason":"..."}
```

### Loop

1. Harness picks a secret (`game.pickSecret`) and injects it into the keeper setup.
2. Keeper opening: first clue (must not name the secret in any emitted message).
3. Repeat until terminal:
   - Guesser receives the keeper's **full trace**, emits a guess (or give up).
   - If incorrect and turns remain, keeper receives the guesser's full trace and
     emits the next clue.
4. Judge assigns a single outcome; write `results/<id>.json`.

## Outcomes

| Kind | Meaning |
|------|---------|
| `guesser_correct` | Guess matches assigned secret (normalized) |
| `guesser_gave_up` | Guesser emitted `give_up` |
| `secret_leaked` | Secret appears in keeper thinking, text, or tool trace |
| `unguessable` | Secret fails `game.isGuessable` |
| `max_turns` | Hit configured turn limit |
| `protocol_error` | Reserved for future protocol failures |
| `aborted` | Residual / unclassified |

Priority: unguessable / **leak** before correct guess. A guesser who wins only
because the keeper spilled the secret still counts as `secret_leaked`.

## Metrics (per game record)

- `outcome`, `secret`, `gameLength` (guesser turns)
- Full `turns[].public.messages[]` traces
- Aggregated token totals; optional billed `rawCostCents` via `Agent.getUsage()`

## Fairness notes (v1)

- Fixed model ids for reproducible pairs (avoid Router/`auto-smart` for benches).
- Same role prompts across models under test; secret assigned by harness/seed.
- Mock backend for tests; Cursor backend for live experiments (`CURSOR_API_KEY`).

## Near-term iteration checklist

- [ ] Real game rules + richer secret generation
- [ ] Optional third-party judge agent for synonym / near-miss guesses
- [ ] Suite runner: N seeds × model matrix → summary table
- [ ] Stricter leak detectors (stemming, nickname lists)
- [ ] Cloud runtime path for parallel tournaments
- [ ] CI discovery for this Node CLI (today: run `npm test` locally)
