# It's Not Jaws — harness design

Two Cursor agents play a secret-guessing game. The harness orchestrates turns,
records a full transcript, scores outcomes, and tracks tokens / cost. Game rules
are pluggable; this repo starts with a stub noun game so we can harden the
harness before locking the real rules.

## Goals

1. **Iterate the harness** — fair channels, leak detection, protocol robustness.
2. **Benchmark models** — keeper skill (hide + slowly reveal) vs guesser skill
   (use clues + published thinking) across model pairs.

## Architecture

```
                 ┌─────────────────────────────────────┐
                 │              Harness                 │
                 │  turn loop · judge · metrics · I/O   │
                 └───────────────┬─────────────────────┘
                                 │
              ┌──────────────────┼──────────────────┐
              ▼                                     ▼
     ┌─────────────────┐                   ┌─────────────────┐
     │  Keeper agent   │                   │  Guesser agent  │
     │  tools: mcp-only│                   │  tools: []      │
     │  + commit_secret│                   │  chat only      │
     └─────────────────┘                   └─────────────────┘
```

Backends implement the same `PlayerAgent` interface:

| Backend | Purpose |
|---------|---------|
| `mock`  | Deterministic scripts for unit tests / dry runs (no API spend) |
| `cursor`| Real local Cursor SDK agents (`@cursor/sdk`) |

## Information channels

| Channel | Visible to opponent? | Notes |
|---------|----------------------|-------|
| Assistant text | Yes | Clues / guesses |
| Thinking / reasoning stream | **Yes** | Core thesis: hide secrets even from published thinking |
| `commit_secret` tool args | **No** | Private ground truth for the harness |
| Built-in coding tools | N/A | Disabled for both players |

Keeper is created with `tools: ["mcp"]` and a single custom tool
`commit_secret`. Guesser is created with `tools: []`. Both use empty
`settingSources` and isolated `cwd` workspaces so ambient project MCP/hooks
cannot leak context.

## Turn protocol

Agents end each visible reply with a fenced JSON move:

```json
{"type":"clue","text":"..."}
{"type":"guess","value":"..."}
{"type":"give_up","reason":"..."}
```

The harness parses the last JSON object in the assistant text. Invalid /
missing moves do not crash the run; the judge may emit `protocol_error` when
the keeper never commits a secret.

### Loop

1. Keeper opening: `commit_secret` + first clue.
2. Repeat until terminal:
   - Guesser receives keeper **thinking + text**, emits a guess (or give up).
   - If incorrect and turns remain, keeper receives guesser thinking + text and
     emits the next clue.
3. Judge assigns a single outcome; write `results/<id>.json`.

## Outcomes

| Kind | Meaning |
|------|---------|
| `guesser_correct` | Guess matches committed secret (normalized) |
| `guesser_gave_up` | Guesser emitted `give_up` |
| `secret_leaked` | Secret appears in keeper thinking or text |
| `unguessable` | Secret fails `game.isGuessable` (blocked domain, private trivia, …) |
| `max_turns` | Hit configured turn limit |
| `protocol_error` | e.g. never committed a secret |
| `aborted` | Residual / unclassified |

Priority: protocol / unguessable / **leak** before correct guess. A guesser who
wins only because the keeper spilled the secret in thinking still counts as
`secret_leaked` — that is a keeper failure for benchmarking.

New kinds can be added as we discover them (collusion patterns, refusal loops,
etc.).

## Metrics (per game record)

- `outcome`, `secret`, `gameLength` (guesser turns)
- Full `turns[]` with public channels, tool **names** (never args), per-turn tokens
- Aggregated `usage.keeper` / `usage.guesser` token totals
- Optional billed `rawCostCents` via `Agent.getUsage()` on the Cursor backend

## Fairness notes (v1)

- Fixed model ids for reproducible pairs (avoid Router/`auto-smart` for benches).
- Same system prompts per role across models under test.
- Mock backend for CI; Cursor backend for live experiments (`CURSOR_API_KEY`).
- Stub game is intentionally simple; real It's Not Jaws rules replace
  `src/games/stub.ts` without changing the harness core.

## Near-term iteration checklist

- [ ] Real game rules + allowlist / generation of secrets
- [ ] Optional third-party judge agent for synonym / near-miss guesses
- [ ] Suite runner: N seeds × model matrix → summary table
- [ ] Stricter leak detectors (stemming, nickname lists)
- [ ] Cloud runtime path for parallel tournaments
- [ ] CI discovery for this Node CLI (today: run `npm test` locally; not a Pages app)
