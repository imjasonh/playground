# It's Not Jaws

Harness for two AI agents playing a secret-guessing game against each other,
built on the [Cursor TypeScript SDK](https://cursor.com/docs/sdk/typescript).

One agent (keeper) picks and slowly reveals a secret; the other (guesser) tries
to find it. The guesser sees the keeper's **thinking traces** as well as their
messages — the benchmark is about hiding a secret even from published reasoning.

See [DESIGN.md](./DESIGN.md) for architecture, channels, and outcome taxonomy.

> Game rules are still a stub (`stub-noun`). The harness is ready for iteration
> and live Cursor runs while the real It's Not Jaws rules are specified.

## Requirements

- Node.js ≥ 22.13
- For live games: `CURSOR_API_KEY` from the [Cursor dashboard](https://cursor.com/dashboard/api)

## Setup

```bash
cd its-not-jaws
npm install
```

## Test (mock backend, no API spend)

```bash
npm test
npm run typecheck
```

## Play

Mock dry run (default):

```bash
npm run play:mock
# or
npm run play -- --backend mock --verbose
```

Live Cursor agents:

```bash
export CURSOR_API_KEY=...
npm run play -- --backend cursor \
  --keeper-model composer-2.5 \
  --guesser-model composer-2.5 \
  --max-turns 8 \
  --verbose
```

Each run prints a JSON summary and writes a full record to `results/<id>.json`
(outcome, secret, turns, thinking, token usage, optional cost).

## Layout

```
its-not-jaws/
├── DESIGN.md
├── src/
│   ├── cli.ts           # CLI entry
│   ├── harness.ts       # Turn loop + record writer
│   ├── judge.ts         # Deterministic outcomes
│   ├── protocol.ts      # Move parsing + leak helpers
│   ├── prompts.ts
│   ├── agents/          # mock + cursor PlayerAgent backends
│   └── games/           # Pluggable rules (stub for now)
├── tests/
└── results/             # Game JSON records (gitignored contents)
```

## Notes

- Not a GitHub Pages browser app (no `index.html`); shared deploy workflows ignore it.
- Shared `test.yml` app discovery also skips it today — run `npm test` here when
  changing this directory (same pattern as other non-browser tools in the repo).
