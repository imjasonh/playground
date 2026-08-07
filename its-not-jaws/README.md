# It's Not Jaws

Harness for two AI agents playing **It's Not Jaws** — a movie shared-fact
guessing game — built on the
[Cursor TypeScript SDK](https://cursor.com/docs/sdk/typescript).

- **Knower (A)** secretly picks a well-known movie.
- **Guesser (B)** guesses titles; after each miss, A names a fact both movies share.
- During gameplay B sees A's **full published trace** (thinking, text, tool calls).

Rules: [GAME.md](./GAME.md) · Harness design: [DESIGN.md](./DESIGN.md)

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

```bash
npm run play:mock
# live:
export CURSOR_API_KEY=...
npm run play -- --backend cursor \
  --knower-model composer-2.5 \
  --guesser-model composer-2.5 \
  --max-turns 8 \
  --verbose
```

Each run prints a JSON summary and writes `results/<id>.json`.

## Layout

```
its-not-jaws/
├── GAME.md              # Canonical game rules
├── DESIGN.md            # Harness architecture
├── src/
│   ├── cli.ts
│   ├── harness.ts
│   ├── judge.ts
│   ├── protocol.ts
│   ├── prompts.ts
│   ├── agents/          # mock + cursor backends
│   └── games/           # its-not-jaws game definition
├── tests/
└── results/
```

## CI

PRs that touch `its-not-jaws/**` run `.github/workflows/its-not-jaws.yml`:

1. Require repo secret **`CURSOR_API_KEY`** (job fails if missing)
2. `npm test` + typecheck
3. One live Cursor game

Add the secret under **Settings → Secrets and variables → Actions**.

Optional Actions variables (defaults in parentheses):

| Variable | Default |
|----------|---------|
| `ITS_NOT_JAWS_KNOWER_MODEL` | `composer-2.5` |
| `ITS_NOT_JAWS_GUESSER_MODEL` | `composer-2.5` |
| `ITS_NOT_JAWS_MAX_TURNS` | `8` |

Manual run: Actions → It's Not Jaws → Run workflow.

## Notes

- Not a GitHub Pages browser app (no `index.html`).
- Shared `test.yml` discovery skips unit tests here; the workflow above covers them on relevant PRs.
