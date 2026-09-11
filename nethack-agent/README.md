# NetHack agent

Harness for a Cursor agent that plays NetHack from the terminal, without a rules dump. Later lives see only notes and key sequences earlier lives wrote, plus the screens the process printed when those lives ended.

Design: [DESIGN.md](./DESIGN.md)

## Requirements

- Node.js ≥ 22.13
- For a real game: a `nethack` binary on `PATH`, and `python3`
- For a live Cursor agent: `CURSOR_API_KEY` from the [Cursor dashboard](https://cursor.com/dashboard/api)

## Setup

```bash
cd nethack-agent
npm install
```

## Test

The tests use a scripted agent and a fake screen. They do not call the Cursor API and they do not need NetHack installed.

```bash
npm test
npm run typecheck
```

## Play

```bash
npm run play:mock
```

A short live run against the fake screen:

```bash
export CURSOR_API_KEY=...
npm run play -- --backend cursor --game fake --lives 2 --max-turns 12 --verbose
```

Against the real binary, when `nethack` is installed:

```bash
npm run play -- --backend cursor --game tty --command nethack --lives 1 --max-turns 30
```

Continue from a previous notebook:

```bash
npm run play -- --backend cursor --game tty --resume results/<id>/memory --lives 3
```

Each run writes `results/<id>/record.json`, a text transcript, and `results/<id>/memory/`.

The agent prompt does not name the game or list commands. Do not add a guide, a role flag, or an options file to close that gap. If the binary prints a menu, that menu is the lesson.
