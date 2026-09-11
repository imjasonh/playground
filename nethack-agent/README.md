# NetHack agent

Harness for a Cursor agent that plays NetHack from the terminal, without a rules dump. Later lives see only notes and key sequences earlier lives wrote, plus the screens the process printed when those lives ended.

Design: [DESIGN.md](./DESIGN.md)

## Requirements

- Node.js ≥ 22.13
- `nethack` on `PATH`, or `/usr/games/nethack` (`nethack-console` on Debian and Ubuntu)
- `python3`
- `CURSOR_API_KEY` from the [Cursor dashboard](https://cursor.com/dashboard/api)

## Setup

```bash
cd nethack-agent
npm install
```

On Debian or Ubuntu:

```bash
sudo apt-get install nethack-console
```

## Test

Unit tests use a scripted agent and a fake screen. They do not call the Cursor API, they do not need NetHack installed, and they do not write `notebook/`.

```bash
npm test
npm run typecheck
```

## Play

Play always attaches to the real `nethack` process and resumes `notebook/`.

```bash
export CURSOR_API_KEY=...
npm run play -- --lives 1 --max-turns 16 --verbose
```

Each run writes `results/<id>/` and updates `notebook/` (notes, saved sequences, ending screens). Do not point play at the fake screen. That stand-in is for tests only.

The agent prompt does not name the game or list commands. Do not add a guide, a role flag, or an options file to close that gap. If the binary prints a menu, that menu is the lesson.
