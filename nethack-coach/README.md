# NetHack Coach

A tmux-hosted advisor that watches you play NetHack and gives advice in a side
pane. You play the game yourself; a Cursor agent reads the screen and suggests
what to do next. It never presses keys.

This is the inverse of the sibling [`nethack-agent`](../nethack-agent) harness,
which teaches the agent nothing and lets it play. The coach exists to teach the
human, so it names the game and draws on real NetHack knowledge.

## How it works

The launcher opens one tmux session with two panes:

- Left: `/usr/games/nethack`, which you drive as usual.
- Right: the advisor, which reads the game pane with `tmux capture-pane` and
  prints advice.

tmux is a real terminal, so NetHack runs exactly as it would on its own. The
advisor only ever reads the rendered screen text; it has no built-in tools and
loads no repo settings.

Advice is event- and demand-driven, not per keystroke:

- Automatic advice fires when the screen settles after a change, with a cooldown
  so a burst of redraws becomes one call.
- Press F9 any time to ask for advice on the current screen, even mid-move.
- Press F10 to toggle automatic advice off or on.
- Press F8 to quit.

The sidebar footer shows the running token count and, once the SDK reports it,
the token cost.

## Requirements

- Node.js ≥ 22.13
- `tmux`
- `nethack` on `PATH`, or `/usr/games/nethack` (`nethack-console` on Debian and
  Ubuntu)
- `CURSOR_API_KEY` from the [Cursor dashboard](https://cursor.com/dashboard/api)

## Setup

```bash
cd nethack-coach
npm install
```

On Debian or Ubuntu:

```bash
sudo apt-get install nethack-console
```

## Play

```bash
export CURSOR_API_KEY=...
npm start
```

The default model is `grok-4.6`. Override it or the game command through the
environment:

```bash
NHC_MODEL=gpt-5.2 NHC_SIDEBAR_COLS=52 npm start
```

| Variable | Default | Purpose |
|----------|---------|---------|
| `NHC_MODEL` | `grok-4.6` | Advisor model id from your account catalog |
| `NHC_SIDEBAR_COLS` | `46` | Width of the advisor pane |
| `NHC_GAME_CMD` | the nethack binary | Command to run as the game |
| `NHC_SESSION` | `coach-<pid>` | tmux session name |
| `NHC_SOCKET` | `nethack-coach` | tmux socket name (private server) |

Closing the window (F8, or the game and advisor both exiting) ends the session.
`C-b d` detaches tmux; this launcher then tears the session down, so detaching
ends the game rather than leaving it in the background.

## Test

Unit tests cover the advice decision, screen diffing, and sidebar layout. An
injected-dependency test drives the whole watch loop without tmux, the game, or
the API.

```bash
npm test
npm run typecheck
```

These do not call the Cursor API and do not need NetHack or tmux installed.

## Layout

| File | Role |
|------|------|
| `bin/nethack-coach` | Launcher: builds the tmux session and hotkeys |
| `coach.tmux.conf` | Private tmux profile (panes, borders, status line) |
| `src/advisor.ts` | Entry point for the side pane; wires real dependencies |
| `src/loop.ts` | The watch loop (dependency-injected, testable) |
| `src/advice.ts` | When to ask for advice |
| `src/screen.ts` | tmux capture, screen normalize, and diff |
| `src/controls.ts` | Reads the F9/F10 marker files the hotkeys drop |
| `src/render.ts` | Sidebar layout and painting |
| `src/prompts.ts` | The advisor's instructions and per-screen message |
| `src/cursor.ts` | The read-only Cursor agent |
| `src/cost.ts` | Token totals and SDK cost reads |
