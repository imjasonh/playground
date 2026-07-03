# RC Pro Loop

A browser racing toy inspired by **Super RC Pro-Am**: tiny RC cars on a carpet
circuit with a hairpin, esses, and a loop around the infield carpet pile.

## Play locally

```bash
cd rc-pro-am
npm start
```

Open `http://localhost:3000`.

## Controls

| Input | Action |
| --- | --- |
| `↑` / `W` | Throttle |
| `↓` / `S` | Brake / reverse |
| `←` `→` or `A` `D` | Steer |
| `Shift` | Turbo boost (once per press) |
| `R` | Restart race |
| Touch left pad | Drag left/right to steer |
| Touch right pad | Hold for throttle |

## Tests

```bash
cd rc-pro-am
npm test
```

Unit tests cover track containment, RC-style drift physics, lap counting, AI
steering, and race standings.

## Deploy

This directory is a browser app (`index.html` at the root). Merging to `main`
deploys it to GitHub Pages at `/rc-pro-am/`.
