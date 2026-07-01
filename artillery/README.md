# Artillery

A touch-first, turn-based artillery duel inspired by the classic Mac game. Set
the cannon angle and powder charge, compensate for a new crosswind every turn,
and wear the opposing tank's armor down to zero.

The app is a static site with no runtime dependencies. It includes a local
two-player pass-and-play mode and a computer opponent that searches for a viable
firing solution, then adds enough error to remain beatable.

## Controls

- **Touch / mouse:** use the angle and powder sliders (or their step buttons),
  then press **Fire**.
- **Keyboard:** left/right adjust angle, up/down adjust powder, and space fires.
- **Sound:** toggle the synthesized sound effects from the header.
- **New duel:** return to the mode selector at any point.

Crosswind changes after every shot. Direct hits inflict 62 armor damage, while
nearby explosions cause distance-based splash damage and carve a crater into
the battlefield. The first tank reduced from 100 armor to zero loses.

## Run locally

```bash
npm start
```

Then open <http://localhost:3000>. Run the game-engine tests with:

```bash
npm test
```
