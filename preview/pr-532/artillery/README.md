# Artillery

A touch-first, turn-based artillery duel inspired by the classic Mac game. Set
the cannon angle and powder charge, compensate for a new crosswind every turn,
and wear the opposing tank's armor down to zero.

The app is a static site with no runtime dependencies. It includes a local
two-player pass-and-play mode and a computer opponent that searches for a viable
firing solution using an imperfect wind estimate, then adds enough error to
remain beatable.

## Controls

- **Touch / mouse:** use the angle and powder sliders (or their step buttons),
  then press **Fire**.
- **Keyboard:** left/right adjust angle, up/down adjust powder, and space fires.
- **Sound:** toggle the synthesized sound effects from the header.
- **New duel:** return to the mode selector at any point.

Every duel generates a new landscape with level starting pads. Crosswind changes
after every shot and can strongly bend a round, while cannon elevation remains
relative to the horizon even if a crater tilts the tank. Direct hits inflict 62
armor damage; nearby explosions cause distance-based splash damage and deform
the battlefield. The first tank reduced from 100 armor to zero loses.

## Run locally

```bash
npm start
```

Then open <http://localhost:3000>. Run the game-engine tests with:

```bash
npm test
```
