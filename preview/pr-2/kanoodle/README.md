# Kanoodle

A browser-based implementation of the [Kanoodle](https://www.educationalinsights.com/item-kanoodle-game) puzzle game. Fit all 12 uniquely shaped noodles onto a 5×11 board.

## Rules

1. The board is a 5 row × 11 column grid (55 cells total).
2. Every puzzle uses all 12 pieces; each piece is used exactly once.
3. In puzzle mode, starter pieces shown on the board are **fixed** and cannot be moved.
4. Place the remaining pieces so every cell is filled with no overlaps or gaps.
5. Pieces may be rotated and flipped.

## Play

Open `index.html` in a browser, or run a local server:

```bash
npm install
npm start
```

Then visit http://localhost:3000

### Controls

- **New game** — start a puzzle at the selected difficulty, or load a classic puzzle from the dropdown.
- **Difficulty** — levels 1–5 follow the official booklet style (more empty cells at higher levels). Level 6 is free play with an empty board.
- **Rotate / Flip** — transform the selected piece (keyboard: `R` and `F`).
- **Drag and drop** — click a tray piece, then drag onto the board. Double-click a placed piece to pick it up again.

## Tests

```bash
npm test
```

## Project layout

- `src/pieces.js` — piece shapes and orientation math
- `src/board.js` — placement and validation
- `src/solver.js` — backtracking solver for puzzle generation
- `src/puzzle.js` — game state and win detection
- `src/game.js` — interactive game controller
- `src/app.js` — browser UI
