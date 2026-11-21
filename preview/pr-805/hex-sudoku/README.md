# Hex sudoku

Generates 16×16 sudoku boards in the hex digits 0-9 and A-F. Every row,
column, and 4×4 box holds each symbol once. Each board has exactly one
solution, and the clue pattern looks the same after a half turn.

The level sets which solving techniques a board needs. No level needs
guessing.

- **Easy** boards need only hidden singles, where a symbol fits only one
  cell of a row, column, or box. They have 120 clues.
- **Medium** boards also need naked singles, where only one symbol fits a
  cell. They have about 104 clues.
- **Hard** boards also need locked candidates, naked pairs, or hidden
  pairs. They have about 102 clues.

The URL holds the level and an eight-digit hex seed. The same level and
seed always build the same board, so a link shares a board. Boards with the
same seed share a solution, so switching levels keeps the solution and
changes the clues. **Copy as text** copies the board as 16 lines of 16
characters, with `.` for an empty cell. When the solution is showing,
**Copy as text** and **Print** include it.

## Run locally

```bash
cd hex-sudoku
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```

## How boards are built

`src/sudoku.js` fills a random grid from the seed, then clears clues in
pairs that mirror through the center. A pair stays cleared only if the
level's techniques still solve the board. Solving with those techniques
proves there is one solution, so the generator doesn't need a separate
uniqueness check.
