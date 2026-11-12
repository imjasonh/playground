# Queens

Generates and plays Queens and Two Not Touch puzzles. It's built for phones
first.

Both games split a square grid into colored regions. Every row, column, and
region holds the same number of pieces, and no two pieces touch, not even
at a corner.

- **Queens** places one queen per row, column, and region.
- **Two Not Touch** places two stars per row, column, and region.

Tap a cell once to mark it ×, again for a piece, and again to clear it.
Drag across cells to mark them all ×. With **Auto ×** on, dots fill the
cells that your pieces rule out. **Hint** first points out a mark that
disagrees with the solution. Otherwise it highlights the next step and
explains it. Arrow keys move between cells, and Space or Enter marks one.

The URL holds the game, the level, and an eight-digit hex seed. The same
URL always builds the same puzzle, so a link shares a puzzle. The page
saves your marks and time, so a reload picks up where you left off.

## Levels

Every puzzle has exactly one solution and needs no guessing. The level sets
the board size and the hardest rule a puzzle needs. A puzzle at a level is
solvable with that level's rules and not with the rules of the level below.

| Rule | What it says |
| --- | --- |
| Forced | A row, column, or region with as many open cells as missing pieces fills them. |
| Touch | A piece in a cell would leave some row, column, or region too little room, so the cell is empty. |
| Group | When n regions fit inside n rows (or columns), those regions hold all of those rows' pieces, so the rest of the rows is empty. The same works the other way round. |
| Forcing | A piece in a cell, followed by the forced rule and its eliminations, leads to a contradiction, so the cell is empty. |

| Level | Queens | Two Not Touch |
| --- | --- | --- |
| Easy | 7×7, forced | 9×9, touch |
| Medium | 8×8, touch | 10×10, touch |
| Hard | 9×9, group | 10×10, group |
| Expert | 10×10, forcing | 10×10, forcing |

Two Not Touch starts at the touch rule, because the forced rule can't place
a star on an empty board. A region that holds two stars that can't touch
always has more than two cells.

Two Not Touch has no 8×8 level. A 2×2 block can hold only one star, and
the 16 blocks that tile an 8×8 board must hold all 16 stars, one each. Only
two star layouts fit, mirror images of each other, so every 8×8 board would
have one of the same two solutions whatever its regions.

## Run locally

```bash
cd queens
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```

## How puzzles are built

`src/puzzle.js` places the pieces first, at random, with none touching.
It grows one region from each queen, or for Two Not Touch, grows one region
per star and pairs neighboring regions. Then it moves cells between
neighboring regions, one at a time. It keeps a move unless the move lets
the level's rules solve less of the board, or lets the rules of the level
below solve more. It stops when the level's rules solve the whole board
and the easier rules don't. The rules only make sound deductions, so a
board they solve has exactly one solution. The tests check that with a
brute-force solver.

A worker builds puzzles off the main thread. An expert board takes about a
second on a laptop and can take several on a phone, so while you play, a
second worker builds the next puzzle at the same level.

`src/game.js` handles the player's marks: conflicts, the win check, the
dots, and hints. A hint runs the same rules from your marks and explains
the first step it finds.
