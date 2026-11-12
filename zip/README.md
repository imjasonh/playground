# Zip

Generates and plays Zip puzzles, like the LinkedIn game. It's built for
phones first.

Draw one path that starts at 1, passes every number in order, and fills
every cell. The path moves up, down, left, or right, and it can't cross a
thick wall.

Drag from 1 to draw. Drag back along the path, or tap a cell on it, to
erase back to that cell. A quick drag in a straight line fills the cells it
skips. Arrow keys draw one cell at a time, and Backspace erases the last
one. **Hint** first points out a wrong turn and the cell to back up to.
Otherwise it shows the next few cells of the solution.

The URL holds the level and an eight-digit hex seed. The same URL always
builds the same puzzle, so a link shares a puzzle. The page saves your path
and time, so a reload picks up where you left off.

## Levels

Every puzzle has exactly one solution.

| Level | Board | Walls | Numbers |
| --- | --- | --- | --- |
| Easy | 6×6 | none | the fewest that make the path unique, plus up to six more |
| Medium | 7×7 | up to 2 | the fewest, plus up to two more |
| Hard | 8×8 | up to 4 | the fewest |

## Run locally

```bash
cd zip
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```

## How puzzles are built

`src/zip.js` draws a random path through every cell. It starts from a
zigzag and applies backbite moves: it joins one end of the path to a
neighboring cell elsewhere on the path and reverses the piece between
them.

It numbers both ends and a cell every few steps, then searches for a
second solution. While there is one, it rules it out. Either it puts a
wall on an edge that the other solution uses and the real one doesn't, or
it numbers the cell where the two paths split. Then it removes every
number and wall that the solution doesn't need, in random order, and puts
back extra numbers for the easier levels.

The search walks paths from 1 and prunes any branch that leaves the
unvisited cells disconnected, or leaves a cell other than the end with
fewer than two open neighbors. It gives up after 200,000 steps. A number
or wall it can't prove unnecessary stays.

A worker builds puzzles off the main thread. A hard board takes about 0.3
seconds on a laptop, and up to a second, so while you play, a second
worker builds the next puzzle at the same level.
