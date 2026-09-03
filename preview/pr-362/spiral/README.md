# The Spiral

Generate interlocking word spirals. Every cell sits in one inward word
(cells 1→center) and one outward word (center→1), like magazine Spiral
puzzles.

## Play

1. Pick a size (36, 48, or 64 cells).
2. Click **New puzzle**.
3. Select a clue or cell, then type. Arrow keys move along the active clue.
4. **Check** marks wrong letters. **Reveal** shows the answer. **Clear**
   wipes your guesses.

Inward clues read from cell 1 into the center. Outward clues read from the
center back to cell 1. The letter string is the same both ways; only the
word breaks differ. Finishing the puzzle (without Reveal) sprays confetti.

## Run locally

```bash
npm start
```

Open <http://localhost:3000>. Tests:

```bash
npm test
```

## How generation works

The generator fills the ring from the outside with dictionary words and
drops any partial fill whose reverse cannot finish as an outward
word-break. When the ring is full, it re-breaks the reverse string so
outward boundaries never land on the same seams as the inward ones. That
stagger is what keeps you from stalling when one direction is stuck.
Answers and clue texts are unique within each puzzle.

The URL stores `size` and `seed` after each generate, so you can reload or
share the same puzzle.
