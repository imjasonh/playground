# The Spiral

Generate interlocking word spirals on demand. Every cell belongs to one inward
word (cells 1→center) and one outward word (center→1), the same structure as
magazine "Spiral" puzzles.

## Play

1. Pick a size (36, 48, 64, or 100 cells).
2. Click **New puzzle**.
3. Select a clue or cell, then type letters. Arrow keys move along the active
   clue.
4. Use **Check** to mark wrong letters, **Reveal** for the answer, or **Clear**
   to wipe your guesses.

Inward clues read counter-clockwise from cell 1 into the center. Outward clues
read clockwise from the center back to cell 1. The letter string is the same
both ways; only the word breaks differ.

## Run locally

```bash
npm start
```

Open <http://localhost:3000>. Tests:

```bash
npm test
```

## How generation works

The generator fills the ring from the outside with dictionary words, pruning
any partial fill whose reverse cannot finish as an outward word-break. When the
ring is full, it word-breaks the reverse string into the outward clue list.
Each entry carries a short crossword-style clue.

The URL stores `size` and `seed` after each generate, so you can reload or share
the same puzzle.
