import { PIECES } from './pieces.js';
import { boardFromFlat } from './board.js';

const INDEX_TO_ID = PIECES.map((p) => p.id);

function fromFlat(flat) {
  return boardFromFlat(flat, (index) => INDEX_TO_ID[index]);
}

/** Curated puzzles derived from official Kanoodle layouts (piece indices 0–11). */
export const PUZZLE_LIBRARY = [
  {
    id: 0,
    difficulty: 1,
    label: 'Classic #1',
    startBoard: fromFlat([
      5, 5, 4, 4, 4, 10, 10, 10, 10, 1, 1, 9, 5, 5, 5, 4, 7, 6, 6, 6, 6, 1, 9, 9, 9, 0, 4, 7, 3, 3, 6, 1, 1, 2, 2, 0, 0, 0, 7, 11, 3, 3, 8, 8, 2, 2, 2, 0, 7, 7, 11, 11, 3, 8, 8,
    ]),
    solutionBoard: fromFlat([
      5, 5, 4, 4, 4, 10, 10, 10, 10, 1, 1, 9, 5, 5, 5, 4, 7, 6, 6, 6, 6, 1, 9, 9, 9, 0, 4, 7, 3, 3, 6, 1, 1, 2, 2, 0, 0, 0, 7, 11, 3, 3, 8, 8, 2, 2, 2, 0, 7, 7, 11, 11, 3, 8, 8,
    ]),
  },
  {
    id: 1,
    difficulty: 2,
    label: 'Classic #2',
    startBoard: fromFlat([
      9, 9, 9, 7, 7, 7, 7, 6, 6, 6, 6, 9, 3, 3, 7, 4, 4, 4, 0, 6, 8, 8, 1, 1, 3, 3, 4, 11, 0, 0, 0, 8, 8, 1, 5, 5, 3, 4, 11, 11, 0, -1, -1, -1, 1, 1, 5, 5, 5, 10, 10, 10, 10, -1, -1,
    ]),
    solutionBoard: fromFlat([
      9, 9, 9, 7, 7, 7, 7, 6, 6, 6, 6, 9, 3, 3, 7, 4, 4, 4, 0, 6, 8, 8, 1, 1, 3, 3, 4, 11, 0, 0, 0, 8, 8, 1, 5, 5, 3, 4, 11, 11, 0, 2, 2, 2, 1, 1, 5, 5, 5, 10, 10, 10, 10, 2, 2,
    ]),
  },
  {
    id: 2,
    difficulty: 3,
    label: 'Classic #3',
    startBoard: fromFlat([
      2, 10, 10, 10, 10, 7, 3, 3, 4, 4, 4, 2, 2, 7, 7, 7, 7, 0, 3, 3, 9, 4, 2, 2, 1, 1, 11, 0, 0, 0, 3, 9, 4, 8, 8, 1, 11, 11, 6, 0, -1, -1, 9, 9, 8, 8, 1, 1, 6, 6, 6, 6, -1, -1, -1,
    ]),
    solutionBoard: fromFlat([
      2, 10, 10, 10, 10, 7, 3, 3, 4, 4, 4, 2, 2, 7, 7, 7, 7, 0, 3, 3, 9, 4, 2, 2, 1, 1, 11, 0, 0, 0, 3, 9, 4, 8, 8, 1, 11, 11, 6, 0, 5, 5, 9, 9, 8, 8, 1, 1, 6, 6, 6, 6, 5, 5, 5,
    ]),
  },
  {
    id: 3,
    difficulty: 4,
    label: 'Classic #4',
    startBoard: fromFlat([
      7, 7, 7, 7, 6, 11, 11, 8, 8, 9, 9, 7, 0, 6, 6, 6, 6, 11, 8, 8, 3, 9, 0, 0, 0, 4, 10, 10, 10, 10, 3, 3, 9, 1, 0, 1, 4, 5, 5, 5, 3, 3, -1, -1, 1, 1, 1, 4, 4, 4, 5, 5, -1, -1, -1,
    ]),
    solutionBoard: fromFlat([
      7, 7, 7, 7, 6, 11, 11, 8, 8, 9, 9, 7, 0, 6, 6, 6, 6, 11, 8, 8, 3, 9, 0, 0, 0, 4, 10, 10, 10, 10, 3, 3, 9, 1, 0, 1, 4, 5, 5, 5, 3, 3, 2, 2, 1, 1, 1, 4, 4, 4, 5, 5, 2, 2, 2,
    ]),
  },
  {
    id: 4,
    difficulty: 5,
    label: 'Classic #5',
    startBoard: fromFlat([
      6, 6, 6, 6, 0, 7, 7, 7, 7, 8, 8, 11, 6, 4, 0, 0, 0, 2, 2, 7, 8, 8, 11, 11, 4, 1, 0, 1, 2, 2, 2, 3, -1, 4, 4, 4, 1, 1, 1, 5, 5, 3, 3, -1, 10, 10, 10, 10, 5, 5, 5, 3, 3, -1, -1,
    ]),
    solutionBoard: fromFlat([
      6, 6, 6, 6, 0, 7, 7, 7, 7, 8, 8, 11, 6, 4, 0, 0, 0, 2, 2, 7, 8, 8, 11, 11, 4, 1, 0, 1, 2, 2, 2, 3, 9, 4, 4, 4, 1, 1, 1, 5, 5, 3, 3, 9, 10, 10, 10, 10, 5, 5, 5, 3, 3, 9, 9,
    ]),
  },
];

export function listLibraryPuzzles() {
  return PUZZLE_LIBRARY.map(({ id, difficulty, label }) => ({ id, difficulty, label }));
}
