import { createEmptyBoard, isBoardFull } from '../src/board.js';
import { generateSolution, solveBoard } from '../src/solver.js';
import { PIECES } from '../src/pieces.js';

describe('solver', () => {
  test('solves an empty 5x11 board with all 12 pieces', () => {
    const result = solveBoard(createEmptyBoard());
    expect(result).not.toBeNull();
    expect(isBoardFull(result.board)).toBe(true);
    expect(Object.keys(result.placements)).toHaveLength(PIECES.length);
  }, 30000);

  test('generateSolution returns a reproducible layout for a fixed seed', () => {
    const first = generateSolution(42);
    const second = generateSolution(42);
    expect(first.board).toEqual(second.board);
  }, 30000);
});
