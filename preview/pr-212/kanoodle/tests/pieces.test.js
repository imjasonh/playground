import {
  PIECES,
  flipDots,
  getOrientations,
  normalizeDots,
  rotateDots,
  pieceById,
} from '../src/pieces.js';
import { ROWS, COLS } from '../src/constants.js';

describe('pieces', () => {
  test('defines 12 unique Kanoodle noodles', () => {
    expect(PIECES).toHaveLength(12);
    const ids = PIECES.map((p) => p.id);
    expect(new Set(ids).size).toBe(12);
  });

  test('all pieces cover exactly 55 cells combined', () => {
    const total = PIECES.reduce((sum, piece) => sum + piece.dots.length, 0);
    expect(total).toBe(ROWS * COLS);
  });

  test('normalizeDots shifts shapes to origin', () => {
    const normalized = normalizeDots([
      [2, 3],
      [2, 4],
    ]);
    expect(normalized).toEqual([
      [0, 0],
      [0, 1],
    ]);
  });

  test('rotateDots turns L-shape 90 degrees', () => {
    const original = [
      [0, 0],
      [1, 0],
      [1, 1],
    ];
    const rotated = rotateDots(original);
    expect(rotated).toEqual([
      [0, 1],
      [0, 0],
      [1, 0],
    ]);
  });

  test('flipDots mirrors horizontally', () => {
    const original = [
      [0, 0],
      [0, 1],
      [1, 1],
    ];
    const flipped = flipDots(original);
    expect(flipped).toEqual([
      [0, 1],
      [0, 0],
      [1, 0],
    ]);
  });

  test('getOrientations deduplicates symmetric pieces', () => {
    const tri = pieceById('F');
    const orientations = getOrientations(tri.dots);
    expect(orientations.length).toBeGreaterThanOrEqual(4);
    expect(orientations.length).toBeLessThanOrEqual(8);
  });

  test('each piece has at least one orientation', () => {
    for (const piece of PIECES) {
      expect(getOrientations(piece.dots).length).toBeGreaterThanOrEqual(1);
    }
  });

  test('asymmetric pieces have multiple orientations', () => {
    expect(getOrientations(pieceById('A').dots).length).toBeGreaterThan(1);
    expect(getOrientations(pieceById('C').dots).length).toBeGreaterThan(1);
  });
});
