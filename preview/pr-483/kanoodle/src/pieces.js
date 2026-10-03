/**
 * Kanoodle piece definitions.
 * Each piece is a set of [row, col] offsets relative to its anchor (top-left of bounding box).
 * Based on the official 12-noodle set for the 5×11 board.
 */
export const PIECES = [
  {
    id: 'L',
    name: 'Gray',
    color: '#cfc4b2',
    dots: [[0, 0], [1, 0], [2, 0], [1, 1], [1, -1]],
  },
  {
    id: 'I',
    name: 'Yellow',
    color: '#ffd603',
    dots: [[0, 0], [0, 1], [1, 1], [2, 1], [2, 0]],
  },
  {
    id: 'B',
    name: 'Red',
    color: '#f63202',
    dots: [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1]],
  },
  {
    id: 'H',
    name: 'Magenta',
    color: '#f35e95',
    dots: [[0, 0], [1, 0], [1, 1], [2, 1], [2, 2]],
  },
  {
    id: 'G',
    name: 'Light Blue',
    color: '#b6d8e5',
    dots: [[0, 0], [1, 0], [2, 0], [2, 1], [2, 2]],
  },
  {
    id: 'E',
    name: 'Green',
    color: '#009b59',
    dots: [[0, 0], [1, 0], [1, 1], [2, 1], [3, 1]],
  },
  {
    id: 'D',
    name: 'Pink',
    color: '#efc19f',
    dots: [[0, 0], [1, 0], [1, 1], [2, 0], [3, 0]],
  },
  {
    id: 'C',
    name: 'Blue',
    color: '#0149c2',
    dots: [[0, 0], [1, 0], [2, 0], [3, 0], [3, 1]],
  },
  {
    id: 'K',
    name: 'Light Green',
    color: '#abe64c',
    dots: [[0, 0], [1, 0], [0, 1], [1, 1]],
  },
  {
    id: 'A',
    name: 'Orange',
    color: '#ff8a00',
    dots: [[0, 0], [1, 0], [2, 0], [2, 1]],
  },
  {
    id: 'J',
    name: 'Purple',
    color: '#925abb',
    dots: [[0, 0], [1, 0], [2, 0], [3, 0]],
  },
  {
    id: 'F',
    name: 'White',
    color: '#ffffe8',
    dots: [[0, 0], [1, 0], [1, 1]],
  },
];

export function pieceById(id) {
  const piece = PIECES.find((p) => p.id === id);
  if (!piece) {
    throw new Error(`Unknown piece id: ${id}`);
  }
  return piece;
}

export function pieceIndexById(id) {
  const index = PIECES.findIndex((p) => p.id === id);
  if (index === -1) {
    throw new Error(`Unknown piece id: ${id}`);
  }
  return index;
}

/** Normalize dots so minimum row and col are both 0. */
export function normalizeDots(dots) {
  const minRow = Math.min(...dots.map(([r]) => r));
  const minCol = Math.min(...dots.map(([, c]) => c));
  return dots.map(([r, c]) => [r - minRow, c - minCol]);
}

/** Rotate dots 90° clockwise. */
export function rotateDots(dots) {
  return normalizeDots(dots.map(([r, c]) => [c, -r]));
}

/** Flip dots horizontally (mirror over vertical axis). */
export function flipDots(dots) {
  return normalizeDots(dots.map(([r, c]) => [r, -c]));
}

function dotsKey(dots) {
  return normalizeDots([...dots])
    .map(([r, c]) => `${r},${c}`)
    .sort()
    .join('|');
}

/** All unique orientations for a piece (rotations and flips). */
export function getOrientations(dots) {
  const seen = new Set();
  const orientations = [];
  let current = normalizeDots(dots);

  for (let flip = 0; flip < 2; flip += 1) {
    for (let rot = 0; rot < 4; rot += 1) {
      const key = dotsKey(current);
      if (!seen.has(key)) {
        seen.add(key);
        orientations.push(current.map(([r, c]) => [r, c]));
      }
      current = rotateDots(current);
    }
    current = flipDots(current);
  }

  return orientations;
}

/** Absolute board cells for a piece placed at (row, col) with given orientation dots. */
export function absoluteCells(orientationDots, row, col) {
  return orientationDots.map(([dr, dc]) => [row + dr, col + dc]);
}
