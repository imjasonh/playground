import { ROWS, COLS, CELL_COUNT } from './constants.js';
import { absoluteCells } from './pieces.js';

export function createEmptyBoard() {
  return Array.from({ length: ROWS }, () => Array(COLS).fill(null));
}

export function cloneBoard(board) {
  return board.map((row) => [...row]);
}

export function inBounds(row, col) {
  return row >= 0 && row < ROWS && col >= 0 && col < COLS;
}

export function cellsInBounds(cells) {
  return cells.every(([r, c]) => inBounds(r, c));
}

export function canPlace(board, pieceId, orientationDots, row, col, { ignoreCells = null } = {}) {
  const cells = absoluteCells(orientationDots, row, col);
  if (!cellsInBounds(cells)) {
    return false;
  }

  for (const [r, c] of cells) {
    const occupant = board[r][c];
    if (occupant !== null && occupant !== pieceId) {
      if (!ignoreCells || !ignoreCells.has(`${r},${c}`)) {
        return false;
      }
    }
  }

  return true;
}

export function placePiece(board, pieceId, orientationDots, row, col) {
  const cells = absoluteCells(orientationDots, row, col);
  if (!canPlace(board, pieceId, orientationDots, row, col)) {
    return false;
  }

  for (const [r, c] of cells) {
    board[r][c] = pieceId;
  }
  return true;
}

export function removePiece(board, pieceId) {
  for (let r = 0; r < ROWS; r += 1) {
    for (let c = 0; c < COLS; c += 1) {
      if (board[r][c] === pieceId) {
        board[r][c] = null;
      }
    }
  }
}

export function isBoardFull(board) {
  return board.every((row) => row.every((cell) => cell !== null));
}

export function countEmptyCells(board) {
  let count = 0;
  for (const row of board) {
    for (const cell of row) {
      if (cell === null) count += 1;
    }
  }
  return count;
}

export function boardToFlat(board) {
  const flat = [];
  for (let r = 0; r < ROWS; r += 1) {
    for (let c = 0; c < COLS; c += 1) {
      flat.push(board[r][c]);
    }
  }
  return flat;
}

export function boardFromFlat(flat, indexToPieceId) {
  if (flat.length !== CELL_COUNT) {
    throw new Error(`Expected ${CELL_COUNT} cells, got ${flat.length}`);
  }

  const board = createEmptyBoard();
  for (let i = 0; i < flat.length; i += 1) {
    const value = flat[i];
    const r = Math.floor(i / COLS);
    const c = i % COLS;
    if (value === null || value === -1) {
      board[r][c] = null;
    } else if (typeof value === 'string') {
      board[r][c] = value;
    } else {
      board[r][c] = indexToPieceId(value);
    }
  }
  return board;
}

/** Find anchor (top-left of bounding box) for a piece already on the board. */
export function findPieceAnchor(board, pieceId) {
  const cells = [];
  for (let r = 0; r < ROWS; r += 1) {
    for (let c = 0; c < COLS; c += 1) {
      if (board[r][c] === pieceId) {
        cells.push([r, c]);
      }
    }
  }
  if (cells.length === 0) {
    return null;
  }

  const minRow = Math.min(...cells.map(([r]) => r));
  const minCol = Math.min(...cells.map(([, c]) => c));
  return { row: minRow, col: minCol, cells };
}
