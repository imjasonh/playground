import { PIECES, getOrientations } from './pieces.js';
import {
  canPlace,
  cloneBoard,
  countEmptyCells,
  createEmptyBoard,
  isBoardFull,
  placePiece,
  removePiece,
} from './board.js';

const ORIENTATIONS_BY_ID = Object.fromEntries(
  PIECES.map((piece) => [piece.id, getOrientations(piece.dots)])
);

const DEFAULT_PIECE_ORDER = [...PIECES]
  .sort((a, b) => b.dots.length - a.dots.length)
  .map((piece) => piece.id);

function firstEmptyCell(board) {
  for (let row = 0; row < board.length; row += 1) {
    for (let col = 0; col < board[row].length; col += 1) {
      if (board[row][col] === null) {
        return [row, col];
      }
    }
  }
  return null;
}

function piecesOnBoard(board) {
  const set = new Set();
  for (const row of board) {
    for (const cell of row) {
      if (cell) set.add(cell);
    }
  }
  return set;
}

function regionTooSmall(board, remainingPieceIds) {
  const minPieceSize = Math.min(
    ...remainingPieceIds.map((id) => PIECES.find((p) => p.id === id).dots.length)
  );
  const visited = Array.from({ length: board.length }, () => Array(board[0].length).fill(false));
  const directions = [[1, 0], [-1, 0], [0, 1], [0, -1]];

  for (let row = 0; row < board.length; row += 1) {
    for (let col = 0; col < board[row].length; col += 1) {
      if (board[row][col] !== null || visited[row][col]) {
        continue;
      }

      let size = 0;
      const stack = [[row, col]];
      visited[row][col] = true;

      while (stack.length > 0) {
        const [r, c] = stack.pop();
        size += 1;
        for (const [dr, dc] of directions) {
          const nr = r + dr;
          const nc = c + dc;
          if (
            nr >= 0 &&
            nr < board.length &&
            nc >= 0 &&
            nc < board[0].length &&
            !visited[nr][nc] &&
            board[nr][nc] === null
          ) {
            visited[nr][nc] = true;
            stack.push([nr, nc]);
          }
        }
      }

      if (size > 0 && size < minPieceSize) {
        return true;
      }
    }
  }

  return false;
}

/**
 * Depth-first backtracking solver with first-empty-cell heuristic.
 * Returns the first complete placement map or null.
 */
export function solveBoard(board, { fixedPieces = new Set(), pieceOrder = null } = {}) {
  const working = cloneBoard(board);
  const order = pieceOrder || DEFAULT_PIECE_ORDER;
  const placements = {};

  function backtrack() {
    if (isBoardFull(working)) {
      return true;
    }

    const emptyCell = firstEmptyCell(working);
    if (!emptyCell) {
      return false;
    }

    const [targetRow, targetCol] = emptyCell;
    const used = piecesOnBoard(working);
    const remaining = order.filter((id) => !used.has(id));

    if (regionTooSmall(working, remaining)) {
      return false;
    }

    for (const pieceId of remaining) {
      if (fixedPieces.has(pieceId) && !used.has(pieceId)) {
        continue;
      }

      for (const orientation of ORIENTATIONS_BY_ID[pieceId]) {
        for (let row = 0; row <= targetRow; row += 1) {
          for (let col = 0; col <= targetCol; col += 1) {
            const coversTarget = orientation.some(
              ([dr, dc]) => row + dr === targetRow && col + dc === targetCol
            );
            if (!coversTarget) {
              continue;
            }
            if (!canPlace(working, pieceId, orientation, row, col)) {
              continue;
            }

            placePiece(working, pieceId, orientation, row, col);
            placements[pieceId] = { row, col, orientation };

            if (backtrack()) {
              return true;
            }

            removePiece(working, pieceId);
            delete placements[pieceId];
          }
        }
      }
    }

    return false;
  }

  if (backtrack()) {
    return { board: working, placements };
  }
  return null;
}

/** Build a random solved board by running the solver on an empty grid. */
export function generateSolution(seed = Date.now()) {
  let attempt = 0;
  while (attempt < 20) {
    const shuffled = shufflePieces(seed + attempt);
    const result = solveBoard(createEmptyBoard(), { pieceOrder: shuffled });
    if (result) {
      return result;
    }
    attempt += 1;
  }
  throw new Error('Could not generate a Kanoodle solution');
}

function shufflePieces(seed) {
  const ids = PIECES.map((p) => p.id);
  let state = seed >>> 0;
  for (let i = ids.length - 1; i > 0; i -= 1) {
    state = (state * 1664525 + 1013904223) >>> 0;
    const j = state % (i + 1);
    [ids[i], ids[j]] = [ids[j], ids[i]];
  }
  return ids;
}

export { ORIENTATIONS_BY_ID };
