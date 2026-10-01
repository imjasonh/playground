import {
  canPlace,
  countEmptyCells,
  createEmptyBoard,
  isBoardFull,
  placePiece,
  removePiece,
} from '../src/board.js';
import { getOrientations, pieceById } from '../src/pieces.js';

describe('board', () => {
  let board;

  beforeEach(() => {
    board = createEmptyBoard();
  });

  test('starts empty', () => {
    expect(countEmptyCells(board)).toBe(55);
    expect(isBoardFull(board)).toBe(false);
  });

  test('places and removes a piece', () => {
    const piece = pieceById('F');
    const orientation = getOrientations(piece.dots)[0];
    expect(placePiece(board, piece.id, orientation, 0, 0)).toBe(true);
    expect(board[0][0]).toBe('F');
    expect(board[1][0]).toBe('F');
    expect(board[1][1]).toBe('F');
    removePiece(board, 'F');
    expect(countEmptyCells(board)).toBe(55);
  });

  test('rejects out-of-bounds placement', () => {
    const piece = pieceById('J');
    const orientation = getOrientations(piece.dots)[0];
    expect(canPlace(board, piece.id, orientation, 4, 0)).toBe(false);
  });

  test('rejects overlapping placement', () => {
    const a = pieceById('F');
    const orientation = getOrientations(a.dots)[0];
    placePiece(board, a.id, orientation, 0, 0);
    expect(canPlace(board, a.id, orientation, 0, 0)).toBe(true);
    expect(canPlace(board, 'K', getOrientations(pieceById('K').dots)[0], 0, 0)).toBe(false);
  });
});
