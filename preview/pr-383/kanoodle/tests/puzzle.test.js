import { createGameState, checkWin } from '../src/puzzle.js';
import { KanoodleGame } from '../src/game.js';
import { generateSolution } from '../src/solver.js';
import { PUZZLE_LIBRARY } from '../src/puzzleLibrary.js';

describe('puzzle', () => {
  test('level 6 free play starts with empty board and all pieces in tray', () => {
    const state = createGameState({ difficulty: 6 });
    expect(state.trayPieces).toHaveLength(12);
    expect(state.fixedPieces.size).toBe(0);
    expect(state.board.every((row) => row.every((cell) => cell === null))).toBe(true);
  });

  test('level 1 leaves one piece in the tray', () => {
    const state = createGameState({ difficulty: 1, seed: 100 });
    expect(state.trayPieces).toHaveLength(1);
    expect(state.fixedPieces.size).toBe(11);
  });

  test('library puzzle loads fixed starters', () => {
    const state = createGameState({ puzzleId: 1 });
    expect(state.fixedPieces.size).toBeGreaterThan(0);
    expect(state.trayPieces.length).toBeGreaterThan(0);
    expect(PUZZLE_LIBRARY[1].startBoard).toBeDefined();
  });

  test('checkWin detects a full board with empty tray', () => {
    const { board, placements } = generateSolution(999);
    const state = {
      difficulty: 6,
      board: board.map((row) => [...row]),
      fixedPieces: new Set(),
      trayPieces: [],
      placements: Object.fromEntries(
        Object.entries(placements).map(([id, p]) => [
          id,
          { row: p.row, col: p.col, orientation: p.orientation.map(([r, c]) => [r, c]), fixed: false },
        ])
      ),
      solved: false,
      mode: 'freeplay',
      puzzleId: null,
    };
    expect(checkWin(state)).toBe(true);
  }, 30000);

  test('tryPlaceCovering places piece on tapped cell', () => {
    const state = createGameState({ difficulty: 6 });
    const game = new KanoodleGame(state);
    const pieceId = state.trayPieces[0];
    game.selectPiece(pieceId);
    expect(game.tryPlaceCovering(2, 5)).toBe(true);
    expect(game.isOnBoard(pieceId)).toBe(true);
  });

  test('game prevents moving fixed pieces', () => {
    const state = createGameState({ difficulty: 1, seed: 7 });
    const fixedId = [...state.fixedPieces][0];
    const game = new KanoodleGame(state);
    expect(game.pickUpBoardPiece(fixedId)).toBe(false);
  });
});
