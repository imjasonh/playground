import { DIFFICULTY_STARTER_PIECES } from './constants.js';
import { PIECES } from './pieces.js';
import { cloneBoard, createEmptyBoard } from './board.js';
import { generateSolution } from './solver.js';
import { PUZZLE_LIBRARY } from './puzzleLibrary.js';

export function createGameState({ difficulty = 1, puzzleId = null, seed = Date.now() } = {}) {
  if (puzzleId !== null) {
    return createFromLibraryPuzzle(puzzleId);
  }

  const starterCount = DIFFICULTY_STARTER_PIECES[difficulty];
  if (starterCount === undefined) {
    throw new Error(`Invalid difficulty: ${difficulty}`);
  }

  if (starterCount === 0) {
    return createFreePlayState();
  }

  return createFromGeneratedSolution(difficulty, starterCount, seed);
}

function createFreePlayState() {
  return {
    difficulty: 6,
    board: createEmptyBoard(),
    fixedPieces: new Set(),
    trayPieces: PIECES.map((p) => p.id),
    placements: {},
    solved: false,
    mode: 'freeplay',
    puzzleId: null,
  };
}

function createFromGeneratedSolution(difficulty, starterCount, seed) {
  const { board: solutionBoard, placements: solutionPlacements } = generateSolution(seed);
  const pieceIds = PIECES.map((p) => p.id);
  const shuffled = shuffleArray(pieceIds, seed);
  const fixedIds = new Set(shuffled.slice(0, starterCount));
  const trayIds = shuffled.slice(starterCount);

  const board = createEmptyBoard();
  const placements = {};

  for (const pieceId of fixedIds) {
    const placement = solutionPlacements[pieceId];
    placements[pieceId] = {
      row: placement.row,
      col: placement.col,
      orientation: placement.orientation.map(([r, c]) => [r, c]),
      fixed: true,
    };
    for (const [dr, dc] of placement.orientation) {
      board[placement.row + dr][placement.col + dc] = pieceId;
    }
  }

  return {
    difficulty,
    board,
    fixedPieces: fixedIds,
    trayPieces: trayIds,
    placements,
    solved: false,
    mode: 'puzzle',
    puzzleId: null,
    solutionPlacements,
  };
}

function createFromLibraryPuzzle(puzzleId) {
  const puzzle = PUZZLE_LIBRARY.find((p) => p.id === puzzleId);
  if (!puzzle) {
    throw new Error(`Unknown puzzle id: ${puzzleId}`);
  }

  const board = cloneBoard(puzzle.startBoard);
  const fixedPieces = new Set();
  const placements = {};
  const trayPieces = [];

  for (const piece of PIECES) {
    const onBoard = board.some((row) => row.includes(piece.id));
    if (onBoard) {
      fixedPieces.add(piece.id);
      placements[piece.id] = { fixed: true, onBoard: true };
    } else {
      trayPieces.push(piece.id);
    }
  }

  return {
    difficulty: puzzle.difficulty,
    board,
    fixedPieces,
    trayPieces,
    placements,
    solved: false,
    mode: 'puzzle',
    puzzleId,
    solutionBoard: puzzle.solutionBoard,
  };
}

export function checkWin(state) {
  const allPlaced = state.trayPieces.length === 0;
  const full = state.board.every((row) => row.every((cell) => cell !== null));
  return allPlaced && full;
}

function shuffleArray(items, seed) {
  const copy = [...items];
  let state = seed >>> 0;
  for (let i = copy.length - 1; i > 0; i -= 1) {
    state = (state * 1664525 + 1013904223) >>> 0;
    const j = state % (i + 1);
    [copy[i], copy[j]] = [copy[j], copy[i]];
  }
  return copy;
}
