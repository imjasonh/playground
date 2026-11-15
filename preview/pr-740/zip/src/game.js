// The player's side of a Zip puzzle: drawing the path, the win check, and
// hints. No DOM, so Node can test it.
//
// A path is an array of cells in the order the player drew them. It always
// starts on 1 and passes the numbers in order.

import {adjacency} from './zip.js';

// A hint shows at most this many cells ahead.
const HINT_CELLS = 4;

export function boardOf(puzzle) {
  const {size, clues, walls} = puzzle;
  const last = Math.max(...clues);
  return {
    size,
    cells: size * size,
    clues,
    adj: adjacency(size, walls),
    last,
    start: clues.indexOf(1),
    end: clues.indexOf(last),
  };
}

// Returns the number the path must reach next.
export function nextNumber(board, path) {
  let reached = 0;
  for (const cell of path) {
    reached = Math.max(reached, board.clues[cell]);
  }
  return reached + 1;
}

export function canExtend(board, path, cell) {
  if (path.length === 0) {
    return cell === board.start;
  }
  const head = path.at(-1);
  if (head === board.end || !board.adj[head].includes(cell) ||
      path.includes(cell)) {
    return false;
  }
  const number = board.clues[cell];
  return number === 0 || number === nextNumber(board, path);
}

// Returns the path after the player moves onto cell, or null if the move
// isn't allowed. A cell already on the path cuts the path back to it. A
// cell in line with the head extends the path through every cell between,
// so a quick drag that skips cells still works.
export function moveTo(board, path, cell) {
  const index = path.indexOf(cell);
  if (index >= 0) {
    return path.slice(0, index + 1);
  }
  if (canExtend(board, path, cell)) {
    return [...path, cell];
  }
  if (path.length === 0) {
    return null;
  }
  const {size} = board;
  const head = path.at(-1);
  const dr = Math.sign(Math.floor(cell / size) - Math.floor(head / size));
  const dc = Math.sign((cell % size) - (head % size));
  if (dr !== 0 && dc !== 0) {
    return null;
  }
  const step = dr * size + dc;
  let result = path;
  for (let next = head + step; ; next += step) {
    if (!canExtend(board, result, next)) {
      return null;
    }
    result = [...result, next];
    if (next === cell) {
      return result;
    }
  }
}

export function isSolved(board, path) {
  return path.length === board.cells && path.at(-1) === board.end;
}

// Finds a hint for path. If the path leaves the solution, the hint marks
// the last cell it got right and the cells after it. Otherwise it shows
// the next few cells of the solution, up to the next number.
//
// Returns {rule, from, cells, wrong, text}: 'start', 'back', or 'next';
// the cell the hint starts from; the cells to draw; the cells to undo; and
// the explanation.
export function findHint(puzzle, path) {
  const {solution, clues} = puzzle;
  const board = boardOf(puzzle);
  if (isSolved(board, path)) {
    return null;
  }
  let right = 0;
  while (right < path.length && path[right] === solution[right]) {
    right += 1;
  }
  if (right < path.length) {
    const from = path[right - 1];
    return {
      rule: 'back',
      from,
      cells: [from],
      wrong: path.slice(right),
      text: 'The path goes wrong after this cell. Back up to here.',
    };
  }
  if (path.length === 0) {
    return {
      rule: 'start',
      from: -1,
      cells: solution.slice(0, HINT_CELLS),
      wrong: [],
      text: 'Start at 1 and head this way.',
    };
  }
  const cells = [];
  for (let i = right; i < solution.length && cells.length < HINT_CELLS;
    i += 1) {
    cells.push(solution[i]);
    if (clues[solution[i]] !== 0) {
      break;
    }
  }
  const goal = nextNumber(board, path);
  const reached = clues[cells.at(-1)] === goal;
  return {
    rule: 'next',
    from: path.at(-1),
    cells,
    wrong: [],
    text: reached ? `Head this way to reach ${goal}.` :
        `Head this way toward ${goal}.`,
  };
}
