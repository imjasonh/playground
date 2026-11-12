// Zip puzzles. No DOM, so Node can test it.
//
// A Zip board is an n×n grid with some numbered cells and, on harder
// levels, some walls between cells. The player draws one path that starts
// at 1, visits every cell exactly once, moves only between cells that share
// an edge and have no wall between them, passes the numbers in order, and
// ends on the highest number.
//
// Cells are numbered in row-major order. A puzzle's clues array holds each
// cell's number, or 0. Walls are pairs of neighboring cells [a, b] with
// a < b.

// Each level sets the board size, how many walls a puzzle may use, and how
// many numbers it keeps beyond the fewest that make the solution unique.
export const LEVELS = {
  easy: {size: 6, walls: 0, extraClues: 6},
  medium: {size: 7, walls: 2, extraClues: 2},
  hard: {size: 8, walls: 4, extraClues: 0},
};

export const LEVEL_NAMES = Object.keys(LEVELS);

// The solver gives up after this many search nodes and reports the puzzle
// as not proven unique, so a clue that would need a longer search stays.
const SEARCH_NODES = 200000;

// Backbite moves that shuffle the starting zigzag path, per cell.
const SHUFFLE_MOVES = 40;

export function makeRandom(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function shuffle(items, random) {
  for (let i = items.length - 1; i > 0; i -= 1) {
    const j = Math.floor(random() * (i + 1));
    [items[i], items[j]] = [items[j], items[i]];
  }
  return items;
}

export function gridNeighbors(size, cell) {
  const row = Math.floor(cell / size);
  const col = cell % size;
  const result = [];
  if (row > 0) {
    result.push(cell - size);
  }
  if (col < size - 1) {
    result.push(cell + 1);
  }
  if (row < size - 1) {
    result.push(cell + size);
  }
  if (col > 0) {
    result.push(cell - 1);
  }
  return result;
}

export function wallKey(a, b) {
  return a < b ? `${a}-${b}` : `${b}-${a}`;
}

// Lists the cells each cell can step to: its edge neighbors without a wall
// between them.
export function adjacency(size, walls) {
  const blocked = new Set(walls.map(([a, b]) => wallKey(a, b)));
  const result = [];
  for (let cell = 0; cell < size * size; cell += 1) {
    result.push(gridNeighbors(size, cell)
        .filter((n) => !blocked.has(wallKey(cell, n))));
  }
  return result;
}

// Returns a random path through every cell of the grid. Starts from a
// zigzag and applies backbite moves: join one end to a grid neighbor
// elsewhere on the path and reverse the piece between them.
export function randomPath(size, random) {
  const path = [];
  for (let row = 0; row < size; row += 1) {
    for (let i = 0; i < size; i += 1) {
      const col = row % 2 === 0 ? i : size - 1 - i;
      path.push(row * size + col);
    }
  }
  const index = new Int32Array(size * size);
  const reindex = (from, to) => {
    for (let i = from; i < to; i += 1) {
      index[path[i]] = i;
    }
  };
  reindex(0, path.length);
  const last = path.length - 1;
  for (let move = 0; move < SHUFFLE_MOVES * size * size; move += 1) {
    if (random() < 0.5) {
      path.reverse();
      reindex(0, path.length);
    }
    const end = path[last];
    const options = gridNeighbors(size, end).filter((n) => n !== path[last - 1]);
    const next = options[Math.floor(random() * options.length)];
    const i = index[next];
    const tail = path.splice(i + 1).reverse();
    path.push(...tail);
    reindex(i + 1, path.length);
  }
  return path;
}

// Finds up to limit paths that solve a board. Returns null if the search
// runs out of nodes before it can tell.
export function findSolutions(size, clues, walls, limit = 2) {
  const cells = size * size;
  const adj = adjacency(size, walls);
  let start = -1;
  let end = -1;
  let last = 0;
  clues.forEach((number, cell) => {
    if (number === 1) {
      start = cell;
    }
    if (number > last) {
      last = number;
      end = cell;
    }
  });
  const visited = new Uint8Array(cells);
  const seen = new Int32Array(cells);
  let stamp = 0;
  const queue = new Int32Array(cells);
  const trail = [];
  const found = [];
  let nodes = 0;

  // Reports whether the unvisited cells can still be covered from head:
  // they're all reachable from it, and no cell other than the end has
  // fewer than two ways in and out.
  const viable = (head, left) => {
    for (let cell = 0; cell < cells; cell += 1) {
      if (visited[cell]) {
        continue;
      }
      let degree = 0;
      for (const n of adj[cell]) {
        if (!visited[n] || n === head) {
          degree += 1;
        }
      }
      if (degree < (cell === end ? 1 : 2)) {
        return false;
      }
    }
    stamp += 1;
    let tail = 0;
    queue[tail] = head;
    tail += 1;
    seen[head] = stamp;
    for (let q = 0; q < tail; q += 1) {
      for (const n of adj[queue[q]]) {
        if (!visited[n] && seen[n] !== stamp) {
          seen[n] = stamp;
          queue[tail] = n;
          tail += 1;
        }
      }
    }
    return tail - 1 === left;
  };

  const search = (head, next) => {
    nodes += 1;
    if (nodes > SEARCH_NODES) {
      return;
    }
    if (trail.length === cells) {
      found.push([...trail]);
      return;
    }
    for (const n of adj[head]) {
      const number = clues[n];
      if (visited[n] || (number !== 0 && number !== next) ||
          (n === end && trail.length + 1 !== cells)) {
        continue;
      }
      visited[n] = 1;
      trail.push(n);
      if (viable(n, cells - trail.length)) {
        search(n, number !== 0 ? next + 1 : next);
      }
      trail.pop();
      visited[n] = 0;
      if (found.length >= limit || nodes > SEARCH_NODES) {
        return;
      }
    }
  };

  if (start < 0) {
    return null;
  }
  visited[start] = 1;
  trail.push(start);
  if (viable(start, cells - 1)) {
    search(start, 2);
  }
  return nodes > SEARCH_NODES ? null : found;
}

function isUnique(size, clues, walls) {
  return findSolutions(size, clues, walls)?.length === 1;
}

// Numbers the cells at the given path positions in path order.
function numberCells(size, path, positions) {
  const clues = new Array(size * size).fill(0);
  [...positions].sort((a, b) => a - b).forEach((position, i) => {
    clues[path[position]] = i + 1;
  });
  return clues;
}

// Builds the puzzle for level and seed. The same arguments always build
// the same puzzle, and it has exactly one solution.
export function generatePuzzle(level, seed) {
  const {size, walls: wallBudget, extraClues} = LEVELS[level];
  const random = makeRandom(seed);
  const cells = size * size;
  for (;;) {
    const path = randomPath(size, random);
    const onPath = new Set();
    for (let i = 1; i < cells; i += 1) {
      onPath.add(wallKey(path[i - 1], path[i]));
    }
    // Start with the two ends and a number every few cells.
    const positions = new Set([0, cells - 1]);
    const spacing = size + 2;
    for (let p = spacing; p < cells - 1; p += spacing) {
      positions.add(p + Math.floor(random() * 3) - 1);
    }
    const walls = [];
    let clues = numberCells(size, path, positions);
    let solutions = findSolutions(size, clues, walls);
    let tries = 0;
    while (solutions?.length !== 1 && tries < cells) {
      tries += 1;
      const other = solutions?.find(
          (solution) => solution.some((cell, i) => cell !== path[i]));
      if (other && walls.length < wallBudget && random() < 0.6) {
        // A wall on an edge the other solution uses and this one doesn't
        // rules that solution out.
        const edges = [];
        for (let i = 1; i < cells; i += 1) {
          const key = wallKey(other[i - 1], other[i]);
          if (!onPath.has(key)) {
            edges.push([Math.min(other[i - 1], other[i]),
              Math.max(other[i - 1], other[i])]);
          }
        }
        walls.push(edges[Math.floor(random() * edges.length)]);
      } else {
        // Number the cell where the other solution first leaves this one,
        // or any unnumbered cell if the search couldn't find one.
        let position = -1;
        if (other) {
          position = other.findIndex((cell, i) => cell !== path[i]);
        }
        if (position < 0 || positions.has(position)) {
          const free = [];
          for (let p = 1; p < cells - 1; p += 1) {
            if (!positions.has(p)) {
              free.push(p);
            }
          }
          position = free[Math.floor(random() * free.length)];
        }
        positions.add(position);
      }
      clues = numberCells(size, path, positions);
      solutions = findSolutions(size, clues, walls);
    }
    if (solutions?.length !== 1) {
      continue;
    }
    // Drop every number and wall the solution doesn't need, in random
    // order, then put back extra numbers for the easier levels.
    const removed = [];
    for (const position of shuffle([...positions], random)) {
      if (position === 0 || position === cells - 1) {
        continue;
      }
      positions.delete(position);
      if (isUnique(size, numberCells(size, path, positions), walls)) {
        removed.push(position);
      } else {
        positions.add(position);
      }
    }
    clues = numberCells(size, path, positions);
    for (const wall of shuffle([...walls], random)) {
      const rest = walls.filter((w) => w !== wall);
      if (isUnique(size, clues, rest)) {
        walls.splice(walls.indexOf(wall), 1);
      }
    }
    for (const position of shuffle(removed, random).slice(0, extraClues)) {
      positions.add(position);
    }
    clues = numberCells(size, path, positions);
    return {
      level,
      seed,
      size,
      clues,
      walls: walls.map(([a, b]) => [a, b]).sort((x, y) => x[0] - y[0] ||
          x[1] - y[1]),
      solution: path,
    };
  }
}

export function parseLevel(value) {
  return Object.hasOwn(LEVELS, value) ? value : null;
}

export function formatSeed(seed) {
  return (seed >>> 0).toString(16).padStart(8, '0');
}

export function parseSeed(value) {
  if (typeof value !== 'string' || !/^[0-9a-f]{1,8}$/i.test(value)) {
    return null;
  }
  return Number.parseInt(value, 16) >>> 0;
}
