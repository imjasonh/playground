import {formatSeed, gridNeighbors, parseLevel, parseSeed} from './zip.js';
import {boardOf, canExtend, findHint, isSolved, moveTo, nextNumber} from
  './game.js';

const DEFAULT_LEVEL = 'easy';
const STORAGE_KEY = 'zip:v1';
const LEVEL_NAMES = {easy: 'Easy', medium: 'Medium', hard: 'Hard'};
// Leaves time for the numbers to pop before the dialog covers them.
const WIN_DIALOG_DELAY_MS = 900;
const SVG_NS = 'http://www.w3.org/2000/svg';

const boardEl = document.querySelector('#board');
const cellsEl = document.querySelector('#cells');
const badgesEl = document.querySelector('#badges');
const linesEl = document.querySelector('#lines');
const pathLine = document.querySelector('#path');
const hintLine = document.querySelector('#hint-line');
const headDot = document.querySelector('#head');
const infoEl = document.querySelector('#info');
const timerEl = document.querySelector('#timer');
const messageEl = document.querySelector('#message');
const levelInputs = [...document.querySelectorAll('input[name="level"]')];
const undoButton = document.querySelector('#undo');
const clearButton = document.querySelector('#clear');
const hintButton = document.querySelector('#hint');
const newButton = document.querySelector('#new');
const wonDialog = document.querySelector('#won');
const wonText = document.querySelector('#won-text');
const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');

const state = {
  level: DEFAULT_LEVEL,
  puzzle: null,
  board: null,
  path: [],
  history: [],
  hint: null,
  hints: 0,
  elapsed: 0,
  startedAt: null,
  solved: false,
};
let cells = [];
let loadToken = 0;
let drag = null;
let prefetched = null;

// Puzzles by key, as promises. The foreground worker builds the puzzle on
// screen and the background worker builds the next one, so a slow
// background build never holds up the board.
const puzzles = new Map();
const resolvers = new Map();
const workers = {foreground: null, background: null};
const busy = {foreground: new Set(), background: new Set()};

function startWorker(lane) {
  const worker = new Worker(new URL('./worker.js', import.meta.url),
      {type: 'module'});
  worker.addEventListener('message', (event) => {
    const {key, puzzle} = event.data;
    busy[lane].delete(key);
    resolvers.get(key)?.(puzzle);
    resolvers.delete(key);
  });
  workers[lane] = worker;
}

function puzzleKey(level, seed) {
  return `${level}:${formatSeed(seed)}`;
}

function requestPuzzle(level, seed, lane) {
  const key = puzzleKey(level, seed);
  if (puzzles.has(key)) {
    return puzzles.get(key);
  }
  // A new board on screen replaces any the foreground worker is still
  // building.
  if (lane === 'foreground' && busy.foreground.size > 0) {
    workers.foreground.terminate();
    for (const stale of busy.foreground) {
      puzzles.delete(stale);
      resolvers.delete(stale);
    }
    busy.foreground.clear();
    startWorker(lane);
  }
  if (!workers[lane]) {
    startWorker(lane);
  }
  const promise = new Promise((resolve) => {
    resolvers.set(key, resolve);
  });
  puzzles.set(key, promise);
  busy[lane].add(key);
  workers[lane].postMessage({key, level, seed});
  return promise;
}

function randomSeed() {
  return crypto.getRandomValues(new Uint32Array(1))[0];
}

// Builds the next puzzle at the current level in the background, so New
// shows it at once.
function prefetch() {
  prefetched = {level: state.level, seed: randomSeed()};
  requestPuzzle(prefetched.level, prefetched.seed, 'background');
  const keep = new Set([
    puzzleKey(state.level, state.puzzle.seed),
    puzzleKey(prefetched.level, prefetched.seed),
  ]);
  for (const key of puzzles.keys()) {
    if (!keep.has(key)) {
      puzzles.delete(key);
    }
  }
}

function loadSaved() {
  try {
    return JSON.parse(localStorage.getItem(STORAGE_KEY)) ?? {};
  } catch {
    return {};
  }
}

function save() {
  if (!state.puzzle) {
    return;
  }
  const saved = {
    level: state.level,
    seed: formatSeed(state.puzzle.seed),
    path: state.path,
    elapsed: Math.round(elapsedMs()),
    hints: state.hints,
    solved: state.solved,
  };
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(saved));
  } catch {
    // Storage can be full or turned off; the puzzle still plays.
  }
}

function elapsedMs() {
  const running = state.startedAt === null ?
      0 : performance.now() - state.startedAt;
  return state.elapsed + running;
}

function startTimer() {
  if (state.puzzle && state.startedAt === null && !state.solved &&
      !document.hidden) {
    state.startedAt = performance.now();
  }
}

function stopTimer() {
  state.elapsed = elapsedMs();
  state.startedAt = null;
}

function formatTime(ms) {
  const seconds = Math.floor(ms / 1000);
  const minutes = Math.floor(seconds / 60);
  const rest = String(seconds % 60).padStart(2, '0');
  if (minutes < 60) {
    return `${minutes}:${rest}`;
  }
  const hours = Math.floor(minutes / 60);
  return `${hours}:${String(minutes % 60).padStart(2, '0')}:${rest}`;
}

function renderTimer() {
  timerEl.textContent = formatTime(elapsedMs());
}

function buildBoard() {
  const {size, clues, walls} = state.puzzle;
  boardEl.style.setProperty('--n', String(size));
  boardEl.classList.remove('won');
  linesEl.setAttribute('viewBox', `0 0 ${size} ${size}`);
  const blocked = new Set(walls.map(([a, b]) => `${a}-${b}`));
  const wall = (a, b) => blocked.has(a < b ? `${a}-${b}` : `${b}-${a}`);
  cells = [];
  const rows = [];
  const badges = [];
  for (let r = 0; r < size; r += 1) {
    const row = document.createElement('div');
    row.className = 'row';
    row.setAttribute('role', 'row');
    for (let c = 0; c < size; c += 1) {
      const i = r * size + c;
      const cell = document.createElement('div');
      cell.className = 'cell';
      cell.id = `cell-${i}`;
      cell.setAttribute('role', 'gridcell');
      cell.classList.toggle('wall-top', r > 0 && wall(i, i - size));
      cell.classList.toggle('wall-left', c > 0 && wall(i, i - 1));
      cell.classList.toggle('wall-right', c < size - 1 && wall(i, i + 1));
      cell.classList.toggle('wall-bottom',
          r < size - 1 && wall(i, i + size));
      cell.classList.toggle('last-col', c === size - 1);
      cell.classList.toggle('last-row', r === size - 1);
      row.append(cell);
      cells.push(cell);
      if (clues[i]) {
        const badge = document.createElement('div');
        badge.className = 'badge';
        badge.textContent = String(clues[i]);
        badge.style.gridArea = `${r + 1} / ${c + 1}`;
        badge.style.setProperty('--order', String(clues[i]));
        badges.push(badge);
      }
    }
    rows.push(row);
  }
  cellsEl.replaceChildren(...rows);
  badgesEl.replaceChildren(...badges);
}

function points(path) {
  const {size} = state.puzzle;
  return path.map((cell) =>
    `${(cell % size) + 0.5},${Math.floor(cell / size) + 0.5}`).join(' ');
}

function statusText() {
  const {board, path} = state;
  if (state.solved) {
    return `Solved in ${formatTime(elapsedMs())}.`;
  }
  if (path.length === 0) {
    return 'Start at 1.';
  }
  const left = board.cells - path.length;
  if (path.at(-1) === board.end) {
    return `The path reached ${board.last} with ${left} ` +
        `${left === 1 ? 'cell' : 'cells'} left to fill.`;
  }
  return `${path.length} of ${board.cells} cells. ` +
      `Next number: ${nextNumber(board, path)}.`;
}

function render() {
  const {puzzle, board, path, hint} = state;
  const {size} = puzzle;
  const step = new Map(path.map((cell, i) => [cell, i + 1]));
  const wrong = new Set(hint?.wrong);
  let target = -1;
  if (hint) {
    target = hint.rule === 'back' ? hint.from : hint.cells.at(-1);
  }
  for (let i = 0; i < cells.length; i += 1) {
    const cell = cells[i];
    cell.classList.toggle('on-path', step.has(i) && !wrong.has(i));
    cell.classList.toggle('wrong', wrong.has(i));
    cell.classList.toggle('hint-target', i === target);
    const parts = [
      `Row ${Math.floor(i / size) + 1}`,
      `column ${(i % size) + 1}`,
    ];
    if (puzzle.clues[i]) {
      parts.push(`number ${puzzle.clues[i]}`);
    }
    if (step.has(i)) {
      parts.push(`step ${step.get(i)}`);
    }
    cell.setAttribute('aria-label', parts.join(', '));
  }
  pathLine.setAttribute('points', points(path));
  const head = path.at(-1);
  if (head === undefined) {
    headDot.setAttribute('visibility', 'hidden');
  } else {
    headDot.setAttribute('visibility', 'visible');
    headDot.setAttribute('cx', String((head % size) + 0.5));
    headDot.setAttribute('cy', String(Math.floor(head / size) + 0.5));
  }
  const hintPath = hint && hint.rule !== 'back' ?
      [...(hint.from >= 0 ? [hint.from] : []), ...hint.cells] : [];
  hintLine.setAttribute('points', points(hintPath));
  boardEl.setAttribute('aria-activedescendant',
      `cell-${head ?? board.start}`);
  messageEl.textContent = hint?.text ?? statusText();
  messageEl.classList.toggle('hint', Boolean(hint));
  undoButton.disabled = state.solved || state.history.length === 0;
  clearButton.disabled = state.solved || path.length === 0;
  hintButton.disabled = state.solved;
  renderTimer();
}

// Shows the puzzle for level and seed and records them in the URL, so a
// reload or a shared link shows the same puzzle. A pushed entry lets Back
// return to the previous puzzle.
async function showPuzzle(level, seed, historyMode) {
  const url = new URL(window.location.href);
  url.searchParams.set('level', level);
  url.searchParams.set('seed', formatSeed(seed));
  if (historyMode === 'push') {
    window.history.pushState(null, '', url);
  } else {
    window.history.replaceState(null, '', url);
  }
  if (state.puzzle) {
    stopTimer();
    save();
  }
  state.level = level;
  for (const input of levelInputs) {
    input.checked = input.value === level;
  }
  infoEl.textContent = LEVEL_NAMES[level];
  wonDialog.close();
  loadToken += 1;
  const token = loadToken;
  boardEl.setAttribute('aria-busy', 'true');
  const puzzle = await requestPuzzle(level, seed, 'foreground');
  if (token !== loadToken) {
    return;
  }
  const board = boardOf(puzzle);
  const saved = loadSaved();
  const resume = saved.level === level && saved.seed === formatSeed(seed) &&
      Array.isArray(saved.path);
  // Replays the saved path through the move rules, so a damaged save can't
  // put an impossible path on the board.
  let path = [];
  for (const cell of resume ? saved.path : []) {
    if (!canExtend(board, path, cell)) {
      break;
    }
    path = [...path, cell];
  }
  Object.assign(state, {
    puzzle,
    board,
    path,
    history: [],
    hint: null,
    hints: resume ? saved.hints ?? 0 : 0,
    elapsed: resume ? saved.elapsed ?? 0 : 0,
    startedAt: null,
    solved: isSolved(board, path),
  });
  infoEl.textContent = `${LEVEL_NAMES[level]} · ${puzzle.size}×${puzzle.size}`;
  buildBoard();
  boardEl.classList.toggle('won', state.solved);
  boardEl.setAttribute('aria-busy', 'false');
  startTimer();
  render();
  save();
  prefetch();
}

function showPuzzleFromUrl() {
  const params = new URLSearchParams(window.location.search);
  const saved = loadSaved();
  let level = parseLevel(params.get('level'));
  let seed = parseSeed(params.get('seed'));
  if (!level && seed === null && parseLevel(saved.level) &&
      parseSeed(saved.seed) !== null) {
    level = saved.level;
    seed = parseSeed(saved.seed);
  }
  showPuzzle(level ?? DEFAULT_LEVEL, seed ?? randomSeed(), 'replace');
}

function newPuzzle(level) {
  const ready = prefetched?.level === level;
  showPuzzle(level, ready ? prefetched.seed : randomSeed(), 'push');
}

function celebrate() {
  stopTimer();
  boardEl.classList.add('won');
  const {hints} = state;
  const used = hints === 0 ? 'no hints' :
      `${hints} ${hints === 1 ? 'hint' : 'hints'}`;
  wonText.textContent = `${LEVEL_NAMES[state.level]}. Solved in ` +
      `${formatTime(elapsedMs())} with ${used}.`;
  const token = loadToken;
  setTimeout(() => {
    if (token === loadToken && state.solved) {
      wonDialog.showModal();
    }
  }, reducedMotion.matches ? 0 : WIN_DIALOG_DELAY_MS);
}

// Reports whether the board takes moves: a puzzle is showing, it isn't
// solved, and no other puzzle is loading.
function playable() {
  return state.puzzle !== null && !state.solved &&
      boardEl.getAttribute('aria-busy') !== 'true';
}

// Records a move from the path before it. The path may already show the
// move, as it does during a drag.
function commit(before, after) {
  state.path = after;
  if (before.length === after.length &&
      before.every((cell, i) => cell === after[i])) {
    render();
    return;
  }
  state.history.push(before);
  state.hint = null;
  if (isSolved(state.board, after)) {
    state.solved = true;
    celebrate();
  }
  render();
  save();
}

function cellAt(x, y) {
  const {size} = state.puzzle;
  const rect = cellsEl.getBoundingClientRect();
  const col = Math.floor((x - rect.left) / rect.width * size);
  const row = Math.floor((y - rect.top) / rect.height * size);
  if (col < 0 || col >= size || row < 0 || row >= size) {
    return -1;
  }
  return row * size + col;
}

boardEl.addEventListener('pointerdown', (event) => {
  if (!event.isPrimary || event.button !== 0 || !playable()) {
    return;
  }
  const cell = cellAt(event.clientX, event.clientY);
  if (cell < 0) {
    return;
  }
  const next = moveTo(state.board, state.path, cell);
  if (!next) {
    return;
  }
  boardEl.setPointerCapture(event.pointerId);
  drag = {pointerId: event.pointerId, before: state.path, last: cell};
  state.path = next;
  state.hint = null;
  render();
});

boardEl.addEventListener('pointermove', (event) => {
  if (!drag || event.pointerId !== drag.pointerId) {
    return;
  }
  const cell = cellAt(event.clientX, event.clientY);
  if (cell < 0 || cell === drag.last) {
    return;
  }
  drag.last = cell;
  const next = moveTo(state.board, state.path, cell);
  if (next) {
    state.path = next;
    render();
  }
});

function endDrag(event) {
  if (!drag || event.pointerId !== drag.pointerId) {
    return;
  }
  const {before} = drag;
  drag = null;
  commit(before, state.path);
}

boardEl.addEventListener('pointerup', endDrag);
boardEl.addEventListener('pointercancel', endDrag);

const ARROWS = {ArrowUp: [-1, 0], ArrowDown: [1, 0], ArrowLeft: [0, -1],
  ArrowRight: [0, 1]};

// Arrow keys draw from the end of the path, and back up when they point at
// the cell before it. On an empty board, any arrow starts at 1.
boardEl.addEventListener('keydown', (event) => {
  if (event.defaultPrevented || event.altKey || event.ctrlKey ||
      event.metaKey || !playable()) {
    return;
  }
  const {board, path} = state;
  let next = null;
  if (event.key === 'Backspace' || event.key === 'Delete') {
    next = path.slice(0, -1);
  } else if (Object.hasOwn(ARROWS, event.key)) {
    if (path.length === 0) {
      next = [board.start];
    } else {
      const [dr, dc] = ARROWS[event.key];
      const head = path.at(-1);
      const target = gridNeighbors(board.size, head).find((n) =>
        Math.floor(n / board.size) - Math.floor(head / board.size) === dr &&
          (n % board.size) - (head % board.size) === dc);
      if (target !== undefined && target === path.at(-2)) {
        next = path.slice(0, -1);
      } else if (target !== undefined && canExtend(board, path, target)) {
        next = [...path, target];
      }
    }
  }
  if (next === null || next.length === path.length) {
    return;
  }
  event.preventDefault();
  commit(path, next);
});

undoButton.addEventListener('click', () => {
  if (!playable() || state.history.length === 0) {
    return;
  }
  state.path = state.history.pop();
  state.hint = null;
  render();
  save();
});

clearButton.addEventListener('click', () => {
  if (playable()) {
    commit(state.path, []);
  }
});

hintButton.addEventListener('click', () => {
  if (!playable() || state.hint) {
    return;
  }
  state.hint = findHint(state.puzzle, state.path);
  if (state.hint) {
    state.hints += 1;
  }
  render();
  save();
});

newButton.addEventListener('click', () => {
  newPuzzle(state.level);
});

for (const input of levelInputs) {
  input.addEventListener('change', () => newPuzzle(input.value));
}

wonDialog.addEventListener('close', () => {
  if (wonDialog.returnValue === 'new') {
    newPuzzle(state.level);
  }
  wonDialog.returnValue = '';
});

document.addEventListener('visibilitychange', () => {
  if (document.hidden) {
    stopTimer();
    save();
  } else {
    startTimer();
  }
});

window.addEventListener('pagehide', save);
window.addEventListener('popstate', showPuzzleFromUrl);
setInterval(renderTimer, 500);
showPuzzleFromUrl();

if ('serviceWorker' in navigator) {
  navigator.serviceWorker.register('sw.js').catch(() => {});
}
